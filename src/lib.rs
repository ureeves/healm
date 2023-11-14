//! **He**ap **al**located **me**rkle tree.
#![deny(missing_docs)]
#![deny(clippy::pedantic)]
#![deny(rustdoc::broken_intra_doc_links)]
#![feature(allocator_api)]

extern crate alloc;
use alloc::alloc::{Allocator, Global, Layout};

use core::{
    mem,
    ptr::{self, NonNull},
};

type Node<T> = Option<T>;

/// Types that can be aggregated to produce a new value.
pub trait Aggregate: Sized {
    /// Aggregate the given nodes into a new node.
    fn aggregate(nodes: &[Option<Self>]) -> Self;
}

/// A heap allocated Merkle tree.
pub struct HamTree<T, const H: u32, const A: usize, Alloc: Allocator = Global> {
    base: *mut Node<T>,
    alloc: Alloc,
}

impl<T, const H: u32, const A: usize, Alloc: Allocator>
    HamTree<T, H, A, Alloc>
{
    /// The maximum number of leaves a tree can hold.
    pub const N_LEAVES: usize = n_tree_leaves(H, A);

    /// Layout of the tree in memory.
    const LAYOUT: Layout = tree_layout::<T>(H, A);
}

impl<T, const H: u32, const A: usize> HamTree<T, H, A>
where
    T: Aggregate,
{
    /// Construct a new, empty `HamTree`.
    ///
    /// The tree will not allocate until leaves are inserted.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            base: ptr::null_mut(),
            alloc: Global,
        }
    }
}

impl<T, const H: u32, const A: usize, Alloc> HamTree<T, H, A, Alloc>
where
    T: Aggregate,
    Alloc: Allocator,
{
    /// Construct a new, empty `HamTree`, that will allocate using the given
    /// `alloc`ator.
    ///
    /// The tree will not allocate until leaves are inserted.
    pub const fn new_in(alloc: Alloc) -> Self {
        Self {
            base: ptr::null_mut(),
            alloc,
        }
    }

    /// Inserts a leaf at position `index` in the tree, ejecting the last
    /// element occupying the position, if any.
    ///
    /// # Panics
    /// Panics if `index >= capacity`.
    pub fn insert(&mut self, index: usize, leaf: T) -> Option<T> {
        assert!(index < Self::N_LEAVES, "Index out of bounds");

        self.ensure_allocated();

        // safety: the memory was just allocated, and we ensure in the layout
        // that our calculations never leave the bounds of the allocated object
        //
        // # See docs/layout.svg
        // # https://doc.rust-lang.org/core/ptr/index.html#allocated-object
        unsafe {
            let mut level_ptr = self.base;
            let mut index = index;

            // Modify the leaf node
            let mut leaf = Some(leaf);
            let node_ptr = level_ptr.add(index);
            let node = &mut *node_ptr.cast();
            mem::swap(node, &mut leaf);

            // Propagate changes towards the root
            let mut n_nodes = Self::N_LEAVES;
            for _ in 0..=H {
                let next_level_ptr = level_ptr.add(n_nodes);

                let next_n_nodes = n_nodes / A;
                let next_index = index / A;

                let siblings_index = index - (index % A);
                let siblings_ptr = level_ptr.add(siblings_index);
                let siblings: *const [Node<T>; A] = siblings_ptr.cast();

                let new_parent = T::aggregate(&*siblings);
                let parent_ptr = next_level_ptr.add(next_index);
                *parent_ptr = Some(new_parent);

                index = next_index;
                n_nodes = next_n_nodes;

                level_ptr = next_level_ptr;
            }

            leaf
        }
    }

    /// Returns the root of the tree.
    ///
    /// If no leaves have been inserted, it returns `None`.
    #[must_use]
    pub fn root(&self) -> Option<&T> {
        if self.is_unallocated() {
            return None;
        }
        // safety: we check that the tree is allocated above, so de-referencing
        // the root is safe.
        unsafe {
            let root_ptr = self.base.add(n_tree_nodes(H, A) - 1);
            let root = &*root_ptr.cast::<Node<T>>();
            root.as_ref()
        }
    }

    /// The maximum number of leaves the tree can hold.
    ///
    /// This number is the same as [`N_LEAVES`].
    ///
    /// [`N_LEAVES`]: Self::N_LEAVES
    #[must_use]
    pub const fn capacity(&self) -> usize {
        Self::N_LEAVES
    }

    /// Ensures that the tree is allocated.
    ///
    /// # Panics
    /// Panics if the underlying allocator fails.
    fn ensure_allocated(&mut self) {
        if self.is_unallocated() {
            match self.alloc.allocate(Self::LAYOUT) {
                Ok(ptr) => {
                    self.base = ptr.as_ptr().cast();

                    // safety: we just allocated the memory, so we can
                    // de-reference it safely.
                    unsafe {
                        *self.base = None;

                        let mut ptr = self.base;
                        let mut count = 1;

                        for _ in 0..H {
                            let next_ptr = ptr.add(count);

                            for a in 0..A {
                                ptr::copy_nonoverlapping(
                                    ptr,
                                    next_ptr.add(a * count),
                                    count,
                                );
                            }

                            count *= A;
                            ptr = next_ptr;
                        }
                    }
                }
                Err(err) => panic!("HamTree failed allocation: {err}"),
            }
        }
    }

    fn is_unallocated(&self) -> bool {
        self.base.is_null()
    }
}

impl<T, const H: u32, const A: usize, Alloc> Drop for HamTree<T, H, A, Alloc>
where
    Alloc: Allocator,
{
    fn drop(&mut self) {
        // safety: we check if the tree is allocated using `NonNull::new` so
        // de-allocating is safe.
        unsafe {
            if let Some(ptr) = NonNull::new(self.base) {
                self.alloc.deallocate(ptr.cast(), Self::LAYOUT);
            }
        }
    }
}

const fn tree_layout<T>(height: u32, arity: usize) -> Layout {
    let node_size = mem::size_of::<Node<T>>();
    let node_align = mem::align_of::<Node<T>>();

    let size = n_tree_nodes(height, arity) * node_size;
    let align = node_align;

    unsafe { Layout::from_size_align_unchecked(size, align) }
}

/// Number of leaves in a tree with the given height and arity.
const fn n_tree_leaves(height: u32, arity: usize) -> usize {
    arity.pow(height)
}

/// Total number of nodes in a tree with the given height and arity.
const fn n_tree_nodes(height: u32, arity: usize) -> usize {
    let mut n_nodes = 0;

    let mut h = 0;
    while h <= height {
        n_nodes += n_tree_leaves(h, arity);
        h += 1;
    }

    n_nodes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Clone, Copy, PartialEq)]
    struct Count(usize);

    impl Aggregate for Count {
        fn aggregate(nodes: &[Option<Self>]) -> Self {
            let mut sum = 0;
            nodes.iter().flatten().for_each(|node| sum += node.0);
            Self(sum)
        }
    }

    #[test]
    fn insertion() {
        const H: u32 = 3;
        const A: usize = 2;

        type Tree = HamTree<Count, H, A>;

        struct TestCase {
            count: Count,
            expected_root: Count,
        }

        impl TestCase {
            const fn new(count: usize) -> Self {
                Self {
                    count: Count(count),
                    expected_root: Count(count * Tree::N_LEAVES),
                }
            }
        }

        const TEST_CASES: [TestCase; 8] = [
            TestCase::new(1),
            TestCase::new(2),
            TestCase::new(3),
            TestCase::new(4),
            TestCase::new(5),
            TestCase::new(6),
            TestCase::new(7),
            TestCase::new(8),
        ];

        let mut tree = HamTree::<Count, H, A>::new();

        for case in TEST_CASES {
            for i in 0..Tree::N_LEAVES {
                tree.insert(i, case.count);
            }

            assert!(matches!(tree.root(), Some(x) if *x == case.expected_root));
        }
    }
}
