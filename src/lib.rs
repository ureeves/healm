//! **He**ap **al**located **me**rkle tree.
#![deny(missing_docs)]
#![deny(clippy::pedantic)]
#![deny(rustdoc::broken_intra_doc_links)]
#![feature(allocator_api)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(feature = "test", feature(test))]
#![no_std]

extern crate alloc;
extern crate core;

use alloc::alloc::{Allocator, Global, Layout};

use core::{
    mem,
    ptr::{self, NonNull},
    slice,
};

#[cfg(feature = "blake3")]
#[cfg_attr(docsrs, doc(cfg(feature = "blake3")))]
mod blake3;

/// Types that can be nodes in a `HamTree`. `Aggregate`s can be aggregated to
/// produce a new node.
///
/// `Aggregate` types must be `PartialEq`, since comparison is used to determine
/// whether a `HamTree` node is zeroed or not.
///
/// # Safety
/// The implementer must ensure that the type is safely zeroable. If
/// [`mem::zeroed`] is safe to call on the type, then it is also safe to
/// implement `Aggregate`.
pub unsafe trait Aggregate: PartialEq + Sized {
    /// Aggregate the given nodes into a new node.
    fn aggregate(nodes: &[Self]) -> Self;
}

fn empty_node<T: Aggregate>() -> T {
    unsafe { mem::zeroed() }
}

unsafe impl<T, const H: u32, const A: usize, Alloc: Allocator> Send
    for HamTree<T, H, A, Alloc>
{
}
unsafe impl<T, const H: u32, const A: usize, Alloc: Allocator> Sync
    for HamTree<T, H, A, Alloc>
{
}

/// A heap allocated Merkle tree.
pub struct HamTree<T, const H: u32, const A: usize, Alloc: Allocator = Global> {
    base: *mut T,
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
    /// Panics if `index >= capacity`, or the underlying allocator fails if it
    /// is the first insertion.
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
            let mut leaf = leaf;
            let leaf_ptr = level_ptr.add(index);
            ptr::swap(leaf_ptr, &mut leaf);

            // Propagate changes towards the root
            let mut n_nodes = Self::N_LEAVES;
            for _ in 0..H {
                let next_level_ptr = level_ptr.add(n_nodes);

                let next_n_nodes = n_nodes / A;
                let next_index = index / A;

                let siblings_index = index - (index % A);
                let siblings_ptr = level_ptr.add(siblings_index);
                let siblings: *const [T; A] = siblings_ptr.cast();

                let parent_ptr = next_level_ptr.add(next_index);
                *parent_ptr = T::aggregate(&*siblings);

                index = next_index;
                n_nodes = next_n_nodes;

                level_ptr = next_level_ptr;
            }

            if leaf == empty_node() {
                None
            } else {
                Some(leaf)
            }
        }
    }

    fn empty(node: &T) -> Option<&T> {
        if *node == unsafe { mem::zeroed::<T>() } {
            None
        } else {
            Some(node)
        }
    }

    /// Returns the leaf at the given index, if any.
    pub fn get(&self, index: usize) -> Option<&T> {
        if self.is_unallocated() {
            return None;
        }

        // safety: we check that the tree is allocated above, so de-referencing
        // is safe.
        unsafe {
            let leaf_ptr = self.base.add(index);
            let leaf = &*leaf_ptr.cast::<T>();

            Self::empty(leaf)
        }
    }

    /// Returns an iterator over the leaves of the tree.
    pub fn leaves(&self) -> impl Iterator<Item = &T> {
        if self.is_unallocated() {
            return [].iter().filter_map(Self::empty);
        }

        // safety: we check that the tree is allocated above, so de-referencing
        // is safe.
        unsafe {
            slice::from_raw_parts(self.base, Self::N_LEAVES)
                .iter()
                .filter_map(Self::empty)
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
            let root = &*root_ptr.cast::<T>();

            if *root == empty_node() {
                None
            } else {
                Some(root)
            }
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
            match self.alloc.allocate_zeroed(Self::LAYOUT) {
                Ok(ptr) => self.base = ptr.as_ptr().cast(),
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
    let node_size = mem::size_of::<T>();
    let node_align = mem::align_of::<T>();

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

    use alloc::collections::BTreeSet;

    use paste::paste;
    use rand::{rngs::StdRng, RngCore, SeedableRng};

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    struct Count(usize);

    unsafe impl Aggregate for Count {
        fn aggregate(nodes: &[Self]) -> Self {
            let mut sum = 0;
            for node in nodes {
                sum += node.0;
            }
            Self(sum)
        }
    }

    // A macro that generates test cases for the given arity and height.
    macro_rules! tree_tests {
        (H=$height:literal; A = $($arity:literal),+) => {
            $(
            paste! {
                mod [<tree _ h $height _ a $arity>] {
                    use super::*;

                    type Tree = HamTree<Count, $height, $arity>;

                    const N_INSERTIONS: usize = 100;

                    #[test]
                    fn insertion() {
                        let mut rng = StdRng::seed_from_u64(0xBAAD_F00D);

                        let mut tree = Tree::new();
                        let mut index_set = BTreeSet::new();

                        for _ in 0..N_INSERTIONS {
                            let i = (rng.next_u64() % Tree::N_LEAVES as u64) as usize;
                            index_set.insert(i);
                            tree.insert(i, Count(1));
                        }

                        let n_insertions = index_set.len();
                        assert!(matches!(tree.root(), Some(x) if *x == Count(n_insertions)));
                    }

                    #[test]
                    fn get() {
                        let mut rng = StdRng::seed_from_u64(0xBAAD_F00D);

                        let mut tree = Tree::new();
                        let mut index_set = BTreeSet::new();

                        for _ in 0..N_INSERTIONS {
                            let i = (rng.next_u64() % Tree::N_LEAVES as u64) as usize;
                            index_set.insert(i);
                            tree.insert(i, Count(1));
                        }

                        for i in index_set {
                            assert_eq!(tree.get(i), Some(&Count(1)));
                        }
                    }

                    #[test]
                    fn get_empty() {
                        let tree = Tree::new();
                        assert_eq!(tree.get(0), None);
                    }

                    #[test]
                    fn leaves() {
                        let mut rng = StdRng::seed_from_u64(0xBAAD_F00D);

                        let mut tree = Tree::new();
                        let mut index_set = BTreeSet::new();

                        for _ in 0..N_INSERTIONS {
                            let i = (rng.next_u64() % Tree::N_LEAVES as u64) as usize;
                            index_set.insert(i);
                            tree.insert(i, Count(1));
                        }

                        let mut leaf_count = 0;
                        for leaf in tree.leaves() {
                            assert_eq!(*leaf, Count(1));
                            leaf_count += 1;
                        }

                        let n_insertions = index_set.len();
                        assert_eq!(leaf_count, n_insertions);
                    }

                    #[test]
                    fn leaves_empty() {
                        let tree = Tree::new();
                        assert_eq!(tree.leaves().count(), 0);
                    }
                }
            }
            )+
        };
    }

    tree_tests!(H = 0; A = 2, 3, 4, 5);
    tree_tests!(H = 1; A = 2, 3, 4, 5);
    tree_tests!(H = 2; A = 2, 3, 4, 5);
    tree_tests!(H = 3; A = 2, 3, 4, 5);
    tree_tests!(H = 4; A = 2, 3, 4, 5);
    tree_tests!(H = 5; A = 2, 3, 4, 5);
    tree_tests!(H = 6; A = 2, 3, 4, 5);
    tree_tests!(H = 7; A = 2, 3, 4, 5);
    tree_tests!(H = 8; A = 2, 3, 4, 5);
}
