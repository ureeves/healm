//! **He**ap **al**located **me**rkle tree.
#![deny(missing_docs)]
#![deny(clippy::pedantic)]
#![deny(rustdoc::broken_intra_doc_links)]
#![feature(allocator_api, slice_ptr_get)]

extern crate alloc;
use alloc::alloc::{Allocator, Global, Layout};

use core::{mem, ptr};

/// A heap allocated Merkle tree.
pub struct HamTree<T, const H: u32, const A: usize, Alloc = Global> {
    ptr: *mut Node<T>,
    alloc: Alloc,
}

type Node<T> = Option<T>;

const fn n_tree_leaves(height: u32, arity: usize) -> usize {
    arity.pow(height)
}

/// Number of nodes in a tree.
const fn n_tree_nodes(height: u32, arity: usize) -> usize {
    let mut n_nodes = 0;

    let mut h = 0;
    while h <= height {
        n_nodes += n_tree_leaves(height, arity);
        h += 1;
    }

    n_nodes
}

/// Returns the layout of a tree of the given height and arity, together with
/// the number of nodes in the tree.
const fn tree_layout<T>(height: u32, arity: usize) -> Layout {
    let node_size = mem::size_of::<Node<T>>();
    let node_align = mem::align_of::<Node<T>>();

    let n_tree_nodes = n_tree_nodes(height, arity);
    let tree_size = node_size * n_tree_nodes;

    unsafe { Layout::from_size_align_unchecked(tree_size, node_align) }
}

impl<T, const H: u32, const A: usize> HamTree<T, H, A>
where
    T: Aggregate<A>,
{
    /// Construct a new, empty `HamTree<T, H, A>`.
    ///
    /// The tree will not allocate until elements are inserted.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            ptr: ptr::null_mut(),
            alloc: Global,
        }
    }
}

impl<T, const H: u32, const A: usize, Alloc> HamTree<T, H, A, Alloc>
where
    T: Aggregate<A>,
    Alloc: Allocator,
{
    const LAYOUT: Layout = tree_layout::<T>(H, A);

    /// The maximum number of leaves a tree can hold.
    pub const N_LEAVES: usize = n_tree_leaves(H, A);

    /// Construct a new, empty `HamTree<T, H, A>`.
    ///
    /// The tree will not allocate until elements are inserted.
    #[must_use]
    pub const fn new_in(alloc: Alloc) -> Self {
        Self {
            ptr: ptr::null_mut(),
            alloc,
        }
    }

    /// Inserts an element at position `index` in the tree, ejecting the last
    /// element occupying that position, if any.
    ///
    /// # Panics
    /// Panics if `index >= capacity`.
    pub fn insert(&mut self, index: usize, leaf: T) -> Option<T> {
        assert!(index < Self::N_LEAVES, "Index out of bounds");

        if self.ptr.is_null() {
            let ptr = match self.alloc.allocate_zeroed(Self::LAYOUT) {
                Ok(ptr) => ptr,
                Err(err) => panic!("Allocation error: {err}"),
            };
            self.ptr = ptr.as_ptr().cast();
        }

        // safety: the memory was just allocated, and we ensure in the layout
        // that our calculations never leave the bounds of the allocated object
        //
        // # See docs/layout.svg
        // # https://doc.rust-lang.org/core/ptr/index.html#allocated-object
        unsafe {
            let mut level_ptr = self.ptr;
            let mut index = index;

            // Modify the leaf node
            let mut leaf = Some(leaf);
            let node_ptr = level_ptr.add(index);
            let node = &mut *node_ptr.cast();
            mem::swap(node, &mut leaf);

            // Propagate changes towards the root
            let mut n_nodes = Self::N_LEAVES;
            for _ in 0..H {
                let next_level_ptr = level_ptr.add(n_nodes);

                let next_n_nodes = n_nodes / A;
                let next_index = index / A;

                let siblings_index = A * (index / A);
                let siblings_ptr = level_ptr.add(siblings_index);
                let siblings = siblings_ptr.cast();

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
    pub fn root(&self) -> Option<&T> {
        if self.ptr.is_null() {
            return None;
        }

        unsafe {
            let root_index = n_tree_nodes(H, A) - 1;
            let root_ptr = self.ptr.add(root_index);

            (*root_ptr).as_ref()
        }
    }

    /// The maximum number of leaves the tree can hold.
    ///
    /// This number is the same as [`N_LEAVES`].
    ///
    /// [`N_LEAVES`]: Self::N_LEAVES
    pub const fn capacity(&self) -> usize {
        Self::N_LEAVES
    }
}

/// Types that can be aggregated to produce a new value.
pub trait Aggregate<const A: usize>: Sized {
    /// Aggregate the given nodes into a new node.
    fn aggregate(nodes: &[Option<Self>; A]) -> Self;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq)]
    struct Count(usize);

    impl<const A: usize> Aggregate<A> for Count {
        fn aggregate(nodes: &[Option<Self>; A]) -> Self {
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

        let mut tree = HamTree::<Count, H, A>::new();
        for i in 0..Tree::N_LEAVES {
            tree.insert(i, Count(1));
        }

        println!("{:?}", tree.root());

        assert!(matches!(tree.root(), Some(Count(Tree::N_LEAVES))));
    }
}
