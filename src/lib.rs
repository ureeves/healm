//! **He**ap **al**located **me**rkle tree.
#![deny(missing_docs)]
#![deny(clippy::pedantic)]
#![deny(rustdoc::broken_intra_doc_links)]
#![feature(allocator_api, slice_ptr_get)]

extern crate alloc;
use alloc::alloc::{Allocator, Global, Layout};

use core::{marker::PhantomData, mem, ptr};

/// A heap allocated Merkle tree.
pub struct HamTree<T, const H: usize, const A: usize, Alloc = Global> {
    ptr: *mut u8,
    alloc: Alloc,
    _marker: PhantomData<T>,
}

type Node<T> = Option<T>;

/// Returns the layout of a tree of the given height and arity, together with
/// the number of nodes in the tree.
const fn node_layout<T, const H: usize, const A: usize>() -> Layout {
    let node_size = mem::size_of::<Node<T>>();
    let node_align = mem::align_of::<Node<T>>();

    let n_tree_nodes = n_tree_nodes::<H, A>();
    let n_tree_leaves = n_tree_leaves::<H, A>();

    let tree_size = node_size * (n_tree_nodes + n_tree_leaves);

    unsafe { Layout::from_size_align_unchecked(tree_size, node_align) }
}

/// An array of number of nodes - that are *not leaves* - in a tree of the
/// given height and arity, counting from the level closest to the leaves up
/// to the root.
const fn tree_levels<const H: usize, const A: usize>() -> [usize; H] {
    let mut n_nodes = [0; H];

    let mut h = H;
    #[allow(clippy::cast_possible_truncation)]
    while h > 0 {
        n_nodes[H - h] = A.pow(h as u32);
        h -= 1;
    }

    n_nodes
}

/// Number of nodes in a tree that are *not leaves*.
const fn n_tree_nodes<const H: usize, const A: usize>() -> usize {
    let mut n_nodes = 0;

    let mut h = H;
    while h > 0 {
        n_nodes += tree_levels::<H, A>()[H - h];
        h -= 1;
    }

    n_nodes
}

/// Number of leaves in a tree with a certain height.
const fn n_tree_leaves<const H: usize, const A: usize>() -> usize {
    #[allow(clippy::cast_possible_truncation)]
    A.pow(H as u32)
}

impl<T, const H: usize, const A: usize> HamTree<T, H, A> {
    /// Construct a new, empty `HamTree<T, H, A>`.
    ///
    /// The tree will not allocate until elements are inserted.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            ptr: ptr::null_mut(),
            alloc: Global,
            _marker: PhantomData,
        }
    }
}

impl<T, const H: usize, const A: usize, Alloc: Allocator>
    HamTree<T, H, A, Alloc>
{
    const LAYOUT: Layout = node_layout::<T, H, A>();

    const N_NODES: usize = n_tree_nodes::<H, A>();
    const N_LEAVES: usize = n_tree_leaves::<H, A>();

    const LEVELS: [usize; H] = tree_levels::<H, A>();

    /// Construct a new, empty `HamTree<T, H, A>`.
    ///
    /// The tree will not allocate until elements are inserted.
    #[must_use]
    pub const fn new_in(alloc: Alloc) -> Self {
        Self {
            ptr: ptr::null_mut(),
            alloc,
            _marker: PhantomData,
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
            let ptr = match self.alloc.allocate(Self::LAYOUT) {
                Ok(ptr) => ptr,
                Err(err) => panic!("Allocation error: {err}"),
            };
            self.ptr = ptr.as_mut_ptr();
        }

        todo!("decide on how to lay out the tree")
    }

    /// The maximum number of leaves the tree can hold.
    ///
    /// This number is the same as [`n_leaves`].
    ///
    /// [`n_leaves`]: Self::n_leaves
    pub const fn capacity(&self) -> usize {
        Self::n_leaves()
    }

    /// The maximum number of leaves a tree can hold.
    ///
    /// This number is the same as [`capacity`].
    ///
    /// [`capacity`]: Self::capacity
    #[must_use]
    pub const fn n_leaves() -> usize {
        Self::N_LEAVES
    }
}
