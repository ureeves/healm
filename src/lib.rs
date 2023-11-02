//! **He**ap **al**located **me**rkle tree.
#![deny(missing_docs)]
#![deny(clippy::pedantic)]
#![deny(rustdoc::broken_intra_doc_links)]
#![feature(allocator_api, slice_ptr_get)]

extern crate alloc;
use alloc::alloc::{Allocator, Global, Layout};

use core::{mem, ptr};

/// A heap allocated Merkle tree.
pub struct HamTree<T, const H: usize, const A: usize, Alloc = Global> {
    ptr: *mut T,
    alloc: Alloc,
}

type Node<T> = Option<T>;

/// Number of nodes in a tree.
const fn n_tree_nodes<const H: usize, const A: usize>() -> usize {
    let mut n_nodes = 1; // start with the root

    let mut h = H;
    while h > 0 {
        n_nodes += tree_levels::<H, A>()[H - h];
        h -= 1;
    }

    n_nodes
}

/// Returns the layout of a tree of the given height and arity, together with
/// the number of nodes in the tree.
const fn node_layout<T, const H: usize, const A: usize>() -> Layout {
    let node_size = mem::size_of::<Node<T>>();
    let node_align = mem::align_of::<Node<T>>();

    let n_tree_nodes = n_tree_nodes::<H, A>();
    let tree_size = node_size * n_tree_nodes;

    unsafe { Layout::from_size_align_unchecked(tree_size, node_align) }
}

/// Number of nodes in all levels of a tree of the given height and arity,
/// ordered from the leaves up to, but excluding, the root.
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

impl<T, const H: usize, const A: usize> HamTree<T, H, A> {
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

impl<T, const H: usize, const A: usize, Alloc: Allocator>
    HamTree<T, H, A, Alloc>
{
    const LAYOUT: Layout = node_layout::<T, H, A>();
    const LEVELS: [usize; H] = tree_levels::<H, A>();

    // Indexing the level array at 0 means that `H` can never be 0, which allows
    // us to optimize a check away at insertion. That check would have been
    // between inserting directly at the root or not.

    /// The maximum number of leaves a tree can hold.
    pub const N_LEAVES: usize = Self::LEVELS[0];

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
            let ptr = match self.alloc.allocate(Self::LAYOUT) {
                Ok(ptr) => ptr,
                Err(err) => panic!("Allocation error: {err}"),
            };
            self.ptr = ptr.as_ptr().cast();
        }

        // safety: this dereferences memory that was just allocated previously
        let popped = unsafe {
            let mut leaf = Some(leaf);

            let ptr = self.ptr.add(index);
            let leaf_ref = &mut *ptr.cast::<Node<T>>();

            mem::swap(leaf_ref, &mut leaf);

            leaf
        };

        todo!("update the tree's hashes");

        popped
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
