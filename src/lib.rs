//! Heap allocated merkle tree
#![deny(missing_docs)]
#![deny(clippy::pedantic)]
#![feature(allocator_api)]

extern crate alloc;
use alloc::alloc::{Allocator, Global, Layout};

use core::{marker::PhantomData, mem, ptr};

/// A heap allocated Merkle tree.
pub struct HamTree<T, const H: u32, const A: usize, Alloc = Global> {
    ptr: *mut u8,
    alloc: Alloc,
    _marker: PhantomData<T>,
}

type Node<T> = Option<T>;

impl<T, const H: u32, const A: usize> HamTree<T, H, A> {
    /// Creates a new heap allocated Merkle tree.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            ptr: ptr::null_mut(),
            alloc: Global,
            _marker: PhantomData,
        }
    }
}

/// Returns the layout of a tree of the given height and arity, together with
/// the number of nodes in the tree.
const fn node_layout<T>(height: u32, arity: usize) -> Layout {
    let node_size = mem::size_of::<Node<T>>();
    let node_align = mem::align_of::<Node<T>>();

    let tree_size = node_size * n_tree_nodes(height, arity);

    unsafe { Layout::from_size_align_unchecked(tree_size, node_align) }
}

/// Return the number of nodes in a tree of the given height and arity.
const fn n_tree_nodes(height: u32, arity: usize) -> usize {
    let mut size = 1;

    let mut h = 0;
    while h < height {
        size += arity.pow(h);
        h += 1;
    }

    size
}

const fn n_tree_leaves(height: u32, arity: usize) -> usize {
    arity.pow(height)
}

impl<T, const H: u32, const A: usize, Alloc: Allocator>
    HamTree<T, H, A, Alloc>
{
    const LAYOUT: Layout = node_layout::<T>(H, A);

    const N_NODES: usize = n_tree_nodes(H, A);
    const N_LEAVES: usize = n_tree_leaves(H, A);

    /// Creates a new heap allocated Merkle tree with a custom allocator.
    #[must_use]
    pub const fn new_in(alloc: Alloc) -> Self {
        Self {
            ptr: ptr::null_mut(),
            alloc,
            _marker: PhantomData,
        }
    }
}
