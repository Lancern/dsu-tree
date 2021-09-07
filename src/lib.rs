//! This crate provides a non-invasive implementation of a disjoint-set-like tree data structure.
//!

#![no_std]

use alloc::rc::Rc;
use core::cell::RefCell;

/// An owning smart pointer that always points to the root of a DSU tree.
///
/// One can logically consider that `DsuRoot` smart pointers refer to a standalone DSU tree. When
/// merging two DSU trees by calling the [`merge_into`] function, the two DSU trees are given
/// through two `DsuRoot` smart pointers that logically refer to the two trees.
///
/// [`merge_into`]: #method.merge_into
#[derive(Clone, Debug)]
pub struct DsuRoot<T> {
    node: Rc<DsuNode<T>>,
}

impl<T> DsuRoot<T> {
    /// Create a new DSU tree node and attach a `DsuRoot` smart pointer to the new node.
    ///
    /// The new DSU tree node contains the given value.
    pub fn new(value: T) -> Self {
        Self {
            node: Rc::new(DsuNode::new(value)),
        }
    }

    /// Get the value contained in the DSU tree node pointed to by this `DsuRoot` smart pointer.
    ///
    /// This function requires `&mut self` since the `DsuRoot` smart pointer may move around over
    /// the DSU tree so that it eventually points to the root node.
    pub fn value(&mut self) -> &T {
        self.move_to_root();
        &self.node.value
    }

    /// Merge two DSU trees into one.
    ///
    /// The first DSU tree is given through `self`. The second DSU tree is given through `another`.
    ///
    /// If initially, the two trees are the same tree, then this function does nothing. Otherwise,
    /// the parent node of the root node of the tree specified through `self` is set to the root
    /// node of the tree specified through `another`.
    pub fn merge_into(&mut self, another: &mut DsuRoot<T>) {
        if self.same(another) {
            return;
        }

        // After calling `same`, `self` and `another` should both point to the root of their DSU
        // tree.
        debug_assert!(self.node.is_root());
        debug_assert!(another.node.is_root());

        self.node.set_parent(another.node.clone())
    }

    /// Determine whether the two `DsuRoot` smart pointers refer to the same tree.
    ///
    /// ```
    /// let mut dsu_1 = dsu_tree::DsuRoot::new(10);
    /// let mut dsu_2 = dsu_tree::DsuRoot::new(20);
    /// assert!(!dsu_1.same(&mut dsu_2));
    ///
    /// dsu_1.merge_into(&mut dsu_2);
    /// assert!(dsu_1.same(&mut dsu_2));
    /// ```
    pub fn same(&mut self, another: &mut DsuRoot<T>) -> bool {
        self.move_to_root();
        another.move_to_root();
        self.node.ptr_eq(&another.node)
    }

    /// Move this smart pointer to make it point to the root node of the referring DSU tree.
    fn move_to_root(&mut self) {
        self.node.compress_path();
        if !self.node.is_root() {
            self.node = self.node.parent().unwrap();
        }

        debug_assert!(self.node.is_root());
    }
}

/// The DSU tree node.
#[derive(Debug)]
struct DsuNode<T> {
    parent: RefCell<Option<Rc<DsuNode<T>>>>,
    value: T,
}

impl<T> DsuNode<T> {
    /// Create a new DSU tree node that contains the given value.
    fn new(value: T) -> Self {
        Self {
            parent: RefCell::new(None),
            value,
        }
    }

    /// Determine whether this node is the root node.
    fn is_root(&self) -> bool {
        self.parent.borrow().is_none()
    }

    /// Get the parent node wrapped in an [`Option`].
    ///
    /// If this node is the root node, this function returns [`None`].
    ///
    /// [`Option`]: https://doc.rust-lang.org/core/option/enum.Option.html
    /// [`None`]: https://doc.rust-lang.org/core/option/enum.Option.html#variant.None
    fn parent(&self) -> Option<Rc<DsuNode<T>>> {
        (*self.parent.borrow()).clone()
    }

    /// Set the parent node.
    //noinspection ALL
    fn set_parent(&self, parent: Rc<DsuNode<T>>) {
        *self.parent.borrow() = Some(parent);
    }

    /// Compress the path from this node to the root node of the tree.
    ///
    /// After path compression, the number of nodes along the path from this node to the root node
    /// cannot be greater than 2. That is, after path compression, one of the two conditions holds:
    /// * This node is initially the root node, and so it keeps to be the root node after path
    ///   compression;
    /// * This node is not the root node initially, and after path compression, the parent node
    ///   becomes the root node.
    fn compress_path(&self) {
        // Quick check to bail the trivial situations out in which:
        // * `self` is itself a root node;
        // * The parent node of `self` is a root node.
        //
        // In any of the two cases above, we don't have to do anything.
        let trivial = {
            let parent_borrow = self.parent.borrow();
            match &*parent_borrow {
                Some(parent) => parent.is_root(),
                None => true,
            };
        };
        if trivial {
            return;
        }

        // Do the path compression.
        let mut parent_borrow = self.parent.borrow_mut();

        // First, compress the path from the parent to the root. After this step, the parent of the
        // parent node should be the root.
        let parent_node = parent_borrow.as_ref().unwrap();
        parent_borrow.compress_path();

        // Then, simply update the parent pointer.
        *parent_borrow = Some(parent_node.parent().unwrap());
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
