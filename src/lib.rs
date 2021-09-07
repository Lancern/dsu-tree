//! This crate provides a non-invasive implementation of a **disjoint-set tree** data structure.
//!
//! # Disjoint-Set Tree
//!
//! **[Disjoint sets] data structure**, or **DSU**, or **union-find data structure**, or **merge-
//! find set**, is a data structure that stores a collection of disjoint sets. It provides
//! operations for adding new sets, merging sets (equivalent to replacing the sets with the union
//! of them) and finding the representative member of a set. DSU is very useful in implementing
//! algorithms like [minimum spanning tree] and more.
//!
//! DSU can be implemented with its extreme efficiency by using **disjoint-set trees**. Disjoint-set
//! trees are actually a forest in which each node represents a set and each tree represents the
//! union of sets that are merged together. The three DSU operations can be implemented as follows:
//! - Adding new sets: Easy. Just add new nodes to the forest and it's done. The new nodes are
//!   themselves a tree in the forest to indicate that they have not been merged with other sets.
//! - Merging sets: To merge two sets whose corresponding nodes are `A` and `B`, respectively, we
//!   just change the parent node of `A` to `B` and it's done. In real implementations, some corner
//!   cases need to be considered, such as merging a set into itself.
//! - Finding the representative member of a set: Each tree within the disjoint-set trees represents
//!   a set. The representative member of a set can be chosen to be the representative member of the
//!   set corresponding to the root node of the tree.
//!
//! # `dsu-tree`
//!
//! Rather than implementing a disjoint-set data structure, this crate provides the implementation
//! of the underlying disjoint-set tree data structure.
//!
//! [`DsuRoot`] is provided to access the disjoint-set trees. It is a smart pointer that can be
//! thought as "always" points to the root node of a tree within the disjoint-set trees.
//!
//! To create a new disjoint-set tree node, call the [`DsuRoot::new`] function. To merge two
//! disjoint-set trees, call the [`DsuRoot::merge_into`] function. To test whether two disjoint-set
//! trees are actually the same tree, call the [`DsuRoot::same`] function.
//!
//! # `#![no_std]`
//!
//! This crate is `#![no_std]`.
//!
//! [Disjoint sets]: https://en.wikipedia.org/wiki/Disjoint-set_data_structure
//! [minimum spanning tree]: https://en.wikipedia.org/wiki/Minimum_spanning_tree
//!
//! [`DsuRoot`]: struct.DsuRoot.html
//! [`DsuRoot::new`]: struct.DsuRoot.html#method.new
//! [`DsuRoot::merge_into`]: struct.DsuRoot.html#method.merge_into
//! [`DsuRoot::same`]: struct.DsuRoot.html#method.same
//!

#![no_std]

extern crate alloc;

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

    /// Determine whether the two `DsuRoot` smart pointers refer to the same tree.
    ///
    /// ```
    /// use dsu_tree::DsuRoot;
    ///
    /// let mut dsu_1 = DsuRoot::new(10);
    /// let mut dsu_2 = DsuRoot::new(20);
    /// assert!(!DsuRoot::same(&mut dsu_1, &mut dsu_2));
    ///
    /// dsu_1.merge_into(&mut dsu_2);
    /// assert!(DsuRoot::same(&mut dsu_1, &mut dsu_2));
    /// ```
    pub fn same(lhs: &mut Self, rhs: &mut Self) -> bool {
        lhs.move_to_root();
        rhs.move_to_root();
        Rc::ptr_eq(&lhs.node, &rhs.node)
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
    pub fn merge_into(&mut self, another: &mut Self) {
        if Self::same(self, another) {
            return;
        }

        // After calling `same`, `self` and `another` should both point to the root of their DSU
        // tree.
        debug_assert!(self.node.is_root());
        debug_assert!(another.node.is_root());

        self.node.set_parent(another.node.clone())
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
        *self.parent.borrow_mut() = Some(parent);
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
            }
        };
        if trivial {
            return;
        }

        // Do the path compression.
        let mut parent_borrow = self.parent.borrow_mut();

        // First, compress the path from the parent to the root. After this step, the parent of the
        // parent node should be the root.
        let parent_node = parent_borrow.as_ref().unwrap();
        parent_node.compress_path();

        // Then, simply update the parent pointer.
        *parent_borrow = Some(parent_node.parent().unwrap());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    fn create_link_tree() -> Vec<Rc<DsuNode<i32>>> {
        let mut nodes = Vec::with_capacity(10);

        let root = Rc::new(DsuNode::new(0));
        nodes.push(root.clone());

        for i in 1..10usize {
            let mut node = DsuNode::new(i as i32);
            node.parent = RefCell::new(Some(nodes[i - 1].clone()));

            nodes.push(Rc::new(node));
        }

        nodes
    }

    fn assert_path_compressed(nodes: &[Rc<DsuNode<i32>>]) {
        let root = nodes[0].clone();
        for i in 1..nodes.len() {
            let parent = nodes[i].parent();
            assert!(parent.is_some());
            assert!(Rc::ptr_eq(parent.as_ref().unwrap(), &root));
        }
    }

    mod dsu_node_tests {
        use super::*;

        #[test]
        fn test_new() {
            let node = DsuNode::new(10);

            assert!(node.parent.borrow().is_none());
            assert_eq!(node.value, 10);
        }

        #[test]
        fn test_is_root_true() {
            let node = DsuNode::new(10);
            assert!(node.is_root());
        }

        #[test]
        fn test_is_root_false() {
            let mut node = DsuNode::new(10);
            node.parent = RefCell::new(Some(Rc::new(DsuNode::new(20))));

            assert!(!node.is_root());
        }

        #[test]
        fn test_parent_root() {
            let node = DsuNode::new(10);

            assert!(node.parent().is_none());
        }

        #[test]
        fn test_parent_non_root() {
            let mut node = DsuNode::new(10);
            let root = Rc::new(DsuNode::new(20));
            node.parent = RefCell::new(Some(root.clone()));

            let node_parent = node.parent();
            assert!(node_parent.is_some());
            assert!(Rc::ptr_eq(node_parent.as_ref().unwrap(), &root));
        }

        #[test]
        fn test_set_parent() {
            let node = DsuNode::new(10);
            let parent = Rc::new(DsuNode::new(20));

            node.set_parent(parent.clone());

            assert!(node.parent.borrow().is_some());
            assert!(Rc::ptr_eq(node.parent.borrow().as_ref().unwrap(), &parent));
        }

        #[test]
        fn test_compress_path_root() {
            let node = DsuNode::new(10);

            node.compress_path();

            assert!(node.parent.borrow().is_none());
        }

        #[test]
        fn test_compress_path_root_child() {
            let mut node = DsuNode::new(10);
            let root = Rc::new(DsuNode::new(20));
            node.parent = RefCell::new(Some(root.clone()));

            node.compress_path();

            assert!(node.parent.borrow().is_some());
            assert!(Rc::ptr_eq(node.parent.borrow().as_ref().unwrap(), &root));
        }

        #[test]
        fn test_compress_path_deep() {
            let nodes = create_link_tree();

            nodes.last().unwrap().compress_path();

            assert_path_compressed(&nodes);
        }
    }

    mod dsu_root_tests {
        use super::*;

        #[test]
        fn test_new() {
            let ptr = DsuRoot::new(10);

            assert!(ptr.node.is_root());
            assert_eq!(ptr.node.value, 10);
        }

        #[test]
        fn test_same() {
            let mut ptr_1 = DsuRoot::new(10);
            let mut ptr_2 = DsuRoot::new(20);

            assert!(!DsuRoot::same(&mut ptr_1, &mut ptr_2));

            ptr_1.node.set_parent(ptr_2.node.clone());

            assert!(DsuRoot::same(&mut ptr_1, &mut ptr_2));
        }

        #[test]
        fn test_value_basic() {
            let mut ptr = DsuRoot::new(10);
            assert_eq!(*ptr.value(), 10);
        }

        #[test]
        fn test_value_merged() {
            let mut ptr = DsuRoot::new(10);
            ptr.node.set_parent(Rc::new(DsuNode::new(20)));

            assert_eq!(*ptr.value(), 20);
        }

        #[test]
        fn test_merge_into_basic() {
            let mut ptr = DsuRoot::new(10);
            let mut root = DsuRoot::new(20);

            ptr.merge_into(&mut root);

            assert!(DsuRoot::same(&mut ptr, &mut root));
            assert_eq!(*ptr.value(), 20);
        }

        #[test]
        fn test_merge_into_root() {
            let mut ptr = DsuRoot::new(10);
            let mut root = DsuRoot::new(20);

            ptr.node.set_parent(root.node.clone());

            ptr.merge_into(&mut root);

            assert_eq!(*ptr.value(), 20);
        }

        #[test]
        fn test_merge_into_child() {
            let mut ptr = DsuRoot::new(10);
            let mut root = DsuRoot::new(20);

            ptr.node.set_parent(root.node.clone());

            root.merge_into(&mut ptr);

            assert_eq!(*root.value(), 20);
        }

        #[test]
        fn test_move_to_root() {
            let nodes = create_link_tree();
            let root = nodes[0].clone();

            let mut ptr = DsuRoot {
                node: nodes.last().unwrap().clone(),
            };
            ptr.move_to_root();

            assert!(Rc::ptr_eq(&ptr.node, &root));

            assert_path_compressed(&nodes);
        }
    }
}
