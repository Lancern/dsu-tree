# dsu-tree

A non-invasive implementation of a **disjoint-set tree** data structure, written in Rust.

# Disjoint-Set Tree

**[Disjoint sets](https://en.wikipedia.org/wiki/Disjoint-set_data_structure) data structure**, or **DSU**, or **union-find data structure**, or **merge- find set**, is a data structure that stores a collection of disjoint sets. It provides operations for adding new sets, merging sets (equivalent to replacing the sets with the union of them) and finding the representative member of a set. DSU is very useful in implementing algorithms like [minimum spanning tree](https://en.wikipedia.org/wiki/Minimum_spanning_tree) and more.

DSU can be implemented with its extreme efficiency by using **disjoint-set trees**. Disjoint-set trees are actually a forest in which each node represents a set and each tree represents the union of sets that are merged together. The three DSU operations can be implemented as follows:
- Adding new sets: Easy. Just add new nodes to the forest and it's done. The new nodes are themselves a tree in the forest to indicate that they have not been merged with other sets.
- Merging sets: To merge two sets whose corresponding nodes are `A` and `B`, respectively, we just change the parent node of `A` to `B` and it's done. In real implementations, some corner cases need to be considered, such as merging a set into itself.
- Finding the representative member of a set: Each tree within the disjoint-set trees represents a set. The representative member of a set can be chosen to be the representative member of the set corresponding to the root node of the tree.

# This Crate

Rather than implementing a disjoint-set data structure, this crate provides the implementation of the underlying disjoint-set tree data structure.

For the usage of this library, please refer to the [documentation](https://docs.rs/dsu-tree/0.1.0/dsu-tree).

# License

This library is open-sourced under [MIT License](./LICENSE).
