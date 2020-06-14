// TOOD:
//  * iterator
//  * remove

use std::ptr;

struct NodePtr<K: Ord, V> {
    p: *mut Node<K, V>,
}

struct Node<K: Ord, V> {
    key: K,
    val: Option<V>,
    left: NodePtr<K, V>,
    right: NodePtr<K, V>,
    parent: NodePtr<K, V>,
    is_red: bool,
}

pub struct RBTree<K: Ord, V> {
    root: NodePtr<K, V>,
    size: usize,
}

impl<K: Ord, V> Copy for NodePtr<K, V> {}
impl<K: Ord, V> Clone for NodePtr<K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K: Ord, V> PartialEq for NodePtr<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.p == other.p
    }
}

impl<K: Ord, V> NodePtr<K, V> {
    fn none() -> NodePtr<K, V> {
        NodePtr { p: ptr::null_mut() }
    }

    fn set_some(&mut self, node: &mut Node<K, V>) {
        self.p = node;
    }

    fn is_some(&self) -> bool {
        !self.p.is_null()
    }

    fn resolve<'a>(&self) -> Option<&'a Node<K, V>> {
        if self.p.is_null() {
            None
        } else {
            Some(unsafe { &*self.p })
        }
    }

    fn resolve_mut<'a>(&mut self) -> Option<&'a mut Node<K, V>> {
        if self.p.is_null() {
            None
        } else {
            Some(unsafe { &mut *self.p })
        }
    }
}

impl<K: Ord, V> Node<K, V> {
    fn new(k: K, v: V) -> Self {
        Node {
            key: k,
            val: Some(v),
            left: NodePtr::none(),
            right: NodePtr::none(),
            parent: NodePtr::none(),
            is_red: true,
        }
    }

    fn set_parent(&mut self, node_ptr: NodePtr<K, V>) {
        self.parent = node_ptr;
    }

    fn left_child_ref(&self) -> &NodePtr<K, V> {
        &self.left
    }

    fn right_child_ref(&self) -> &NodePtr<K, V> {
        &self.right
    }

    fn left_child_mut(&mut self) -> &mut NodePtr<K, V> {
        &mut self.left
    }

    fn right_child_mut(&mut self) -> &mut NodePtr<K, V> {
        &mut self.right
    }

    fn set_left_child(&mut self, node_ptr: NodePtr<K, V>) {
        self.left = node_ptr;
    }

    fn set_right_child(&mut self, node_ptr: NodePtr<K, V>) {
        self.right = node_ptr;
    }
}

impl<K: Ord, V> RBTree<K, V> {
    pub fn new() -> Self {
        RBTree {
            root: NodePtr::none(),
            size: 0,
        }
    }

    pub fn clear(&mut self) {
        *self = RBTree::new();
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        if let Some(node) = self.find_node(key) {
            return (*node).val.as_ref();
        }
        None
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if let Some(node) = self.find_node_mut(key) {
            return (*node).val.as_mut();
        }
        None
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let (node, old_val) = self._insert(k, v);
        if node.is_some() {
            self.fixup(node);
        }
        self.size += 1;
        return old_val;
    }

    pub fn contains_key(&self, k: &K) -> bool {
        match self.find_node(k) {
            Some(_) => true,
            None => false,
        }
    }

    pub fn size(&self) -> usize {
        return self.size;
    }

    fn single_rotate_left(&mut self, mut target_node_ptr: NodePtr<K, V>) {
        //
        //      Root                Root
        //        \                   \
        //         A                   C
        //        / \       <--       / \
        //       B   C               A   E
        //          / \             / \
        //         D   E           B   D
        //

        let target_node: &mut Node<K, V>;
        let tmp_node: &mut Node<K, V>;

        let mut child_node_ptr: NodePtr<K, V>;

        if let Some(node) = target_node_ptr.resolve_mut() {
            target_node = node;
        } else {
            return;
        }

        let mut tmp_node_ptr = *target_node.left_child_mut();
        if let Some(node) = tmp_node_ptr.resolve_mut() {
            tmp_node = node;
        } else {
            return;
        }

        child_node_ptr = *tmp_node.right_child_mut();
        child_node_ptr.resolve_mut().map(|child_node| {
            child_node.parent = target_node_ptr;
        });

        target_node.set_left_child(child_node_ptr);
        tmp_node.set_right_child(target_node_ptr);

        let mut parent_node_ptr = target_node.parent;
        target_node.parent = tmp_node_ptr;

        match parent_node_ptr.resolve_mut() {
            Some(parent_node) => {
                if *parent_node.left_child_ref() == target_node_ptr {
                    parent_node.set_left_child(tmp_node_ptr);
                } else if *parent_node.right_child_ref() == target_node_ptr {
                    parent_node.set_right_child(tmp_node_ptr);
                }
            }
            None => {
                self.root = tmp_node_ptr;
            }
        }

        tmp_node.parent = parent_node_ptr;
    }

    fn single_rotate_right(&mut self, mut target_node_ptr: NodePtr<K, V>) {
        //
        //      Root                Root
        //        \                   \
        //         A                   B
        //        / \       -->       / \
        //       B   C               D   A
        //      / \                     / \
        //     D   E                   E   C
        //

        let target_node: &mut Node<K, V>;
        let tmp_node: &mut Node<K, V>;

        let mut child_node_ptr: NodePtr<K, V>;

        if let Some(node) = target_node_ptr.resolve_mut() {
            target_node = node;
        } else {
            return;
        }

        let mut tmp_node_ptr = *target_node.right_child_mut();
        if let Some(node) = tmp_node_ptr.resolve_mut() {
            tmp_node = node;
        } else {
            return;
        }

        child_node_ptr = *tmp_node.left_child_mut();
        child_node_ptr.resolve_mut().map(|child_node| {
            child_node.parent = target_node_ptr;
        });

        target_node.set_right_child(child_node_ptr);
        tmp_node.set_left_child(target_node_ptr);

        let mut parent_node_ptr = target_node.parent;
        target_node.parent = tmp_node_ptr;

        match parent_node_ptr.resolve_mut() {
            Some(parent_node) => {
                if *parent_node.right_child_ref() == target_node_ptr {
                    parent_node.set_right_child(tmp_node_ptr);
                } else if *parent_node.left_child_ref() == target_node_ptr {
                    parent_node.set_left_child(tmp_node_ptr);
                }
            }
            None => {
                self.root = tmp_node_ptr;
            }
        }

        tmp_node.parent = parent_node_ptr;
    }

    fn fixup(&mut self, node_ptr: NodePtr<K, V>) {
        if !node_ptr.is_some() {
            return;
        }

        let mut tmp_node_ptr = node_ptr;
        let mut uncle_node_ptr: NodePtr<K, V>;

        while tmp_node_ptr != self.root {
            let parent_node_ptr = RBTree::_parent(tmp_node_ptr);

            if !parent_node_ptr.is_some() {
                break;
            }
            if !RBTree::_is_red(parent_node_ptr) {
                break;
            }

            if parent_node_ptr == RBTree::_left_uncle(tmp_node_ptr) {
                uncle_node_ptr = RBTree::_right_uncle(tmp_node_ptr);

                if uncle_node_ptr.is_some() && RBTree::_is_red(uncle_node_ptr) {
                    let grand_parent_node_ptr = RBTree::_gparent(tmp_node_ptr);
                    RBTree::_set_red(grand_parent_node_ptr);
                    RBTree::_set_black(parent_node_ptr);
                    RBTree::_set_black(uncle_node_ptr);
                    tmp_node_ptr = grand_parent_node_ptr;
                } else {
                    if tmp_node_ptr == RBTree::_right_sibling(tmp_node_ptr) {
                        tmp_node_ptr = RBTree::_parent(tmp_node_ptr);
                        self.single_rotate_right(tmp_node_ptr);
                    }
                    let grand_parent_node_ptr = RBTree::_gparent(tmp_node_ptr);
                    RBTree::_set_red(grand_parent_node_ptr);
                    RBTree::_set_black(RBTree::_parent(tmp_node_ptr));
                    self.single_rotate_left(grand_parent_node_ptr);
                }
            } else {
                uncle_node_ptr = RBTree::_left_uncle(tmp_node_ptr);

                if uncle_node_ptr.is_some() && RBTree::_is_red(uncle_node_ptr) {
                    let grand_parent_node_ptr = RBTree::_gparent(tmp_node_ptr);
                    RBTree::_set_red(grand_parent_node_ptr);
                    RBTree::_set_black(parent_node_ptr);
                    RBTree::_set_black(uncle_node_ptr);
                    tmp_node_ptr = grand_parent_node_ptr;
                } else {
                    if tmp_node_ptr == RBTree::_left_sibling(tmp_node_ptr) {
                        tmp_node_ptr = RBTree::_parent(tmp_node_ptr);
                        self.single_rotate_left(tmp_node_ptr);
                    }
                    let grand_parent_node_ptr = RBTree::_gparent(tmp_node_ptr);
                    RBTree::_set_red(grand_parent_node_ptr);
                    RBTree::_set_black(RBTree::_parent(tmp_node_ptr));
                    self.single_rotate_right(grand_parent_node_ptr);
                }
            }
        }

        RBTree::_set_black(self.root);
    }

    fn find_node(&self, k: &K) -> Option<&Node<K, V>> {
        let mut root = &self.root;

        while let Some(node) = root.resolve() {
            if node.key == *k {
                return root.resolve();
            }

            if *k < node.key {
                root = node.left_child_ref();
            } else {
                root = node.right_child_ref();
            }
        }
        None
    }

    fn find_node_mut(&mut self, k: &K) -> Option<&mut Node<K, V>> {
        let mut root = &mut self.root;

        while let Some(node) = root.resolve_mut() {
            if node.key == *k {
                return root.resolve_mut();
            }

            if *k < node.key {
                root = node.left_child_mut();
            } else {
                root = node.right_child_mut();
            }
        }
        None
    }

    fn _insert(&mut self, k: K, v: V) -> (NodePtr<K, V>, Option<V>) {
        let mut root = &mut self.root;
        let mut parent: NodePtr<K, V> = NodePtr::none();

        while let Some(node) = root.resolve_mut() {
            if node.key == k {
                let old_val = node.val.take();
                node.val = Some(v);
                return (*root, old_val);
            }

            parent = *root;

            if k < node.key {
                root = node.left_child_mut();
            } else {
                root = node.right_child_mut();
            }
        }

        let mut node = Box::new(Node::new(k, v));
        (*node).set_parent(parent);
        root.set_some(Box::leak(node));

        (*root, None)
    }

    fn _is_red(node: NodePtr<K, V>) -> bool {
        node.resolve().unwrap().is_red
    }

    fn _parent(node: NodePtr<K, V>) -> NodePtr<K, V> {
        if let Some(n) = node.resolve() {
            return n.parent;
        }
        NodePtr::none()
    }

    fn _gparent(node: NodePtr<K, V>) -> NodePtr<K, V> {
        if let Some(n) = RBTree::_parent(node).resolve() {
            return n.parent;
        }
        NodePtr::none()
    }

    fn _left_uncle(node: NodePtr<K, V>) -> NodePtr<K, V> {
        if let Some(n) = RBTree::_gparent(node).resolve() {
            return n.left;
        }
        NodePtr::none()
    }

    fn _right_uncle(node: NodePtr<K, V>) -> NodePtr<K, V> {
        if let Some(n) = RBTree::_gparent(node).resolve() {
            return n.right;
        }
        NodePtr::none()
    }

    fn _left_sibling(node: NodePtr<K, V>) -> NodePtr<K, V> {
        if let Some(n) = RBTree::_parent(node).resolve() {
            return n.left;
        }
        NodePtr::none()
    }

    fn _right_sibling(node: NodePtr<K, V>) -> NodePtr<K, V> {
        if let Some(n) = RBTree::_parent(node).resolve() {
            return n.right;
        }
        NodePtr::none()
    }

    fn _set_red(mut node: NodePtr<K, V>) {
        if let Some(n) = node.resolve_mut() {
            n.is_red = true;
        }
    }

    fn _set_black(mut node: NodePtr<K, V>) {
        if let Some(n) = node.resolve_mut() {
            n.is_red = false;
        }
    }

    fn _destroy(mut node_ptr: NodePtr<K, V>) {
        if let Some(node) = node_ptr.resolve_mut() {
            RBTree::_destroy(node.left);
            RBTree::_destroy(node.right);
            unsafe { Box::from_raw(node) };
        }
    }
}

impl<K: Ord, V> Drop for RBTree<K, V> {
    fn drop(&mut self) {
        RBTree::_destroy(self.root);
    }
}

#[cfg(test)]
mod tests {
    use super::Node;
    use super::RBTree;

    fn child<K: Ord, V>(node: &Node<K, V>, direct: usize) -> &Node<K, V> {
        if direct == 0 {
            &(*node).left.resolve().unwrap()
        } else {
            &(*node).right.resolve().unwrap()
        }
    }

    #[test]
    fn test_insert() {
        let mut tree: RBTree<i32, i32> = RBTree::new();

        assert_eq!(tree.insert(1, 1), None);
        assert_eq!(tree.insert(2, 2), None);
        assert_eq!(tree.insert(3, 3), None);
        assert_eq!(tree.insert(3, 4), Some(3));
    }

    #[test]
    fn test_balancing_tree() {
        let mut tree: RBTree<i32, i32> = RBTree::new();

        assert_eq!(tree.size(), 0);

        tree.insert(10, 10);
        tree.insert(11, 11);
        tree.insert(12, 12);
        tree.insert(13, 13);
        tree.insert(14, 14);
        tree.insert(5, 5);
        tree.insert(4, 4);
        tree.insert(3, 3);
        tree.insert(2, 2);
        tree.insert(1, 1);
        tree.insert(6, 6);
        tree.insert(7, 7);
        tree.insert(8, 8);
        tree.insert(9, 9);

        let node = tree.root.resolve().unwrap();

        assert_eq!(node.val.unwrap(), 5);
        assert_eq!(node.is_red, false);

        assert_eq!(child(&node, 0).val.unwrap(), 3);
        assert_eq!(child(&node, 0).is_red, false);

        assert_eq!(child(child(&node, 0), 1).val.unwrap(), 4);
        assert_eq!(child(child(&node, 0), 1).is_red, false);

        assert_eq!(child(child(&node, 0), 0).val.unwrap(), 2);
        assert_eq!(child(child(&node, 0), 0).is_red, false);

        assert_eq!(child(child(child(&node, 0), 0), 0).val.unwrap(), 1);
        assert_eq!(child(child(child(&node, 0), 0), 0).is_red, true);

        assert_eq!(child(&node, 1).val.unwrap(), 11);
        assert_eq!(child(&node, 1).is_red, false);

        assert_eq!(child(child(&node, 1), 1).val.unwrap(), 13);
        assert_eq!(child(child(&node, 1), 1).is_red, false);

        assert_eq!(child(child(child(&node, 1), 1), 1).val.unwrap(), 14);
        assert_eq!(child(child(child(&node, 1), 1), 1).is_red, true);

        assert_eq!(child(child(child(&node, 1), 1), 0).val.unwrap(), 12);
        assert_eq!(child(child(child(&node, 1), 1), 0).is_red, true);

        assert_eq!(child(child(&node, 1), 0).val.unwrap(), 7);
        assert_eq!(child(child(&node, 1), 0).is_red, true);

        assert_eq!(child(child(child(&node, 1), 0), 0).val.unwrap(), 6);
        assert_eq!(child(child(child(&node, 1), 0), 0).is_red, false);

        assert_eq!(child(child(child(&node, 1), 0), 1).val.unwrap(), 9);
        assert_eq!(child(child(child(&node, 1), 0), 1).is_red, false);

        assert_eq!(
            child(child(child(child(&node, 1), 0), 1), 0).val.unwrap(),
            8
        );
        assert_eq!(child(child(child(child(&node, 1), 0), 1), 0).is_red, true);

        assert_eq!(
            child(child(child(child(&node, 1), 0), 1), 1).val.unwrap(),
            10
        );
        assert_eq!(child(child(child(child(&node, 1), 0), 1), 1).is_red, true);
    }

    #[test]
    fn test_empty() {
        let tree: RBTree<i32, i32> = RBTree::new();

        assert_eq!(tree.size(), 0);
    }

    #[test]
    fn test_clear() {
        let mut tree: RBTree<i32, i32> = RBTree::new();
        tree.insert(1, 1);
        tree.insert(2, 2);
        tree.insert(3, 3);

        assert_eq!(tree.size(), 3);

        tree.clear();
        assert_eq!(tree.size(), 0);
    }

    #[test]
    fn test_get() {
        let mut tree: RBTree<i32, i32> = RBTree::new();
        tree.insert(1, 1);
        tree.insert(2, 2);
        tree.insert(3, 3);

        assert_eq!(tree.get(&1), Some(&1));
        assert_eq!(tree.get(&2), Some(&2));
        assert_eq!(tree.get(&3), Some(&3));

        assert_eq!(tree.get(&4), None);
    }

    #[test]
    fn test_get_mut() {
        let mut tree: RBTree<i32, i32> = RBTree::new();
        tree.insert(1, 1);
        tree.insert(2, 2);
        tree.insert(3, 3);

        assert_eq!(tree.get_mut(&1), Some(&mut 1));
        assert_eq!(tree.get_mut(&2), Some(&mut 2));
        assert_eq!(tree.get_mut(&3), Some(&mut 3));

        assert_eq!(tree.get_mut(&4), None);
    }

    #[test]
    fn test_contains_key() {
        let mut tree: RBTree<i32, i32> = RBTree::new();

        tree.insert(1, 1);
        tree.insert(2, 2);
        tree.insert(3, 3);

        assert!(tree.contains_key(&1));
        assert!(tree.contains_key(&2));
        assert!(tree.contains_key(&3));

        assert!(tree.contains_key(&4) == false);
    }
}
