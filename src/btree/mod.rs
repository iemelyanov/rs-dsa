use std::cmp::Ord;
use std::mem;

type Childred<K, V> = Vec<Node<K, V>>;

struct Node<K, V> {
    childs: Childred<K, V>,
    keys: Vec<K>,
    vals: Vec<V>,
}

impl<K: Ord, V> Node<K, V> {
    fn new() -> Self {
        Node {
            childs: Vec::new(),
            keys: Vec::new(),
            vals: Vec::new(),
        }
    }

    fn split(&mut self, i: usize) -> (K, V, Node<K, V>) {
        let mut next_node = Node::new();

        next_node.keys = self.keys.split_off(i + 1);
        next_node.vals = self.vals.split_off(i + 1);

        if self.childs.len() > 0 {
            next_node.childs = self.childs.split_off(i + 1);
        }

        (self.keys.remove(i), self.vals.remove(i), next_node)
    }

    fn maybe_split_child(&mut self, i: usize, max_items: usize) -> bool {
        if let Some(ref mut node) = self.childs.get_mut(i) {
            if node.keys.len() < max_items {
                return false;
            }

            let (k, v, next_node) = node.split(max_items / 2);

            self.keys.insert(i, k);
            self.vals.insert(i, v);
            self.childs.insert(i+1, next_node);

            return true;
        }

        false
    }

    fn insert(&mut self, k: K, v: V, max_items: usize) -> Option<(K, V)> {
        let r = self.keys.binary_search(&k);

        match r {
            Ok(i) => {
                let mut result: (K, V) = (k, v);
                unsafe {
                    mem::swap(&mut result.1, self.vals.get_unchecked_mut(i));
                }
                return Some(result);
            },
            Err(mut i) => {
                if self.childs.len() == 0 {
                    self.keys.insert(i, k);
                    self.vals.insert(i, v);
                    return None
                }

                if self.maybe_split_child(i, max_items) {
                    let _k = unsafe { self.keys.get_unchecked(i) };
                    match &k {
                        x if *x < *_k => {},
                        x if *_k < *x => {
                            i += 1;    
                        }
                        _ => {
                            let mut result: (K, V) = (k, v);
                            unsafe {
                                mem::swap(
                                    &mut result.1,
                                    self.vals.get_unchecked_mut(i)
                                );
                            }
                            return Some(result);
                        }
                    }
                }

                return self.childs.get_mut(i).map(|node| {
                    node.insert(k, v, max_items)
                }).unwrap();
            }
        }

        None
    }

    fn get(&self, k: &K) -> Option<&V> {
        match self.keys.binary_search(k) {
            Ok(i) => {
                return self.vals.get(i);
            },
            Err(i) => {
                if let Some(node) = self.childs.get(i) {
                    return node.get(k);
                }
            },
        }

        None
    }
}

pub struct BTree<K, V> {
    root: Node<K, V>,
    size: usize,
    degree: usize,
}

impl<K: Ord, V> BTree<K, V> {
    pub fn new(degree: usize) -> Self {
        BTree {
            root: Node::new(),
            size: 0,
            degree: degree,
        }
    }

    pub fn len(&self) -> usize {
        self.size
    }

    fn max_items(&self) -> usize {
        self.degree * 2 - 1
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        if self.root.keys.len() == 0 {
            self.root.keys.push(k);
            self.root.vals.push(v);
            self.size += 1;
            return None;
        } else {
            if self.root.keys.len() >= self.max_items() {
                let (k, v, next_node) = self.root.split(self.max_items() / 2);
                let mut tmp_node: Node<K, V> = Node::new();

                mem::swap(&mut self.root, &mut tmp_node);
                
                self.root.keys.push(k);
                self.root.vals.push(v);
                self.root.childs.push(tmp_node);
                self.root.childs.push(next_node);
            }
        }

        match self.root.insert(k, v, self.max_items()) {
            Some(item) => {
                return Some(item.1);
            }
            None => {
                self.size += 1;
                return None;
            }
        }
    }

    pub fn get(&self, k: &K) -> Option<&V> {
        self.root.get(k)
    }
}

#[cfg(test)]
mod btree_tests {
    use super::*;

    #[test]
    fn node_split() {
        let mut node = Node::new();
        node.keys = vec![1, 2, 3, 4];
        node.vals = vec![1, 2, 3, 4];

        let mid = node.keys.len() / 2;

        let (k, v, next_node) = node.split(mid);

        assert_eq!(3, k);
        assert_eq!(3, v);

        assert_eq!(vec![1, 2], node.keys);
        assert_eq!(vec![1, 2], node.vals);

        assert_eq!(vec![4], next_node.keys);
        assert_eq!(vec![4], next_node.vals);
    }

    #[test]
    fn node_maybe_split_child() {
        let mut root = Node::new();
        root.keys = vec![3];
        root.vals = vec![3];

        let mut node1 = Node::new();
        node1.keys = vec![1, 2];
        node1.vals = vec![1, 2];

        let mut node2 = Node::new();
        node2.keys = vec![4, 5, 6];
        node2.vals = vec![4, 5, 6];

        root.childs = vec![node1, node2];

        assert!(root.maybe_split_child(1, 3));
        assert_eq!(root.keys, vec![3, 5]);
        assert_eq!(root.vals, vec![3, 5]);
        assert_eq!(root.childs.len(), 3);
        assert_eq!(root.childs.get(0).unwrap().keys, vec![1, 2]); 
        assert_eq!(root.childs.get(1).unwrap().keys, vec![4]);
        assert_eq!(root.childs.get(2).unwrap().keys, vec![6]);
    }

    #[test]
    fn node_insert() {
        let mut root = Node::new();
        root.keys = vec![3];
        root.vals = vec![3];

        let mut node1 = Node::new();
        node1.keys = vec![1, 2];
        node1.vals = vec![1, 2];

        let mut node2 = Node::new();
        node2.keys = vec![4, 5];
        node2.vals = vec![4, 5];

        root.childs = vec![node1, node2];

        root.insert(6, 6, 3);
        root.insert(7, 7, 3);
        assert_eq!(root.keys, vec![3, 5]);
        assert_eq!(root.vals, vec![3, 5]);
        assert_eq!(root.childs.len(), 3);
        assert_eq!(root.childs.get(0).unwrap().keys, vec![1, 2]); 
        assert_eq!(root.childs.get(1).unwrap().keys, vec![4]);
        assert_eq!(root.childs.get(2).unwrap().keys, vec![6, 7]);
    }

    #[test]
    fn btree_insert() {
        let mut tree = BTree::new(8);
        for i in 0..200 {
            tree.insert(i, i);
        }
        assert_eq!(tree.len(), 200);

        for i in 0..200 {
            assert_eq!(tree.get(&i), Some(&i));
        }
    }
}
