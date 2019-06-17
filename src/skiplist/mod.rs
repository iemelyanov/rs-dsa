extern crate rand;

use rand::Rng;
use std::cmp::Ord;
use std::ptr;
use std::mem;
use std::marker;

struct NodePtr<T> {
    p: *mut T,
}

impl<T> Copy for NodePtr<T> {}

impl<T> Clone for NodePtr<T> {
    fn clone(&self) -> NodePtr<T> {
        *self
    }
}

impl<T> NodePtr<T> {
    #[inline]
    fn some(n: &mut T) -> NodePtr<T> {
        NodePtr { p: n }
    }

    #[inline]
    fn none() -> NodePtr<T> {
        NodePtr { p: ptr::null_mut() }
    }

    #[inline]
    fn resolve<'a>(&self) -> Option<&'a T> {
        if self.p.is_null() {
            None
        } else {
            Some(unsafe { &*self.p })
        }
    }

    #[inline]
    fn resolve_mut<'a>(&mut self) -> Option<&'a mut T> {
        if self.p.is_null() {
            None
        } else {
            Some(unsafe { &mut *self.p })
        }
    }
}

struct Node<K, V> {
    key: Option<K>,
    val: Option<V>,
    forward: Vec<NodePtr<Node<K, V>>>,
}

impl<K, V> Node<K, V> {
    fn new(k: K, v: V, height: usize) -> Self {
        let mut forward = Vec::with_capacity(height);
        for _ in 0..height {
            forward.push(NodePtr::none());
        }

        Node {
            key: Some(k),
            val: Some(v),
            forward: forward,
        }
    }

    fn new_head(height: usize) -> Self {
        let mut forward = Vec::with_capacity(height);
        for _ in 0..height {
            forward.push(NodePtr::none());
        }

        Node {
            key: None,
            val: None,
            forward: forward,
        }
    }
}

pub struct Iter<'a, K: 'a, V: 'a> {
    head: NodePtr<Node<K, V>>,
    len: usize,
    marker: marker::PhantomData<&'a Node<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            None
        } else {
            self.head.resolve().map(|node| {
                self.len -= 1;
                self.head = node.forward[0];
                (node.key.as_ref().unwrap(), node.val.as_ref().unwrap())
            })
        }
    }
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    head: NodePtr<Node<K, V>>,
    len: usize,
    marker: marker::PhantomData<&'a mut Node<K, V>>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            None
        } else {
            self.head.resolve_mut().map(|node| {
                self.len -= 1;
                self.head = node.forward[0];
                (node.key.as_ref().unwrap(), node.val.as_mut().unwrap())
            })
        }
    }
}

pub struct SkipList<K, V> {
    head: NodePtr<Node<K, V>>,
    len: usize,
    max_level: usize,
    rng: rand::prelude::ThreadRng,
}

impl<K, V> SkipList<K, V> where K: Ord,
{
    pub fn new(max_level: usize) -> Self {
        let node = unsafe {
            Box::leak(Box::new(Node::new_head(max_level)))
        };

        SkipList {
            head: NodePtr::some(node),
            len: 0,
            max_level: max_level,
            rng: rand::thread_rng(),
        }
    }

    pub fn append(&mut self, k: K, v: V) {
        let mut prev_node_ptrs: Vec<NodePtr<Node<K, V>>> = Vec::with_capacity(self.max_level);
        for _ in 0..self.max_level {
            prev_node_ptrs.push(NodePtr::none());
        }

        let mut curr_node_ptr = self.head;

        for i in (0..self.max_level).rev() {
            while let Some(node) = curr_node_ptr.resolve_mut() {
                match node.forward[i].resolve_mut() {
                    Some(x) => {
                        if *x.key.as_ref().unwrap() == k {
                            x.val = Some(v);
                            return;
                        }
                        
                        if *x.key.as_ref().unwrap() < k {
                            curr_node_ptr = node.forward[i];
                        } else {
                            break;
                        }
                    }
                    None => break,
                }
            }
            prev_node_ptrs[i] = curr_node_ptr;
        }

        let mut level = 1;
        let branching = 2;
        while level < self.max_level && ((self.rng.gen::<i32>() % branching) == 0) {
            level += 1;
        }

        let new_node = Box::leak(Box::new(Node::new(k, v, level)));

        for i in 0..level {
            prev_node_ptrs[i].resolve_mut().map(|n| {
                new_node.forward[i] = n.forward[i];
                n.forward[i] = NodePtr::some(new_node)
            });
        }

        self.len += 1;
    }

    pub fn get(&self, k: &K) -> Option<&V> {
        let mut curr_node_ptr = self.head;

        for i in (0..self.max_level).rev() {
            while let Some(node) = curr_node_ptr.resolve() {
                match node.forward[i].resolve() {
                    Some(x) => {
                        if *x.key.as_ref().unwrap() == *k {
                            return x.val.as_ref();
                        }
                        
                        if *x.key.as_ref().unwrap() < *k {
                            curr_node_ptr = node.forward[i];
                        } else {
                            break;
                        }
                    }
                    None => break,
                }
            }
        }

        None
    }

    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        let mut curr_node_ptr = self.head;

        for i in (0..self.max_level).rev() {
            while let Some(node) = curr_node_ptr.resolve_mut() {
                match node.forward[i].resolve_mut() {
                    Some(x) => {
                        if *x.key.as_ref().unwrap() == *k {
                            return x.val.as_mut();
                        }
                        
                        if *x.key.as_ref().unwrap() < *k {
                            curr_node_ptr = node.forward[i];
                        } else {
                            break;
                        }
                    }
                    None => break,
                }
            }
        }

        None
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            head: self.head.resolve().unwrap().forward[0],
            len: self.len,
            marker: marker::PhantomData,
        }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            head: self.head.resolve_mut().unwrap().forward[0],
            len: self.len,
            marker: marker::PhantomData,
        }
    }
}

impl<K, V> Drop for SkipList<K, V> {
    fn drop(&mut self) {
        let mut next_node_ptr = self.head;
        while let Some(node) = next_node_ptr.resolve_mut() {
            next_node_ptr = node.forward[0];
            unsafe { Box::from_raw(node) };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::SkipList;

    #[test]
    fn test_append() {
        let mut sl = SkipList::new(1 << 5);
        assert_eq!(sl.len(), 0);
        sl.append(2, "q");
        assert_eq!(sl.len(), 1);
        sl.append(0, "w");
        assert_eq!(sl.len(), 2);
        sl.append(1, "e");
        assert_eq!(sl.len(), 3);

        assert_eq!(sl.get(&2), Some(&"q"));
        assert_eq!(sl.get(&0), Some(&"w"));
        assert_eq!(sl.get(&1), Some(&"e"));

        sl.append(1, "z");
        assert_eq!(sl.len(), 3);
        assert_eq!(sl.get(&1), Some(&"z"));
    }

    #[test]
    fn test_iterators() {
        let mut sl = SkipList::new(1 << 5);
        sl.append(0, "q");
        sl.append(1, "w");
        sl.append(2, "e");

        let mut iter = sl.iter();
        assert_eq!(iter.next(), Some((&0, &"q")));
        assert_eq!(iter.next(), Some((&1, &"w")));
        assert_eq!(iter.next(), Some((&2, &"e")));
        assert_eq!(iter.next(), None);

        let mut iter_mut = sl.iter_mut();
        assert_eq!(iter_mut.next(), Some((&0, &mut "q")));
        assert_eq!(iter_mut.next(), Some((&1, &mut "w")));
        assert_eq!(iter_mut.next(), Some((&2, &mut "e")));
        assert_eq!(iter_mut.next(), None);
    }

    #[test]
    fn test_lots_of_appends() {
        let mut sl = SkipList::new(1 << 5);

        for i in 0..100 {
            sl.append(
                "key_".to_string() + &i.to_string(),
                "val_".to_string() + &i.to_string(),
            );
        }

        for i in 0..100 {
            assert_eq!(
                sl.get(&("key_".to_string() + &i.to_string())),
                Some(&("val_".to_string() + &i.to_string()))
            );
        }
    }
}
