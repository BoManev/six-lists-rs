use std::{marker::PhantomData, ptr::NonNull};

// Layout: ... <=> (ptr, A, ptr) <=> (ptr, B, ptr) <=> ...
// Ends on the stack [corner cases]:
// [ptr , ptr] <=> (ptr, A, ptr) <=> (ptr, B, ptr)
//   ^-----------------------------------------^
// Ends using `dumby` nodes:
// [ptr] -> (ptr, ??, ptr) <=> (ptr, A, ptr) <=> (ptr, B, ptr)
//            ^--------------------------------------------^
// [ptr] -> (ptr, ??, ptr) [no corner case]
//            ^--------^
// extra allocation and indirection (cow, stack pinning)
// store value (Option, MaybeUninit, type magic)

pub struct LinkedList<T> {
    front: Link<T>,
    back: Link<T>,
    len: usize,
    /// "as if" we store T by-value
    _ghost: PhantomData<T>,
}

// invarient => no subtyping
// type Link<T> = *mut Node<T>;
type Link<T> = Option<NonNull<Node<T>>>;

struct Node<T> {
    front: Link<T>,
    back: Link<T>,
    elem: T,
}

impl<T> LinkedList<T> {
    pub fn new() -> Self {
        Self {
            front: None,
            back: None,
            len: 0,
            _ghost: PhantomData,
        }
    }

    pub fn push_front(&mut self, elem: T) {
        unsafe {
            let new = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                front: None,
                back: None,
                elem,
            })));
            if let Some(old) = self.front {
                (*old.as_ptr()).front = Some(new);
                (*new.as_ptr()).back = Some(old);
            } else {
                self.back = Some(new);
            }
            self.front = Some(new);
            self.len += 1;
        }
    }

    pub fn push_back(&mut self, elem: T) {
        unsafe {
            let new = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                front: None,
                back: None,
                elem,
            })));
            if let Some(old) = self.back {
                (*old.as_ptr()).back = Some(new);
                (*new.as_ptr()).front = Some(old);
            } else {
                self.front = Some(new);
            }
            self.back = Some(new);
            self.len += 1;
        }
    }

    pub fn pop_front(&mut self) -> Option<T> {
        unsafe {
            self.front.map(|node| {
                let boxed = Box::from_raw(node.as_ptr());
                let elem = boxed.elem;

                self.front = boxed.back;
                if let Some(new) = self.front {
                    (*new.as_ptr()).front = None;
                } else {
                    self.back = None;
                }
                self.len -= 1;
                elem
                // Box is freed and knows T is `taken`
            })
        }
    }

    pub fn pop_back(&mut self) -> Option<T> {
        unsafe {
            self.back.map(|node| {
                let boxed = Box::from_raw(node.as_ptr());
                let elem = boxed.elem;

                self.back = boxed.front;
                if let Some(new) = self.back {
                    (*new.as_ptr()).back = None;
                } else {
                    self.front = None;
                }

                self.len -= 1;
                elem
            })
        }
    }

    pub fn front(&self) -> Option<&T> {
        unsafe { Some(&(*self.front?.as_ptr()).elem) }
    }

    pub fn front_mut(&mut self) -> Option<&mut T> {
        unsafe { self.front.map(|node| &mut (*node.as_ptr()).elem) }
    }

    pub fn back(&self) -> Option<&T> {
        unsafe { Some(&(*self.back?.as_ptr()).elem) }
    }

    pub fn back_mut(&mut self) -> Option<&mut T> {
        unsafe { self.back.map(|node| &mut (*node.as_ptr()).elem) }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_emptry(&self) -> bool {
        self.len == 0
    }

    pub fn clear(&mut self) {
        while let Some(_) = self.pop_front() {}
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            front: self.front,
            back: self.back,
            len: self.len,
            _ghost: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            front: self.front,
            back: self.back,
            len: self.len,
            _ghost: PhantomData,
        }
    }

    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter { list: self }
    }

    pub fn cursor_mut(&mut self) -> CursorMut<T> {
        CursorMut {
            cur: None,
            list: self,
            index: None,
        }
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        self.clear()
    }
}

pub struct Iter<'a, T> {
    front: Link<T>,
    back: Link<T>,
    len: usize,
    _ghost: PhantomData<&'a T>,
}

pub struct IterMut<'a, T> {
    front: Link<T>,
    back: Link<T>,
    len: usize,
    // invarient
    _ghost: PhantomData<&'a mut T>,
}

pub struct IntoIter<T> {
    list: LinkedList<T>,
}

impl<'a, T> IntoIterator for &'a LinkedList<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut LinkedList<T> {
    type IntoIter = IterMut<'a, T>;
    type Item = &'a mut T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T> IntoIterator for LinkedList<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.front.map(|node| unsafe {
                self.len -= 1;
                self.front = (*node.as_ptr()).back;
                &(*node.as_ptr()).elem
            })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.front.map(|node| unsafe {
                self.len -= 1;
                self.front = (*node.as_ptr()).back;
                &mut (*node.as_ptr()).elem
            })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.back.map(|node| unsafe {
                self.len -= 1;
                self.back = (*node.as_ptr()).front;
                &(*node.as_ptr()).elem
            })
        } else {
            None
        }
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.back.map(|node| unsafe {
                self.len -= 1;
                self.back = (*node.as_ptr()).front;
                &mut (*node.as_ptr()).elem
            })
        } else {
            None
        }
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.pop_back()
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.list.len
    }
}

impl<T> Default for LinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Clone for LinkedList<T> {
    fn clone(&self) -> Self {
        let mut new_list = Self::new();
        for elem in self {
            new_list.push_back(elem.clone())
        }
        new_list
    }
}

impl<T> Extend<T> for LinkedList<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for elem in iter {
            self.push_back(elem)
        }
    }
}

impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        list.extend(iter);
        list
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for LinkedList<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq> PartialEq for LinkedList<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }

    fn ne(&self, other: &Self) -> bool {
        self.len() != other.len() || self.iter().ne(other)
    }
}

impl<T: Eq> Eq for LinkedList<T> {}

impl<T: PartialOrd> PartialOrd for LinkedList<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for LinkedList<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other)
    }
}

impl<T: std::hash::Hash> std::hash::Hash for LinkedList<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // prevent prefix collisions
        self.len().hash(state);
        for elem in self {
            elem.hash(state);
        }
    }
}

// Send: type can be safely `send` to another thread
// Sync: type can be safely shared between threads (&Self: Send)
unsafe impl<T: Send> Send for LinkedList<T> {}
unsafe impl<T: Sync> Sync for LinkedList<T> {}

unsafe impl<'a, T: Send> Send for Iter<'a, T> {}
unsafe impl<'a, T: Sync> Sync for Iter<'a, T> {}

unsafe impl<'a, T: Send> Send for IterMut<'a, T> {}
unsafe impl<'a, T: Sync> Sync for IterMut<'a, T> {}
// Note: IntoIter can be auto-derives Send and Sync

pub struct CursorMut<'a, T> {
    cur: Link<T>,
    list: &'a mut LinkedList<T>,
    index: Option<usize>,
}

impl<'a, T> CursorMut<'a, T> {
    pub fn index(&self) -> Option<usize> {
        self.index
    }

    pub fn move_next(&mut self) {
        if let Some(cur) = self.cur {
            unsafe {
                self.cur = (*cur.as_ptr()).back;
                if self.cur.is_some() {
                    *self.index.as_mut().unwrap() += 1;
                } else {
                    // arrived at ghost
                    self.index = None;
                }
            }
        } else if !self.list.is_emptry() {
            // at ghost node, circle to front
            self.cur = self.list.front;
            self.index = Some(0)
        } else {
            // at ghost and empty
        }
    }

    pub fn move_back(&mut self) {
        if let Some(cur) = self.cur {
            unsafe {
                self.cur = (*cur.as_ptr()).front;
                if self.cur.is_some() {
                    *self.index.as_mut().unwrap() -= 1;
                } else {
                    self.index = None;
                }
            }
        } else if !self.list.is_emptry() {
            self.cur = self.list.back;
            self.index = Some(self.list.len - 1)
        } else {
        }
    }

    // make cursor by mut to prevent it from yielding more than 1 value
    pub fn current(&mut self) -> Option<&mut T> {
        unsafe { self.cur.map(|node| &mut (*node.as_ptr()).elem) }
    }

    pub fn peek_next(&mut self) -> Option<&mut T> {
        unsafe {
            self.cur
                .and_then(|node| (*node.as_ptr()).back)
                .map(|node| &mut (*node.as_ptr()).elem)
        }
    }

    pub fn peek_prev(&mut self) -> Option<&mut T> {
        unsafe {
            self.cur
                .and_then(|node| (*node.as_ptr()).front)
                .map(|node| &mut (*node.as_ptr()).elem)
        }
    }

    // Input:
    //      list.front -> A <-> B <-> C <-> D <- list.back
    //                                ^
    //                               cur
    //
    // Output:
    //      list.front -> C <-> D <- list.back
    //                    ^
    //                   cur
    //
    //      return.front -> A <-> B <- return.back
    pub fn split_before(&mut self) -> LinkedList<T> {
        if let Some(cur) = self.cur {
            unsafe {
                let old_len = self.list.len;
                let old_idx = self.index.unwrap();
                let prev = (*cur.as_ptr()).front;

                let new_len = old_len - old_idx;
                let new_front = self.cur;
                let new_back = self.list.back;
                let new_idx = Some(0);

                let out_len = old_len - new_len;
                let out_front = self.list.front;
                let out_back = prev;

                if let Some(_prev) = prev {
                    (*cur.as_ptr()).front = None;
                    (*prev.unwrap().as_ptr()).back = None;
                }

                self.list.len = new_len;
                self.list.front = new_front;
                self.list.back = new_back;
                self.index = new_idx;

                LinkedList {
                    front: out_front,
                    back: out_back,
                    len: out_len,
                    _ghost: PhantomData,
                }
            }
        } else {
            // split at ghost
            std::mem::replace(self.list, LinkedList::default())
        }
    }

    // Input:
    //      list.front -> A <-> B <-> C <-> D <- list.back
    //                                ^
    //                               cur
    //
    // Output:
    //      list.front -> A <-> B <-> C <-> list.back
    //                                ^
    //                               cur
    //
    //      return.front -> D <- return.back
    pub fn split_after(&mut self) -> LinkedList<T> {
        if let Some(cur) = self.cur {
            unsafe {
                let old_len = self.list.len;
                let old_idx = self.index.unwrap();
                let next = (*cur.as_ptr()).back;

                let new_len = old_idx + 1;
                let new_idx = Some(old_idx);
                let new_back = self.cur;
                let new_front = self.list.front;

                let out_len = old_len - new_len;
                let out_front = next;
                let out_back = self.list.back;

                if let Some(_next) = next {
                    (*cur.as_ptr()).back = None;
                    (*next.unwrap().as_ptr()).front = None;
                }

                self.list.len = new_len;
                self.list.front = new_front;
                self.list.back = new_back;
                self.index = new_idx;

                LinkedList {
                    front: out_front,
                    back: out_back,
                    len: out_len,
                    _ghost: PhantomData,
                }
            }
        } else {
            std::mem::replace(self.list, LinkedList::default())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn list_from<T: Clone>(v: &[T]) -> LinkedList<T> {
        v.iter().map(|x| (*x).clone()).collect()
    }
    fn gen_list() -> LinkedList<i32> {
        list_from(&[0, 1, 2, 3, 4, 5, 6])
    }

    #[test]
    fn test_basic_front() {
        let mut list = LinkedList::new();

        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);

        list.push_front(10);
        assert_eq!(list.len(), 1);
        assert_eq!(list.pop_front(), Some(10));
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);

        list.push_front(10);
        assert_eq!(list.len(), 1);
        list.push_front(20);
        assert_eq!(list.len(), 2);
        list.push_front(30);
        assert_eq!(list.len(), 3);
        assert_eq!(list.pop_front(), Some(30));
        assert_eq!(list.len(), 2);
        list.push_front(40);
        assert_eq!(list.len(), 3);
        assert_eq!(list.pop_front(), Some(40));
        assert_eq!(list.len(), 2);
        assert_eq!(list.pop_front(), Some(20));
        assert_eq!(list.len(), 1);
        assert_eq!(list.pop_front(), Some(10));
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn test_iterator() {
        let list = gen_list();
        for (i, elem) in list.iter().enumerate() {
            assert_eq!(i as i32, *elem);
        }

        let mut list = LinkedList::new();
        assert_eq!(list.iter().next(), None);
        list.push_front(4);
        let mut it = list.iter();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next().unwrap(), &4);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_iterator_double_end() {
        let mut list = LinkedList::new();
        assert_eq!(list.iter().next(), None);
        list.push_front(4);
        list.push_front(5);
        list.push_front(6);
        let mut it = list.iter();
        assert_eq!(it.size_hint(), (3, Some(3)));
        assert_eq!(it.next().unwrap(), &6);
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert_eq!(it.next_back().unwrap(), &4);
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next_back().unwrap(), &5);
        assert_eq!(it.next_back(), None);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_rev_iter() {
        let list = gen_list();
        for (i, elem) in list.iter().rev().enumerate() {
            assert_eq!(6 - i as i32, *elem);
        }
        let mut list = LinkedList::new();
        assert_eq!(list.iter().rev().next(), None);
        list.push_front(4);
        let mut it = list.iter().rev();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next().unwrap(), &4);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_mut_iter() {
        let mut list = gen_list();
        let mut len = list.len();
        for (i, elem) in list.iter_mut().enumerate() {
            assert_eq!(i as i32, *elem);
            len -= 1;
        }
        assert_eq!(len, 0);
        let mut list = LinkedList::new();
        assert!(list.iter_mut().next().is_none());
        list.push_front(4);
        list.push_back(5);
        let mut it = list.iter_mut();
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert!(it.next().is_some());
        assert!(it.next().is_some());
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert!(it.next().is_none());
    }

    #[test]
    fn test_ord() {
        let n = list_from(&[]);
        let m = list_from(&[1, 2, 3]);
        assert!(n < m);
        assert!(m > n);
        assert!(n <= n);
        assert!(n >= n);
    }

    #[test]
    fn test_eq() {
        let mut n: LinkedList<u8> = list_from(&[]);
        let mut m = list_from(&[]);
        assert!(n == m);
        n.push_front(1);
        assert!(n != m);
        m.push_back(1);
        assert!(n == m);

        let n = list_from(&[2, 3, 4]);
        let m = list_from(&[1, 2, 3]);
        assert!(n != m);
    }

    #[test]
    fn test_debug() {
        let list: LinkedList<i32> = (0..10).collect();
        assert_eq!(format!("{:?}", list), "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]");

        let list: LinkedList<&str> = vec!["just", "one", "test", "more"]
            .iter()
            .copied()
            .collect();
        assert_eq!(format!("{:?}", list), r#"["just", "one", "test", "more"]"#);
    }

    // variance is how the subtyping of its inputs affects the subtyping of its outputs
    // F is covariant if `F<Sub>` is a subtype of F<Super>
    // - &'a T is covariant over 'a if 'a <: 'b
    // F is contravariant if `F<Super>` is a subtype of F<Sub> (inverted covarience)
    // otherwise F is invariant (no subtyping relationship exists)
    // - &mut T is an invariant over T
    // assert whether LinkedList is send and sync (compiler check)
    #[allow(dead_code)]
    fn assert_thread_safety() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        is_send::<LinkedList<i32>>();
        is_sync::<LinkedList<i32>>();

        is_send::<IntoIter<i32>>();
        is_sync::<IntoIter<i32>>();

        is_send::<Iter<i32>>();
        is_sync::<Iter<i32>>();

        is_send::<IterMut<i32>>();
        is_sync::<IterMut<i32>>();

        fn _linked_list_covariant<'a, T>(x: LinkedList<&'static T>) -> LinkedList<&'a T> {
            x
        }
        fn _iter_covariant<'i, 'a, T>(x: Iter<'i, &'static T>) -> Iter<'i, &'a T> {
            x
        }
        fn _into_iter_covariant<'a, T>(x: IntoIter<&'static T>) -> IntoIter<&'a T> {
            x
        }
    }
}

/// ```compile_fail
/// use six_lists_rs::prod::IterMut;
///
/// fn iter_mut_covariant<'i, 'a, T>(x: IterMut<'i, &'static T>) -> IterMut<'i, &'a T> { x }
/// ```
#[allow(dead_code)]
fn iter_mut_invariant() {}
