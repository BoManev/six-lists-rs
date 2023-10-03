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
                // sanity checks
                debug_assert!(self.back.is_none());
                debug_assert!(self.front.is_none());
                debug_assert!(self.len == 0);

                self.back = Some(new);
            }
            self.front = Some(new);
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
                    debug_assert!(self.len == 1);
                    self.back = None;
                }
                self.len -= 1;
                elem
            })
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

#[cfg(test)]
mod test {
    use super::LinkedList;

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
}