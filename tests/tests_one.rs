use repeat_finite::repeat_finite;

fn test_size<T: Clone>() {
    use core::mem::size_of;
    use repeat_finite::RepeatFinite;

    assert_eq!(size_of::<RepeatFinite<T>>(), size_of::<(T, usize)>());
}

#[test]
fn assert_sizes() {
    test_size::<()>();
    test_size::<u8>();
    test_size::<u32>();
    test_size::<u64>();
    test_size::<Box<&[u8]>>();
    test_size::<Vec<u8>>();
    test_size::<String>();
}

#[test]
fn basic() {
    assert_eq!(repeat_finite(0u32, 0).count(), 0);
    assert_eq!(repeat_finite(0u32, 1).count(), 1);
    assert_eq!(repeat_finite(0u32, 2).count(), 2);
}

#[test]
fn collect() {
    assert_eq!(repeat_finite(0u32, 0).collect::<Vec<_>>(), []);
    assert_eq!(repeat_finite(0u32, 1).collect::<Vec<_>>(), [0u32]);
    assert_eq!(repeat_finite(0u32, 2).collect::<Vec<_>>(), [0u32, 0]);
}

#[test]
fn into_inner() {
    let i = repeat_finite(String::new(), 0);
    assert_eq!(i.try_into_inner(), None);

    let i = repeat_finite(String::new(), 1);
    assert_eq!(i.try_into_inner(), Some(String::new()));
}

#[test]
fn noncopy() {
    use std::cell::Cell;

    #[derive(PartialEq, Eq, Debug)]
    struct S {
        cloned: Cell<usize>,
    }

    impl S {
        fn new(x: usize) -> Self {
            Self { cloned: Cell::new(x) }
        }
    }

    impl Clone for S {
        fn clone(&self) -> Self {
            self.cloned.set(self.cloned.get() + 1);
            let cloned = self.cloned.clone();
            Self { cloned }
        }
    }

    let s = S { cloned: Cell::new(0) };
    assert_eq!(
        repeat_finite(s, 3).collect::<Vec<_>>(), 
        [S::new(1), S::new(2), S::new(2)]
    );
}

