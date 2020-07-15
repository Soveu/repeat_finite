#![cfg_attr(feature = "trusted_len", feature(trusted_len))]
#![no_std]

//! It is like [repeat](core::iter::repeat), but, you know, finite

use core::num::NonZeroUsize;
use core::iter::{
    Iterator,
    FusedIterator,
    ExactSizeIterator,
};

/// Creates a new iterator that finitely repeats a single element.
///
/// For more details see [RepeatFinite]
#[must_use]
pub fn repeat_finite<T: Clone>(x: T, n: usize) -> RepeatFinite<T> {
    RepeatFinite::new(x, n)
}

/// An iterator that repeats an element a finite amount of times.
///
/// It is roughly equivalent to `repeat(x).take(n)` from std.
/// It is *slightly* more efficient that [Repeat](core::iter::Repeat) +
/// [Take](core::iter::Take) combo, because on last iteration it returns 
/// the element it holds.
///
/// It has the same size as `repeat(x).take(n)` iterator, because instead of
/// being effectively a `(T, usize)` pair, it is an `Option<(T, NonZeroUsize)>`.
/// This structure also allows to implement it with 100% safe code.
/// The only unsafe line of code is the `unsafe impl` for 
/// [TrustedLen](core::iter::TrustedLen), which is not included by default,
/// only with `trusted_len` feature of this crate
///
#[derive(Clone, Debug)]
pub struct RepeatFinite<T: Clone> {
    inner: Option<RepeatFiniteInner<T>>,
}

impl<T: Clone> RepeatFinite<T> {
    /// Creates an iterator that repeats `x` `n` times.\
    /// The same as function [repeat_finite].
    /// ```
    /// # use repeat_finite::*;
    /// let s: String = repeat_finite("asdf", 4).collect();
    /// assert_eq!(s, "asdf".repeat(4));
    /// ```
    #[must_use]
    pub fn new(x: T, n: usize) -> Self {
        let inner = RepeatFiniteInner::new(x, n);
        Self { inner }
    }

    /// Returns the inner element.\
    /// Note, that this is NOT equivalent to `last()`, because
    /// iteration can cause side-effects.
    /// ```
    /// # use repeat_finite::*;
    /// let b = Box::new([1u8,2,3]);
    /// let mut it = repeat_finite(b, 3);
    /// assert_eq!(it.next(), Some(Box::new([1,2,3])));
    /// assert_eq!(it.next(), Some(Box::new([1,2,3])));
    ///
    /// let b2: Box<[u8]> = it.try_into_inner().unwrap();
    /// ```
    #[must_use]
    pub fn try_into_inner(self) -> Option<T> {
        self.inner.map(|inner| inner.value)
    }

    /// Tries to change the number of iteration, returns the new number of iterations.
    /// ```
    /// # use repeat_finite::*;
    /// let b = Box::new([1u8,2,3]);
    /// let mut it = repeat_finite(b, 3);
    /// assert_eq!(it.next(), Some(Box::new([1,2,3])));
    /// assert_eq!(it.next(), Some(Box::new([1,2,3])));
    ///
    /// it.try_set_count(0);
    /// assert_eq!(it.try_into_inner(), None);
    /// ```
    pub fn try_set_count(&mut self, count: usize) -> usize {
        if let Some(n) = NonZeroUsize::new(count) {
            if let Some(inner) = self.inner.as_mut() {
                inner.count = n;
                return count;
            }
            /* else (if self.inner == None) */
            return 0;
        }
        /* else (if n == 0) */
        self.inner.take();
        return 0;
    }

    /// Use this instead of `take()`.\
    /// Effectively sets the counter to min(counter, n) and returns modified self.
    /// ```
    /// # use repeat_finite::*;
    /// let mut it = repeat_finite("asdf", 42).take_n(1);
    /// assert_eq!(it.next(), Some("asdf"));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn take_n(mut self, n: usize) -> Self {
        if let Some(n) = NonZeroUsize::new(n) {
            if let Some(inner) = self.inner.as_mut() {
                inner.count = core::cmp::min(n, inner.count);
            }
            return self;
        }
        /* else (if n == 0) */
        self.inner.take();
        return self;
    }

    /// Use this instead of `cycle()`.
    /// It won't cycle forever, but `usize::MAX` times, so close enough to that.\
    /// If the iterator is exhausted, it stays the same, otherwise counter
    /// is set to `usize::MAX`.
    /// ```
    /// # use repeat_finite::*;
    /// let it = repeat_finite("asdf", 1);
    /// let mut it = it.cycle_nearly_forever();
    ///
    /// assert_eq!(it.next(), Some("asdf"));
    /// assert_eq!(it.next(), Some("asdf"));
    /// assert_eq!(it.next(), Some("asdf"));
    /// assert_eq!(it.next(), Some("asdf"));
    /// # assert_eq!(it.try_set_count(2), 2);
    /// // One eternity later...
    /// assert_eq!(it.next(), Some("asdf"));
    /// assert_eq!(it.next(), Some("asdf"));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn cycle_nearly_forever(mut self) -> Self {
        self.try_set_count(usize::MAX);
        return self;
    }
}

impl<T: Clone> Iterator for RepeatFinite<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let inner = self.inner.as_mut()?;
        let count = inner.count.get();

        if let Some(n) = NonZeroUsize::new(count - 1) {
            inner.count = n;
            return Some(inner.value.clone());
        }

        self.inner.take().map(|inner| inner.value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.inner.as_ref()
            .map_or(0, |inner| inner.count.get());
        (n, Some(n))
    }

    fn count(self) -> usize {
        self.inner.map_or(0, |inner| inner.count.get())
    }

    /* (1.46 nightly) Currently `Cycle` and `Take` have private constructors */
    /*
    fn cycle(self) -> Cycle<Self> {
        self.inner.as_mut()
            .map(|inner| inner.count = NonZeroUsize::new(usize::MAX).unwrap());

        Cycle::new(self)
    }

    fn take(self, n: usize) -> Take<Self> {
        let count = self.len();
        if n < count {
            self.try_set_len(n);
            return Take::new(self, n);
        }

        return Take::new(self, count);
    }
    */
}

impl<T: Clone> FusedIterator for RepeatFinite<T> {}
impl<T: Clone> ExactSizeIterator for RepeatFinite<T> {}

#[cfg(feature = "trusted_len")]
unsafe impl<T: Clone> core::iter::TrustedLen for RepeatFinite<T> {}

impl<T: Clone> Default for RepeatFinite<T> {
    fn default() -> Self {
        Self { inner: None }
    }
}

/* non-public stuff */

#[derive(Clone, Debug)]
struct RepeatFiniteInner<T> {
    value: T,
    count: NonZeroUsize,
}

impl<T> RepeatFiniteInner<T> {
    fn new(value: T, count: usize) -> Option<Self> {
        let count = NonZeroUsize::new(count)?;
        Some(Self { value, count })
    }
}

