//! A custom LazyLock+Cow suitable for holding borrowed, owned or lazy data.

use std::borrow::{Borrow, Cow};
use std::fmt::{Debug, Display};
use std::ops::Deref;
use std::sync::LazyLock;

mod lazy_lock_state {
    use std::cell::UnsafeCell;
    use std::mem::ManuallyDrop;
    use std::ops::Deref;
    use std::sync::Once;

    pub(super) struct LazyLockState<T, S = (), F = fn(S) -> T> {
        once: Once,
        data: UnsafeCell<Data<T, S, F>>,
    }

    union Data<T, S, F> {
        state: ManuallyDrop<(S, F)>,
        value: ManuallyDrop<T>,
    }

    impl<T, S, F: FnOnce(S) -> T> LazyLockState<T, S, F> {
        /// Creates a new lazy value with the given initializing
        /// function.
        #[inline]
        pub const fn new(s: S, f: F) -> LazyLockState<T, S, F> {
            LazyLockState {
                once: Once::new(),
                data: UnsafeCell::new(Data { state: ManuallyDrop::new((s, f)) }),
            }
        }
    }

    impl<T, S, F: FnOnce(S) -> T> Deref for LazyLockState<T, S, F> {
        type Target = T;

        #[inline]
        fn deref(&self) -> &T {
            self.once.call_once(|| {
                // SAFETY: `call_once` only runs this closure once, ever.
                let data = unsafe { &mut *self.data.get() };
                let (s, f) = unsafe { ManuallyDrop::take(&mut data.state) };
                let value = f(s);
                data.value = ManuallyDrop::new(value);
            });

            // SAFETY:
            // * the closure was not called because the Once is poisoned, so this point
            //   is never reached.
            // So `value` has definitely been initialized and will not be modified again.
            unsafe { &*(*self.data.get()).value }
        }
    }

    // We never create a `&F` from a `&LazyLock<T, F>` so it is fine
    // to not impl `Sync` for `F`
    unsafe impl<T: Sync + Send, F: Send, S: Send> Sync for LazyLockState<T, S, F> {}
    unsafe impl<T: Send, F: Send, S: Send> Send for LazyLockState<T, S, F> {}
}

enum MaybeLazyInner<T: 'static + ToOwned + ?Sized, S> {
    LazyState(lazy_lock_state::LazyLockState<T::Owned, S>),
    Lazy(LazyLock<T::Owned>),
    Cow(Cow<'static, T>),
}

/// A custom LazyLock+Cow suitable for holding borrowed, owned or lazy data.
///
/// Technically this structure has 3 states: borrowed, owned and lazy
/// They can all be constructed from the [`MaybeLazy::borrowed`], [`MaybeLazy::owned`] and
/// [`MaybeLazy::lazy`] methods.
#[repr(transparent)]
pub struct MaybeLazy<T: 'static + ToOwned + ?Sized, S = ()> {
    // Inner state.
    //
    // Not to be inlined since we may want in the future to
    // make this struct usable to statics and we might need to
    // workaround const-eval limitation (particulary around drop).
    inner: MaybeLazyInner<T, S>,
}

impl<T: 'static + ?Sized + ToOwned, S> MaybeLazy<T, S> {
    /// Create a [`MaybeLazy`] from an borrowed `T`.
    #[inline]
    pub const fn borrowed(a: &'static T) -> Self {
        MaybeLazy { inner: MaybeLazyInner::Cow(Cow::Borrowed(a)) }
    }

    /// Create a [`MaybeLazy`] from an borrowed `T`.
    #[inline]
    pub const fn owned(a: T::Owned) -> Self {
        MaybeLazy { inner: MaybeLazyInner::Cow(Cow::Owned(a)) }
    }

    /// Create a [`MaybeLazy`] that is lazy by taking a function pointer.
    ///
    /// This function pointer cannot *ever* take a closure. User can potentially
    /// workaround that by using closure-to-fnptr or `const` items.
    #[inline]
    pub const fn lazy(a: fn() -> T::Owned) -> Self {
        MaybeLazy { inner: MaybeLazyInner::Lazy(LazyLock::new(a)) }
    }

    /// Create a [`MaybeLazy`] that is lazy by taking a function pointer and a
    /// state that is pass to the function pointer to faciliate the creation
    /// of the lazy value.
    #[inline]
    pub const fn with_state(s: S, f: fn(S) -> T::Owned) -> Self {
        MaybeLazy { inner: MaybeLazyInner::LazyState(lazy_lock_state::LazyLockState::new(s, f)) }
    }
}

impl<T: 'static + ?Sized + ToOwned<Owned: Clone>, S> Clone for MaybeLazy<T, S> {
    #[inline]
    fn clone(&self) -> Self {
        MaybeLazy {
            inner: MaybeLazyInner::Cow(match &self.inner {
                MaybeLazyInner::LazyState(l) => Cow::Owned((*l).to_owned()),
                MaybeLazyInner::Lazy(f) => Cow::Owned((*f).to_owned()),
                MaybeLazyInner::Cow(c) => c.clone(),
            }),
        }
    }
}

impl<T: 'static + ?Sized + ToOwned<Owned: Default>, S> Default for MaybeLazy<T, S> {
    #[inline]
    fn default() -> MaybeLazy<T, S> {
        MaybeLazy::lazy(T::Owned::default)
    }
}

// `Debug`, `Display` and other traits below are implemented in terms of this `Deref`
impl<T: 'static + ?Sized + ToOwned<Owned: Borrow<T>>, S> Deref for MaybeLazy<T, S> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        match &self.inner {
            MaybeLazyInner::LazyState(l) => (&**l).borrow(),
            MaybeLazyInner::Lazy(f) => (&**f).borrow(),
            MaybeLazyInner::Cow(c) => &*c,
        }
    }
}

impl<T: 'static + ?Sized + ToOwned<Owned: Debug> + Debug, S> Debug for MaybeLazy<T, S> {
    #[inline]
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&**self, fmt)
    }
}

impl<T: 'static + ?Sized + ToOwned<Owned: Display> + Display, S> Display for MaybeLazy<T, S> {
    #[inline]
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&**self, fmt)
    }
}

impl<T: 'static + ?Sized + ToOwned, S> AsRef<T> for MaybeLazy<T, S> {
    #[inline]
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<B: ?Sized + PartialEq<C> + ToOwned, C: ?Sized + ToOwned, S> PartialEq<MaybeLazy<C, S>>
    for MaybeLazy<B, S>
{
    #[inline]
    fn eq(&self, other: &MaybeLazy<C, S>) -> bool {
        PartialEq::eq(&**self, &**other)
    }
}

impl<S> PartialEq<&str> for MaybeLazy<str, S> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        &**self == *other
    }
}

impl<S> From<&'static str> for MaybeLazy<str, S> {
    #[inline]
    fn from(s: &'static str) -> MaybeLazy<str, S> {
        MaybeLazy::borrowed(s)
    }
}
