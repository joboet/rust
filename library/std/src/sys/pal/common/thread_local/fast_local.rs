use super::lazy::LazyKeyInner;
use crate::cell::{Cell, RefCell};
use crate::{fmt, mem, panic};

#[doc(hidden)]
#[allow_internal_unstable(thread_local_internals, cfg_target_thread_local, thread_local)]
#[allow_internal_unsafe]
#[unstable(feature = "thread_local_internals", issue = "none")]
#[rustc_macro_transparency = "semitransparent"]
pub macro thread_local_inner {
    // used to generate the `LocalKey` value for const-initialized thread locals
    (@key $t:ty, const $init:expr) => {{
        #[inline]
        #[deny(unsafe_op_in_unsafe_fn)]
        // FIXME: Use `SyncUnsafeCell` instead of allowing `static_mut_ref` lint
        #[allow(static_mut_ref)]
        unsafe fn __getit(
            _init: $crate::option::Option<&mut $crate::option::Option<$t>>,
        ) -> $crate::option::Option<&'static $t> {
            const INIT_EXPR: $t = $init;
            // If the platform has support for `#[thread_local]`, use it.
            #[thread_local]
            static mut VAL: $t = INIT_EXPR;

            // If a dtor isn't needed we can do something "very raw" and
            // just get going.
            if !$crate::mem::needs_drop::<$t>() {
                unsafe {
                    return $crate::option::Option::Some(&VAL)
                }
            }

            // 0 == dtor not registered
            // 1 == dtor registered, dtor not run
            // 2 == dtor registered and is running or has run
            #[thread_local]
            static STATE: $crate::cell::Cell<$crate::primitive::u8> = $crate::cell::Cell::new(0);

            // Safety: Performs `drop_in_place(ptr as *mut $t)`, and requires
            // all that comes with it.
            unsafe fn destroy(ptr: *mut $crate::primitive::u8) {
                let old_state = STATE.replace(2);
                $crate::debug_assert_eq!(old_state, 1);
                // Safety: safety requirement is passed on to caller.
                unsafe { $crate::ptr::drop_in_place(ptr.cast::<$t>()); }
            }

            unsafe {
                match STATE.get() {
                    // 0 == we haven't registered a destructor, so do
                    //   so now.
                    0 => {
                        $crate::thread::local_impl::Key::<$t>::register_dtor(
                            $crate::ptr::addr_of_mut!(VAL) as *mut $crate::primitive::u8,
                            destroy,
                        );
                        STATE.set(1);
                        $crate::option::Option::Some(&VAL)
                    }
                    // 1 == the destructor is registered and the value
                    //   is valid, so return the pointer.
                    1 => $crate::option::Option::Some(&VAL),
                    // otherwise the destructor has already run, so we
                    // can't give access.
                    _ => $crate::option::Option::None,
                }
            }
        }

        unsafe {
            $crate::thread::LocalKey::new(__getit)
        }
    }},

    // used to generate the `LocalKey` value for `thread_local!`
    (@key $t:ty, $init:expr) => {
        {
            #[inline]
            fn __init() -> $t { $init }

            #[inline]
            unsafe fn __getit(
                init: $crate::option::Option<&mut $crate::option::Option<$t>>,
            ) -> $crate::option::Option<&'static $t> {
                #[thread_local]
                static __KEY: $crate::thread::local_impl::Key<$t> =
                    $crate::thread::local_impl::Key::<$t>::new();

                unsafe {
                    __KEY.get(move || {
                        if let $crate::option::Option::Some(init) = init {
                            if let $crate::option::Option::Some(value) = init.take() {
                                return value;
                            }
                            if $crate::cfg!(debug_assertions) {
                                $crate::unreachable!("missing default value");
                            }
                        }
                        __init()
                    })
                }
            }

            unsafe {
                $crate::thread::LocalKey::new(__getit)
            }
        }
    },
    ($(#[$attr:meta])* $vis:vis $name:ident, $t:ty, $($init:tt)*) => {
        $(#[$attr])* $vis const $name: $crate::thread::LocalKey<$t> =
            $crate::thread::local_impl::thread_local_inner!(@key $t, $($init)*);
    },
}

#[derive(Copy, Clone)]
enum DtorState {
    Unregistered,
    Registered,
    RunningOrHasRun,
}

// This data structure has been carefully constructed so that the fast path
// only contains one branch on x86. That optimization is necessary to avoid
// duplicated tls lookups on OSX.
//
// LLVM issue: https://bugs.llvm.org/show_bug.cgi?id=41722
pub struct Key<T> {
    // If `LazyKeyInner::get` returns `None`, that indicates either:
    //   * The value has never been initialized
    //   * The value is being recursively initialized
    //   * The value has already been destroyed or is being destroyed
    // To determine which kind of `None`, check `dtor_state`.
    //
    // This is very optimizer friendly for the fast path - initialized but
    // not yet dropped.
    inner: LazyKeyInner<T>,

    // Metadata to keep track of the state of the destructor. Remember that
    // this variable is thread-local, not global.
    dtor_state: Cell<DtorState>,
}

impl<T> fmt::Debug for Key<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Key").finish_non_exhaustive()
    }
}
impl<T> Key<T> {
    pub const fn new() -> Key<T> {
        Key { inner: LazyKeyInner::new(), dtor_state: Cell::new(DtorState::Unregistered) }
    }

    // note that this is just a publicly-callable function only for the
    // const-initialized form of thread locals, basically a way to call the
    // free `register_dtor` function.
    pub unsafe fn register_dtor(a: *mut u8, dtor: unsafe fn(*mut u8)) {
        unsafe {
            register_dtor(a, dtor);
        }
    }

    pub unsafe fn get<F: FnOnce() -> T>(&self, init: F) -> Option<&'static T> {
        // SAFETY: See the definitions of `LazyKeyInner::get` and
        // `try_initialize` for more information.
        //
        // The caller must ensure no mutable references are ever active to
        // the inner cell or the inner T when this is called.
        // The `try_initialize` is dependant on the passed `init` function
        // for this.
        unsafe {
            match self.inner.get() {
                Some(val) => Some(val),
                None => self.try_initialize(init),
            }
        }
    }

    // `try_initialize` is only called once per fast thread local variable,
    // except in corner cases where thread_local dtors reference other
    // thread_local's, or it is being recursively initialized.
    //
    // Macos: Inlining this function can cause two `tlv_get_addr` calls to
    // be performed for every call to `Key::get`.
    // LLVM issue: https://bugs.llvm.org/show_bug.cgi?id=41722
    #[inline(never)]
    unsafe fn try_initialize<F: FnOnce() -> T>(&self, init: F) -> Option<&'static T> {
        // SAFETY: See comment above (this function doc).
        if !mem::needs_drop::<T>() || unsafe { self.try_register_dtor() } {
            // SAFETY: See comment above (this function doc).
            Some(unsafe { self.inner.initialize(init) })
        } else {
            None
        }
    }

    // `try_register_dtor` is only called once per fast thread local
    // variable, except in corner cases where thread_local dtors reference
    // other thread_local's, or it is being recursively initialized.
    unsafe fn try_register_dtor(&self) -> bool {
        match self.dtor_state.get() {
            DtorState::Unregistered => {
                // SAFETY: dtor registration happens before initialization.
                // Passing `self` as a pointer while using `destroy_value<T>`
                // is safe because the function will build a pointer to a
                // Key<T>, which is the type of self and so find the correct
                // size.
                unsafe { register_dtor(self as *const _ as *mut u8, destroy_value::<T>) };
                self.dtor_state.set(DtorState::Registered);
                true
            }
            DtorState::Registered => {
                // recursively initialized
                true
            }
            DtorState::RunningOrHasRun => false,
        }
    }
}

unsafe fn destroy_value<T>(ptr: *mut u8) {
    let ptr = ptr as *mut Key<T>;

    // SAFETY:
    //
    // The pointer `ptr` has been built just above and comes from
    // `try_register_dtor` where it is originally a Key<T> coming from `self`,
    // making it non-NUL and of the correct type.
    //
    // Right before we run the user destructor be sure to set the
    // `Option<T>` to `None`, and `dtor_state` to `RunningOrHasRun`. This
    // causes future calls to `get` to run `try_initialize_drop` again,
    // which will now fail, and return `None`.
    unsafe {
        let value = (*ptr).inner.take();
        (*ptr).dtor_state.set(DtorState::RunningOrHasRun);
        drop(value);
    }
}

#[thread_local]
static DTORS: RefCell<Vec<(*mut u8, unsafe fn(*mut u8))>> = RefCell::new(Vec::new());

// Ensure this can never be inlined on Windows because otherwise this may break
// in dylibs. See #44391.
#[cfg_attr(windows, inline(never))]
unsafe fn register_dtor(t: *mut u8, dtor: unsafe fn(*mut u8)) {
    // Ensure that destructors are run on thread exit.
    crate::sys::thread_local_guard::activate();

    let mut dtors = match DTORS.try_borrow_mut() {
        Ok(dtors) => dtors,
        // The only place this function can be called reentrantly is inside the
        // heap allocator. This is currently forbidden.
        Err(_) => rtabort!("the global allocator may not register TLS destructors"),
    };
    dtors.push((t, dtor));
}

/// Called by the platform on thread exit to run all registered destructors.
/// The signature was chosen so that this function may be passed as a callback
/// to platform functions. The argument is ignored.
///
/// # Safety
/// May only be called on thread exit. In particular, no thread locals may
/// currently be referenced.
pub unsafe extern "C" fn run_dtors(_unused: *mut u8) {
    // This function must not unwind. This is ensured by the `extern "C"` ABI,
    // but by catching the unwind, we can print a more helpful message.

    match panic::catch_unwind(|| {
        let dtors = &DTORS;

        loop {
            // Ensure that the `RefMut` guard is not held while the destructor is
            // executed to allow initializing TLS variables in destructors.
            let (t, dtor) = {
                let mut dtors = dtors.borrow_mut();
                match dtors.pop() {
                    Some(entry) => entry,
                    None => break,
                }
            };

            unsafe {
                (dtor)(t);
            }
        }

        // All destructors were run, deallocate the list.
        drop(dtors.replace(Vec::new()));
    }) {
        Ok(()) => {}
        Err(_) => rtabort!("thread local panicked on drop"),
    }
}
