//! OS-based thread local storage
//!
//! This module provides an implementation of OS-based thread local storage,
//! using the native OS-provided facilities (think `TlsAlloc` or
//! `pthread_setspecific`). The interface of this differs from the other types
//! of thread-local-storage provided in this crate in that OS-based TLS can only
//! get/set pointer-sized data, possibly with an associated destructor.
//!
//! This module also provides two flavors of TLS. One is intended for static
//! initialization, and does not contain a `Drop` implementation to deallocate
//! the OS-TLS key. The other is a type which does implement `Drop` and hence
//! has a safe interface.
//!
//! # Usage
//!
//! This module should likely not be used directly unless other primitives are
//! being built on. Types such as `thread_local::spawn::Key` are likely much
//! more useful in practice than this OS-based version which likely requires
//! unsafe code to interoperate with.
//!
//! # Examples
//!
//! Using a dynamically allocated TLS key. Note that this key can be shared
//! among many threads via an `Arc`.
//!
//! ```ignore (cannot-doctest-private-modules)
//! let key = Key::new(None);
//! assert!(key.get().is_null());
//! key.set(1 as *mut u8);
//! assert!(!key.get().is_null());
//!
//! drop(key); // deallocate this TLS slot.
//! ```
//!
//! Sometimes a statically allocated key is either required or easier to work
//! with, however.
//!
//! ```ignore (cannot-doctest-private-modules)
//! static KEY: StaticKey = INIT;
//!
//! unsafe {
//!     assert!(KEY.get().is_null());
//!     KEY.set(1 as *mut u8);
//! }
//! ```

#![allow(non_camel_case_types)]
#![unstable(feature = "thread_local_internals", issue = "none")]
#![allow(dead_code)]

#[cfg(test)]
mod tests;

use crate::sync::atomic::{self, AtomicUsize, Ordering};
use crate::sys::thread_local_key as imp;

/// A type for TLS keys that are statically allocated.
///
/// This type is entirely `unsafe` to use as it does not protect against
/// use-after-deallocation or use-during-deallocation.
///
/// The actual OS-TLS key is lazily allocated when this is used for the first
/// time. The key is also deallocated when the Rust runtime exits or `destroy`
/// is called, whichever comes first.
///
/// # Examples
///
/// ```ignore (cannot-doctest-private-modules)
/// use tls::os::{StaticKey, INIT};
///
/// // Use a regular global static to store the key.
/// static KEY: StaticKey = INIT;
///
/// // The state provided via `get` and `set` is thread-local.
/// unsafe {
///     assert!(KEY.get().is_null());
///     KEY.set(1 as *mut u8);
/// }
/// ```
pub struct StaticKey {
    /// Inner static TLS key (internals).
    key: AtomicUsize,
    /// Destructor for the TLS value.
    ///
    /// See `Key::new` for information about when the destructor runs and how
    /// it runs.
    dtor: Option<unsafe extern "C" fn(*mut u8)>,
}

/// A type for a safely managed OS-based TLS slot.
///
/// This type allocates an OS TLS key when it is initialized and will deallocate
/// the key when it falls out of scope. When compared with `StaticKey`, this
/// type is entirely safe to use.
///
/// Implementations will likely, however, contain unsafe code as this type only
/// operates on `*mut u8`, a raw pointer.
///
/// # Examples
///
/// ```ignore (cannot-doctest-private-modules)
/// use tls::os::Key;
///
/// let key = Key::new(None);
/// assert!(key.get().is_null());
/// key.set(1 as *mut u8);
/// assert!(!key.get().is_null());
///
/// drop(key); // deallocate this TLS slot.
/// ```
pub struct Key {
    key: imp::Key,
}

/// Constant initialization value for static TLS keys.
///
/// This value specifies no destructor by default.
pub const INIT: StaticKey = StaticKey::new(None);

impl StaticKey {
    #[rustc_const_unstable(feature = "thread_local_internals", issue = "none")]
    pub const fn new(dtor: Option<unsafe extern "C" fn(*mut u8)>) -> StaticKey {
        StaticKey { key: atomic::AtomicUsize::new(0), dtor }
    }

    /// Gets the value associated with this TLS key
    ///
    /// This will lazily allocate a TLS key from the OS if one has not already
    /// been allocated.
    #[inline]
    pub unsafe fn get(&self) -> *mut u8 {
        imp::get(self.key())
    }

    /// Sets this TLS key to a new value.
    ///
    /// This will lazily allocate a TLS key from the OS if one has not already
    /// been allocated.
    #[inline]
    pub unsafe fn set(&self, val: *mut u8) {
        imp::set(self.key(), val)
    }

    #[inline]
    unsafe fn key(&self) -> imp::Key {
        match self.key.load(Ordering::Relaxed) {
            0 => self.lazy_init() as imp::Key,
            n => n as imp::Key,
        }
    }

    unsafe fn lazy_init(&self) -> usize {
        let key = imp::create(self.dtor);
        debug_assert!(key != 0);
        match self.key.compare_exchange(0, key as usize, Ordering::AcqRel, Ordering::Acquire) {
            // The CAS succeeded, so we've created the actual key
            Ok(_) => key as usize,
            // If someone beat us to the punch, use their key instead
            Err(n) => {
                imp::destroy(key);
                n
            }
        }
    }
}

impl Key {
    /// Creates a new managed OS TLS key.
    ///
    /// This key will be deallocated when the key falls out of scope.
    ///
    /// The argument provided is an optionally-specified destructor for the
    /// value of this TLS key. When a thread exits and the value for this key
    /// is non-null the destructor will be invoked. The TLS value will be reset
    /// to null before the destructor is invoked.
    ///
    /// Note that the destructor will not be run when the `Key` goes out of
    /// scope.
    #[inline]
    pub fn new(dtor: Option<unsafe extern "C" fn(*mut u8)>) -> Key {
        Key { key: unsafe { imp::create(dtor) } }
    }

    /// See StaticKey::get
    #[inline]
    pub fn get(&self) -> *mut u8 {
        unsafe { imp::get(self.key) }
    }

    /// See StaticKey::set
    #[inline]
    pub fn set(&self, val: *mut u8) {
        unsafe { imp::set(self.key, val) }
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        unsafe { imp::destroy(self.key) }
    }
}
