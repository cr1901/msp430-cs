#![cfg_attr(not(feature = "std"), no_std)]
#![doc = include_str!("../README.md")]
#![feature(asm_experimental_arch)]

mod mutex;
#[cfg(feature = "std")]
mod std;

use core::marker::PhantomData;

pub use self::mutex::Mutex;

/// Critical section token.
///
/// An instance of this type indicates that the current thread is executing code within a critical
/// section.
#[derive(Clone, Copy, Debug)]
pub struct CriticalSection<'cs> {
    _private: PhantomData<&'cs ()>,
}

impl<'cs> CriticalSection<'cs> {
    /// Creates a critical section token.
    ///
    /// This method is meant to be used to create safe abstractions rather than being directly used
    /// in applications.
    ///
    /// # Safety
    ///
    /// This must only be called when the current thread is in a critical section. The caller must
    /// ensure that the returned instance will not live beyond the end of the critical section.
    ///
    /// The caller must use adequate fences to prevent the compiler from moving the
    /// instructions inside the critical section to the outside of it. Sequentially consistent fences are
    /// suggested immediately after entry and immediately before exit from the critical section.
    ///
    /// Note that the lifetime `'cs` of the returned instance is unconstrained. User code must not
    /// be able to influence the lifetime picked for this type, since that might cause it to be
    /// inferred to `'static`.
    #[inline(always)]
    pub unsafe fn new() -> Self {
        CriticalSection {
            _private: PhantomData,
        }
    }
}

type RawRestoreStateInner = u16;

// We have RawRestoreStateInner and RawRestoreState so that we don't have to copypaste the docs 5 times.
// In the docs this shows as `pub type RawRestoreState = u8` or whatever the selected type is, because
// the "inner" type alias is private.

/// Raw, transparent "restore state".
///
/// This type changes based on which Cargo feature is selected, out of
/// - `restore-state-none` (default, makes the type be `()`)
/// - `restore-state-bool`
/// - `restore-state-u8`
/// - `restore-state-u16`
/// - `restore-state-u32`
/// - `restore-state-u64`
///
/// See [`RestoreState`].
///
/// User code uses [`RestoreState`] opaquely, critical section implementations
/// use [`RawRestoreState`] so that they can use the inner value.
pub type RawRestoreState = RawRestoreStateInner;

/// Opaque "restore state".
///
/// Implementations use this to "carry over" information between acquiring and releasing
/// a critical section. For example, when nesting two critical sections of an
/// implementation that disables interrupts globally, acquiring the inner one won't disable
/// the interrupts since they're already disabled. The impl would use the restore state to "tell"
/// the corresponding release that it does *not* have to reenable interrupts yet, only the
/// outer release should do so.
///
/// User code uses [`RestoreState`] opaquely, critical section implementations
/// use [`RawRestoreState`] so that they can use the inner value.
#[derive(Clone, Copy, Debug)]
pub struct RestoreState(RawRestoreState);

impl RestoreState {
    /// Create an invalid, dummy  `RestoreState`.
    ///
    /// This can be useful to avoid `Option` when storing a `RestoreState` in a
    /// struct field, or a `static`.
    ///
    /// Note that due to the safety contract of [`acquire`]/[`release`], you must not pass
    /// a `RestoreState` obtained from this method to [`release`].
    pub const fn invalid() -> Self {
        return Self(0);
    }
}

/// Acquire a critical section in the current thread.
///
/// This function is extremely low level. Strongly prefer using [`with`] instead.
///
/// Nesting critical sections is allowed. The inner critical sections
/// are mostly no-ops since they're already protected by the outer one.
///
/// # Safety
///
/// - Each `acquire` call must be paired with exactly one `release` call in the same thread.
/// - `acquire` returns a "restore state" that you must pass to the corresponding `release` call.
/// - `acquire`/`release` pairs must be "properly nested", ie it's not OK to do `a=acquire(); b=acquire(); release(a); release(b);`.
/// - It is UB to call `release` if the critical section is not acquired in the current thread.
/// - It is UB to call `release` with a "restore state" that does not come from the corresponding `acquire` call.
/// - It must provide ordering guarantees at least equivalent to a [`core::sync::atomic::Ordering::Acquire`]
///   on a memory location shared by all critical sections, on which the `release` call will do a
///   [`core::sync::atomic::Ordering::Release`] operation.
#[inline(always)]
pub unsafe fn acquire() -> RestoreState {
    #[allow(clippy::unit_arg)]
    RestoreState(_critical_section_1_0_acquire())
}

/// Release the critical section.
///
/// This function is extremely low level. Strongly prefer using [`with`] instead.
///
/// # Safety
///
/// See [`acquire`] for the safety contract description.
#[inline(always)]
pub unsafe fn release(restore_state: RestoreState) {
    #[allow(clippy::unit_arg)]
    _critical_section_1_0_release(restore_state.0)
}

/// Execute closure `f` in a critical section.
///
/// Nesting critical sections is allowed. The inner critical sections
/// are mostly no-ops since they're already protected by the outer one.
///
/// # Panics
///
/// This function panics if the given closure `f` panics. In this case
/// the critical section is released before unwinding.
#[inline]
pub fn with<R>(f: impl FnOnce(CriticalSection) -> R) -> R {
    // Helper for making sure `release` is called even if `f` panics.
    struct Guard {
        state: RestoreState,
    }

    impl Drop for Guard {
        #[inline(always)]
        fn drop(&mut self) {
            unsafe { release(self.state) }
        }
    }

    let state = unsafe { acquire() };
    let _guard = Guard { state };

    unsafe { f(CriticalSection::new()) }
}

/// Methods required for a critical section implementation.
///
/// This trait is not intended to be used except when implementing a critical section.
///
/// # Safety
///
/// Implementations must uphold the contract specified in [`crate::acquire`] and [`crate::release`].
pub unsafe trait Impl {
    /// Acquire the critical section.
    ///
    /// # Safety
    ///
    /// Callers must uphold the contract specified in [`crate::acquire`] and [`crate::release`].
    unsafe fn acquire() -> RawRestoreState;

    /// Release the critical section.
    ///
    /// # Safety
    ///
    /// Callers must uphold the contract specified in [`crate::acquire`] and [`crate::release`].
    unsafe fn release(restore_state: RawRestoreState);
}

/// Set the critical section implementation.
///
/// # Example
///
/// ```
/// # #[cfg(not(feature = "std"))] // needed for `cargo test --features std`
/// # mod no_std {
/// use critical_section::RawRestoreState;
///
/// struct MyCriticalSection;
/// critical_section::set_impl!(MyCriticalSection);
///
/// unsafe impl critical_section::Impl for MyCriticalSection {
///     unsafe fn acquire() -> RawRestoreState {
///         // ...
///     }
///
///     unsafe fn release(restore_state: RawRestoreState) {
///         // ...
///     }
/// }
/// # }

mod sr {
    use core::arch::asm;

    /// Status Register
    #[derive(Clone, Copy, Debug)]
    #[repr(transparent)]
    pub struct Sr {
        bits: u16,
    }

    impl Sr {
        /// Returns the contents of the register as raw bits
        pub fn bits(&self) -> u16 {
            self.bits
        }

        /// General interrupt enable flag
        /// When this bit is set, it enables maskable interrupts.
        /// When it is reset, all maskable interrupts are disabled.
        pub fn gie(&self) -> bool {
            self.bits & (1 << 3) != 0
        }
    }

    /// Reads the CPU register
    #[inline(always)]
    pub fn read() -> Sr {
        let r: u16;
        unsafe {
            asm!("mov R2, {0}", out(reg) r, options(nomem, nostack, preserves_flags));
        }
        Sr { bits: r }
    }
}

mod interrupt {
    use core::arch::asm;

    #[inline(always)]
    pub fn disable() {
        match () {
            #[cfg(target_arch = "msp430")]
            () => unsafe {
                // Do not use `nomem` and `readonly` because prevent subsequent memory accesses from being reordered before interrupts are disabled.
                // Do not use `preserves_flags` because DINT modifies the GIE (global interrupt enable) bit of the status register.
                asm!("dint {{ nop", options(nostack));
            },
            #[cfg(not(target_arch = "msp430"))]
            () => {}
        }
    }

    /// Enables all the interrupts
    ///
    /// # Safety
    ///
    /// - In any function `f()` that calls `enable`, `CriticalSection` or `&CriticalSection` tokens cannot be used in `f()`'s body after the
    ///   call to `enable`. If `f()` owns `CriticalSection` tokens, it is recommended to [`drop`](https://doc.rust-lang.org/nightly/core/mem/fn.drop.html)
    ///   these tokens before calling `enable`.
    #[inline(always)]
    pub unsafe fn enable() {
        match () {
            #[cfg(target_arch = "msp430")]
            () => {
                // Do not use `nomem` and `readonly` because prevent preceding memory accesses from being reordered after interrupts are enabled.
                // Do not use `preserves_flags` because EINT modifies the GIE (global interrupt enable) bit of the status register.
                asm!("nop {{ eint {{ nop", options(nostack));
            }
            #[cfg(not(target_arch = "msp430"))]
            () => {}
        }
    }
}

#[inline]
unsafe fn _critical_section_1_0_acquire() -> RawRestoreState {
    let sr = sr::read().bits();
    interrupt::disable();
    // Safety: Sr is repr(transparent), RawRestoreState is u16, and Sr
    // contains only a single u16. This should be fine.
    core::mem::transmute(sr)
}

#[inline]
unsafe fn _critical_section_1_0_release(sr: RawRestoreState) {
    // Safety: Must be called w/ acquire, otherwise we could receive
    // an invalid Sr (even though internally it's a u16, not all bits
    // are actually used). It would be better to pass Sr as
    // RawRestoreState, but since we can't, this will be acceptable,
    // See acquire() for why this is safe.
    let sr: sr::Sr = core::mem::transmute(sr);

    // If the interrupts were active before our `disable` call, then re-enable
    // them. Otherwise, keep them disabled.
    if sr.gie() {
        interrupt::enable();
    }
}
