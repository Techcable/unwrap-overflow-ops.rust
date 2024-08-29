//! Arithmetic operations that always panic overflow,
//! providing a polyfill for the [`unwrap_overflow_ops` feature].
//!
//! To avoid conflicts with the standard library,
//! methods are prefixed with `unwrap_` instead of `strict_`.
//! For example [`i32::strict_add`] becomes [`UnwrapOverflowOps::unwrap_add`].
//!
//! Methods are available through the [`UnwrapOverflowOps`] extension trait.
//! Some methods are only supported for signed/unsigned integers,
//! and require [`UnwrapOverflowOpsSigned`] or [`UnwrapOverflowOpsUnsigned`].
//!
//! Import the entire crate to use all three traits:
//! `use strict_overflow_ops::*;`
//!
//! ## Example
//! ```
//! use unwrap_overflow_ops::*;
//!
//! assert_eq!(0i32.unwrap_add(5), 5);
//! assert_eq!(7u32.unwrap_add_signed(-3), 4);
//! assert_eq!(-7i32.unwrap_neg(), 7);
//! ```
//!
//! [`strict_overflow_ops` feature]: https://github.com/rust-lang/rust/issues/118260
#![deny(missing_docs)]
#![no_std]
use core::fmt::Debug;

macro_rules! _stringify_or_default {
    (default: $default:tt; $val:ident) => (stringify!($val));
    (default: $default:tt;) => ($default);
}

macro_rules! unwrap_num_ops {
    ($($op:ident {
        $(arg: $arg:ty,)?
        res: $res:ty,
        begin_doc: $begin_doc:literal,
        basic_example: $basic_example:literal,
        panic_example: $panic_example:literal,
        $(example_type: $example_type:ident,)?
    },)+ $(,)?) => (paste::paste! {$(
        #[doc = $begin_doc]
        ///
        /// This is a polyfill for the [`strict_overflow_ops` feature],
        #[doc = concat!(
            "which offers equivalent methods for each primitive integer type (ex. [`",
             _stringify_or_default!(default: "i32"; $($example_type)*),
             "::strict_",
             stringify!($op),
             "`])."
        )]
        ///
        /// [`strict_overflow_ops` feature]: https://github.com/rust-lang/rust/issues/118260
        ///
        /// # Panics
        /// This function will always panic on overflow,
        /// regardless of whether overflow checks are enabled.
        ///
        /// # Examples
        /// Basic usage:
        ///
        /// ```
        /// use unwrap_overflow_ops::*;
        #[doc = $basic_example]
        /// ```
        ///
        /// The following panics because of overflow:
        ///
        /// ```should_panic
        /// use unwrap_overflow_ops::*;
        #[doc = $panic_example]
        /// ```
        #[must_use = "this returns the result of the operation, without modifying the original"]
        fn [<unwrap_ $op>](self, $(arg: $arg)*) -> $res;
    )*});

}


/// An extension trait for arithmetic operations
/// that are guaranteed to panic on overflow.
///
/// This is a polyfill for the [`strict_overflow_ops` feature].
///
/// These operations are only implemented for primitive integer types.
///
/// [`strict_overflow_ops` feature]: https://github.com/rust-lang/rust/issues/118260
///
/// ## Safety
/// These methods are guarenteed to check for overflow,
/// regardless of compiler settings and `cfg!(...)` flags.
///
/// The correctness of these methods can be relied upon for memory safety.
pub unsafe trait UnwrapOverflowOps: Copy + Debug + Sized + sealed::Sealed {
    unwrap_num_ops! {
        add {
            arg: Self,
            res: Self,
            begin_doc: "Strict integer addition. Computes `self + rhs`, panicking if overflow occurred.",
            basic_example: "assert_eq!((i32::MAX - 2).unwrap_add(1), i32::MAX - 1);",
            panic_example: "let _ = (i32::MAX - 2).unwrap_add(3);",
        },
        sub {
            arg: Self,
            res: Self,
            begin_doc: "Strict integer subtraction. Computes `self - rhs`, panicking if overflow occurred.",
            basic_example: "assert_eq!((i32::MIN + 2).unwrap_sub(1), i32::MIN + 1);",
            panic_example: "let _ = (i32::MIN + 2).unwrap_sub(3);",
        },
        mul {
            arg: Self,
            res: Self,
            begin_doc: "Strict integer multiplication. Computes `self * rhs`, panicking if overflow occurred.",
            basic_example: "assert_eq!(i32::MAX.unwrap_mul(1), i32::MAX);",
            panic_example: "let _ = i32::MAX.unwrap_mul(2);",
        },
        div {
            arg: Self,
            res: Self,
            begin_doc: "Strict integer division. Computes `self / rhs`, panicking if overflow occurred.",
            basic_example: "assert_eq!((i32::MIN + 1).unwrap_div(-1), 2147483647);",
            panic_example: "let _ = i32::MIN.unwrap_div(-1);",
        },
        rem {
            arg: Self,
            res: Self,
            begin_doc: "Strict integer remainder. Computes `self % rhs`, panicking if the division results in overflow.",
            basic_example: "assert_eq!(5i32.unwrap_rem(2), 1);",
            panic_example: "let _ = 5i32.unwrap_rem(0);",
        },
        shr {
            arg: u32,
            res: Self,
            begin_doc: "Strict shift right. Computes `self >> rhs`, panicking `rhs` is larger than or equal to the number of bits in `self`.",
            basic_example: "assert_eq!(0x10i32.unwrap_shr(4), 0x1);",
            panic_example: "let _ = 0x10i32.unwrap_shr(128);",
        },
        shl {
            arg: u32,
            res: Self,
            begin_doc: "Strict shift left. Computes self << rhs, panicking if `rhs` is larger than or equal to the number of bits in `self`.",
            basic_example: "assert_eq!(0x1i32.unwrap_shl(4), 0x10);",
            panic_example: "let _ = 0x1i32.unwrap_shl(129);",
        },
        pow {
            arg: u32,
            res: Self,
            begin_doc: "Strict exponentiation. Computes `self.pow(exp)`, panicking if overflow occurred.",
            basic_example: "assert_eq!(8i32.unwrap_pow(2), 64);",
            panic_example: "let _ = i32::MAX.unwrap_pow(2);",
        },
    }
}

/// An extension trait for signed arithmetic operations
/// that are guaranteed to panic on overflow.
///
/// This implements operations specific to signed integers,
/// the [`UnwrapOverflowOps`] trait is for operations supported bya ll integers.
///
/// This is a polyfill for the [`strict_overflow_ops` feature].
///
/// These operations are only implemented for primitive integer types.
///
/// [`strict_overflow_ops` feature]: https://github.com/rust-lang/rust/issues/118260
/// ## Safety
/// These methods are guarenteed to check for overflow,
/// regardless of compiler settings and `cfg!(...)` flags.
///
/// The correctness of these methods can be relied upon for memory safety.
pub unsafe trait UnwrapOverflowOpsSigned: UnwrapOverflowOps {
    /// The unsigned integer type with the same size
    type Unsigned: UnwrapOverflowOpsUnsigned;
    unwrap_num_ops! {
        add_unsigned {
            arg: Self::Unsigned,
            res: Self,
            begin_doc: "Strict addition with an unsigned integer. Computes `self + rhs`, panicking if overflow occurred.",
            basic_example: "assert_eq!(1i32.unwrap_add_unsigned(2), 3);",
            panic_example: "let _ = 1u32.unwrap_add_signed(-2);",
        },
        sub_unsigned {
            arg: Self::Unsigned,
            res: Self,
            begin_doc: "Strict subtraction with an unsigned integer. Computes `self - rhs`, panicking if overflow occurred.",
            basic_example: "assert_eq!(1i32.unwrap_sub_unsigned(2), -1);",
            panic_example: "let _ = (i32::MIN + 2).unwrap_sub_unsigned(3);",
        },
        neg {
            res: Self,
            begin_doc: "Strict negation. Computes `-self`, panicking if `self == MIN`.",
            basic_example: "assert_eq!(5i32.unwrap_neg(), -5);",
            panic_example: "let _ = i32::MIN.unwrap_neg();",
        },
    }
}

/// An extension trait for unsigned arithmetic operations
/// that are guaranteed to panic on overflow.
///
/// This implements operations specific to unsigned integers,
/// the [`UnwrapOverflowOps`] trait is for operations supported by all integers.
///
/// This is a polyfill for the [`strict_overflow_ops` feature].
///
/// These operations are only implemented for primitive integer types.
///
/// [`strict_overflow_ops` feature]: https://github.com/rust-lang/rust/issues/118260
///
/// ## Safety
/// These methods are guarenteed to check for overflow,
/// regardless of compiler settings and `cfg!(...)` flags.
///
/// The correctness of these methods can be relied upon for memory safety.
pub unsafe trait UnwrapOverflowOpsUnsigned: UnwrapOverflowOps {
    /// The signed integer type with the same size
    type Signed: UnwrapOverflowOpsSigned;
    unwrap_num_ops! {
        add_signed {
            arg: Self::Signed,
            res: Self,
            begin_doc: "Strict addition with a signed integer. Computes `self + rhs`, panicking if overflow occurred.",
            basic_example: "assert_eq!(1u32.unwrap_add_signed(2), 3);",
            panic_example: "let _ = 1u32.unwrap_add_signed(-2);",
            example_type: u32,
        },
    }
}
macro_rules! common_methods_impl {
    () => (common_methods_impl! {
        add(Self) -> Self,
        sub(Self) -> Self,
        mul(Self) -> Self,
        div(Self) -> Self,
        rem(Self) -> Self,
        shr(u32) -> Self,
        shl(u32) -> Self,
        pow(u32) -> Self,
    });
    ($($op:ident($arg:ty) -> $res:ty),+ $(,)?) => (paste::paste! {$(
        #[inline]
        #[track_caller]
        fn [<unwrap_ $op>](self, other: $arg) -> $res {
            match self.[<checked_ $op>](other) {
                Some(res) => res,
                None => overflow_ops::$op(),
            }
        }
    )*});

}
macro_rules! impl_signed_ints {
    ($($size:tt),+) => (paste::paste!{ $(
        unsafe impl UnwrapOverflowOps for [<i $size>] {
            common_methods_impl!();
        }
        unsafe impl UnwrapOverflowOpsSigned for [<i $size>] {
            type Unsigned = [<u $size>];
            common_methods_impl! {
                add_unsigned(Self::Unsigned) -> Self,
                sub_unsigned(Self::Unsigned) -> Self,
            }

            #[inline]
            #[track_caller]
            fn unwrap_neg(self) -> Self {
                match self.checked_neg() {
                    Some(res) => res,
                    None => overflow_ops::neg(),
                }
            }
        }
        impl sealed::Sealed for [<i $size>] {}
    )* });
}
impl_signed_ints!(8, 16, 32, 64, 128, size);
macro_rules! impl_unsigned_ints {
    ($($size:tt),+) => (paste::paste!{ $(
        unsafe impl UnwrapOverflowOps for [<u $size>] {
            common_methods_impl!();
        }

        unsafe impl UnwrapOverflowOpsUnsigned for [<u $size>] {
            type Signed = [<i $size>];
            common_methods_impl!(add_signed(Self::Signed) -> Self);
        }
        impl sealed::Sealed for [<u $size>] {}
    )* })
}
impl_unsigned_ints!(8, 16, 32, 64, 128, size);

mod sealed {
    pub trait Sealed {}
}

/// Fallback functions for panicking on overflow.
///
/// Mostly a reimplementation of the stdlib
/// private module `core::src::num::overflow_panic`.
mod overflow_ops {
    macro_rules! overflow_panic_msg {
        ($($op:ident => $name:literal),+ $(,)?) => {$(
            #[cold]
            #[track_caller]
            pub fn $op() -> ! {
                panic!(concat!("attempt to ", $name, " with overflow"))
            }
        )*};
    }

    overflow_panic_msg! {
        add => "add",
        sub => "subtract",
        mul => "multiply",
        div => "divide",
        rem => "calculate the remainder",
        neg => "negate",
        shr => "shift right",
        shl => "shift left",
        pow => "take integer power",
    }

    // alias used by macros
    pub use self::add as add_signed;
    pub use self::add as add_unsigned;
    pub use self::sub as sub_unsigned;
}

