# unwrap-overflow-ops

[![Crates.io Version](https://img.shields.io/crates/v/strict-overflow-ops?style=for-the-badge)](https://crates.io/crates/strict-overflow-ops)
[![docs.rs](https://img.shields.io/docsrs/strict-overflow-ops?style=for-the-badge)](https://docs.rs/strict-overflow-ops)

<!-- cargo-rdme start -->

Arithmetic operations that always panic overflow,
providing a polyfill for the [`unwrap_overflow_ops` feature].

To avoid conflicts with the standard library,
methods are prefixed with `unwrap_` instead of `strict_`.
For example [`i32::strict_add`] becomes [`UnwrapOverflowOps::unwrap_add`].

Methods are available through the [`UnwrapOverflowOps`] extension trait.
Some methods are only supported for signed/unsigned integers,
and require [`UnwrapOverflowOpsSigned`] or [`UnwrapOverflowOpsUnsigned`].

Import the entire crate to use all three traits:
`use strict_overflow_ops::*;`

### Example
```rust
use unwrap_overflow_ops::*;

assert_eq!(0i32.unwrap_add(5), 5);
assert_eq!(7u32.unwrap_add_signed(-3), 4);
assert_eq!(-7i32.unwrap_neg(), 7);
```

[`strict_overflow_ops` feature]: https://github.com/rust-lang/rust/issues/118260

<!-- cargo-rdme end -->


## License
Licensed under either of Apache License, Version 2.0 or MIT license at your option.
Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in Serde by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions. 
