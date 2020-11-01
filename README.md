cstr_core
=========

[![Build Status](https://travis-ci.org/Amanieu/cstr_core.svg?branch=master)](https://travis-ci.org/Amanieu/cstr_core) [![Crates.io](https://img.shields.io/crates/v/cstr_core.svg)](https://crates.io/crates/cstr_core)

This crate provides implementations of `CStr` and `CString` which do not depend on the standard library and are suitable for `no_std` environments.

`CString` support is only available if the `alloc` feature is enabled, which requires the `alloc` crate.
`CStr` is always available.

Some hardware targets (e.g. thumbv6m-none-eabi for Cortex M0,M0+) have no support for atomic operations. For these platforms, disable the `arc` feature to omit the parts of the crate that depend on atomic operations. Compatibility with thead-safe code and `Arc<T>` will not be available. 

In addition, the `nightly` feature allows the usage of `CStr::from_bytes_with_nul_unchecked` to be used in a `const` context. However, it requires a nightly version of the compiler.

### Documentation

[https://docs.rs/cstr_core](https://docs.rs/cstr_core)

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
