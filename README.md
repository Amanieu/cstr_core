cstr_core
=========

[![Build Status](https://travis-ci.org/Amanieu/cstr_core.svg?branch=master)](https://travis-ci.org/Amanieu/cstr_core) [![Crates.io](https://img.shields.io/crates/v/cstr_core.svg)](https://crates.io/crates/cstr_core)

This crate provides an implementation of `CStr` and `CString` which do not depend on the standard library and are suitable for `no_std` environments.

`CString` support is only available if the `alloc` feature is enabled. `CStr` is always available.

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
