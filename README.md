# mmverify-rs

`mmverify-rs` is currently a verifier for [Metamath](https://us.metamath.org/). However, work is ongoing to make it something more. 😉

## Background

Metamath is a language defining formal systems and specifying proofs within those formal systems.

`mmverify-rs` is one of [many](https://us.metamath.org/other.html#verifiers) verifiers for Metamath. It is somewhat more complicated than the simplest verifiers, such as [mmverify.py](https://github.com/david-a-wheeler/mmverify.py) (~800 lines of Rust vs. ~500 lines of Python), but is also notably faster (~3 seconds vs. ~22 seconds to verify `set.mm` on my machine). It is slower and has less features than fastest verifiers, such as [metamath-knife](https://github.com/metamath/metamath-knife) (~3 seconds vs. ~0.7 seconds to verify `set.mm` with a single thread on my machine), but is also much simpler (~800 lines of Rust vs. ~12,500 lines of Rust).

## Building

Install Rust (the standard method is [rustup](https://rustup.rs/)).

Use cargo to build the bin:

```
cargo build --release
```

The bin will be located at `target/release/mmverify-rs`.

## Running and Testing

Testing was done by verifying that all databases in [set.mm](https://github.com/metamath/set.mm) passed verification.

To test it yourself, clone the [set.mm](https://github.com/metamath/set.mm) repository somewhere convenient, and then run `mmverify-rs` with the path to any of the metamath databases as the sole command line argument.

For example, from within the top level `mmverify-rs` directory:

```
$ git clone https://github.com/metamath/set.mm.git
$ target/release/mmverify-rs set.mm/set.mm
```

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
