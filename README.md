# Cron job wrapper for better failure reporting

`cron-wrapper` allows you to configure when your cron jobs produce output.

For example, you might want to normally suppress all output from your cron job
_unless_ there is output on stderr:

```
cron-wrapper --on-error -- /usr/local/bin/my-command -xyz foobar
```

Or, you might want to suppress output _unless_ the command returns a non-zero
exit code:

```
cron-wrapper --on-fail -- /usr/local/bin/my-other-command
```

Or, you might want to suppress output _unless_ the command returns a non-zero
exit code _or_ produces output on stderr:

```
cron-wrapper --on-fail --on-error -- /usr/local/bin/do-something zyx
```

## Installation

```sh
cargo install cron-wrapper
```

If you have [`cargo binstall`][binstall], you can use it to download and install
a binary:

```sh
cargo binstall cron-wrapper
```

Finally, you can download binaries directly from the [GitHub releases
page][releases]. Just extract the archive and copy the file inside into your
`$PATH`, e.g. `/usr/local/bin`. The most common ones are:

  * Linux: [x86-64](https://github.com/danielparks/cron-wrapper/releases/latest/download/cron-wrapper-x86_64-unknown-linux-gnu.tar.gz),
    [ARM](https://github.com/danielparks/cron-wrapper/releases/latest/download/cron-wrapper-aarch64-unknown-linux-musl.tar.gz)
  * macOS: [Intel](https://github.com/danielparks/cron-wrapper/releases/latest/download/cron-wrapper-x86_64-apple-darwin.tar.gz),
    [Apple silicon](https://github.com/danielparks/cron-wrapper/releases/latest/download/cron-wrapper-aarch64-apple-darwin.tar.gz)
  * [Windows on x86-64](https://github.com/danielparks/cron-wrapper/releases/latest/download/cron-wrapper-x86_64-pc-windows-msvc.zip)


## Rust Crate

[![docs.rs](https://img.shields.io/docsrs/cron-wrapper)][docs.rs]
[![Crates.io](https://img.shields.io/crates/v/cron-wrapper)][crates.io]
![Rust version 1.65+](https://img.shields.io/badge/Rust%20version-1.65%2B-success)

## Development status

This is in active development. I am open to [suggestions][issues].

## License

This project dual-licensed under the Apache 2 and MIT licenses. You may choose
to use either.

  * [Apache License, Version 2.0](LICENSE-APACHE)
  * [MIT license](LICENSE-MIT)

### Contributions

Unless you explicitly state otherwise, any contribution you submit as defined
in the Apache 2.0 license shall be dual licensed as above, without any
additional terms or conditions.

[docs.rs]: https://docs.rs/cron-wrapper/latest/cron_wrapper/
[crates.io]: https://crates.io/crates/cron-wrapper
[binstall]: https://github.com/cargo-bins/cargo-binstall
[releases]: https://github.com/danielparks/cron-wrapper/releases
[issues]: https://github.com/danielparks/cron-wrapper/issues
