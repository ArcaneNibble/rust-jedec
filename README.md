[![Crates.io](https://img.shields.io/crates/v/jedec.svg)](https://crates.io/crates/jedec)
[![Docs.rs](https://img.shields.io/badge/docs.rs-jedec-informational.svg)](https://docs.rs/jedec)

# JEDEC programming file parser/writer

Parse and write `.jed` files for PAL/GAL/CPLD devices. Compatible with `no_std`.

## Parsing

```rust
let parsed = JEDECFile::from_bytes(..., &Quirks::new()).unwrap();

// access bits
parsed.f.get(...);
```

## Writing

```rust
let mut jed = JEDECFile::new(100);
jed.header = Cow::Borrowed(b"File written by example tool\n");
jed.f.set(12345, true);

jed.write_io(..., &Quirks::new()).unwrap();
```
