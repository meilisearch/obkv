# obkv

A micro key-value store where the key is always one byte.
It is highly inspired by the [KVDS crate](https://lib.rs/crates/kvds).

# Usage

```rust
let mut writer = KvWriter::memory();
writer.insert(0, b"hello").unwrap();
writer.insert(1, b"blue").unwrap();
writer.insert(255, b"world").unwrap();
let obkv = writer.into_inner().unwrap();

let reader = KvReader::new(&obkv);
assert_eq!(reader.get(0), Some(&b"hello"[..]));
assert_eq!(reader.get(1), Some(&b"blue"[..]));
assert_eq!(reader.get(10), None);
assert_eq!(reader.get(255), Some(&b"world"[..]));
```
