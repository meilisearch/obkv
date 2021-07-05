//! `obkv` stands for one-byte key and a value store.
//!
//! The main purpose of this library is to be able to store key value entries
//! where the key can be represented by one byte, this allows a lot of optimizations.
//!
//! ## Example: Creating an `obkv` and iterating over the entries
//!
//! ```
//! use obkv::{KvWriterU16, KvReaderU16};
//!
//! let mut writer = KvWriterU16::memory();
//! writer.insert(0, b"hello").unwrap();
//! writer.insert(1, b"blue").unwrap();
//! writer.insert(255, b"world").unwrap();
//! let obkv = writer.into_inner().unwrap();
//!
//! let mut iter = KvReaderU16::new(&obkv).iter();
//! assert_eq!(iter.next(), Some((0, &b"hello"[..])));
//! assert_eq!(iter.next(), Some((1, &b"blue"[..])));
//! assert_eq!(iter.next(), Some((255, &b"world"[..])));
//! assert_eq!(iter.next(), None);
//! assert_eq!(iter.next(), None); // is it fused?
//! ```

#![warn(missing_docs)]

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

mod varint;

use std::convert::{TryFrom, TryInto};
use std::io::{self, Error, ErrorKind::Other};
use std::iter::Fuse;
use std::marker::PhantomData;

use self::varint::{varint_decode32, varint_encode32};

/// An `obkv` writer that uses `u8` keys.
pub type KvWriterU8<W> = KvWriter<W, u8>;
/// An `obkv` writer that uses `u16` keys.
pub type KvWriterU16<W> = KvWriter<W, u16>;
/// An `obkv` writer that uses `u32` keys.
pub type KvWriterU32<W> = KvWriter<W, u32>;
/// An `obkv` writer that uses `u64` keys.
pub type KvWriterU64<W> = KvWriter<W, u64>;

/// A reader that can read obkvs with `u8` keys.
pub type KvReaderU8<'a> = KvReader<'a, u8>;
/// A reader that can read obkvs with `u16` keys.
pub type KvReaderU16<'a> = KvReader<'a, u16>;
/// A reader that can read obkvs with `u32` keys.
pub type KvReaderU32<'a> = KvReader<'a, u32>;
/// A reader that can read obkvs with `u64` keys.
pub type KvReaderU64<'a> = KvReader<'a, u64>;

/// An `obkv` database writer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KvWriter<W, K> {
    last_key: Option<K>,
    writer: W,
}

impl<K> KvWriter<Vec<u8>, K> {
    /// Creates an in memory `KvWriter` that writes the bytes into a `Vec<u8>`.
    ///
    /// ```
    /// use obkv::KvWriterU16;
    ///
    /// let mut writer = KvWriterU16::memory();
    ///
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    ///
    /// let vec = writer.into_inner().unwrap();
    /// ```
    pub fn memory() -> KvWriter<Vec<u8>, K> {
        KvWriter {
            last_key: None,
            writer: Vec::new(),
        }
    }
}

impl<W, K> KvWriter<W, K> {
    /// Creates a `KvWriter` that writes the bytes into
    /// the given `io::Write` type (e.g. `File`, `Vec<u8>`).
    ///
    /// ```
    /// use obkv::KvWriterU16;
    ///
    /// let mut writer = KvWriterU16::new(Vec::new());
    ///
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    ///
    /// let vec = writer.into_inner().unwrap();
    /// ```
    pub fn new(writer: W) -> KvWriter<W, K> {
        KvWriter {
            last_key: None,
            writer,
        }
    }
}

impl<W: io::Write, K: Key + PartialOrd> KvWriter<W, K> {
    /// Insert a key value pair into the database, keys must be
    /// inserted in order and must be inserted only one time.
    ///
    /// ```
    /// use obkv::KvWriterU16;
    ///
    /// let mut writer = KvWriterU16::new(Vec::new());
    ///
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    ///
    /// let vec = writer.into_inner().unwrap();
    /// ```
    pub fn insert<A: AsRef<[u8]>>(&mut self, key: K, value: A) -> io::Result<()> {
        if self.last_key.map_or(false, |last| key <= last) {
            return Err(Error::new(
                Other,
                "keys must be inserted in order and only one time",
            ));
        }

        let val = value.as_ref();
        let val_len = match val.len().try_into() {
            Ok(len) => len,
            Err(_) => return Err(Error::new(Other, "value length is bigger than u32 MAX")),
        };

        let mut buffer = [0; 5];
        let len_bytes = varint_encode32(&mut buffer, val_len);

        self.writer.write_all(key.to_be_bytes().as_ref())?;
        self.writer.write_all(len_bytes)?;
        self.writer.write_all(val)?;

        self.last_key = Some(key);

        Ok(())
    }

    /// Insert the key value pairs into the database, keys must be
    /// inserted in order and must be inserted only one time.
    pub fn extend<I, V>(&mut self, iter: I) -> io::Result<()>
    where
        I: IntoIterator<Item = (K, V)>,
        V: AsRef<[u8]>,
    {
        for (k, v) in iter {
            self.insert(k, v)?;
        }

        Ok(())
    }

    /// Flushes then extract the internal writer that now contains the keys value entries.
    pub fn into_inner(mut self) -> io::Result<W> {
        self.writer.flush()?;
        Ok(self.writer)
    }

    /// Flushes the internal writer that now contains the keys value entries.
    pub fn finish(self) -> io::Result<()> {
        self.into_inner().map(drop)
    }
}

/// A reader of `obkv` databases.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KvReader<'a, K> {
    bytes: &'a [u8],
    _phantom: PhantomData<K>,
}

impl<'a, K> KvReader<'a, K> {
    /// Construct a reader on top of a memory area.
    ///
    /// ```
    /// use obkv::KvReaderU16;
    ///
    /// let mut iter = KvReaderU16::new(&[]).iter();
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn new(bytes: &[u8]) -> KvReader<K> {
        KvReader {
            bytes,
            _phantom: PhantomData,
        }
    }

    /// Returns the value associated with the given key
    /// or `None` if the key is not present.
    ///
    /// ```
    /// use obkv::{KvWriterU16, KvReaderU16};
    ///
    /// let mut writer = KvWriterU16::memory();
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    /// let obkv = writer.into_inner().unwrap();
    ///
    /// let reader = KvReaderU16::new(&obkv);
    /// assert_eq!(reader.get(0), Some(&b"hello"[..]));
    /// assert_eq!(reader.get(1), Some(&b"blue"[..]));
    /// assert_eq!(reader.get(10), None);
    /// assert_eq!(reader.get(255), Some(&b"world"[..]));
    /// ```
    pub fn get(&self, requested_key: K) -> Option<&'a [u8]>
    where
        K: Key + PartialOrd,
    {
        self.iter()
            .take_while(|(key, _)| *key <= requested_key)
            .find(|(key, _)| *key == requested_key)
            .map(|(_, val)| val)
    }

    /// Returns an iterator over all the keys in the key-value store.
    ///
    /// ```
    /// use obkv::{KvWriterU16, KvReaderU16};
    ///
    /// let mut writer = KvWriterU16::memory();
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    /// let obkv = writer.into_inner().unwrap();
    ///
    /// let mut iter = KvReaderU16::new(&obkv).iter();
    /// assert_eq!(iter.next(), Some((0, &b"hello"[..])));
    /// assert_eq!(iter.next(), Some((1, &b"blue"[..])));
    /// assert_eq!(iter.next(), Some((255, &b"world"[..])));
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next(), None); // is it fused?
    /// ```
    pub fn iter(&self) -> Fuse<KvIter<'a, K>>
    where
        K: Key,
    {
        KvIter {
            bytes: self.bytes,
            offset: 0,
            _phantom: PhantomData,
        }
        .fuse()
    }
}

/// An iterator over a `obkv` database.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KvIter<'a, K> {
    bytes: &'a [u8],
    offset: usize,
    _phantom: PhantomData<K>,
}

impl<'a, K: Key> Iterator for KvIter<'a, K> {
    type Item = (K, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        let key = self
            .bytes
            .get(self.offset..self.offset + K::BYTES::len())
            .and_then(|s| s.try_into().ok())
            .map(K::from_be_bytes)?;

        self.offset += K::BYTES::len();

        let val_len = {
            let mut val_len = 0;
            let bytes = self.bytes.get(self.offset..)?;
            self.offset += varint_decode32(bytes, &mut val_len)?;
            val_len as usize
        };

        let val = self.bytes.get(self.offset..self.offset + val_len)?;
        self.offset += val_len;

        Some((key, val))
    }
}

/// Represents any array of bytes.
pub trait BytesArray: AsRef<[u8]> + for<'a> TryFrom<&'a [u8]> {
    /// Returns the number of bytes this array contains.
    fn len() -> usize;
}

impl<const N: usize> BytesArray for [u8; N] {
    fn len() -> usize {
        N
    }
}

/// A trait that represents a key, this key will be encoded to disk.
pub trait Key: Copy {
    /// The array that will contains the bytes of the key.
    type BYTES: BytesArray;

    /// Returns a slice of the key bytes in its native representation,
    /// in native-endian.
    fn to_be_bytes(&self) -> Self::BYTES;

    /// Returns the key that corresponds to the given bytes.
    fn from_be_bytes(array: Self::BYTES) -> Self;
}

macro_rules! impl_key {
    ($($t:ty),+) => {
        $(impl Key for $t {
            type BYTES = [u8; std::mem::size_of::<$t>()];

            fn to_be_bytes(&self) -> Self::BYTES {
                <$t>::to_be_bytes(*self)
            }

            fn from_be_bytes(array: Self::BYTES) -> Self {
                Self::from_be_bytes(array)
            }
        })+
    };
}

impl_key!(u8, u16, u32, u64);
