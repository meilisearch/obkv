//! `obkv` stands for optimized-bytes key and a value store.
//!
//! The main purpose of this library is to be able to store key value entries
//! where the key can be represented by an optimized amount of bytes,
//! this allows a lot of optimizations.
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
//! let reader: &KvReaderU16 = obkv[..].into();
//! let mut iter = reader.iter();
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
use std::mem;

use self::varint::{varint_decode32, varint_encode32};

/// An `obkv` writer that uses `u8` keys.
pub type KvWriterU8<W> = KvWriter<W, u8>;
/// An `obkv` writer that uses `u16` keys.
pub type KvWriterU16<W> = KvWriter<W, u16>;
/// An `obkv` writer that uses `u32` keys.
pub type KvWriterU32<W> = KvWriter<W, u32>;
/// An `obkv` writer that uses `u64` keys.
pub type KvWriterU64<W> = KvWriter<W, u64>;

/// A reader that can read `obkv`s with `u8` keys.
pub type KvReaderU8 = KvReader<u8>;
/// A reader that can read `obkv`s with `u16` keys.
pub type KvReaderU16 = KvReader<u16>;
/// A reader that can read `obkv`s with `u32` keys.
pub type KvReaderU32 = KvReader<u32>;
/// A reader that can read `obkv`s with `u64` keys.
pub type KvReaderU64 = KvReader<u64>;

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

    /// Returns `true` if not entry was written into the writer.
    pub fn is_empty(&self) -> bool {
        self.last_key.is_none()
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

impl<K: Key + PartialOrd> KvWriter<Vec<u8>, K> {
    // TODO find a better name
    pub fn lazy_insert<F>(&mut self, key: K, val_length: u32, val_serialize: F) -> io::Result<()>
    where
        F: FnOnce(&mut [u8]) -> io::Result<()>,
    {
        if self.last_key.map_or(false, |last| key <= last) {
            return Err(Error::new(
                Other,
                "keys must be inserted in order and only one time",
            ));
        }

        let mut buffer = [0; 5];
        let len_bytes = varint_encode32(&mut buffer, val_length);

        self.writer.extend_from_slice(key.to_be_bytes().as_ref());
        self.writer.extend_from_slice(len_bytes);

        let len = self.writer.len();
        self.writer.resize(len + val_length as usize, 0);
        (val_serialize)(&mut self.writer[len..])?;

        self.last_key = Some(key);

        Ok(())
    }
}

/// A reader of `obkv` databases.
#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct KvReader<K> {
    _phantom: PhantomData<K>,
    bytes: [u8],
}

impl<K> KvReader<K> {
    /// Construct a reader on top of a memory area.
    ///
    /// ```
    /// use obkv::KvReaderU16;
    ///
    /// let reader = KvReaderU16::from_slice(&[][..]);
    /// let mut iter = reader.iter();
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn from_slice(bytes: &[u8]) -> &KvReader<K> {
        bytes.into()
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
    /// let reader: &KvReaderU16 = obkv[..].into();
    /// assert_eq!(reader.get(0), Some(&b"hello"[..]));
    /// assert_eq!(reader.get(1), Some(&b"blue"[..]));
    /// assert_eq!(reader.get(10), None);
    /// assert_eq!(reader.get(255), Some(&b"world"[..]));
    /// ```
    pub fn get(&self, requested_key: K) -> Option<&[u8]>
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
    /// let reader: &KvReaderU16 = obkv[..].into();
    /// let mut iter = reader.iter();
    /// assert_eq!(iter.next(), Some((0, &b"hello"[..])));
    /// assert_eq!(iter.next(), Some((1, &b"blue"[..])));
    /// assert_eq!(iter.next(), Some((255, &b"world"[..])));
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next(), None); // is it fused?
    /// ```
    pub fn iter(&self) -> Fuse<KvIter<'_, K>>
    where
        K: Key,
    {
        KvIter {
            _phantom: PhantomData,
            offset: 0,
            bytes: self.as_bytes(),
        }
        .fuse()
    }

    /// Converts a [`KvReader`] to a byte slice.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Converts a [`KvReader`] to a boxed `KvReader`.
    pub fn boxed(&self) -> Box<Self> {
        self.as_bytes().to_vec().into_boxed_slice().into()
    }
}

/// Construct a reader on top of a memory area.
///
/// ```
/// use obkv::KvReaderU16;
///
/// let reader: Box<KvReaderU16> = Vec::new().into_boxed_slice().into();
/// let mut iter = reader.iter();
/// assert_eq!(iter.next(), None);
/// ```
impl<K> From<Box<[u8]>> for Box<KvReader<K>> {
    fn from(boxed_bytes: Box<[u8]>) -> Self {
        unsafe { mem::transmute(boxed_bytes) }
    }
}

impl<K> From<Box<KvReader<K>>> for Box<[u8]> {
    fn from(boxed_bytes: Box<KvReader<K>>) -> Self {
        unsafe { mem::transmute(boxed_bytes) }
    }
}

/// Construct a reader on top of a memory area.
///
/// ```
/// use obkv::KvReaderU16;
///
/// let reader: &KvReaderU16 = [][..].into();
/// let mut iter = reader.iter();
/// assert_eq!(iter.next(), None);
/// ```
impl<'a, K> From<&'a [u8]> for &'a KvReader<K> {
    fn from(bytes: &'a [u8]) -> Self {
        unsafe { mem::transmute(bytes) }
    }
}

impl<'a, K: Key> IntoIterator for &'a KvReader<K> {
    type Item = (K, &'a [u8]);
    type IntoIter = Fuse<KvIter<'a, K>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over a `obkv` database.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KvIter<'a, K> {
    _phantom: PhantomData<K>,
    offset: usize,
    bytes: &'a [u8],
}

impl<'a, K: Key> Iterator for KvIter<'a, K> {
    type Item = (K, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        let key = self
            .bytes
            .get(self.offset..self.offset + K::BYTES_SIZE)
            .and_then(|s| s.try_into().ok())
            .map(K::from_be_bytes)?;

        self.offset += K::BYTES_SIZE;

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

/// A trait that represents a key, this key will be encoded to disk.
pub trait Key: Copy {
    /// The number of bytes the `BYTES` array contains.
    const BYTES_SIZE: usize;
    /// The array that will contain the bytes of the key.
    type BYTES: AsRef<[u8]> + for<'a> TryFrom<&'a [u8]>;

    /// Returns an array of the key bytes in big-endian.
    fn to_be_bytes(&self) -> Self::BYTES;
    /// Returns the key that corresponds to the given bytes array.
    fn from_be_bytes(array: Self::BYTES) -> Self;
}

macro_rules! impl_key {
    ($($t:ty),+) => {
        $(impl Key for $t {
            const BYTES_SIZE: usize = std::mem::size_of::<$t>();
            type BYTES = [u8; Self::BYTES_SIZE];

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

#[cfg(test)]
mod test {
    use crate::{KvReaderU8, KvWriterU8};

    fn reinterpret_box_u8_to_kvreader(boxed_bytes: Box<[u8]>) -> Box<KvReaderU8> {
        // Ensure the conversion from Box<[u8]> to Box<KvReader>
        unsafe { std::mem::transmute(boxed_bytes) }
    }

    // You can construct an obkv and store the KvReader in owned memory.
    #[test]
    fn owned_kvreader() {
        let mut writer = KvWriterU8::memory();
        writer.insert(1, "hello").unwrap();
        writer.insert(10, "world").unwrap();
        writer.insert(20, "poupoupidoup").unwrap();
        let buffer = writer.into_inner().unwrap();

        let boxed = buffer.into_boxed_slice();
        let _boxed: Box<KvReaderU8> = reinterpret_box_u8_to_kvreader(boxed);
    }
}
