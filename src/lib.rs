//! `obkv` stands for one-byte key and a value store.
//!
//! The main purpose of this library is to be able to store key value entries
//! where the key can be represented by one byte, this allows a lot of optimizations.
//!
//! ## Example: Creating an `obkv` and iterating over the entries
//!
//! ```
//! use obkv::{KvWriter, KvReader};
//!
//! let mut writer = KvWriter::memory();
//! writer.insert(0u16, b"hello").unwrap();
//! writer.insert(1, b"blue").unwrap();
//! writer.insert(255, b"world").unwrap();
//! let obkv = writer.into_inner().unwrap();
//!
//! let mut iter = KvReader::<u16>::new(&obkv).iter();
//! assert_eq!(iter.next(), Some((0, &b"hello"[..])));
//! assert_eq!(iter.next(), Some((1, &b"blue"[..])));
//! assert_eq!(iter.next(), Some((255, &b"world"[..])));
//! assert_eq!(iter.next(), None);
//! assert_eq!(iter.next(), None); // is it fused?
//! ```

#![warn(missing_docs)]

#[cfg(test)]
#[macro_use] extern crate quickcheck;

mod varint;

use std::convert::TryInto;
use std::io::{self, Error, ErrorKind::Other};
use std::iter::Fuse;
use std::marker::PhantomData;

use self::varint::{varint_encode32, varint_decode32};

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
    /// use obkv::KvWriter;
    ///
    /// let mut writer = KvWriter::memory();
    ///
    /// writer.insert(0u16, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    ///
    /// let vec = writer.into_inner().unwrap();
    /// ```
    pub fn memory() -> KvWriter<Vec<u8>, K> {
        KvWriter { last_key: None, writer: Vec::new() }
    }
}

impl<W, K> KvWriter<W, K> {
    /// Creates a `KvWriter` that writes the bytes into
    /// the given `io::Write` type (e.g. `File`, `Vec<u8>`).
    ///
    /// ```
    /// use obkv::KvWriter;
    ///
    /// let mut writer = KvWriter::new(Vec::new());
    ///
    /// writer.insert(0u16, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    ///
    /// let vec = writer.into_inner().unwrap();
    /// ```
    pub fn new(writer: W) -> KvWriter<W, K> {
        KvWriter { last_key: None, writer }
    }
}

impl<W: io::Write, K: Key + PartialOrd> KvWriter<W, K> {
    /// Insert a key value pair into the database, keys must be
    /// inserted in order and must be inserted only one time.
    ///
    /// ```
    /// use obkv::KvWriter;
    ///
    /// let mut writer = KvWriter::new(Vec::new());
    ///
    /// writer.insert(0u16, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    ///
    /// let vec = writer.into_inner().unwrap();
    /// ```
    pub fn insert<A: AsRef<[u8]>>(&mut self, key: K, value: A) -> io::Result<()> {
        if self.last_key.map_or(false, |last| key <= last) {
            return Err(Error::new(Other, "keys must be inserted in order and only one time"));
        }

        let val = value.as_ref();
        let val_len = match val.len().try_into() {
            Ok(len) => len,
            Err(_) => return Err(Error::new(Other, "value length is bigger than u32 MAX")),
        };

        let mut buffer = [0; 5];
        let len_bytes = varint_encode32(&mut buffer, val_len);

        self.writer.write_all(key.to_ne_bytes())?;
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
    /// use obkv::KvReader;
    ///
    /// let mut iter = KvReader::<u16>::new(&[]).iter();
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn new(bytes: &[u8]) -> KvReader<K> {
        KvReader { bytes, _phantom: PhantomData }
    }

    /// Returns the value associated with the given key
    /// or `None` if the key is not present.
    ///
    /// ```
    /// use obkv::{KvWriter, KvReader};
    ///
    /// let mut writer = KvWriter::memory();
    /// writer.insert(0u16, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    /// let obkv = writer.into_inner().unwrap();
    ///
    /// let reader = KvReader::<u16>::new(&obkv);
    /// assert_eq!(reader.get(0), Some(&b"hello"[..]));
    /// assert_eq!(reader.get(1), Some(&b"blue"[..]));
    /// assert_eq!(reader.get(10), None);
    /// assert_eq!(reader.get(255), Some(&b"world"[..]));
    /// ```
    pub fn get(&self, requested_key: K) -> Option<&'a [u8]>
    where K: Key + PartialOrd,
    {
        self.iter()
            .take_while(|(key, _)| *key <= requested_key)
            .find(|(key, _)| *key == requested_key)
            .map(|(_, val)| val)
    }

    /// Returns an iterator over all the keys in the key-value store.
    ///
    /// ```
    /// use obkv::{KvWriter, KvReader};
    ///
    /// let mut writer = KvWriter::memory();
    /// writer.insert(0u16, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    /// let obkv = writer.into_inner().unwrap();
    ///
    /// let mut iter = KvReader::<u16>::new(&obkv).iter();
    /// assert_eq!(iter.next(), Some((0, &b"hello"[..])));
    /// assert_eq!(iter.next(), Some((1, &b"blue"[..])));
    /// assert_eq!(iter.next(), Some((255, &b"world"[..])));
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next(), None); // is it fused?
    /// ```
    pub fn iter(&self) -> Fuse<KvIter<'a, K>>
    where K: Key,
    {
        KvIter { bytes: self.bytes, offset: 0, _phantom: PhantomData }.fuse()
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
        let key = self.bytes.get(self.offset..self.offset + K::SIZE).map(K::from_ne_bytes)?;
        self.offset += K::SIZE;

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

pub trait Key: Copy {
    const SIZE: usize;

    fn to_ne_bytes(&self) -> &[u8];
    fn from_ne_bytes(slice: &[u8]) -> Self;
}

macro_rules! impl_key {
    ($($t:ty),+) => {
        $(impl Key for $t {
            const SIZE: usize = std::mem::size_of::<$t>();

            fn to_ne_bytes(&self) -> &[u8] {
                bytemuck::bytes_of(self)
            }

            fn from_ne_bytes(slice: &[u8]) -> Self {
                std::convert::TryInto::try_into(slice)
                    .map(<$t>::from_ne_bytes)
                    .unwrap()
            }
        })+
    };
}

impl_key!(u8, u16, u32, u64);
