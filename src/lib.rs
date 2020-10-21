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
//! writer.insert(0, b"hello").unwrap();
//! writer.insert(1, b"blue").unwrap();
//! writer.insert(255, b"world").unwrap();
//! let obkv = writer.into_inner().unwrap();
//!
//! let mut iter = KvReader::new(&obkv).iter();
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

use self::varint::{varint_encode32, varint_decode32};

/// An `obkv` database writer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KvWriter<W> {
    last_key: Option<u8>,
    writer: W,
}

impl KvWriter<Vec<u8>> {
    /// Creates an in memory `KvWriter` that writes the bytes into a `Vec<u8>`.
    ///
    /// ```
    /// use obkv::KvWriter;
    ///
    /// let mut writer = KvWriter::memory();
    ///
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    ///
    /// let vec = writer.into_inner().unwrap();
    /// ```
    pub fn memory() -> KvWriter<Vec<u8>> {
        KvWriter { last_key: None, writer: Vec::new() }
    }
}

impl<W> KvWriter<W> {
    /// Creates a `KvWriter` that writes the bytes into
    /// the given `io::Write` type (e.g. `File`, `Vec<u8>`).
    ///
    /// ```
    /// use obkv::KvWriter;
    ///
    /// let mut writer = KvWriter::new(Vec::new());
    ///
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    ///
    /// let vec = writer.into_inner().unwrap();
    /// ```
    pub fn new(writer: W) -> KvWriter<W> {
        KvWriter { last_key: None, writer }
    }
}

impl<W: io::Write> KvWriter<W> {
    /// Insert a key value pair into the database, keys must be
    /// inserted in order and must be inserted only one time.
    ///
    /// ```
    /// use obkv::KvWriter;
    ///
    /// let mut writer = KvWriter::new(Vec::new());
    ///
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    ///
    /// let vec = writer.into_inner().unwrap();
    /// ```
    pub fn insert<A: AsRef<[u8]>>(&mut self, key: u8, value: A) -> io::Result<()> {
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

        self.writer.write_all(&[key])?;
        self.writer.write_all(len_bytes)?;
        self.writer.write_all(val)?;

        self.last_key = Some(key);

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
pub struct KvReader<'a> {
    bytes: &'a [u8],
}

impl<'a> KvReader<'a> {
    /// Construct a reader on top of a memory area.
    ///
    /// ```
    /// use obkv::KvReader;
    ///
    /// let mut iter = KvReader::new(&[]).iter();
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn new(bytes: &[u8]) -> KvReader {
        KvReader { bytes }
    }

    /// Returns the value associated with the given key
    /// or `None` if the key is not present.
    ///
    /// ```
    /// use obkv::{KvWriter, KvReader};
    ///
    /// let mut writer = KvWriter::memory();
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    /// let obkv = writer.into_inner().unwrap();
    ///
    /// let reader = KvReader::new(&obkv);
    /// assert_eq!(reader.get(0), Some(&b"hello"[..]));
    /// assert_eq!(reader.get(1), Some(&b"blue"[..]));
    /// assert_eq!(reader.get(10), None);
    /// assert_eq!(reader.get(255), Some(&b"world"[..]));
    /// ```
    pub fn get(&self, requested_key: u8) -> Option<&'a [u8]> {
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
    /// writer.insert(0, b"hello").unwrap();
    /// writer.insert(1, b"blue").unwrap();
    /// writer.insert(255, b"world").unwrap();
    /// let obkv = writer.into_inner().unwrap();
    ///
    /// let mut iter = KvReader::new(&obkv).iter();
    /// assert_eq!(iter.next(), Some((0, &b"hello"[..])));
    /// assert_eq!(iter.next(), Some((1, &b"blue"[..])));
    /// assert_eq!(iter.next(), Some((255, &b"world"[..])));
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next(), None); // is it fused?
    /// ```
    pub fn iter(&self) -> Fuse<KvIter<'a>> {
        KvIter { bytes: self.bytes, offset: 0 }.fuse()
    }
}

/// An iterator over a `obkv` database.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KvIter<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Iterator for KvIter<'a> {
    type Item = (u8, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        let key = *self.bytes.get(self.offset)?;
        self.offset += 1;

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
