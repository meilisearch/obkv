#[cfg(test)]
#[macro_use] extern crate quickcheck;

mod varint;

use std::convert::TryInto;
use std::io::{self, Error, ErrorKind::Other};
use std::iter::Fuse;

use self::varint::{varint_encode32, varint_decode32};

pub struct KvWriter<W> {
    last_key: Option<u8>,
    writer: W,
}

impl<W> KvWriter<W> {
    pub fn new(writer: W) -> KvWriter<W> {
        KvWriter { last_key: None, writer }
    }
}

impl KvWriter<Vec<u8>> {
    pub fn memory() -> KvWriter<Vec<u8>> {
        KvWriter { last_key: None, writer: Vec::new() }
    }
}

impl<W: io::Write> KvWriter<W> {
    pub fn insert(&mut self, key: u8, value: impl AsRef<[u8]>) -> io::Result<()> {
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

    pub fn into_inner(mut self) -> io::Result<W> {
        self.writer.flush()?;
        Ok(self.writer)
    }

    pub fn finish(self) -> io::Result<()> {
        self.into_inner().map(drop)
    }
}

pub struct KvReader<'a> {
    bytes: &'a [u8],
}

impl<'a> KvReader<'a> {
    pub fn new(bytes: &[u8]) -> KvReader {
        KvReader { bytes }
    }

    pub fn get(&self, requested_key: u8) -> Option<&'a [u8]> {
        self.iter()
            .take_while(|(key, _)| *key <= requested_key)
            .find(|(key, _)| *key == requested_key)
            .map(|(_, val)| val)
    }

    pub fn iter(&self) -> Fuse<KvIter<'a>> {
        KvIter { bytes: self.bytes, offset: 0 }.fuse()
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gets() {
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
    }

    #[test]
    fn iter() {
        let mut writer = KvWriter::memory();
        writer.insert(0, b"hello").unwrap();
        writer.insert(1, b"blue").unwrap();
        writer.insert(255, b"world").unwrap();
        let obkv = writer.into_inner().unwrap();

        let reader = KvReader::new(&obkv);
        let mut iter = reader.iter();
        assert_eq!(iter.next(), Some((0, &b"hello"[..])));
        assert_eq!(iter.next(), Some((1, &b"blue"[..])));
        assert_eq!(iter.next(), Some((255, &b"world"[..])));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None); // is it fused?
    }
}
