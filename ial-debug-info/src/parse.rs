// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! functionality relating to reading and writing [`DebugInfo`]
//!
//! First, the file begins with a 7-byte [magic sequence][MAGIC] used to identify it as a file
//! containing encoded IAL [`DebugInfo`], then the [version number][VERSION], then the [data payload].
//!
//! # Data Payload
//!
//! The data payload is zlib-compressed data. Once decompressed (e.g. with [flate2::ZlibDecoder]),
//! it consists of 2 sections.
//!
//! ## Labels section
//!
//! This section contains the serialized [`DebugInfo::labels`]. It consists of the number of labels
//! within the section, serialized as an [`EncodedSize`], followed by the labels themselves.
//!
//! The serialized labels are structured as follows:
//!
//! | field            | encoded as                                                      |
//! |------------------|-----------------------------------------------------------------|
//! | label text       | length as [`EncodedSize`] followed by raw bytes                 |
//! | span in source   | start as [`EncodedSize`], followed by length as [`EncodedSize`] |
//! | resolved address | [little-endian i64][i64::to_le_bytes]                           |
//!
//! ### Reading a Label
//!
//! To read a serialized label, do the following:
//!
//! 1. Deserialize a number, using the algorithm documented for [`EncodedSize`]s.
//! 2. Read the number of bytes deserialized during step 1.
//!    * Recommended: validate that the bytes are [valid UTF-8].
//!       * This is required to be able to use the text as a [`&str`] in Rust.
//!    * Optional: validate that the bytes are valid identifiers (e.g. with [`valid_ident`]).
//! 3. Deserialize the starting address of the span, using the same algorithm as step 1.
//! 4. Deserialize the length of the span, using the same algorithm as before. Add the span
//!    start from step 3 to get the end of the span
//! 5. Read 8 bytes, and interpret them as a 64-bit signed 2's complement integer, with a
//!    little-endian byte order, to get the address.
//!
//! ## Directives Section
//!
//! This section contains the serialized [`DebugInfo::directives`]. It consists of the number of
//! directives within the section, encoded as an [`EncodedSize`], followed by the directives
//! themselves.
//!
//! The serialized directives are structured as follows:
//!
//! | field          | encoded as                                                      |
//! |----------------|-----------------------------------------------------------------|
//! | directive kind | [`DirectiveKind`] [`as`] [`u8`]                                 |
//! | span in source | start as [`EncodedSize`], followed by length as [`EncodedSize`] |
//! | span in output | start as [`EncodedSize`], followed by length as [`EncodedSize`] |
//!
//! ### Reading a Directive
//!
//! To read a serialized directive, do the following:
//!
//! 1. Read 1 byte as the directive kind.
//!    * If it isn't a valid [`DirectiveKind`] discriminant, then you have invalid debug info.
//! 2. Read the source span, using the same method as steps 3 and 4 of [Reading a Label].
//! 3. Read the output span, using the same method as steps 3 and 4 of [Reading a Label].
//!
//! [data payload]: <#data-payload>
//! [valid UTF-8]: <https://en.wikipedia.org/wiki/UTF-8#Description>
//! [flate2::ZlibDecoder]: <https://docs.rs/flate2/latest/flate2/read/struct.ZlibDecoder.html>
//! [`as`]: <https://doc.rust-lang.org/stable/reference/expressions/operator-expr.html#r-expr.as.enum>
//! [Reading a Label]: <#reading-a-label>

use super::{DebugInfo, DirectiveDebug, DirectiveKind, SimpleSpan};
use chumsky::text::Char;
use ial_ast::util::span;
use std::io::{self, BufRead, Read, Write};

/// the magic bytes for on-disk debug data.
pub const MAGIC: [u8; 7] = *b"\0IALDBG";
/// The debug format version. Version 0 is the format that is described in the [module docs]
///
/// [module docs]: self
pub const VERSION: u8 = 0;

const FLATE_LOWER_THRESHOLD: usize = 4096;
const FLATE_MIDDLE_THRESHOLD: usize = FLATE_LOWER_THRESHOLD * 4;
const FLATE_UPPER_THRESHOLD: usize = FLATE_MIDDLE_THRESHOLD * 4;

/// Check if `text` is a valid identifier
#[must_use]
pub fn valid_ident(text: &str) -> bool {
    let mut chars = text.chars();
    chars.next().is_some_and(|c| c.is_ident_start()) && chars.all(|c| c.is_ident_continue())
}

#[repr(transparent)]
/// Portable binary serialization for unsigned integers of any size, designed for small values
///
/// An "Encoded Size" consists of a non-empty sequence of bytes. The most significant bit in every
/// byte except for the last one is set to `1`, to mark it as a continuation byte.
///
/// To convert an "encoded size" back into an integer value, the following algorithm can be used:
///
/// ```no_run
/// let encoded_size = // ...
///# Box::<ial_debug_info::parse::EncodedSize>::from(0);
/// let mut val = 0;
/// let mut shift = 0;
/// for byte in encoded_size.iter().copied() {
///     val |= (byte & 0x7f) << shift;
///     shift += 7;
/// }
/// ```
///
/// *In fact, the implementation of [`TryFrom<&EncodedSize>`] for [usize] uses that approach, with
/// the addition of overflow checking to ensure that it's less than [`usize::MAX`].*
///
/// An [`EncodedSize`] can be [dereferenced][core::ops::Deref] into a [`[u8]`][slice].
#[derive(PartialEq)]
pub struct EncodedSize([u8]);

impl EncodedSize {
    #[cfg_attr(not(debug_assertions), inline(always))]
    fn panic_if_invalid(slice: &[u8]) {
        let Some(last) = slice.last().copied() else {
            panic!("EncodedSize must not be empty");
        };
        debug_assert_eq!(
            last & 0x80,
            0,
            "Invalid final byte for EncodedSize: 0x{last:02x} (most significant byte is 1)"
        );
        for &byte in &slice[..slice.len() - 1] {
            debug_assert_eq!(
                byte & 0x80,
                0x80,
                "Invalid non-final byte for EncodedSize: 0x{byte:02x} (most significant byte is 0)"
            );
        }
    }

    /// Converts a [`Box<[u8]>`][Box] into a [`Box<EncodedSize>`][EncodedSize]
    ///
    /// # Panics
    ///
    /// * Panics `slice` is empty.
    /// * If `cfg(debug_assertions)` is set, panics if the most significant bit of the final byte
    ///   of `slice` is 1, or if the most significant bit of any other byte of `slice` is 0.
    #[must_use]
    pub fn from_boxed_slice(slice: Box<[u8]>) -> Box<Self> {
        EncodedSize::panic_if_invalid(&slice);
        // SAFETY: this is accepted by Miri, and the same pattern is used in the (unstable)
        // `impl From<Box<[u8]>> for Box<ByteStr>` as of Rust 1.92.0.
        unsafe { Box::from_raw(Box::into_raw(slice) as *mut Self) }
    }

    /// Converts an [`&[u8]`][slice] into an [`&EncodedSize`][EncodedSize]
    ///
    /// # Panics
    ///
    /// * Panics `slice` is empty.
    /// * If `cfg(debug_assertions)` is set, panics if the most significant bit of the final byte
    ///   of `slice` is 1, or if the most significant bit of any other byte of `slice` is 0.
    #[must_use]
    pub fn from_slice(slice: &[u8]) -> &Self {
        EncodedSize::panic_if_invalid(slice);

        #[allow(clippy::ref_as_ptr, reason = "match precedent cited in SAFETY comment")]
        // SAFETY: given the fact that EncodedSize is #[repr(transparent)], and that this construct
        // is used in the (unstable) `core::bstr::ByteStr::from_bytes` as of Rust 1.92.0, this
        // should be safe.
        unsafe {
            &*(slice as *const [u8] as *const EncodedSize)
        }
    }

    /// Create an [`EncodedSize`] inline within `buffer`
    ///
    /// Returns a reference to the [`EncodedSize`]
    pub fn encode_into_vec(buffer: &mut Vec<u8>, size: usize) -> &Self {
        let start = buffer.len();
        encode_size(buffer, size);
        Self::from_slice(&buffer[start..])
    }
}

impl std::ops::Deref for EncodedSize {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[allow(
    clippy::cast_possible_truncation,
    reason = "designed to split a usize into a [u8]"
)]
fn encode_size(vec: &mut Vec<u8>, mut size: usize) {
    while size > 0x7f {
        vec.push((size & 0x7f) as u8 | 0x80);
        size >>= 7;
    }
    vec.push(size as u8);
}

fn read_size<R: BufRead>(reader: &mut R) -> Result<usize, DebugInfoReadError> {
    let mut val = 0;
    let mut shift: u32 = 0;
    let mut bytes = reader.by_ref().bytes();

    loop {
        let b = bytes
            .next()
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "unexpected end of file reading encoded size",
                )
            })
            .flatten()?;
        val |= ((b as usize) & 0x7f)
            .checked_shl(shift)
            .ok_or(DebugInfoReadError::IntSize)?;
        if b & 0x80 == 0x80 {
            shift += 7;
        } else {
            break;
        }
    }
    Ok(val)
}

impl From<usize> for Box<EncodedSize> {
    fn from(value: usize) -> Self {
        let mut bytes = Vec::new();
        encode_size(&mut bytes, value);
        EncodedSize::from_boxed_slice(bytes.into_boxed_slice())
    }
}

// To allow a single docstring for `pub type BitCounter`, define it to be an alias for _BitCounter,
// and define _BitCounter using cfg_if.

#[cfg(any(target_pointer_width = "16", target_pointer_width = "32"))]

type _BitCounter = u32;
#[cfg(not(any(target_pointer_width = "16", target_pointer_width = "32")))]
type _BitCounter = usize;

/// Unsigned integer type for dealing with bit widths
///
/// [`core::num`] uses [u32] for bit counts, but the bit count of an [`EncodedSize`] is dependent on
/// its [`len`][slice::len], which is a [usize].
///
/// This type alias is used to make sure that the larger of the two types is always used, by
/// resolving to [u32] for 16-bit and 32-bit targets, but [usize] for all other targets.
pub type BitCounter = _BitCounter;

/// The minimum bit length needed for [usize] to be able to store an [`EncodedSize`] that was too
/// large to fit.
#[derive(Debug, PartialEq)]
pub struct NeededBits(BitCounter);

/// sanity check to make sure that the right type was selected for [`BitCounter`]
const _: () = assert!(
    BitCounter::BITS
        == if u32::BITS >= usize::BITS {
            u32::BITS
        } else {
            usize::BITS
        },
    "wrong BitCounter type selected"
);

/// An array containing the magic bytes and version number of an IAL debug file
pub const HEADER: [u8; 8] = const {
    let mut header: [u8; 8] = [0; 8];
    let mut i = 0;
    while i < MAGIC.len() {
        header[i] = MAGIC[i];
        i += 1;
    }
    header[i] = VERSION;
    header
};

impl DebugInfo {
    /// Write the debug info into the format described in [the module docs][crate::parse]
    ///
    /// # Errors
    ///
    /// If writing to `f` fails, bubbles up the [`Error`][io::Error].
    pub fn write(self, mut f: impl Write) -> io::Result<()> {
        use flate2::write::ZlibEncoder;
        let DebugInfo { labels, directives } = self;

        f.write_all(&HEADER)?;

        let mut buffer = Vec::new();

        macro_rules! write_span {
            ($span: expr) => {
                encode_size(&mut buffer, $span.start);
                encode_size(&mut buffer, $span.end - $span.start);
            };
        }

        encode_size(&mut buffer, labels.len());

        for (label, addr) in labels {
            encode_size(&mut buffer, label.inner.len());
            buffer.extend(label.inner.as_bytes());
            write_span!(label.span);
            buffer.extend(addr.to_le_bytes());
        }

        encode_size(&mut buffer, directives.len());

        for dir in directives {
            buffer.push(dir.kind as u8);
            write_span!(dir.src_span);
            write_span!(dir.output_span);
        }
        let compression_level = {
            use flate2::Compression;
            match buffer.len().saturating_sub(HEADER.len()) {
                ..FLATE_LOWER_THRESHOLD => Compression::none(),
                FLATE_LOWER_THRESHOLD..FLATE_MIDDLE_THRESHOLD => Compression::fast(),
                FLATE_MIDDLE_THRESHOLD..FLATE_UPPER_THRESHOLD => Compression::default(),
                FLATE_UPPER_THRESHOLD.. => Compression::best(),
            }
        };
        ZlibEncoder::new(f, compression_level).write_all(&buffer)
    }

    /// Read the debug info from the format described in [the module docs][crate::parse]
    ///
    /// # Errors
    ///
    /// Returns a [`DebugInfoReadError`] on failure - see the [`DebugInfoReadError`] docs for
    /// details on possible errors and their meanings.
    pub fn read(mut f: impl Read) -> Result<Self, DebugInfoReadError> {
        use DebugInfoReadError as Error;
        use flate2::read::ZlibDecoder;
        let mut header = HEADER;
        f.read_exact(&mut header)?;

        if header[..7] != MAGIC {
            return Err(Error::BadMagic(core::array::from_fn(|i| header[i])));
        }

        if header[7] != VERSION {
            return Err(Error::VersionMismatch(header[7]));
        }

        let mut reader = io::BufReader::new(ZlibDecoder::new(f));
        let mut buf: [u8; 8] = [0; 8];

        macro_rules! read_i64 {
            () => {{
                reader.read_exact(&mut buf)?;
                i64::from_le_bytes(buf)
            }};
        }

        let nlabels = read_size(&mut reader)?;
        let mut labels = Vec::with_capacity(nlabels);
        for _ in 0..nlabels {
            let len = read_size(&mut reader)?;

            // SAFETY: `0` is a valid u8 value
            let mut raw_label_text = vec![0; len];
            reader.read_exact(&mut raw_label_text)?;
            let label_text = String::from_utf8(raw_label_text)?.into_boxed_str();

            if !valid_ident(&label_text) {
                return Err(Error::InvalidLabel(label_text));
            }

            let start = read_size(&mut reader)?;
            let end = start + read_size(&mut reader)?;
            let addr = read_i64!();
            let label = span(label_text, start..end);
            labels.push((label, addr));
        }
        let labels = labels.into_boxed_slice();

        let ndirectives = read_size(&mut reader)?;
        let mut directives = Vec::with_capacity(ndirectives);
        for _ in 0..ndirectives {
            reader.read_exact(&mut buf[..1])?;
            let kind = DirectiveKind::try_from(buf[0]).map_err(Error::BadDirectiveByte)?;
            let start = read_size(&mut reader)?;
            let end = start + read_size(&mut reader)?;
            let src_span = SimpleSpan {
                start,
                end,
                context: (),
            };
            let start = read_size(&mut reader)?;
            let end = start + read_size(&mut reader)?;
            let output_span = SimpleSpan {
                start,
                end,
                context: (),
            };

            directives.push(DirectiveDebug {
                kind,
                src_span,
                output_span,
            });
        }
        let directives = directives.into_boxed_slice();

        Ok(Self { labels, directives })
    }
}

#[non_exhaustive]
#[derive(Debug)]
/// An error that occored while trying to read [`DebugInfo`] from its opaque on-disk format
pub enum DebugInfoReadError {
    /// The first 8 bytes of the on-disk data didn't match the proper magic byte sequence
    BadMagic([u8; 8]),
    /// The version of the on-disk data format was not recognized
    VersionMismatch(u8),
    /// While reading, the contained [`io::Error`] occored
    IoError(io::Error),
    /// [usize] too small to store a given size
    IntSize,
    /// The provided byte didn't match any [`DirectiveKind`]
    BadDirectiveByte(u8),
    /// A [label][DebugInfo::labels]'s [span][SimpleSpan] is backwards
    /// A label's text data wasn't UTF-8-encoded
    NonUtf8Label(FromUtf8Error),
    /// A label was valid UTF-8, but was not a valid identifier
    InvalidLabel(Box<str>),
}

use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::string::FromUtf8Error;

impl Debug for EncodedSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0
            .iter()
            .rev()
            .copied()
            .fold(&mut f.debug_tuple("EncodedSize"), |dbg, b| {
                dbg.field(&format_args!("{:07b}", b & 0x7f))
            })
            .finish()
    }
}

impl Display for DebugInfoReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DebugInfoReadError::BadMagic(magic) => write!(
                f,
                "bad magic bytes after decompression: {}",
                magic.escape_ascii()
            ),
            DebugInfoReadError::VersionMismatch(version) => {
                write!(f, "unsupported version: {version}")
            }
            DebugInfoReadError::IoError(error) => Display::fmt(error, f),
            DebugInfoReadError::IntSize => {
                write!(f, "usize too small to load value")
            }
            DebugInfoReadError::BadDirectiveByte(byte) => {
                write!(f, "bad directive byte: 0x{byte:02x}")
            }
            DebugInfoReadError::NonUtf8Label(label) => {
                write!(f, "tried to decode a non-utf8 label: {label}")
            }
            DebugInfoReadError::InvalidLabel(s) => {
                write!(f, "invalid label: {:?}", s.as_ref())
            }
        }
    }
}

impl Error for DebugInfoReadError {}

impl From<io::Error> for DebugInfoReadError {
    fn from(err: io::Error) -> Self {
        Self::IoError(err)
    }
}

impl From<FromUtf8Error> for DebugInfoReadError {
    fn from(err: FromUtf8Error) -> Self {
        Self::NonUtf8Label(err)
    }
}

impl From<NeededBits> for DebugInfoReadError {
    fn from(_: NeededBits) -> Self {
        Self::IntSize
    }
}

impl TryFrom<&EncodedSize> for usize {
    type Error = NeededBits;

    fn try_from(encoded_val: &EncodedSize) -> Result<Self, Self::Error> {
        let needed_bits = encoded_val.len().saturating_sub(1) as BitCounter * 7
            + (8 - (encoded_val.last().expect("EncodedSize is non-empty")).leading_zeros()
                as BitCounter);
        if needed_bits > usize::BITS as BitCounter {
            return Err(NeededBits(needed_bits));
        }

        debug_assert!(
            encoded_val.last().is_some_and(|v| v & 0x80 == 0),
            "{encoded_val:?}"
        );
        debug_assert!(
            (encoded_val.get(..encoded_val.len() - 1))
                .is_none_or(|s| s.iter().all(|v| v & 0x80 == 0x80)),
            "{encoded_val:?}"
        );
        let mut val = 0;
        let mut shift: u32 = 0;
        for byte in encoded_val.iter().copied() {
            val |= usize::from(byte & 0x7f) << shift;
            shift += 7;
        }
        Ok(val)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    #[test]
    fn encoded_size_test() {
        let encoded_0xff = EncodedSize::from_slice(&[0b1111_1111, 0b0000_0001]);
        assert_eq!(Box::<EncodedSize>::from(0xff_usize).as_ref(), encoded_0xff);
        assert_eq!(
            usize::try_from(encoded_0xff).unwrap(),
            0xff,
            "{encoded_0xff:?}"
        );
        let encoded_usize_max = Box::<EncodedSize>::from(usize::MAX);
        assert_eq!(usize::try_from(&*encoded_usize_max), Ok(usize::MAX));
        let mut v = encoded_usize_max.to_vec();
        if let Some(l) = v.last_mut()
            && *l != 0xff
        {
            let mut shift = 0;
            while *l & (1 << shift) != 0 {
                shift += 1;
            }
            assert!(shift < 7);
            *l |= 1 << shift;
        } else {
            v.push(0b1000_0001);
        }

        let encoded_usize_overflow = EncodedSize::from_boxed_slice(v.into_boxed_slice());
        assert_eq!(
            usize::try_from(encoded_usize_overflow.as_ref()),
            Err(NeededBits(usize::BITS as BitCounter + 1)),
            "{encoded_usize_overflow:?}"
        );

        for power in 1..=4 {
            for base in [2, 7] {
                let base_val = usize::pow(base, power);
                for i in [base_val - 1, base_val, base_val + 1] {
                    let expected_bit_width = (usize::BITS - i.leading_zeros()) as BitCounter;
                    let expected_byte_width = expected_bit_width.div_ceil(7);
                    let encoded = Box::<EncodedSize>::from(i);
                    assert_eq!(usize::try_from(&*encoded), Ok(i), "{i}, {encoded:?}");
                    assert_eq!(encoded.len() as BitCounter, expected_byte_width);
                }
            }
        }
    }
}
