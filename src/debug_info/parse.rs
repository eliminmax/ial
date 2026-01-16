// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

/// the magic bytes for on-disk debug data.
const MAGIC: [u8; 8] = *b"\0IALDBG\0";
/// the debug format version
const VERSION: u8 = 0;
use super::*;
use crate::asm::ast_util::span;
use chumsky::text::Char;
use either::Either;
use std::io::{self, Read, Write};
use std::num::TryFromIntError;

fn ident(text: &str) -> bool {
    let mut chars = text.chars();
    let head = chars.next();
    head.is_some_and(|c| c.is_ident_start()) && chars.all(|c| c.is_ident_continue())
}

impl DebugInfo {
    /// Write the debug info into an opaque on-disk format
    pub fn write(self, f: impl Write) -> Result<(), Either<io::Error, TryFromIntError>> {
        use flate2::write::ZlibEncoder;
        let DebugInfo { labels, directives } = self;

        let mut buffer = Vec::new();

        macro_rules! write_usize {
            ($val: expr) => {
                buffer.extend(
                    u64::try_from($val)
                        .map_err(Either::Right)
                        .map(u64::to_le_bytes)?,
                );
            };
        }

        buffer.extend(MAGIC);
        buffer.push(VERSION);
        write_usize!(labels.len());

        for (label, addr) in labels {
            write_usize!(label.inner.len());
            buffer.extend(label.inner.as_bytes());
            write_usize!(label.span.start);
            write_usize!(label.span.end);
            buffer.extend(addr.to_le_bytes());
        }

        write_usize!(directives.len());

        for dir in directives {
            buffer.push(dir.kind as u8);
            write_usize!(dir.src_span.start);
            write_usize!(dir.src_span.end);
            write_usize!(dir.output_span.start);
            write_usize!(dir.output_span.end);
        }
        ZlibEncoder::new(f, flate2::Compression::best())
            .write_all(&buffer)
            .map_err(Either::Left)
    }

    /// Read the debug info from an opaque on-disk format
    pub fn read(f: impl Read) -> Result<Self, DebugInfoReadError> {
        use DebugInfoReadError as Error;
        use flate2::read::ZlibDecoder;
        let mut reader = ZlibDecoder::new(f);
        let mut buf: [u8; 8] = [0; 8];

        let mut read = |buf: &mut [u8]| -> Result<(), Error> {
            reader.read_exact(buf).map_err(DebugInfoReadError::IoError)
        };

        macro_rules! read_usize {
            () => {{
                read(&mut buf)?;
                usize::try_from(u64::from_le_bytes(buf)).map_err(Error::IntSize)?
            }};
        }
        macro_rules! read_i64 {
            () => {{
                read(&mut buf)?;
                i64::from_le_bytes(buf)
            }};
        }

        read(&mut buf)?;
        if buf != MAGIC {
            return Err(Error::BadMagic(buf));
        }
        read(&mut buf[..1])?;
        if buf[0] != VERSION {
            return Err(Error::VersionMismatch(buf[0]));
        }

        read(&mut buf)?;
        let nlabels = read_usize!();
        let mut labels = Vec::with_capacity(nlabels);
        for _ in 0..nlabels {
            let len = read_usize!();

            // SAFETY: `0` is a valid u8 value
            let mut raw_label_text = unsafe { Box::new_zeroed_slice(len).assume_init() };
            read(&mut raw_label_text)?;
            // because there's no str::from_boxed_utf8 that validates, but there is an unsafe
            // unchecked `std::str::from_boxed_utf8_unchecked`, first validate, then convert within
            // an unsafe block
            let label_text = if str::from_utf8(&raw_label_text).is_ok() {
                // SAFETY: Already validated
                unsafe { std::str::from_boxed_utf8_unchecked(raw_label_text) }
            } else {
                return Err(Error::NonUtf8Label(raw_label_text));
            };

            if !ident(&label_text) {
                return Err(Error::InvalidLabel(label_text));
            }

            let start = read_usize!();
            let end = read_usize!();
            let addr = read_i64!();
            if start > end {
                return Err(Error::BackwardsLabelSpan { start, end });
            }
            let label = span(label_text, start..end);
            labels.push((label, addr));
        }
        let labels = labels.into_boxed_slice();

        let ndirectives = read_usize!();
        let mut directives = Vec::with_capacity(ndirectives);
        for _ in 0..ndirectives {
            read(&mut buf[..1])?;
            let kind = DirectiveKind::try_from(buf[0]).map_err(Error::BadDirectiveByte)?;
            let start = read_usize!();
            let end = read_usize!();
            if start > end {
                return Err(Error::BackwardsSrcSpan { start, end });
            }
            let src_span = SimpleSpan {
                start,
                end,
                context: (),
            };
            let start = read_usize!();
            let end = read_usize!();
            if start > end {
                return Err(Error::BackwardsOutSpan { start, end });
            }
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
/// An error that occored while trying to read [DebugInfo] from its opaque on-disk format
pub enum DebugInfoReadError {
    /// The first 8 bytes of the on-disk data didn't match the proper magic byte sequence
    BadMagic([u8; 8]),
    /// The version of the on-disk data format was not recognized
    VersionMismatch(u8),
    /// While reading, the contained [io::Error] occored
    IoError(io::Error),
    /// An error occured converting a [[u8]; 8] into a [usize]
    IntSize(TryFromIntError),
    /// The provided byte didn't match any [DirectiveKind]
    BadDirectiveByte(u8),
    /// A [label][DebugInfo::labels]'s [span][SimpleSpan] is backwards
    BackwardsLabelSpan {
        /// The would-be start of the label's span
        start: usize,
        /// The would-be end of the label's span
        end: usize,
    },
    /// A directive's [span][SimpleSpan] in the [source code][DirectiveDebug::src_span] is backwards
    BackwardsSrcSpan {
        /// The would-be start of the directive's source span
        start: usize,
        /// The would-be end of the directive's source span
        end: usize,
    },
    /// A directive's [span][SimpleSpan] in the [output][DirectiveDebug::output_span] is backwards
    BackwardsOutSpan {
        /// The would-be start of the directive's output span
        start: usize,
        /// The would-be end of the directive's output span
        end: usize,
    },
    /// A label's text data wasn't UTF-8-encoded
    NonUtf8Label(Box<[u8]>),
    /// A label was valid UTF-8, but was not a valid identifier
    InvalidLabel(Box<str>),
}

use std::error::Error;
use std::fmt::{self, Display};

impl Display for DebugInfoReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        macro_rules! backwards_span {
            ($span_type: literal, $start: ident, $end: ident) => {{
                write!(
                    f,
                    "backwards {} span from {} to {}",
                    $span_type, $start, $end
                )
            }};
        }
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
            DebugInfoReadError::IntSize(try_from_int_error) => Display::fmt(try_from_int_error, f),
            DebugInfoReadError::BadDirectiveByte(byte) => {
                write!(f, "Bad directive byte: 0x{byte:02x}")
            }
            DebugInfoReadError::BackwardsLabelSpan { start, end } => {
                backwards_span!("label", start, end)
            }
            DebugInfoReadError::BackwardsSrcSpan { start, end } => {
                backwards_span!("source", start, end)
            }
            DebugInfoReadError::BackwardsOutSpan { start, end } => {
                backwards_span!("output", start, end)
            }
            DebugInfoReadError::NonUtf8Label(label) => {
                write!(
                    f,
                    "tried to decode a non-utf8 label: {}",
                    label.escape_ascii()
                )
            }
            DebugInfoReadError::InvalidLabel(s) => {
                write!(f, "invalid label: {:?}", s.as_ref())
            }
        }
    }
}

impl Error for DebugInfoReadError {}

