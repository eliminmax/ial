// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use super::{DebugInfo, DirectiveDebug, DirectiveKind};
use chumsky::span::SimpleSpan;
use either::Either;
use std::io::{self, Read, Write};
use std::num::TryFromIntError;

/// the magic bytes for on-disk debug data.
const MAGIC: [u8; 8] = *b"\0IALDBG\0";
/// the debug format version
const VERSION: u8 = 0;

impl DebugInfo {
    /// Write the debug info into an opaque on-disk format
    pub fn write(self, f: impl Write) -> Result<(), Either<io::Error, TryFromIntError>> {
        use flate2::write::ZlibEncoder;
        let DebugInfo { labels, directives } = self;

        let output_len = MAGIC.len() + 17 + labels.len() * 24 + directives.len() * 33;
        let mut buffer = Vec::with_capacity(output_len);

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
            write_usize!(label.start);
            write_usize!(label.end);
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
        debug_assert_eq!(buffer.len(), output_len);
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
            let start = read_usize!();
            let end = read_usize!();
            let addr = read_i64!();
            if start > end {
                return Err(Error::BackwardsLabelSpan { start, end });
            }
            let label = SimpleSpan {
                start,
                end,
                context: (),
            };
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
}
