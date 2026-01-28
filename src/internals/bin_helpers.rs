// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Common functionality used within the `[[bin]]` targets
#![doc(hidden)]
#![allow(missing_docs, reason = "internal")]
use clap::ValueEnum;
use std::error::Error;
use std::fmt::{self, Debug, Display};

#[derive(PartialEq, Clone, Copy, ValueEnum)]
pub enum BinaryFormat {
    /// comma-separated ASCII-encoded decimal numbers
    #[value(alias("text"))]
    #[value(alias("aoc"))]
    Ascii,
    /// little-endian 64-bit integers
    #[cfg_attr(target_endian = "little", value(alias("binary-native")))]
    #[value(name("binary-little-endian"), alias("binle"))]
    LittleEndian,
    #[cfg_attr(target_endian = "big", value(alias("binary-native")))]
    #[value(name("binary-big-endian"), alias("binbe"))]
    /// big-endian 64-bit integers
    BigEndian,
}

/// A wrapper around a [`Box`ed][Box] [dyn Error][Error] that uses its implementation of [Display]
/// for the [Debug] impl, to display the Error if returned from `main`
///
/// Doesn't implement [`Error`], as it would conflict with its blanket implementation of
/// [`From<E: Error>`].
pub struct DisplayedError<'a>(Box<dyn Error + 'a>);

impl<'a, E: Error + 'a> From<E> for DisplayedError<'a> {
    fn from(e: E) -> Self {
        Self(Box::from(e))
    }
}

impl Debug for DisplayedError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}
