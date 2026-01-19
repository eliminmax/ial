// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Module for [`DebugInfo`] and its related functionality

use chumsky::span::{SimpleSpan, Spanned};
use std::io::{self, Write};

pub mod parse;

#[derive(Debug, PartialEq, Clone, Copy)]
/// Debug info about a given directive
pub struct DirectiveDebug {
    /// Type of the directive
    pub kind: DirectiveKind,
    /// span within the source code of the directive
    pub src_span: SimpleSpan,
    /// span within the output of the directive
    pub output_span: SimpleSpan,
}

#[non_exhaustive]
#[derive(Debug, PartialEq)]
/// Debug info generated when assembling source code with [`assemble_with_debug`]
///
/// [`assemble_with_debug`]: crate::asm::assemble_with_debug
pub struct DebugInfo {
    /// Mapping of labels' spans in the source code to their resolved addresses in the output
    pub labels: Box<[(Spanned<Box<str>>, i64)]>,
    /// Boxed slice of debug info about each directive
    pub directives: Box<[DirectiveDebug]>,
}

#[non_exhaustive]
#[derive(Debug, PartialEq, Clone, Copy)]
/// The type of a [Directive]
///
/// [Directive]: crate::asm::Directive
#[allow(missing_docs, reason = "trivial")]
pub enum DirectiveKind {
    Instruction = 0,
    Data = 1,
    Ascii = 2,
}

impl TryFrom<u8> for DirectiveKind {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Instruction),
            1 => Ok(Self::Data),
            2 => Ok(Self::Ascii),
            _ => Err(value),
        }
    }
}

impl crate::Interpreter {
    /// Write diagnostic information about the interpreter's state to `writer`
    ///
    /// Uses [`debug_info.labels`][DebugInfo::labels] to determine points of interest
    ///
    /// # Errors
    ///
    /// If writing to `writer` fails, returns the resulting [`io::Error`]
    pub fn diagnose<W: Write>(&self, debug_info: &DebugInfo, writer: &mut W) -> io::Result<()> {
        todo!(
            "Interpreter::diagnose({}, writer: {})",
            std::any::type_name_of_val(&debug_info),
            std::any::type_name_of_val(&writer)
        )
    }
}
