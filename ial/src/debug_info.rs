//! Module for [`DebugInfo`] and its related functionality

use chumsky::span::{SimpleSpan, Spanned};

use ial_ast::DirectiveKind;

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
#[derive(Debug, Clone, PartialEq)]
/// Debug info generated when assembling IAL
pub struct DebugInfo {
    /// Mapping of labels' spans in the source code to their resolved addresses in the output
    pub labels: Box<[(Spanned<Box<str>>, i64)]>,
    /// Boxed slice of debug info about each directive
    pub directives: Box<[DirectiveDebug]>,
}

use std::fmt::{self, Display};
#[derive(Debug)]
/// An error that occured when attempting to use [`DebugInfo`] to disassemble code
pub enum DebugInfoError {
    /// Debug info included at least this many ints beyond the end of the input
    MissingInts(usize),
    /// An [instruction directive] had either 0 or more than 4 ints in its [`output_span`]
    ///
    /// [instruction directive]: ial_ast::DirectiveKind::Instruction
    /// [`output_span`]: DirectiveDebug::output_span
    CorruptDirectiveSize,
    /// A [directive] from the [`DebugInfo`] was larger than [`i64::MAX`]
    ///
    /// [directive]: ial_ast::Directive
    DirectiveTooLarge(usize),
}
impl Display for DebugInfoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DebugInfoError::MissingInts(i) => write!(f, "expected at least {i} more ints"),
            DebugInfoError::CorruptDirectiveSize => {
                write!(f, "debug info has an invalid instruction directive size")
            }
            DebugInfoError::DirectiveTooLarge(size) => {
                write!(
                    f,
                    "debug info has a directive {size} long, which is longer than i64::MAX"
                )
            }
        }
    }
}
impl std::error::Error for DebugInfoError {}
