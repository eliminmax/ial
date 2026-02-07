// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Module for [`DebugInfo`] and its related functionality

use chumsky::span::{SimpleSpan, Spanned};
use itertools::Itertools;
use std::io::{self, Write};

use crate::Interpreter;
use ast::DirectiveKind;

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

impl Interpreter {
    /// Write human-readable diagnostic information about the interpreter's state to `writer`
    ///
    /// Uses [`debug_info.labels`][DebugInfo::labels] to determine points of interest, and to
    /// disassemble the intcode memory.
    ///
    /// # Errors
    ///
    /// If writing to `writer` fails, returns the resulting [`io::Error`].
    ///
    /// If `debug_info` fails to apply to this [`Interpreter`], then it does not return an error,
    /// but it does write the error message instead of writing the dissassembly to the output.
    pub fn write_diagnostic<W: Write>(
        &self,
        debug_info: &DebugInfo,
        writer: &mut W,
    ) -> io::Result<()> {
        use std::collections::BTreeMap;
        let label_map = debug_info
            .labels
            .iter()
            .map(|(s, a)| (a, s.inner.as_ref()))
            .into_group_map();
        let directive_starts = debug_info
            .directives
            .iter()
            .enumerate()
            .filter_map(|(i, dir)| {
                i64::try_from(dir.output_span.start)
                    .ok()
                    .map(|start| (start, i + 1))
            })
            .collect::<BTreeMap<i64, usize>>();

        writeln!(writer, "INTERPRETER STATE")?;
        if let Some(labels) = label_map.get(&self.index) {
            writeln!(
                writer,
                "    instruction pointer: {} ({})",
                self.index,
                labels.join(", ")
            )?;
        } else {
            writeln!(writer, "    instruction pointer: {}", self.index)?;
        }
        if let Some(i) = directive_starts.get(&self.index) {
            writeln!(writer, "        directive #{i}")
        } else {
            writeln!(writer, "        not a directive boundary")
        }?;

        if let Some(labels) = label_map.get(&self.rel_offset) {
            writeln!(
                writer,
                "    relative base: {} ({})",
                self.rel_offset,
                labels.join(", ")
            )?;
        } else {
            writeln!(writer, "    relative base {}", self.rel_offset)?;
        }

        match debug_info.disassemble(self.code.clone()) {
            Ok(dis) => writeln!(writer, "\n\nDISASSEMBLY\n{dis}")?,
            Err(e) => writeln!(
                writer,
                "unable to disassemble with provided debug_info: {e}"
            )?,
        }
        Ok(())
    }
}
