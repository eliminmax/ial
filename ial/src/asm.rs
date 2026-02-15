// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Module for assembling IAL
//!
//! This module provides functions for assembling the [proposed assembly syntax] from
//! the Esolangs Community Wiki.
//! ```
//! use ial::prelude::*;
//! use ial::asm::assemble;
//! const HELLO_ASM: &str = r#"
//! ; A simple Hello World program
//! RBO #hello      ; set relative base to address of hello text
//! loop: OUT @0    ; output int at relative base
//!       RBO #1    ; increment relative base
//!       JNZ @0, #loop
//! HALT
//!
//! hello: ASCII "Hello, world!\n\0" ; a classic greeting
//! "#;
//!
//! let mut interpreter = Interpreter::new(assemble(HELLO_ASM).unwrap());
//! let (output, state) = dbg!(interpreter).run_through_inputs(std::iter::empty()).unwrap();
//!
//! let expected_output: Vec<i64> = b"Hello, world!\n".into_iter().copied().map(i64::from).collect();
//!
//! assert_eq!(state, State::Halted);
//! assert_eq!(output, expected_output);
//! ```
//!
//! [NASM]: <https://www.nasm.us/doc/nasm03.html>
//! [proposed assembly syntax]: <https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax>

use crate::debug_info::{DebugInfo, DirectiveDebug};
use chumsky::error::Rich;
use chumsky::span::{SimpleSpan, Spanned};
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::{self, Display};
use std::error::Error;

pub use ial_core::AssemblyError;
use ial_ast::{Directive, Instr, Label, Line, parsers};

/// The Abstract Syntax Tree generated from the assembly
#[derive(Debug, PartialEq, Clone)]
pub struct Ast<'a>(Vec<Line<'a>>);

#[cfg(feature = "ast")]
impl<'a> Ast<'a> {
    /// Access the AST's internals
    ///
    /// <div class="warning">
    ///
    /// This and other methods gated behind the `"ast"` crate feature expose internals, and may
    /// have breaking changes in minor updates.
    ///
    /// </div>
    #[must_use]
    pub fn inner(&self) -> &[Line<'a>] {
        &self.0
    }

    /// Mutably access the AST's internals
    ///
    /// <div class="warning">
    ///
    /// This and other methods gated behind the `"ast"` crate feature expose internals, and may
    /// have breaking changes in minor updates.
    ///
    /// </div>
    #[must_use]
    pub fn inner_mut(&mut self) -> &mut Vec<Line<'a>> {
        &mut self.0
    }

    /// take the underlying [`Vec`] of [`Line`]s 
    ///
    /// <div class="warning">
    ///
    /// This and other methods gated behind the `"ast"` crate feature expose internals, and may
    /// have breaking changes in minor updates.
    ///
    /// </div>
    #[must_use]
    pub fn into_inner(self) -> Vec<Line<'a>> {
        self.0
    }
    
    /// convert a [`Vec`] of [`Line`]s into an [`Ast`]
    ///
    /// <div class="warning">
    ///
    /// This and other methods gated behind the `"ast"` crate feature expose internals, and may
    /// have breaking changes in minor updates.
    ///
    /// </div>
    #[must_use]
    pub fn from_lines(lines: Vec<Line<'a>>) -> Self {
        Self(lines)
    }
}

/// Parse the assembly code into a [`Vec<Line>`], or a [`Vec<Rich<char>>`] on failure.
///
/// # Errors
///
/// If the provided code fails to parse, the parser error/s are returned.
///
/// # Example
///
/// ```
/// use ial::asm::build_ast;
/// use ial::Interpreter;
///
/// assert!(build_ast(r#"
/// RBO #hello
/// loop: OUT @0
///     INCB #1
///     JNZ @0, #loop
/// HALT
/// hello: ASCII "Hello, world!"
/// "#).is_ok());
/// ```
pub fn build_ast(code: &str) -> Result<Ast<'_>, AstBuildErr<'_>> {
    use chumsky::Parser;
    parsers::ial().parse(code).into_result().map(Ast).map_err(AstBuildErr)
}

type RawDebugInfo<'a> = (Vec<(Spanned<&'a str>, i64)>, Vec<DirectiveDebug>);

/// Common implementation of [`assemble_ast`] and [`assemble_with_debug`].
///
/// If `generate_debug` is false, then both vecs in the returned [`RawDebugInfo`] will be empty to
/// avoid allocating
fn assemble_inner<'a>(
    code: Ast<'a>,
    generate_debug: bool,
) -> Result<(Vec<i64>, RawDebugInfo<'a>), AssemblyError<'a>> {
    let mut labels: HashMap<&'a str, (i64, SimpleSpan)> = HashMap::new();
    let mut index = 0;
    let mut directives = Vec::new();

    let mut add_label =
        |label: &'a str, index: i64, span: SimpleSpan| -> Result<(), AssemblyError<'a>> {
            if let Some((_, old_span)) = labels.insert(label, (index, span)) {
                Err(AssemblyError::DuplicateLabel {
                    label,
                    spans: [old_span.into_range(), span.into_range()],
                })
            } else {
                Ok(())
            }
        };

    for line in &code.0 {
        for Label(Spanned { inner: label, span }) in &line.labels {
            add_label(label, index, *span)?;
        }
        if let Some(directive) = line.directive.as_ref() {
            if let Directive::Instruction(instr) = &directive.inner {
                macro_rules! add_param_labels {
                    ($param: ident, $offset: literal) => {{
                        for &Label(Spanned { inner: label, span }) in &$param.1.labels {
                            add_label(label, index + $offset, span)?;
                        }
                    }};
                }
                match instr.as_ref() {
                    Instr::Add(a, b, c)
                    | Instr::Mul(a, b, c)
                    | Instr::Lt(a, b, c)
                    | Instr::Eq(a, b, c) => {
                        add_param_labels!(a, 1);
                        add_param_labels!(b, 2);
                        add_param_labels!(c, 3);
                    }
                    Instr::Jnz(a, b) | Instr::Jz(a, b) => {
                        add_param_labels!(a, 1);
                        add_param_labels!(b, 2);
                    }
                    Instr::In(a) | Instr::Out(a) | Instr::Rbo(a) => add_param_labels!(a, 1),
                    Instr::Halt => (),
                }
            }

            index += directive
                .size()
                .map_err(|size| AssemblyError::DirectiveTooLarge {
                    size,
                    span: directive.span.into_range(),
                })?;
        }
    }

    let label_spans = if generate_debug {
        labels
            .iter()
            .map(|(&inner, &(index, span))| (Spanned { inner, span }, index))
            .collect()
    } else {
        Vec::new()
    };
    let labels = labels
        .into_iter()
        .map(|(label, (index, _span))| (label, index))
        .collect();

    let mut v = Vec::with_capacity(index.try_into().unwrap_or_default());

    for line in code.0 {
        if generate_debug {
            if let Some(spanned) = line.directive.as_ref() {
                let kind = spanned.inner.kind();
                let src_span = spanned.span;
                let start = v.len();
                line.encode_into(&mut v, &labels)?;
                let end = v.len();
                directives.push(DirectiveDebug {
                    kind,
                    src_span,
                    output_span: SimpleSpan {
                        start,
                        end,
                        context: (),
                    },
                });
            }
        } else {
            line.encode_into(&mut v, &labels)?;
        }
    }

    Ok((v, (label_spans, directives)))
}

/// Assemble an AST in the form of a [`Vec<Line>`] into a [`Vec<i64>`], preserving debug info
///
/// On success, returns `Ok((code, debug))`, where `code` is a [`Vec<i64>`] and `debug` is a
/// [`DebugInfo`].
///
/// # Errors
///
/// * If a directive would exceed [`usize::MAX`] in length, returns
///   [`AssemblyError::DirectiveTooLarge`].
/// * If there are duplicate labels within the source, returns [`AssemblyError::DuplicateLabel`].
/// * If an expression fails to resolve due to a missing label, returns
///   [`AssemblyError::UnresolvedLabel`].
pub fn assemble_with_debug(
    code: Ast<'_>,
) -> Result<(Vec<i64>, DebugInfo), AssemblyError<'_>> {
    assemble_inner(code, true).map(|(output, (labels, directives))| {
        (
            output,
            DebugInfo {
                labels: labels
                    .into_iter()
                    .map(|(Spanned { inner, span }, addr)| {
                        (
                            Spanned {
                                inner: inner.into(),
                                span,
                            },
                            addr,
                        )
                    })
                    .sorted_by_key(|(Spanned { span, .. }, index)| (*index, *span))
                    .collect_vec()
                    .into_boxed_slice(),
                directives: directives.into_boxed_slice(),
            },
        )
    })
}

/// Assemble an AST in the form of a [`Vec<Line>`] into a [`Vec<i64>`]
///
/// On success, returns the assembled code as a [`Vec<i64>`].
///
/// # Errors
///
/// * If a directive would exceed [`usize::MAX`] in length, returns
///   [`AssemblyError::DirectiveTooLarge`].
/// * If there are duplicate labels within the source, returns [`AssemblyError::DuplicateLabel`].
/// * If an expression fails to resolve due to a missing label, returns
///   [`AssemblyError::UnresolvedLabel`].
///
/// # Example
///
/// ```
/// use ial::asm::{build_ast, assemble_ast};
/// let ast = build_ast("halt: HALT; halts the program").unwrap();
/// assert_eq!(assemble_ast(ast).unwrap(), vec![99]);
/// ```
pub fn assemble_ast(code: Ast<'_>) -> Result<Vec<i64>, AssemblyError<'_>> {
    assemble_inner(code, false).map(|(output, _)| output)
}

#[derive(Debug)]
/// One or more parsing errors that occured in [`build_ast`]
pub struct AstBuildErr<'a>(Vec<Rich<'a, char>>);

#[cfg(feature = "ast")]
impl<'a> AstBuildErr<'a> {
    /// Get the underlying [`chumsky::error::Rich<'_, char>`]s in a slice
    ///
    /// <div class="warning">
    ///
    /// This and other methods gated behind the `"ast"` crate feature expose internals, and may
    /// have breaking changes in minor updates.
    ///
    /// </div>
    #[must_use]
    pub fn inner(&self) -> &[Rich<'a, char>] {
        self.0.as_slice()
    }

    /// Convert the [`AstBuildErr`] into the underlying [`Vec`] of
    /// [`chumsky::error::Rich<'_, char>`]
    ///
    /// <div class="warning">
    ///
    /// This and other methods gated behind the `"ast"` crate feature expose internals, and may
    /// have breaking changes in minor updates.
    ///
    /// </div>
    #[must_use]
    pub fn into_inner(self) -> Vec<Rich<'a, char>> {
        self.0
    }

    /// Convert a [`Vec`] of [`chumsky::error::Rich<'a, char>`]s into an [`AstBuildErr<'a>`]
    ///
    /// <div class="warning">
    ///
    /// This and other methods gated behind the `"ast"` crate feature expose internals, and may
    /// have breaking changes in minor updates.
    ///
    /// </div>
    #[must_use]
    pub fn from_inner(v: Vec<Rich<'a, char>>) -> Self {
        Self(v)
    }
}

impl Display for AstBuildErr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.iter().format("\n"))
    }
}

impl Error for AstBuildErr<'_> {}

/// An error that indicates where in the assembly process a failure occured, and wraps around the
/// error type for that part of the process.
#[derive(Debug)]
pub enum GeneralAsmError<'a> {
    /// Failure to build the AST
    BuildAst(AstBuildErr<'a>),
    /// Failure to assemble the parsed AST
    Assemble(AssemblyError<'a>),
}

/// Try to assemble the code into a [`Vec<i64>`]
///
/// This is a thin convenience wrapper around [`build_ast`] and [`assemble_ast`].
///
/// # Errors
///
/// If the internal call to [`build_ast`] returns any errors, returns them within a
/// [`GeneralAsmError::BuildAst`].
///
/// If the internal call to [`assemble_ast`] returns any errors, returns them within a
/// [`GeneralAsmError::Assemble`].
#[inline]
pub fn assemble(code: &str) -> Result<Vec<i64>, GeneralAsmError<'_>> {
    assemble_ast(build_ast(code).map_err(GeneralAsmError::BuildAst)?)
        .map_err(GeneralAsmError::Assemble)
}
