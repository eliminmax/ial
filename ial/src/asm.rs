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

use chumsky::error::Rich;
use chumsky::span::{SimpleSpan, Spanned};
use ial_debug_info::{DebugInfo, DirectiveDebug};
use std::collections::HashMap;

pub use ast;
pub use ast::AssemblyError;
use ast::{Directive, Instr, Label, Line, parsers};

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
pub fn build_ast(code: &str) -> Result<Vec<Line<'_>>, Vec<Rich<'_, char>>> {
    use chumsky::Parser;
    parsers::ial().parse(code).into_result()
}

type RawDebugInfo<'a> = (Vec<(Spanned<&'a str>, i64)>, Vec<DirectiveDebug>);

/// Common implementation of [`assemble_ast`] and [`assemble_with_debug`].
///
/// If `generate_debug` is false, then both vecs in the returned [`RawDebugInfo`] will be empty to
/// avoid allocating
fn assemble_inner<'a>(
    code: Vec<Line<'a>>,
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
                    spans: [old_span, span],
                })
            } else {
                Ok(())
            }
        };

    for line in &code {
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
                    span: directive.span,
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

    for line in code {
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
    code: Vec<Line<'_>>,
) -> Result<(Vec<i64>, DebugInfo), AssemblyError<'_>> {
    assemble_inner(code, true)
        .map(|(output, (labels, directives))| (output, DebugInfo::new(labels, directives)))
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
/// use ial::asm::{assemble_ast, ast::{Line, Directive, Instr, Parameter}};
/// use chumsky::prelude::{Spanned, SimpleSpan};
///
/// let inner = Directive::Instruction(Box::new(Instr::Halt));
///
/// let ast = vec![
///     Line {
///         labels: vec![],
///         directive: Some(Spanned { inner, span: SimpleSpan::default() }),
///         comment: None,
///     }
/// ];
///
/// assert_eq!(assemble_ast(ast).unwrap(), vec![99]);
/// ```
pub fn assemble_ast(code: Vec<Line<'_>>) -> Result<Vec<i64>, AssemblyError<'_>> {
    assemble_inner(code, false).map(|(output, _)| output)
}

/// An error that indicates where in the assembly process a failure occured, and wraps around the
/// error type for that part of the process.
#[derive(Debug)]
pub enum GeneralAsmError<'a> {
    /// Failure to build the AST
    BuildAst(Vec<Rich<'a, char>>),
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
