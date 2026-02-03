// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Module for working with an assembly language for Intcode
//!
//! This module defines an AST for an extended version of the [proposed assembly syntax] from
//! the Esolangs Community Wiki, powered by [chumsky]. It provides mnemonics for each of the
//! intcode instructions, and the ability to include inline data, either directly or as ASCII text.
//!
//! Each [line](Line) has three components, any of which can be omitted.
//!
//! The first component is a label, which will resolve to the index of the next intcode int added
//! by a directive, either on the same line or a future one.
//!
//! The next is a [directive](Directive), which is what will actually be converted into intcode.
//! The third is a comment - it is ignored completely.
//!
//! Following from [NASM]'s syntax, the syntax of a line is as follows:
//!
//! ```text
//! label: directive ; comment
//! ```
//!
//! Labels are parsed using [`chumsky::text::ident`], so identifiers the same rules as [Rust], except
//! without Unicode normalization.
//!
//! # Example
//!
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
//! If you want, you can view the AST before assembling, though it's quite unwieldy:
//!
//! # Example
//!
//! ```
//! use ial::{prelude::*, asm::ast::prelude::*};
//!
//! let ast = build_ast("idle_loop: JZ #0, #idle_loop").unwrap();
//! let expected = vec![Line {
//!     labels: vec![Label(Spanned {
//!         inner: "idle_loop",
//!         span: SimpleSpan { start: 0, end: 9, context: () },
//!     })],
//!     directive: Some(Spanned {
//!         span: SimpleSpan { start: 11, end: 28, context: () },
//!         inner: Directive::Instruction(Box::new(Instr::Jz(
//!             Parameter (
//!                 ParamMode::Immediate,
//!                 Box::new(OuterExpr {
//!                     expr: Spanned {
//!                         inner: Expr::Number(0),
//!                         span: SimpleSpan { start: 15, end: 16, context: () },
//!                     },
//!                     labels: Vec::new(),
//!                 }),
//!             ),
//!             Parameter (
//!                 ParamMode::Immediate,
//!                 Box::new(OuterExpr {
//!                     expr: Spanned {
//!                         inner: Expr::Ident("idle_loop"),
//!                         span: SimpleSpan { start: 19, end: 28, context: () },
//!                     },
//!                     labels: Vec::new(),
//!                 }),
//!             ),
//!         )))
//!     }),
//!     comment: None,
//! }];
//!
//! assert_eq!(ast, expected);
//! assert_eq!(assemble_ast(ast).unwrap(), vec![1106, 0, 0]);
//! ```
//!
//! The [`ast::util`] module provides some small functions and macros to express things more
//! concicely:
//!
//! ```
//! use ial::{prelude::*, asm::ast::prelude::*};
//! use ial::asm::ast::util::*;
//! let ast = build_ast("idle_loop: JZ #0, #idle_loop").unwrap();
//! let expected = vec![Line {
//!     labels: vec![Label(span("idle_loop", 0..9))],
//!     directive: Some(span(
//!         Directive::Instruction(Box::new(Instr::Jz(
//!             param!(#<expr!(0);>[14..16]),
//!             param!(#<expr!(idle_loop);>[18..28])
//!         ))),
//!         11..28
//!     )),
//!     comment: None,
//! }];
//!
//! assert_eq!(ast, expected);
//! assert_eq!(assemble_ast(ast).unwrap(), vec![1106, 0, 0]);
//! ```
//!
//! [NASM]: <https://www.nasm.us/doc/nasm03.html>
//! [proposed assembly syntax]: <https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax>
//! [Rust]: <https://doc.rust-lang.org/reference/identifiers.html>

use crate::debug_info::{DebugInfo, DirectiveDebug};
use chumsky::error::Rich;
use chumsky::span::{SimpleSpan, Spanned};
use itertools::Itertools;
use std::collections::HashMap;

mod display_impls;
mod parsers;

pub mod ast;
use ast::{Directive, Instr, Label, Line};

/// An error that occured while trying to assemble the AST into Intcode
#[derive(Debug)]
#[cfg_attr(not(feature = "bin_deps"), non_exhaustive)]
pub enum AssemblyError<'a> {
    /// An expresison used a label that could not be resolved
    UnresolvedLabel {
        /// The unresolved label
        label: &'a str,
        /// The span within the input of the unresolved label
        span: SimpleSpan,
    },
    /// A label was defined more than once
    DuplicateLabel {
        /// The duplicated label
        label: &'a str,
        /// The spans of the new and old definitions of the label
        spans: [SimpleSpan; 2],
    },
    /// A directive resolved to more than [`i64::MAX`] ints, and somehow didn't crash your computer
    /// before it was time to size things up
    DirectiveTooLarge {
        /// The output size of the directive
        size: usize,
        /// The span within the input of the directive
        span: SimpleSpan,
    },
}

/// A cheap iterator that uses a fixed amount of stack space for up to four `T`
enum StackIter<T: Copy> {
    Four(T, T, T, T),
    Three(T, T, T),
    Two(T, T),
    One(T),
    Empty,
}

impl<T: Copy> Iterator for StackIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            StackIter::Four(a, b, c, d) => {
                let a = *a;
                *self = Self::Three(*b, *c, *d);
                Some(a)
            }
            StackIter::Three(a, b, c) => {
                let a = *a;
                *self = Self::Two(*b, *c);
                Some(a)
            }
            StackIter::Two(a, b) => {
                let a = *a;
                *self = Self::One(*b);
                Some(a)
            }
            StackIter::One(a) => {
                let a = *a;
                *self = Self::Empty;
                Some(a)
            }
            StackIter::Empty => None,
        }
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
pub fn build_ast(code: &str) -> Result<Vec<Line<'_>>, Vec<Rich<'_, char>>> {
    use chumsky::Parser;
    parsers::grammar().parse(code).into_result()
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
                        for label in &$param.1.labels {
                            add_label(label.0.inner, index + $offset, label.0.span)?;
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
                let kind = spanned.inner.dtype();
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
    assemble_inner(code, true).map(|(output, (labels, directives))| {
        let labels = labels
            .into_iter()
            .map(|(Spanned { inner, span }, index)| {
                (
                    Spanned {
                        inner: Box::from(inner),
                        span,
                    },
                    index,
                )
            })
            .sorted_by_key(|(Spanned { span, .. }, index)| (*index, *span))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let directives = directives.into_boxed_slice();
        (output, DebugInfo { labels, directives })
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

impl std::error::Error for AssemblyError<'_> {}
