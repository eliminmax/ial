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
//! use ial::{prelude::*, asm::ast_prelude::*};
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
//!     })
//! }];
//!
//! assert_eq!(ast, expected);
//! assert_eq!(assemble_ast(ast).unwrap(), vec![1106, 0, 0]);
//! ```
//!
//! The [`ast_util`] module provides some small functions and macros to express things more
//! concicely:
//!
//! ```
//! use ial::{prelude::*, asm::ast_prelude::*};
//! use ial::asm::ast_util::*;
//! let ast = build_ast("idle_loop: JZ #0, #idle_loop").unwrap();
//! let expected = vec![Line {
//!     labels: vec![Label(span("idle_loop", 0..9))],
//!     directive: Some(span(
//!         Directive::Instruction(Box::new(Instr::Jz(
//!             param!(#<expr!(0);>[14..16]),
//!             param!(#<expr!(idle_loop);>[18..28])
//!         ))),
//!         11..28
//!     ))
//! }];
//!
//! assert_eq!(ast, expected);
//! assert_eq!(assemble_ast(ast).unwrap(), vec![1106, 0, 0]);
//! ```
//!
//! [NASM]: <https://www.nasm.us/doc/nasm03.html>
//! [proposed assembly syntax]: <https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax>
//! [Rust]: <https://doc.rust-lang.org/reference/identifiers.html>

use crate::debug_info::{DebugInfo, DirectiveDebug, DirectiveKind};
use ast_prelude::*;
use chumsky::error::Rich;
use itertools::Itertools;
use std::collections::HashMap;

mod display_impls;
mod parsers;

/// a small module that re-exports the types needed to work with the AST of the assembly language.
pub mod ast_prelude {
    pub use super::ast_util;
    pub use crate::{ParamMode, asm};
    pub use asm::{
        BinOperator, Directive, Expr, Instr, Label, Line, OuterExpr, Parameter, assemble,
        assemble_ast, build_ast,
    };
    pub use chumsky::span::{SimpleSpan, Spanned};
}

/// Small utility functions and macros for making it less painful to work with the AST
pub mod ast_util;
use ast_util::unspan;

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq)]
/// A binary operatior within an [`Expr::BinOp`]
pub enum BinOperator {
    /// An addition operator
    #[doc(alias = "+")]
    Add = 0,
    /// A subtraction operator
    #[doc(alias = "*")]
    Sub = 1,
    /// A multiplication operator
    #[doc(alias = "*")]
    Mul = 2,
    /// A division operator
    #[doc(alias = "/")]
    Div = 3,
}

impl BinOperator {
    const fn apply(self, a: i64, b: i64) -> i64 {
        match self {
            BinOperator::Add => a + b,
            BinOperator::Sub => a - b,
            BinOperator::Mul => a * b,
            BinOperator::Div => a / b,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
/// An assembler expression, evaluated into a number when assembling
///
/// Expressions must be fully resolvable when assembling, and cannot depend on the assembled code.
///
/// There are three types of expression that stand on their own:
/// * [A literal number] - an integer from `0` through [`i64::MAX`], written in decimal.
/// * [A character literal] - either a single ASCII character other than `'` or `\`, or an escape
///   sequence[^escape], enclosed within single quotes
/// * [A label] - a text identifier accepted by [`chumsky::text::ident`]. Evaluates to the
///   beginning index of the first directive appearing in or after a [line] with the same label.
///
/// Additionally, expressions can be defined in relation to other expressions, in a few ways:
///
/// An expression can be [wrapped in parentheses] to ensure that it's evaluated before any other
/// expressions that depend on it:
///
/// ```code
/// (expr)
/// ```
///
/// An expression can be [negated with `-`]. This unsurprisingly evaluates to the negation of its
/// right-hand side.
///
/// ```code
/// -expr
/// ```
///
/// Two expressions can be combined using [basic arithmetic operations]:
///
/// ```code
/// expr * expr
/// expr / expr
/// expr + expr
/// expr - expr
/// ```
///
/// The order of operations is standard:
/// 1. Parentheses
/// 2. Multiplication and Division, from Left to Right
/// 3. Addition and Subtraction, from Left to Right
///
/// [A literal number]: Expr::Number
/// [A character literal]: Expr::AsciiChar
/// [A label]: Expr::Ident
/// [line]: Line
/// [wrapped in parentheses]: Expr::Parenthesized
/// [negated with `-`]: Expr::Negate
/// [basic arithmetic operations]: Expr::BinOp
/// [^escape]: see [`Directive::Ascii`] for a list of supported escapes
pub enum Expr<'a> {
    /// a 64-bit integer
    Number(i64),
    /// An ASCII character literal
    AsciiChar(u8),
    /// a label
    Ident(&'a str),
    /// a binary operation
    BinOp {
        /// the left-hand-side expression
        lhs: Box<Spanned<Expr<'a>>>,
        /// the operation to perform
        op: Spanned<BinOperator>,
        /// the right-hand-side expression
        rhs: Box<Spanned<Expr<'a>>>,
    },
    /// the negation of the inner expression
    Negate(Box<Spanned<Expr<'a>>>),
    #[doc(hidden)]
    /// A unary plus sign, which evaluates to the value of its right-hand side. It's defined for
    /// compatibility with the [proposed assembly syntax] from the Esolangs Community Wiki, but
    /// has no use that I can see.
    ///
    /// [proposed assembly syntax]: <https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax>
    UnaryAdd(Box<Spanned<Expr<'a>>>),
    /// an inner expression in parentheses
    Parenthesized(Box<Spanned<Expr<'a>>>),
}

/// An error that occured while trying to generate the intcode from the AST.
#[derive(Debug)]
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

impl<'a> Expr<'a> {
    /// Given a mapping of labels to indexes, try to resolve into a concrete value.
    ///
    /// # Errors
    ///
    /// If a label can't be found within `labels`, it will return that label as an Err value
    pub fn resolve(self, labels: &HashMap<&'a str, i64>) -> Result<i64, &'a str> {
        macro_rules! inner {
            ($i: ident) => {
                $i.inner.resolve(labels)?
            };
        }
        match self {
            Expr::Number(n) => Ok(n),
            Expr::AsciiChar(c) => Ok(i64::from(c)),
            Expr::Ident(s) => labels.get(s).copied().ok_or(s),
            Expr::BinOp { lhs, op, rhs } => Ok(op.inner.apply(inner!(lhs), inner!(rhs))),
            Expr::Negate(expr) => Ok(-inner!(expr)),
            Expr::UnaryAdd(expr) | Expr::Parenthesized(expr) => Ok(inner!(expr)),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
/// A simple tuple struct containing the parameter mode and the expression for the parameter
pub struct Parameter<'a>(pub ParamMode, pub Box<OuterExpr<'a>>);

impl Parameter<'_> {
    /// Return the [span](SimpleSpan) of the parameter
    #[must_use]
    pub const fn span(&self) -> SimpleSpan {
        match self.0 {
            ParamMode::Positional => self.1.span(),
            ParamMode::Immediate | ParamMode::Relative => SimpleSpan {
                start: self.1.span().start,
                ..self.1.span()
            },
        }
    }
}

/// An Intcode machine instruction
///
/// There are 10 defined intcode instructions, which take varying numbers of parameters:
///
/// | Instruction | Syntax        | Opcode | Pseudocode                 |
/// |-------------|---------------|--------|----------------------------|
/// | [ADD]       | `ADD a, b, c` | 1      | `c = a + b`                |
/// | [MUL]       | `MUL a, b, c` | 2      | `c = a * b`                |
/// | [IN]        | `IN a`        | 3      | `a = input_num()`          |
/// | [OUT]       | `OUT a`       | 4      | `yield a`                  |
/// | [JNZ]       | `JNZ a, b`    | 5      | `if b != 0: goto a`        |
/// | [JZ]        | `JZ a, b`     | 6      | `if b == 0: goto a`        |
/// | [LT]        | `LT a, b, c`  | 7      | `c = if (1 < v) 1 else 0`  |
/// | [EQ]        | `EQ a, b, c`  | 8      | `c = if (a == b) 1 else 0` |
/// | [RBO]       | `RBO a`       | 9      | `base_offset += a`         |
/// | [HALT]      | `HALT`        | 99     | `exit()`                   |
///
/// Additionally, for compatibility with the [proposed assembly syntax] that this was based on, the
/// following aliases are defined:
///
/// | Alias  | Instruction |
/// |--------|-------------|
/// | `INCB` | `RBO`       |
/// | `SEQ`  | `EQ`        |
/// | `SLT`  | `LT`        |
///
/// Each parameter consists of an optional [mode specifier], followed by a single [expression].
///
/// [ADD]: Instr::Add  
/// [MUL]: Instr::Mul  
/// [IN]: Instr::In    
/// [OUT]: Instr::Out  
/// [JNZ]: Instr::Jnz  
/// [JZ]: Instr::Jz    
/// [LT]: Instr::Lt  
/// [EQ]: Instr::Eq  
/// [RBO]: Instr::Rbo
/// [HALT]: Instr::Halt
/// [expression]: Expr
/// [mode specifier]: ParamMode
///
#[derive(Debug, Clone, PartialEq)]
#[repr(u8)]
pub enum Instr<'a> {
    /// `ADD a, b, c`: store `a + b` in `c`
    ///
    /// If `c` is in [immediate mode] at time of execution, instruction will trap
    ///
    /// [immediate mode]: ParamMode::Immediate
    Add(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 1,
    /// `MUL a, b, c`: store `a * b` in `c`
    ///
    /// If `c` is in [immediate mode] at time of execution, instruction will trap
    ///
    /// [immediate mode]: ParamMode::Immediate
    Mul(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 2,
    /// `IN a`: store the next input number in `a`
    ///
    /// If no input is available, machine will wait.
    /// If `a` is in [immediate mode] at time of execution, instruction will trap
    ///
    /// [immediate mode]: ParamMode::Immediate
    In(Parameter<'a>) = 3,
    /// `OUT a`: output `a`
    Out(Parameter<'a>) = 4,
    /// `JNZ a, b`: jump to `b` if `a` is nonzero
    Jnz(Parameter<'a>, Parameter<'a>) = 5,
    /// `JZ a, b`: jump to `b` if `a` is zero
    Jz(Parameter<'a>, Parameter<'a>) = 6,
    /// `LT a, b`: store `(a < b) as i64` in `c`
    ///
    /// If `c` is in [immediate mode] at time of execution, instruction will trap
    ///
    /// [immediate mode]: ParamMode::Immediate
    #[doc(alias("SLT", "LT", "CMP"))]
    Lt(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 7,
    /// `EQ a, b`: store `(a == b) as i64` in `c`
    ///
    /// If `c` is in [immediate mode] at time of execution, instruction will trap
    ///
    /// [immediate mode]: ParamMode::Immediate
    #[doc(alias("SEQ", "EQ", "CMP"))]
    Eq(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 8,
    /// `RBO a`: add `a` to Relative Base
    #[doc(alias("INCB", "relative base", "relative base offset"))]
    Rbo(Parameter<'a>) = 9,
    /// `HALT`: exit program
    Halt = 99,
}

impl Instr<'_> {
    /// Return the number of integers the instruction will resolve to
    #[must_use]
    pub const fn size(&self) -> i64 {
        match self {
            Instr::Halt => 1,
            Instr::In(..) | Instr::Out(..) | Instr::Rbo(..) => 2,
            Instr::Jnz(..) | Instr::Jz(..) => 3,
            Instr::Add(..) | Instr::Mul(..) | Instr::Lt(..) | Instr::Eq(..) => 4,
        }
    }
}

/// An identifier, [spanned](Spanned) by its position in the source code
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Label<'a>(pub Spanned<&'a str>);

/// An outermost expression with an optional label
#[derive(Debug, Clone, PartialEq)]
pub struct OuterExpr<'a> {
    /// the (optional) label of the expression
    pub labels: Vec<Label<'a>>,
    /// the expression itself
    pub expr: Spanned<Expr<'a>>,
}

impl OuterExpr<'_> {
    /// Return the span of the outer expression
    #[must_use]
    pub const fn span(&self) -> SimpleSpan {
        if let Some(spanned) = self.labels.as_slice().first() {
            SimpleSpan {
                start: spanned.0.span.start,
                ..self.expr.span
            }
        } else {
            self.expr.span
        }
    }
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

impl<'a> Instr<'a> {
    /// try to encode the instructions into an opaque [Iterator] of [`i64`]s, using the label
    /// resolution provided
    ///
    /// # Errors
    ///
    /// If a parameter depends on a label that isn't defined in labels, returns an
    /// [`AssemblyError::UnresolvedLabel`] with the label in question, along with its span within
    /// the source.
    pub fn resolve(
        self,
        labels: &HashMap<&'a str, i64>,
    ) -> Result<impl Iterator<Item = i64>, AssemblyError<'a>> {
        macro_rules! process_param {
            ($param: ident * $multiplier: literal, &mut $instr: ident) => {{
                let Parameter(mode, outer_expr) = $param;
                let Spanned { inner: expr, span } = outer_expr.expr;
                $instr += mode as i64 * $multiplier;
                expr.resolve(labels)
                    .map_err(|label| AssemblyError::UnresolvedLabel { label, span })?
            }};
        }

        macro_rules! process_instr {
            ($val: literal, $a: tt, $b: tt, $c: tt) => {{
                let mut instr = $val;
                let a = process_param!($a * 100, &mut instr);
                let b = process_param!($b * 1000, &mut instr);
                let c = process_param!($c * 10000, &mut instr);
                Ok(StackIter::Four(instr, a, b, c))
            }};
            ($val: literal, $a: tt, $b: tt) => {{
                let mut instr = $val;
                let a = process_param!($a * 100, &mut instr);
                let b = process_param!($b * 1000, &mut instr);
                Ok(StackIter::Three(instr, a, b))
            }};
            ($val: literal, $a: tt) => {{
                let mut instr = $val;
                let a = process_param!($a * 100, &mut instr);
                Ok(StackIter::Two(instr, a))
            }};
            ($val: literal) => {{ Ok(StackIter::One($val)) }};
        }

        match self.clone() {
            Instr::Add(a, b, c) => process_instr!(1, a, b, c),
            Instr::Mul(a, b, c) => process_instr!(2, a, b, c),
            Instr::In(a) => process_instr!(3, a),
            Instr::Out(a) => process_instr!(4, a),
            Instr::Jnz(a, b) => process_instr!(5, a, b),
            Instr::Jz(a, b) => process_instr!(6, a, b),
            Instr::Lt(a, b, c) => process_instr!(7, a, b, c),
            Instr::Eq(a, b, c) => process_instr!(8, a, b, c),
            Instr::Rbo(a) => process_instr!(9, a),
            Instr::Halt => process_instr!(99),
        }
    }
}

#[non_exhaustive]
#[derive(Debug, PartialEq, Clone)]
/// The directive of a line
///
/// This is what actually gets output into the program
pub enum Directive<'a> {
    /// An arbitrary sequence of comma-separated assembler expressions
    ///
    /// # Example
    ///
    /// ```
    /// const ASM_SRC: &str = "data: DATA 1, 2, data + 3, 4 * 4 / 4, 5";
    /// let assembled = ial::asm::assemble(ASM_SRC).unwrap();
    /// assert_eq!(assembled[..], [1, 2, 3, 4, 5][..]);
    /// ```
    Data(Vec<Spanned<Expr<'a>>>),
    /// A string of text, encoded in accordance with the "Aft Scaffolding Control and Information
    /// Interface" [specification](https://adventofcode.com/2019/day/17), surrounded by
    /// double-quotes.
    ///
    /// Each character in the string can be either:
    /// * an ASCII character other than `'\'` or `'"'`
    /// * an escape sequence
    ///
    /// The following escape sequences are supported:
    ///
    /// | sequence | meaning                                                             |
    /// |----------|---------------------------------------------------------------------|
    /// | `\\`     | a literal backslash                                                 |
    /// | `\'`     | a literal single quote                                              |
    /// | `\"`     | a literal double-quote                                              |
    /// | `\n`     | a line-feed                                                         |
    /// | `\t`     | a horizontal tab                                                    |
    /// | `\r`     | a carriage-return                                                   |
    /// | `\e`     | an escape character                                                 |
    /// | `\O`     | a byte with the value O, where O is a 1, 2, or 3 digit octal number |
    /// | `\xHH`   | a byte with the value HH, where HH is a 2-digit hexadecimal number  |
    ///
    /// # Example
    ///
    /// ```
    /// const ASM_SRC: &str = r#"ASCII "Hello, world!\n""#;
    /// let assembled = ial::asm::assemble(ASM_SRC).unwrap();
    /// let expected: [i64; 14] = core::array::from_fn(|i| i64::from(b"Hello, world!\n"[i] ));
    /// assert_eq!(assembled[..], expected[..]);
    /// ```
    Ascii(Spanned<Vec<u8>>),
    /// An [instruction](Instr)
    Instruction(Box<Instr<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
/// A single line of assembly, containing an optional label, an optional directive, and an optional
/// comment - the last of which is not stored.
pub struct Line<'a> {
    /// the labels for the line
    pub labels: Vec<Label<'a>>,
    /// the directive for the line, if applicable
    pub directive: Option<Spanned<Directive<'a>>>,
}

impl Directive<'_> {
    /// Return the number of integers that this [`Directive`] will resolve to.
    ///
    /// # Errors
    ///
    /// If called with an [`Data`][Directive::Data] or [`Ascii`][Directive::Ascii] variant longer
    /// than [`i64::MAX`], returns the length as an [`Err`] value.
    pub fn size(&self) -> Result<i64, usize> {
        match self {
            Directive::Data(exprs) => exprs.len().try_into().map_err(|_| exprs.len()),
            Directive::Ascii(text) => text.len().try_into().map_err(|_| text.len()),
            Directive::Instruction(instr) => Ok(instr.size()),
        }
    }
    fn dtype(&self) -> DirectiveKind {
        match self {
            Directive::Data(_) => DirectiveKind::Data,
            Directive::Ascii(_) => DirectiveKind::Ascii,
            Directive::Instruction(_) => DirectiveKind::Instruction,
        }
    }
}

impl<'a> Line<'a> {
    /// Consume the line, appending the bytes to `v`.
    ///
    /// # Errors
    ///
    /// If [`self.directive`] is either an [`Instruction`] or a [`Data`] directive, and an
    /// expression fails to [resolve] due to a missing label, returns an
    /// [`AssemblyError::UnresolvedLabel`] pointing to the source of the missing label.
    ///
    /// [`self.directive`]: Line::directive
    /// [`Instruction`]: Directive::Instruction
    /// [`Data`]: Directive::Data
    /// [resolve]: Expr::resolve
    pub fn encode_into(
        self,
        v: &mut Vec<i64>,
        labels: &HashMap<&'a str, i64>,
    ) -> Result<(), AssemblyError<'a>> {
        if let Some(Spanned {
            inner: directive, ..
        }) = self.directive
        {
            match directive {
                Directive::Data(exprs) => {
                    for expr in exprs {
                        let Spanned { inner: expr, span } = expr;
                        v.push(
                            expr.resolve(labels)
                                .map_err(|label| AssemblyError::UnresolvedLabel { label, span })?,
                        );
                    }
                }
                Directive::Ascii(text) => v.extend(unspan(text).into_iter().map(i64::from)),
                Directive::Instruction(instr) => {
                    v.extend(instr.resolve(labels)?);
                }
            }
        }
        Ok(())
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
        |label: &'a str, index, span: SimpleSpan| -> Result<(), AssemblyError<'a>> {
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
            index += directive
                .size()
                .map_err(|size| AssemblyError::DirectiveTooLarge {
                    size,
                    span: directive.span,
                })?;

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
/// use ial::asm::{assemble_ast, Line, Directive, Instr, Parameter};
/// use chumsky::prelude::{Spanned, SimpleSpan};
///
/// let inner = Directive::Instruction(Box::new(Instr::Halt));
///
/// let ast = vec![
///     Line { labels: vec![], directive: Some(Spanned { inner, span: SimpleSpan::default() }) }
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
