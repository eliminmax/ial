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
//! Labels are parsed using [chumsky::text::ident], so identifiers the same rules as [Rust], except
//! without Unicode normalization.
//!
//! # Example
//!
//! ```
//! use intcode::prelude::*;
//! use intcode::asm::assemble;
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
//! use intcode::{prelude::*, asm::ast_prelude::*};
//!
//! let ast = build_ast("idle_loop: JZ #0, #idle_loop").unwrap();
//! let expected = vec![Line {
//!     label: Some("idle_loop"),
//!     inner: Some(Spanned {
//!         span: SimpleSpan { start: 10, end: 28, context: () },
//!         inner: Directive::Instruction(Box::new(Instr::Jz(
//!             Parameter (
//!                 Spanned {
//!                     inner: ParamMode::Immediate,
//!                     span: SimpleSpan { start: 14, end: 15, context: () },
//!                 },
//!                 Box::new(Spanned {
//!                     inner: Expr::Number(0),
//!                     span: SimpleSpan { start: 15, end: 16, context: () },
//!                 }),
//!             ),
//!             Parameter (
//!                 Spanned {
//!                     inner: ParamMode::Immediate,
//!                     span: SimpleSpan { start: 18, end: 19, context: () },
//!                 },
//!                 Box::new(Spanned {
//!                     inner: Expr::Ident("idle_loop"),
//!                     span: SimpleSpan { start: 19, end: 28, context: () },
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
//! The [ast_util] module provides some small functions and macros to express things more
//! concicely:
//!
//! ```
//! use intcode::{prelude::*, asm::ast_prelude::*};
//! use intcode::asm::ast_util::*;
//! let ast = build_ast("idle_loop: JZ #0, #idle_loop").unwrap();
//! let expected = vec![Line {
//!     label: Some("idle_loop"),
//!     inner: Some(span(
//!         Directive::Instruction(Box::new(Instr::Jz(
//!             param!(#<expr!(0);>[14..16]),
//!             param!(#<expr!(idle_loop);>[18..28])
//!         ))),
//!         10..28
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

use ast_prelude::*;
use chumsky::prelude::*;
use chumsky::text::Char;
use std::collections::HashMap;

/// a small module that re-exports the types needed to work with the AST of the assembly language.
pub mod ast_prelude {
    pub use crate::{ParamMode, asm};
    pub use asm::{
        BinOperator, Directive, Expr, Instr, Line, Parameter, assemble, assemble_ast, build_ast,
    };
    pub use chumsky::span::{SimpleSpan, Spanned};
}

/// Small utility functions and macros for making it less painful to work with the AST
pub mod ast_util;

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
/// There are two types of expression that stand on their own:
/// * [A literal number] - an integer from `0` through [`i64::MAX`], written in decimal.
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
/// [A label]: Expr::Ident
/// [line]: Line
/// [wrapped in parentheses]: Expr::Inner
/// [negated with `-`]: Expr::Negate
/// [basic arithmetic operations]: Expr::BinOp
///
pub enum Expr<'a> {
    /// a 64-bit integer
    Number(i64),
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
    UnresolvedLabel(&'a str),
    /// A label was defined more than once
    DuplicateLabel(&'a str),
    /// A directive resolved to more than [`i64::MAX`] ints, and somehow didn't crash your computer
    /// before it was time to size things up
    TooLarge(usize),
}

impl<'a> Expr<'a> {
    /// Given a mapping of labels to indexes, try to resolve into a concrete value.
    /// If a label can't be resolved, it will return that label
    pub fn resolve(self, labels: &HashMap<&'a str, i64>) -> Result<i64, AssemblyError<'a>> {
        macro_rules! inner {
            ($i: ident) => {
                $i.inner.resolve(labels)?
            };
        }
        match self {
            Expr::Number(n) => Ok(n),
            Expr::Ident(s) => labels
                .get(s)
                .copied()
                .ok_or(AssemblyError::UnresolvedLabel(s)),
            Expr::BinOp { lhs, op, rhs } => Ok(op.inner.apply(inner!(lhs), inner!(rhs))),
            Expr::Negate(expr) => Ok(-inner!(expr)),
            Expr::UnaryAdd(expr) | Expr::Parenthesized(expr) => Ok(inner!(expr)),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
/// A simple tuple struct containing the parameter mode and the expression for the parameter
pub struct Parameter<'a>(pub ParamMode, pub Box<Spanned<Expr<'a>>>);

impl Parameter<'_> {
    /// Return the [span](SimpleSpan)` of the parameter
    pub const fn span(&self) -> SimpleSpan {
        match self.0 {
            ParamMode::Positional => self.1.span,
            ParamMode::Immediate | ParamMode::Relative => SimpleSpan {
                start: self.1.span.start,
                ..self.1.span
            },
        }
    }
}

fn unspan<T>(Spanned { inner, .. }: Spanned<T>) -> T {
    inner
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
    pub const fn size(&self) -> i64 {
        match self {
            Instr::Halt => 1,
            Instr::In(..) | Instr::Out(..) | Instr::Rbo(..) => 2,
            Instr::Jnz(..) | Instr::Jz(..) => 3,
            Instr::Add(..) | Instr::Mul(..) | Instr::Lt(..) | Instr::Eq(..) => 4,
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
    pub fn resolve(
        self,
        labels: &HashMap<&'a str, i64>,
    ) -> Result<impl Iterator<Item = i64>, AssemblyError<'a>> {
        macro_rules! process_param {
            ($param: ident * $multiplier: literal, &mut $instr: ident) => {{
                let Parameter(mode, expr) = $param;
                $instr += mode as i64 * $multiplier;
                unspan(*expr).resolve(labels)?
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
#[derive(Debug, PartialEq)]
/// The directive of a line
///
/// This is what actually gets output into the program
pub enum Directive<'a> {
    /// An arbitrary sequence of comma-separated assembler expressions
    DataDirective(Vec<Spanned<Expr<'a>>>),
    /// A string of text, encoded in accordance with the "Aft Scaffolding Control and Information
    /// Interface" [specification](https://adventofcode.com/2019/day/17)
    Ascii(Spanned<Vec<u8>>),
    /// An [instruction](Instr)
    Instruction(Box<Instr<'a>>),
}

#[derive(Debug, PartialEq)]
/// A single line of assembly, containing an optional label, an optional directive, and an optional
/// comment - the last of which is not stored.
pub struct Line<'a> {
    /// the label for the line, if applicable
    pub label: Option<Spanned<&'a str>>,
    /// the directive for the line, if applicable
    pub inner: Option<Spanned<Directive<'a>>>,
}

macro_rules! padded {
    ($inner: expr) => {{ $inner.padded_by(text::inline_whitespace()) }};
}

macro_rules! with_sep {
    ($inner: expr) => {{ padded!($inner.then_ignore(text::inline_whitespace().at_least(1))) }};
}

type RichErr<'a> = chumsky::extra::Err<Rich<'a, char>>;

fn param<'a>() -> impl Parser<'a, &'a str, Parameter<'a>, RichErr<'a>> {
    padded!(
        choice((
            just('#').to(ParamMode::Immediate),
            just('@').to(ParamMode::Relative),
            empty().to(ParamMode::Positional),
        ))
        .then(expr())
    )
    .map(|(mode, expr)| Parameter(mode, Box::new(expr)))
}

fn mnemonic<'a>(kw: &'static str) -> impl Parser<'a, &'a str, (), RichErr<'a>> {
    text::ascii::ident().try_map(move |s: &'a str, span| {
        if s.eq_ignore_ascii_case(kw) {
            Ok(())
        } else {
            Err(Rich::custom(span, format!("failed to match keyword {kw}")))
        }
    })
}

fn instr<'a>() -> impl Parser<'a, &'a str, Instr<'a>, RichErr<'a>> {
    macro_rules! params {
        ($n: literal) => {{
            param()
                .separated_by(padded!(just(',')))
                .exactly($n)
                .collect::<Vec<_>>()
                .map(|v| <[Parameter; $n]>::try_from(v).expect("sized"))
        }};
    }
    macro_rules! op {
        ($name: literal, $variant: ident::<1>) => {
            with_sep!(mnemonic($name)).ignore_then(param().map(Instr::$variant))
        };
        ($name: literal, $variant: ident::<2>) => {
            with_sep!(mnemonic($name)).ignore_then((params!(2)).map(|[a, b]| Instr::$variant(a, b)))
        };
        ($name: literal, $variant: ident::<3>) => {
            with_sep!(mnemonic($name))
                .ignore_then((params!(3)).map(|[a, b, c]| Instr::$variant(a, b, c)))
        };
    }

    padded!(choice((
        op!("ADD", Add::<3>),
        op!("MUL", Mul::<3>),
        op!("IN", In::<1>),
        op!("OUT", Out::<1>),
        op!("JNZ", Jnz::<2>),
        op!("JZ", Jz::<2>),
        op!("LT", Lt::<3>),
        op!("SLT", Lt::<3>),
        op!("EQ", Eq::<3>),
        op!("SEQ", Eq::<3>),
        op!("RBO", Rbo::<1>),
        op!("INCB", Rbo::<1>),
        just("HALT").to(Instr::Halt),
    )))
}

fn expr<'a>() -> impl Parser<'a, &'a str, Spanned<Expr<'a>>, RichErr<'a>> + Clone {
    recursive(|expr| {
        let int = text::int(10).try_map(|s: &str, span| {
            s.parse::<i64>()
                .map(Expr::Number)
                .map_err(|e| Rich::custom(span, format!("error parsing {s} as i64: {e}")))
        });
        let ident = text::ident().map(|s: &str| Expr::Ident(s));
        let bracketed = expr
            .delimited_by(just('('), just(')'))
            .map(|e| Expr::Parenthesized(Box::new(e)));
        let atom = int.or(ident).or(bracketed).spanned();
        let unary = padded!(one_of("-+").spanned()).repeated().foldr(
            atom,
            |Spanned { inner, mut span }: Spanned<char>, rhs: Spanned<Expr<'a>>| {
                span.end = rhs.span.end;
                Spanned {
                    inner: match inner {
                        '+' => Expr::UnaryAdd(Box::new(rhs)),
                        '-' => Expr::Negate(Box::new(rhs)),
                        _ => unreachable!(),
                    },
                    span,
                }
            },
        );

        let folder = |lhs: Spanned<Expr<'a>>,
                      (op, rhs): (Spanned<BinOperator>, Spanned<Expr<'a>>)| {
            let span = SimpleSpan {
                start: lhs.span.start,
                end: rhs.span.end,
                context: (),
            };
            let inner = Expr::BinOp {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            };
            Spanned { span, inner }
        };

        let prod = unary.clone().foldl(
            padded!(
                choice((
                    just('*').to(BinOperator::Mul),
                    just('/').to(BinOperator::Div),
                ))
                .spanned()
            )
            .then(unary)
            .repeated(),
            folder,
        );

        prod.clone().foldl(
            padded!(
                choice((
                    just('+').to(BinOperator::Add),
                    just('-').to(BinOperator::Sub),
                ))
                .spanned()
            )
            .then(prod)
            .repeated(),
            folder,
        )
    })
}

impl Directive<'_> {
    /// return the number of integers that this [`Directive`] will resolve to.
    pub fn size(&self) -> Result<i64, usize> {
        match self {
            Directive::DataDirective(exprs) => exprs.len().try_into().map_err(|_| exprs.len()),
            Directive::Ascii(text) => text.len().try_into().map_err(|_| text.len()),
            Directive::Instruction(instr) => Ok(instr.size()),
        }
    }
}

impl<'a> Line<'a> {
    /// Consume the line, appending the bytes to `v`. If any expressions fail to resolve, bubble up
    /// the error.
    pub fn encode_into(
        self,
        v: &mut Vec<i64>,
        labels: &HashMap<&'a str, i64>,
    ) -> Result<(), AssemblyError<'a>> {
        if let Some(Spanned { inner, .. }) = self.inner {
            match inner {
                Directive::DataDirective(exprs) => {
                    for expr in exprs {
                        v.push(unspan(expr).resolve(labels)?);
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

fn ascii_parse<'a>() -> impl Parser<'a, &'a str, Spanned<Vec<u8>>, RichErr<'a>> {
    const HEX_DIGITS: &str = "0123456789ABCDEFabcdef";
    const OCT_DIGITS: &str = "01234567";

    fn strict_hex_val(c: char) -> u8 {
        assert!(c.is_ascii());
        #[expect(
            non_contiguous_range_endpoints,
            reason = "mask leaves 1 byte value before b'a' possible"
        )]
        match c as u8 | 0x20 {
            d @ b'0'..=b'9' => d - b'0',
            l @ b'a'..=b'f' => l - b'a' + 10,
            ..32 | 64..96 => unreachable!("masked out"),
            128 => unreachable!("known ascii"),
            c => panic!("invalid hex digit: {}", c.escape_ascii()),
        }
    }
    just('"')
        .ignore_then(
            choice((
                none_of("\"\\")
                    .filter(|c: &char| c.is_ascii())
                    .map(|c| c as u8),
                just('\\').ignore_then(choice((
                    just('\\').to(b'\\'),
                    just('\'').to(b'\''),
                    just('\"').to(b'\"'),
                    just('n').to(b'\n'),
                    just('t').to(b'\t'),
                    just('r').to(b'\r'),
                    just('e').to(b'\x1b'),
                    just('3')
                        .ignore_then(one_of(OCT_DIGITS).then(one_of(OCT_DIGITS)))
                        .map(|(a, b)| 0o300 + ((a as u8 - b'0') * 8) + (b as u8 - b'0')),
                    (one_of(OCT_DIGITS).repeated().at_least(1).at_most(2))
                        .fold(0, |acc, x| acc * 8 + (x as u8 - b'0')),
                    just('x')
                        .ignore_then(one_of(HEX_DIGITS).then(one_of(HEX_DIGITS)))
                        .map(|(a, b)| (strict_hex_val(a) << 4) | strict_hex_val(b)),
                ))),
            ))
            .repeated()
            .collect(),
        )
        .then_ignore(just('"'))
        .spanned()
}

fn line_inner<'a>() -> impl Parser<'a, &'a str, Option<Spanned<Directive<'a>>>, RichErr<'a>> {
    choice((
        (with_sep!(just("DATA"))
            .ignore_then(expr().separated_by(padded!(just(","))).collect())
            .map(Directive::DataDirective)),
        with_sep!(just("ASCII"))
            .ignore_then(ascii_parse())
            .map(Directive::Ascii),
        instr().map(Box::new).map(Directive::Instruction),
    ))
    .spanned()
    .or_not()
}

fn parse_line<'a>() -> impl Parser<'a, &'a str, Line<'a>, RichErr<'a>> {
    padded!(
        (text::ident().then_ignore(just(":")).spanned())
            .or_not()
            .then(line_inner())
            .map(|(label, inner)| Line { label, inner })
            .then_ignore(
                (padded!(just(';')).then((any().filter(|c: &char| !c.is_newline())).repeated()))
                    .or_not(),
            )
    )
}

fn grammar<'a>() -> impl Parser<'a, &'a str, Vec<Line<'a>>, RichErr<'a>> {
    parse_line().separated_by(just("\n")).collect()
}

/// Parse the assembly code into a [`Vec<Line>`], or a [`Vec<Rich<char>>`] on failure.
///
/// # Example
///
/// ```
/// use intcode::asm::build_ast;
/// use intcode::Interpreter;
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
pub fn build_ast<'a>(code: &'a str) -> Result<Vec<Line<'a>>, Vec<Rich<'a, char>>> {
    grammar().parse(code).into_result()
}

/// Assemble an AST in the form of a [`Vec<Line>`] into a [`Vec<i64>`]
///
/// On failure, returns an [`AssemblyError`].
///
/// # Example
///
/// ```
/// use intcode::asm::{assemble_ast, Line, Directive, Instr, Parameter};
/// use chumsky::prelude::{Spanned, SimpleSpan};
///
/// let inner = Directive::Instruction(Box::new(Instr::Halt));
///
/// let ast = vec![
///     Line { label: None, inner: Some(Spanned { inner, span: SimpleSpan::default() }) }
/// ];
///
/// assert_eq!(assemble_ast(ast).unwrap(), vec![99]);
/// ```
pub fn assemble_ast<'a>(code: Vec<Line<'a>>) -> Result<Vec<i64>, AssemblyError<'a>> {
    let mut labels: HashMap<&'a str, i64> = HashMap::new();
    let mut index = 0;
    for line in code.iter() {
        if let Some(Spanned { inner: label, .. }) = line.label
            && labels.insert(label, index).is_some()
        {
            return Err(AssemblyError::DuplicateLabel(label));
        }
        if let Some(inner) = line.inner.as_ref() {
            index += inner.size().map_err(AssemblyError::TooLarge)?;
        }
    }

    let mut v = Vec::with_capacity(index.try_into().unwrap_or_default());

    for line in code {
        line.encode_into(&mut v, &labels)?;
    }

    Ok(v)
}

/// An error that indicates where in the assembly process a failure occured, and wraps around the
/// error type for that part of the process
#[derive(Debug)]
pub enum AsmError<'a> {
    /// Failure to build the AST
    BuildAst(Vec<Rich<'a, char>>),
    /// Failure to assemble the parsed AST
    Assemble(AssemblyError<'a>),
}

/// Try to assemble the code into a [`Vec<i64>`]
///
/// This is a thin convenience wrapper around [`build_ast`] and [`assemble_ast`].
#[inline]
pub fn assemble<'a>(code: &'a str) -> Result<Vec<i64>, AsmError<'a>> {
    assemble_ast(build_ast(code).map_err(AsmError::BuildAst)?).map_err(AsmError::Assemble)
}

mod fmt_impls;

#[cfg(test)]
mod ast_tests;
