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
//! The first component is a label, which will resolve to the index of the next intcode int added.
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
//! [NASM]: <https://www.nasm.us/doc/nasm03.html>
//! [proposed assembly syntax]: <https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax>
//! [Rust](https://doc.rust-lang.org/reference/identifiers.html)

use super::ParamMode;
use chumsky::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;

#[cfg_attr(test, derive(PartialEq))]
#[non_exhaustive]
#[derive(Debug, Clone)]
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

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug, Clone)]
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
        lhs: Arc<Spanned<Expr<'a>>>,
        /// the operation to perform
        op: Spanned<BinOperator>,
        /// the right-hand-side expression
        rhs: Arc<Spanned<Expr<'a>>>,
    },
    /// the negation of the inner expression
    Negate(Arc<Spanned<Expr<'a>>>),
    #[doc(hidden)]
    /// A unary plus sign, which evaluates to the value of its right-hand side. It's defined for
    /// compatibility with the [proposed assembly syntax] from the Esolangs Community Wiki, but
    /// has no use that I can see.
    ///
    /// [proposed assembly syntax]: <https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax>
    UnaryAdd(Arc<Spanned<Expr<'a>>>),
    /// an inner expression in parentheses
    Inner(Arc<Spanned<Expr<'a>>>),
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
                Arc::unwrap_or_clone($i).inner.resolve(labels)?
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
            Expr::UnaryAdd(expr) | Expr::Inner(expr) => Ok(inner!(expr)),
        }
    }
}

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug, Clone)]
/// A simple tuple struct containing the parameter mode and the expression for the parameter
pub struct Parameter<'a>(pub Spanned<ParamMode>, pub Arc<Spanned<Expr<'a>>>);

fn unspan<T>(Spanned { inner, .. }: Spanned<T>) -> T {
    inner
}

/// An Intcode machine instruction
///
/// There are 10 defined intcode instructions, which take varying numbers of parameters:
///
/// | Instruction | Syntax          | Opcode | Pseudocode                 |
/// |-------------|-----------------|--------|----------------------------|
/// | [ADD]       | `ADD a, b, (c)` | 1      | `c = a + b`                |
/// | [MUL]       | `MUL a, b, (c)` | 2      | `c = a * b`                |
/// | [IN]        | `IN (a)`        | 3      | `a = input_num()`          |
/// | [OUT]       | `OUT a`         | 4      | `yield a`                  |
/// | [JNZ]       | `JNZ a, b`      | 5      | `if b != 0: goto a`        |
/// | [JZ]        | `JZ a, b`       | 6      | `if b == 0: goto a`        |
/// | [SLT]       | `LT a, b, (c)`  | 7      | `c = if (1 < v) 1 else 0`  |
/// | [SEQ]       | `EQ a, b, (c)`  | 8      | `c = if (a == b) 1 else 0` |
/// | [INCB]      | `INCB a`        | 9      | `base_offset += a`         |
/// | [HALT]      | `HALT`          | 99     | `exit()`                   |
///
/// Each parameter consists of an optional [mode specifier], followed by a single [expression].
/// Parameters marked in parentheses cannot be in [immediate mode].
///
/// [ADD]: Instr::Add  
/// [MUL]: Instr::Mul  
/// [IN]: Instr::In    
/// [OUT]: Instr::Out  
/// [JNZ]: Instr::Jnz  
/// [JZ]: Instr::Jz    
/// [SLT]: Instr::Slt  
/// [SEQ]: Instr::Seq  
/// [INCB]: Instr::Incb
/// [HALT]: Instr::Halt
/// [expression]: Expr
/// [mode specifier]: ParamMode
/// [immediate mode]: ParamMode::Immediate
///
#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug, Clone)]
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
    /// `JNZ a, b`: jump to `a` if `b` is nonzero
    Jnz(Parameter<'a>, Parameter<'a>) = 5,
    /// `JZ a, b`: jump to `a` if `b` is zero
    Jz(Parameter<'a>, Parameter<'a>) = 6,
    /// `LT a, b`: store `(a < b) as i64` in `c`
    ///
    /// If `c` is in [immediate mode] at time of execution, instruction will trap
    ///
    /// [immediate mode]: ParamMode::Immediate
    #[doc(alias("SLT", "LT", "CMP"))]
    Slt(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 7,
    /// `EQ a, b`: store `(a == b) as i64` in `c`
    ///
    /// If `c` is in [immediate mode] at time of execution, instruction will trap
    ///
    /// [immediate mode]: ParamMode::Immediate
    #[doc(alias("SEQ", "EQ", "CMP"))]
    Seq(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 8,
    /// `INCB a`: add `a` to Relative Base
    Incb(Parameter<'a>) = 9,
    /// `HALT`: exit program
    Halt = 99,
}

impl Instr<'_> {
    /// Return the number of integers the instruction will resolve to
    pub const fn size(&self) -> i64 {
        match self {
            Instr::Halt => 1,
            Instr::In(..) | Instr::Out(..) | Instr::Incb(..) => 2,
            Instr::Jnz(..) | Instr::Jz(..) => 3,
            Instr::Add(..) | Instr::Mul(..) | Instr::Slt(..) | Instr::Seq(..) => 4,
        }
    }
}

// A zero-allocation iterator of instructions
enum InstrIter {
    Four(i64, i64, i64, i64),
    Three(i64, i64, i64),
    Two(i64, i64),
    One(i64),
    Empty,
}

impl Iterator for InstrIter {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            InstrIter::Four(a, b, c, d) => {
                let a = *a;
                *self = Self::Three(*b, *c, *d);
                Some(a)
            }
            InstrIter::Three(a, b, c) => {
                let a = *a;
                *self = Self::Two(*b, *c);
                Some(a)
            }
            InstrIter::Two(a, b) => {
                let a = *a;
                *self = Self::One(*b);
                Some(a)
            }
            InstrIter::One(a) => {
                let a = *a;
                *self = Self::Empty;
                Some(a)
            }
            InstrIter::Empty => None,
        }
    }
}

impl<'a> Instr<'a> {
    /// try to encode the instructions into an opaque [iterator] of [`i64`]s
    ///
    /// [iterator]: Iterator
    pub fn resolve(
        self,
        labels: &HashMap<&'a str, i64>,
    ) -> Result<impl Iterator<Item = i64>, AssemblyError<'a>> {
        macro_rules! process_param {
            ($param: ident * $multiplier: literal, &mut $instr: ident) => {{
                let Parameter(mode, expr) = $param;
                $instr += mode.inner as i64 * $multiplier;
                unspan(Arc::unwrap_or_clone(expr)).resolve(labels)?
            }};
        }

        macro_rules! process_instr {
            ($val: literal, $a: tt, $b: tt, $c: tt) => {{
                let mut instr = $val;
                let a = process_param!($a * 100, &mut instr);
                let b = process_param!($b * 1000, &mut instr);
                let c = process_param!($c * 10000, &mut instr);
                Ok(InstrIter::Four(instr, a, b, c))
            }};
            ($val: literal, $a: tt, $b: tt) => {{
                let mut instr = $val;
                let a = process_param!($a * 100, &mut instr);
                let b = process_param!($b * 1000, &mut instr);
                Ok(InstrIter::Three(instr, a, b))
            }};
            ($val: literal, $a: tt) => {{
                let mut instr = $val;
                let a = process_param!($a * 100, &mut instr);
                Ok(InstrIter::Two(instr, a))
            }};
            ($val: literal) => {{ Ok(InstrIter::One($val)) }};
        }

        match self.clone() {
            Instr::Add(a, b, c) => process_instr!(1, a, b, c),
            Instr::Mul(a, b, c) => process_instr!(2, a, b, c),
            Instr::In(a) => process_instr!(3, a),
            Instr::Out(a) => process_instr!(4, a),
            Instr::Jnz(a, b) => process_instr!(5, a, b),
            Instr::Jz(a, b) => process_instr!(6, a, b),
            Instr::Slt(a, b, c) => process_instr!(7, a, b, c),
            Instr::Seq(a, b, c) => process_instr!(8, a, b, c),
            Instr::Incb(a) => process_instr!(9, a),
            Instr::Halt => process_instr!(99),
        }
    }
}

#[cfg_attr(test, derive(PartialEq))]
#[non_exhaustive]
#[derive(Debug)]
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

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug)]
/// A single line of assembly, containing an optional label, an optional directive, and an optional
/// comment - the last of which is not stored.
pub struct Line<'a> {
    /// the label for the line, if applicable
    pub label: Option<&'a str>,
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
        .spanned()
        .then(expr())
    )
    .map(|(mode, expr)| Parameter(mode, Arc::new(expr)))
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
            with_sep!(just($name)).ignore_then(param().map(Instr::$variant))
        };
        ($name: literal, $variant: ident::<2>) => {
            with_sep!(just($name)).ignore_then((params!(2)).map(|[a, b]| Instr::$variant(a, b)))
        };
        ($name: literal, $variant: ident::<3>) => {
            with_sep!(just($name))
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
        op!("SLT", Slt::<3>),
        op!("LT", Slt::<3>),
        op!("SEQ", Seq::<3>),
        op!("EQ", Seq::<3>),
        op!("INCB", Incb::<1>),
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
            .map(|e| Expr::Inner(Arc::new(e)));
        let atom = int.or(ident).or(bracketed).spanned();
        let unary = padded!(one_of("-+").spanned()).repeated().foldr(
            atom,
            |Spanned { inner, mut span }: Spanned<char>, rhs: Spanned<Expr<'a>>| {
                span.end = rhs.span.end;
                Spanned {
                    inner: match inner {
                        '+' => Expr::UnaryAdd(Arc::new(rhs)),
                        '-' => Expr::Negate(Arc::new(rhs)),
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
                lhs: Arc::new(lhs),
                op,
                rhs: Arc::new(rhs),
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
    text::ident()
        .then_ignore(just(":"))
        .or_not()
        .then(line_inner())
        .map(|(label, inner)| Line { label, inner })
        .then_ignore(
            just(';')
                .then_ignore(text::newline().not().repeated())
                .or_not(),
        )
}

fn grammar<'a>() -> impl Parser<'a, &'a str, Vec<Line<'a>>, RichErr<'a>> {
    parse_line().separated_by(just("\n")).collect()
}

/// Parse the assembly code into a [`Vec<Line<'a>>`], or a [`Vec<Rich<char>>`] on failure.
pub fn build_ast<'a>(code: &'a str) -> Result<Vec<Line<'a>>, Vec<Rich<'a, char>>> {
    grammar().parse(code).into_result()
}

/// Assemble an AST in the form of a [`Vec<Line>`] into a [`Vec<i64>`]
///
/// On failure, returns an [`AssemblyError`].
pub fn assemble_ast<'a>(code: Vec<Line<'a>>) -> Result<Vec<i64>, AssemblyError<'a>> {
    let mut labels: HashMap<&'a str, i64> = HashMap::new();
    let mut index = 0;
    for line in code.iter() {
        if let Some(label) = line.label
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
/// This is a wrapper around [`build_ast`] and [`assemble_ast`].
/// ```no_run
/// assemble_ast(build_ast(code).map_err(Error::Parse)?).map_err(Error::Assemble)
/// ```
#[inline]
pub fn assemble<'a>(code: &'a str) -> Result<Vec<i64>, AsmError<'a>> {
    assemble_ast(build_ast(code).map_err(AsmError::BuildAst)?).map_err(AsmError::Assemble)
}

mod fmt_impls;

#[cfg(test)]
mod ast_tests;
