// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Crate of functionality related to the Abstract Syntax Tree

#[doc(hidden)]
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

use chumsky::Parser;
use chumsky::span::{SimpleSpan, Span, Spanned};
use ial_core::{AssemblyError, DirectiveKind, OpCode, ParamMode};
use std::collections::HashMap;
use std::ops::{Deref, Range};
use util::unspan;

pub mod parsers;
pub mod util;

mod display_impls;

/// a small module that re-exports the types needed to work with the AST of the assembly language.
pub mod prelude {
    pub use super::{
        BinOperator, Directive, Expr, Instr, Label, Line, OuterExpr, Parameter, SingleByteSpan,
        SpannedExpr,
    };
    pub use chumsky::span::{SimpleSpan, Spanned};
    pub use ial_core::ParamMode;
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

#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
/// A [`usize`] newtype that implements [`Span`], for when something is always 1 byte
pub struct SingleByteSpan(pub usize);
impl Span for SingleByteSpan {
    type Context = ();

    type Offset = usize;

    fn new((): (), range: Range<Self::Offset>) -> Self {
        assert_eq!(
            range.start,
            range.end - 1,
            "SingleByteSpan range length must be 1"
        );
        Self(range.start)
    }

    #[inline(always)]
    // exclude empty function that's optimized away from code coverage
    #[cfg(not(tarpaulin_include))]
    fn context(&self) {}

    #[inline]
    fn start(&self) -> Self::Offset {
        self.0
    }

    #[inline]
    fn end(&self) -> Self::Offset {
        self.0 + 1
    }
}

#[derive(Debug, Clone, PartialEq)]
/// A binary operator within an [`Expr::BinOp`]
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
    /// Apply this binary operator to two concrete values
    #[must_use]
    #[inline]
    pub const fn apply(&self, a: i64, b: i64) -> i64 {
        match self {
            BinOperator::Add => a + b,
            BinOperator::Sub => a - b,
            BinOperator::Mul => a * b,
            BinOperator::Div => a / b,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
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
        lhs: Box<SpannedExpr<'a>>,
        /// the operation to perform
        op: Spanned<BinOperator, SingleByteSpan>,
        /// the right-hand-side expression
        rhs: Box<SpannedExpr<'a>>,
    },
    /// the negation of the inner expression
    Negate(Box<SpannedExpr<'a>>),
    #[doc(hidden)]
    /// A unary plus sign, which evaluates to the value of its right-hand side. It's defined for
    /// compatibility with the [proposed assembly syntax] from the Esolangs Community Wiki, but
    /// has no use that I can see.
    ///
    /// [proposed assembly syntax]: <https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax>
    UnaryAdd(Box<SpannedExpr<'a>>),
    /// an inner expression in parentheses
    Parenthesized(Box<SpannedExpr<'a>>),
}

impl Expr<'_> {
    /// Check that expressions are semantically identical, ignoring the spans of their elements
    ///
    /// # Example
    ///
    /// ```
    ///# use ial_ast::Expr;
    /// // a and b have the same semantic tokens, but at different positions
    /// let a = Expr::parse("1 + 1").unwrap();
    /// let b = Expr::parse("1+1").unwrap();
    ///
    /// assert_ne!(a, b);
    /// assert!(a.eq_ignore_spans(&b));
    ///
    /// // while `c` evaluates to the same value as `a`, it has additional semantic tokens
    /// let c = Expr::parse("(1 + 1)").unwrap();
    /// assert!(!a.eq_ignore_spans(&c));
    /// ```
    #[must_use]
    pub fn eq_ignore_spans(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::Number(a), Expr::Number(b)) => a == b,
            (Expr::AsciiChar(a), Expr::AsciiChar(b)) => a == b,
            (Expr::Ident(a), Expr::Ident(b)) => a == b,
            (
                Expr::BinOp {
                    lhs: lhs_a,
                    op: op_a,
                    rhs: rhs_a,
                },
                Expr::BinOp {
                    lhs: lhs_b,
                    op: op_b,
                    rhs: rhs_b,
                },
            ) => {
                op_a.inner == op_b.inner
                    && lhs_a.eq_ignore_spans(lhs_b)
                    && rhs_a.eq_ignore_spans(rhs_b)
            }
            (Expr::Negate(a), Expr::Negate(b))
            | (Expr::UnaryAdd(a), Expr::UnaryAdd(b))
            | (Expr::Parenthesized(a), Expr::Parenthesized(b)) => a.eq_ignore_spans(b),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SpannedExpr<'a> {
    pub expr: Expr<'a>,
    pub span: SimpleSpan,
}

#[cfg(not(tarpaulin_include))]
impl<'a> From<Spanned<Expr<'a>>> for SpannedExpr<'a> {
    fn from(Spanned { inner: expr, span }: Spanned<Expr<'a>>) -> Self {
        Self { expr, span }
    }
}

impl<'a> Deref for SpannedExpr<'a> {
    type Target = Expr<'a>;

    fn deref(&self) -> &Self::Target {
        &self.expr
    }
}

impl<'a> Expr<'a> {
    /// Parse a [`SpannedExpr`] from a [string slice][str]
    ///
    /// # Errors
    ///
    /// Any parsing errors that occur are returned
    pub fn parse(s: &'a str) -> Result<SpannedExpr<'a>, Vec<chumsky::error::Rich<'a, char>>> {
        parsers::expr().parse(s.trim()).into_result()
    }
}

impl<'a> SpannedExpr<'a> {
    fn resolve(&self, labels: &HashMap<&'a str, i64>) -> Result<i64, AssemblyError<'a>> {
        match &self.expr {
            Expr::Number(n) => Ok(*n),
            Expr::AsciiChar(c) => Ok(i64::from(*c)),
            Expr::Ident(s) => labels
                .get(s)
                .copied()
                .ok_or(AssemblyError::UnresolvedLabel {
                    label: s,
                    span: self.span.into_range(),
                }),
            Expr::BinOp { lhs, op, rhs } => {
                if **op == BinOperator::Div && rhs.resolve(labels)? == 0 {
                    Err(AssemblyError::DivisionByZero {
                        lhs_span: lhs.span.into_range(),
                        div_index: op.span.0,
                        rhs_span: rhs.span.into_range(),
                    })
                } else {
                    Ok(op.apply(lhs.resolve(labels)?, rhs.resolve(labels)?))
                }
            }
            Expr::Negate(expr) => Ok(-expr.resolve(labels)?),
            Expr::UnaryAdd(expr) | Expr::Parenthesized(expr) => Ok(expr.resolve(labels)?),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
/// A simple tuple struct containing the parameter mode, labels, and expression for the parameter
///
/// The labels and expression are stored as an [`OuterExpr`]
pub struct Parameter<'a>(pub ParamMode, pub Box<OuterExpr<'a>>);

/// An outermost expression with an optional label
#[derive(Debug, Clone, PartialEq)]
pub struct OuterExpr<'a> {
    /// the (optional) label of the expression
    pub labels: Vec<Label<'a>>,
    /// the expression itself
    pub expr: SpannedExpr<'a>,
}

#[derive(Debug, PartialEq, Clone)]
/// A single line of assembly, containing any number of labels, an optional directive, and an
/// optional comment
pub struct Line<'a> {
    /// the labels for the line
    pub labels: Vec<Label<'a>>,
    /// the directive for the line, if applicable
    pub directive: Option<Spanned<Directive<'a>>>,
    /// the Line's comment
    pub comment: Option<Spanned<&'a str>>,
}

impl<'a> Line<'a> {
    fn from_tuple(
        (labels, directive, comment): (
            Vec<Label<'a>>,
            Option<Spanned<Directive<'a>>>,
            Option<Spanned<&'a str>>,
        ),
    ) -> Self {
        Self {
            labels,
            directive,
            comment,
        }
    }

    /// Thin convenience wrapper around [`Directive::encode_into`]
    ///
    /// Does nothing if [`self.directive`] is [`None`].
    ///
    /// # Errors
    ///
    /// If the internal call to [`self.directive.inner.encode_into`] fails, passes the resulting
    /// error along.
    ///
    /// [`self.directive`]: Line::directive
    /// [`self.directive.inner.encode_into`]: Directive::encode_into
    pub fn encode_into(
        self,
        v: &mut Vec<i64>,
        labels: &HashMap<&'a str, i64>,
    ) -> Result<(), AssemblyError<'a>> {
        match self.directive {
            Some(directive) => directive.inner.encode_into(v, labels),
            None => Ok(()),
        }
    }
}

impl Line<'_> {
    /// Check if line is empty
    ///
    /// Returns `false` unless [`labels`] is empty, and both [`directive`] and [`comment`] are
    /// [`None`].
    ///
    /// [`labels`]: Line::labels
    /// [`directive`]: Line::directive
    /// [`comment`]: Line::comment
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.labels.is_empty() && self.directive.is_none() && self.comment.is_none()
    }
}

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
    /// use ial_ast::parsers::{Parser, directive};
    /// use ial_ast::util::unspan;
    /// use std::collections::HashMap;
    /// const ASM_SRC: &str = "DATA 1, 2, zero + 3, 4 * 4 / 4, 5";
    /// let directive = directive().parse(ASM_SRC).unwrap().unwrap().inner;
    /// let mut assembled = Vec::new();
    /// directive.encode_into(&mut assembled, &HashMap::from([("zero", 0)])).unwrap();
    /// assert_eq!(assembled, vec![1, 2, 3, 4, 5]);
    /// ```
    Data(Vec<SpannedExpr<'a>>),
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
    /// use ial_ast::parsers::{Parser, directive};
    /// let directive = directive().parse(ASM_SRC).unwrap().unwrap().inner;
    /// assert_eq!(directive.kind(), ial_core::DirectiveKind::Ascii);
    /// let mut assembled = Vec::new();
    /// directive.encode_into(&mut assembled, &Default::default()).unwrap();
    /// let expected: Vec<i64> = b"Hello, world!\n".into_iter().map(|&i| i64::from(i)).collect();
    /// assert_eq!(assembled, expected);
    /// ```
    Ascii(Spanned<Vec<u8>>),
    /// An [instruction](Instr)
    Instruction(Box<Instr<'a>>),
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

    /// Return the [`DirectiveKind`] of this directive
    #[must_use]
    pub fn kind(&self) -> DirectiveKind {
        match self {
            Directive::Data(_) => DirectiveKind::Data,
            Directive::Ascii(_) => DirectiveKind::Ascii,
            Directive::Instruction(_) => DirectiveKind::Instruction,
        }
    }
}

impl<'a> Directive<'a> {
    /// Consume the directive, appending the bytes to `v`.
    ///
    /// # Errors
    /// If the directive is either an [`Instruction`] or a [`Data`] directive, and an
    /// expression fails to [resolve], returns an [`AssemblyError`]
    ///
    /// [`Instruction`]: Directive::Instruction
    /// [`Data`]: Directive::Data
    /// [resolve]: Expr::resolve
    ///
    pub fn encode_into(
        self,
        v: &mut Vec<i64>,
        labels: &HashMap<&'a str, i64>,
    ) -> Result<(), AssemblyError<'a>> {
        match self {
            Directive::Data(exprs) => {
                for expr in exprs {
                    v.push(expr.resolve(labels)?);
                }
            }
            Directive::Ascii(text) => v.extend(unspan(text).into_iter().map(i64::from)),
            Directive::Instruction(instr) => {
                v.extend(instr.resolve(labels)?);
            }
        }
        Ok(())
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
    #[must_use]
    /// Return the opcode of the instruction as an [`OpCode`]
    pub const fn op_code(&self) -> OpCode {
        match self {
            Instr::Add(_, _, _) => OpCode::Add,
            Instr::Mul(_, _, _) => OpCode::Mul,
            Instr::In(_) => OpCode::In,
            Instr::Out(_) => OpCode::Out,
            Instr::Jnz(_, _) => OpCode::Jnz,
            Instr::Jz(_, _) => OpCode::Jz,
            Instr::Lt(_, _, _) => OpCode::Lt,
            Instr::Eq(_, _, _) => OpCode::Eq,
            Instr::Rbo(_) => OpCode::Rbo,
            Instr::Halt => OpCode::Halt,
        }
    }

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
        let mut instr_int = self.op_code() as i64;
        match self {
            Instr::Add(a, b, c) | Instr::Mul(a, b, c) | Instr::Lt(a, b, c) | Instr::Eq(a, b, c) => {
                instr_int += (a.0 as i64 * 100) + (b.0 as i64 * 1000) + (c.0 as i64 * 10000);
                let a = a.1.expr.resolve(labels)?;
                let b = b.1.expr.resolve(labels)?;
                let c = c.1.expr.resolve(labels)?;
                Ok(StackIter::Four(instr_int, a, b, c))
            }
            Instr::Jnz(a, b) | Instr::Jz(a, b) => {
                instr_int += (a.0 as i64 * 100) + (b.0 as i64 * 1000);
                let a = a.1.expr.resolve(labels)?;
                let b = b.1.expr.resolve(labels)?;
                Ok(StackIter::Three(instr_int, a, b))
            }
            Instr::In(a) | Instr::Out(a) | Instr::Rbo(a) => {
                instr_int += a.0 as i64 * 100;
                let a = a.1.expr.resolve(labels)?;
                Ok(StackIter::Two(instr_int, a))
            }
            Instr::Halt => Ok(StackIter::One(instr_int)),
        }
    }
}

/// An identifier, [spanned](Spanned) by its position in the source code
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Label<'a>(pub Spanned<&'a str>);

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use super::*;
    macro_rules! hash_map {
        {$($k: expr => $v: expr),*} => {
            HashMap::from([$(($k, $v)),*])
        }
    }

    #[test]
    fn single_byte_span_impl() {
        let sbs = SingleByteSpan::new((), 0..1);
        assert_eq!(sbs.start(), 0);
        assert_eq!(sbs.end(), 1);
    }

    #[test]
    fn expr_resolution() {
        macro_rules! assert_resolves_to {
            ($expr: literal, $val: expr) => {{
                assert_eq!(
                    Expr::parse($expr).unwrap().resolve(&HashMap::new()),
                    Ok($val)
                );
            }};
        }
        assert_resolves_to!("1", 1);
        assert_resolves_to!("+1", 1);
        assert_resolves_to!("-1", -1);
        assert_resolves_to!("1 + 1", 2);
        assert_resolves_to!("1 - 1", 0);
        assert_resolves_to!("1 * 1", 1);
        assert_resolves_to!("1 / 1", 1);
        // some more complex order-of-operations stuff
        assert_resolves_to!("-1 - 1", -2);
        assert_resolves_to!("-1 * +1", -1);
        assert_resolves_to!("1 + 1 * 1 + 1", 3);
        // division truncates towards zero
        assert_resolves_to!("1 / 2", 0);
        assert_resolves_to!("3 / 2", 1);
        assert_resolves_to!("-3 / 2", -1);

        // messy combination of unary adds, double-negatives, and parentheses that should be
        // equivalent to `1 * 1`
        assert_resolves_to!("1 *+(+----(1))", 1);

        let expr = Expr::parse("a + b").unwrap();
        assert_eq!(expr.resolve(&hash_map! { "a" => 1, "b" => 0}), Ok(1));
        assert_eq!(expr.resolve(&hash_map! { "a" => 0, "b" => 0}), Ok(0));
        assert_eq!(
            expr.resolve(&hash_map! { "a" => 0}),
            Err(AssemblyError::UnresolvedLabel {
                label: "b",
                span: 4..5
            })
        );
        let div_by_0 = Expr::parse("1 / (1 - 1)")
            .unwrap()
            .resolve(&hash_map! {})
            .unwrap_err();
        assert_eq!(
            div_by_0,
            AssemblyError::DivisionByZero {
                lhs_span: 0..1,
                div_index: 2,
                rhs_span: 4..11
            }
        );
    }

    #[test]
    fn full_eq_ignore_spans() {
        macro_rules! assert_eq_ignore_spans {
            ($a: literal, $b: literal) => {{
                let a = Expr::parse($a).unwrap();
                let b = Expr::parse($b).unwrap();
                assert!(a.eq_ignore_spans(&b));
            }};
        }
        assert_eq_ignore_spans!("+1", "+  1");
        assert_eq_ignore_spans!("1", "1");
        assert_eq_ignore_spans!("'1'", "'1'");
        assert_eq_ignore_spans!("-1", "-\t\t 1");
        assert_eq_ignore_spans!("1 + 1", "1+1");
        // the following should hit all branches
        assert_eq_ignore_spans!("1+(-'1') + _1", "1 + (   \t  -'1')+_1");
        assert!(
            !Expr::parse("-1")
                .unwrap()
                .eq_ignore_spans(&Expr::parse("+1").unwrap())
        );
    }

    #[test]
    fn resolve_all_instructions() {
        use parsers::{Parser, instr};
        let tests = [
            ("ADD #90, #9, 4", vec![1101, 90, 9, 4]),
            ("MUL #11, #9, 4", vec![1102, 11, 9, 4]),
            ("IN 2", vec![3, 2]),
            (r"OUT #'\n'", vec![104, 10]),
            ("JNZ #1, #2", vec![1105, 1, 2]),
            ("JZ #0, #2", vec![1106, 0, 2]),
            ("LT #0, #1, 4", vec![1107, 0, 1, 4]),
            ("EQ #0, #0, 4", vec![1108, 0, 0, 4]),
            ("RBO @0", vec![209, 0]),
            ("HALT", vec![99]),
        ];

        for (instr_text, expected) in tests {
            let actual = instr()
                .parse(instr_text)
                .unwrap()
                .resolve(&hash_map! {})
                .unwrap()
                .collect_vec();
            assert_eq!(actual, expected, "{instr_text}");
        }
    }
}
