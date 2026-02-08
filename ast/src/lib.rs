// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

//! Module of types related to the Abstract Syntax Tree
use chumsky::error::Rich;
use chumsky::span::{SimpleSpan, Span, Spanned};
use ial_core::ParamMode;
use std::collections::HashMap;
use std::ops::Range;
use util::unspan;

pub mod parsers;
pub mod util;

mod display_impls;

/// Format the code into a reasonable default appearance, attempting to preserve indentation
///
/// # Errors
///
/// If a line of source code fails to parse, then returns the parser errors
pub fn format(code: &str) -> Result<String, Vec<Rich<'_, char>>> {
    use chumsky::prelude::*;
    let mut formatted = String::with_capacity(code.len());
    let leading_whitespace = || {
        text::whitespace()
            .to_slice()
            .map(|s: &str| s.replace('\t', "    "))
    };
    for l in code.lines() {
        let (indent, code) = leading_whitespace()
            .then(parsers::line())
            .parse(l)
            .into_result()?;
        let mut l = format!("{indent}{code}");
        while l.as_bytes().last().copied() == Some(b' ') {
            l.pop();
        }
        l.push('\n');
        formatted += &l;
    }
    Ok(formatted)
}

#[derive(Debug, PartialEq, Clone, Copy)]
/// The type of a [`Directive`]
#[allow(missing_docs, reason = "trivial")]
pub enum DirectiveKind {
    Instruction = 0,
    Data = 1,
    Ascii = 2,
}

/// a small module that re-exports the types needed to work with the AST of the assembly language.
pub mod prelude {
    pub use super::{
        BinOperator, Directive, Expr, Instr, Label, Line, OuterExpr, Parameter, SingleByteSpan,
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

    #[inline]
    fn context(&self) {}

    #[inline]
    fn start(&self) -> Self::Offset {
        self.0
    }

    #[inline]
    fn end(&self) -> Self::Offset {
        self.0
    }
}

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
    /// Apply this binary operator to two concrete values
    #[must_use]
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
        lhs: Box<Spanned<Expr<'a>>>,
        /// the operation to perform
        op: Spanned<BinOperator, SingleByteSpan>,
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

impl<'a> Expr<'a> {
    /// Given a mapping of labels to indexes, try to resolve into a concrete value.
    ///
    /// # Errors
    ///
    /// If a label can't be found within `labels`, it will return that label as an Err value
    pub fn resolve(&self, labels: &HashMap<&'a str, i64>) -> Result<i64, ExprResolutionError<'a>> {
        match self {
            Expr::Number(n) => Ok(*n),
            Expr::AsciiChar(c) => Ok(i64::from(*c)),
            Expr::Ident(s) => labels
                .get(s)
                .copied()
                .ok_or(ExprResolutionError::UnresolvedLabel(s)),
            Expr::BinOp { lhs, op, rhs } => {
                if **op == BinOperator::Div && rhs.resolve(labels)? == 0 {
                    Err(ExprResolutionError::DivisionByZero {
                        lhs_span: lhs.span,
                        div_index: op.span.0,
                        rhs_span: rhs.span,
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

#[derive(Debug, PartialEq, Clone)]
/// An error occurred resolving an expression to a concrete value
pub enum ExprResolutionError<'a> {
    /// The contained identifer could not be resolved into a concrete label
    UnresolvedLabel(&'a str),
    /// A divison expression's right-hand side evaluated to zero
    DivisionByZero {
        /// The left-hand side of the expression
        lhs_span: SimpleSpan,
        /// The index of the division operator in the source
        div_index: usize,
        /// The right-hand side of the expression
        rhs_span: SimpleSpan,
    },
}

impl<'a> ExprResolutionError<'a> {
    fn generalize_with_span(self, span: SimpleSpan) -> AssemblyError<'a> {
        match self {
            ExprResolutionError::UnresolvedLabel(label) => {
                AssemblyError::UnresolvedLabel { label, span }
            }
            ExprResolutionError::DivisionByZero {
                lhs_span,
                div_index,
                rhs_span,
            } => AssemblyError::DivisionByZero {
                lhs_span,
                div_index,
                rhs_span,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
/// A simple tuple struct containing the parameter mode, labels, and expression for the parameter
///
/// The labels and expression are stored as an [`OuterExpr`]
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
    /// Thin convinience wrapper around [`Directive::encode_into`]
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
    /// use ast::parsers::{Parser, directive};
    /// use ast::util::unspan;
    /// use std::collections::HashMap;
    /// const ASM_SRC: &str = "DATA 1, 2, zero + 3, 4 * 4 / 4, 5";
    /// let directive = directive().parse(ASM_SRC).unwrap().unwrap().inner;
    /// let mut assembled = Vec::new();
    /// directive.encode_into(&mut assembled, &HashMap::from([("zero", 0)])).unwrap();
    /// assert_eq!(assembled, vec![1, 2, 3, 4, 5]);
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
    /// use ast::parsers::{Parser, directive};
    /// let directive = directive().parse(ASM_SRC).unwrap().unwrap().inner;
    /// assert_eq!(directive.kind(), ast::DirectiveKind::Ascii);
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
                    let Spanned { inner: expr, span } = expr;
                    v.push(
                        expr.resolve(labels)
                            .map_err(|err| err.generalize_with_span(span))?,
                    );
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
        macro_rules! process_param {
            ($param: ident * $multiplier: literal, &mut $instr: ident) => {{
                let Parameter(mode, outer_expr) = $param;
                let Spanned { inner: expr, span } = outer_expr.expr;
                $instr += mode as i64 * $multiplier;
                expr.resolve(labels)
                    .map_err(|err| err.generalize_with_span(span))?
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

/// An identifier, [spanned](Spanned) by its position in the source code
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Label<'a>(pub Spanned<&'a str>);
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

/// An error that occured while trying to assemble the AST into Intcode
#[derive(Debug)]
#[non_exhaustive]
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
    /// A divison expression's right-hand side evaluated to zero
    DivisionByZero {
        /// The left-hand side of the expression
        lhs_span: SimpleSpan,
        /// The index of the division operator in the source
        div_index: usize,
        /// The right-hand side of the expression
        rhs_span: SimpleSpan,
    },
}

impl std::error::Error for AssemblyError<'_> {}
