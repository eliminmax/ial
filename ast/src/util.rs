// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD
//! Small utility functions and macros for making it less painful to work with the AST

use super::prelude::*;
use std::ops::Range;

pub use crate::expr;
pub use crate::param;
/// A macro to make constructing [expressions](Expr) simpler.
///
/// If passed a literal, it will resolve to an [`Expr::Number`] with that literal value
///
/// ```
/// use ast::{prelude::*, util::*};
/// assert_eq!(expr!(10), Expr::Number(10));
/// ```
///
/// If passed an identifier, it will resolve to an [`Expr::Ident`] with that identifer
/// (stringified with [`stringify`]).
/// ```
///# use ast::{prelude::*, util::*};
/// assert_eq!(expr!(e), Expr::Ident("e"));
/// ```
///
/// If passed a literal preceded by a colon (`:`), it will resolve to an [`Expr::AsciiChar`] with
/// the literal cast to a [u8]. This is because there's no way to select based on the type of a
/// literal within a declarative macro without incurring runtime overhead.
///
/// ```
///# use ast::{prelude::*, util::*};
/// assert_eq!(expr!(:'a'), Expr::AsciiChar(b'a'));
/// ```
///
/// Expressions within expressions can be expressed using the syntax `expr;[span]`, which is
/// messy, but works around ambiguity about where an expression ends, and allows the span to be
/// provided, and is overall still far more concise than fully writing it out:
///
/// ```
///# use ast::{prelude::*, util::*};
/// assert_eq!(
///     expr!( (expr!(e);[1..2]) ),
///     Expr::Parenthesized(boxed(span(Expr::Ident("e"), 1..2)))
/// );
/// assert_eq!(
///     expr!(- expr!(e);[1..2]),
///     Expr::Negate(boxed(span(Expr::Ident("e"), 1..2)))
/// );
/// assert_eq!(
///     expr!(expr!(1);[0..1] +[2] expr!(1);[4..5]),
///     Expr::BinOp {
///         lhs: boxed(span(Expr::Number(1), 0..1)),
///         op: Spanned { inner: BinOperator::Add, span: SingleByteSpan(2) },
///         rhs: boxed(span(Expr::Number(1), 4..5)),
///     }
/// );
/// ```
///
#[macro_export]
macro_rules! expr {
    (+ $e:expr;[$span: expr]) => {{
        $crate::Expr::UnaryAdd(
            ::std::boxed::Box::new(
                $crate::util::span($e, $span)
            )
        )
    }};
    (- $e:expr;[$span: expr]) => {{
        $crate::Expr::Negate(Box::new($crate::util::span($e, $span)))
    }};
    (:$a: literal) => {{
        $crate::Expr::AsciiChar($a as u8)
    }};
    ($i:ident) => {{ $crate::Expr::Ident(stringify!($i)) }};
    ($n:literal) => {{ $crate::Expr::Number($n) }};
    ( ($e:expr;[$span: expr]) ) => {{
        $crate::Expr::Parenthesized(
            ::std::boxed::Box::new($crate::util::span($e, $span))
        )
    }};
    ($l:expr;[$span_l:expr] $op:tt[$op_index:expr] $r:expr;[$span_r:expr]) => {{
        macro_rules! op {
            [+] => {{ $crate::BinOperator::Add }};
            [-] => {{ $crate::BinOperator::Sub }};
            [*] => {{ $crate::BinOperator::Mul }};
            [/] => {{ $crate::BinOperator::Div }};
        }
        $crate::Expr::BinOp {
            lhs: ::std::boxed::Box::new($crate::util::span($l, $span_l)),
            op: ::chumsky::span::Spanned {
                inner: op![$op],
                span: $crate::SingleByteSpan($op_index)
            },
            rhs: ::std::boxed::Box::new($crate::util::span($r, $span_r)),
        }
    }};
}

/// A macro to make constructing [parameters](Parameter) simpler.
///
/// Construct a parameter using the syntax `param!(<mode> expr; span)`, where `<mode>` is
/// either blank for parameter mode, `#` for immediate mode, or `@` for relative mode
///
/// ```
/// use ast::{prelude::*, util::*};
/// assert_eq!(
///     param!(@<expr!(0);>[0..2]),
///     Parameter(
///         ParamMode::Relative,
///         boxed(OuterExpr {
///             expr: span(Expr::Number(0), 1..2),
///             labels: Vec::new(),
///         })
///     )
/// );
/// ```
#[macro_export]
macro_rules! param {
    (@ <$e: expr;>[$span: expr]) => {{
        $crate::Parameter(
            $crate::ParamMode::Relative,
            ::std::boxed::Box::new($crate::OuterExpr {
                expr: $crate::util::span($e, ($span.start + 1)..($span.end)),
                labels: ::std::vec::Vec::new(),
            }),
        )
    }};
    (# <$e: expr;>[$span: expr]) => {{
        $crate::Parameter(
            $crate::ParamMode::Immediate,
            ::std::boxed::Box::new($crate::OuterExpr {
                expr: $crate::util::span($e, ($span.start + 1)..($span.end)),
                labels: ::std::vec::Vec::new(),
            }),
        )
    }};
    (<$e: expr;>[$span: expr]) => {{
        $crate::Parameter(
            $crate::ParamMode::Positional,
            ::std::boxed::Box::new($crate::OuterExpr {
                expr: $crate::util::span($e, ($span.start)..($span.end)),
                labels: ::std::vec::Vec::new(),
            }),
        )
    }};
}

#[inline]
/// Unwrap a [`Spanned<T>`] into the underlying `T`
pub fn unspan<T>(Spanned { inner, .. }: Spanned<T>) -> T {
    inner
}

#[inline]
/// Wrap a `T` into a [`Spanned<T>`] with the provided range
pub const fn span<T>(inner: T, range: Range<usize>) -> Spanned<T> {
    Spanned {
        inner,
        span: SimpleSpan {
            start: range.start,
            end: range.end,
            context: (),
        },
    }
}

#[inline]
/// Move `inner` into a [`Box`]
pub fn boxed<T>(inner: T) -> Box<T> {
    Box::new(inner)
}
