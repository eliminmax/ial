// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use super::ast_prelude::*;
use std::ops::Range;

pub use crate::expr;
pub use crate::param;
/// A macro to make constructing [expressions](Expr) simpler.
///
/// If passed a literal, it will resolve to an [Expr::Number] with that literal value
///
/// ```
/// use intcode::asm::{ast_prelude::*, ast_util::*};
/// assert_eq!(expr!(10), Expr::Number(10));
/// ```
///
/// If passed an identifier, it will resolve to an `[Expr::Ident]` with that identifer
/// (stringified with [`stringify`]).
/// ```
///# use intcode::asm::{ast_prelude::*, ast_util::*};
/// assert_eq!(expr!(e), Expr::Ident("e"));
/// ```
///
/// Expressions within expressions can be expressed using the syntax `expr;[span]`, which is
/// messy, but works around ambiguity about where an expression ends, and allows the span to be
/// provided, and is overall still far more concise than fully writing it out:
///
/// ```
///# use intcode::asm::{ast_prelude::*, ast_util::*};
/// assert_eq!(
///     expr!( (expr!(e);[1..2]) ),
///     Expr::Parenthesized(boxed(span(Expr::Ident("e"), 1..2)))
/// );
/// assert_eq!(
///     expr!(- expr!(e);[1..2]),
///     Expr::Negate(boxed(span(Expr::Ident("e"), 1..2)))
/// );
/// assert_eq!(
///     expr!(expr!(1);[0..1] +[2..3] expr!(1);[4..5]),
///     Expr::BinOp {
///         lhs: boxed(span(Expr::Number(1), 0..1)),
///         op: span(BinOperator::Add, 2..3),
///         rhs: boxed(span(Expr::Number(1), 4..5)),
///     }
/// );
/// ```
///
#[macro_export]
macro_rules! expr {
    (+ $e:expr;[$span: expr]) => {{
        $crate::asm::Expr::UnaryAdd(
            ::std::boxed::Box::new(
                $crate::asm::ast_util::span($e, $span)
            )
        )
    }};
    (- $e:expr;[$span: expr]) => {{
        $crate::asm::Expr::Negate(Box::new($crate::asm::ast_util::span($e, $span)))
    }};
    ($i:ident) => {{ $crate::asm::Expr::Ident(stringify!($i)) }};
    ($n:literal) => {{ $crate::asm::Expr::Number($n) }};
    ( ($e:expr;[$span: expr]) ) => {{
        $crate::asm::Expr::Parenthesized(
            ::std::boxed::Box::new($crate::asm::ast_util::span($e, $span))
        )
    }};
    ($l:expr;[$span_l:expr] $op:tt[$span_op:expr] $r:expr;[$span_r:expr]) => {{
        macro_rules! op {
            [+] => {{ $crate::asm::BinOperator::Add }};
            [-] => {{ $crate::asm::BinOperator::Sub }};
            [*] => {{ $crate::asm::BinOperator::Mul }};
            [/] => {{ $crate::asm::BinOperator::Div }};
        }
        $crate::asm::Expr::BinOp {
            lhs: ::std::boxed::Box::new($crate::asm::ast_util::span($l, $span_l)),
            op: $crate::asm::ast_util::span(op![$op], $span_op),
            rhs: ::std::boxed::Box::new($crate::asm::ast_util::span($r, $span_r)),
        }
    }};
}

/// A macro to make constructing [parameters](Parameter) simpler.
///
/// Construct a parameter using the syntax `param!(<mode> expr; span)`, where `<mode>` is
/// either blank for parameter mode, `#` for immediate mode, or `@` for relative mode
///
/// ```
/// use intcode::asm::{ast_prelude::*, ast_util::*};
/// assert_eq!(
///     param!(@<expr!(0);>[0..2]),
///     Parameter(span(ParamMode::Relative, 0..1), boxed(span(Expr::Number(0), 1..2)))
/// );
/// ```
#[macro_export]
macro_rules! param {
    (@ <$e: expr;>[$span: expr]) => {{
        $crate::asm::Parameter(
            $crate::ParamMode::Relative,
            ::std::boxed::Box::new($crate::asm::ast_util::span(
                $e,
                ($span.start + 1)..($span.end),
            )),
        )
    }};
    (# <$e: expr;>[$span: expr]) => {{
        $crate::asm::Parameter(
            $crate::ParamMode::Immediate,
            ::std::boxed::Box::new($crate::asm::ast_util::span(
                $e,
                ($span.start + 1)..($span.end),
            )),
        )
    }};
    (<$e: expr;>[$span: expr]) => {{
        $crate::asm::Parameter(
            $crate::ParamMode::Positional,
            ::std::boxed::Box::new($crate::asm::ast_util::span($e, $span)),
        )
    }};
}

#[inline]
/// Unwrap a [`Spanned<T>`] into the underlying [`T`]
pub fn unspan<T>(Spanned { inner, .. }: Spanned<T>) -> T {
    inner
}

#[inline]
/// Wrap a [`T`] into a [`Spanned<T>`] with the provided range
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
