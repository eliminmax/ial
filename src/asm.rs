// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use chumsky::prelude::*;

use super::ParamMode;
use std::sync::Arc;
#[derive(Debug, Clone)]
pub enum BinOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone)]
pub enum Expr<'a> {
    Number(i64),
    Ident(&'a str),
    BinOp {
        op: BinOperator,
        lhs: Arc<Expr<'a>>,
        rhs: Arc<Expr<'a>>,
    },
    Negate(Arc<Expr<'a>>),
    UnaryAdd(Arc<Expr<'a>>),
    Inner(Arc<Expr<'a>>),
}

#[derive(Debug, Clone)]
pub struct Parameter<'a>(pub ParamMode, pub Expr<'a>);

#[derive(Debug, Clone)]
#[repr(u8)]
pub enum Instr<'a> {
    Add(Parameter<'a>, Parameter<'a>) = 1,
    Mul(Parameter<'a>, Parameter<'a>) = 2,
    In(Parameter<'a>) = 3,
    Out(Parameter<'a>) = 4,
    Jnz(Parameter<'a>, Parameter<'a>) = 5,
    Jz(Parameter<'a>, Parameter<'a>) = 6,
    Slt(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 7,
    Seq(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 8,
    Incb(Parameter<'a>) = 9,
    Halt = 99,
}

pub enum LineInner<'a> {
    DataDirective(Vec<Expr<'a>>),
    Instruction(Instr<'a>),
}

pub struct Line<'a> {
    pub label: Option<&'a str>,
    pub inner: Option<LineInner<'a>>,
}

fn param<'a>() -> impl Parser<'a, &'a str, Parameter<'a>> {
    choice((
        just('@')
            .ignore_then(expr())
            .map(|e| Parameter(ParamMode::Relative, e)),
        just('#')
            .ignore_then(expr())
            .map(|e| Parameter(ParamMode::Immediate, e)),
        expr().map(|e| Parameter(ParamMode::Positional, e)),
    ))
}

fn instr<'a>() -> impl Parser<'a, &'a str, Instr<'a>> {
    macro_rules! params {
        ($n: literal) => {{
            param()
                .separated_by(just(',').padded_by(text::inline_whitespace()))
                .exactly($n)
                .collect::<Vec<_>>()
                .map(|v| <[Parameter; $n]>::try_from(v).expect("sized"))
        }};
    }
    macro_rules! op {
        ($name: literal, $variant: ident ::<1>) => {
            just($name)
                .padded_by(text::inline_whitespace())
                .ignore_then(param().padded_by(text::inline_whitespace()))
                .map(Instr::$variant)
        };
        ($name: literal, $variant: ident ::<2>) => {
            just($name)
                .padded_by(text::inline_whitespace())
                .ignore_then((params!(2)).map(|[a, b]| Instr::$variant(a, b)))
        };
        ($name: literal, $variant: ident ::<3>) => {
            just($name)
                .padded_by(text::inline_whitespace())
                .ignore_then((params!(3)).map(|[a, b, c]| Instr::$variant(a, b, c)))
        };
    }

    choice((
        op!("ADD", Add::<2>),
        op!("MUL", Mul::<2>),
        op!("IN", In::<1>),
        op!("OUT", Out::<1>),
        op!("JNZ", Jnz::<2>),
        op!("JZ", Jz::<2>),
        op!("SLT", Slt::<3>),
        op!("LT", Slt::<3>),
        op!("SEQ", Seq::<3>),
        op!("EQ", Seq::<3>),
        op!("INCB", Incb::<1>),
        just("HALT")
            .padded_by(text::inline_whitespace())
            .to(Instr::Halt),
    ))
}

fn expr<'a>() -> impl Parser<'a, &'a str, Expr<'a>> + Clone {
    recursive(|e| {
        choice((
            e.delimited_by(just('('), just(')'))
                .map(Arc::new)
                .map(Expr::Inner),
            expr()
                .then(one_of("*/"))
                .then(expr())
                .map(|((a, b), c)| Expr::BinOp {
                    op: match b {
                        '*' => BinOperator::Mul,
                        '/' => BinOperator::Div,
                        _ => unreachable!(),
                    },
                    lhs: Arc::new(a),
                    rhs: Arc::new(c),
                }),
            expr()
                .then(one_of("+-"))
                .then(expr())
                .map(|((a, b), c)| Expr::BinOp {
                    op: match b {
                        '+' => BinOperator::Add,
                        '-' => BinOperator::Sub,
                        _ => unreachable!(),
                    },
                    lhs: Arc::new(a),
                    rhs: Arc::new(c),
                }),
            just("-")
                .then(expr())
                .map(|(_, e)| Expr::Negate(Arc::new(e))),
            just("+")
                .then(expr())
                .map(|(_, e)| Expr::UnaryAdd(Arc::new(e))),
            text::ident().map(|s: &str| Expr::Ident(s)),
            text::int(10).try_map(|s: &str, _| {
                s.parse::<i64>()
                    .map(Expr::Number)
                    .map_err(|_| EmptyErr::default())
            }),
            todo(),
        ))
    })
}

fn line_inner<'a>() -> impl Parser<'a, &'a str, Option<LineInner<'a>>> {
    ((just("DATA").padded_by(text::inline_whitespace()))
        .ignore_then(expr().separated_by(just(",")).collect())
        .map(LineInner::DataDirective))
    .or(instr().map(LineInner::Instruction))
    .or_not()
}

fn parse_line<'a>() -> impl Parser<'a, &'a str, Line<'a>> {
    text::ascii::ident()
        .then_ignore(just(":"))
        .or_not()
        .then(line_inner())
        .map(|(label, inner)| Line { label, inner })
}

fn grammar<'a>() -> impl Parser<'a, &'a str, Vec<Line<'a>>> {
    parse_line().separated_by(just("\n")).collect()
}

#[derive(Debug)]
pub struct AstParseError(#[allow(unused, reason = "for error info")] Vec<chumsky::error::EmptyErr>);

/// Parse the assembly code into a [Vec<Line<'a>>]
pub fn build_ast<'a>(s: &'a str) -> Result<Vec<Line<'a>>, AstParseError> {
    grammar().parse(s).into_result().map_err(AstParseError)
}

mod fmt_impls;
