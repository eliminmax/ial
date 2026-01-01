// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only
use chumsky::prelude::*;

use super::ParamMode;
use std::sync::Arc;
#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum BinOperator {
    Add,
    Sub,
    Mul,
    Div,
}

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum Expr<'a> {
    Number(i64),
    Ident(&'a str),
    BinOp {
        lhs: Arc<Expr<'a>>,
        op: BinOperator,
        rhs: Arc<Expr<'a>>,
    },
    Negate(Arc<Expr<'a>>),
    UnaryAdd(Arc<Expr<'a>>),
    Inner(Arc<Expr<'a>>),
}

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug, Clone)]
pub struct Parameter<'a>(pub ParamMode, pub Expr<'a>);

#[cfg_attr(test, derive(PartialEq))]
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

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug)]
pub enum LineInner<'a> {
    DataDirective(Vec<Expr<'a>>),
    Instruction(Instr<'a>),
}

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug)]
pub struct Line<'a> {
    pub label: Option<&'a str>,
    pub inner: Option<LineInner<'a>>,
}

macro_rules! padded {
    ($inner: expr) => {{
        $inner.padded_by(text::inline_whitespace())
    }};
}

macro_rules! with_sep {
    ($inner: expr) => {{
        padded!($inner.then_ignore(text::inline_whitespace()))
    }};
}

fn param<'a>() -> impl Parser<'a, &'a str, Parameter<'a>> {
    padded!(choice((
        just('@').ignore_then(expr().map(|e| Parameter(ParamMode::Relative, e))),
        just('#').ignore_then(expr().map(|e| Parameter(ParamMode::Immediate, e))),
        expr().map(|e| Parameter(ParamMode::Positional, e)),
    )))
}

fn instr<'a>() -> impl Parser<'a, &'a str, Instr<'a>> {
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
        ($name: literal, $variant: ident ::<1>) => {
            with_sep!(just($name)).ignore_then(param().map(Instr::$variant))
        };
        ($name: literal, $variant: ident ::<2>) => {
            with_sep!(just($name)).ignore_then((params!(2)).map(|[a, b]| Instr::$variant(a, b)))
        };
        ($name: literal, $variant: ident ::<3>) => {
            with_sep!(just($name))
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
        padded!(just("HALT")).to(Instr::Halt),
    ))
}

fn expr<'a>() -> impl Parser<'a, &'a str, Expr<'a>> + Clone {
    recursive(|expr| {
        let int = text::int(10).try_map(|s: &str, _| {
            s.parse::<i64>()
                .map(Expr::Number)
                .map_err(|_| EmptyErr::default())
        });
        let ident = text::ident().map(|s: &str| Expr::Ident(s));
        let bracketed = expr
            .delimited_by(just('('), just(')'))
            .map(|e| Expr::Inner(Arc::new(e)));
        let atom = int.or(ident).or(bracketed);
        let unary = padded!(one_of("-+"))
            .repeated()
            .foldr(atom, |op, rhs| match op {
                '+' => Expr::UnaryAdd(Arc::new(rhs)),
                '-' => Expr::Negate(Arc::new(rhs)),
                _ => unreachable!(),
            });

        let folder = |lhs: Expr<'a>, (op, rhs): (BinOperator, Expr<'a>)| Expr::BinOp {
            lhs: Arc::new(lhs),
            op,
            rhs: Arc::new(rhs),
        };

        let prod = unary.clone().foldl(
            choice((
                padded!(just('*')).to(BinOperator::Mul),
                padded!(just('/')).to(BinOperator::Div),
            ))
            .then(unary)
            .repeated(),
            folder,
        );

        prod.clone().foldl(
            choice((
                padded!(just('+')).to(BinOperator::Add),
                padded!(just('-')).to(BinOperator::Sub),
            ))
            .then(prod)
            .repeated(),
            folder,
        )
    })
}

fn line_inner<'a>() -> impl Parser<'a, &'a str, Option<LineInner<'a>>> {
    (with_sep!(just("DATA"))
        .ignore_then(expr().separated_by(padded!(just(","))).collect())
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

/// A newtype that wraps around the chumsky error vector from the AST, to allow for changing the
/// underlying error type or parser in the future
#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug)]
pub struct AstParseError(#[allow(unused, reason = "for error info")] Vec<EmptyErr>);

/// Parse the assembly code into a [Vec<Line<'a>>]
pub fn build_ast<'a>(s: &'a str) -> Result<Vec<Line<'a>>, AstParseError> {
    grammar().parse(s).into_result().map_err(AstParseError)
}

mod fmt_impls;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parse_blank_line() {
        assert_eq!(
            parse_line().parse("").unwrap(),
            Line {
                label: None,
                inner: None
            }
        )
    }
    #[test]
    fn parse_data() {
        assert_eq!(
            line_inner().parse("DATA 1, 1, 1").unwrap(),
            Some(LineInner::DataDirective(vec![
                Expr::Number(1),
                Expr::Number(1),
                Expr::Number(1)
            ]))
        );
    }

    #[test]
    fn parse_instrs() {
        let parser = instr();
        macro_rules! p {
            (#$e: literal) => {
                Parameter(ParamMode::Immediate, Expr::Number($e))
            };
            (@$e: literal) => {
                Parameter(ParamMode::Relative, Expr::Number($e))
            };
            ($e: literal) => {
                Parameter(ParamMode::Positional, Expr::Number($e))
            };
            (#$e: ident) => {
                Parameter(ParamMode::Immediate, Expr::Ident(stringify!($e)))
            };
            (@$e: ident) => {
                Parameter(ParamMode::Relative, Expr::Ident(stringify!($e)))
            };
            ($e: ident) => {
                Parameter(ParamMode::Positional, Expr::Ident(stringify!($e)))
            };
        }
        macro_rules! i {
            [$i: ident] => { Instr::$i };
            [$i: ident ($($params: expr),+)] => { Instr::$i ($($params),+ ) };
        }
        macro_rules! parse {
            ($text: literal) => {
                parser.parse($text).unwrap()
            };
        }
        assert_eq!(parse!("ADD #1, @1"), i![Add(p!(#1), p!(@1))]);
        assert_eq!(parse!("MUL 3, @20"), i![Mul(p!(3), p!(@20))]);
        assert_eq!(parse!("IN #e"), i![In(p!(#e))]);
        assert_eq!(parse!("OUT #5"), i![Out(p!(#5))]);
        assert_eq!(parse!("JNZ @a, #b"), i![Jnz(p!(@a), p!(#b))]);
        assert_eq!(parse!("JZ @a, #b"), i![Jz(p!(@a), p!(#b))]);
        assert_eq!(parse!("SLT 1,@1, #5"), i![Slt(p!(1), p!(@1), p!(#5))]);
        assert_eq!(parse!("LT 1,@1, #5"), i![Slt(p!(1), p!(@1), p!(#5))]);
        assert_eq!(parse!("SEQ @3, 32, 1"), i![Seq(p!(@3), p!(32), p!(1))]);
        assert_eq!(parse!("EQ @3, 32, 1"), i![Seq(p!(@3), p!(32), p!(1))]);
        assert_eq!(parse!("INCB #hello"), i![Incb(p!(#hello))]);
        assert_eq!(parse!("HALT"), i![Halt]);
    }

    #[test]
    fn parse_exprs() {
        let expr_parse = expr();
        macro_rules! expr_test {
            ($expr: literal, $expected: ident) => {
                let parsed = expr_parse.parse($expr).unwrap();
                assert_eq!(parsed, $expected, "{{ {} }} != {{ {parsed} }}", $expr);
            };
        }
        let one = Expr::Number(1);
        expr_test!("1", one);

        let one = Arc::new(one);
        let lhs = Arc::clone(&one);
        let rhs = Arc::clone(&one);
        let expected = Expr::BinOp {
            lhs,
            op: BinOperator::Add,
            rhs,
        };
        expr_test!("1 + 1", expected);

        let expected = Expr::BinOp {
            lhs: Arc::new(Expr::BinOp {
                lhs: Arc::clone(&one),
                op: BinOperator::Mul,
                rhs: Arc::clone(&one),
            }),
            op: BinOperator::Add,
            rhs: Arc::clone(&one),
        };
        expr_test!("1 * 1 + 1", expected);

        let expected = Expr::Inner(Arc::new(Expr::UnaryAdd(Arc::new(Expr::Ident("e")))));
        expr_test!("(+e)", expected);
        let expected = Expr::BinOp {
            lhs: Arc::new(Expr::Inner(Arc::new(Expr::BinOp {
                lhs: Arc::clone(&one),
                op: BinOperator::Add,
                rhs: Arc::new(Expr::UnaryAdd(Arc::new(Expr::Negate(Arc::new(
                    Expr::Ident("e"),
                ))))),
            }))),
            op: BinOperator::Sub,
            rhs: Arc::clone(&one),
        };
        expr_test!("(1 + +-e) - 1", expected);
    }
}
