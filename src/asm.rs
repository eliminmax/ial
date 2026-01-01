// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use super::ParamMode;
use chumsky::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;

#[cfg_attr(test, derive(PartialEq))]
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum BinOperator {
    Add = 0,
    Sub = 1,
    Mul = 2,
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

#[derive(Debug)]
pub enum AssemblyError<'a> {
    UnresolvedLabel(&'a str),
    DuplicateLabel(&'a str),
    WriteToImmediate(Instr<'a>),
}

impl<'a> Expr<'a> {
    pub fn resolve(self, labels: &HashMap<&'a str, i64>) -> Result<i64, AssemblyError<'a>> {
        macro_rules! inner {
            ($i: ident) => {
                Arc::unwrap_or_clone($i).resolve(labels)?
            };
        }
        match self {
            Expr::Number(n) => Ok(n),
            Expr::Ident(s) => labels
                .get(s)
                .copied()
                .ok_or(AssemblyError::UnresolvedLabel(s)),
            Expr::BinOp { lhs, op, rhs } => Ok(op.apply(inner!(lhs), inner!(rhs))),
            Expr::Negate(expr) => Ok(-inner!(expr)),
            Expr::UnaryAdd(expr) | Expr::Inner(expr) => Ok(inner!(expr)),
        }
    }
}

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug, Clone)]
pub struct Parameter<'a>(pub ParamMode, pub Expr<'a>);

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug, Clone)]
#[repr(u8)]
pub enum Instr<'a> {
    Add(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 1,
    Mul(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 2,
    In(Parameter<'a>) = 3,
    Out(Parameter<'a>) = 4,
    Jnz(Parameter<'a>, Parameter<'a>) = 5,
    Jz(Parameter<'a>, Parameter<'a>) = 6,
    Slt(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 7,
    Seq(Parameter<'a>, Parameter<'a>, Parameter<'a>) = 8,
    Incb(Parameter<'a>) = 9,
    Halt = 99,
}

impl Instr<'_> {
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
    pub fn resolve(
        self,
        labels: &HashMap<&'a str, i64>,
    ) -> Result<impl Iterator<Item = i64>, AssemblyError<'a>> {
        macro_rules! imm_guard {
            ($mode: ident) => {
                if $mode == ParamMode::Immediate {
                    return Err(AssemblyError::WriteToImmediate(self));
                }
            };
        }
        macro_rules! process_param {
            ([$param: ident] * $multiplier: literal, &mut $instr: ident) => {{
                let Parameter(mode, expr) = $param;
                imm_guard!(mode);
                $instr += mode as i64 * $multiplier;
                expr.resolve(labels)?
            }};
            ($param: ident * $multiplier: literal, &mut $instr: ident) => {{
                let Parameter(mode, expr) = $param;
                $instr += mode as i64 * $multiplier;
                expr.resolve(labels)?
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
            Instr::Add(a, b, c) => process_instr!(1, a, b, [c]),
            Instr::Mul(a, b, c) => process_instr!(2, a, b, [c]),
            Instr::In(a) => process_instr!(3, [a]),
            Instr::Out(a) => process_instr!(4, a),
            Instr::Jnz(a, b) => process_instr!(5, a, b),
            Instr::Jz(a, b) => process_instr!(6, a, b),
            Instr::Slt(a, b, c) => process_instr!(7, a, b, [c]),
            Instr::Seq(a, b, c) => process_instr!(8, a, b, [c]),
            Instr::Incb(a) => process_instr!(9, a),
            Instr::Halt => process_instr!(99),
        }
    }
}

#[cfg_attr(test, derive(PartialEq))]
#[non_exhaustive]
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
    ($inner: expr) => {{ $inner.padded_by(text::inline_whitespace()) }};
}

macro_rules! with_sep {
    ($inner: expr) => {{ padded!($inner.then_ignore(text::inline_whitespace().at_least(1))) }};
}

type RichErr<'a> = chumsky::extra::Err<Rich<'a, char>>;

fn param<'a>() -> impl Parser<'a, &'a str, Parameter<'a>, RichErr<'a>> {
    padded!(choice((
        just('@').ignore_then(expr().map(|e| Parameter(ParamMode::Relative, e))),
        just('#').ignore_then(expr().map(|e| Parameter(ParamMode::Immediate, e))),
        expr().map(|e| Parameter(ParamMode::Positional, e)),
    )))
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

fn expr<'a>() -> impl Parser<'a, &'a str, Expr<'a>, RichErr<'a>> + Clone {
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

impl LineInner<'_> {
    pub fn size(&self) -> i64 {
        match self {
            LineInner::DataDirective(exprs) => exprs
                .len()
                .try_into()
                .expect("less than i64::MAX expressions"),
            LineInner::Instruction(instr) => instr.size(),
        }
    }
}
impl<'a> Line<'a> {
    pub fn encode_into(
        self,
        v: &mut Vec<i64>,
        labels: &HashMap<&'a str, i64>,
    ) -> Result<(), AssemblyError<'a>> {
        if let Some(inner) = self.inner {
            match inner {
                LineInner::DataDirective(exprs) => {
                    for expr in exprs {
                        v.push(expr.resolve(labels)?);
                    }
                }
                LineInner::Instruction(instr) => {
                    v.extend(instr.resolve(labels)?);
                }
            }
        }
        Ok(())
    }
}
fn line_inner<'a>() -> impl Parser<'a, &'a str, Option<LineInner<'a>>, RichErr<'a>> {
    (with_sep!(just("DATA"))
        .ignore_then(expr().separated_by(padded!(just(","))).collect())
        .map(LineInner::DataDirective))
    .or(instr().map(LineInner::Instruction))
    .or_not()
}

fn parse_line<'a>() -> impl Parser<'a, &'a str, Line<'a>, RichErr<'a>> {
    text::ascii::ident()
        .then_ignore(just(":"))
        .or_not()
        .then(line_inner())
        .map(|(label, inner)| Line { label, inner })
}

fn grammar<'a>() -> impl Parser<'a, &'a str, Vec<Line<'a>>, RichErr<'a>> {
    parse_line().separated_by(just("\n")).collect()
}

/// Parse the assembly code into a [Vec<Line<'a>>], or a [Vec<Rich<char>>] on failure.
pub fn build_ast<'a>(code: &'a str) -> Result<Vec<Line<'a>>, Vec<Rich<'a, char>>> {
    grammar().parse(code).into_result()
}

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
            index += inner.size();
        }
    }

    let mut v = Vec::with_capacity(index.try_into().unwrap_or_default());

    for line in code {
        line.encode_into(&mut v, &labels)?;
    }

    Ok(v)
}

mod fmt_impls;

#[cfg(test)]
mod ast_tests {
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
        assert_eq!(parse!("ADD #1, @1, 1"), i![Add(p!(#1), p!(@1), p!(1))]);
        assert_eq!(parse!("MUL 3, @20, e"), i![Mul(p!(3), p!(@20), p!(e))]);
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
