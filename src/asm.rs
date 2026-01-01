// SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff
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
        lhs: Arc<Spanned<Expr<'a>>>,
        op: Spanned<BinOperator>,
        rhs: Arc<Spanned<Expr<'a>>>,
    },
    Negate(Arc<Spanned<Expr<'a>>>),
    UnaryAdd(Arc<Spanned<Expr<'a>>>),
    Inner(Arc<Spanned<Expr<'a>>>),
}

#[derive(Debug)]
pub enum AssemblyError<'a> {
    UnresolvedLabel(&'a str),
    DuplicateLabel(&'a str),
    WriteToImmediate(Box<Instr<'a>>),
}

impl<'a> Expr<'a> {
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
pub struct Parameter<'a>(pub Spanned<ParamMode>, pub Spanned<Expr<'a>>);

fn unspan<T>(Spanned { inner, .. }: Spanned<T>) -> T {
    inner
}

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
                if $mode.inner == ParamMode::Immediate {
                    return Err(AssemblyError::WriteToImmediate(Box::new(self)));
                }
            };
        }
        macro_rules! process_param {
            ([$param: ident] * $multiplier: literal, &mut $instr: ident) => {{
                let Parameter(mode, expr) = $param;
                imm_guard!(mode);
                $instr += mode.inner as i64 * $multiplier;
                unspan(expr).resolve(labels)?
            }};
            ($param: ident * $multiplier: literal, &mut $instr: ident) => {{
                let Parameter(mode, expr) = $param;
                $instr += mode.inner as i64 * $multiplier;
                unspan(expr).resolve(labels)?
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
    DataDirective(Vec<Spanned<Expr<'a>>>),
    Ascii(Spanned<Vec<u8>>),
    Instruction(Box<Instr<'a>>),
}

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug)]
pub struct Line<'a> {
    pub label: Option<&'a str>,
    pub inner: Option<Spanned<LineInner<'a>>>,
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
    .map(|(mode, expr)| Parameter(mode, expr))
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

impl LineInner<'_> {
    pub fn size(&self) -> i64 {
        match self {
            LineInner::DataDirective(exprs) => exprs
                .len()
                .try_into()
                .expect("less than i64::MAX expressions"),
            LineInner::Ascii(text) => text
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
        if let Some(Spanned { inner, .. }) = self.inner {
            match inner {
                LineInner::DataDirective(exprs) => {
                    for expr in exprs {
                        v.push(unspan(expr).resolve(labels)?);
                    }
                }
                LineInner::Ascii(text) => v.extend(unspan(text).into_iter().map(i64::from)),
                LineInner::Instruction(instr) => {
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

fn line_inner<'a>() -> impl Parser<'a, &'a str, Option<Spanned<LineInner<'a>>>, RichErr<'a>> {
    choice((
        (with_sep!(just("DATA"))
            .ignore_then(expr().separated_by(padded!(just(","))).collect())
            .map(LineInner::DataDirective)),
        with_sep!(just("ASCII"))
            .ignore_then(ascii_parse())
            .map(LineInner::Ascii),
        instr().map(Box::new).map(LineInner::Instruction),
    ))
    .spanned()
    .or_not()
}

fn parse_line<'a>() -> impl Parser<'a, &'a str, Line<'a>, RichErr<'a>> {
    text::ascii::ident()
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
mod ast_tests;
