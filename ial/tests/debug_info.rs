// SPDX-FileCopyrightText: 2026 Eli Array Minkoff
//
// SPDX-License-Identifier: 0BSD

use chumsky::Parser;
use flate2::read::ZlibDecoder;
use ial_ast::parsers::ial;
use ial_ast::util::span;
use ial_ast::{DirectiveKind, prelude::*};
use ial_debug_info::{DebugInfo, DirectiveDebug};
use std::io::Read;

/// Unreadable macro to allow for readable test values
///
/// Values can be grouped together in curly braces, and this macro will strip them out,
/// allowing for long sequences of connected bytes to be kept grouped near a comment explaining
/// them.
///
/// Internally, it keeps the sequence of comma-separated u8 literals it's handled within curly
/// braces, separated by the unprocessed tokens by a `~`, and recursively calls itself,
/// unpacking groups, and appending tokens into the handled tokens within the curly brackets,
/// until all tokens are handled
macro_rules! encoded {
    // If passed a sequence of comma-separated token trees, rerun with `{} ~` appended.
    [$($toks: tt),+] => {{ encoded![{} ~ $($toks),+] }};

    // If no values are handled, and the leading token is a group, unpack that group
    [{} ~ {$($group: tt),+}, $($terms: tt),+] => {{ encoded![{} ~ $($group),+, $($terms),*] }};

    // If no values are handled, and the leading token is a literal, put it into the handled
    // tokens
    [{} ~ $current: literal, $($terms: tt),+] => {{ encoded![{ $current } ~ $($terms),*] }};
    // If the next unhandled value is a literal, append it
    [{$($handled: tt),+} ~ $current: literal, $($terms: tt),+] => {{
        encoded![{$($handled),+, $current } ~ $($terms),+]
    }};

    // if the next unhandled value is a group, unpack it
    [{$($handled: tt),+} ~ {$($group: tt),+}, $($terms: tt),+] => {{
        encoded![{$($handled),+ } ~ $($group),+, $($terms),+]
    }};

    // If the last unhandled value is a literal, append it and resolve to the final array
    [{$($handled: tt),+} ~ $current: literal] => {{ [$($handled),+, $current] }};

    // If the last unhandled value is a group, unpack it
    [{$($handled: tt),+} ~ {$($group: tt),+}] => {{ encoded![{$($handled),+ } ~ $($group),+] }};

}

#[test]
fn round_trip() {
    let ast = ial()
        .parse("a: b: c: ADD #9, #90, d\nd:ASCII \"hi\"")
        .unwrap();
    let expected_debug_info = DebugInfo::new(
        vec![
            (span("a", 0..1), 0),
            (span("b", 3..4), 0),
            (span("c", 6..7), 0),
            (span("d", 24..25), 4),
        ],
        vec![
            DirectiveDebug {
                kind: DirectiveKind::Instruction,
                src_span: SimpleSpan::from(9..23),
                output_span: SimpleSpan::from(0..4),
            },
            DirectiveDebug {
                kind: DirectiveKind::Ascii,
                src_span: SimpleSpan::from(26..36),
                output_span: SimpleSpan::from(4..6),
            },
        ],
    );

    let expected_serialized = encoded![
        // 4 labels total
        {4,
            // 1st label is 1 byte long, and the byte/s consist of { b'a' }
            {1, {b'a'}},
            // 1st label's source span starts at 0, and is 1 long
            {0, 1},
            // 1st label resolves to address 0
            {0, 0, 0, 0, 0, 0, 0, 0},
            // 2nd label is 1 byte long, and the byte/s consist of  { b'b' }
            {1, {b'b'}},
            // 2nd label's source span starts at 3, and is 1 long
            {3, 1},
            // 2nd label resolves to address 0
            {0, 0, 0, 0, 0, 0, 0, 0},
            // 3rd label is 1 byte long, and the byte/s consist of { b'c' }
            {1, {b'c'}},
            // 3rd label's source span starts at 6, and is 1 long
            {6, 1},
            // 3rd label resolves to address 0
            {0, 0, 0, 0, 0, 0, 0, 0},
            // 4th label is 1 byte long, and the byte/s consist of { b'd' }
            {1, {b'd'}},
            // 4th label's source span starts at 24, and is 1 long
            {24, 1},
            // 4th label resolves to address 4
            {4, 0, 0, 0, 0, 0, 0, 0}
        },
        // 2 directives total
        {2,
            // 1st directive is an instruction
            {0,
                // span in source starts at 9 and is 14 long
                {9, 14},
                // span in output starts at 0 and is 4 long
                {0, 4}
            },
            // 2nd directive is ascii
            {2,
                // span in source starts at 26 and is 10 long
                {26, 10},
                // span in output starts at 4 and is 2 long
                {4, 2}
            }
        }
    ];

    let (_, dbg) = ial::asm::assemble_with_debug(ast).unwrap();
    assert_eq!(dbg, expected_debug_info);
    let written: Vec<u8> = {
        let mut w = Vec::new();
        dbg.write(&mut w).unwrap();
        w
    };

    assert_eq!(&written[..8], ial_debug_info::parse::HEADER);

    let mut decoded = Vec::with_capacity(expected_serialized.len());
    ZlibDecoder::new(&written[8..])
        .read_to_end(&mut decoded)
        .unwrap();
    assert_eq!(decoded, expected_serialized);

    assert_eq!(
        DebugInfo::read(written.as_slice()).unwrap(),
        expected_debug_info
    );
}
