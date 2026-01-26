<!--
SPDX-FileCopyrightText: 2026 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->
# Intcode Assembly Language (IAL)

<!-- vim-markdown-toc GFM -->

* [Lines](#lines)
    * [Labels](#labels)
    * [Directives](#directives)
        * [Instructions](#instructions)
            * [Parameters](#parameters)
        * [DATA Directives](#data-directives)
        * [ASCII Directives](#ascii-directives)
    * [Comments](#comments)
* [Expressions](#expressions)
* [Extensions to Assembly Proposal](#extensions-to-assembly-proposal)

<!-- vim-markdown-toc -->

IAL uses a line-based syntax. Source code is encoded as UTF-8 text.

## Lines

Each line has 3 components - one of more [labels](#labels), an optional [directive](#directives), and an optional [comment](#comments).

Taking a cue from [NASM][nasm], a label is an identifier followed by a colon (`:`), and the comment starts with `;`:

<pre>
label: directive ; comment
</pre>

### Labels

A label is a unique[^label-uniqueness] identifer which can be used to refer to the index of the next integer in the Intcode output. It can be thought of as a name for that index.

Each label is immediately followed by a colon, without any whitespace. More than one label can exist on the same line.

As an example, the following code starts out with a single `ADD` instruction, which sets the initially-zeroed opcode integer of the following instruction to a `HALT` instruction.

```ial
ADD #0, #99, halt
halt:
```

<details><summary>Pedantry about valid label identifiers</summary>
Recognition of valid identifiers is done with <a href="https://docs.rs/chumsky/0.12.0/chumsky/text/unicode/fn.ident.html"><code>chumsky::text::unicode::ident</code></a>, which is documented to match identifiers "defined as per 'Default Identifiers' in <a href="https://www.unicode.org/reports/tr31/#Default_Identifier_Syntax">Unicode® Standard Annex #31</a>", so valid identifiers are more-or-less what you'd expect.

Note that no Unicode normalization is performed, so the identifier `é` (U+00e9 "Latin Small Letter E with acute") is <strong>not</strong> treated identically to `é` (U+0065 Latin Small Letter E followed by U+0301 Combining Acute Accent).
</details>

### Directives

IAL has 3 kinds of directives: instructions, DATA directives, and ASCII[^ASCII-AOC] directives.

Each directive starts with a mnemonic, followed by at least one non-newline whitespace character.

* [Instructions](#instructions) are for actual intcode instructions
* [DATA directives](#data-directives) are for arbitrary data.
* [ASCII directives](#ascii-directives) are for ASCII text literals

#### Instructions

The instructions consist of a mnemonic followed by a comma-separated list of [parameters](#parameters).

When assembled, the instructions are encoded directly, as documented in the various Advent of Code puzzles that intcode originates from.

The following instructions are supported:

| Opcode | Mnemonic(s)\* | Parameters      | Origin                       | Description                                             |
|--------|---------------|-----------------|------------------------------|---------------------------------------------------------|
| 1      | `ADD`         | `a`, `b`, `out` | [Day 2][day-2]               | Store `a + b` in `out`[^out-params]                     |
| 2      | `MUL`         | `a`, `b`, `out` | [Day 2][day-2]               | Store `a * b` in `out`[^out-params]                     |
| 3      | `IN`          | `out`           | [Day 5][day-5]               | Read 1 int from input, store in `out`[^out-params]      |
| 4      | `OUT`         | `a`             | [Day 5][day-5]               | Write `a` to output                                     |
| 5      | `JNZ`         | `addr`, `val`   | [Day 5 part 2][day-5-part-2] | If `val` is nonzero, move instruction pointer to `addr` |
| 6      | `JZ`          | `addr`, `val`   | [Day 5 part 2][day-5-part-2] | If `val` is zero, move instruction pointer to `addr`    |
| 7      | `LT`, `SLT`   | `a`, `b`, `out` | [Day 5 part 2][day-5-part-2] | Store `a < b`[^cmp] in `out`[^out-params]               |
| 8      | `EQ`, `SEQ`   | `a`, `b`, `out` | [Day 5 part 2][day-5-part-2] | Store `a == b`[^cmp] in `out`[^out-params]              |
| 9      | `RBO`, `INCB` | `a`             | [Day 9][day-9]               | Add `a` to the Relative Base Offset                     |
| 99     | `HALT`        | *none*          | [Day 2][day-2]               | Halt execution                                          |

\* *where there are multiple mnemonics, that's because of a mismatch between the name I prefer, and the name that the [proposed assembly syntax][^proposed-syntax] IAL is based on uses, so IAL supports both.*

##### Parameters

A Parameter consist of an optional parameter-mode prefix, followed by a single [expression](#expressions).

| Prefix | Mode                |
|--------|---------------------|
| *none* | [Positional][day-5] |
| `#`    | [Immediate][day-5]  |
| `@`    | [Relative][day-9]   |

#### DATA Directives

A data directive consists of the special mnemonic "`DATA`", followed by any number of comma-separated [expressions](#expression). The evaluated expressions are stored within the output, immediately after any previous directive's output, and before any further directive's output.

#### ASCII Directives

An ASCII[^ASCII-AOC] directive consists of the special mnemonic "`ASCII`", followed by string of ASCII[^ASCII-REAL] text, within double quotes. Each character within the quotes may be any ASCII character other than `\` or `"`, or an escape sequence.

The following escape sequences are supported:

| sequence | meaning                                                             |
|----------|---------------------------------------------------------------------|
| `\\`     | a literal backslash                                                 |
| `\'`     | a literal single quote                                              |
| `\"`     | a literal double-quote                                              |
| `\n`     | a line-feed                                                         |
| `\t`     | a horizontal tab                                                    |
| `\r`     | a carriage-return                                                   |
| `\e`     | an escape character                                                 |
| `\O`     | a byte with the value O, where O is a 1, 2, or 3 digit octal number |
| `\xHH`   | a byte with the value HH, where HH is a 2-digit hexadecimal number  |

For example, the following hello world program uses an ASCII directive:

```ial
RBO #hello
loop: OUT @0
      RBO #1
      JNZ #loop, @0
hello: ASCII "Hello, world!\n\0"
```

### Comments

A comment starts with a semicolon (`;`). The semicolon, as well as any character that appears between it and the end of the line, are completely ignored during parsing.

If you're wondering why a semicolon is used, it's because it's otherwise unused, and it's what [NASM][nasm] uses.

## Expressions

Expressions are evaluated when assembling the source, so must not depend on the contents within the intcode memory.

Expressions can be numbers, character literals, [labels](#labels), or basic arithmetic operations on other subexpressions. For example, `32 + LABEL / (-1 * 20 - 5)`. The order of operations is pretty standard:

1. subexpressions in parentheses are evaluated
2. negative signs[^neg-sub] are evaluated
3. multiplications and divisions are evaluated, from left to right
4. additions and subtractions are evaluated, from left to right

Expressions are by far the most complex part of the IAL definition. The simpler version is all you really need to be able to use IAL, but if pedantically-overexplained is more your style, then read the following:

<details><summary>pedantry</summary>

* A **number** is any non-negative 64-bit signed integer, written in its decimal form.
* A **character literal** is either an ASCII character other than `\` or `'`, or an escape sequence. The same list of escape sequences is supported as [ASCII Strings](#ascii-directives).
* A **label** is an identifier as explained [above](#labels)
</details>

## Extensions to Assembly Proposal

IAL's syntax is based on the [proposed assembly syntax on the Intcode page on Esolangs.org][proposed-syntax], and is intended to be a fully-compatible superset of that proposed syntax.

That said, there are a few extensions to that syntax that IAL supports, and while it was the original basis, IAL aims to be more flexible and user-friendly than the proposal it's based on:

* IAL supports comments, as documented [above](#comments)
* Instruction mnemonics are parsed in a case-insensitive manner
* The ASCII directive is defined
* Character literals are supported

One major difference: In 3 cases, the name for an opcode I'd used in my interpreter implementation and the proposed mnemonics differed - in those cases, both my names ("LT", "EQ", and "RBO") and the proposed names ("SLT", "SEQ", and "INCB") are supported, though my name is treated as the "canonical" representation within the code.

<!-- FOOTNOTES AND LINKS -->

[^out-params]: `out` parameters (as listed in the [instructions table](#instructions)) must not be in immediate mode when executed - it's documented in [day 5][day-5] that that will never happen, so it's technically undefined behavior
[^cmp]: comparisons evaluate to `1` for true and `0` for false, as in C and many other languages.
[^proposed-syntax]: see [Extensions to Assembly Proposal](#extensions-to-assembly-proposal)
[^label-uniqueness]: if a label is defined more than once, the code is invalid, and cannot be assembled due to the ambiguity if that label is ever used.
[^neg-sub]: while the same character is used, it is unambiguous in context whether it's a subtraction or a negative sign.
[^ASCII-AOC]: [Aft Scaffolding Control and Information Interface](https://adventofcode.com/2019/day/17)
[^ASCII-REAL]: [American Standard Code for Information Interchange](https://en.wikipedia.org/wiki/ASCII)

[day-2]: <https://adventofcode.com/2019/day/2>
[day-5]: <https://adventofcode.com/2019/day/5>
[day-5-part-2]: <https://adventofcode.com/2019/day/5#part2>
[day-7]: <https://adventofcode.com/2019/day/7>
[day-9]: <https://adventofcode.com/2019/day/9>
[day-17]: <https://adventofcode.com/2019/day/17>
[proposed-syntax]: <https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax>
[nasm]: <https://www.nasm.us/doc/nasm03.html>
