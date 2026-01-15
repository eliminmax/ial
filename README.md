<!--
SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->

# Intcode Assembly Language

A library built around my Intcode module from Advent of Code 2019, cleaned up and reorganized, as well as an assembly language that can assemble into it.

**It is in a state of active tweaking with regular breaking changes, and does not yet follow SemVer**

See [IAL.md](./IAL) for documentation of IAL's syntax and semantics.

It's organized as a library which provides the `ial::Interpreter` struct as a way to interpret and debug intcode, an `ial::asm` module which provides an extended version of a [proposed assembly language from the Esolang wiki](https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax), and a few small binaries that make use of those: `ial-as` is an assembler, `ial-dis` is a disassembler, and `intcode` acts as an interpreter.

The interpreter is fully functional, with all of the [opcodes](https://esolangs.org/wiki/Intcode#Opcodes) and [parameter modes](https://esolangs.org/wiki/Intcode#Parameter_Modes) defined in the completed Intcode computer for [Advent of Code 2019 Day 9](https://adventofcode.com/2019/day/9).

## General Examples

```rust
use ial::prelude::*;
let mut interpreter = Interpreter::new(vec![104, 1024, 99]);

assert_eq!(
    interpreter.run_through_inputs(std::iter::empty()).unwrap(),
    (vec![1024], State::Halted)
);
```

```rust
use ial::{prelude::*, asm::assemble};
const ASM: &str = r#"
OUT #1024
HALT
"#;

let assembled = assemble(ASM).unwrap();
assert_eq!(assembled, vec![104, 1024, 99]);

let mut interpreter = Interpreter::new(assembled);
assert_eq!(
    interpreter.run_through_inputs(std::iter::empty()).unwrap(),
    (vec![1024], State::Halted)
);
```

## Code and Documentation Provenance

All code and documentation in this repository is 100% written by me, Eli Array Minkoff, a human being with a cybersecurity degree and an insatiable desire to continuously expand my understanding of computers and computer programming.

I have not used any LLM tools—beyond the widely-discussed ethical and copyright concerns, I program for the joy of learning, and the thrill of seeing my creations come to fruition, and outsourcing the work would undermine that.
