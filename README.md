<!--
SPDX-FileCopyrightText: 2025 - 2026 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->

# Intcode Assembly Language

A library built around my Intcode Assembly Language based on my Advent of Code 2019 Intcode module, and the [proposed assembly language from the Esolang wiki](https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax).

See [IAL.md](./IAL.md) for documentation of IAL's syntax and semantics.

**It is in a state of active tweaking with regular breaking changes, and does not yet follow SemVer**

## Structure

The `ial` crate provides the assembler and interpreter. The assembler uses an AST defined in the `ial-ast` crate. The AST is intended to remain flexible, so I'm in the process of feature-gating anything in the main `ial` crate that exposes it. The `ial-core` crate provides types that fit conceptually into `ial`, but are needed in `ial-ast`, in order to avoid circular dependencies between `ial` and `ial-ast`.

The `ial` crate provides the `ial::Interpreter` struct as a way to interpret and debug intcode, an `ial::asm` module which provides an IAL assembler, and a few smaller modules.

The `ial-cli` crate provides a command-line interface to the functionality found in the `ial` crate.

## General Examples

```rust
use ial::prelude::*;
let mut interpreter = Interpreter::new(vec![104, 1024, 99]);

assert_eq!(
    interpreter.run_through_inputs([]).unwrap(),
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
    interpreter.run_through_inputs([]).unwrap(),
    (vec![1024], State::Halted)
);
```

## Code and Documentation Provenance

All code and documentation in this repository is 100% written by me, Eli Array Minkoff, a human being with a cybersecurity degree and an insatiable desire to continuously expand my understanding of computers and computer programming.

I have not used any LLM tools—beyond the widely-discussed ethical and copyright concerns, I program for the joy of learning, and the thrill of seeing my creations come to fruition, and outsourcing the work would undermine that.
