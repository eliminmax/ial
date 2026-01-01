<!--
SPDX-FileCopyrightText: 2025 Eli Array Minkoff

SPDX-License-Identifier: 0BSD
-->

# intcode

A library built around my intcode module from Advent of Code 2019, cleaned up and reorganized, with additions to support the proposed assembly syntax from [Esolang, the esoteric programming languages wiki](https://esolangs.org/wiki/Intcode#Proposed_Assembly_Syntax).

It's organized as a library which provides the `intcode::Interpreter` struct as a way to interact with intcode, an optional `intcode::asm` module which provides an implementation of the assembly language from the Esolang wiki, and a few small binaries that make use of those: `intcode_as` is an assembler, and `intcode_ascii` provides an interactive interface using [Aft Scaffolding Control and Information Interface](https://adventofcode.com/2019/day/17) *(not to be confused with the [American Standard Code for Information Interchange](https://simple.wikipedia.org/wiki/ASCII))*.
