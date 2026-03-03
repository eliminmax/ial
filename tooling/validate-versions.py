#!/usr/bin/env python3

"""
SPDX-FileCopyrightText: 2026 Eli Array Minkoff

SPDX-License-Identifier: 0BSD

A script that runs various sanity checks on dependency versions
"""

import tomllib
import sys
from collections import defaultdict
import typing


VersionMap: typing.TypeAlias = dict[str, dict[str, list[str]]]
DEPENDENCY_KEYS = ["dependencies", "dev-dependencies", "build-dependencies"]


def eprint(*args, **kwargs):
    """wrapper around print that defaults to stderr instead of stdout"""
    if "file" not in kwargs:
        kwargs["file"] = sys.stderr
    print(*args, **kwargs)


def crate_depends_on(crates: list[str]) -> str:
    match crates:
        case []:
            raise ValueError
        case [a]:
            return f"{a} depends on"
        case [a, b]:
            return f"{a} and {b} depend on"
        case sl:
            return f"{", ".join(sl[:-1])}, and {sl[-1]} depend on"


with open("Cargo.toml", "rb") as f:
    ial_crates: list[str] = tomllib.load(f)["workspace"]["members"]

# load relevant configuration from members' Cargo.toml
ial_versions: dict[str, str] = {}
dep_versions: VersionMap = defaultdict(lambda: defaultdict(list))
for crate in ial_crates:
    with open(f"{crate}/Cargo.toml", "rb") as f:
        cfg = tomllib.load(f)
        ial_versions[crate] = cfg["package"]["version"]

        for key in filter(lambda k: k in cfg, DEPENDENCY_KEYS):
            for dep, data in cfg[key].items():
                version: str = (
                    data if isinstance(data, str) else data["version"]
                )
                dep_versions[dep][version].append(crate)

errors = 0

if ial_versions["ial"] != ial_versions["ial-core"]:
    errors += 1
    eprint(f"ERROR #{errors}: ial and ial-core version mismatch:")
    eprint(f"    ial-core: v{ial_versions["ial-core"]}")
    eprint(f"         ial: v{ial_versions["ial"]}")

for dep, versions in dep_versions.items():
    if dep in ial_crates:
        for v, crates in versions.items():
            if v == ial_versions[dep]:
                continue
            errors += 1
            eprint(
                f"ERROR #{errors}:",
                f"{crate_depends_on(crates)} workspace member {dep}",
                f"v{v}, but {dep} version is {ial_versions[dep]}"
            )

    if len(versions) > 1:
        errors += 1
        eprint(
            f"ERROR #{errors}:",
            f"multiple versions of {dep} in workspace dependencies:"
        )
        for v, crates in versions.items():
            eprint(f"    - {crate_depends_on(crates)} {dep} v{v}")

if errors:
    msg = f"FAILURE: encountered {errors} error"
    if errors != 1:
        msg += "s"
    sys.exit(msg)
