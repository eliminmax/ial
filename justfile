# SPDX-FileCopyrightText: 2026 Eli Array Minkoff
#
# SPDX-License-Identifier: 0BSD

[private]
default: update-deps lint test doc doctests

hookdir := `git config get core.hooksPath || echo "$(git rev-parse --git-dir)"/hooks`

[doc('configure git hooks to invoke `githooks` recipes')]
init-git-hooks:
    just install-git-hook 'pre-commit'
    just install-git-hook 'pre-push'

[private]
[doc('set up the provided git hook to run its corresponding just recipe')]
install-git-hook git-hook:
    #!/bin/sh
    if [ -e "{{hookdir / git-hook}}" ]; then
        if grep -q {{quote ("just " + git-hook)}} {{quote(hookdir / git-hook)}}; then
            echo "already installed {{hookdir / git-hook}}"
            exit 0
        fi
        if [ "$(head -n1 {{quote(hookdir / git-hook)}})" != '#!/bin/sh' ]; then
            echo "{{git-hook}} already exists and is not a POSIX script" >&2
            exit 1
        fi
    else
        echo '#!/bin/sh' > {{quote(hookdir / git-hook)}}
        chmod +x {{quote(hookdir / git-hook)}}
    fi
    echo just {{quote((git-hook))}} >> {{quote(hookdir / git-hook)}}

[doc('update dependencies to latest compatible versions')]
update-deps:
    cargo update

[doc('run through tests')]
test:
    cargo nextest run --locked --offline

[doc('format rust code with cargo fmt')]
fmt:
    cargo fmt

[group('check')]
[doc('run codespell on all files in repo')]
spellcheck:
    git ls-files -z -- . ':!:LICENSES/*.txt' ':!:ial/tests/colortest' |\
            xargs -0 codespell

[group('check')]
[doc('validate rust formatting')]
fmt-check:
    cargo fmt --check

[doc('run `cargo clippy` with sensible options')]
[group('check')]
clippy:
    cargo clippy --locked --offline --workspace

[doc('ensure that all doctests pass')]
[group('check')]
doctests:
    cargo test --locked --offline doc

[group('check')]
[doc('ensure code coverage is at least 90%')]
check-coverage:
    cargo tarpaulin --locked --offline --fail-under 90

[group('check')]
[doc('validate REUSE copyright headers')]
check-reuse:
    reuse lint

[group('check')]
[doc('make sure all crates versions match up')]
validate-versions:
    python3 tooling/validate-versions.py

[doc('build documentation with rustdoc')]
doc:
    cargo doc --no-deps

[doc('install ial-cli from source')]
install:
    cargo install --path ./ial-cli

[group('githooks')]
pre-commit: lint doctests

[group('githooks')]
pre-push: check

[group('meta-recipes')]
[doc('meta-recipe to run lightweight `check`s')]
lint: clippy check-reuse fmt-check spellcheck validate-versions

[group('meta-recipes')]
[doc('meta-recipe to run all `check`s')]
check: spellcheck fmt-check clippy doctests check-coverage check-reuse validate-versions
