#!/usr/bin/env python3
"""Refuse a tree where a numbered result of the paper is written down but not proved.

`make check`'s `sorry` step is not enough on its own.  A result whose *statement* cannot yet be
written -- because it quantifies over something this project has not modelled -- is a
`def … : Prop` taking the absent notion as an argument, and a `def` holds no `sorry`.  So the
sorry step cannot see it, and `make check` would go green with the paper's lemmas unproved.  That
hole was real on 2026-08-13: four of eight statements were invisible to it.

This reads `MAPPING.md`'s status column instead, which is the one place that distinguishes
"proved" from "written down".  Any row marked `STATED` fails.

It also checks that the column cannot lie about the shape in the Lean: a `def … : Prop` may only
sit behind a `STATED` row, never behind a proved one.

Not part of `make dev`.  A `STATED` row is the normal working state; it is `make check` that must
refuse it.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAPPING = ROOT / "MAPPING.md"
STATEMENTS = [
    ROOT / "lean" / "Analysis" / "Lemmas.lean",
    ROOT / "lean" / "Analysis" / "Theorems.lean",
    ROOT / "lean" / "Analysis" / "Corollaries.lean",
]

STATED = "🔨"
PROVED = ("✅", "🟡")
ABSENT = "⛔"

LABEL = r"(?:def|ass|lem|cor|rem|alg|thm|prop):[a-z0-9-]+"
ROW = re.compile(rf"^\| `({LABEL})` \| ([A-Za-z]+)\. (\d+) \| (.*?) \| (.*?) \| (.*?) \|$")
DECL = re.compile(r"^(def|theorem) (lem[A-Z][A-Za-z0-9]*)", re.M)


def main() -> int:
    bad: list[str] = []

    rows = []
    for lineno, line in enumerate(MAPPING.read_text().splitlines(), 1):
        m = ROW.match(line)
        if m:
            rows.append((lineno, *m.groups()))

    # how each result is declared in the Lean, if it is
    shape: dict[str, str] = {}
    for f in STATEMENTS:
        if f.exists():
            for kind, name in DECL.findall(f.read_text()):
                shape[name] = kind

    stated = 0
    for lineno, label, _kind, _num, lean, _cited, status in rows:
        mark = status.strip()[:1]
        if mark == STATED:
            stated += 1
            bad.append(f"{MAPPING.name}:{lineno}: `{label}` is written down but not proved")
        elif mark in PROVED:
            # a proved row must not be backed by a `def … : Prop`
            for name in re.findall(r"`(lem[A-Z][A-Za-z0-9]*)`", lean):
                if shape.get(name) == "def":
                    bad.append(f"{MAPPING.name}:{lineno}: `{label}` is marked proved, but "
                               f"`{name}` is a `def … : Prop`, which asserts nothing")
        elif mark != ABSENT:
            bad.append(f"{MAPPING.name}:{lineno}: `{label}` has an unrecognised status "
                       f"{status.strip()!r}")

    for line in bad:
        print(f"FAIL {line}")
    if bad:
        print(f"FAIL: {stated} numbered result(s) written down but not proved. "
              f"`make dev` allows this; `make check` does not")
        return 1
    print(f"proved check: {len(rows)} rows, none written down but unproved")
    return 0


if __name__ == "__main__":
    sys.exit(main())
