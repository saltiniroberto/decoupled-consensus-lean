#!/usr/bin/env python3
# Imported from the first attempt on 2026-08-13 and re-pointed at this layout the same day.
# Four changes from the original, all of them so that it runs before there is any Lean:
# the paths (`latex-specs`, `MAPPING.md` and `Decoupled/Analysis/Lemmas.lean` at the repository
# root); the file scan walks the whole repository rather than one subtree, minus the four
# directories listed in SKIP; a missing Lemmas.lean counts as zero declarations rather than
# raising; and the notice for an unbuilt paper names `latex-specs`.
"""Check every citation of the paper made by this formalization.

Docstrings and MAPPING.md cite the paper on up to three coordinates: the `\\label` key,
the printed number, and — for the lemma statements — the line span of the environment in
the `.tex`.  The label is durable; the other two rot silently when the paper is edited,
and nothing in a Lean build notices.  This is what notices.

What it checks
--------------
1. Every citation names a label that exists.
2. Its kind word agrees with the label's prefix (`def:` ↔ Definition, and so on).
3. Its printed number agrees with the paper's `.aux`.
4. For a statement header, its claimed line span is exactly the span of the
   `\\begin{lemma}…\\end{lemma}` (or theorem, corollary, proposition) it names.
5. MAPPING.md round-trips against `Decoupled/Analysis/Lemmas.lean`: every `lem*` declaration
   is listed, and every listed name is declared.  A statement counts whether it is still a
   `def … : Prop` or has become a proved `theorem`.  With no such file yet, both sides are
   empty and the check passes.


The four citation forms it recognises, all of which occur in the tree:

    Definition 41 (`def:stable-root`)              prose
    (Definition 23, `def:store-join`)              inside a parenthesis
    **Lemma 10** (`lem:past-finalized`, 1092–1101) a statement header
    | `lem:past-finalized` | Lem. 10 | …           a MAPPING.md table row

Two papers, told apart by a label prefix
----------------------------------------
A bare label cites `height_filter_healing.tex`.  A label written `hft:def:store` cites the
companion paper `full/height_filter_and_timeouts.tex` — the store layer's contract since
2026-08-16 — and is checked against that paper's own `.aux` and line spans.  The prefix is
required because the two papers reuse label names (`def:height` exists in both), so looking
a bare label up in both would silently check against the wrong paper.

Numbers come from each paper's `.aux`, a LaTeX **build artefact** that is not tracked
upstream — the submodule carries only `.tex`.  With no healing `.aux` this exits 0 with a
notice rather than failing, so a fresh clone is not blocked; build the paper
(`cd latex-specs && latexmk -pdf height_filter_healing.tex`) to arm it.  With no
companion `.aux` (`cd latex-specs/full && latexmk -pdf height_filter_and_timeouts.tex`),
`hft:` citations are counted but unchecked, again with a notice.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPECS = ROOT / "latex-specs"
AUX = SPECS / "height_filter_healing.aux"
HFT_AUX = SPECS / "full" / "height_filter_and_timeouts.aux"
HFT_TEX = SPECS / "full" / "height_filter_and_timeouts.tex"
LEMMAS = ROOT / "lean" / "Analysis" / "Lemmas.lean"
MAPPING = ROOT / "MAPPING.md"

# Not scanned for citations: `.git`, `.lake` and `latex-specs` are not ours to police, and
# `deps` is another project's.
SKIP = {".git", ".lake", "deps", "latex-specs"}

KIND = {"def": "Definition", "ass": "Assumption", "lem": "Lemma",
        "cor": "Corollary", "rem": "Remark", "alg": "Figure", "thm": "Theorem",
        "prop": "Proposition"}
SHORT = {"Def": "def", "Ass": "ass", "Lem": "lem", "Cor": "cor",
         "Fig": "alg", "Thm": "thm", "Rem": "rem", "Prop": "prop"}

LABEL = r"(?:hft:)?(?:def|ass|lem|cor|rem|alg|thm|prop):[a-z0-9-]+"
KINDS = "|".join(KIND.values())
DASH = r"[–—-]"

# The kind word may be plural -- "Figures 1 (`alg:state-replay`) and 2 (...)" -- so `s?`. Without
# it the whole citation went unchecked, including the first item, because "Figures" is "Figure"
# followed by `s` rather than by a space.
PROSE = re.compile(rf"(?<!\*\*)({KINDS})s? (\d+) \(`({LABEL})`")

# The second and later items of such a list elide the kind word: "and 2 (`alg:...`)". There is no
# kind word to agree with, so only the number is checked -- against the kind the label's own
# prefix names, which is the same thing `check` derives it from.
ELIDED = re.compile(rf"(?:,|and) (\d+) \(`({LABEL})`")
INPAREN = re.compile(rf"\(({KINDS}) (\d+), `({LABEL})`")
HEADER = re.compile(rf"\*\*({KINDS}) (\d+)\*\* \(`({LABEL})`,[^)]*?(\d+){DASH}(\d+)\)")
ROW = re.compile(rf"\| `({LABEL})`[^|]*\| (Def|Ass|Lem|Cor|Fig|Thm|Rem|Prop)\. (\d+)")


def label_numbers(aux: Path, prefix: str = "") -> dict[str, str]:
    return {prefix + label: num for label, num in
            re.findall(r"\\newlabel\{([^}]+)\}\{\{([^}]*)\}", aux.read_text())}


def environment_spans(texs: list[Path], prefix: str = "") -> dict[str, tuple[Path, int, int]]:
    """Where each labelled result environment begins and ends, per source file."""
    spans: dict[str, tuple[Path, int, int]] = {}
    for tex in texs:
        lines = tex.read_text().splitlines()
        for i, line in enumerate(lines):
            m = re.match(r"\\begin\{(lemma|theorem|corollary|proposition)\}", line)
            if not m:
                continue
            for j in range(i, min(i + 2, len(lines))):
                lm = re.search(r"\\label\{([^}]+)\}", lines[j])
                if not lm:
                    continue
                end = next((k for k in range(i, len(lines))
                            if lines[k].startswith(rf"\end{{{m.group(1)}}}")), i)
                spans[prefix + lm.group(1)] = (tex, i + 1, end + 1)
                break
    return spans


def main() -> int:
    if not AUX.exists():
        print(f"citation check SKIPPED: {AUX.relative_to(ROOT)} not built "
              f"(cd latex-specs && latexmk -pdf height_filter_healing.tex)")
        return 0

    nums = label_numbers(AUX)
    spans = environment_spans(sorted(SPECS.glob("*.tex")))
    hft_armed = HFT_AUX.exists()
    if hft_armed:
        nums |= label_numbers(HFT_AUX, "hft:")
        spans |= environment_spans([HFT_TEX], "hft:")
    else:
        print(f"hft: citations UNCHECKED: {HFT_AUX.relative_to(ROOT)} not built "
              f"(cd latex-specs/full && latexmk -pdf height_filter_and_timeouts.tex)")
    bad, seen = [], 0

    def check(path: Path, lineno: int, kind: str, num: str, label: str) -> None:
        nonlocal seen
        seen += 1
        if label.startswith("hft:") and not hft_armed:
            return
        bare = label.removeprefix("hft:")
        where = f"{path.relative_to(ROOT)}:{lineno}"
        if label not in nums:
            bad.append(f"{where}: `{label}` is not a label in the paper")
        elif KIND[bare.split(':')[0]] != kind:
            bad.append(f"{where}: `{label}` cited as {kind}, "
                       f"but its prefix says {KIND[bare.split(':')[0]]}")
        elif nums[label] != num:
            bad.append(f"{where}: `{label}` cited as {kind} {num}, "
                       f"but the paper numbers it {nums[label]}")

    sources = sorted(p for ext in ("*.lean", "*.md") for p in ROOT.rglob(ext)
                     if not SKIP & set(p.relative_to(ROOT).parts))
    for path in sources:
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            for kind, num, label, a, b in HEADER.findall(line):
                check(path, lineno, kind, num, label)
                if label in spans:
                    tex, sa, sb = spans[label]
                    if (int(a), int(b)) != (sa, sb):
                        bad.append(f"{path.relative_to(ROOT)}:{lineno}: `{label}` claims "
                                   f"lines {a}–{b}, but {tex.name} has it at {sa}–{sb}")
            for rx in (PROSE, INPAREN):
                for kind, num, label in rx.findall(line):
                    check(path, lineno, kind, num, label)
            for num, label in ELIDED.findall(line):
                if label in nums:
                    check(path, lineno, KIND[label.removeprefix("hft:").split(':')[0]],
                          num, label)
                else:
                    check(path, lineno, "?", num, label)
            for label, short, num in ROW.findall(line):
                check(path, lineno, KIND[SHORT[short]], num, label)

    lemmas_text = LEMMAS.read_text() if LEMMAS.exists() else ""
    declared = set(re.findall(r"^(?:def|theorem) (lem[A-Z][A-Za-z0-9]*)", lemmas_text, re.M))
    listed = set(re.findall(r"`(lem[A-Z][A-Za-z0-9]*)`", MAPPING.read_text()))
    for name in sorted(declared - listed):
        bad.append(f"{LEMMAS.relative_to(ROOT)}: `{name}` is declared but absent from MAPPING.md")
    for name in sorted(listed - declared):
        bad.append(f"{MAPPING.relative_to(ROOT)}: `{name}` is listed but not declared")

    for line in bad:
        print(f"FAIL {line}")
    print(f"citation check: {seen} citations in {len(sources)} files, "
          f"{len(declared)} statements, {len(bad)} problem(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
