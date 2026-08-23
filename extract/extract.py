#!/usr/bin/env python3
"""Extract a consensus-1-like document out of the frozen Lean files.

Reads extract/Consensus1-frozen/*.lean, writes extract/out/consensus1.tex, and (unless
--no-pdf) compiles it with latexmk -lualatex.

What v1 does, and deliberately no more:

- One section per source file, in a fixed order (Model, Store, then the figures).
- Section prose comes from the file's module header (/-! ... -/), rendered from its
  markdown-lite (headers, bold, backticks, bullet lists, tables).
- A routine whose docstring opens with `name(args)` (Figure N, lines a-b) contributes its
  pseudocode to that figure's block, ordered by first line; the pdf's line numbers are
  taken from the `-- line n` comments in the body. Other lines are unnumbered.
- The body text is the Lean, lightly cleaned (comments stripped, `let mut S := S` dropped);
  the Lean-to-pseudocode rewriting is expected to grow rules over time.
- Every routine's docstring follows its section's figure block as a note paragraph.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "Consensus1-frozen"
OUT = HERE / "out"

# Section order: file stem -> None (use the module header's own title).
FILE_ORDER = [
    "Model",
    "Store",
    "Fig1GoldfishWalk",
    "Fig2GoldfishDuties",
    "Fig3AvailableConfirmation",
    "Fig4SGForkChoice",
    "Fig5SGDuty",
    "Fig6StateTransition",
    "Fig7FGStore",
]
# Vocabulary files (Nondet, Notation, Raise, FinsetM, OldDefs) are the rendering's own
# machinery, not the draft's content, and are skipped.

DECL_RE = re.compile(
    r"^(?:noncomputable\s+)?(def|abbrev|structure|inductive|class|instance)\s+([^\s(:\[{]+)"
)
CITE_RE = re.compile(r"`([A-Za-z_0-9]+\([^`]*\))`[^(]*\(Figure\s+(\d+),\s*lines?\s+(\d+)")
LINENUM_RE = re.compile(r"--\s*line\s+(\d+)")


def parse_file(path: Path):
    """Return (module_header_text, [items]); an item is (docstring, decl_kind, decl_name,
    source_lines)."""
    text = path.read_text(encoding="utf-8")
    lines = text.split("\n")
    header = None
    items = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if line.startswith("/-!"):
            j = i
            buf = []
            while j < n:
                buf.append(lines[j])
                if lines[j].rstrip().endswith("-/"):
                    break
                j += 1
            block = "\n".join(buf)
            block = block[3:]  # strip /-!
            block = block.rstrip()[: -2].rstrip()  # strip -/
            if header is None:
                header = block.strip("\n")
            i = j + 1
            continue
        if line.startswith("/--"):
            j = i
            buf = []
            while j < n:
                buf.append(lines[j])
                if lines[j].rstrip().endswith("-/"):
                    break
                j += 1
            doc = "\n".join(buf)
            doc = doc[3:]
            doc = doc.rstrip()[: -2].rstrip()
            doc = "\n".join(l[4:] if l.startswith("    ") else l for l in doc.split("\n"))
            doc = doc.strip("\n").strip()
            i = j + 1
            # find the declaration this documents
            while i < n and not DECL_RE.match(lines[i]):
                i += 1
            if i >= n:
                break
            m = DECL_RE.match(lines[i])
            start = i
            i += 1
            while i < n and not is_toplevel(lines[i]):
                i += 1
            items.append((doc, m.group(1), m.group(2), lines[start:i]))
            continue
        m = DECL_RE.match(line)
        if m:
            start = i
            i += 1
            while i < n and not is_toplevel(lines[i]):
                i += 1
            items.append(("", m.group(1), m.group(2), lines[start:i]))
            continue
        i += 1
    return header or "", items


def is_toplevel(line: str) -> bool:
    if not line or line[0] in " \t":
        return False
    return bool(
        re.match(
            r"(/--|/-!|noncomputable\b|def\b|abbrev\b|structure\b|inductive\b|class\b|"
            r"instance\b|end\b|namespace\b|section\b|variable\b|open\b|attribute\b|"
            r"set_option\b|scoped\b|macro_rules\b|deriving\b|@\[)",
            line,
        )
    )


def body_lines(src_lines):
    """The statement lines of a do-routine, or of a plain definition, signature dropped."""
    for k, l in enumerate(src_lines):
        stripped = l.rstrip()
        if re.search(r":=\s*(Id\.run\s+)?do\s*$", stripped):
            return src_lines[k + 1 :]
    for k, l in enumerate(src_lines):
        if ":=" in l:
            tail = l.split(":=", 1)[1].strip()
            rest = src_lines[k + 1 :]
            return ([tail] if tail else []) + rest
    return src_lines[1:]


def clean_code_line(line: str):
    """-> (pdf_line_number|None, indent_units, text|None). None text = drop the line."""
    m = LINENUM_RE.search(line)
    num = m.group(1) if m else None
    code = re.sub(r"\s*--.*$", "", line).rstrip()
    if not code.strip():
        return (num, 0, None) if num is None else (num, 0, "")
    indent = (len(code) - len(code.lstrip())) // 2
    text = code.strip()
    if text in ("let mut S := S",):
        return (num, indent, None)
    return (num, indent, text)


# ---------------------------------------------------------------- LaTeX rendering

SPECIALS = {
    "\\": r"\textbackslash{}",
    "&": r"\&",
    "%": r"\%",
    "$": r"\$",
    "#": r"\#",
    "_": r"\_",
    "{": r"\{",
    "}": r"\}",
    "~": r"\textasciitilde{}",
    "^": r"\textasciicircum{}",
}


def esc(s: str) -> str:
    return "".join(SPECIALS.get(c, c) for c in s)


def md_inline(s: str) -> str:
    """Markdown-lite inline: backtick spans to mono, ** to bold, the rest escaped."""
    out = []
    parts = s.split("`")
    for idx, part in enumerate(parts):
        if idx % 2 == 1:
            out.append(r"\codett{" + esc(part) + "}")
        else:
            t = esc(part)
            t = re.sub(r"\*\*([^*]+)\*\*", r"\\textbf{\1}", t)
            out.append(t)
    return "".join(out)


def md_block(text: str) -> str:
    """Markdown-lite block conversion of a module header or docstring."""
    out = []
    lines = text.split("\n")
    i = 0
    n = len(lines)
    para: list[str] = []

    def flush():
        if para:
            out.append(md_inline(" ".join(para)) + "\n")
            para.clear()

    while i < n:
        line = lines[i]
        s = line.strip()
        if not s:
            flush()
            out.append("")
            i += 1
            continue
        m = re.match(r"(#+)\s+(.*)", s)
        if m and line.startswith("#"):
            flush()
            out.append(r"\subsection*{" + md_inline(m.group(2)) + "}")
            i += 1
            continue
        if s.startswith("|"):
            flush()
            rows = []
            while i < n and lines[i].strip().startswith("|"):
                cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
                if not all(re.fullmatch(r"-{3,}", c) for c in cells):
                    rows.append(cells)
                i += 1
            if rows:
                ncols = max(len(r) for r in rows)
                out.append(r"\begin{center}\begin{tabular}{" + "l" * ncols + "}")
                for k, r in enumerate(rows):
                    out.append(" & ".join(md_inline(c) for c in r) + r" \\")
                    if k == 0:
                        out.append(r"\hline")
                out.append(r"\end{tabular}\end{center}")
            continue
        if s.startswith(("- ", "* ")):
            flush()
            out.append(r"\begin{itemize}")
            cur: list[str] = []
            while i < n:
                t = lines[i].strip()
                if t.startswith(("- ", "* ")):
                    if cur:
                        out.append(r"\item " + md_inline(" ".join(cur)))
                    cur = [t[2:]]
                elif t and lines[i].startswith(("  ", "\t")):
                    cur.append(t)
                elif not t:
                    break
                else:
                    break
                i += 1
            if cur:
                out.append(r"\item " + md_inline(" ".join(cur)))
            out.append(r"\end{itemize}")
            continue
        para.append(s)
        i += 1
    flush()
    return "\n".join(out)


PREAMBLE = r"""\documentclass[10pt]{article}
\usepackage[a4paper,margin=2.6cm]{geometry}
\usepackage{fontspec}
\usepackage{xcolor}
\directlua{luaotfload.add_fallback("symfall", {"DejaVuSans:mode=node;"})}
\setmainfont{Latin Modern Roman}[RawFeature={fallback=symfall}]
\setmonofont{DejaVu Sans Mono}[Scale=0.82,RawFeature={fallback=symfall}]
\newcommand{\codett}[1]{\texttt{#1}}
\newcommand{\figline}[3]{\noindent\makebox[2.4em][r]{\scriptsize\color{black!55}#1}%
\hspace{0.7em}\hspace*{#2}\texttt{#3}\par}
\setlength{\parindent}{0pt}
\setlength{\parskip}{4pt plus 1pt}
\begin{document}
\begin{center}
{\LARGE Consensus-1, extracted from the Lean}\\[2mm]
{\small generated by \codett{extract/extract.py} from \codett{extract/Consensus1-frozen/}}
\end{center}
"""


def render_code_block(src_lines, title=None):
    out = [r"\begin{quote}"]
    if title:
        out.append(r"\figline{}{0em}{" + esc("function " + title) + "}")
    pending = None  # a `-- line n` comment on its own line numbers the next code line
    for raw in src_lines:
        num, indent, text = clean_code_line(raw)
        if not text:
            if num:
                pending = num
            continue
        if num is None and pending is not None:
            num = pending
        pending = None
        pad = f"{(indent + (1 if title else 0)) * 1.1:.1f}em"
        label = f"{num}:" if num else ""
        out.append(r"\figline{" + label + "}{" + pad + "}{" + esc(text) + "}")
    out.append(r"\end{quote}")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-pdf", action="store_true")
    args = ap.parse_args()
    OUT.mkdir(exist_ok=True)
    tex = [PREAMBLE]
    for stem in FILE_ORDER:
        path = SRC / f"{stem}.lean"
        if not path.exists():
            print(f"warning: {path} missing", file=sys.stderr)
            continue
        header, items = parse_file(path)
        title = stem
        body = header
        m = re.match(r"#\s+(.*)\n?", header)
        if m:
            title = m.group(1)
            body = header[m.end():]
        tex.append(r"\section*{" + md_inline(title) + "}")
        tex.append(md_block(body))

        figured = []   # (fig, first_line, name_sig, src)
        plain = []     # (docstring, kind, name, src)
        for doc, kind, name, src in items:
            m = CITE_RE.search(doc.split("\n\n")[0]) if doc else None
            if m and kind == "def":
                figured.append((int(m.group(2)), int(m.group(3)), m.group(1), src))
            plain.append((doc, kind, name, src))

        if figured:
            figured.sort(key=lambda x: (x[0], x[1]))
            fig = figured[0][0]
            tex.append(r"\subsection*{Figure " + str(fig) + "}")
            for _fig, _first, sig, src in figured:
                tex.append(render_code_block(body_lines(src), title=sig))

        notes = [
            (doc, name) for doc, kind, name, _ in plain
            if doc and kind in ("def", "structure", "class", "inductive")
        ]
        if notes:
            tex.append(r"\subsection*{Notes, from the docstrings}")
            for doc, name in notes:
                tex.append(r"\paragraph{" + esc(name) + "}")
                tex.append(md_block(doc))
    tex.append(r"\end{document}")
    texfile = OUT / "consensus1.tex"
    texfile.write_text("\n".join(tex), encoding="utf-8")
    print(f"wrote {texfile}")
    if not args.no_pdf:
        r = subprocess.run(
            ["latexmk", "-lualatex", "-interaction=nonstopmode",
             f"-output-directory={OUT}", str(texfile)],
            capture_output=True, text=True)
        if r.returncode != 0:
            tail = "\n".join(r.stdout.split("\n")[-40:])
            print(tail, file=sys.stderr)
            sys.exit(1)
        print(f"wrote {OUT / 'consensus1.pdf'}")


if __name__ == "__main__":
    main()
