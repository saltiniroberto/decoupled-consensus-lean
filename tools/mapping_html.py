#!/usr/bin/env python3
# Imported from the first attempt on 2026-08-13 and re-pointed at this layout the same day.
# Four changes from the original, all of them so that it runs before there is any Lean: the
# paths; a missing statement file counts as no statements rather than raising; a figure row may
# write `—` where it has no Lean file or declarations yet; and the figures column is skipped
# when FigureDeps.lean is absent, which is what makes the whole page producible with nothing
# formalized. Each is marked below.
"""Generate mapping.html from MAPPING.md's results table.

The HTML is a self-contained, sortable, filterable view of the numbered-results
table. MAPPING.md stays the source of truth for the row set and the status; the
per-result docstrings shown in the expanders are read from the statement files
under `Decoupled/Analysis/`, so they cannot drift from what is actually stated.
Every path written into the page is relative to the repository root; the page's
script prefixes the absolute part at load time, taken from the page's own
location, to build the `vscode://file` hrefs.

The "figures" column is computed rather than read: `FigureDeps.lean`, run against
the compiled library, reports which `Spec/` constants each statement's type
reaches, and MAPPING.md's "five algorithm figures" table says which constants
belong to which figure. With no `FigureDeps.lean` the column is left empty and the
rest of the page is still produced, which is how it runs before anything is
formalized.

Regenerate with `make mapping`.
"""
from __future__ import annotations

import html
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAPPING = ROOT / "MAPPING.md"
OUT = ROOT / "mapping.html"
FIGURE_DEPS = ROOT / "FigureDeps.lean"
NS = "Decoupled."
STATEMENT_FILES = [
    ROOT / "lean" / "Analysis" / "Lemmas.lean",
    ROOT / "lean" / "Analysis" / "Theorems.lean",
    ROOT / "lean" / "Analysis" / "Corollaries.lean",
]
TEX_FILES = [
    ROOT / "latex-specs" / "height_filter_healing.tex",
    ROOT / "latex-specs" / "recovery_core.tex",
]

STATUS_KEY = {"✅ proved": "proved", "🟡 partial": "partial", "🔨 stated": "stated",
              "⛔ absent": "absent"}
# "stated": written down and not proved. Whether the declaration is a `theorem` whose proof
# is `sorry` or a `def … : Prop` over a notion this project has not modelled is a Lean-level
# difference, explained in the statement's own docstring; it is not a difference in progress,
# so it is not a separate status.
LABEL_RE = r"(?:lem|cor|thm|prop):[a-z0-9-]+"


def jump(path: Path, line: int, text: str) -> str:
    """A jump link plus a copy-`path:line` glyph, both carrying `path:line`
    relative to the repository root.

    The script gives the link a `vscode://` href, which works from an external
    browser (the OS hands it to VS Code); inside VS Code's own preview that
    scheme is swallowed, so the glyph copies `path:line` for pasting into
    Ctrl+P, which accepts a repository-relative path with that suffix."""
    target = f"{path.relative_to(ROOT).as_posix()}:{line}"
    return (f'<a class="jump" data-t="{html.escape(target)}" title="open {path.name}:{line}'
            f' (external browser)">{text}</a>'
            f'<button class="copy" data-t="{html.escape(target)}"'
            f' title="copy {path.name}:{line} — paste into Ctrl+P">⧉</button>')


def md_inline(s: str) -> str:
    s = html.escape(s)
    s = re.sub(r"`([^`]+)`", r"<code>\1</code>", s)
    s = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", s)
    return s


def docstring_html(doc: str) -> str:
    """A Lean docstring body as paragraphs, minimally rendered."""
    body = re.sub(r"^\s*", "", doc, flags=re.M)
    paras = [p.strip() for p in re.split(r"\n\s*\n", body) if p.strip()]
    return "".join(f"<p>{md_inline(re.sub(chr(10), ' ', p))}</p>" for p in paras)


def lean_statements() -> dict[str, dict]:
    """label -> {name, names, file, line, doc} for every statement of record.

    A label can be rendered by more than one theorem — `lem:empty-slot-noop` is
    `lemEmptySlotNoop` and `lemEmptySlotNoop_fields`. The first one is what the row
    links to and quotes; `names` is all of them, which is what the figure
    dependencies are taken over."""
    out: dict[str, dict] = {}
    # `def` as well as `theorem`: a result whose statement cannot yet be written over the
    # current vocabulary is a `def … : Prop` taking the absent notion as an argument.
    decl = re.compile(r"/--((?:[^-]|-(?!/))*?)-/\s*\n(?:theorem|def) (\w+)")
    # A statement file that does not exist yet contributes no statements. Every row is then
    # absent, which `build` requires of a row with no Lean.
    for f in (f for f in STATEMENT_FILES if f.exists()):
        text = f.read_text()
        for m in decl.finditer(text):
            doc, name = m.group(1), m.group(2)
            lm = re.search(rf"\(`({LABEL_RE})`", doc)
            if not lm:
                continue
            line = text.count("\n", 0, m.end(2)) + 1
            entry = out.setdefault(
                lm.group(1), {"name": name, "names": [], "file": f, "line": line, "doc": doc})
            entry["names"].append(name)
    return out


def tex_spans() -> dict[str, tuple[Path, int]]:
    """label -> (tex file, line of the result's or the figure's \\begin{...})."""
    out: dict[str, tuple[Path, int]] = {}
    for f in TEX_FILES:
        lines = f.read_text().splitlines()
        for i, line in enumerate(lines):
            # A result's own \label is the first one after its \begin; a figure's
            # caption can carry a second label (`fig:recovery-round`), so there the
            # `alg:` one is picked out rather than the first.
            if re.match(r"\\begin\{(lemma|theorem|corollary|proposition)\}", line):
                pat, span = r"\\label\{([^}]+)\}", 3
            elif re.match(r"\\begin\{figure\}", line):
                pat, span = r"\\label\{(alg:[^}]+)\}", 4
            else:
                continue
            for j in range(i, min(i + span, len(lines))):
                lm = re.search(pat, lines[j])
                if lm:
                    out.setdefault(lm.group(1), (f, i + 1))
                    break
    return out


def figures() -> list[dict]:
    """MAPPING.md's five algorithm figures: label, number, Lean file, declarations.

    A figure not yet rendered writes `—` in both Lean cells; `file` is then None and `decls`
    is empty, and neither the legend nor `figure_deps` asks anything of it."""
    row = re.compile(r"\| `(alg:[a-z-]+)` \| Fig\. (\d+) \| (`[^`]+`|—) \| (.*?) \|$")
    out = [{"label": m.group(1), "num": m.group(2),
            "file": None if m.group(3) == "—" else ROOT / m.group(3).strip("`"),
            "decls": [] if m.group(4).strip() == "—"
                     else [d.strip(" `") for d in m.group(4).split(",")]}
           for m in (row.match(line) for line in MAPPING.read_text().splitlines()) if m]
    if not out:
        raise SystemExit("no algorithm-figure rows found in MAPPING.md")
    return out


def figure_deps(figs: list[dict]) -> dict[str, list[dict]]:
    """theorem name -> the figures its statement reaches, in figure order.

    `FigureDeps.lean` reports the `Spec/` constants each statement's type reaches,
    transitively and through unfolded definitions; a constant belongs to a figure
    when it is one of that figure's declarations from MAPPING.md, or is nested
    under one (`RoundOutput.mk`, `processSlot.eq_1`).

    No `FigureDeps.lean` means nothing is formalized yet: no statement can reach a figure, so
    the answer is empty for every name and the column comes out as `—` throughout."""
    if not FIGURE_DEPS.exists():
        print(f"figures column SKIPPED: no {FIGURE_DEPS.name}")
        return {}

    r = subprocess.run(["lake", "env", "lean", str(FIGURE_DEPS.relative_to(ROOT))],
                       cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"{FIGURE_DEPS.name} failed — is the library built?"
                         f" (`make build`)\n{r.stdout}{r.stderr}")

    declared: set[str] = set()
    reached: dict[str, list[str]] = {}
    for line in r.stdout.splitlines():
        kind, _, rest = line.partition("\t")
        if kind == "spec":
            declared.add(rest)
        elif kind == "dep":
            name, _, consts = rest.partition("\t")
            reached[name.removeprefix(NS)] = consts.split()
        else:
            raise SystemExit(f"unexpected output from {FIGURE_DEPS.name}: {line[:80]}")

    def under(const: str, decl: str) -> bool:
        return const == NS + decl or const.startswith(f"{NS}{decl}.")

    owned: list[set[str]] = []
    for f in figs:
        for d in f["decls"]:
            if not any(under(c, d) for c in declared):
                raise SystemExit(f"MAPPING.md lists `{d}` under {f['label']},"
                                 " but no such declaration is in Spec/")
        owned.append({c for c in declared if any(under(c, d) for d in f["decls"])})
    return {name: [f for f, cs in zip(figs, owned) if not cs.isdisjoint(consts)]
            for name, consts in reached.items()}


def rows() -> list[dict[str, str]]:
    lines = MAPPING.read_text().splitlines()
    try:
        hdr = lines.index("| Paper | № | Lean | cited by | Status |")
    except ValueError as e:
        raise SystemExit("results-table header not found in MAPPING.md") from e
    out = []
    for line in lines[hdr + 2:]:
        if not line.startswith("| "):
            break
        cells = [c.strip() for c in line.strip().strip("|").split(" | ")]
        if len(cells) != 5:
            raise SystemExit(f"row does not have 5 cells: {line[:80]}")
        label, num, note, cited, status = cells
        if status not in STATUS_KEY:
            raise SystemExit(f"unknown status {status!r} in: {line[:80]}")
        kind, _, n = num.partition(". ")
        out.append({
            "label": label.strip("`"), "kind": kind, "num": n,
            "note": note, "cited": cited, "status": status, "key": STATUS_KEY[status],
        })
    return out


def build(rs: list[dict], leans: dict[str, dict], texs: dict[str, tuple[Path, int]],
          figs: list[dict], deps: dict[str, list[dict]]) -> str:
    counts = {k: sum(1 for r in rs if r["key"] == k)
              for k in ("proved", "partial", "stated", "absent")}
    kind_names = {"Lem": "lemmas", "Thm": "theorems", "Cor": "corollaries", "Prop": "propositions"}
    kind_counts = {k: sum(1 for r in rs if r["kind"] == k) for k in kind_names}
    kind_buttons = "".join(
        f'<button data-k="{k}">{kind_names[k]} ({kind_counts[k]})</button>'
        for k in kind_names if kind_counts[k])
    body_rows = []
    missing_tex, missing_lean = [], []
    if any(f["label"] not in texs for f in figs):
        raise SystemExit("no tex figure found for: "
                         + ", ".join(f["label"] for f in figs if f["label"] not in texs))
    fig_counts = {f["num"]: 0 for f in figs}
    none_count = 0
    for r in rs:
        label = r["label"]
        tex = texs.get(label)
        if tex is None:
            missing_tex.append(label)
        lean = leans.get(label)
        if lean is None and r["key"] != "absent":
            missing_lean.append(label)

        label_cell = f"<code>{html.escape(label)}</code>"
        if tex:
            label_cell += " " + jump(tex[0], tex[1], "tex")
        if lean:
            label_cell += " " + jump(lean["file"], lean["line"], "lean")

        note_html = md_inline(r["note"])
        if lean:
            summary = ("what is proved, and what the paper’s sentence adds"
                       if r["key"] in ("partial", "stated")
                       else "the statement’s docstring")
            note_html += (f'<details><summary>{summary}</summary>'
                          f'<div class="doc">{docstring_html(lean["doc"])}</div></details>')

        row_figs = [f for f in figs
                    if lean and any(f in deps.get(n, []) for n in lean["names"])]
        for f in row_figs:
            fig_counts[f["num"]] += 1
        none_count += not row_figs
        fig_cell = "".join(
            f'<span class="fig">Fig. {f["num"]} <code>{html.escape(f["label"])}</code></span>'
            for f in row_figs) or '<span class="none">—</span>'

        cited_sort = re.search(r"\d+", r["cited"])
        body_rows.append(
            f'<tr data-status="{r["key"]}" data-kind="{html.escape(r["kind"])}"'
            f' data-figs="{" ".join(f["num"] for f in row_figs)}">'
            f'<td><span class="badge {r["key"]}">{html.escape(r["status"].split(" ", 1)[1])}</span></td>'
            f"<td>{label_cell}</td>"
            f'<td data-sort="{html.escape(r["kind"])}{int(r["num"]):03d}">'
            f'{html.escape(r["kind"])}. {html.escape(r["num"])}</td>'
            f"<td>{note_html}</td>"
            # No figure sorts last: "9" is above every list of figure numbers as a string.
            f'<td data-sort="{" ".join(f["num"] for f in row_figs) or "9"}">{fig_cell}</td>'
            f'<td data-sort="{cited_sort.group(0) if cited_sort else "0"}">{md_inline(r["cited"])}</td>'
            "</tr>"
        )
    fig_buttons = "".join(
        f'<button data-g="{f["num"]}" title="{html.escape(f["label"])}">'
        f'Fig. {f["num"]} ({fig_counts[f["num"]]})</button>' for f in figs)
    fig_buttons += f'<button data-g="none">no figure ({none_count})</button>'
    dash = '<span class="none">—</span>'
    fig_legend = ""
    for f in figs:
        # `—` in either cell for a figure with no Lean yet.
        file_cell = (jump(f["file"], 1, f["file"].relative_to(ROOT).as_posix())
                     if f["file"] else dash)
        decls_cell = ", ".join(f"<code>{html.escape(d)}</code>" for d in f["decls"]) or dash
        fig_legend += (f'<tr><td>Fig. {f["num"]}</td>'
                       f'<td><code>{html.escape(f["label"])}</code> '
                       f'{jump(*texs[f["label"]], "tex")}</td>'
                       f"<td>{file_cell}</td><td>{decls_cell}</td></tr>")
    if missing_tex:
        raise SystemExit(f"no tex span found for: {', '.join(missing_tex)}")
    if missing_lean:
        raise SystemExit(f"no Lean statement found for non-absent: {', '.join(missing_lean)}")
    up = len(OUT.parent.relative_to(ROOT).parts)

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Paper ↔ Lean mapping — numbered results</title>
<style>
  :root {{ --fg: #1a1a1a; --bg: #ffffff; --line: #d8d8d8; --dim: #666; --inset: #f4f4f5; }}
  @media (prefers-color-scheme: dark) {{
    :root {{ --fg: #e4e4e4; --bg: #17181a; --line: #3a3b3e; --dim: #9a9a9a; --inset: #212226; }}
  }}
  body {{ color: var(--fg); background: var(--bg); font: 15px/1.5 system-ui, sans-serif;
         margin: 2rem auto; max-width: 74rem; padding: 0 1rem; }}
  h1 {{ font-size: 1.4rem; }}
  p.note {{ color: var(--dim); }}
  .controls {{ display: flex; gap: .5rem; flex-wrap: wrap; margin: 1rem 0; align-items: center; }}
  .controls button {{ font: inherit; padding: .25rem .7rem; border: 1px solid var(--line);
    border-radius: 1rem; background: transparent; color: var(--fg); cursor: pointer; }}
  .controls button.on {{ border-color: currentColor; font-weight: 600; }}
  .controls input {{ font: inherit; padding: .25rem .5rem; border: 1px solid var(--line);
    border-radius: .3rem; background: transparent; color: var(--fg); flex: 1; min-width: 12rem; }}
  .controls .sep {{ border-left: 1px solid var(--line); align-self: stretch; }}
  .tablewrap {{ overflow-x: auto; }}
  table {{ border-collapse: collapse; width: 100%; }}
  th, td {{ text-align: left; padding: .35rem .6rem; border-bottom: 1px solid var(--line);
            vertical-align: top; }}
  th {{ cursor: pointer; white-space: nowrap; user-select: none; }}
  th .arrow {{ color: var(--dim); font-size: .8em; }}
  code {{ font-size: .92em; }}
  a.jump {{ font-size: .8em; color: var(--dim); border: 1px solid var(--line);
            border-radius: .3rem 0 0 .3rem; padding: 0 .3rem; text-decoration: none;
            white-space: nowrap; cursor: pointer; }}
  a.jump:hover {{ color: var(--fg); border-color: currentColor; }}
  button.copy {{ font-size: .8em; color: var(--dim); border: 1px solid var(--line);
                 border-left: none; border-radius: 0 .3rem .3rem 0; padding: 0 .3rem;
                 background: transparent; cursor: pointer; }}
  button.copy:hover {{ color: var(--fg); border-color: currentColor; }}
  details {{ margin-top: .3rem; }}
  summary {{ cursor: pointer; color: var(--dim); font-size: .88em; }}
  .doc {{ background: var(--inset); border-left: 3px solid var(--line);
          padding: .4rem .8rem; margin: .3rem 0; font-size: .92em; }}
  .doc p {{ margin: .4rem 0; }}
  .badge {{ display: inline-block; padding: 0 .55rem; border-radius: 1rem; font-size: .85em;
            white-space: nowrap; border: 1px solid transparent; }}
  .fig {{ display: block; white-space: nowrap; font-size: .9em; }}
  .none {{ color: var(--dim); }}
  details.legend {{ margin: 1rem 0; }}
  details.legend table {{ width: auto; margin: .4rem 0; }}
  details.legend td {{ border-bottom: none; padding: .15rem .8rem .15rem 0; }}
  .badge.proved  {{ background: #1a7f3722; color: #1a7f37; border-color: #1a7f3755; }}
  .badge.partial {{ background: #9a670022; color: #b07800; border-color: #9a670055; }}
  .badge.stated  {{ background: #8250df22; color: #8250df; border-color: #8250df55; }}
  .badge.absent  {{ background: #cf222e1e; color: #cf222e; border-color: #cf222e55; }}
  @media (prefers-color-scheme: dark) {{
    .badge.proved  {{ color: #4ac26b; }}
    .badge.partial {{ color: #d4a72c; }}
    .badge.stated  {{ color: #d2a8ff; }}
    .badge.absent  {{ color: #ff7b72; }}
  }}
  td:nth-child(4) {{ min-width: 26rem; }}
</style>
</head>
<body>
<h1>Paper ↔ Lean mapping — numbered results</h1>
<p class="note">Generated from <code>MAPPING.md</code> (the source of truth) by
<code>mapping_html.py</code>; regenerate with <code>make mapping</code>.
{counts["proved"]} proved · {counts["partial"]} partial · {counts["stated"]} stated ·
{counts["absent"]} absent.
Click a column header to sort; buttons and the search box filter. The
<em>tex</em>/<em>lean</em> links open the file in VS Code at the result's line
<strong>when this page is viewed in an external browser</strong>; inside VS Code's
own preview that scheme is blocked — use the ⧉ glyph instead, which copies
<code>path:line</code>, relative to the repository root, for pasting into Ctrl+P.
Expanders show the Lean statement's own
docstring — for 🟡 rows, that is where "what is proved, and what the paper's sentence
adds" is spelled out.</p>
<p class="note"><strong>figures</strong> lists the algorithm figures the Lean statement
reads. It is computed, not written down: unfold every definition the statement mentions,
and see which of the five figures' declarations are reached. So it is transitive — a
statement about <code>blockState</code> reads Figures 1 and 2, because the replay calls
them, and one about a store reads Figure 3 and those two. A row with no figure is stated
over definitions only. Traversing each proof term as well changes no row (2026-08-10).</p>
<details class="legend"><summary>the five algorithm figures</summary>
<table>{fig_legend}</table>
</details>
<div class="controls">
  <button data-f="all" class="on">All ({len(rs)})</button>
  <button data-f="proved">✅ proved ({counts["proved"]})</button>
  <button data-f="partial">🟡 partial ({counts["partial"]})</button>
  <button data-f="stated">🔨 stated ({counts["stated"]})</button>
  <button data-f="absent">⛔ absent ({counts["absent"]})</button>
  <span class="sep"></span>
  <button data-k="all" class="on">all kinds ({len(rs)})</button>
  {kind_buttons}
</div>
<div class="controls">
  <button data-g="all" class="on">all figures ({len(rs)})</button>
  {fig_buttons}
  <input id="q" type="search" placeholder="filter by text — label, note, lemma name…">
</div>
<div class="tablewrap">
<table id="t">
<thead><tr>
  <th>Status <span class="arrow"></span></th>
  <th>Label <span class="arrow"></span></th>
  <th>№ <span class="arrow"></span></th>
  <th>Lean <span class="arrow"></span></th>
  <th>figures <span class="arrow"></span></th>
  <th>cited by <span class="arrow"></span></th>
</tr></thead>
<tbody>
{chr(10).join(body_rows)}
</tbody>
</table>
</div>
<script>
// Paths in the table are relative to the repository root, so this page holds no
// path from the checkout that generated it. This page sits {up} directories below
// that root, so dropping {up} segments from its own location gives the prefix the
// `vscode://file` scheme needs.
const root = decodeURIComponent(location.pathname).split('/').slice(0, -1 - {up}).join('/');
document.querySelectorAll('a.jump').forEach(a => {{
  a.href = 'vscode://file' + root + '/' + a.dataset.t;
}});
const tb = document.querySelector('#t tbody');
const all = Array.from(tb.rows);
let statusF = 'all';
let kindF = 'all';
let figF = 'all';
const q = document.getElementById('q');
function apply() {{
  const needle = q.value.toLowerCase();
  for (const r of all) {{
    const figs = r.dataset.figs ? r.dataset.figs.split(' ') : [];
    const okS = statusF === 'all' || r.dataset.status === statusF;
    const okK = kindF === 'all' || r.dataset.kind === kindF;
    const okG = figF === 'all' || (figF === 'none' ? !figs.length : figs.includes(figF));
    const okQ = !needle || r.textContent.toLowerCase().includes(needle);
    r.style.display = (okS && okK && okG && okQ) ? '' : 'none';
  }}
}}
document.querySelectorAll('.controls button[data-f]').forEach(b => b.onclick = () => {{
  document.querySelectorAll('.controls button[data-f]').forEach(x => x.classList.remove('on'));
  b.classList.add('on'); statusF = b.dataset.f; apply();
}});
document.querySelectorAll('.controls button[data-k]').forEach(b => b.onclick = () => {{
  document.querySelectorAll('.controls button[data-k]').forEach(x => x.classList.remove('on'));
  b.classList.add('on'); kindF = b.dataset.k; apply();
}});
document.querySelectorAll('.controls button[data-g]').forEach(b => b.onclick = () => {{
  document.querySelectorAll('.controls button[data-g]').forEach(x => x.classList.remove('on'));
  b.classList.add('on'); figF = b.dataset.g; apply();
}});
q.oninput = apply;
document.querySelectorAll('button.copy').forEach(b => b.onclick = async () => {{
  try {{ await navigator.clipboard.writeText(b.dataset.t); }}
  catch {{
    const ta = document.createElement('textarea');
    ta.value = b.dataset.t; document.body.appendChild(ta);
    ta.select(); document.execCommand('copy'); ta.remove();
  }}
  const old = b.textContent; b.textContent = '✓';
  setTimeout(() => b.textContent = old, 900);
}});
document.querySelectorAll('#t th').forEach((th, col) => {{
  let dir = 1;
  th.onclick = () => {{
    const key = r => {{
      const c = r.cells[col];
      const s = c.dataset.sort ?? c.textContent.trim();
      const n = Number(s);
      return Number.isNaN(n) ? s : n;
    }};
    all.sort((a, b) => {{
      const x = key(a), y = key(b);
      return (x < y ? -1 : x > y ? 1 : 0) * dir;
    }});
    dir = -dir;
    document.querySelectorAll('#t th .arrow').forEach(a => a.textContent = '');
    th.querySelector('.arrow').textContent = dir === -1 ? '▲' : '▼';
    all.forEach(r => tb.appendChild(r));
  }};
}});
</script>
</body>
</html>
"""


def main() -> None:
    rs = rows()
    figs = figures()
    page = build(rs, lean_statements(), tex_spans(), figs, figure_deps(figs))
    OUT.write_text(page)
    print(f"wrote {OUT.relative_to(ROOT)} ({len(rs)} rows, {len(figs)} figures)")


if __name__ == "__main__":
    main()
