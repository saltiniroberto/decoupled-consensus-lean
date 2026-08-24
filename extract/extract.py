#!/usr/bin/env python3
"""Extract a consensus-1-like document out of the Lean specification.

Reads the live spec named by SRC below (lean/Spec/, subdirectories included),
writes extract/out/dc.tex, and (unless --no-pdf) compiles it with
latexmk -lualatex. The document's title comes from extract/config.ini
(`title` under `[document]`).

v6: prose can quote a definition instead of restating it. `[eq:name]` in `## Extract`
prose expands to the named declaration's docstring opening span — the formula is
written once, at the definition site; the key is the Lean name, a unique Lean-name
tail, or a unique harvested paper symbol. A paragraph consisting of nothing but
backticked spans and/or `[eq:…]` refs renders as a displayed line: centered, items
separated by quad space — the draft's own equation rows.

v5: the sources drive the structure. Files in a subdirectory render before the files
at SRC's root (the vocabulary a spec is written in terms of precedes its algorithms);
within a directory, config.ini's [order] key for it decides — alphabetical by default,
or a defined order, with `*` standing for the unlisted files alphabetically. A file
emits a section only when something in it is marked `## Extract`.
A `def` whose own docstring carries an `## Extract` section is *figured* — rendered as
pseudocode in the file's figure, in the file's declaration order. The paper form
derives from the Lean signature (`goldfishScore (votes …) (s …) (B …)` renders
`goldfish_score(votes, s, B)`, a store-typed parameter by its structure's symbol); a
docstring that opens with a backticked `name(args)` span overrides the derivation —
the way a paper signature hides Lean-side parameters (`on_tick(Σ, t)` hides the
validator and the proposer test). Any `--` comment in a body is the margin note of the
statement it trails or precedes; nothing numbers lines (a legacy `line n:` prefix in a
comment is stripped; the live spec no longer carries any).

v4: definition blocks. An `## Extract — Definition (Title)` section renders as the
draft's definition environment — bold "Definition N (Title)." running into the section's
first paragraph, later paragraphs following as plain prose. N is assigned by this script,
sequentially in document order: the Lean is the source of truth and the PDF is generated
from it, so no number is read from a docstring (Roberto, 2026-08-24; the docstrings'
"(Definition N of the draft)" citations are provenance, never input).

v3: prose is opt-in. A module header or docstring section headed `## Extract` is
document prose (Roberto, 2026-08-24, choosing the marked-for-inclusion direction and the
keyword); everything unmarked is Lean-side commentary and stays out of the PDF. A header
section `## Extract — X` gets subsection title X. A figured routine's `## Extract`
section leads its figure in, the way the draft's prose introduces each figure; other
declarations' marked sections follow the figure. Marked prose and the figures' margin
notes render in the paper's typography: each backticked span goes through the same
rewriter the figures use, falling back to mono exactly when the span quotes Lean
(binder keywords, `:=`, camelCase or Type-looking names).

v2: the figure blocks are rewritten from Lean into the draft's own pseudocode style.
Every rewrite rule is general — keyed on Lean/Mathlib surface syntax, or driven by
tables harvested from the sources' own conventions — so the script applies to any spec
written with the same stylistic rules. The harvested conventions:

- a docstring that opens with a backticked paper form (`Σ.gf_votes[k]`, `t_s = 4Δs`,
  `B_gen`, `Q_target(σ) = {...}`) names that declaration's paper symbol and access shape;
- a figure citation `name(args)` (Figure N, lines a-b) names a routine, its paper
  signature, and its block; the Lean params are matched against the signature, and
  params absent from it (the validator `i`, the `isProposer` test) stay hidden at call
  sites exactly as the paper's own calls hide them;
- a structure whose field docstrings open with `X.…` is the paper's `X` (the store's Σ),
  and any parameter of that type renders as `X`;
- a structure whose docstring says the tuple `(…)` renders its `.mk` as a tuple, the
  way the paper writes votes; other constructors render as "a <name> with .f = e, …".

Syntax-keyed rules (the paper's spellings, from its own figures): `let`/`let mut`/`:=`
all render `←`; `if _ : c` drops the binder; top-level `∧`/`∨` in a condition become
"and"/"or" and `∧` inside a set-builder becomes a comma; `X ← X ∪ {e}` becomes
"add e to X"; `x ← fun y => e` becomes "define x(y) as e"; a `{state, send}` duty
return becomes "broadcast m; call"; `for x in s` becomes "for all x ∈ s";
`for _ in [:e]` is the figure's bounded "loop"; coercion and Option noise (`↑`,
`(e : T)`, `.toNat`, `.toFinset`, `some`, `.get h`, `pure`, `(← e)`) is stripped, with
`.isSome` rendered `≠ ⊥` and `.getD d` dropped; `filterM`/`imageM`/`biUnion` render as
set-builders and a big union.
"""

import argparse
import configparser
import datetime
import re
import subprocess
import sys
import unicodedata
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE.parent / "lean" / "Spec"
OUT = HERE / "out"
CONFIG = HERE / "config.ini"


def load_config() -> configparser.ConfigParser:
    """The config file beside this script: the document's title, and the per-directory
    file order."""
    cp = configparser.ConfigParser()
    cp.optionxform = str  # directory names are case-sensitive keys
    if not cp.read(CONFIG):
        sys.exit(f"error: {CONFIG} is missing — it sets the document's title")
    return cp


def document_title(cp: configparser.ConfigParser) -> str:
    title = cp.get("document", "title", fallback=None)
    if not title:
        sys.exit(f"error: {CONFIG} sets no title — add `title = …` under [document]")
    return title


def ordered_files(cp: configparser.ConfigParser):
    """The .lean files of SRC in render order. Directories come vocabulary-first
    (subdirectories before the root); within a directory, the [order] key for it
    (its path relative to SRC, `.` for the root) decides: `*` or no key renders
    alphabetically; an exhaustive list of file stems is the defined order, a file it
    does not name an error; a list containing one `*` renders the listed files in
    place and the rest alphabetically at the `*`."""
    by_dir: dict = {}
    for p in SRC.rglob("*.lean"):
        by_dir.setdefault(p.parent, []).append(p)
    dirs = sorted(by_dir, key=lambda d: (d == SRC, str(d)))
    out = []
    for d in dirs:
        rel = str(d.relative_to(SRC)) if d != SRC else "."
        spec = cp.get("order", rel, fallback="*")
        out.extend(order_directory(by_dir[d], spec, rel))
    return out


def order_directory(paths, spec: str, rel: str):
    stems = {p.stem: p for p in paths}
    items = [t.strip() for t in spec.split(",") if t.strip()]
    if items.count("*") > 1:
        sys.exit(f"error: [order] {rel} holds more than one `*`")
    listed = [t for t in items if t != "*"]
    for t in listed:
        if t not in stems:
            sys.exit(f"error: [order] {rel} names `{t}`, but no such file is in {rel}/")
    rest = sorted(s for s in stems if s not in listed)
    if "*" not in items:
        if rest:
            sys.exit(f"error: [order] {rel} is a defined order but does not place "
                     f"{', '.join(rest)} — name them, or add `*` for the rest")
        return [stems[t] for t in listed]
    out = []
    for t in items:
        if t == "*":
            out.extend(stems[s] for s in rest)
        else:
            out.append(stems[t])
    return out

# Files render in alphabetical order of their path under SRC; a file with nothing
# marked `## Extract` emits no section but is still harvested for renames.

DECL_RE = re.compile(
    r"^(?:noncomputable\s+)?(def|abbrev|structure|inductive|class|instance)\s+([^\s(:\[{]+)"
)
# a docstring's opening span that is a pure call — `name(args)` and nothing else —
# names a figured routine's paper signature explicitly, overriding the derivation
SPAN_CALL_RE = re.compile(r"([A-Za-z_0-9]+)\(([^)]*)\)")


# ---------------------------------------------------------------- Lean parsing

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
            block = block.rstrip()[:-2].rstrip()  # strip -/
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
            doc = doc.rstrip()[:-2].rstrip()
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
            r"set_option\b|scoped\b|macro_rules\b|deriving\b|mutual\b|@\[)",
            line,
        )
    )


def split_signature(src_lines):
    """Split a def's source into (signature_text, body_lines).

    The body starts after a line ending `:= do` / `:= Id.run do`, after a bare
    `Id.run do` continuation line, or after the first top-level `:=`."""
    for k, l in enumerate(src_lines):
        stripped = l.rstrip()
        if re.search(r":=\s*(Id\.run\s+)?do\s*$", stripped):
            sig = "\n".join(src_lines[: k + 1])
            return re.sub(r":=\s*(Id\.run\s+)?do\s*$", "", sig), src_lines[k + 1:]
        if re.fullmatch(r"\s*(Id\.run\s+)?do\s*", l):
            return "\n".join(src_lines[:k]).rstrip().rstrip(":=").rstrip(), src_lines[k + 1:]
    for k, l in enumerate(src_lines):
        if ":=" in l:
            head, tail = l.split(":=", 1)
            sig = "\n".join(src_lines[:k]) + "\n" + head
            rest = src_lines[k + 1:]
            body = ([tail] if tail.strip() else []) + rest
            return sig, body
    return "\n".join(src_lines[:1]), src_lines[1:]


PARAM_RE = re.compile(r"\(([^():]+):((?:[^()]|\([^()]*\))*)\)")


def parse_params(sig_text: str):
    """Explicit value params of a signature: [(name, type, is_autoparam)]."""
    # cut at the result-type colon conservatively: scan groups instead
    params = []
    for m in PARAM_RE.finditer(sig_text):
        names = m.group(1).split()
        typ = m.group(2).strip()
        auto = ":=" in typ
        typ = typ.split(":=")[0].strip()
        for nm in names:
            params.append((nm, typ, auto))
    return params


def harvest_fields(src_lines):
    """(field_name, docstring, type) triples from a structure/class/inductive body, and
    (ctor_name, docstring, [param_names]) for inductive constructors."""
    fields, ctors = [], []
    i = 0
    n = len(src_lines)
    doc = ""
    while i < n:
        s = src_lines[i].strip()
        if s.startswith("/--"):
            buf = []
            while i < n:
                buf.append(src_lines[i].strip())
                if src_lines[i].rstrip().endswith("-/"):
                    break
                i += 1
            doc = " ".join(buf)
            doc = doc[3:].rstrip()[:-2].strip()
            i += 1
            continue
        m = re.match(r"\|\s*([A-Za-z_][\w']*)\s*(.*)", s)
        if m:
            pnames = re.findall(r"\(\s*([^():]+?)\s*:", m.group(2))
            names = [nm for grp in pnames for nm in grp.split()]
            ctors.append((m.group(1), doc, names))
            doc = ""
            i += 1
            continue
        m = re.match(r"([A-Za-z_ησΣ][\w'!?]*)\s*:\s*(\S.*)", s)
        if m and src_lines[i].startswith(" "):
            fields.append((m.group(1), doc, m.group(2).strip()))
            doc = ""
            i += 1
            continue
        i += 1
    return fields, ctors


def type_arity(typ: str) -> int:
    """Top-level `→`s of a type: the number of value arguments it takes."""
    depth = 0
    arity = 0
    for c in typ:
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "→" and depth == 0:
            arity += 1
    return arity


# ---------------------------------------------------------------- harvest: rename tables

class Sym:
    """A harvested paper symbol: how a Lean name renders.

    shape: 'plain' | 'call' | 'bracket' | 'subscript' | 'template'
    """

    def __init__(self, name, shape, args=None, template=None, smallcaps=False):
        self.name = name
        self.shape = shape
        self.args = args or []
        self.template = template
        self.smallcaps = smallcaps  # an uncited routine: set like the cited ones

    def __repr__(self):
        return f"Sym({self.name!r},{self.shape})"


def first_span(doc: str):
    """The opening backticked span of a docstring, if the doc starts with one."""
    if not doc or not doc.startswith("`"):
        return None
    end = doc.find("`", 1)
    if end < 0:
        return None
    return doc[1:end]


def parse_symbol(span: str, param_names):
    """Parse a docstring's opening span into a Sym, or None.

    `X.name[..]` / `X.name(..)` / `name(..)` / `sym = …` / `sym_p` / plain."""
    span = span.split(" = ")[0].strip()
    if not span or any(c in span for c in "{}∑⌈"):
        # `q = ⌈2W/3⌉`-style right sides were cut above; a left side with set braces
        # or big operators is a definition body, not a symbol
        if not span or span[0] in "{∑⌈":
            return None
    owner = None
    m = re.fullmatch(r"([A-Za-zΣσ𝒦][\w']*)\.(.+)", span)
    if m and "(" not in m.group(1):
        owner, span = m.group(1), m.group(2)
    m = re.fullmatch(r"([^()\[\]]+)\((.*)\)", span)
    if m:
        args = [a.strip() for a in m.group(2).split(",")] if m.group(2).strip() else []
        return Sym(m.group(1).strip(), "call", args=args), owner
    m = re.fullmatch(r"([^()\[\]]+)\[(.*)\]", span)
    if m:
        return Sym(m.group(1).strip(), "bracket"), owner
    m = re.fullmatch(r"(\w)_(\w+)", span)
    if m and m.group(2) in param_names:
        return Sym(m.group(1), "subscript", args=[m.group(2)]), owner
    if re.fullmatch(r"[^\s,;:]+", span):
        return Sym(span, "plain"), owner
    return None


class Routine:
    def __init__(self, lean_name, paper_name, cite_args, params):
        self.lean_name = lean_name
        self.paper_name = paper_name
        self.cite_args = cite_args      # the paper signature's arg names, as displayed
        self.params = params            # explicit non-autoparam (name, type) pairs


class Tables:
    """Everything harvested from the sources."""

    def __init__(self):
        self.routines = {}       # lean qualified name -> Routine
        self.defs = {}           # lean qualified name -> Sym (non-routine defs/class fields)
        self.fields = {}         # field name -> Sym  (structure-field renames)
        self.struct_sym = {}     # structure lean name -> paper symbol (Store -> Σ)
        self.tuple_structs = set()
        self.ctors = {}          # ctor name -> (Sym or None, param_names)
        self.def_arity = {}      # lean qualified name -> explicit arity
        self.raw_spans = {}      # lean name -> the docstring's full opening span
        self.paper_names = set() # routine names as the paper spells them
        self.duty_monad = None   # the monad `broadcast` writes into (NDREB)

    def callable_names(self):
        return set(self.routines) | set(self.defs)


def derived_arg(t: "Tables", pname: str, ptype: str) -> str:
    """One derived paper-signature slot: a struct-typed parameter shows as its
    structure's paper symbol (the store's Σ), anything else as its snake-cased name."""
    for sname, ssym in t.struct_sym.items():
        if ptype.startswith(sname):
            return ssym
    return snake(pname)


def snake(name: str) -> str:
    """camelCase -> snake_case, the style's own naming rule in reverse.

    Only names with an internal case boundary convert; `B`, `H`, `T_h`, `S'` stay.
    A single-letter suffix keeps its case (`σB` -> `σ_B`)."""
    if not re.search(r"[a-z0-9][A-Z]", name):
        return name
    out = re.sub(r"(?<=[a-z0-9])([A-Z])", r"_\1", name)
    segs = out.split("_")
    if all(len(s) == 1 for s in segs[1:]):
        return out
    return out.lower()


def harvest(all_items):
    """Build the rename tables from every parsed declaration. Two passes: the
    structures first, so a def's derived signature can render a store-typed parameter
    by its structure's paper symbol."""
    t = Tables()
    for doc, kind, name, src in all_items:
        sig, _body = split_signature(src)
        params = [(n, ty) for n, ty, auto in parse_params(sig) if not auto]
        t.def_arity[name] = len(params)
        if kind in ("structure", "class", "inductive"):
            fields, ctors = harvest_fields(src)
            if kind != "inductive" and re.search(r"the tuple\s+`\(", doc):
                t.tuple_structs.add(name)
            owners = []
            for fname, fdoc, ftyp in fields:
                arity = type_arity(ftyp)
                span = first_span(fdoc)
                if span:
                    t.raw_spans.setdefault(fname, span)
                    t.raw_spans[f"{name}.{fname}"] = span
                sym = None
                if span:
                    parsed = parse_symbol(span, [])
                    if parsed:
                        sym, owner = parsed
                        if owner:
                            owners.append(owner)
                if sym is None:
                    shape = "call" if arity else "plain"
                    sym = Sym(snake(fname), shape, args=["·"] * arity)
                elif sym.shape == "plain" and arity:
                    # `a_r` on a function-typed field: the subscript is the argument
                    m2 = re.fullmatch(r"(\w)_(\w+)", sym.name)
                    if m2:
                        sym = Sym(m2.group(1), "subscript", args=[m2.group(2)])
                    else:
                        sym = Sym(sym.name, "call", args=["·"] * arity)
                t.fields.setdefault(fname, sym)
                # a class field is also reachable qualified: Ns.field
                t.defs[f"{name}.{fname}"] = sym
            if owners and len(set(owners)) == 1:
                t.struct_sym[name] = owners[0]
            for cname, cdoc, cparams in ctors:
                sym = None
                # a tuple template anywhere in the doc: "An empty-target vote `(h, ⊥)`"
                for span in re.findall(r"`([^`]+)`", cdoc):
                    if span.startswith("(") and span.endswith(")"):
                        inner = [a.strip() for a in span[1:-1].split(",")]
                        if all(a in cparams or not a.isidentifier() for a in inner) \
                                and any(a in cparams for a in inner):
                            sym = Sym(cname, "template", template=inner, args=cparams)
                            break
                if sym is None:
                    span = first_span(cdoc)
                    if span:
                        parsed = parse_symbol(span, cparams)
                        if parsed and parsed[0].shape == "plain":
                            sym = parsed[0]
                t.ctors[cname] = (sym, cparams)
            continue
    for doc, kind, name, src in all_items:
        if kind != "def":
            continue
        sig, _body = split_signature(src)
        params = [(n, ty) for n, ty, auto in parse_params(sig) if not auto]
        raw = first_span(doc)
        if raw:
            t.raw_spans.setdefault(name, raw)
        if has_extract_section(doc):
            # the def is figured: paper name and signature derive from the Lean def;
            # an opening `name(args)` span overrides — the way the paper hides params
            span = first_span(doc)
            m = SPAN_CALL_RE.fullmatch(span) if span else None
            if m:
                paper = m.group(1)
                cite_args = [a.strip() for a in m.group(2).split(",")] \
                    if m.group(2).strip() else []
            else:
                paper = snake(name.split(".")[-1])
                cite_args = [derived_arg(t, p, ty) for p, ty in params]
            t.routines[name] = Routine(name, paper, cite_args, params)
            continue
        span = first_span(doc)
        if span:
            parsed = parse_symbol(span, [p for p, _ in params])
            if parsed and parsed[0]:
                t.defs[name] = parsed[0]
                continue
        # no harvestable symbol: an unfigured routine still renders as a call, snake-cased
        t.defs[name] = Sym(snake(name.split(".")[-1]), "call",
                           args=[p for p, _ in params], smallcaps=True)
    t.paper_names = {r.paper_name for r in t.routines.values()} | \
        {sym.name for sym in t.defs.values() if sym.smallcaps}
    # the duty monad: the head of `broadcast`'s result type. Routines typed in it are
    # duties — they broadcast as a statement and their tail call carries no `return`.
    for doc, kind, name, src in all_items:
        if kind == "def" and name == "broadcast":
            sig, _b = split_signature(src)
            m = re.search(r":\s*([A-Za-z]\w*)[^:()]*$", sig.strip())
            if m:
                t.duty_monad = m.group(1)
    return t


# ---------------------------------------------------------------- tokenizer

TOKEN_RE = re.compile(
    r"←ᵖ|∈ᴹ|:=|=>|--|[(){}\[\]]"
    r"|[^\W\d][\w'!?]*"            # identifiers, unicode letters included
    r"|\d+"
    r"|[^\sA-Za-z0-9(){}\[\]]",    # any other single symbol char
    re.UNICODE,
)

OPEN = {"(": ")", "[": "]", "{": "}"}


def tokenize(s: str):
    return TOKEN_RE.findall(s)


def parse_group(toks, i=0, closer=None):
    """Token list -> nested tree. A group is ['(', item...]-style dict."""
    items = []
    n = len(toks)
    while i < n:
        tk = toks[i]
        if tk in OPEN:
            sub, i = parse_group(toks, i + 1, OPEN[tk])
            items.append({"open": tk, "items": sub})
            continue
        if closer and tk == closer:
            return items, i + 1
        items.append(tk)
        i += 1
    return items, i


def tree_of(s: str):
    items, _ = parse_group(tokenize(s))
    return items


def is_group(x, br=None):
    return isinstance(x, dict) and (br is None or x["open"] == br)


def flat(tree):
    """Back to a plain string (diagnostics)."""
    out = []
    for x in tree:
        if is_group(x):
            out.append(x["open"] + flat(x["items"]) + OPEN[x["open"]])
        else:
            out.append(x)
    return " ".join(out)


# ---------------------------------------------------------------- statements

class Stmt:
    def __init__(self, indent, text, note=None):
        self.indent = indent
        self.text = text
        self.note = note        # margin note text
        self.spans = None       # rendered spans, filled by the rewriter

    def __repr__(self):
        return f"Stmt({self.text!r})"


BLOCK_ENDERS = ("then", "do", "else")


def clean_note(text: str):
    """A comment's note text: a legacy `line n:` prefix drops (the sources may still
    number their lines; the rendering does not), leading punctuation is trimmed."""
    text = re.sub(r"^lines?\s+\d+(?:[–-]\d+)?\s*", "", text.strip())
    return text.lstrip(",:;— ").strip() or None


def statements_of(body_lines):
    """Join continuation lines into logical statements. Any `--` comment is the margin
    note of the statement it trails or precedes; consecutive comment lines join."""
    stmts = []
    pending_note = None
    for raw in body_lines:
        m = re.search(r"--\s*(.*)$", raw)
        note = clean_note(m.group(1)) if m else None
        code = re.sub(r"\s*--.*$", "", raw).rstrip()
        if not code.strip():
            if note:
                pending_note = f"{pending_note} {note}" if pending_note else note
            continue
        indent = (len(code) - len(code.lstrip())) // 2
        text = code.strip()
        if stmts and _continues(stmts[-1], indent, text):
            stmts[-1].text += " " + text
            if note and not stmts[-1].note:
                stmts[-1].note = note
            continue
        st = Stmt(indent, text, note or pending_note)
        pending_note = None
        stmts.append(st)
    return stmts


def _continues(prev: Stmt, indent: int, text: str) -> bool:
    if prev.text.rstrip().endswith(BLOCK_ENDERS):
        return False
    if indent <= prev.indent:
        return False
    # unbalanced brackets, a trailing connective, or a leading one
    bal = 0
    for c in prev.text:
        if c in OPEN:
            bal += 1
        elif c in OPEN.values():
            bal -= 1
    if bal > 0:
        return True
    if re.search(r"[,∧∨←+\-*/=<>≤≥⪯≺:]$|:=$|∃$", prev.text.rstrip()):
        return True
    if re.match(r"[∧∨+\-*/=<>≤≥⪯≺)(]", text):
        return True
    if text.startswith("("):
        return True
    return False


# ---------------------------------------------------------------- spans (typed output)

# span kinds: kw fn id field sym num
def S_(kind, text):
    return (kind, text)


def sp_id(t):
    return [("id", t)]


def sp_sym(t):
    return [("sym", t)]


def sp_kw(t):
    return [("kw", t)]


def join_sp(parts, sep=None):
    out = []
    for k, p in enumerate(parts):
        if k and sep:
            out.extend(sep)
        out.extend(p)
    return out


COMMA = [("sym", ","), ("space", " ")]


# ---------------------------------------------------------------- the rewriter

KEYWORDS = {"if", "then", "else", "return", "for", "do", "in", "fun", "let", "mut",
            "match", "with", "true", "false",
            # spelled-out connectives, for prose spans quoting figure lines
            "and", "or", "not", "mod"}

INFIX = set("=≠<>≤≥+-*/%∧∨∈∉∪∩⊆⊇\\⪯≺∼←↦∣") | {":=", "=>", "←ᵖ", "∈ᴹ", "→"}


class Rewriter:
    def __init__(self, tables: Tables, routine: Routine | None, store_param: str | None,
                 param_types: dict, is_duty: bool = False):
        self.t = tables
        self.routine = routine
        self.store_param = store_param   # Lean name of the store-typed param, if any
        self.param_types = param_types   # param name -> type text
        self.is_duty = is_duty           # typed in the duty monad: broadcasts, no `return`
        self.miss = False                # set when a span turns out to quote Lean
        # idents that rename inside this routine's body
        self.var_renames = {}
        if store_param:
            sym = None
            for sname, ssym in tables.struct_sym.items():
                if param_types.get(store_param, "").startswith(sname):
                    sym = ssym
            if sym:
                self.var_renames[store_param] = sym

    # -------- expression rendering: tree -> spans

    def expr(self, tree, depth=0, in_builder=False):
        out = []
        i = 0
        n = len(tree)
        while i < n:
            x = tree[i]
            if isinstance(x, str):
                # `some e` / `pure e` unwrap: ⊥ is the style's absent value
                if x in ("some", "pure"):
                    i += 1
                    continue
                # an anonymous constructor `.ctor args`
                if x == "." and i + 1 < n and isinstance(tree[i + 1], str) \
                        and tree[i + 1] in self.t.ctors:
                    args, j = self.collect_atoms(tree, i + 2)
                    out.extend(self.render_ctor(tree[i + 1], args))
                    i = j
                    continue
                # ident chains and applications
                if re.match(r"[^\W\d]", x, re.UNICODE) and x not in KEYWORDS:
                    spans, i = self.ident_chain(tree, i, depth, in_builder)
                    out.extend(spans)
                    continue
                if x == "↑":
                    i += 1
                    continue
                if x == "¬":
                    out.extend(sp_sym("¬"))
                    i += 1
                    continue
                if x == "←" and i + 1 < n:
                    out.extend([("space", " "), ("sym", "←"), ("space", " ")])
                    i += 1
                    continue
                if x in ("∧", "∨") :
                    if in_builder and depth == 0 and x == "∧":
                        out.extend([("sym", ","), ("space", " ")])
                    elif depth == 0:
                        out.extend([("space", " "), ("kw", "and" if x == "∧" else "or"),
                                    ("space", " ")])
                    else:
                        out.extend([("space", " "), ("sym", x), ("space", " ")])
                    i += 1
                    continue
                if x in KEYWORDS:
                    out.extend([("kw", x)])
                    i += 1
                    continue
                if re.match(r"\d", x):
                    out.append(("num", x))
                    # a numeral times an ident: `3 * Δ` -> 3Δ-style thin product
                    if i + 1 < n and tree[i + 1] == "*":
                        out.append(("space", "\u2009"))
                        i += 2
                        continue
                    i += 1
                    continue
                if x == "*":
                    out.extend([("space", " "), ("sym", "·"), ("space", " ")])
                    i += 1
                    continue
                if x == "-":
                    out.extend([("space", " "), ("sym", "−"), ("space", " ")])
                    i += 1
                    continue
                if x == "%":
                    out.extend([("space", " "), ("kw", "mod"), ("space", " ")])
                    i += 1
                    continue
                if x in INFIX or x in (",", ":", ";"):
                    if x == ",":
                        out.extend([("sym", ","), ("space", " ")])
                    else:
                        out.extend([("space", " "), ("sym", x), ("space", " ")])
                    i += 1
                    continue
                out.append(("sym", x))
                i += 1
                continue
            # groups
            if is_group(x, "{"):
                start = len(out)
                out.extend(self.builder(x["items"]))
                i = self.postfix(tree, i + 1, out, start)
                continue
            if is_group(x, "("):
                start = len(out)
                out.extend(self.strip_group(x["items"], depth, in_builder))
                i = self.postfix(tree, i + 1, out, start)
                continue
            if is_group(x, "["):
                out.append(("sym", "["))
                out.extend(self.expr(x["items"], depth + 1))
                out.append(("sym", "]"))
                i += 1
                continue
            i += 1
        return out

    def postfix(self, tree, i, out, start):
        """`.method` chains after a group: coercion noise, .max, .biUnion, .filterM…
        `start` marks where the receiver's spans begin inside `out`."""
        n = len(tree)
        while i + 1 < n and tree[i] == "." and isinstance(tree[i + 1], str):
            meth = tree[i + 1]
            if meth in ("toFinset", "run"):
                i += 2
                continue
            if meth == "toNat":
                # ⌊…⌋ when the receiver is a division: the paper's own floor
                recv = out[start:]
                txt = "".join(t for _k, t in recv if isinstance(t, str))
                if "/" in txt:
                    if recv and recv[0] == ("sym", "(") and recv[-1] == ("sym", ")"):
                        recv = recv[1:-1]
                    out[start:] = [("sym", "⌊")] + recv + [("sym", "⌋")]
                i += 2
                continue
            if meth == "isSome":
                out.extend([("space", " "), ("sym", "≠"), ("space", " "), ("sym", "⊥")])
                i += 2
                continue
            if meth == "get":
                i += 3 if i + 2 < n and isinstance(tree[i + 2], str) else 2
                continue
            if meth in ("max", "min"):
                out[start:] = [("id", meth)] + out[start:]
                i += 2
                continue
            if meth == "getD":
                i += 3 if i + 2 < n else 2  # drop the default argument atom
                continue
            if meth in ("biUnion", "filterM", "imageM"):
                args, j = self.collect_atoms(tree, i + 2)
                out[start:] = self.method_call(meth, out[start:], args)
                i = j
                continue
            break
        return i

    def strip_group(self, items, depth, in_builder):
        """A parenthesized group: strip `(e : T)` ascriptions and `(← e)` binds; the
        parens around a single atom drop."""
        # (← e) -> e
        if items and items[0] == "←":
            return self.expr(items[1:], depth, in_builder)
        # type ascription: top-level `:` -> keep the left half only
        for k, x in enumerate(items):
            if x == ":":
                items = items[:k]
                break
        if len(items) == 1:
            return self.expr(items, depth, in_builder=False)
        # a single application/chain with no top-level operator needs no parens
        if not any(isinstance(x, str) and (x in INFIX or x in (",", "|", ";")
                                           or x in ("∧", "∨", "¬", "∃", "∀", "*", "%"))
                   for x in items):
            return self.expr(items, depth, in_builder=False)
        inner = self.expr(items, depth + 1, in_builder=False)
        # a tuple or an operator expression keeps its parens
        return [("sym", "(")] + inner + [("sym", ")")]

    # -------- identifier chains, field access, calls

    BUILTINS = {"max": 2, "min": 2, "abs": 1, "Finset.range": 1}

    NOISE_METHODS = ("toNat", "toFinset", "isSome", "get", "getD", "max", "min",
                     "biUnion", "filterM", "imageM", "run", "mk")

    def ident_chain(self, tree, i, depth, in_builder):
        """Parse `a.b.c` (with bracket/paren interludes) starting at tree[i]."""
        n = len(tree)
        parts = [tree[i]]
        i += 1
        while i + 1 < n and tree[i] == "." and isinstance(tree[i + 1], str) \
                and re.match(r"[^\W\d]", tree[i + 1], re.UNICODE):
            # stop the chain where a call target is already resolved: `ghost .genesis`,
            # `S.liveTree .imageM`
            qname = ".".join(parts)
            if qname in self.BUILTINS or self.lookup_callable(qname):
                break
            if len(parts) > 1 and parts[-1] not in self.t.fields \
                    and self.lookup_dot(parts[-1]):
                break
            if tree[i + 1] in self.NOISE_METHODS:
                break
            parts.append(tree[i + 1])
            i += 2
        qname = ".".join(parts)
        spans = None
        last_fld = parts[-1]

        # `t_{s−1}`: a trailing-underscore name with a braced subscript, prose spelling
        if len(parts) == 1 and parts[0].endswith("_") and len(parts[0]) > 1 \
                and i < n and is_group(tree[i], "{"):
            return [("id", parts[0][:-1]),
                    ("sub", self.expr(tree[i]["items"]))], i + 1

        # Lean/Mathlib generics applied prefix-style: max a b -> max(a, b)
        if spans is None and qname in self.BUILTINS:
            args, j = self.collect_atoms(tree, i)
            if len(args) == 1 and len(args[0]) == 1 and is_group(args[0][0], "(") \
                    and any(x == "," for x in args[0][0]["items"]):
                args = split_top(args[0][0]["items"], ",")
            if args:
                name = snake(qname.split(".")[-1])
                vals = [self.render_atom(a) for a in args]
                spans = [("id", name), ("sym", "(")] + join_sp(vals, COMMA) + \
                    [("sym", ")")]
                i = j

        # known routine or def, fully qualified?
        if spans is None:
            hit = self.lookup_callable(qname)
            if hit:
                spans, i = self.render_call(hit, None, tree, i)

        # a function-typed parameter applies call-style: isProposer s i
        if spans is None and len(parts) == 1 \
                and "→" in self.param_types.get(parts[0], ""):
            args, j = self.collect_atoms(tree, i)
            if args:
                vals = [self.render_atom(a) for a in args]
                spans = [("id", snake(parts[0])), ("sym", "(")] + \
                    join_sp(vals, COMMA) + [("sym", ")")]
                i = j

        # dotted: a routine reachable by dot notation — `S.processGoldfishVote vote`
        if spans is None and len(parts) > 1 and parts[-1] not in self.t.fields:
            dot_hit = self.lookup_dot(parts[-1])
            if dot_hit:
                recv = self.render_var(parts[0])
                if len(parts) > 2:
                    recv = self.field_chain(recv, parts[1:-1])
                spans, i = self.render_call(dot_hit, recv, tree, i)

        # otherwise: a variable and its fields
        if spans is None:
            spans = self.field_chain(self.render_var(parts[0]), parts[1:])
            # a name written with its own parens — `w({…})`, `Σ.timestamp(x)` — keeps
            # them tight
            if i < n and is_group(tree[i], "("):
                spans = spans + [("sym", "(")] + \
                    self.expr(tree[i]["items"], depth + 1) + [("sym", ")")]
                i += 1
        # bracket group following the chain: the field's harvested access shape
        while i < n and is_group(tree[i], "["):
            shape = self.fields_shape(last_fld)
            inner = self.expr(tree[i]["items"], depth + 1)
            if shape == "call":
                spans = spans + [("sym", "(")] + inner + [("sym", ")")]
            else:
                spans = spans + [("sym", "[")] + inner + [("sym", "]")]
            i += 1
        # postfix noise on an ident chain: .isSome, .get h, .toNat, .max...
        while i + 1 < n and tree[i] == "." and isinstance(tree[i + 1], str):
            meth = tree[i + 1]
            if meth in ("toNat", "toFinset", "run"):
                i += 2
                continue
            if meth == "isSome":
                spans = spans + [("space", " "), ("sym", "≠"), ("space", " "), ("sym", "⊥")]
                i += 2
                continue
            if meth == "get":
                i += 3 if i + 2 < n and isinstance(tree[i + 2], str) else 2
                continue
            if meth in ("max", "min"):
                spans = [("id", meth), ("sym", "(")] + spans + [("sym", ")")]
                i += 2
                continue
            if meth == "getD":
                i += 3 if i + 2 < n else 2
                continue
            if meth in ("biUnion", "filterM", "imageM"):
                args, j = self.collect_atoms(tree, i + 2)
                spans = self.method_call(meth, spans, args)
                i = j
                continue
            # unknown method: a field after all
            spans = self.field_chain(spans, [meth])
            i += 2
        return spans, i

    def render_var(self, name):
        if name in self.var_renames:
            return [("id", self.var_renames[name])]
        # a `.ctor` anonymous constructor cannot reach here (leading dot is separate)
        if name in self.t.ctors and self.t.ctors[name][0]:
            return [("id", self.t.ctors[name][0].name)]
        # a paper-spelled routine name, in prose spans: set like the figures set it
        if name in self.t.paper_names:
            return [("fn", name)]
        # Lean-only vocabulary marks the span as code (consulted by the prose pass):
        # a camelCase name, or a Type/Namespace-looking one — not a paper spelling
        base = name.rstrip("'")  # a primed letter (`T'`, `S'`) is paper vocabulary
        if snake(name) != name:
            self.miss = True
        elif len(base) > 1 and base[0].isupper() and not is_greek(base) \
                and not is_greek(base[0]) and not SUBSCRIPT_ID.match(base) \
                and (any(c.islower() for c in base[1:]) or base.isupper()):
            # greek-initial names (`Δs`, `ηSG`) are paper vocabulary, not Lean types
            self.miss = True
        return [("id", snake(name))]

    def field_chain(self, base_spans, fields):
        spans = base_spans
        for fld in fields:
            sym = self.t.fields.get(fld)
            name = sym.name if sym else snake(fld)
            spans = spans + [("sym", "."), ("field", name)]
        return spans

    def fields_shape(self, fld):
        sym = self.t.fields.get(fld)
        if sym and sym.shape == "call":
            return "call"
        return "bracket"

    def lookup_callable(self, qname):
        if qname in self.t.routines:
            return self.t.routines[qname]
        if qname in self.t.defs:
            sym = self.t.defs[qname]
            if sym.shape in ("call", "subscript"):
                return sym
            return sym
        # unqualified tail: `ghost`, `goldfishScore` defined bare
        return None

    def lookup_dot(self, fld):
        """`S.processGoldfishVote` -> the routine Store.processGoldfishVote."""
        for qname, r in self.t.routines.items():
            if qname.split(".")[-1] == fld:
                # dot notation resolves on the receiver's type; the style has at most
                # one routine per tail name, so the tail is enough
                return r
        for qname, sym in self.t.defs.items():
            if "." in qname and qname.split(".")[-1] == fld and sym.shape == "call":
                return sym
        return None

    def collect_atoms(self, tree, i):
        """Argument atoms of an application, until a token that cannot start one."""
        args = []
        n = len(tree)
        while i < n:
            x = tree[i]
            if isinstance(x, str):
                if x == "." and i + 1 < n and isinstance(tree[i + 1], str):
                    if tree[i + 1] not in self.t.ctors:
                        break  # a `.method` postfix ends the argument list
                    # anonymous constructor `.genesis` as an argument
                    args.append([".", tree[i + 1]])
                    i += 2
                    continue
                if x == "fun":
                    # a trailing lambda extends to the end of the application
                    args.append(tree[i:])
                    i = n
                    break
                if x in KEYWORDS or x in INFIX or x in (",", ";", ":", "|", "¬", "∃", "∀"):
                    break
                if re.match(r"[\d]", x):
                    args.append([x])
                    i += 1
                    continue
                if re.match(r"[^\W\d]", x, re.UNICODE):
                    # an ident atom: swallow its dotted chain and trailing brackets
                    j = i + 1
                    while j + 1 < n and tree[j] == "." and isinstance(tree[j + 1], str):
                        j += 2
                    while j < n and is_group(tree[j], "["):
                        j += 1
                    args.append(tree[i:j])
                    i = j
                    continue
                break
            if is_group(x, "(") or is_group(x, "{"):
                args.append([x])
                i += 1
                continue
            break
        return args, i

    def render_atom(self, atom):
        if len(atom) == 2 and atom[0] == ".":
            return self.render_ctor(atom[1], [])
        # a lambda argument eta-folds to a partial call where it can
        if atom and (atom[0] == "fun" or
                     (len(atom) == 1 and is_group(atom[0], "(")
                      and atom[0]["items"][:1] == ["fun"])):
            body, _binder = self.fun_body(atom)
            if body is not None:
                return body
        # argument parens drop: the commas already delimit — but a tuple keeps its own
        if len(atom) == 1 and is_group(atom[0], "("):
            items = atom[0]["items"]
            if items and items[0] == "←":
                items = items[1:]
            for k, x in enumerate(items):
                if x == ":":
                    items = items[:k]
                    break
            if not any(x == "," for x in items):
                return self.expr(items)
            return self.strip_group(atom[0]["items"], 0, False)
        return self.expr(atom)

    def render_ctor(self, cname, args):
        sym, cparams = self.t.ctors.get(cname, (None, []))
        if sym and sym.shape == "plain":
            return [("id", sym.name)]
        if sym and sym.shape == "template":
            sub = dict(zip(sym.args, args))
            parts = []
            for a in sym.template:
                if a in sub:
                    parts.append(self.render_atom(sub[a]) if isinstance(sub[a], list)
                                 else sub[a])
                else:
                    parts.append([("sym", a)])
            return [("sym", "(")] + join_sp(parts, COMMA) + [("sym", ")")]
        if args:
            return [("sym", "(")] + join_sp([self.render_atom(a) for a in args], COMMA) \
                + [("sym", ")")]
        return [("id", snake(cname))]

    def render_call(self, target, recv_spans, tree, i):
        """Render a routine/def application. tree[i] is the first argument token."""
        args, i = self.collect_atoms(tree, i)
        # a prose span writes the call in paper form — `ghost(anchor, tree, …)` — so a
        # single parenthesized comma tuple is the argument list, not one argument
        if len(args) == 1 and len(args[0]) == 1 and is_group(args[0][0], "(") \
                and any(x == "," for x in args[0][0]["items"]):
            args = split_top(args[0][0]["items"], ",")
        if isinstance(target, Routine):
            spans = self.routine_call(target, recv_spans, args)
            return spans, i
        sym = target
        if sym.shape == "subscript":
            sub = self.render_atom(args[0]) if args else [("id", sym.args[0])]
            return [("id", sym.name), ("sub", sub)], i
        if sym.shape == "call":
            vals = [self.render_atom(a) for a in args]
            if recv_spans is not None:
                vals = [recv_spans] + vals
            kind = "fn" if sym.smallcaps else "id"
            # a bare mention with no arguments at all is the name, not a padded call —
            # `round` as a tuple field stays `round`
            if not vals:
                return [(kind, sym.name)], i
            arity = len(sym.args) if sym.args else None
            if arity and len(vals) < arity:
                vals += [[("sym", "·")]] * (arity - len(vals))
            return [(kind, sym.name), ("sym", "(")] + join_sp(vals, COMMA) \
                + [("sym", ")")], i
        return [("id", sym.name)], i

    def routine_call(self, r: Routine, recv_spans, args):
        """Match Lean args to the paper signature; hidden params disappear."""
        # the store-typed param, and each struct-typed param's paper symbol
        store_sym = None
        for pname, ptype in r.params:
            for sname, ssym in self.t.struct_sym.items():
                if ptype.startswith(sname):
                    store_sym = (pname, ssym)
        values = {}
        params = list(r.params)
        if recv_spans is not None and params:
            # dot notation binds the first param of the namespace's own type
            ns = r.lean_name.rsplit(".", 1)[0] if "." in r.lean_name else None
            recv_param = None
            for pname, ptype in params:
                if ns and ptype.startswith(ns):
                    recv_param = pname
                    break
            if recv_param is None:
                recv_param = params[0][0]
            values[recv_param] = recv_spans
            params = [(p, t) for p, t in params if p != recv_param]
        for (pname, _ptype), a in zip(params, args):
            values[pname] = self.render_atom(a)
        # show the cited slots only, in the paper's order; unfilled ones are ·
        shown = []
        used = set()
        for c in r.cite_args:
            if store_sym and c == store_sym[1]:
                shown.append(values.get(store_sym[0], [("id", store_sym[1])]))
                used.add(store_sym[0])
                continue
            hit = None
            for pname, _pt in r.params:
                if pname == c and pname not in used:
                    hit = pname
                    break
            if hit is None:
                for pname, _pt in r.params:
                    if pname in values and pname not in used \
                            and (not store_sym or pname != store_sym[0]):
                        hit = pname
                        break
            if hit is not None:
                used.add(hit)
                shown.append(values.get(hit, [("sym", "·")]))
            else:
                shown.append([("sym", "·")])
        return [("fn", r.paper_name), ("sym", "(")] + join_sp(shown, COMMA) + [("sym", ")")]

    # -------- set builders

    def builder(self, items):
        """{x ∈ s | p} / {x ∈ᴹ s | p} / {e} literals -> paper set notation."""
        # split at the top-level | (the separator, not cardinality bars)
        depth = 0
        sep = None
        for k, x in enumerate(items):
            if isinstance(x, str):
                if x == "|":
                    if depth == 0 and sep is None and k > 0:
                        sep = k
            # groups keep their own bars inside
        if sep is not None:
            left = [("∈" if t == "∈ᴹ" else t) if isinstance(t, str) else t
                    for t in items[:sep]]
            right = items[sep + 1:]
            lspans = self.expr(left, depth=1)
            rspans = self.expr(right, depth=0, in_builder=True)
            return [("sym", "{")] + lspans + [("space", " "), ("sym", ":"),
                                              ("space", " ")] + rspans + [("sym", "}")]
        inner = self.expr(items, depth=1)
        return [("sym", "{")] + inner + [("sym", "}")]

    def method_call(self, meth, recv_spans, args):
        if meth == "filterM":
            binder = None
            if recv_spans and recv_spans[0] == ("sym", "{") \
                    and len(recv_spans) > 1 and recv_spans[1][0] == "id":
                binder = recv_spans[1][1]
            pred = self.pred_spans(args[0], binder) if args else [("sym", "·")]
            # fuse into a builder when the receiver already is one
            if recv_spans and recv_spans[0] == ("sym", "{") and recv_spans[-1] == ("sym", "}"):
                return recv_spans[:-1] + [("sym", ","), ("space", " ")] + pred + [("sym", "}")]
            return [("sym", "{"), ("id", "x"), ("space", " "), ("sym", "∈"), ("space", " ")] \
                + recv_spans + [("space", " "), ("sym", ":"), ("space", " ")] + pred \
                + [("sym", "}")]
        if meth == "imageM":
            body, binder = self.fun_body(args[0]) if args else (None, "x")
            src = recv_spans
            if body is None:
                return recv_spans
            return [("sym", "{")] + body + [("space", " "), ("sym", ":"), ("space", " "),
                                            ("id", binder), ("space", " "), ("sym", "∈"),
                                            ("space", " ")] + src + [("sym", "}")]
        if meth == "biUnion":
            body, binder = self.fun_body(args[0]) if args else (None, "x")
            if body is None:
                return recv_spans
            src = recv_spans
            # fuse {B ∈ T : p}.biUnion -> ⋃{body : B ∈ T, p}
            if src and src[0] == ("sym", "{") and src[-1] == ("sym", "}"):
                inner = [(("sym", ",") if s == ("sym", ":") else s) for s in src[1:-1]]
                return [("sym", "⋃"), ("sym", "{")] + body + \
                    [("space", " "), ("sym", ":"), ("space", " ")] + inner + [("sym", "}")]
            return [("sym", "⋃"), ("sym", "{")] + body + \
                [("space", " "), ("sym", ":"), ("space", " "), ("id", binder),
                 ("space", " "), ("sym", "∈"), ("space", " ")] + src + [("sym", "}")]
        return recv_spans

    def pred_spans(self, atom, binder=None):
        """A predicate argument: an ident (-> name(binder)) or a fun."""
        body, _b = self.fun_body(atom)
        if body is not None:
            return body
        spans = self.render_atom(atom)
        if len(spans) == 1 and spans[0][0] in ("id", "fn"):
            arg = ("id", binder) if binder else ("sym", "·")
            return [spans[0], ("sym", "("), arg, ("sym", ")")]
        return spans

    def fun_body(self, atom):
        """`(fun x => e)` -> (rendered e with x free, x); eta-folds a trailing x."""
        items = atom
        if len(atom) == 1 and is_group(atom[0], "("):
            items = atom[0]["items"]
        if not items or items[0] != "fun":
            return None, None
        try:
            arrow = items.index("=>")
        except ValueError:
            return None, None
        binders = [t for t in items[1:arrow] if isinstance(t, str)]
        binder = binders[0] if binders else "x"
        body = items[arrow + 1:]
        # strip `do return e` / `pure (…)` wrappers, however nested
        changed = True
        while changed:
            changed = False
            while body and body[0] in ("do", "return", "pure"):
                body = body[1:]
                changed = True
            if len(body) == 1 and is_group(body[0], "(") and body[0]["items"]:
                inner = body[0]["items"]
                if inner[0] in ("do", "return", "pure") or \
                        (inner and isinstance(inner[-1], str) and inner[-1] == binder):
                    body = inner
                    changed = True
        # eta-fold: f a b x -> partial call
        if body and isinstance(body[-1], str) and body[-1] == binder and binder != "_":
            head = body[:-1]
            spans = self.expr(head + [])
            # the call renderer already pads missing args with · when arity is known;
            # rendering head alone yields f(a, b, ·) for a known callable
            return spans, binder
        return self.expr(body), binder


# ---------------------------------------------------------------- statement rules

def rewrite_statement(rw: Rewriter, st: Stmt, is_last: bool):
    """One logical Lean statement -> spans (or None to drop the line)."""
    text = st.text

    # `let mut S := S` — the shadow copy of a parameter
    m = re.fullmatch(r"let mut (\S+) := (\S+)", text)
    if m and m.group(1) == m.group(2):
        return None

    tree = tree_of(text)

    # peel `let` / `let mut`
    if tree and tree[0] == "let":
        tree = tree[1:]
        if tree and tree[0] == "mut":
            tree = tree[1:]

    # if _ : cond then / if hp : cond then  -> if cond then
    if tree and tree[0] == "if" and len(tree) > 2 and tree[2] == ":":
        tree = [tree[0]] + tree[3:]

    # for x in s do  |  for _ in [:e] do -> loop
    if tree and tree[0] == "for":
        if len(tree) > 3 and tree[1] == "_" and is_group(tree[3], "["):
            return sp_kw("loop")
        if len(tree) > 3 and tree[1] == "_" and tree[2] == "in":
            return sp_kw("loop")
        binder = tree[1]
        rest = tree[3:]
        if rest and rest[-1] == "do":
            rest = rest[:-1]
        if len(rest) == 1 and is_group(rest[0], "["):
            return sp_kw("loop")
        return [("kw", "for all"), ("space", " "), ("id", snake(binder)),
                ("space", " "), ("sym", "∈"), ("space", " ")] + rw.expr(rest) + \
            [("space", " "), ("kw", "do")]

    # broadcast m — the draft's own verb, a statement in the duty monad
    if tree and tree[0] == "broadcast" and rw.t.duty_monad:
        arg = tree[1:]
        if len(arg) == 1 and is_group(arg[0], "("):
            arg = arg[0]["items"]
        # a `Message.ctor x` wrapper strips: the paper broadcasts the object itself
        if len(arg) >= 3 and isinstance(arg[0], str) and arg[1] == ".":
            arg = arg[3:]
        return [("kw", "broadcast"), ("space", " ")] + rw.expr(arg)

    # return …
    if tree and tree[0] == "return":
        rest = tree[1:]
        if not rest:
            return sp_kw("return")
        # return ← call  -> the call as a statement
        if rest[0] == "←":
            return rw.expr(rest[1:])
        # return { state := …, send := … }
        if len(rest) == 1 and is_group(rest[0], "{"):
            duty = duty_result(rw, rest[0]["items"], is_last)
            if duty == "drop":
                return None
            if duty is not None:
                return duty
        # return of the store variable itself
        if len(rest) == 1 and isinstance(rest[0], str) and rest[0] in rw.var_renames:
            return None if is_last else sp_kw("return")
        # a duty's tail call carries no `return`: the draft's duties end on the call
        if rw.is_duty:
            return rw.expr(rest)
        # return f args… where f is a routine: the paper's call-with-return
        return [("kw", "return"), ("space", " ")] + rw.expr(rest)

    # define x(y) as e   from   x := fun y => e   (after let-peel)
    m_assign = None
    for k, x in enumerate(tree):
        if isinstance(x, str) and x in (":=", "←", "←ᵖ"):
            m_assign = k
            break
    if m_assign is not None:
        lhs = tree[:m_assign]
        op = tree[m_assign]
        rhs = tree[m_assign + 1:]
        # a `let x : T := e` type annotation drops
        for k, x in enumerate(lhs):
            if x == ":":
                lhs = lhs[:k]
                break
        if rhs and rhs[0] == "fun":
            body, binder = rw.fun_body(rhs)
            if body is not None:
                lhs_sp = rw.expr(lhs)
                if binder and binder != "_":
                    return [("kw", "define"), ("space", " ")] + lhs_sp + \
                        [("sym", "("), ("id", snake(binder)), ("sym", ")"),
                         ("space", " "), ("kw", "as"), ("space", " ")] + body
                return lhs_sp + [("space", " "), ("sym", "←"), ("space", " "),
                                 ("sym", "_"), ("space", " "), ("sym", "↦"),
                                 ("space", " ")] + body
        # X ← X ∪ {e}  ->  add e to X
        if len(rhs) >= 3:
            # find top-level ∪ with a singleton right side
            if rhs[-2:-1] == ["∪"] and is_group(rhs[-1], "{"):
                left = rhs[:-2]
                if tokens_equal(left, lhs):
                    elem = rw.expr(rhs[-1]["items"])
                    return [("kw", "add"), ("space", " ")] + elem + \
                        [("space", " "), ("kw", "to"), ("space", " ")] + rw.expr(lhs)
        # constructor: T.mk (f := e)…  ->  a t with x.f = e, …
        ctor = constructor_spans(rw, lhs, rhs)
        if ctor is not None:
            return ctor
        lhs_sp = rw.expr(lhs)
        arrow = "←ᵖ" if op == "←ᵖ" else "←"
        rhs_sp = rw.expr(rhs)
        return lhs_sp + [("space", " "), ("sym", arrow), ("space", " ")] + rhs_sp

    # a bare final expression of a plain def / do block: the figure's return
    if is_last and tree and tree[0] not in ("if", "else"):
        return [("kw", "return"), ("space", " ")] + rw.expr(tree)

    return rw.expr(tree)


def tokens_equal(a, b):
    return flat(a) == flat(b)


def duty_result(rw: Rewriter, items, is_last):
    """{ state := e, send := M } -> broadcast m; <state rendered as a statement>."""
    fields = split_fields(items)
    if set(fields) != {"state", "send"}:
        return None
    state = fields["state"]
    send = fields["send"]
    out = []
    # broadcasts
    if len(send) == 1 and is_group(send[0], "{"):
        for msg in split_top(send[0]["items"], ","):
            # strip a `Message.ctor x` wrapper: Qualified.ident applied to one atom
            if len(msg) >= 3 and isinstance(msg[0], str) and msg[1] == ".":
                msg = msg[3:]
            out += [("kw", "broadcast"), ("space", " ")] + rw.expr(msg) + \
                [("sym", ";"), ("space", " ")]
    elif not (len(send) == 1 and send[0] == "∅"):
        out += [("kw", "broadcast"), ("space", " ")] + rw.expr(send) + \
            [("sym", ";"), ("space", " ")]
    # the post-state
    if len(state) == 1 and isinstance(state[0], str) and state[0] in rw.var_renames:
        state_sp = []
    else:
        state_sp = rw.expr(state)
    if out and out[-2:] == [("sym", ";"), ("space", " ")] and not state_sp:
        out = out[:-2]
    if not out and not state_sp:
        return "drop" if is_last else sp_kw("return")
    if not out:
        return ([] if is_last else [("kw", "return"), ("space", " ")]) + state_sp
    return out + state_sp


def split_fields(items):
    """{ f := e, g := e' } -> {f: tokens, g: tokens}."""
    fields = {}
    for part in split_top(items, ","):
        if len(part) >= 2 and isinstance(part[0], str) and part[1] == ":=":
            fields[part[0]] = part[2:]
    return fields


def split_top(items, sep):
    out, cur = [], []
    for x in items:
        if isinstance(x, str) and x == sep:
            out.append(cur)
            cur = []
        else:
            cur.append(x)
    if cur:
        out.append(cur)
    return out


def constructor_spans(rw: Rewriter, lhs, rhs):
    """`B := T.mk (f := e)…` -> tuple or "a t with B.f = e, …"."""
    if len(rhs) < 3:
        return None
    head = rhs[0]
    if not (isinstance(head, str) and rhs[1] == "." and rhs[2] == "mk"):
        return None
    struct = head
    named = []
    for g in rhs[3:]:
        if not is_group(g, "("):
            return None
        fields = split_fields(g["items"])
        for f, v in fields.items():
            named.append((f, v))
    if not named:
        return None
    lhs_sp = rw.expr(lhs)
    if struct in rw.t.tuple_structs:
        vals = [rw.expr(v) for _f, v in named]
        return lhs_sp + [("space", " "), ("sym", "←"), ("space", " "), ("sym", "(")] + \
            join_sp(vals, COMMA) + [("sym", ")")]
    parts = []
    for f, v in named:
        sym = rw.t.fields.get(f)
        fname = sym.name if sym else snake(f)
        parts.append(lhs_sp + [("sym", "."), ("field", fname), ("space", " "),
                               ("sym", "="), ("space", " ")] + rw.expr(v))
    return lhs_sp + [("space", " "), ("sym", "←"), ("space", " "),
                     ("kw", "a"), ("space", " "), ("id", snake(struct).lower()),
                     ("space", " "), ("kw", "with"), ("space", " ")] + \
        join_sp(parts, COMMA)


# ---------------------------------------------------------------- routine -> figure lines

def routine_lines(tables: Tables, r: Routine, decl_src, store_param, param_types):
    """Render one figured routine into [(indent, spans, note)] lines."""
    sig, body = split_signature(decl_src)
    is_duty = bool(tables.duty_monad
                   and re.search(rf"\b{tables.duty_monad}\b", sig))
    rw = Rewriter(tables, r, store_param, param_types, is_duty=is_duty)
    stmts = statements_of(body)
    rendered = []
    for k, st in enumerate(stmts):
        is_last = (k == len(stmts) - 1)
        spans = rewrite_statement(rw, st, is_last)
        if spans is None:
            continue
        rendered.append((st, spans))
    # peephole: `X ← call` directly followed by `return {state := X, send := ∅}` was
    # already reduced by duty_result to `return X`; collapse the pair to the call
    lines = []
    idx = 0
    while idx < len(rendered):
        st, spans = rendered[idx]
        if idx + 1 < len(rendered):
            st2, spans2 = rendered[idx + 1]
            bound = bound_var(spans)
            if bound and spans2 is not None \
                    and st2.indent == st.indent and is_return_of(spans2, bound):
                spans = strip_binder(spans, bound)
                lines.append((st.indent, spans, st.note))
                idx += 2
                continue
        lines.append((st.indent, spans, st.note))
        idx += 1
    # the function header
    header = [("kw", "function"), ("space", " "), ("fn", r.paper_name), ("sym", "(")] + \
        join_sp([[("id", a)] for a in r.cite_args], COMMA) + [("sym", ")")]
    return [(-1, header, None)] + lines


def bound_var(spans):
    """spans of `X ← f(...)` -> X when X is a single fresh ident."""
    if len(spans) > 2 and spans[0][0] == "id" and spans[1] == ("space", " ") \
            and spans[2] == ("sym", "←"):
        return spans[0][1]
    return None


def is_return_of(spans, var):
    txt = [t for _k, t in spans if isinstance(t, str) and t.strip()]
    return txt == ["return", var] or txt == [var]


def strip_binder(spans, _var):
    return spans[4:]  # drop `X`, space, `←`, space


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


SUBSCRIPT_ID = re.compile(r"^([^\W\d])_(\w+)$", re.UNICODE)


def is_greek(text):
    try:
        return all(unicodedata.name(c).startswith("GREEK") for c in text)
    except ValueError:
        return False


def latex_ident(text, italic=True):
    """An identifier: 1-char base + _suffix subscripts; the rest literal. Greek
    letters stay upright, as the paper sets them."""
    if italic and is_greek(text):
        return esc(text)
    m = SUBSCRIPT_ID.match(text)
    wrap = (lambda s: r"\textit{" + s + "}") if italic else (lambda s: r"\textsf{" + s + "}")
    if m:
        base = esc(m.group(1)) if is_greek(m.group(1)) else wrap(esc(m.group(1)))
        return base + r"\textsubscript{" + wrap(esc(m.group(2))) + "}"
    return wrap(esc(text))


WORDY = {"kw", "id", "fn", "field", "num", "sub"}


def fix_spaces(spans):
    """Insert the spaces juxtaposition dropped: between words, after keywords, never
    before an opening paren of a call or after a dot."""
    out = []
    for span in spans:
        if out:
            lk, lt = out[-1]
            rk, rt = span[0], span[1]
            lword = lk in WORDY or (lk == "sym" and isinstance(lt, str) and lt in ")]}\u22a5\u2205\u230b")
            rword = rk in WORDY or (rk == "sym" and isinstance(rt, str) and rt in "\u00ac\u2203\u2200\u230a\u22c3\u22a5\u2205{")
            sep = False
            if lk == "space" or rk == "space" or rk == "sub":
                sep = False
            elif lk == "kw" or rk == "kw":
                sep = not (isinstance(rt, str) and rt in ",;()[]")
            elif lword and rword:
                sep = True
            # no space after a quantifier: math typesetting joins the binder tight
            if sep:
                # a numeral times a short symbol is a juxtaposed product: 2W, 4Δs
                thin = lk == "num" and rk == "id" and isinstance(rt, str) \
                    and (len(rt) == 1 or is_greek(rt[0]))
                out.append(("space", " " if thin else " "))
        out.append(span)
    return out


def latex_spans(spans):
    out = []
    for kind, text in fix_spaces(spans):
        if kind == "space":
            out.append(r"\," if text == "\u2009" else " ")
        elif kind == "kw":
            out.append(r"\textbf{" + esc(text) + "}")
        elif kind == "fn":
            out.append(r"\textsc{" + esc(text) + "}")
        elif kind == "id":
            out.append(latex_ident(text, italic=True))
        elif kind == "field":
            out.append(latex_ident(text, italic=False))
        elif kind == "num":
            out.append(esc(text))
        elif kind == "sub":
            out.append(r"\textsubscript{" + latex_spans(text) + "}")
        else:
            out.append(esc(text))
    return "".join(out)


def md_inline(s: str) -> str:
    """Markdown-lite inline: backtick spans to mono, ** to bold, the rest escaped.
    A bold span may contain code spans, so bold recurses first."""
    m = re.search(r"\*\*(.+?)\*\*", s, re.DOTALL)
    if m:
        return md_inline(s[:m.start()]) + r"\textbf{" + md_inline(m.group(1)) + "}" + \
            md_inline(s[m.end():])
    out = []
    parts = s.split("`")
    for idx, part in enumerate(parts):
        if idx % 2 == 1:
            out.append(r"\codett{" + esc(part) + "}")
        else:
            out.append(esc(part))
    return "".join(out)


def md_block(text: str, inline=None, display=None) -> str:
    """Markdown-lite block conversion of a module header or docstring. `display`, when
    given, sees each paragraph first and may claim it whole (a displayed line)."""
    if inline is None:
        inline = md_inline
    out = []
    lines = text.split("\n")
    i = 0
    n = len(lines)
    para: list[str] = []

    def flush():
        if para:
            joined = " ".join(para)
            para.clear()
            if display:
                d = display(joined)
                if d is not None:
                    out.append(d)
                    return
            out.append(inline(joined) + "\n")

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
            out.append(r"\subsection*{" + inline(m.group(2)) + "}")
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
                    out.append(" & ".join(inline(c) for c in r) + r" \\")
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
                        out.append(r"\item " + inline(" ".join(cur)))
                    cur = [t[2:]]
                elif t and lines[i].startswith(("  ", "\t")):
                    cur.append(t)
                elif not t:
                    break
                else:
                    break
                i += 1
            if cur:
                out.append(r"\item " + inline(" ".join(cur)))
            out.append(r"\end{itemize}")
            continue
        para.append(s)
        i += 1
    flush()
    return "\n".join(out)


# ------------------------------------------------------------- the `## Extract` prose

EXTRACT_HEADING = re.compile(r"Extract\b\s*(?:[—:–-]+\s*(.*))?$")

# a subtitle of the form `Definition (Title)`: rendered as the draft's definition
# environment, numbered by this script in document order
DEF_SUBTITLE = re.compile(r"Definition\s*(?:\((.*)\))?\s*$")


def split_sections(text: str):
    """A module header or docstring -> [(heading|None, body)], split at `## ` lines."""
    out = []
    heading = None
    buf: list[str] = []
    for line in text.split("\n"):
        if line.startswith("## "):
            out.append((heading, "\n".join(buf).strip("\n")))
            heading = line[3:].strip()
            buf = []
        else:
            buf.append(line)
    out.append((heading, "\n".join(buf).strip("\n")))
    return out


def extract_sections(text: str):
    """The document prose of a header/docstring: [(subtitle|None, body)] of the
    sections marked `## Extract`. Everything unmarked stays out of the PDF."""
    out = []
    for heading, body in split_sections(text):
        if heading is None:
            continue
        m = EXTRACT_HEADING.match(heading)
        if m and body:
            out.append((m.group(1) or None, body))
    return out


def has_extract_section(text: str) -> bool:
    """Whether a docstring carries an `## Extract` heading at all — the mark that makes
    a `def` figured, prose under the heading or not."""
    return any(h is not None and EXTRACT_HEADING.match(h)
               for h, _b in split_sections(text))


def prose_span(span: str, rw) -> str | None:
    """A backticked span set in the paper's typography, or None when it quotes Lean
    (binder keywords, camelCase or Type-looking names) and should stay mono."""
    toks = tokenize(span)
    if any(t in ("let", "fun", "do", "mut", ":=", "=>", "←ᵖ", "∈ᴹ", "sorry")
           for t in toks):
        return None
    rw.miss = False
    tree, _ = parse_group(toks)
    spans = rw.expr(tree)
    if rw.miss or not spans:
        return None
    return latex_spans(spans)


REF_RE = re.compile(r"\[(fig|def|eq):([A-Za-z0-9_.-]+)\]")
REF_WORD = {"fig": "Figure", "def": "Definition"}


def eq_span(t: Tables, key: str):
    """The raw opening span behind `[eq:key]`: the Lean name exactly, else a unique
    Lean-name tail (`[eq:q]` finds `Weights.q`), else a unique harvested paper symbol
    (`[eq:Q_target]` finds `ChainState.Qtarget`, whose span opens `Q_target(σ) = …`)."""
    if key in t.raw_spans:
        return t.raw_spans[key]
    hits = {v for k, v in t.raw_spans.items() if k.split(".")[-1] == key}
    if len(hits) == 1:
        return hits.pop()
    named = dict(t.defs)
    named.update(t.fields)
    hits = {t.raw_spans[k] for k, sym in named.items()
            if sym.name == key and k in t.raw_spans}
    if len(hits) == 1:
        return hits.pop()
    return None


def render_eq(key: str, rw) -> str:
    """`[eq:key]` renders the referenced declaration's own opening span — the formula
    is written once, at the definition site. A dangling key stays visible, in mono."""
    span = eq_span(rw.t, key)
    if span is None:
        return r"\codett{" + esc(f"[eq:{key}]??") + "}"
    styled = prose_span(span, rw)
    return styled if styled is not None else r"\codett{" + esc(span) + "}"


def resolve_refs(s: str, rw) -> str:
    """`[fig:Name]` / `[def:slug]` in plain prose become \\ref links — the prose never
    writes a generated number, so it cannot go stale; `[eq:name]` expands to the named
    declaration's harvested opening span."""
    out = []
    pos = 0
    for m in REF_RE.finditer(s):
        out.append(esc(s[pos:m.start()]))
        if m.group(1) == "eq":
            out.append(render_eq(m.group(2), rw))
        else:
            out.append(REF_WORD[m.group(1)] + r"~\ref{" + m.group(1) + ":" + m.group(2) + "}")
        pos = m.end()
    out.append(esc(s[pos:]))
    return "".join(out)


def prose_inline(s: str, rw) -> str:
    """md_inline, with code spans routed through the figure rewriter where they parse
    as spec vocabulary, and [fig:…]/[def:…] references resolved."""
    m = re.search(r"\*\*(.+?)\*\*", s, re.DOTALL)
    if m:
        return prose_inline(s[:m.start()], rw) + r"\textbf{" + \
            prose_inline(m.group(1), rw) + "}" + prose_inline(s[m.end():], rw)
    out = []
    parts = s.split("`")
    for idx, part in enumerate(parts):
        if idx % 2 == 1:
            styled = prose_span(part, rw)
            out.append(styled if styled is not None else r"\codett{" + esc(part) + "}")
        else:
            out.append(resolve_refs(part, rw))
    return "".join(out)


# a display paragraph: nothing but backticked spans and/or [eq:…] references
DISPLAY_PARA = re.compile(r"\s*(?:(?:`[^`]+`|\[eq:[A-Za-z0-9_.-]+\])\s*)+")
DISPLAY_ITEM = re.compile(r"`([^`]+)`|\[eq:([A-Za-z0-9_.-]+)\]")


def prose_display(s: str, rw):
    """A paragraph consisting only of spans/[eq:…] refs is a displayed line: centered,
    each item through the rewriter, items separated by quad space. Returns None when
    the paragraph is ordinary prose."""
    if not DISPLAY_PARA.fullmatch(s):
        return None
    items = []
    for span, key in DISPLAY_ITEM.findall(s):
        if key:
            items.append(render_eq(key, rw))
        else:
            styled = prose_span(span, rw)
            items.append(styled if styled is not None
                         else r"\codett{" + esc(span) + "}")
    return "\\begin{center}\n" + "\\quad\n".join(items) + "\n\\end{center}"


def prose_block(text: str, rw) -> str:
    """md_block with the paper-typography inline pass and the display-paragraph rule."""
    return md_block(text, inline=lambda s: prose_inline(s, rw),
                    display=lambda s: prose_display(s, rw))


def slug(title: str) -> str:
    return re.sub(r"-+", "-", re.sub(r"[^a-z0-9]", "-", title.lower())).strip("-")


def emit_sections(tex, sections, prose_rw):
    """Emit `## Extract` sections: plain prose, subsections, and definition blocks.
    Definitions are amsthm environments — LaTeX owns the numbering."""
    for subtitle, sec in sections:
        m = DEF_SUBTITLE.fullmatch(subtitle) if subtitle else None
        if m is not None:
            title = m.group(1) or ""
            head = r"\begin{definition}"
            if title:
                head += "[" + prose_inline(title, prose_rw) + "]"
                head += r"\label{def:" + slug(title) + "}"
            tex.append(head)
            tex.append(prose_block(sec, prose_rw))
            tex.append(r"\end{definition}")
            continue
        if subtitle:
            tex.append(r"\subsection*{" + prose_inline(subtitle, prose_rw) + "}")
        tex.append(prose_block(sec, prose_rw))


PREAMBLE = r"""\documentclass[10pt]{article}
\usepackage[a4paper,margin=2.6cm]{geometry}
\usepackage{fontspec}
\usepackage{xcolor}
\usepackage{amsthm}
\usepackage{float}
\usepackage[noend]{algpseudocode}
% symbol glyphs (⪯, ∈, ⊥, …) are absent from the text fonts: fall back to Latin
% Modern Math first, so they match the text's stroke weight; DejaVu is last resort
\directlua{luaotfload.add_fallback("symfall",
  {"latinmodern-math:mode=node;", "DejaVuSans:mode=node;"})}
\setmainfont{Latin Modern Roman}[RawFeature={fallback=symfall}]
\setsansfont{Latin Modern Sans}[RawFeature={fallback=symfall}]
\setmonofont{DejaVu Sans Mono}[Scale=0.82,RawFeature={fallback=symfall}]
\newcommand{\codett}[1]{\texttt{#1}}
\theoremstyle{definition}
\newtheorem{definition}{Definition}
% right-aligned small figure comments, the draft's own style
\algrenewcommand{\algorithmiccomment}[1]{\hfill{\scriptsize\color{black!55}$\triangleright$ #1}}
\setlength{\parindent}{0pt}
\setlength{\parskip}{4pt plus 1pt}
\usepackage[colorlinks=true, allcolors=blue!35!black]{hyperref}
\begin{document}
"""


def frontmatter(title: str):
    """Title page material: the document's provenance is machine-stamped."""
    try:
        commit = subprocess.run(
            ["git", "-C", str(HERE), "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True).stdout.strip() or "unknown"
        dirty = subprocess.run(
            ["git", "-C", str(HERE), "status", "--porcelain", "--", str(SRC)],
            capture_output=True, text=True).stdout.strip()
        if dirty:
            commit += " (spec has uncommitted changes)"
    except OSError:
        commit = "unknown"
    stamp = datetime.date.today().isoformat()
    return "\n".join([
        r"\begin{center}",
        r"{\LARGE " + esc(title) + r"}\\[2mm]",
        r"{\small generated from the Lean specification, \codett{" +
        esc(str(SRC.relative_to(HERE.parent))) + r"/}}\\[1mm]",
        r"{\small " + esc(commit) + r" · " + esc(stamp) + "}",
        r"\end{center}",
        r"\tableofcontents",
        r"\medskip",
    ])


def note_echoes(note: str, spans) -> bool:
    """A margin note that only repeats the rewritten code adds nothing: drop it."""
    def norm(s):
        return re.sub(r"[\W_]+", "", s, flags=re.UNICODE)

    code = norm("".join(t for _k, t in flatten_spans(spans)))
    n = norm(note)
    return bool(n) and (n in code or code in n)


def flatten_spans(spans):
    for k, t in spans:
        if k == "sub":
            yield from flatten_spans(t)
        elif isinstance(t, str):
            yield (k, t)


def classify_stmt(indent, spans):
    """(algorithmicx command, latex content) for one rewritten statement."""
    kinds = [(k, t) for k, t in spans if k != "space"]
    def strip_wrap(spans, lead, trail):
        s = list(spans)
        while s and (s[0][0] == "space" or (s[0][0] == "kw" and s[0][1] in lead)):
            s.pop(0)
        while s and (s[-1][0] == "space" or (s[-1][0] == "kw" and s[-1][1] in trail)):
            s.pop()
        return s
    if indent < 0:
        # the function header: \Function{name}{args}
        name = next(t for k, t in spans if k == "fn")
        depth = 0
        args = []
        for k, t in spans:
            if k == "sym" and t == "(":
                depth += 1
                if depth == 1:
                    continue
            if k == "sym" and t == ")":
                depth -= 1
                if depth == 0:
                    break
            if depth >= 1:
                args.append((k, t))
        return "function", (esc(name), latex_spans(args))
    if kinds and kinds[0] == ("kw", "else"):
        if len(kinds) > 1 and kinds[1] == ("kw", "if"):
            return "elsif", latex_spans(strip_wrap(spans, ("else", "if"), ("then",)))
        return "else", None
    if kinds and kinds[0] == ("kw", "if"):
        return "if", latex_spans(strip_wrap(spans, ("if",), ("then",)))
    if kinds and kinds[0] == ("kw", "for all"):
        return "forall", latex_spans(strip_wrap(spans, ("for all",), ("do",)))
    if kinds and kinds[0] == ("kw", "loop"):
        return "loop", None
    return "state", latex_spans(spans)


def render_figure(tex, stem, title, routines_lines, prose_rw):
    """One figure: a captioned, labelled float holding one algorithmic block whose
    line numbers are the rendering's own."""
    tex.append(r"\begin{figure}[H]")
    tex.append(r"\caption{" + esc(title) + r"}\label{fig:" + stem + "}")
    # the draft boxes each figure: a thin full frame around the algorithm block
    tex.append(r"\noindent\fbox{\begin{minipage}"
               r"{\dimexpr\linewidth-2\fboxsep-2\fboxrule\relax}")
    tex.append(r"\begin{algorithmic}[1]")
    stack = []  # open blocks: (indent, end command)
    first = True
    for lines in routines_lines:
        for indent, spans, note in lines:
            kind, content = classify_stmt(indent, spans)
            comment = ""
            trailing = None
            if note and not note_echoes(note, spans):
                rendered_note = r" \Comment{" + prose_inline(note, prose_rw) + "}"
                if len(note) > 55:
                    # a long note wraps badly mid-code: it gets its own unnumbered line
                    trailing = r"\Statex" + rendered_note
                else:
                    comment = rendered_note
            if kind == "function":
                while stack:
                    tex.append(stack.pop()[1])
                if not first:
                    tex.append(r"\Statex")
                first = False
                name, args = content
                tex.append(r"\Function{" + name + "}{" + args + "}" + comment)
                stack.append((-1, r"\EndFunction"))
                if trailing:
                    tex.append(trailing)
                continue
            if kind in ("else", "elsif"):
                # continue the innermost \If at this indent; do not close it
                while stack and stack[-1][0] > indent:
                    tex.append(stack.pop()[1])
                tex.append((r"\ElsIf{" + content + "}" if kind == "elsif" else r"\Else")
                           + comment)
                if trailing:
                    tex.append(trailing)
                continue
            while stack and stack[-1][0] >= indent:
                tex.append(stack.pop()[1])
            if kind == "if":
                tex.append(r"\If{" + content + "}" + comment)
                stack.append((indent, r"\EndIf"))
            elif kind == "forall":
                tex.append(r"\ForAll{" + content + "}" + comment)
                stack.append((indent, r"\EndFor"))
            elif kind == "loop":
                tex.append(r"\Loop" + comment)
                stack.append((indent, r"\EndLoop"))
            else:
                tex.append(r"\State " + content + comment)
            if trailing:
                tex.append(trailing)
    while stack:
        tex.append(stack.pop()[1])
    tex.append(r"\end{algorithmic}")
    tex.append(r"\end{minipage}}")
    tex.append(r"\end{figure}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-pdf", action="store_true")
    args = ap.parse_args()
    OUT.mkdir(exist_ok=True)

    # harvest over every file, vocabulary included. Files in a subdirectory render
    # before the files at SRC's root — the vocabulary a spec is written in terms of
    # precedes its algorithms; within a directory, config.ini's [order] decides.
    cfg = load_config()
    all_items = []
    parsed = []
    for path in ordered_files(cfg):
        header, items = parse_file(path)
        parsed.append((path, header, items))
        all_items.extend(items)
    tables = harvest(all_items)

    tex = [PREAMBLE, frontmatter(document_title(cfg))]
    for path, header, items in parsed:
        stem = path.stem
        title = stem
        body = header
        m = re.match(r"#\s+(.*)\n?", header)
        if m:
            title = m.group(1)
            body = header[m.end():]
        figured = []   # (routine, src, docstring), in the file's declaration order
        others = []    # (docstring, name)
        for doc, kind, name, src in items:
            r = tables.routines.get(name)
            if r and kind == "def":
                figured.append((r, src, doc))
            elif doc:
                others.append((doc, name))

        # a file with nothing marked `## Extract` emits no section
        header_secs = extract_sections(body)
        if not header_secs and not figured \
                and not any(extract_sections(doc) for doc, _n in others):
            continue

        prose_rw = Rewriter(tables, None, None, {})
        tex.append(r"\section{" + prose_inline(title, prose_rw) + "}")
        # the flip: only `## Extract` sections reach the PDF, in the paper's typography
        emit_sections(tex, header_secs, prose_rw)

        if figured:
            blocks = []
            for r, src, doc in figured:
                # a figured routine's `## Extract` prose leads its figure in, the way
                # the draft's prose introduces each figure
                emit_sections(tex, extract_sections(doc), prose_rw)
                sig, _b = split_signature(src)
                params = parse_params(sig)
                ptypes = {n: ty for n, ty, _a2 in params}
                store_param = None
                for n, ty, auto in params:
                    if auto:
                        continue
                    for sname in tables.struct_sym:
                        if ty.startswith(sname):
                            store_param = n
                blocks.append(routine_lines(tables, r, src, store_param, ptypes))
            render_figure(tex, stem, title, blocks, prose_rw)

        # `## Extract` prose of the file's other declarations follows the figure
        for doc, _name in others:
            emit_sections(tex, extract_sections(doc), prose_rw)
    tex.append(r"\end{document}")
    texfile = OUT / "dc.tex"
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
        print(f"wrote {OUT / 'dc.pdf'}")


if __name__ == "__main__":
    main()
