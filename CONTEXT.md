# Context

The durable record for this project: what was decided, what is proved, what failed. Read it
whole before starting a session; keep it current as work progresses. The rules for what goes
in it are in [CLAUDE.md](CLAUDE.md).

**Everything here is usable by anyone who has this repository and the Internet.** Anything
that needs Roberto's machine — where the earlier attempt sits on disk, which sibling checkouts
exist, what state they are in — goes in `CONTEXT_LOCAL.md` instead, which is **gitignored** and
so is absent from a fresh clone.

When you add an entry, put it in whichever of the two the reader could act on — and when either
would do, put it here, because this is the half git keeps.

Techniques go in a skill instead, under `.claude/skills/`.

## What this is

A Lean 4 formalization of *Height Filtering and Healing for a Simplex-Style Finality Variant*,
built section by section, auditing each part as it lands.

It is the **second** formalization of that paper. The first is complete and frozen, in a
different repository, and nothing from it is here — not its Lean, not copies of its notes. Its
conclusions are unverified from here, and possibly wrong. It is consulted on request; where to
read it is in the gitignored `REFERENCES_LOCAL.md`.

## 2026-08-13 — the project starts

### Why a separate repository, and not another attempt in the first one

The first attempt lives in a repository built for parallel attempts to coexist, so adding one
more directory there was the obvious move. Rejected. "Consulted only as reference" is a
property of *location*: in one working directory it is a rule that has to be remembered on
every grep and every edit, and outside it the earlier tree is not in the search path at all.
The failure being avoided is not a wrong edit — a hook can stop those — but absorbing the
earlier encoding's decisions as given, which is what the audit exists to prevent.

Costs accepted: its own Mathlib clone and cache, its own submodule pins, copies of the
tooling, and no shared `make`. All one-time.

Cost that remains, and now accepted rather than mitigated: a grep no longer finds that
something was already proved. That attempt's declaration index is the lookup that answers it,
and it is read where it lives rather than copied here.

### The paper: `latex-specs`, pinned

Submodule `latex-specs`, pinned at `e4375c5`. That is the same commit the first attempt tracks,
which keeps that attempt's paper ↔ Lean table usable when read: its rows carry `.tex` line
spans and printed numbers valid against one revision only.

The url is <https://github.com/saltiniroberto/decoupled-consensus-latex-specs>, which is
public: a recursive clone with terminal prompts disabled brings the paper down, so nothing
here needs credentials. It replaced a private Overleaf url on 2026-08-13; `e4375c5` exists in
both with the same hash, being the same history, so the pin did not move.

`ignore = untracked`, because building the paper leaves artefacts in the working tree.

**The pin is the gitlink**, mode `160000` in this repository's own tree — not anything in
`.gitmodules`, which records only path and url. So it moves with history, and `git bisect`
here moves the paper with it. To change it: check out the commit inside `latex-specs`, then
`git add latex-specs` in the parent.

**The paper is four commits ahead of the pin** as of 2026-08-13: `5853db7` folds erratum E3,
`ebca523` E4–E5, `799c608` E6, and `eb9a71c` adds a licence. Those errata look like the ones
that attempt recorded, folded upstream. Bumping the pin would change the `.tex` line
spans and printed numbers that `make cites` validates, so it is a decision of its own and has
not been taken.

The printed numbers come from `height_filter_healing.aux`, a LaTeX **build artefact** the
submodule does not carry. Build the paper to get them:

    cd latex-specs && latexmk -pdf height_filter_healing.tex

### The framework: `StsMultisetLog`, as a submodule

Submodule `deps/lean-sts`, url `https://github.com/saltiniroberto/lean-sts`, pinned at
`870c535` (`origin/main` at the time of writing), required by path in `lakefile.toml`. The
package offers five flavours and shares nothing between them; this project uses
`StsMultisetLog`.

Its toolchain (`v4.32.2`) and Mathlib rev (`v4.32.2`) already match this project's, so there is
one rev per dependency name across the build graph, which is what Lake requires. Bump all three
together.

A submodule rather than a Lake git `require`, so the revision this project builds against is
recorded in this repository's own history: `git submodule status` says which, and a `git bisect`
here moves it.

Verified at the time of writing, not assumed:

* `lake update` resolves — one Mathlib (`905b9581`), `sts-framework` as a `path` package, and
  Mathlib's post-update step fetched all 8,639 cache files.
* `lake build StsMultisetLog` builds the framework: 927 jobs, successful.
* A file importing `StsMultisetLog.Spec.Protocol` elaborates against this project's `lake env`.
  **The namespace is `Framework.StsMultisetLog`** and `Protocol` there takes four type
  arguments.
* `make check` passes, and `lake build` warns "no targets specified" until the `lean_lib` is
  uncommented. Expected, not a fault.

### Pushing to lean-sts is denied, not discouraged

`.claude/hooks/protect-lean-sts.py`, wired up by `.claude/settings.json` as a `PreToolUse` hook
on `Bash` and on the file-editing tools. It denies the tool call rather than warning about it,
because a push from inside a submodule goes to that submodule's remote.

Tested on eleven cases when written. Refused: `cd deps/lean-sts && git push`,
`git -C deps/lean-sts push`, a push naming the remote's URL, `git submodule foreach git push`,
and a bare `git push` with the shell's working directory inside the submodule. Allowed: a
push of this repository, a grep of the submodule, `pushd`, and a write to this project's own
files.

It also refuses writes under `deps/lean-sts/`, because the framework is a separate project and
should be changed in its own working copy.

Moving this project to a different framework revision needs no push: check out the commit in
`deps/lean-sts` and commit the submodule pointer here.

### No Lean yet, on instruction

`lakefile.toml` declares the two requires and has this project's `lean_lib` **commented out**: a
glob with no matching module makes `lake build` fail rather than do nothing. Uncomment it with
the first source file.

### The mapping and the citation check, wired up with everything absent

`MAPPING.md` and `mapping.html` exist and every row is absent, on instruction. `make cites` and
`make mapping` run; `make check` is now sorry, cites, build.

`MAPPING.md` was derived from that attempt's own table, keeping only the paper-level
columns — the `\label`, the printed number, and how often the paper's own proofs cite each
result — with every Lean cell `—` and every status `⛔ absent`. 5 figures, 49 definitions and
assumptions, 92 numbered results.

**The first attempt's judgements were deliberately not carried over.** Its table marks nine
results as absent *with a reason* — prose-only, or an opaque `ghost` walk, or a composition
this model does not carry. Every row here instead says "not yet stated", because an absent row
here means "not yet examined", and adopting the earlier call on what to skip is what this
project exists not to do.

The two scripts were re-pointed at this layout, with four changes each so they run before there
is any Lean; the changes are listed in a comment at the top of each file. The ones worth knowing:

* `check_citations.py` walks the whole repository minus `.git`, `.lake`, `deps` and
  `latex-specs`.
* `mapping_html.py` skips the figures column when `FigureDeps.lean` is absent, which is what
  makes the page producible with nothing formalized. That file is Lean and was not imported.
* A figure row may write `—` for its Lean file and declarations.

Measured after wiring up: **146 citations across 7 files, 0 problems**, against a paper built
with `make paper`. So every `\label` and every printed number in `MAPPING.md` agrees with
`height_filter_healing.aux` at the pinned revision.

Python note: `mapping_html.py`'s original used a multi-line expression inside an f-string, which
needs Python 3.12. It raised `SyntaxError: unterminated string literal` here. Compute the cell
before the f-string instead.

### The declaration index, generating an empty file

`tools/decl_index.lean` and `make index`. It writes `INDEX.tsv`: 0 declarations, with a header
saying why.

The mechanism is worth knowing, because it is what makes an empty index possible at all.
`collect` walks the **compiled environment** and keeps declarations whose defining module name
starts with `Decoupled`. A module reaches that environment only by being imported. So the file
imports `Lean` alone, with `import Decoupled.Analysis.Lemmas` and its two siblings commented
out, and the answer is necessarily zero. Uncommenting those lines with the first statements is
the whole change needed.

This is the one piece of Lean in the repository. It is tooling, not formalization: it is in no
`lean_lib`, so `lake build` never sees it, and `make index` runs it with `lake env lean`.

Adapted from the first attempt's copy in four ways, listed at the top of the file. Two worth
knowing: an empty row list writes no trailing blank line, and `suppressed` still drops a
`Schedule` binder because every declaration in that attempt carried one. Check that against this
project's own statements rather than assuming it fits.

### Nothing from the earlier attempt is copied in — decided the same day, after trying it

For part of 2026-08-13 a `Reference/` directory held five files copied from the earlier attempt:
its declaration index, its paper ↔ Lean table, its findings about the paper, its assumption
inventory, and a README. All five were removed, and what replaced them is a list of places to
read in the gitignored `REFERENCES_LOCAL.md`.

Two reasons, the second decisive.

The copies undid what the separate repository was for. The argument for a new repository was that
the earlier tree should be out of the search path, so its decisions are not absorbed as given.
Fifteen hundred lines of its conclusions sitting here put them back in the path of every grep.

And its conclusions may be **wrong**, not merely superseded. Roberto's judgement on
`FINDINGS.md`, and it generalizes: a file inside this repository reads as this project's
material, so an inherited error would be believed rather than checked. Re-deriving a conclusion
from the paper is cheaper than discovering later that one was mistaken.

What was kept, and why each is not a copied conclusion: the `lean-proof-idioms` skill, which is
technique rather than a claim about the paper; the two Python check scripts and the index
generator, which are tooling; and `MAPPING.md`'s **row set**, which is the paper's own list of
numbered results, with every judgement dropped.

Consequences in the tree: the hook lost its `Reference/` clause and is back to one job, the
lean-sts push and writes under that submodule. `check_citations.py`'s `SKIP` lost `Reference`,
and the `sorry` check lost its `--exclude-dir`.

The history was then squashed to a single commit, so the copies are not in this repository at
all — not in a tree, not in a commit. Read those files where they live; `REFERENCES_LOCAL.md`
says where.

## Next

1. Decide the module and namespace root, and land the first source file. `lakefile.toml`
   suggests lib `Decoupled`, modules `Decoupled.*`.
2. Read `StsMultisetLog/Spec/` and record here what it provides and what it leaves to the
   protocol. This is the layer where the first attempt's trouble concentrated — see
   its assumption inventory — so it is the first thing that wants auditing rather than
   assuming.
3. Section 1 of `height_filter_healing.tex`, and the audit method the rest will follow.
