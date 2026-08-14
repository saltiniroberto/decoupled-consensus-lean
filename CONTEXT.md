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
that attempt recorded, folded upstream.

**2026-08-13, Roberto: the pin stays at `e4375c5`.** Not "not yet decided" — decided. So the
paper this project formalizes is `e4375c5` and nothing later, and the three errata folded
upstream are not in it. Two consequences to keep in mind:

* `\label`s, printed numbers and `.tex` line spans in `MAPPING.md` and in docstrings are
  against `e4375c5`, and `make cites` checks them against that revision's `.aux`. They stay
  valid.
* Where the pinned text is wrong and an upstream erratum fixes it, the fix is **not** in what
  this project reads. Record the discrepancy here when one is hit; do not bump the pin to
  resolve it.

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

`lakefile.toml` declared the two requires and had this project's `lean_lib` **commented out**: a
glob with no matching module makes `lake build` fail rather than do nothing.

Superseded the same day by the first source files — see "The layout: `lean/Spec`" below for
what the `lean_lib` became.

### The mapping and the citation check, wired up with everything absent

`MAPPING.md` and `mapping.html` were wired up with every row absent, on instruction. `make cites`
and `make mapping` run; `make check` is now sorry, cites, build.

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

### The declaration index

`tools/decl_index.lean` and `make index`, which write `INDEX.tsv`. It generated an empty file
until the first modules landed; it now has 69 rows.

The mechanism is what decides the row set. `collect` walks the **compiled environment** and
keeps declarations whose defining module name starts with `Decoupled`. A module reaches that
environment only by being imported, so the file's own import list is the coverage: add a line
per module root. The analysis imports are still commented out, there being no statements.

It is tooling, not formalization: it is in no `lean_lib`, so `lake build` never sees it, and
`make index` runs it with `lake env lean`. Its `import Spec` line was uncommented
when that module landed, and the index now has rows.

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

## 2026-08-13 — Figures 1 and 2, and the first source files

### The layout: `lean/Spec`, modules `Spec.…`

**Superseded once the same day.** It was first `lean/specs` with modules `Decoupled.Spec.…`,
so the files sat at `lean/specs/Decoupled/Spec/…` — `specs` and `Spec` both in the path, and
two directory levels below `srcDir`. Roberto asked for the files one level from `lean`, and
then for the module names to be changed to allow it. The current form:

    [[lean_lib]]
    name = "Spec"
    srcDir = "lean"
    globs = ["Spec", "Spec.+"]

so a module `Spec.Defs.Basic` is the file `lean/Spec/Defs/Basic.lean`.

`defaultTargets = ["Spec"]` is needed too: with a `lean_lib` declared but no default target,
`lake build` says "no targets specified" and builds nothing.

**Lake derives a module's path from its name and nothing else, and there is no remapping.**
Measured in a throwaway package, not assumed. With `srcDir = "src"` and a module `Root.Mid.Leaf`,
a file at `src/Leaf.lean` is not merely rejected but never looked for:

    error: no such file or directory
      file: …/src/Root/Mid

The same file with the module renamed flat to `Leaf` builds. So the directory under `srcDir`
always repeats the module root, and the only way to shorten the path is to shorten the name.
That is why the root is now `Spec` rather than `Decoupled.Spec`.

Two alternatives were rejected. A **lowercase root** `specs` keeps the directory literally
`lean/specs` and does build — verified, `✔ Built specs.Leaf` — but `import specs.Basic` is not
how Lean modules are spelled. **Flat modules** (`Basic`, `Pseudocode`, …) with `srcDir` at
`lean/specs` put the files exactly where asked, at the cost of no prefix at all: the module
namespace is global across every dependency, so an unprefixed `Basic` collides with anything a
package adds later, every new file has to be listed in `globs` by hand, and the index filter has
nothing to match.

**What the shorter root cost: there is no longer one module prefix over both halves.** The
analysis is expected to become a second `lean_lib` over the same `srcDir` with root `Analysis`,
so `lean/Analysis/…`; the two globs stay disjoint because the roots differ. But
`tools/decl_index.lean` used to filter on the single prefix `Decoupled`, and now filters on a
**list**, `modRoots`, currently `["Spec"]`. Adding a module root without adding it there is
silent — those declarations are simply absent from `INDEX.tsv`. The import list and `modRoots`
have to grow together, and the file says so.

Lean note while making that change: `modRoots.any (toString modName).startsWith` does not
elaborate. `String.startsWith` takes a pattern with a `Pattern.ForwardPattern` instance, so the
point-free form has type `(pat : ?m) → [inst] → Bool` and will not unify with `String → Bool`.
Write the lambda: `fun r => (toString modName).startsWith r`.

Declaration names were untouched by all of this. `namespace Decoupled` inside the files is
independent of the module name, so every declaration is still `Decoupled.…` and `INDEX.tsv` has
the same 81 rows, with only the module column changed.

**The two scripts pointed at a guessed path until the analysis landed.**
`tools/check_citations.py` had `LEMMAS = ROOT/"Decoupled"/"Analysis"/"Lemmas.lean"` and
`tools/mapping_html.py` the same three paths in `STATEMENT_FILES`. No such file could exist
under any layout this project adopted, and both treat a missing file as "no statements", so
both passed while checking nothing. Repointed at `lean/Analysis/` on 2026-08-13; `make cites`
now reports 8 statements rather than 0, which is what says the cross-check is live.

### `Spec/` holds only the figure translations; everything else is in `Spec/Defs/`

On instruction, 2026-08-13, third and last layout change of the day. The goal Roberto gave: a
reader looking for the pseudocode translations should find them in one directory with nothing
else in it. So `ls lean/Spec/*.lean` is now exactly the figures, and the two files the figures
are written in terms of moved down:

    lean/Spec.lean                            Spec
    lean/Spec/Fig1SlotReplay.lean             Spec.Fig1SlotReplay
    lean/Spec/Fig2AttestationProcessing.lean  Spec.Fig2AttestationProcessing
    lean/Spec/Defs/Basic.lean                 Spec.Defs.Basic
    lean/Spec/Defs/Notation.lean              Spec.Defs.Notation      (was Pseudocode.lean)

`Pseudocode.lean` became `Notation.lean` because `Defs/Pseudocode` reads as though it were a
rendering of the paper's pseudocode, which is what the figure files are; that file is the macro
layer and holds no protocol content.

Alternative rejected: a `Spec/Figures/` subdirectory with `Basic.lean` and the notation staying
at `Spec/`. It reaches the same arrangement from the other side, but `Spec.Figures.Fig1SlotReplay`
stutters, and removing the stutter means dropping either `Figures` or the `Fig<n>` prefix — and
the printed figure number in the file name was settled earlier the same day. Moving the two
non-figures is the change that leaves the figure names alone.

`Defs` rather than `Core`, `Base` or `Model`. The paper's own unit is "Definition N", so the name
needs no explaining, and the directory will not hold one file for long: Definitions 28 to 50 are
Section 6 onward. **Not** `Model`, which in a formalization reads as a semantic model.

The honest wrinkle: the notation layer is not a definition, so `Defs` covers it only loosely.
Accepted rather than adding a second one-file directory.

No source changed — imports, four prose paths, and the tables in `MAPPING.md`, `README.md` and
here. `INDEX.tsv` came back with the same 81 rows and only the module column different, which is
the check that nothing but the paths moved. `tools/decl_index.lean` needed nothing: `modRoots` is
`["Spec"]` and the root did not change.

### A figure file is named `Fig<n><Subject>`

On instruction, 2026-08-13: a file rendering one of the paper's five algorithm figures carries
the figure's printed number in its own name, not only in its module docstring. So
`SlotReplay.lean` became `Fig1SlotReplay.lean` and `AttestationProcessing.lean` became
`Fig2AttestationProcessing.lean`, with the module names following (`Spec.Fig1SlotReplay`).
The remaining three will be `Fig3Store`, `Fig4ForkChoiceState` and `Fig5RecoveryAction`.

The number leads so that a listing of `lean/Spec/` sorts in the paper's figure
order. Spellings rejected: `Figure1SlotReplay` (same order, longer for nothing);
`SlotReplayFig1` (sorts by subject, which is the order the figure number exists to override);
and a `Figures/` subdirectory holding `Fig1.lean`…`Fig5.lean`, which drops the subject from the
name entirely.

**A file that renders no figure takes no prefix.** `Basic.lean` holds the numbered definitions
the figures read and `Defs/Notation.lean` holds notation; each already says in its own docstring
that it is not a figure. The convention is stated in `Spec.lean`'s docstring and above
the figure table in `MAPPING.md`.

The number is the printed one at the pinned revision `e4375c5`. It is therefore the same kind of
fact as the numbers in the docstrings, and would move if the pin ever moved — which, per the
decision above, it does not.

### `alg:recovery-round` was not a label; `make cites` did not catch it

`Spec.lean` named Figure 5 `alg:recovery-round`. The paper's label is
`alg:recovery-action` (`recovery_core.tex:2083`, and `height_filter_healing.aux:171`).
`MAPPING.md` had it right, so the invented one was in one place only. Fixed 2026-08-13.

Worth knowing because `make cites` reported 0 problems with it in the tree. The text was
`Figures 3 (\`alg:store\`), 4 (\`alg:fork-choice-state\`) and 5 (\`alg:recovery-round\`)`, and
none of those three was checked. `check_citations.py`'s `PROSE` pattern is
`({KINDS}) (\d+) \(\`({LABEL})\`` with `KINDS` the **singular** words, so it needs the kind word
and a space immediately before the number. Two shapes defeat it, and the plural list uses both:

* the plural — `Figures 3` is `Figure` followed by `s`, not a space, so the first item of a list
  is unchecked as well as the later ones;
* the elided kind word — `and 5 (\`alg:recovery-round\`)` has no kind word at all.

Verified against the script, not assumed. The fix in `Spec.lean` was to write `Figure` out in
the singular on each item, which brings all three under the check. **Other citations in the tree
are in the unchecked shape** — five in `Basic.lean` (lines 124, 334, 457, 462) and the prose in
this file — and they are correct, merely invisible to `make cites`. Closing the blind spot means
either rewriting those to the singular form or teaching `PROSE` the plural and the elided item;
undecided as of 2026-08-13.

### What is rendered

Figures 1 (`alg:state-replay`) and 2 (`alg:attestation-processing`), and the numbered
definitions those two read: 3 (`def:validator-weights`), 4 (`def:height`),
5 (`def:block-chain`), 8 (`def:fg-message`), 9 (`def:valid-attestation-inclusion`),
13 (`def:chain-state`), 14 (`def:nonjustifiable`), 15 (`def:participation-state`), and the
"a state or `invalid`" of 24 (`def:total-raw-replay`). Four files under
`lean/Spec/`: `Fig2AttestationProcessing.lean` and `Fig1SlotReplay.lean`, with
`Defs/Basic.lean` and `Defs/Notation.lean` under them, plus `lean/Spec.lean` importing all four.

**Nothing is proved.** These are definitions; no numbered result is stated yet.

`make check` is green, `make index` reports 69 declarations, and `make cites` reports 222
citations in 14 files with 0 problems — so every printed number in the new docstrings agrees
with `height_filter_healing.aux` at the pinned revision.

### The notation layer is the one part taken from the first attempt

On instruction: the `do` semantics and the notation come from that attempt's
`Spec/Pseudocode.lean`, everything else was re-derived from the paper. What came across is
three `scoped` macros — `σ.f ← e`, `σ.f, σ.g ← e`, `σ.arr[i] ← e` — each expanding to a
reassignment of the enclosing block's `let mut`, and the decision that a routine is a plain
`def … : T := Id.run do` with no `function` command and no loop macro.

The macros claim **bare** identifiers as well as dotted ones, so `σ ← process_slots(σ, B.slot)`
is written with the same arrow as `σ.s ← σ.s + 1`. The cost is that `x ← someMonadicAction`
becomes unwritable while the namespace is open; nothing here wants it, and a mistake is a type
error rather than a silent one.

Checked by `#print` rather than assumed:

* `advance_height` expands with `h_j := σ.h` reading the **pre**-increment `h` and
  `nj := nonjustifiable σ.h σ.h_F` reading the **post**-increment one — which is what
  Definition 14 (`def:nonjustifiable`) and the figure's line order mean.
* `process_slots`' bare `while` elaborates to `forIn Lean.Loop.mk`, so no bound and no macro
  are needed to write it.

### Modelling decisions

**A block is its content.** `Blk` is an inductive type with `genesis` and `mk`, so two blocks
are equal exactly when their contents are — Definition 5 (`def:block-chain`)'s "we identify
the block with its root", made structural. Alternative rejected: an abstract type with
`parent`/`slot` accessors supplied by a class, which needs `ancestors` to carry a
`termination_by` and a hypothesis that a block's slot exceeds its parent's — and that slot
condition is a *check* in Definition 24 (`def:total-raw-replay`), so a block failing it must
stay representable.

**Measured, not inherited**: `deriving DecidableEq` does not reach the family. The error is

    None of the deriving handlers for class `DecidableEq` applied to
    `Blk`, `Attestation`, and `HeightPair`

and it is the nesting through `List` and `Option` that causes it, not the `mutual` — the two
are unavoidable together, since a block carries attestations and an attestation names blocks.
Confirmed by de-nesting: replacing `List (Attestation …)` with a mutual `AttList` and
`Option (Blk …)` with a mutual `OptBlk` makes the same `deriving` line succeed, with no axioms
at all.

**Resolved 2026-08-13. The procedure is written out, and nothing in the spec is
`noncomputable`.** The four `Classical.propDecidable` instances are gone. `Basic.lean` now
carries, under "Decidable equality, written out": six mutual `Bool` functions — `blkBeq`,
`attBeq`, `attListBeq`, `optBlkBeq`, `heightPairBeq`, `finalityPairBeq` — then six mutual
soundness theorems `… = true ↔ a = b`, then the four instances via `decidable_of_iff`.
Termination is inferred, with no `termination_by`. `attListBeq` and `optBlkBeq` carry the nesting
and are exactly what the deriving handler will not generate.

Equality between blocks was never undecidable. A block is a finite tree and comparing two is a
structural recursion; `propDecidable` has type `(a : Prop) → Decidable a` and asserts a decision
exists without providing one. So the old `noncomputable` traced to a missing deriving handler
plus a stopgap, not to anything about the model. Worth keeping in mind when reading "equality is
classical" in an older note: it is easy to misread as the stronger claim.

Alternative rejected: de-nest the datatype, which is three lines of `deriving` and no proofs.
`List` is what Definition 5's "finite canonically ordered set of signed attestations" reads as,
and `Option` is where `⊥` for `head` comes from, so that bends the model to suit the tooling.

**It runs.** `stateTransition` on `ChainState.gen` and a slot-1 block whose three attestations
target genesis at height 1 evaluates to `s=1 h=2 h_j=1 h_F=0 |P|=0`; a block that does not extend
the latest one evaluates to `invalid`; `decide (.genesis ⪯ b1)` is `true`. Executing the figures
is not a goal of this project, but it is now available as a check that a rendering is not vacuous.

**What it cost: `[DecidableEq Root]`.** A block carries a `claimedRoot`, so deciding block
equality decides root equality. The three `DecidableRel` instances and both figure files'
`variable` lines now assume it. No routine body changed.

**`by decide` still does not work, and did not before.** The mutual block compiles through
`blkBeq._mutual` over a `PSum` — well-founded, not structural — so `blkBeq .genesis .genesis` is
not definitionally `true`, and `by decide` reports "did not reduce to `isTrue` or `isFalse`".
Proofs go through the equation lemmas, `simp [blkBeq]`, which is what the soundness theorems do.
Nothing reduced under `propDecidable` either, so this is not a regression. De-nesting is the only
route that would buy reduction, and it was rejected above.

#### What used to force `noncomputable`, kept as the map of the dependency

Measured before the fix by stripping a routine down to one test at a time. Three instances forced
it, and each did so on its own:

| The test | The instance it needed |
| --- | --- |
| `σ.F ⪯ σ.J` | `instDecidableRelBlkPreceq` |
| `a.finalityPair = .commit σ.h_j σ.J` | `instDecidableEqFinalityPair` |
| `T = Th`, and `σ.T_h = ⊥` through `Option.decEq` | `instDecidableEqBlk` |

So `⪯` was never the only path, and "every routine reached by `⪯`" was too narrow: `processSlot`
uses no `⪯` at all, and it was `σ.T_h = ⊥` on line 739 of the figure. The mechanism is that
`Preceq` returns a `Prop`, so `if σ.F ⪯ σ.J then` elaborates to `ite`, whose `Decidable` argument
the elaborator supplies — printed explicitly it is
`@ite Nat (@Preceq Node Root a b) (@instDecidableRelBlkPreceq Node Root a b) 1 0`. The instance is
in the term, never in the source. `ancestors` was always clean and depends on no axioms: walking
the chain never compared blocks.

`advanceHeight` never needed the keyword at all — `if let some T := justify` is a pattern match,
not a comparison. Its keyword was dropped separately, before this work.

**`#print axioms` does not decide computability.** Choice inside erased proof terms costs nothing;
what blocks compilation is choice in *data* position, which is what `propDecidable` did — it built
the `Decidable` value itself out of choice. Whether Lean demands the keyword is the test, not the
axiom list. A live example survives the fix: `processSlots` and `stateTransition` still report
`Classical.choice` and both run, because core Lean's `while` does — `Lean.Loop.forIn` itself
depends on it. The other six routines report `[propext, Quot.sound]`.

**The two pairs are inductive types**, not pairs of `Option`s. Definition 8
(`def:fg-message`) admits `(h, T)`, `(h, ⊥)` and `(⊥, ⊥)` and not `(⊥, T)`; an inductive type
is how the missing combination is made unrepresentable.

**`TransitionResult`, not `Option (ChainState …)`.** `Option.none` already renders the paper's
`⊥` (absent target, height, head), and `invalid` is a different symbol. A `Coe` lets a routine
of that return type end with the paper's bare `return σ`.

**A signature is the `validator` field — a hole, left open deliberately.** Definition 5
(`def:block-chain`) has a block carry *signed* attestations and Definition 9
(`def:valid-attestation-inclusion`) asks each to verify under the named validator's key. Here
`Attestation` has a plain `validator` field, so a block naming a validator that never signed is
representable and `ValidInclusion` checks only membership in `V`. Nothing in Figures 1 and 2
depends on which shape is chosen; what closes it is the execution layer, where
`Framework.StsMultisetLog.SignedMsg` makes sending under `sender = p` the same thing as being
signed by `p`. **Decide it there rather than inheriting this.**

**Scope discipline in `Basic.lean`.** Only what the two figures read. `Params` carries `K` and
`Ddebt` and their two inequalities and nothing else — no `slotStart`, which belongs to
Definition 24 (`def:total-raw-replay`). No `assignedProposer`, no state-root function, no
tiebreak hash: Figures 1 and 2 read none of them. `m`, `StrictMajority`, `∼` and `≺` are in,
unused, because each is part of a definition that is otherwise needed. Measured 2026-08-13 by a
reference scan over the compiled environment: in the two figure files `⪯` appears 4 times and
`w(·)` 3 times, while `≺` and `∼` appear 0 times. `≺` joined that list when the nine lemmas were
withdrawn — Lemma 7's `T ≺ B` was its only user.

**Two deviations from the figures' own spelling**, both noted in the files:

* `σ.` is written out on every field write. The figure elides it inside a routine; recovering
  that would need the assignment macro to know which bare identifiers are fields of the state
  record, which it cannot without elaboration.
* `process_block` binds `A := σ.L` where the figure writes `A ← B.parent`. The two are the same
  block at that point — the preceding check has already returned `invalid` unless
  `B.parent = σ.L` — and `σ.L` is a block where `B.parent` is an `Option`.
* `process_slots`' second parameter is `target`, not the figure's `slot`, which would shadow
  the `Blk.slot` projection inside that one routine.

## 2026-08-13 — the analysis half

### The nine lemmas were written in one pass, then withdrawn

**Roberto's instruction, the same day: take them back out and go lemma by lemma.** The pass
below stated eight of the nine in one commit (`e42ef9b`); that commit is not reverted — the
`lean_lib` wiring and the tooling it repointed are kept — but the statements and `replayChain`
are removed, and `MAPPING.md`'s eight rows are back to `⛔ absent`.

Why the statements rather than the whole commit: the wiring is not what wants re-examining, and
tearing it out only to restore it with the first lemma would make those decisions twice. What
wants re-examining is each sentence against the paper, one at a time.

`replayChain` went with them, being a definition added only because the lemmas needed it. Where
it belongs is an open question — see below.

**Not reverted in the plain sense**: `git revert e42ef9b` was rejected because `4be9087` touches
two of the same files (`mapping.html`, `tools/mapping_html.py`), so both a revert and a
rebase-drop conflict there and risk re-breaking the `make mapping` fix. Removal by a forward
commit instead.

**The groundwork was kept, in `Analysis/Lemmas.lean`'s docstring**, because re-deriving it is the
expensive part: which of the nine are statable today, which wait on which numbered definition,
the line spans, and the two-shapes rule. Everything below stands as the record of that pass.

### The analysis is its own library, at `lean/Analysis`

On instruction. A second `lean_lib` named `Analysis`, same `srcDir = "lean"`, globs
`["Analysis", "Analysis.+"]`, so `Analysis.Lemmas` is `lean/Analysis/Lemmas.lean`.
`defaultTargets` is now `["Spec", "Analysis"]`.

Two libraries, not one, so there is no shared module prefix over the two halves. Consequences,
each already paid:

* `tools/decl_index.lean` filters on `modRoots`, now `["Spec", "Analysis"]`. Missing a root is
  silent — its declarations are simply absent from `INDEX.tsv`.
* `tools/check_citations.py` and `tools/mapping_html.py` were repointed from the guessed
  `Decoupled/Analysis/…` to `lean/Analysis/…`.

**A glob naming a root requires that root to exist as a file.** `globs = ["Analysis", …]` failed
with `Analysis: some modules have bad imports` until `lean/Analysis.lean` existed. That mirrors
`lean/Spec.lean`, so each half now has a root module that imports its own files.

### Nine lemmas of Sections 3 and 4 — the withdrawn pass, kept as the plan

Sections 3 (`sec:state-machine`, lines 535–980) and 4 (`sec:safety`, lines 981–1197) hold nine
lemmas, printed numbers 3 to 11. Theorem 5 (`thm:accountable-safety`) is in Section 4 too and is
not a lemma, so it is not among them and its row stays absent.

`sorry` became allowed the same day, so the proofs are `sorry` and `make check` fails until they
are discharged. But **a missing proof and an unwritable statement are different**, and both occur
here, so the file uses two shapes:

* `theorem … := sorry` where the paper's sentence is expressible in the current vocabulary.
  Lemmas 4, 6, 7, 8. This asserts the claim.
* `def … : Prop`, taking the absent notion as an argument, where it is not. Lemmas 3, 5, 10, 11.
  A `def` of type `Prop` asserts nothing. It must **not** be a `theorem`: over an unconstrained
  argument the claim would be false rather than unproved, and a `sorry` would hide that. Each
  becomes a `theorem` when its argument can be replaced by a real definition.

What is absent, and which lemma waits on it: the finality action state, Definition 20
(`def:finality-action-state`) — Lemmas 3, 4, 10; certificates and "finalized at height `h`",
Definition 21 (`def:certificates`) — Lemmas 5, 6, 10, 11; the slashing conditions E1 and E2,
Definition 11 (`def:slashing`) — Lemmas 5, 10; and Assumption 1's Byzantine weight `b` with
`3b < W` — Lemma 11. `Electorate` carries `V`, `w` and `w_pos` only, which is why the last is on
the list.

**Two the paper numbers are not on it.** State-height (Def. 6) and the current-height target
(Def. 7) are `σ.h` and `σ.T_h` of the replayed state, so Lemmas 7 and 8 needed no new
vocabulary. Worth knowing before someone models them separately.

**Four are narrower than the paper's sentence**, each saying so in its docstring: Lemma 4 covers
block post-states but not finality action states; Lemma 6 the increment half but not "requires a
certificate"; Lemma 8 the conflicting-branch half but not the vote-transfer half; Lemma 10 the
same post-state restriction as Lemma 4.

**Lemma 9 (`lem:target-bit-compression`) is not written down at all.** "All information needed
for the justification and progress rules is contained in the two Boolean arrays" is a sufficiency
claim with no formal shape in the paper; it is not a proposition about the model until someone
chooses what "needed" quantifies over. That is a modelling decision, not a transcription, so its
row stays absent and no declaration carries its name. One reading is recorded in the file for
whoever takes it on.

### `replayChain` was not a faithful `σ[B]` — corrected 2026-08-13

Four of the nine lemmas quantify over the paper's `σ[B]`. The withdrawn pass defined `replayChain`
in `Analysis/Lemmas.lean` as `ChainState.gen` at genesis and `stateTransition` at each block after,
and recorded that it "belongs in `Spec` under Definition 24 (`def:total-raw-replay`)".

**Both halves of that were wrong**, found when checking the paper rather than the note
(`height_filter_healing.tex:1555-1577`).

`σ[·]` is built by `derive_block_states` in **Figure 3** (`alg:store`), not by Definition 24.
Definition 24 governs when `state_transition` is called — the structural precheck, slot
eligibility, and that the transition is total — while the map itself is the figure's.

And the fold is not equivalent to it. A block enters `σ[·]` only when all of

    structural_precheck(x, B, B.parent) = valid          -- Definition 24's first part
    state_transition(σ[B.parent], B) ≠ invalid
    B's claimed post-state root = root(σ')               -- needs a state-root function

hold, over the objects of a store `S` whose clock admits the block's slot. `replayChain` checked
only the middle one, so it accepted a block whose `claimedRoot` disagrees with its own post-state —
which Figure 3 rejects. Had the lemmas stayed in with that definition, four of them would have been
stated over a replay the paper does not have.

**Consequence for the order of work.** Those four lemmas wait on Figure 3, on a state-root function
(`CONTEXT.md` already recorded that none is modelled), and on the store of Definitions 22 and 23.
They are not unblocked by any small addition, and there is nothing to put in `Spec` under
Definition 24 today beyond the `TransitionResult` already there. **The increment half of Lemma 6
is the only statement that needs nothing absent**, so it is the one that can land first. Five of
the nine quantify over `σ[B]`: Lemmas 3, 4, 7, 8 and 10.

Corrected within the hour: this entry first said Lemma 7 was the unblocked one. It is not — Lemma 7
names `σ[B]` twice, once for the chain ending at `B` and once for the post-state at `T`. Checked
against the withdrawn statements in `e42ef9b` rather than against the note.

### `MAPPING.md` and `mapping.html` gained one status, after briefly having two

`🔨 stated`: written down and not proved, with the note column saying what is outstanding. It did
not exist while the rule was "no `sorry`, and an unproved result stays a `def : Prop`".

**A second status, `📐 shape only`, was added and then removed the same day.** It distinguished a
`def … : Prop` over an unmodelled notion from a `theorem` whose proof is `sorry`. Roberto's
correction, and it is right: there is no conceptual or practical difference between them. Both
mean the paper's lemma is written down and not proved, and which Lean keyword a lemma gets is
forced by how much vocabulary exists rather than by anything achieved about the paper. The Lean
shapes still differ — that part is unavoidable, see `replayChain` above and the file's own
header — but a progress table should not have a column for it.

**The argument offered for keeping them apart was that `make check` fails on one and not the
other. That is a hole in the check, not a distinction.** A `def … : Prop` holds no `sorry`, so
the strict target passes it; green therefore means "no `sorry`", not "the paper's results are
proved". Four of the eight lemmas are invisible to it. `MAPPING.md`'s status column is the only
thing that answers the second question today. Closing the hole would mean a check that every
non-absent row names a sorry-free `theorem` — not written, and worth doing before the count of
`def … : Prop` results grows.

`tools/mapping_html.py` needed four changes for them: `STATUS_KEY`, the counts tuple, the badge
CSS in both colour schemes, and the filter buttons. A fifth was not about status: its declaration
regex matched `theorem` only, so the four `def … : Prop` rows came back as
`no Lean statement found for non-absent` until it accepted `def` as well.

With the statements in, the page read `0 proved · 0 partial · 8 stated · 84 absent`. After
the withdrawal it reads `0 proved · 0 partial · 0 stated · 92 absent`, and the two statuses stay
in the legend and in `mapping_html.py` for the first lemma that lands.

### The index generator's `suppressed` drops a `Prop` binder, and it misleads here

`INDEX.tsv`'s row for `lemFinalizedChain` lists one hypothesis where the declaration takes two:
`faultBound : Prop` is dropped, because `suppressed` discards any binder whose type prints as
`Prop`. That rule is inherited from the first attempt and was already flagged here as needing a
re-check; this is the first concrete case where it hides something a reader wants. Not fixed, so
that `INDEX.tsv` stays a search key rather than a signature — but do not read a parameterized
`def : Prop` row as complete.

### An editor tab resurrected a dead path, and nothing caught it

2026-08-13. `lean/specs/Decoupled/Spec/Fig2AttestationProcessing.lean` reappeared as an untracked
file, recreating a directory chain two layout moves out of date. Cause: a VS Code tab still open
on the old path, saved by autosave.

**Nothing in the build noticed, and could not have.** `srcDir` is `lean` with globs `Spec`,
`Spec.+`, `Analysis`, `Analysis.+`; that path is module `specs.Decoupled.Spec.…`, which matches
none of them, so Lake never read it. `make check` stayed green with a stale, uncompilable file in
the tree. Its content differed from the tracked file in exactly two lines, both the import and a
docstring path from before the moves, which is what made it easy to mistake for the real one.

Two fixes, both landed:

* `.vscode/settings.json` sets `files.autoSave: "off"` for this workspace. The hazard is a
  property of this repository rather than of one machine — the specification changed layout three
  times in one day, and `make index` and `make mapping` rewrite committed files — so a buffer
  holding a previous version is a normal state here. Gitignore `.vscode/` instead if that setting
  should stay personal.
* `make orphans`, in both `check` and `dev`: any `.lean` under `lean/` that is not `Spec.lean`,
  `Analysis.lean`, or under `Spec/` or `Analysis/` fails the target. Tested both ways — it passes
  on the clean tree and catches a planted file.

The near miss worth remembering: the same tab open on a file that still exists would have reverted
real work rather than adding a dead copy, silently, exactly as `CLAUDE.local.md`'s Commits section
warns.

## 2026-08-14 — Lemma 3 is proved, and the invariant it needed

### The paper's Lemma 3 is false over an arbitrary state

`lem:empty-slot-noop` says closing empty slots moves nothing but the cursor and, possibly, the
current-height target. Over an arbitrary `ChainState` that is plainly false: a state whose
progress tally already holds a quorum takes a height transition on the first `process_slot`, and a
height transition moves ten fields. The paper means it over states a block can actually produce,
with the reachability left in the prose.

So the Lean statement quantifies over block post-states — `BlockPostState σ`, an inductive
predicate with `ChainState.gen` at the base and one step per accepted `state_transition` — rather
than over an invented `Reachable`. That is what the paper's own hypothesis says, and the induction
then supplies the invariant.

### `Settled` has four conjuncts, and the paper states three

`Settled σ` (`Analysis/Proofs/SlotClosure.lean`) is the negation of each of Definition 18's three
branches, plus

    emptyTarget : σ.T_h = ⊥ → σ.Qtarget = ∅

The fourth is what makes the invariant survive `process_slot`, which writes `T_h ← L` and so flips
a condition the target branch relied on to stay blocked. It is true for a reason visible only in
Figure 2: line 778 is the only writer of a target bit, and it needs a target to be named.

The paper does not state it. Nothing here suggests the paper is wrong — its argument is about
states the protocol produces, where the fourth conjunct holds — but the Lean proof does not go
through without it.

### `Settled` is not preserved phase by phase, and that is the shape of the proof

    Settled σ ──process_slots──▸ Settled            closeSlots_of_settled
              ──process_block──▸ emptyTarget only   processBlock_emptyTarget
      ──process_height_events──▸ Settled            settled_processHeightEvents

Only `emptyTarget` is threaded end to end. `process_block` cannot preserve the other three: it is
where the target and progress tallies are built, so asking it to keep the quorum branches blocked
is asking attestations not to do their job. The last phase rebuilds them from `emptyTarget` alone.
`settled_stateTransition` composes the three, and `settled_of_blockPostState` is the induction,
with `settled_gen` at the base.

### Threshold positivity is a real hypothesis, and it is `PositiveWeight`

`q = ⌈2W/3⌉` is `(2 * W + 2) / 3` in `Nat`, which is `0` when the electorate is empty — and then
every set is a quorum, every branch fires, and genesis itself fails the invariant. So `0 < W` is
needed, as a class:

    class PositiveWeight (Node : Type) [Electorate Node] : Prop where
      posW : 0 < W Node

`Proofs/Weights.lean` also carries `PositiveWeight.ofFaultBound`, so a later file that has
Assumption 1's `3b < W` gets the instance without restating anything.

Named as a class, and named after what it says, following the first attempt. The machinery lemmas
take `(hq : 0 < q Node)` as a plain hypothesis instead, and only the two public entry points
(`settled_of_blockPostState`, `lemEmptySlotNoop`) require the class — so the machinery does not
depend on where the assumption is defined.

### Lean facts measured while proving it

Four, all in the imperative rendering, all now in the `lean-proof-idioms` skill:

* **`Id.run` has to be in the `simp only` set.** `simp only [processHeightEvents]` alone leaves
  the goals carrying a `pure (…).run` wrapper, and `split_ifs` cannot see the `if`s underneath.
  With `simp only [processHeightEvents, Id.run]` all six leaves of that routine's branch tree come
  out reachable.
* **A hand-written `if`-shaped bridge is not `rfl`.** Restating `process_height_events` as a
  readable nest of `if`s and proving the equation by `rfl` fails: the `if`s in the statement
  elaborate their own `Decidable` instances, and `Decidable` is data, so the two terms are not
  definitionally equal. Section 3's `rfl` bridge works for `Lean.Loop.forIn` because that one
  restates the *same* term at a different projection; this is a different term.
* **`split_ifs at h` discharges the contradictory branches itself.** A `h : … = .state σ'` against
  a routine that returns `invalid` on the failed check comes out with the invalid leaves already
  closed, so a bullet for them is an error ("no goals"). Same for `split at h` on the `match`.
* **Do not name `split_ifs` hypotheses positionally here.** Because some leaves are discharged,
  which name lands on which leaf is not stable, and a positional `with h1 h2 h3 …` names
  hypotheses that do not exist. `first | exact … (by assumption) | …` closes all six leaves and
  keeps working if the branch tree changes.

One more, in Figure 2: `⊥` is a `Bot (Option _)` instance rather than a constructor, so a
hypothesis `σ.T_h = ⊥` has to be restated as `σ.T_h = none` before `split` can reduce a `match`
against it. The coercion is definitional, so `have` accepts it with no proof.

### The first attempt was consulted, on instruction, and nothing was copied

Read before starting the assembly: its `Analysis/Proofs/Settled.lean`. Its `Settled` has the same
four conjuncts, and its `Settled.stateTransition` exists — so the step case was known to be
provable there, which lowered the risk of discovering a fifth conjunct halfway through. What
carried across is that much: the decomposition and the `PositiveWeight` name. Every lemma here is
re-derived and machine-checked, the definitions and the framework flavour being different.

### Where it stands

`make check` passes with no `sorry`. Lemma 3 is `lemEmptySlotNoop` (the record equation) and
`lemEmptySlotNoopFields` (the paper's field list, three lines from it), and `MAPPING.md` marks it
✅ proved. `Analysis/Proofs/SlotClosure.lean` holds 41 declarations: `BlockPostState`, `Settled`,
`closeSlots`, `actionState`, Lemma 3's own proof `emptySlotNoop`, and 36 supporting lemmas, each
either `Settled` machinery or a field lemma about a Figure 1 or Figure 2 routine.

Two things it leaves open, deliberately. `T_h` is pinned only up to "`σ.T_h` or `some σ.L`",
because pinning which one needs the induction to split `n = 0` from `n ≥ 1` and nothing yet needs
to know. And `actionState` is `processSlots`, sitting in `Analysis/Proofs/SlotClosure.lean`:
Definition 20 (`def:finality-action-state`) is not modelled, so the name is the paper's σ_a and
nothing more.

## 2026-08-14 — Lemma 4 is proved

`lemFinalizedBeforeJustified`, over a block post-state: `F ⪯ J ⪯ L` and `h_F ≤ h_j < h`. Proved in
the new `Analysis/Proofs/Ancestry.lean`, named for the phrase the paper's own proof uses for what
it establishes. `make check` passes with no `sorry`.

### `Chained` needs no threshold hypothesis, where `Settled` did

The invariant is `Chained`: the lemma's four claims plus

    targetOnChain : ∀ T, σ.T_h = some T → σ.J ⪯ T ∧ T ⪯ σ.L

and it takes **no** `PositiveWeight` and no quorum fact anywhere. The reason is worth keeping,
because it is the difference between this lemma and Lemma 3. `Settled` is the claim that the
height-event branches *stay blocked*, which fails outright when `q = 0`. `Chained` is preserved by
every branch whether or not the branch fires, so thresholds never enter.

Consequently every phase of `state_transition` preserves all five conjuncts, and there is no split
of the kind `Settled` needed.

### The fifth conjunct, again from the paper's prose

Needed because the target branch sets `J ← T_h`. The paper asserts it inside its own proof — "the
justification branch sets `J = T_h`, which lies on the current chain and already contains the
previous `J`" (lines 939–940) — and states it nowhere. It is true because `process_slot` is the
only routine that names a target and it writes `some σ.L`; `advance_height` writes `⊥`.

This is the second invariant here whose statement needs a conjunct the paper does not write. Worth
expecting a third.

### Definition 5's ancestry had no lemmas at all

`Preceq` is `a ∈ ancestors b` and nothing had been proved about it. Three facts were needed and are
now in `Ancestry.lean`, in namespace `Decoupled` rather than `Decoupled.Proofs` so that
`Preceq.refl` and `Preceq.trans` sit under the definition's own name and dot notation works:

* `Preceq.refl`, from `ancestors` putting the block at the head of its own list;
* `ancestors_subset`, "an ancestor's ancestors are ancestors", by structural recursion on the
  descendant — the content of `Preceq.trans`;
* `parent_preceq`, a block's parent precedes it, which is what turns `process_block`'s
  `parent = σ.L` check into an ancestry fact.

None needs `DecidableEq`: walking the chain compares nothing. Only deciding membership does, which
is what the existing `DecidableRel` instance is for.

### The first attempt was consulted first, on instruction, and the check paid off

Read before starting: its `Analysis/Proofs/Chained.lean` and the `INDEX.tsv` row for its
`lemFinalizedBeforeJustified`. Two things came out of it, neither of which was a proof.

**Its Lemma 4 carries no threshold class either.** That answered the question asked — whether more
assumptions were needed — before any Lean was written here, and the answer was no.

**Its `Chained` has the same five conjuncts**, including `targetOnChain` verbatim. That was already
predicted here from the paper's proof text and written into the `sorry`'s docstring, so the check
confirmed a prediction rather than supplying one.

What did not transfer: `Preceq.refl`'s proof there is `cases a <;> simp [Preceq, ancestors]`, which
works here too, but `parent_preceq`'s closing `simp` does not — it leaves
`p = p.mk s n a r ∨ p ∈ ancestors p`, and `List.mem_cons_of_mem _ (Preceq.refl p)` is what closes
it. Everything else was re-derived and compiled first time.

### Both of the lemma's subjects are in one theorem, and one earlier note here was wrong

The paper says "every reachable block post-state *and finality action state*", so
`lemFinalizedBeforeJustified` is a conjunction of the two, quantified over every `t` rather than the
one action slot Definition 20 fixes. The action-state half is three lines from
`Chained.processSlots`.

**Roberto, 2026-08-14: one theorem, not two.** It landed first as two declarations, following
Lemma 2, whose two sentences are two theorems. Wrong call here: Lemma 2 has two *sentences*, the
second needing an assumption the first does not, while Lemma 4 has one sentence with two subjects
and one set of assumptions. So `Lemmas.lean` carries exactly one theorem per such sentence, and
`Proofs/` keeps whatever intermediate pieces the proof wants.

The note this replaces said the action-state half would come "as a corollary of Lemma 3". That route works but
drags in `PositiveWeight`, which nothing else in this lemma needs. `Chained` survives slot closure
whatever the tallies hold, so the assumption never enters — the same distinction as above, in the
one place where it would have cost something.

## 2026-08-14 — Lemma 5 is proved, and the first vocabulary that no figure reads

`lemTargetUniqueness`, proved in `Analysis/Proofs/Certificates.lean`. Three modelling decisions
came with it, and they are the substance — the proof itself is eight lines and needed nothing new.

### `Analysis/Vocabulary.lean` — the paper's definitions that `Spec/` does not hold

Definition 11 (`def:slashing`) and Definition 21 (`def:certificates`) are the paper's numbered
definitions, but no figure reads them: `MAPPING.md` already listed the first under "stated but not
read by a figure". `Spec/` is the figure translations plus the definitions the figures read, so
these go in a new `Analysis/Vocabulary.lean` instead.

Two rules that file states about itself, both worth keeping:

* **Definitions only, no lemmas.** That file plus `Spec/` is then the whole surface to audit for
  what a statement in `Lemmas.lean` *means*.
* **Only the parts a landed statement uses.** Definition 11's E1 and Definition 21's progress and
  finality certificates are absent, because a declaration no statement mentions is an unaudited
  claim about what the paper means. Rejected the alternative of rendering each definition whole:
  it would leave declarations nothing reads, and this project has already had to answer "is
  anything unused in the tree?".

The name is taken from the first attempt, which has a file of the same name doing the same job.

### `BlockPostState` in place of `σ[·]` makes a certificate weaker, and that is the useful direction

Definition 21's JC asks for "the direct height-event invocation that set `(J, h_j) = (T, h)`", which
the paper reaches through `σ[·]`. `BlockPostState` stands in, and it admits more states than `σ[·]`
— it omits Figure 3's structural precheck and claimed-root check. So the rendered certificate is
*easier* to have than the paper's.

In a hypothesis, which is where Lemma 5 puts it, that makes the result stronger. Recorded in the
file because the direction flips if one of these definitions ever appears in a conclusion.

### `Conflicts` is Definition 5's, so it went to `Spec/`

The paper defines it inside Definition 5 (`def:block-chain`), at `height_filter_healing.tex:403`:
"Blocks are *compatible*, written `B ∼ C`, when `B ⪯ C` or `C ⪯ B`. Otherwise they conflict." So
`Conflicts a b := ¬ (a ∼ b)` sits beside `Compatible` in `Spec/Defs/Basic.lean` rather than in the
new vocabulary file, and `MAPPING.md`'s Definition 5 row now names it.

Checked before naming it, per the rule that a term from the paper counts as undefined until the
paper is seen to define it.

### The statement, and what the proof reads

The paper's "unless validators of total weight at least `2q - W` violate E2" is the **conclusion**,
not a hypothesis: the lemma returns the set, its weight, and each member's pair of attestations. So
no fault bound is assumed and none is needed — the claim is that the evidence exists, not that it is
impossible. The evidence is `IncludedOn` both chains, because a bare attestation value proves
nothing to a consumer that sees only blocks.

The proof is the paper's own two sentences: `quorumIntersection` (Lemma 2) gives `Q ∩ Q'` at weight
`2q - W`, and each member's two attestations make E2. Only the **first** clause of each certificate
is read, so this lemma says nothing about the invocation clause and cannot be cited for it — which
also means the `BlockPostState`-for-`σ[·]` substitution above does not affect this result at all.

Conflict enters only as distinctness, E2 asking for `T ≠ T'`, and conflicting blocks are distinct
because `⪯` is reflexive. The distinctness form is therefore strictly stronger than the paper's
sentence; it is not stated separately until something needs it.

## 2026-08-14 — Lemma 6 is proved, with a third invariant

`lemHeightProgression`, both halves of the paper's sentence: the increment, and "requires a
justification certificate or progress certificate". Proved in
`Analysis/Proofs/Certificates.lean`. `make check` passes with no `sorry`.

### Definition 21's progress certificate landed with it

`ProgressCertificate` joins `JustificationCertificate` in `Analysis/Vocabulary.lean`, which is that
file's rule working as intended: the part of a definition a statement needs lands with the
statement. The finality certificate is still absent, waiting on Lemmas 10 and 11.

Two decisions inside it:

* **`σ.J = σp.J` is what identifies the progress branch.** The paper says "advanced height without a
  new justification", and the justification branch always writes `J`, so the branch is pinned by
  what did *not* change rather than by naming the branch.
* **"Setting the progress bits" is not a third clause.** Which bits a state holds is a fact about
  the transition, and `process_attestation` is what sets them, so a clause asking for the bits as
  well would ask for the same thing twice. Recorded because it is a place where the rendering is
  deliberately shorter than the paper's sentence.

### "Every height transition" is quantified as one `state_transition`

A height transition can only happen at a height-event check, and there are two kinds: the block's
own, which is a transition's last phase, and one per closed empty slot. **Lemma 3 rules out the
second kind** from a block post-state, so every height transition is a block's, and quantifying over
`state_transition σp B = .state σ` with `σ.h ≠ σp.h` covers them all.

That is also why `PositiveWeight` is in the statement: with `q = 0` every empty slot advances the
height, so a block after two empty slots raises it by more than one and the first half is false. The
paper's proof cites Assumption 1 at exactly this point, "counted using the fixed validator weights".

Nothing renders that phrase separately: `Electorate` fixes `V` and `w`, and both certificates count
with them.

### `Witnessed`, the third invariant the paper does not state

A fired branch is a fact about **bits**; a certificate is a claim about **attestations**. Nothing
carried the one to the other, so `Analysis/Proofs/Witnessed.lean` is new and does:

    target   : a set target bit means an included attestation for exactly the current height and
               the named target
    progress : a set progress bit means an included attestation at the current height

Both are stated against `σ.L` rather than an endpoint parameter, and `Witnessed.of_fields` moves the
endpoint down the chain where a step needs it. The first attempt's equivalent is an 11-conjunct
`Witnessed` serving many lemmas; two conjuncts are what Lemma 6 needs, and adding the rest before
something reads them would be the guessing this project avoids.

**`Settled` is needed at exactly one step, `process_slot`.** That step can name a target while bits
are already set, which would leave old bits witnessing the wrong target. It cannot happen: naming a
target requires `T_h = ⊥`, and `Settled`'s fourth conjunct then makes the target tally empty. This
is the second time that conjunct — the one the paper never states — is what makes a proof go
through.

So all three invariants now in the project have a different reason to exist: `Settled` says the
branches stay blocked, `Chained` says the blocks and heights stay ordered, `Witnessed` says the bits
have provenance.

### Figure 2's two writers, isolated

`processAttestation_target_bit` and `processAttestation_progress_bit`: a bit is set only if it was
already set, or `a` is the attestation that set it and its height pair is what the writer's own
condition demands. Both proved by `simp only [processAttestation]; repeat' split at hb` and then
`simp_all [Function.update_apply]` with `tauto` behind it — the indexed write expands to
`Function.update`, which is what `Spec/Defs/Notation.lean`'s third macro produces.

### What the assembly needed beyond the invariant

* `advanceHeight_h`, `_L`, `_J_some`, `_h_j_some` — the field lemmas the branch analysis reads.
* `processHeightEvents_advance` — if the height moved, which branch moved it and with what. Phrased
  over `σ` rather than over the state the finality sub-step leaves, since those differ only in `F`
  and `h_F`.
* `processAttestations_chainFields`, `postBlock_fields` — the height the branch fired at is still the
  parent state's, which is Lemma 3 underneath and is where `PositiveWeight` enters.

Two tactic points worth keeping, both now in the skill: `cases hT : σ.T_h` has to come **before**
`split_ifs` (and only `hne` needs the rewrite afterwards, `cases` having already substituted in the
goal), and the leaves close with `exact` rather than `rw` because the goals carry a `pure` wrapper
that `rw` will not see through.

## 2026-08-14 — Lemma 7 is proved, with a fourth invariant

`lemHeightTargetFreshness`, proved in the new `Analysis/Proofs/Freshness.lean`. `make check`
passes with no `sorry`.

### It was on the "blocked" list, and only half of it was

The plan had Lemma 7 waiting on `σ[·]` as a map, because of "the chain's post-state at `T`". Two
things turned out to be true at once. The other claims need nothing absent, and the post-state claim
is expressible over `BlockPostState` — as an **existential**:

    ∃ σT, BlockPostState σT ∧ σT.L = T ∧ σT.h = σ.h

**That is weaker than the paper**, which has a definite description, "*the* chain's post-state at
`T`". `BlockPostState` does not pin uniqueness. Closing the gap needs either Figure 3's map or a
determinism lemma — block post-states agreeing on `L` agree everywhere, which is plausible since the
transition is a function but is not proved here. Written into the statement's docstring rather than
left for a reader to notice.

### The statement is shaped so all three of the paper's claims are visible

Quantified over each counted validator, so the first four conjuncts are exactly `Witnessed.target` —
the vote behind the bit names the stored target at this height — and the last two are the paper's
`≺ B` and the post-state claim. That makes the new content of this lemma exactly the part that is
outstanding.

### `Fresh` is a fourth invariant, and it did *not* go into `Witnessed`

The plan when the statement landed said the proof would extend `Witnessed` with a `fresh` conjunct,
following the first attempt. **That was wrong, and the reason is worth keeping.** `Witnessed` is
preserved step by step, `process_slot` included. Strictness is not: `process_slot` writes
`T_h ← some σ.L`, so immediately after that write the target *is* the latest block. It becomes strict
again only because `process_block` moves `L` to the child.

So this invariant holds of block post-states and of nothing smaller, and its induction is over
`BlockPostState` with a whole transition as the step — the way `Chained` is proved, not the way
`Settled` is. Merging it into `Witnessed` would have forced `Witnessed`'s per-step lemmas to state
something false of their intermediate states.

`Fresh` therefore lives in its own file and carries the two claims that hold **unconditionally**:

    onChain : ∀ T, σ.T_h = some T → T ⪯ σ.L
    anchor  : ∀ T, σ.T_h = some T → ∃ σT, BlockPostState σT ∧ σT.L = T ∧ σT.h = σ.h

### `σ[·]` was not needed after all: a block determines its post-state

The gap left when Lemma 7 first landed — an existential where the paper has a definite description —
is closed, and **not** by rendering Figure 3. `Analysis/Proofs/Determinism.lean` proves

    BlockPostState σ → BlockPostState σ' → σ.L = σ'.L → σ = σ'

by structural recursion on the **block**, not on the derivation: two derivations for one block may
have different shapes, and it is the block that pins the state. `state_transition` is a function and
`process_block` checks `B.parent = some σ.L`, so a block's post-state is fixed by its parent's, down
to genesis — where `ChainState.gen` is the only post-state, every step's block having a parent.

So Lemma 7's last claim is now the paper's: `T` has a post-state, and every post-state of `T` is at
this height. `Fresh.anchorAll` is the two-line bridge from the invariant's existential.

**The correction this forces to an earlier entry**: the plan listed `σ[·]` as blocking any lemma that
reaches a named earlier block's state. Too pessimistic. Figure 3 is needed for what a *store*
accepts; it is not needed to name a block's state. `Lemmas.lean`'s own table said the same and is
corrected too.

Four `L` lemmas came with it — `processSlot_L`, `closeSlots_L`, `processSlots_L`, `stateTransition_L`
— all without `PositiveWeight`. Lemma 3's record equation would have given them at the cost of an
assumption this argument does not otherwise need, and `Freshness.lean`'s own `processSlots_L`, which
did carry it, is deleted in favour of these.

### Strictness is false at genesis, and that is why it sits outside the invariant

At genesis `T_h = some genesis` and `L = genesis`, so `T ≺ L` fails. Every other block post-state is
the result of a transition, where the block phase has already moved `L` past the target, so
strictness holds there with no hypothesis at all.

`prec_of_target` therefore takes `σ.Qtarget.Nonempty` and uses it in the genesis case only — no bit
is set there, which is exactly what Lemma 7's own hypothesis rules out. Keeping `onChain` non-strict
is what lets genesis into the invariant, and the strict version is recovered where it is true.

### What the proof needed besides

* **Strict ancestry**, absent until now: `parent_prec` and `Preceq.trans_prec`, both from counting —
  `ancestors` of a child is one longer than its parent's, so no antisymmetry lemma and no `sizeOf`
  argument is needed. `ancestors_length_le_of_preceq` and `..._lt_of_prec` are the two counting
  lemmas, in `Analysis/Proofs/Ancestry.lean` with the rest of Definition 5.
* **`processHeightEvents_of_target`** — the complement of `processHeightEvents_advance`: if `T_h` is
  still filled after the check then no branch fired, because `advance_height` always clears it, so
  the height, the latest block and the target are all unchanged. The two lemmas together cover the
  check.
* **`processBlock_parent`** — the parent check as a fact about the block. Three proofs now derive it,
  so it is a lemma in `Analysis/Proofs/SlotClosure.lean` rather than four repeated lines.
* `processAttestations_chainFields` moved from `Certificates.lean` to `Ancestry.lean`, beside its
  single-step version, so that `Freshness.lean` can read it without an import cycle.

## 2026-08-15 — `postState` as a function, and Lemma 7 restated over it

`postState : Blk → TransitionResult` (`Analysis/Proofs/SlotClosure.lean`) replays a block's own
chain. It is not `σ[·]`: Figure 3 admits a block only after three further checks, none of them
modelled, so this returns a state for blocks a store would reject. Its docstring lists them.

`Analysis/Proofs/Determinism.lean` relates it to `BlockPostState` in both directions:

    blockPostState_of_postState : postState B = .state σ → BlockPostState σ
    postState_of_blockPostState : BlockPostState σ → postState σ.L = .state σ

The first is structural recursion on the block, the second induction on the derivation. With them a
proof carried out over the predicate can be stated over the function, and Lemma 7's post-state claim
becomes one equation with nothing quantified over:

    (postState T).map ChainState.h = some σ.h

Read aloud: the height of the post-state at `T` is `σ.h`. `postState` is a function of the block, so
the state named is *the* post-state — the definite description no longer needs `postState_unique` at
the use site, and `Fresh.anchorAll` is replaced by `Fresh.anchorPost`. `postState_unique` keeps its
own proof and is now cited by nothing; it is a second route to the same fact and worth keeping.

`TransitionResult.map` (`Spec/Defs/Basic.lean`) reads a field of the state a result carries, `none`
on `invalid`, and exists for exactly this: it lets a statement speak about that state without binding
it. Being an equation against `some` it also carries "the replay did not fail", so the claim is one
conjunct rather than two. Any other field goes the same way — `.map ChainState.L` — so no per-field
accessor is needed. `TransitionResult.toOption` is `map id`, kept for the `Option` API and for
`toOption_eq_some`.

**Two forms tried and rejected first, both on 2026-08-15, both equivalent to the above:**

    ∃ σT, postState T = .state σT ∧ σT.h = σ.h
    postState T ≠ invalid ∧ ∀ σT, postState T = .state σT → σT.h = σ.h

The first reads as "there is some state" where the paper says "the". The second fixes that but still
binds `σT`, which a reader then has to carry through the rest of the sentence; and its first
conjunct cannot be dropped, since without it the `∀` is vacuously true. Roberto, on both: the state
should not have to be quantified over at all for the statement to be readable.

Lemma 7's hypothesis changed with it, from `BlockPostState σ` to `postState B = .state σ`. The two
are interderivable by the bridges above, and the second is nearer the paper's "on a chain ending at
`B`", which names the block.

### `TransitionResult.get`, and why it is not in the statement

`Spec/Defs/Basic.lean` gained `TransitionResult.get`, the `Option.get` shape: the state a result
carries, given `r ≠ invalid`. Lean generates no accessor for one constructor's field of a
two-constructor inductive, so a term naming that state otherwise needs a `match`.

It is deliberately **not** used in Lemma 7. `r.get h` mentions `h`, whose type mentions `r`, so
rewriting `r` afterwards fails with "motive is not type correct" — and this development rewrites
states constantly. A statement wanting the state takes it as a parameter with `r = .state σ` as a
hypothesis. `get` is for a definition that must name the state in a term.

Two Lean facts found while doing it, both cheap to rediscover but easy to misdiagnose:

* `∧` is non-dependent, so a conjunct cannot use the proof asserted by the conjunct beside it.
  `postState T ≠ invalid ∧ ((postState T).get ‹_›).h = σ.h` cannot be written; the dependent form
  `∃ h : postState T ≠ invalid, ((postState T).get h).h = σ.h` can, and is equivalent to the `∃ σT`
  shape above.
* `invalid` is a scoped notation, so its token cannot be an alternative name: `cases r with
  | invalid => …` does not parse. Use positional bullets, or `rcases h : r with ⟨σ⟩ | _` when the
  equation is needed.

## Next

1. **The lemmas, one at a time**, each its own commit with its own `MAPPING.md` row. Of what
   is left of Sections 3 and 4, Lemma 8 looks statable over two block post-states; Lemmas 10 and 11
   wait on absent definitions, and Lemma 9 on a formulation. Read the `lean-proof-idioms` skill
   before attempting a proof — all of them are over routines written in the paper's imperative
   shape, so `sorry` is not the only obstacle.
2. **Model what the rest wait on**, in the order that unblocks most: Definition 21's finality
   certificate for Lemmas 10 and 11, Definition 11 (`def:slashing`)'s E1 for Lemma 10, and
   Assumption 1's `b` with `3b < W` for Lemma 11. Each lands in `Analysis/Vocabulary.lean` with the
   statement that needs it, not before, and each is a modelling decision to record here.
3. **Lemma 9's formulation**, which has to be decided before it can be written at all, and whatever
   Lemmas 8 and 10 turn out to state more narrowly than the paper's sentence. Every statement landed
   so far now covers its sentence in full.
4. Read `StsMultisetLog/Spec/` and record here what it provides and what it leaves to the
   protocol. This is the layer where the first attempt's trouble concentrated — see
   its assumption inventory — so it wants auditing rather than assuming. Settling the signing
   question above is part of it.
5. Section 1 of `height_filter_healing.tex`, and the audit method the rest will follow.
6. Figures 3 to 5, and the definitions Sections 5 onward add.
