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
tiebreak hash: Figures 1 and 2 read none of them. `m`, `StrictMajority` and `∼` are in, unused,
because each is part of a definition that is otherwise needed.

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

### `replayChain`, and why it is not Definition 24

Four of the lemmas quantify over the paper's `σ[B]`, the state derivation along the chain ending
at `B`. `Analysis/Lemmas.lean` defines `replayChain` as `ChainState.gen` at genesis and
`stateTransition` at each block after, so one failed check makes the chain `invalid`.

**Deliberately not offered as Definition 24 (`def:total-raw-replay`)**, which also carries slot
eligibility conditions this project has not modelled; `MAPPING.md` still records only that
definition's "a state or `invalid`" half. Move `replayChain` into the specification under that
number when the rest of Definition 24 lands. Parameterizing over it instead was rejected: an
unconstrained `replay` argument makes the lemmas false rather than unproved, and the fold of
`stateTransition` invents nothing.

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

## Next

1. **Settle where the chain replay lives**, because four of the nine lemmas quantify over it and
   nothing can be stated about them until it exists. The withdrawn pass had it as `replayChain`
   inside `Analysis/Lemmas.lean`; it belongs in `Spec` under Definition 24
   (`def:total-raw-replay`), whose slot eligibility conditions are also still absent.
2. **Then the lemmas, one at a time**, each its own commit with its own `MAPPING.md` row. Lemma 7
   is the one statable in full today; Lemmas 4, 6 and 8 are statable in part. Read the
   `lean-proof-idioms` skill before attempting a proof — all of them are over routines written in
   the paper's imperative shape, so `sorry` is not the only obstacle.
3. **Model what the rest wait on**, in the order that unblocks most:
   Definition 21 (`def:certificates`) is needed by four results, Definition 11 (`def:slashing`)
   by two, Definition 20 (`def:finality-action-state`) by three, and Assumption 1's `b` with
   `3b < W` by one. Each one landed turns a `def … : Prop` into a `theorem`, and each is a
   modelling decision to record here.
4. The parts of Lemmas 4, 6, 8 and 10 that are currently narrower than the paper's sentence, and
   Lemma 9, which needs a formulation decided before it can be written at all.
5. Read `StsMultisetLog/Spec/` and record here what it provides and what it leaves to the
   protocol. This is the layer where the first attempt's trouble concentrated — see
   its assumption inventory — so it wants auditing rather than assuming. Settling the signing
   question above is part of it.
6. Section 1 of `height_filter_healing.tex`, and the audit method the rest will follow.
7. Figures 3 to 5, and the definitions Sections 5 onward add.
