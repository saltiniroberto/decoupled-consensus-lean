# decoupled-consensus-lean

A formalization of `consensus-1.pdf` — a human-controlled draft of a Simplex-style finality
protocol — in Lean 4, as `lean/Spec/Consensus1/`, plus the extractor under `extract/` that
renders the Lean back into a document shaped like the draft.

@CLAUDE.local.md

The line above pulls in this checkout's own rules, which are gitignored. If the file is
absent, as in a fresh clone, the import is a no-op.

## Correctness is the contract

Roberto, 2026-08-19 (and unchanged through the 2026-08-24 narrowing). What matters is that
every definition is correct, and Roberto is the judge of what correct means. Practically:

- **Strictly reactive.** Semantics change only on Roberto's explicit call, and correctness
  work happens where he points. No uninvited correctness audits.
- **`consensus-1.pdf`** is the draft being rendered: a local file at the repository root,
  **never committed** — no PDF spec is. It has no stable labels or line numbers and is
  under revision, so nothing cites it in a checked sense; a docstring saying "Definition 1
  of the draft" names the draft's numbering as of the date the docstring records, and the
  docstring's own text is what the Lean is read against. `pdftoppm` and `pdftotext` are
  installed, so the Read tool renders its pages directly.
- **Definitions carry self-contained docstrings** that say what the definition means, and
  cite nothing.

## What was here before, and where it went

Two older renderings — the `latex-specs` papers (namespace `Decoupled`, with `Analysis/`
and a citation apparatus) and `consensus.pdf` (namespace `Consensus`) — were removed on
2026-08-24 (Roberto: keep only what `Spec/Consensus1/` and the extractor need). **The
branch `pre-consensus1-purge` holds the last commit carrying all of it**, history
included; docstrings that name a removed file point there. The `latex-specs` checkout
survives locally as a plain untracked clone (it was a submodule), and the local
`REFERENCES_LOCAL.md` says where the still-earlier first attempt lives. Treat everything
from those layers as unverified until re-checked here.

## The framework is a submodule, and must not be pushed to

`deps/lean-sts` is a submodule of <https://github.com/saltiniroberto/lean-sts>, a separate
project. This one will use its `StsMultisetLog` flavour, via the path `require` in
[lakefile.toml](lakefile.toml); nothing imports it yet — the sts wiring is future work,
and the duties' `NDREB.outcomes` boundary is shaped for it.

**Never push to it.** A push from inside a submodule goes to that repository, not this one.
`.claude/hooks/protect-lean-sts.py` denies the tool call rather than warning about it, and
also refuses writes under `deps/lean-sts/` — edit the framework in its own working copy of
that repository, and then move the submodule pointer here.

Changing which revision this project builds against needs no push: check out the commit in
`deps/lean-sts`, then commit the submodule pointer here.

## One step at a time, and no decision that depends on unwritten code

Roberto, 2026-08-13. Decide what the step in front of you needs, and nothing further. A
choice that only makes sense given a definition, figure or proof that does not exist yet is
not ready to be made, and making it early means making it twice — first on a guess, then
again when the thing lands and the guess turns out not to fit.

So: do not move a declaration because of where a *future* file will want it. Do not shape a
statement around a definition that is still absent. Do not pick a directory layout for
files that are not written. When one of those questions comes up, say what the step needs,
note the question, and leave it.

**The one exception is deciding which of the draft's results to skip**, which does need
looking ahead: whether something is worth rendering turns on what it depends on and on
whether anything else consumes it, and both are known from the draft without writing any
Lean.

## Protocol code reads like the draft's pseudocode

Roberto, 2026-08-16. When writing protocol code — the figure renderings and the layers
around them — aim for the draft's own spelling, line for line. When a Lean type blocks
that spelling, prefer closing the gap once in the vocabulary or notation layer (the way
`⊥`, `w(S)`, the assignment arrows, `←ᵖ` and `broadcast` are done) over inlining a Lean
idiom in the routine; when the gap cannot be closed safely, keep the routine's shape as
close as the types allow and say in a comment or the docstring which line deviates. One
measured limit: `∈` cannot be overloaded for `Option` elements (recorded on the
`pre-consensus1-purge` branch).

The running list of every stylistic ruling is **"The `Consensus1` style sheet"** in
`CONTEXT.md`; the reader-facing versions are the pages under `lean/Spec/Consensus1/doc/`.
Update the style sheet when a new ruling lands.

**A word the draft *defines* keeps its name; a word it does not define is not used.**
Check that the draft defines a term before adopting it into a name, a docstring or
`CONTEXT.md`. The extractor's conventions (`extract/README.md`) lean on the same
discipline: a docstring opens with the draft's own backticked form, and that is what the
extraction harvests.

## A spec change stops at the spec

Roberto, 2026-08-17. When a `Spec/` definition changes, change `Spec/` and **stop** — do
not reshape statements or repair proofs in the same motion, however mechanical the fix
looks. A changed definition changes what any theorem *says*, and what each should now say
is Roberto's call, made looking at the new definition — not read off a diff that already
rewrote everything downstream. So: land the spec edit, say plainly that the build is red
and which declarations fail, sketch what each failing statement could become, and wait for
the word. (No `Analysis/` exists for this draft yet; the rule is what will govern it when
it does.)

## `Spec/` holds definitions, never theorems

Roberto, 2026-08-17. **A `theorem` in a `Spec/` file is a bug.** The specification layer
is what a reader audits against the draft, and every proved fact about it belongs under
`Analysis/` when that layer exists. The one tolerated exception is a proof a *definition
itself* cannot exist without — the `…Beq_iff` soundness theorems behind `Model.lean`'s
decidability instances, and `Raise.lean`'s `Subsingleton Error` behind the fold
instances; do not add to that set without instruction.

## Proof discipline

Never, at any point: no new `axiom`s, no `native_decide`. Both move a claim off the kernel
permanently, and no later work discharges them. `make check` and `make dev` both refuse
`native_decide`.

**`sorry` and `admit` are allowed while a proof is being developed**, and only then. They
are placeholders with a counter attached, not a resting state:

- `make dev` is the working target. It allows them and reports how many are outstanding.
- `make check` is the strict target. Any `sorry` or `admit` fails it.
- `make sorries` lists them with `file:line`, without failing.

So a `theorem … := sorry` is a legitimate intermediate state, and `make check` is what says
the work is finished. Do not leave one behind silently: if a `sorry` is going to stay for a
while, say so where it is and in `CONTEXT.md`, with what is missing.

The checks are a `grep`, so **write the word in backticks whenever a comment or docstring
talks about one** — the pattern exempts a backticked mention and counts a bare one.

A result whose *statement* cannot yet be written — because it quantifies over something
this project has not modelled — is different from one whose proof is missing. That one
stays a `def … : Prop`, or takes the absent notion as an explicit parameter, so that
nothing claims a shape the draft has not been checked to support.

**Invoke the `lean-proof-idioms` skill before starting a proof over a definition written
in the draft's imperative shape** — `Id.run do`, `let mut`, `while`. The obvious tactics
fail on those in ways that misdiagnose. The skill is an import from the first attempt and
has not been re-checked here; correct it in place when it turns out to be wrong for this
rendering.

## Commands

    make            # list the available targets
    make cache      # fetch prebuilt Mathlib artifacts -- do this before a first build
    make dev        # working target: allows sorry, counts what is outstanding
    make check      # strict target: any sorry/admit fails it
    make sorries    # list the outstanding sorry/admit, without failing
    make build      # build this project's lib

The toolchain is pinned in [lean-toolchain](lean-toolchain) (Lean 4.32.2). Mathlib's rev in
`lakefile.toml` must match it **and** must match the rev `deps/lean-sts` requires — Lake
resolves one rev per dependency name across the whole build graph. All three are `v4.32.2`.
Bump them together.

## Keeping context across sessions

Durable context lives in two files, split by what a reader could act on:

- [CONTEXT.md](CONTEXT.md) — everything usable by anyone with this repository and the
  Internet: decisions, submodule revisions, version pins, what is proved, what failed.
  Tracked.
- `CONTEXT_LOCAL.md` — everything that needs Roberto's machine: where the local checkouts
  are, what state they are in, local quirks already paid for. **Gitignored**, so it is
  absent from a fresh clone and nothing recovers it if it is lost.

When adding an entry, ask which file the reader could act on: an absolute path on this
machine belongs in the local one, a version pin in the other. When either would do, put it
in `CONTEXT.md` — that is the half git keeps.

**Keep them current as work progresses** — they exist so nothing is lost when the
conversation is compacted or a session ends. Write to them, without being asked, whenever:

- a modelling decision is made (record the alternatives rejected, and why);
- a proof approach fails or turns out to be a dead end — the negative results are the most
  expensive thing to rediscover;
- a Lean-specific workaround, tactic or idiom is needed to make something go through;
- the state of the work changes (what is proved, what is stated, what is next).

Keep entries short and factual. Date anything time-sensitive. Delete entries that have
become wrong rather than leaving them to mislead.

A **technique** that would help on the next lemma goes in a skill instead, under
`.claude/skills/<name>/SKILL.md`. Write one without being asked when a lesson transfers,
was expensive to find, and is not already carried by the code, `CONTEXT.md` or git
history. Write the `description` frontmatter as concrete triggers — error messages, tactic
names, symptoms — because that line is the only part in context by default and it decides
whether the skill ever fires.

## Writing

**Do not use a term the reader has not been given a definition for.** Prefer the
identifier over a nickname for it: write `S`, not "the cursor". A coined term is fine if
it earns its keep, but define it where it is first used in that file and then use it
consistently. A term taken from the draft counts as undefined unless the draft defines it,
and checking is the writer's job.

**Write plainly.** Short sentences, one point at a time, in order. Avoid em-dash asides
stacked several to a paragraph, a bolded lead-in on every bullet, "three reasons, the last
decisive" shaping, "not X but Y" inversions, and commit messages built as an essay with a
thesis. Explanation is wanted; the shaping around it is not.
