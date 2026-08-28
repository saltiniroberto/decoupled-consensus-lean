# decoupled-consensus-lean

The Lean 4 specification of **Ethereum decoupled consensus**. `lean/Spec/` is the
protocol's source of truth; `extract/` renders it into a paper-shaped document
(`extract/out/dc.pdf`); `lean/Analysis/` states results against it. The spec originated
as a rendering of a human-controlled draft (`consensus-1.pdf`, not distributed with this
repository); since 2026-08-24 the spec speaks for itself.

@CLAUDE.local.md

The line above pulls in this checkout's own rules, which are gitignored. If the file is
absent, as in a fresh clone, the import is a no-op.

## Correctness is the contract

Roberto, 2026-08-19 (and unchanged through the 2026-08-24 narrowing). What matters is that
every definition is correct, and Roberto is the judge of what correct means. Practically:

- **Strictly reactive.** Semantics change only on Roberto's explicit call, and correctness
  work happens where he points. No uninvited correctness audits.
- **No PDF spec is ever committed.** The draft that seeded the spec stays local
  (`CONTEXT_LOCAL.md` says where to read it) and is consulted only on Roberto's word;
  docstrings cite no document — each definition's own text is what the Lean is read
  against.
- **Definitions carry self-contained docstrings** that say what the definition means, and
  cite nothing.

## What was here before, and where it went

Everything outside the current scope was removed on 2026-08-24; **the branch
`pre-consensus1-purge` holds the last commit carrying all of it**, history included.
Treat everything from those layers as unverified until re-checked here. The one live
pointer is `Analysis/AccountableSafety.lean`'s, to the old proof.

## The framework is a submodule, and must not be pushed to

`deps/lean-sts` is a submodule of <https://github.com/saltiniroberto/lean-sts>, a separate
project. This one will use its `StsMultisetLog` flavour, via the path `require` in
[lakefile.toml](lakefile.toml). `lean/Sts.lean` is what imports it — the spec placed under
the framework's `Protocol`, its own `lean_lib`, imported by nothing in `Spec/`.

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

**The one exception is deciding what of a source document to skip** when importing from
one, which does need looking ahead: whether something is worth carrying over turns on
what it depends on and on whether anything else consumes it, and both are known from the
document without writing any Lean.

## Protocol code reads like paper pseudocode

Roberto, 2026-08-16. When writing protocol code — the algorithm files and the layers
around them — aim for the spelling a paper's figure would use, line for line. When a Lean
type blocks that spelling, prefer closing the gap once in the vocabulary or notation
layer (the way `⊥`, `w(S)`, the assignment arrows, `←ᵖ` and `broadcast` are done) over
inlining a Lean idiom in the routine; when the gap cannot be closed safely, keep the
routine's shape as close as the types allow and say in the docstring where it deviates.
One measured limit: `∈` cannot be overloaded for `Option` elements (recorded on the
`pre-consensus1-purge` branch).

The running list of every stylistic ruling is **"The `DC` style sheet"** in
`CONTEXT.md`; the reader-facing versions are the pages under `lean/Spec/doc/`.
Update the style sheet when a new ruling lands.

**A term is used only where the spec defines it.** A definition's docstring, a module
header, or the `## Extract` prose is where a term gets its meaning; do not adopt a word
into a name, a docstring or `CONTEXT.md` without a definition a reader can find there.
The extractor (`extract/README.md`) leans on the same discipline: a docstring may open
with a backticked paper form, which overrides the paper signature the extraction
otherwise derives from the `def` itself.

## A spec change stops at the spec

Roberto, 2026-08-17. When a `Spec/` definition changes, change `Spec/` and **stop** — do
not reshape statements or repair proofs in the same motion, however mechanical the fix
looks. A changed definition changes what any theorem *says*, and what each should now say
is Roberto's call, made looking at the new definition — not read off a diff that already
rewrote everything downstream. So: land the spec edit, say plainly that the build is red
and which declarations fail, sketch what each failing statement could become, and wait for
the word.

## `Spec/` holds definitions, never theorems

Roberto, 2026-08-17. **A `theorem` in a `Spec/` file is a bug.** The specification layer
is what a reader audits — each definition against its own docstring — and every proved
fact about it belongs under `Analysis/`. The one tolerated exception is a proof a *definition
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
nothing claims a shape that has not been checked to hold.

**Invoke the `lean-proof-idioms` skill before starting a proof over a definition written
in the imperative pseudocode shape** — `Id.run do`, `let mut`, `while`. The obvious tactics
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
consistently. A term taken from a source document counts as undefined unless the spec's
own prose defines it, and checking is the writer's job.

**Write plainly.** Short sentences, one point at a time, in order. Avoid em-dash asides
stacked several to a paragraph, a bolded lead-in on every bullet, "three reasons, the last
decisive" shaping, "not X but Y" inversions, and commit messages built as an essay with a
thesis. Explanation is wanted; the shaping around it is not.
