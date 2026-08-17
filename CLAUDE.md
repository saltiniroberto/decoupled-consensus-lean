# decoupled-consensus-lean

A formalization of *Height Filtering and Healing for a Simplex-Style Finality Variant* in
Lean 4, built section by section, auditing each part as it lands.

@CLAUDE.local.md

The line above pulls in this checkout's own rules, which are gitignored. If the file is
absent, as in a fresh clone, the import is a no-op.

## This is the second attempt

The first attempt is complete and lives in a different repository. **Nothing from it is in this
repository** — not its Lean, and not copies of its notes. Treat its conclusions as unverified:
not merely as decisions this project may retake, but as possibly wrong.

It is consulted on request. Where to read it, and what state it is in, are in the gitignored
`REFERENCES_LOCAL.md` and `CONTEXT_LOCAL.md`. If you find yourself editing a file inside that
other repository, you are in the wrong project.

## The paper is the contract

The source is the `latex-specs` **submodule** at the repository root, pinned at `e4375c5`, so
`git submodule status` says which revision this Lean tracks. That is the same repository and
the same revision the frozen first attempt tracks, so its `MAPPING.md` line numbers and
printed numbers still apply. `height_filter_healing.tex` is Sections 1–5 and `\input`s
`recovery_core.tex` for 6–13.

**Most of the paper's prose is AI-generated.** The numbered definitions, the algorithm figures
and the lemma statements are the contract; the prose around them is not. So do not adopt a
word into a docstring, a name or `CONTEXT.md` because the paper uses it — check that the paper
*defines* it. Three that it does not, measured in the first attempt: `cursor` (write `s`),
`tally`/`tallies` (name the field: `P`, `Q_target`, `Q_prog`), `materialize`. The same care
applies to content: a sentence that reads like an argument may not be one, so check it against
the figures before relying on it.

## The framework is a submodule, and must not be pushed to

`deps/lean-sts` is a submodule of <https://github.com/saltiniroberto/lean-sts>, a separate
project. This one uses its `StsMultisetLog` flavour, via the path `require` in
[lakefile.toml](lakefile.toml).

**Never push to it.** A push from inside a submodule goes to that repository, not this one.
`.claude/hooks/protect-lean-sts.py` denies the tool call rather than warning about it, and
also refuses writes under `deps/lean-sts/` — edit the framework in its own working copy of that
repository, and then move the submodule pointer here.

Changing which revision this project builds against needs no push: check out the commit in
`deps/lean-sts`, then commit the submodule pointer here.

## One step at a time, and no decision that depends on unwritten code

Roberto, 2026-08-13. Decide what the step in front of you needs, and nothing further. A choice
that only makes sense given a definition, figure or proof that does not exist yet is not ready to
be made, and making it early means making it twice — first on a guess, then again when the thing
lands and the guess turns out not to fit.

So: do not move a declaration because of where a *future* file will want it. Do not shape a
statement around a definition that is still absent. Do not pick a directory layout for files that
are not written. When one of those questions comes up, say what the step needs, note the question,
and leave it.

**The one exception is deciding which of the paper's results to skip**, which does need looking
ahead: whether a lemma is worth translating turns on what it depends on and on whether anything
else cites it, and both are known from the paper without writing any Lean.

## Protocol code reads like the paper's pseudocode

Roberto, 2026-08-16. When writing protocol code — the figure renderings and the layers around
them — aim for the paper's own spelling, line for line. When a Lean type blocks that spelling,
prefer closing the gap once in the vocabulary or notation layer (the way `⊥`, `w(S)` and the
assignment arrows are done) over inlining a Lean idiom in the routine; when the gap cannot be
closed safely, keep the routine's shape as close as the types allow and say in a comment or the
docstring which line deviates. `CONTEXT.md` records the measured limits of this — overloading
`∈` is the known one.

## `Spec/` holds definitions, never theorems

Roberto, 2026-08-17. **A `theorem` in a `Spec/` file is a bug.** The specification layer is
what a reader audits against the paper, and every proved fact about it belongs under
`Analysis/`. When a definition wants a companion fact — a membership characterization, a
"the output satisfies the relation" lemma — define the function in `Spec/`, put the theorem
in `Analysis/Proofs/`, and point to it from the definition's docstring
(`getConfirmedSet`/`Proofs.mem_getConfirmedSet` is the worked pair). The one tolerated
exception is a proof a *definition itself* cannot exist without, such as the `…Beq_iff`
soundness theorems behind `Spec/Defs/Basic.lean`'s decidability instances; do not add to
that set without instruction.

## Proof discipline

Never, at any point: no new `axiom`s, no `native_decide`. Both move a claim off the kernel
permanently, and no later work discharges them. `make check` and `make dev` both refuse
`native_decide`.

**`sorry` and `admit` are allowed while a proof is being developed**, and only then. They are
placeholders with a counter attached, not a resting state:

- `make dev` is the working target. It allows them and reports how many are outstanding.
- `make check` is the strict target. Any `sorry` or `admit` fails it.
- `make sorries` lists them with `file:line`, without failing.

So a `theorem … := sorry` is a legitimate intermediate state, and `make check` is what says the
work is finished. Do not leave one behind silently: if a `sorry` is going to stay for a while,
say so where it is and in `CONTEXT.md`, with what is missing.

The checks are a `grep`, so **write the word in backticks whenever a comment or docstring talks
about one** — the pattern exempts a backticked mention and counts a bare one. A docstring
explaining why a proof is outstanding otherwise adds to the count and fails `make check`.

A paper result whose *statement* cannot yet be written — because it quantifies over something
this project has not modelled — is different from one whose proof is missing. That one stays a
`def … : Prop`, or takes the absent notion as an explicit parameter, so that nothing claims a
shape the paper has not been checked to support.

**Invoke the `lean-proof-idioms` skill before starting a proof over a definition written in
the paper's imperative shape** — `Id.run do`, `let mut`, `while`. The obvious tactics fail on
those in ways that misdiagnose: `unfold` leaves `__do_jp` continuations no tactic can see
past, a `while` is a least fixed point that does not reduce even on concrete input, and `rw`
reports "no match" against a goal identical to the lemma. The skill is an import from the
first attempt and has not been re-checked here; correct it in place when it turns out to be
wrong for this rendering.

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

- [CONTEXT.md](CONTEXT.md) — everything usable by anyone with this repository and the Internet:
  decisions, submodule URLs and revisions, version pins, what is proved, what failed. Tracked.
- `CONTEXT_LOCAL.md` — everything that needs Roberto's machine: where the sibling checkouts
  are, what state they are in, local quirks already paid for. **Gitignored**, so it is absent
  from a fresh clone and nothing recovers it if it is lost.

When adding an entry, ask which file the reader could act on: an absolute path on this machine
belongs in the local one, a submodule revision in the other. When either would do, put it in
`CONTEXT.md` — that is the half git keeps.

**Keep them current as work progresses** — they exist so nothing is lost when the conversation
is compacted or a session ends. Write to them, without being asked, whenever:

- a modelling decision is made (record the alternatives rejected, and why);
- a proof approach fails or turns out to be a dead end — the negative results are the most
  expensive thing to rediscover;
- a Lean-specific workaround, tactic or idiom is needed to make something go through;
- the state of the work changes (what is proved, what is stated, what is next).

Keep entries short and factual. Date anything time-sensitive. Delete entries that have become
wrong rather than leaving them to mislead.

A **technique** that would help on the next lemma goes in a skill instead, under
`.claude/skills/<name>/SKILL.md`. Write one without being asked when a lesson transfers, was
expensive to find, and is not already carried by the code, `CONTEXT.md` or git history. Write
the `description` frontmatter as concrete triggers — error messages, tactic names, symptoms —
because that line is the only part in context by default and it decides whether the skill ever
fires.

## Writing

**Do not use a term the reader has not been given a definition for.** Prefer the identifier
over a nickname for it: write `s`, not "the cursor". A coined term is fine if it earns its
keep, but define it where it is first used in that file and then use it consistently. A term
taken from the paper counts as undefined unless the paper defines it, and checking is the
writer's job.

**Write plainly.** Short sentences, one point at a time, in order. Avoid em-dash asides
stacked several to a paragraph, a bolded lead-in on every bullet, "three reasons, the last
decisive" shaping, "not X but Y" inversions, and commit messages built as an essay with a
thesis. Explanation is wanted; the shaping around it is not.
