# Handover — 2026-08-22, at commit `c9ab37e`

Written for a session starting fresh on this repository, with none of the preceding
conversation. It is a snapshot, not a record: `CONTEXT.md` is the record, and where the two
disagree, `CONTEXT.md` is right. Delete this file once it has been read.

## Read these first, in this order

1. `CLAUDE.md` and `CLAUDE.local.md` — the rules. They override defaults, and several of them
   change what happens without being asked (commit at every logical stopping point; never push
   to `deps/lean-sts`).
2. `CONTEXT.md`, from the heading `## 2026-08-19 — strategy pivot: correctness over fidelity`
   to the end. That is the whole of the current phase. The `## Next` section at the bottom is
   the work queue.
3. `lean/Spec/Consensus1/Model.lean` and `lean/Spec/Consensus1/Store.lean`, for the vocabulary
   the newest rendering uses.

## Where the work stands

`main` is at `c9ab37e`, working tree clean, 200 commits ahead of `origin/main`. Last verified
today at that commit: `lake build Spec` completes 830 jobs; `make nodecide orphans sorry cites`
passes, with 535 citations in 77 files and zero outstanding `sorry`.

Two branches are archives, not work in progress: `coherence-invariant` (`f9157d5`) holds a
`Reachable S → Coherent S` proof about the *older* store plus the probe that uses it, and
`finmap-store` (`363dab3`) holds a rejected store representation. Neither is merged, and the
coherence proof does not transfer to the newest rendering.

`README.md` is stale, deliberately — it is refreshed in one pass before a push, per
`CLAUDE.local.md`, and a push is due.

## Three renderings coexist, and share nothing

| Subtree | Namespace | Renders | State |
| --- | --- | --- | --- |
| `lean/Spec/Defs/` | `Decoupled` | the `latex-specs` submodule | frozen record; `make cites` keeps it green |
| `lean/Spec/Consensus/` | `Consensus` | `consensus.pdf` | six figures plus `Validator.lean` |
| `lean/Spec/Consensus1/` | `Consensus1` | `consensus-1.pdf` | seven figures, complete as of today |

`consensus-1.pdf` is a rewrite of the draft, not a revision: block-only Goldfish, one store
built up in three layers, seven figures none of which matches the older draft's six. Roberto's
call was that it lives **beside** the older rendering. `Spec/Consensus/` is byte-identical to
what it was before it arrived (`git diff 52d8141 HEAD -- lean/Spec/Consensus/` is empty).

Two standing instructions follow from that, both still in force:

- **Do not modify `lean/Spec/Consensus/Validator.lean`.** It is the honest-validator layer
  Roberto is writing by dictation, against the older draft's store.
- **Leave `Spec/Consensus/` as it is.** Work on the newer draft happens in `Consensus1`.

Because the three share nothing, `Notation.lean` and `Raise.lean` exist three times over. That
is legal for the notation because its macros are `scoped`. `FinsetM.lean` is *not* duplicated —
its declarations sit in the root `Finset` namespace, so two copies would collide — and
`Consensus1` needs none of it.

The three layers of the newest draft are three namespaces, because Sections 2, 3 and 5 each
redefine `get_head`: `Consensus1.Goldfish`, `Consensus1.SG`, `Consensus1.FG`. The protocol's
fork choice is `FG.getHead`. `ghost` sits in `Consensus1` itself, no section redefining it.

## What is open

From `CONTEXT.md`'s `## Next`, items 0 and 1. Both wait on Roberto — the phase is strictly
reactive, and correctness work happens where he points.

**On `Consensus1`.** One named deviation: `FG.getHead` does not hand `ghost` the extended
eligibility condition, because that condition raises (it reads `Σ.σ[B].h`) while `ghost` takes
a plain `Block → Bool`. The walk reads the height clause through the raw `Option` instead, so
an unrecorded block fails the clause rather than the walk; the two agree wherever `Σ.σ` covers
`Σ.T`. Closing it means a monadic `ghost`, which changes Figure 1. And there is no `Analysis/`
for this draft at all.

**On `Consensus/`.** `Validator.lean`'s one routine, `onSGFGVotingAction`, is still a skeleton,
its invented lines marked `skeleton:`. Missing, all dictated: what the head field carries once
§5 defines confirmation, the veto's real rule, `propose_block`, the Goldfish vote itself, and
the two standing omissions (the source-proposal branch, the signing history). The theorem worth
having next is that its exception never fires, which is one step off the `coherence-invariant`
branch's proof.

## Rules that bite in practice

The full set is in `CLAUDE.md`; these are the ones this phase kept hitting.

- **A question asks for an answer, not for action** (`~/.claude/CLAUDE.md`). Answer and stop.
  Verifying in the scratchpad first is fine; changing project files is not.
- **A spec change stops at the spec.** Change the `Spec/` definition, say plainly which
  declarations now fail, sketch what each failing statement could become, and wait.
- **`Spec/` holds definitions, never theorems.** A `theorem` in a `Spec/` file is a bug. The
  tolerated exception is a proof a definition cannot exist without, such as the `…Beq_iff`
  soundness theorems behind the decidability instances.
- **New and changed definitions cite nothing** — no `latex-specs` citations, no dual texts —
  and carry self-contained docstrings. Existing citations stay exactly as they are.
- **No new `axiom`, ever, and no `native_decide`, ever.** `sorry` is allowed while a proof is
  being developed and must be declared where it sits and in `CONTEXT.md`. Both checks are
  `grep`, so write the word in backticks in any prose that mentions it.
- **Readability rules for the newest subtree**, each given as a correction and standing until
  revoked: no `match` in a spec definition, and no `|` at all — not even
  `let some x := e | return`. The idiom is `if h : o.isSome then let x := o.get h`. No `∣`
  (divides) in code; write `% … = 0`. One spec body still carries the old style, to convert on
  his word: the `match a.heightPair` at
  [Fig1StateTransition.lean:137](lean/Spec/Consensus/Fig1StateTransition.lean#L137). The other
  `match` in the tree, `ghostFuel`'s on its fuel argument, is a recursion pattern rather than a
  branch inside a routine, and stays.
- **Protocol code reads like the paper's pseudocode**, line for line. Close a gap once in the
  notation layer rather than inlining a Lean idiom in a routine. A renamed symbol needs the
  paper's symbol first in its docstring and a glossary row in the module header.
- **`MAPPING.md` prose and `mapping.html` are paused**, refreshed only on instruction. The
  exception that cannot pause: `make cites` fails when a `lem…` declaration in
  `Analysis/Lemmas.lean` has no row, so a new statement of record still gets its bare row.

## Traps measured in this phase

Each of these cost real time. The reasoning behind them is in `CONTEXT.md`; this is the short
form.

**Tooling.**

- **A Bash heredoc containing a Lean docstring opener is denied by the hook.** The strings
  `/-` immediately followed by `-`, and `/-` followed by `!`, read as paths outside the
  project, and `.claude/hooks/confine-to-project.py` denies the whole call. Write Lean files
  with the Write tool. A patch script must live in `scratch/` and run as `python3 scratch/x.py`.
- `scratch/` is gitignored on `main` and tracked on `coherence-invariant`, so `git checkout main`
  deletes files that exist on both.
- Mathlib's rev in `lakefile.toml` must match `lean-toolchain` **and** the rev
  `deps/lean-sts` requires — Lake resolves one rev per dependency name. All three are
  `v4.32.2`. Bump together.

**Lean.**

- `ResultOrExcept α := Except Error α` must be an **`abbrev`**. As a `def` it is not reducible
  for instance synthesis, so `Monad` and `MonadExcept` are not found and `do`, `←` and
  `throw .error` all fail.
- `Error` is payload-free and `Subsingleton`. A payload would make `Std.Commutative` for a
  monadic fold over a `Finset` *false*, not merely unproved.
- **A `Finset` has no `ForIn`**, and `Finset.toList` depends on `Classical.choice`. A loop over
  a set is `Finset.fold`, which needs `Std.Commutative` and `Std.Associative` on the combining
  operation — union has both. Annotate the fold's result type, or instance search is stuck
  inside a `do` block.
- `(← e)` lifts to the nearest enclosing `do` **statement** and cannot cross a `fun` binder.
  Bind above a pure `filter`, or use `filterM`. A *term* macro producing `←` is never lifted;
  a `doElem` macro is.
- **Only values cross a `do`-block join point.** A hypothesis in the local context does not
  survive one, which is why the routines stopped taking proof arguments.
- A bare `{ … }` or `⟨…⟩` against `Option (Recorded …)` fails, and **no coercion is ever
  consulted** — notation whose meaning comes from the expected type cannot be helped by
  anything acting after elaboration. Write `some { … }`.
- `Model.lean`'s `Beq` functions are in **equation style** (`| pat, pat => …`) because that is
  what makes termination inferable. A rewrite in `fun`/`match` style fails termination and then
  `simp made no progress`. Patch that file surgically; do not retype it.
- `deriving DecidableEq` fails for a structure mentioning `Block` before `DecidableEq (Block …)`
  exists. Hand-write the instance after the decidability section.
- `Finset.card`, `Finset.exists_min_image` and `Std.Commutative (· ∪ ·)` each needed an import
  added to `Model.lean`: `Mathlib.Data.Finset.Card`, `.Max`, `.Lattice.Basic`.
- `typeclass instance problem is stuck: Committees ?m` — annotate the call,
  `(Committees.K s : Finset Validator)`.

**The one that took the library down.** Re-rendering the draft in place deleted seven files and
left `Validator.lean` importing `Spec.Consensus.Fig6TimedStore`, which fails at the *import*
stage and so fails everything. That is why there are three subtrees. The same trap is one
`git rm` away whenever a draft is superseded.

## Commands

    make            # list the targets
    make cache      # prebuilt Mathlib artifacts — before a first build
    make dev        # working target: allows sorry, counts what is outstanding
    make check      # strict target: any sorry or admit fails it
    make sorries    # list them with file:line, without failing
    make cites      # citation check over the frozen fidelity apparatus
    lake build Spec # the three renderings, without the analysis layer
