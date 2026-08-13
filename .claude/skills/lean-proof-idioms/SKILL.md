---
name: lean-proof-idioms
description: Lean 4 proof techniques for the decoupled-consensus formalization — proving things about definitions written in `do` notation with `let mut`, unfolding `while`/`repeat` loops (`Lean.Loop.forIn`) that do not reduce, `unfold` leaving `__do_jp` continuations that no tactic can see past, `rw` reporting "no match" against a goal that looks identical, `⊥` not matching `none` under `split`, and what to do when a paper's lemma turns out to be false as literally stated and needs an invariant the paper never wrote down. Read this before starting any proof over a `Spec/` definition rendered in the paper's imperative shape.
---

# Proving over the imperative rendering

**Imported 2026-08-13** from an earlier formalization of the same paper, now frozen. Every
technique below was measured there, against that attempt's definitions — the examples name
`process_slot`, `process_height_events`, `processHeightEvents`, and none of them exists here
yet.

**This copy is free to disagree with its source, and should.** That is the rule the source
project applies to skills, to `CONTEXT.md` and to the modelling attempts themselves:
independent by default, and two copies that drift are cheaper than one abstraction fitting
neither. So when a technique turns out not to apply to this project's rendering, correct it
here rather than deciding which copy is right. When an example names a definition this
project does not have, replace it with one that it does.

Two things carry over unconditionally, because they are facts about Lean rather than about
either attempt: the toolchain note below, and §1 on `simp only` versus `unfold`.

The protocol figures here are transcribed in the paper's own imperative shape —
`Id.run do`, `let mut σ := σ`, `σ.field ← e`, `while`, `for`. That is deliberate: the figure
is the specification and must read like the paper. The cost is that none of it reduces the
way a plain recursive definition would, and the tactics that look like they should work fail
in ways that misdiagnose easily.

Everything below was measured on **Lean 4.32.2 + Mathlib v4.32.2**, the pinned toolchain.
Re-check before copying any of it to a different toolchain — an earlier session lost time to
a claim carried over from a repository on 4.28.0, where `Lean.Loop.forIn` was `partial` and
genuinely unusable. It is not, here.

## 1. Reducing a `do` block: `simp only`, never `unfold`

`unfold f` on a `do`-block definition leaves join-point continuations in the goal:

    have __do_jp := fun σ x => …

and on those, **`split_ifs`, `simp`, `dsimp`, `beta_reduce`, `simp +zetaDelta`, and `rw`
with the equation lemma all fail**, individually and in combination. The join point hides
the branches from every tactic that looks for a top-level `if`.

What works is `simp only` with the definition names, which flattens the continuations into a
plain nest of `if`s and `match`es:

    theorem processHeightEvents_s (σ : ChainState Node Root) (st : Time) :
        (processHeightEvents σ st).s = σ.s := by
      simp only [processHeightEvents, advanceHeight]   -- NOT `unfold`
      split_ifs <;> (try split) <;> rfl

Note the shape of the closer:

* `split_ifs` reaches the `if`s that are now at the top level.
* `(try split)` handles a `match` sitting in one branch and not the others — `split` works
  on both `if` and `match`, `split_ifs` only on `if`.
* `rfl` reads the field straight off each record literal. **A record-projection simp set is
  not needed** (`{σ with F := …}.Qtarget = σ.Qtarget` is definitional); an earlier session
  wrote one down as required work and it was not.

When the nesting is deeper than one level — Figure 2 has an `if` inside a `match` inside an
`if` — `split_ifs <;> (try split)` runs out. Use:

      simp only [processAttestation]
      repeat' split
      all_goals rfl

Include the *called* definitions in the `simp only` list, not just the outer one. A field
lemma about `processHeightEvents` needs `advanceHeight` too, or the branches stay opaque.

### When the branch conditions are hypotheses

If you are proving something conditional on the branches not firing, `by_cases` on each
condition and then `simp` with the definition:

    by_cases h1 : σ.T_h = ⊥ ∧ σ.L.slot ≥ σ.s_h <;>
    by_cases h2 : σ.L.slot < σ.s <;>
      simp [processSlot, h1, h2, processHeightEvents_s]

This only reaches one level down. Past that, prove the inner routine's field lemma first and
pass it in the simp set, as `processHeightEvents_s` is passed above.

## 2. `⊥` is not syntactically `none`

`⊥` for an absent value is a `Bot (Option α)` instance, not a constructor. So after

    simp only [processAttestation, hT]     -- hT : σ.T_h = ⊥

the goal holds `match a.heightPair, ⊥ with | .target hh T, some Th => …` and **`split`
cannot reduce it** — it generalizes the discriminant and hands you the impossible
`some Th` arm as a live case. The failure looks like a missing case in your reasoning, not
like a notation problem, which is what makes it expensive.

Restate the hypothesis at the constructor. The coercion is definitional, so `have` accepts
it with no proof:

    have hT' : σ.T_h = none := hT
    simp only [processAttestation, hT']

### Multi-discriminant matchers

Even then, `match a.heightPair, none with …` will not reduce while the *first* discriminant
is a variable. Case on it first:

    cases hp : a.heightPair <;> simp only [processAttestation, hT', hp] <;>
      (repeat' split) <;> rfl

## 3. Loops

### `for x in xs` — no work needed

`List.forIn` is a structural recursion with simp lemmas. The nil and cons equations come out
of `simp` with the definition, and then you induct on the list normally:

    theorem processAttestations_nil (σ) (A) : processAttestations σ [] A = σ := rfl

    theorem processAttestations_cons (σ) (a) (as) (A) :
        processAttestations σ (a :: as) A
          = processAttestations (processAttestation σ a A) as A := by
      simp [processAttestations]

(The `nil` case is `rfl`; the `cons` case is not.)

### `while` / `repeat … until` — the `rfl` bridge

A `while` elaborates to `Lean.Loop.forIn`, a least fixed point. Nothing about it reduces,
**not even on fully concrete input** — `simp` leaves `forIn Loop.mk …` stuck. There is a
public one-step unfolding lemma, `Lean.Loop.forIn_eq_of_monadTail`
(`Init/Internal/Order/While.lean`), with `MonadTail Id` available
(`Init/Internal/Order/MonadTail.lean`).

But `rw [Lean.Loop.forIn_eq_of_monadTail]` reports **"no match" against a goal that looks
character-for-character like the lemma.** The reason: the goal holds `forIn`, the `ForIn`
*class method* at instance `Lean.instForInLoopUnitOfMonad`, while the lemma is about
`Lean.Loop.forIn` directly. `rw` does not see through the instance projection.

The fix is a `rfl` bridge — restate the loop with the bare `Lean.Loop.forIn`, which is
definitionally the identity, and `rw` then fires:

    theorem processSlots_eq_loop (σ : ChainState Node Root) (t : Time) :
        processSlots σ t =
          Lean.Loop.forIn (m := Id) Lean.Loop.mk σ
            (fun _ s => if s.s < t then pure (.yield (processSlot s)) else pure (.done s)) := rfl

    theorem processSlots_step (σ : ChainState Node Root) (t : Time) :
        processSlots σ t = if σ.s < t then processSlots (processSlot σ) t else σ := by
      rw [processSlots_eq_loop, Lean.Loop.forIn_eq_of_monadTail]
      by_cases h : σ.s < t
      · simp [h, processSlots_eq_loop]
      · simp [h]; rfl

### Then replace the loop with a structural recursion, once

Do not make every later proof unfold the loop. Prove the equivalence once and let everything
downstream induct on a `Nat`:

    noncomputable def closeSlots : Nat → ChainState Node Root → ChainState Node Root
      | 0, σ => σ
      | n + 1, σ => closeSlots n (processSlot σ)

    theorem processSlots_eq_closeSlots (t : Time) (σ : ChainState Node Root) :
        processSlots σ t = closeSlots (t - σ.s) σ := by
      induction hn : t - σ.s generalizing σ with
      | zero => rw [processSlots_step, if_neg (by omega), closeSlots]
      | succ n ih =>
          rw [processSlots_step, if_pos (by omega), closeSlots,
              ih (processSlot σ) (by rw [processSlot_s]; omega)]

The ingredient that makes the count right is a **cursor lemma** — here `processSlot_s`,
saying the body advances the counter by exactly one. Prove that first; it is the thing the
induction is actually about. A loop with no such measure (Figure 3's `repeat … until`
fixed point) can still be unfolded by the bridge, but the count is genuinely open and that
is a different problem.

This lives in `Analysis/`, never in `Spec/` — the figure keeps its literal `while`.

## 4. When the paper's lemma is false as stated

This happens, and it is not a transcription error. A paper lemma is usually stated about
*reachable* states, with the reachability left implicit in the surrounding prose; stated
over an arbitrary state it can be plainly false. The method that worked:

1. **Machine-check the counterexample before rewriting the statement.** A tiny concrete
   model with `local instance`s is enough. Do not reason your way to "the statement must be
   fine"; the whole point is that it looked fine.

2. **Keep the counterexample afterwards.** Its job changes from refuting the lemma to
   justifying the hypothesis you added — and it is what stops a later session from
   "simplifying" the hypothesis away. Rewrite its header to say so.

3. **The missing hypothesis is an invariant, and the invariant needs a conjunct the paper
   never states.** Find it by asking *which single step breaks preservation*. In Lemma 3,
   three conditions (the negations of a definition's three branches) were the obvious
   invariant, and they were not preserved: `process_slot` writes `T_h ← L`, flipping a
   condition that one of the three relied on to stay blocked. The fourth conjunct —
   `σ.T_h = ⊥ → σ.Qtarget = ∅` — is what closes that hole, and it is true for a reason
   visible only in another figure (the only writer of a target bit needs `T_h ≠ ⊥`).

4. **Do not expect one invariant preserved by every step.** It usually is not. Identify the
   *minimal* part that must be threaded end to end, and let a normalizing step at the end of
   the transition re-establish the rest:

       Settled σ  ──process_slots──▸ Settled
                  ──process_block──▸ emptyTarget only   ← quorums get built here, by design
           ──process_height_events──▸ Settled

   Three small proofs instead of one intractable one. Trying to make the full invariant
   survive `process_block` is trying to prove attestations do not do their job.

5. **Watch for degenerate cases hiding in `Nat` arithmetic.** `q = ⌈2W/3⌉` is `(2*W+2)/3`,
   which is `0` on an empty electorate — and then every set is a quorum and even genesis
   fails the invariant. Threshold positivity is a real hypothesis. Take it as a plain
   `(hq : 0 < q Node)` in the machinery file and discharge it from the adversary assumption
   at the point of use; that keeps the machinery independent of the file that defines the
   assumption.

6. **State the hypothesis the paper means, not a proxy.** Lemma 3 quantifies over blocks
   (`blockState X = .state σ`), not over states with a `Reachable` predicate invented for
   the occasion. The block-post-state induction then supplies the invariant.

## 5. State a "nothing changes" lemma positively

A paper phrases an invariance lemma negatively — a list of fields that do not move — and the
obvious transcription is a conjunction:

    σa.h = σ.h ∧ σa.nj = σ.nj ∧ σa.s_h = σ.s_h ∧ …          -- weak

Prefer a **single record equation** saying what may change:

    ∃ Th, (Th = σ.T_h ∨ Th = some σ.L) ∧
      actionState σ actionSlot = { σ with s := max σ.s actionSlot, T_h := Th }

Three reasons it is stronger, the last decisive:

* it pins the fields that *do* move (here the cursor), which the conjunction leaves unstated;
* it pins fields the conjunction never thought to mention;
* **it says nothing else exists.** A field added to the state record later silently weakens
  the conjunction — it still compiles, and it no longer says what you meant. It cannot
  weaken the record equation.

Keep the paper's phrasing as a two-line corollary beside it, so a reader checking the Lean
against the `.tex` still finds the list. The machinery lemma the proof runs on
(`closeSlots_of_settled` here) has to carry the witness for the open field, which is a small
strengthening of its statement, not a new proof.

Leave a field open only as far as you must: pinning `T_h` exactly was possible but needs the
induction to split `n = 0` from `n ≥ 1`, and nothing yet needs to know *which* target was
named. Say that in the docstring rather than leaving it looking like an oversight.

## 6. Mechanics that cost time

* **Iterate in the scratchpad.** Write a throwaway `.lean` importing the library and run
  `lake env lean <file>` — seconds per attempt against a full `lake build`. Move into the
  repo only once it compiles. Run `lake` from the repository root; never `lake -d`.

* **`omega` is the closer for `Nat` thresholds**, including division and truncated
  subtraction by literals. Unfold the definitions into it (`unfold q m b W at *; omega`).

* **The `unusedSectionVars` linter is whack-a-mole.** Each `omit` you add changes what the
  *next* declaration reports, because it changes that declaration's own signature. Worse, it
  sometimes suggests omitting an instance the statement genuinely needs, and you find out
  only from a "failed to synthesize" error further down. Re-read the warnings after every
  single change rather than applying the batch. If a whole section turns out to need fewer
  instances than declared, fix the `variable` line instead of writing five `omit`s.

* **`omit … in` goes before the docstring**, not between the docstring and the `theorem`.
  The latter is a parse error (`unexpected token 'omit'; expected 'lemma'`).

* **Do not write unconditional success echoes in shell loops.** An `echo "=== ALL OK"` that
  fires whether or not `lean` succeeded will make you report a proof that does not compile.
  Count errors (`grep -c ': error'`) and print that.

## 7. Then update the audit and the context log

A new theorem is not covered by `AxiomAudit.lean` until it is listed there — the audit is
named results only, not a library sweep. And the experiment's own `CONTEXT.md` is where the
modelling decision, the dead end, and the Lean workaround belong; write them as you go, not
at the end.

## 8. Name shadowing inside `theorem X.foo`

Inside the body of `theorem X.foo`, the namespace `X` joins the resolution path, so any
bare `bar` that has an `X.bar` sibling resolves to the **sibling**, not the global. Both
directions of this have burned a session:

- defining `Chained.processBlock` made bare `processBlock` in its body resolve to itself;
- defining `WitnessedCore.processBlock` made bare `processAttestations` in its body resolve
  to `WitnessedCore.processAttestations` — a *different* declaration, defined earlier.

The failure modes are `simp only [processBlock]` reporting *"simp made no progress"* (same
message as a genuine unfolding failure — check resolution before tactics), and `invalid
{...} notation, structure type expected` when the wrong constant's argument types swallow a
record literal. Fix: `_root_.<full.path>` on every such reference in the body. Statements
are safe — the theorem's own namespace is not yet in scope while its signature elaborates.

## 9. An invariant that breaks mid-transition: split it

If one clause of an invariant cannot survive a phase of the transition — `Witnessed.latest`
says `blockState σ.L` exists, but `process_block` sets `L := B` before `blockState B` does —
do not weaken the clause. Split the structure: a core that rides the whole transition, and
the fragile clause in an `extends` wrapper re-established at the top of the ancestry walk,
where the completed `blockState` fact for the child is in hand (that is exactly what
`blockState_rec`'s step hypothesis provides). The same split separates what `process_block`
preserves from what only the walk can see.

## 10. Small frictions, quickly

- **`injection h`** sometimes closes the goal itself and sometimes only adds the component
  equation; a following `exact` errors with *"No goals to be solved"* in the first case.
  When it adds the equation flipped, `injection h with h; exact h.symm`.
- **`lake env lean` uses stale `.olean`s.** After editing a file's *dependency*, "unknown
  identifier" for something visibly present is not an error in your file — `lake build`
  the dependency first.
- **Record updates across lines** must indent the continuation past the `{`, or the parser
  stops at the first field: write `{ σ with\n  s := …,\n  T_h := … }`.
- **`omega` sees through `q = (2W + 2) / 3`**: `unfold q; omega` proves `0 < q` from
  `W ≥ 1`, and Nat-division by a literal generally. Positivity of `q` is free whenever any
  electorate member is in hand (`q_pos_of_mem`).

## 11. A nested `repeat`/`for` loop: the verbatim bridge

Section 3's `rfl` bridge extends to a two-level loop (`repeat … until` around a
`for … in` fold), but the bridge will NOT be `rfl` against a hand-written clean model —
the inner `forIn` is not a `foldl`, and floating `pure (.yield ·)` out of a match tree is
not definitional. The recipe that works, from `derive_block_states`:

1. `#print` the definition and copy the elaborated body **word for word** into
   `innerBody`/`outerBody` defs — every `have`, every `match` arm, in order. The bridge
   `deriveBlockStates S = (Loop.forIn … (outerBody S) …)` is then `rfl`.
2. Write the clean per-item function (`tryAccept`) with the **same `have`-shape and match
   tree** as the printed body, differing only at the leaves. Then
   `innerBody = fun a st => pure (.yield (tryAccept st a))` falls to `funext` plus
   lockstep `split`s.
3. **Never `repeat' split` an equation between two similar match trees** — it interleaves
   the two sides' matches and produces garbage cases pairing one side's `state s✝¹` with
   the other's `state s✝`. Split one discriminant at a time; identical scrutinees split
   both sides together.
4. Convert the inner `forIn` to `foldl` by list induction, and consume the outer loop by
   strong induction on a finite measure (`card (bound \ A)`), using the one-step
   unfolding: each yielding pass must strictly grow something inside a fixed bound.

## 12. Anatomy that needs the invariant it helps prove: the `_of` split

A lemma like `advance_quorum` ("an advancing block yields its branch's quorum") wants
`Witnessed` at the parent, and derives it via `blockState_witnessed`. But the walk that
*proves* `blockState_witnessed` wants `advance_quorum` in its own step — a genuine
circularity at the theorem level, invisible until the walk's step needs the anatomy.

The fix is mechanical: split into `advance_quorum_of`, which takes the parent's invariant
(and `Settled`, and `σp.L = P`) **as hypotheses** and is placed *before* the walk, plus a
public `advance_quorum` wrapper *after* the walk that derives them. Inside the walk's step
the induction hypothesis `ih` is exactly the invariant the `_of` form wants.

## 13. "Unless the fault bound is violated": the accountable disjunct

The fault bound constrains the Byzantine *set*, never the chain *data* — nothing in block
validity rejects double votes, so conflicting finalizations are constructible data and a
flat conclusion (`C ⪯ C'`, "h_max never decreases", "fork choice never leaves F") is
FALSE in-model even under `[Adversary Node]`. Render the paper's "unless the fault bound
is violated" as an explicit second disjunct:

    ∨ ∃ S, w(S) ≥ 2 * q Node - W Node ∧ ∀ i ∈ S, ∃ x y, …E1/E2…

Two arithmetic facts make these statements hypothesis-free where the paper has a standing
assumption: `W = 0 → q = 0`, so the empty set testifies at threshold `2q − W = 0`; and
`W ≥ 1 → q ≥ 1` (`q = ⌈2W/3⌉`, `unfold q; omega`), so the `Settled` machinery is available
in the other branch. Only lemmas whose *flat* conclusion needs quorums to be blockable at
all (3, 6, 8, 13, 18) genuinely need `[Adversary Node]`.

**State the disjunct with `IncludedOn`, always.** Three flat lemmas have now had to be
restated for this — `pastFinalized`, `targetUniqueness'`, `finalizedUniqueness` — and
the symptom is identical each time: an execution-level consumer has the slashable set
and an honest signer in it, and cannot get from there to a contradiction, because
`included_attestation_released` needs to know the two attestations sit *on the two
chains*. So write

    ∀ i ∈ S, ∃ x y, x.validator = i ∧ y.validator = i ∧
      IncludedOn x B ∧ IncludedOn y B' ∧ E1 x y

from the start. The inclusions are already in hand where the disjunct is built — the
certificates' quorum clauses carry them — so keeping them costs one `obtain` binder
that would otherwise be `-`. If a paper-numbered statement of record must keep the
paper's weaker shape, prove the strong one under its own name and derive the weak one,
as `finalizedChain` does from `pastFinalized`.

At the execution level the refuting lemma is `Proofs.signerSafetyExec`, which wants both
`sent` facts **at one step**. Two certificates from two different validators' views are
at two different steps: lift both with `sent_mono_le x (Nat.le_max_left m m')` and
`Nat.le_max_right`. State the exec wrapper with two store locations `(m, p)` and
`(m', p')` rather than one — `finalized_unique_exec` and `target_unique_exec` are the
worked pair. A single-location version costs nothing to use and rules out the
cross-validator case you will want next.

A related split: when the paper stresses "without any fault-bound premise", check which
half of the chain fact survives `q = 0`. Monotone lower bounds usually do (heights only
ever increment; a fired finalization has `h_F = h_j ≥ 1`) — re-prove them as per-`pHE`
facts folded through `closeSlots`, no `Settled` needed. Only *upper* bounds ("by exactly
one") need the quorum to be deniable.

## 14. Two small statement-shape lessons

- **Self-referential anatomy equations** dodge branch casing: the advancing height check
  writes `nj = nonjustifiable (pHE σ st).h (pHE σ st).h_F` — stating the written value in
  terms of the *post-state's own fields* is exact in every branch, because the
  finalization sub-step runs first and nothing touches `h_F` afterwards.
- **Extending a big `∧`-chain lemma breaks every consumer's `obtain` arity** — and the
  failure is a bewildering "Dependent elimination failed … `(pHE σ st).13`" at the
  destructuring site, possibly against a stale `.olean`. After extending, grep for the
  lemma's name and fix each `⟨…⟩` pattern; rebuild the dependency before trusting errors.

## 15. Scripted edits: assert, and place `omit` before the docstring

Python/sed batch edits over Lean files must `assert old in s` on every replacement — a
silent no-op (whitespace drift, a hypothesis renamed since the string was drafted) leaves
the file compiling the OLD proof while you debug phantom errors downstream. Two concrete
repeats: an anatomy extension that silently didn't apply, and a fold-lemma edit whose
old-string had one wrong simp argument.

`omit […] in` attaches to the *declaration*, so it goes **before** the `/-- … -/`
docstring, never between docstring and `theorem` — the parse error otherwise
(`unexpected token 'omit'; expected 'lemma'`) points at the docstring's last line, not at
the misplacement.

## 16. `Id.run do` rules with a threaded record (the Lemma 44 development)

Characterizing an imperative rule (`finalityPair`, `heightPair`) end to end:

- `unfold theRule; simp only [Id.run]` first — `split` cannot see an `if`/`match` under
  `.run`. The `pure`s can stay: leaf goals like `Evolves H (pure (p, H')).2` close by
  defeq (`exact Evolves.rfl H`).
- Leaf hypotheses over unreduced projections (`(pure (…)).2.lock k' = some L`) block
  `rw … at`; re-ascribe first — `have h' : H.lock k' = some L := h` — the ascription is a
  defeq check and normalizes the statement.
- Pair equalities from `Finset.mem_image` need `injection h with h1 h2`, not
  `congrArg Prod.fst h` + `rw` — congrArg leaves an unreduced `.1` that `rw` cannot match.
  And remember `injection` may close the goal itself; avoid a trailing `exact`.
- `Function.update`: `Function.update_self` / `Function.update_of_ne hk` are the whole
  API. For "the invariant survives a write at `k`", the `k' = k` case is settled by the
  match-arm hypothesis that put the write under `lock k = ⊥`.
- A big two-`let`-deep projection lemma (`fcw_J_pair`) can whnf-timeout as `rfl`;
  `by simp only [theDefinition]` proves the same equation cheaply.

## 17. Small recurring frictions, batch three

- `omega` cannot see through def-wrapped notation: `w(Q)≥q` elaborates to `Quorum Q`, a
  def. Re-ascribe — `have h4 : w(Q) ≥ q Node := hQw` — before `omega`.
- `(committee s).card` with nothing else fixing `Node` is a stuck metavariable
  (`Committees ?m` won't resolve); write `(committee (Node := Node) s).card` in
  statements.
- A twin that never mentions `Blk` should not take `Root` (or its `DecidableEq`): an
  `omit` on the statement side then strips `Root` from the binders and the one-line proof
  `Proofs.twin Node Root` fails with "Unknown identifier Root". Slim the twin instead.
- Choice-free statements (pure arithmetic, pure `⪯`-chains) pin `[propext, Quot.sound]`
  in AxiomAudit — run the build once to read off the actual axiom set before writing the
  guard line.

## 18. `Step.elim` proofs: stuck `if`s and `protocol.step` vs the step relation

Framework-level invariant proofs (`Analysis/Proofs/Exec.lean`)
hit two frictions that will recur in every lemma proved by `Step.elim` over
`Framework.Sts2MX` executions.

**Stuck `if q = q`.** `Config.setNode` builds `fun q' => if q = q' then … else …`
over the section's opaque `[DecidableEq Node]`, so after `subst` the condition
`q = q` does **not** reduce definitionally — `exact` fails with a type mismatch
showing the whole `if … then … else …` in the expected type. Fix: rewrite it away
explicitly, on the goal *and* on the step hypothesis, before the final `exact`:

    rw [applyNodeStepResult_getElem]      -- turns the bracket into the `if`
    ...
    · subst hqq
      rw [if_pos rfl]                     -- the goal's `if q = q`
      rw [setClock_getElem, if_pos rfl] at hstep   -- the hypothesis's

The framework's read-back lemmas (`applyNodeStepResult_getElem`,
`setClock_getElem`, `receive_getElem`) are the ones that expose the `if`; the
`≠`-branches close with `simp only [<read-back>, if_neg hqq]`.

**`protocol.step` is not syntactically `execStep`.** `Step.elim`'s cases hand you
`Pr.step p … e res` with `Pr := protocol`; a lemma stated over `execStep` will not
unify against it while stuck subterms remain. After the rewrites above, cross the
gap with a defeq re-ascription (the section-15 idiom again):

    have hstep' : execStep q d[q].clock d[q].view d[q].st .wake res := hstep
    exact execStep_history hstep'

Record-update projections (`{ d[q] with clock := t }.st`) are fine — those reduce
definitionally; only the `Decidable`-blocked `if` needs the rewrite.

**Membership lemmas beat equality lemmas in `Step.elim` case bodies.** A goal or
hypothesis there mentions store components through unreduced projection chains
(`(⟨…, 0⟩ : NodeStepResult _ _).state.store.blocks`). `rw` with an equality like
`(advanceTime S t).blocks = S.blocks` fails — no syntactic occurrence. State the fact
as an implication on membership (`h : b ∈ (advanceTime S t).blocks → b ∈ S.blocks`)
and *apply* it: application-side unification reduces the projections definitionally.
`storeViewSound`'s support lemmas (`mem_advanceTime_*`, `ingest_mem_*`) are the
pattern. Inside those lemmas the forms are syntactic and `rw`/`split` work normally —
after `simp only [<def>, Id.run]`, which zeta-reduces the `have`-bindings that make
bare `unfold` output unsplittable.

## 18. A lemma blocked on an opaque interface function: enrich the class, not the proofs

When results are unprovable because an interface function (`ghost`) is opaque, the fix is
to add its paper-stated behaviour to the class of assumed properties (`GoldfishStanding`)
— each field one sentence of the source, cited — not to weaken the lemmas or model the
function. Three lessons from doing it:

- **A counting mismatch between the contract and the proofs usually means a missing
  argument.** `ghost` "with no slot" versus the slot-filtered `childCount` dissolved once
  the slot became a parameter of `ghost` — it was part of the question every caller asks,
  and each call site now documents which slot it counts and why.
- **State capture fields with strict inequalities only.** Every margin the development
  produces is strict, and a strict-win-only field is silent on tie-breaks — a weaker
  assumption than the real algorithm, satisfied by any deterministic tie rule.
- **Layering: an assumed property stated over a counting function pulls that function
  into `Spec/`.** A class field in `Spec/` may not read `Analysis/`; move the counting
  definition (it is a numbered definition's rendering anyway) rather than duplicating it.

**Record-update literals: top level yes, tactic-embedded no; align the fields.** A
`{ S with a := …, b := … }` literal parses fine in a top-level `theorem` statement but
fails inside a tactic-embedded `show … from rfl` or `have : … :=` type with
"unexpected identifier; expected '}'" — hoist it into a named top-level rfl-lemma
(`onBlockBase_blocks` is the pattern). And in a multi-line update, the continuation
fields must be indented to the first field's column (`receipts :=` aligned under
`blocks :=`), or the parser closes the braces early with the same error.

## 19. `cases` on a match over derived-view terms: whnf timeout — abstract the view

`cases hd : deepest …` (or any `cases`/`split` whose discriminant is spelled with
`roundView x[i'][v].st v r` projections) can die with

    (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)

The discriminant abstraction forces the projections to reduce, which unfolds
`deriveForkChoiceWith` and the whole store derivation under them. The same proof over
an *abstract* view is instant.

Fix: state the core lemma over abstract `V Vp : RoundView …` variables, taking as
hypotheses exactly the facts the exec layer supplies (`hpr : pr = buildProposal Vp …`,
view inclusions as `eligibleBatch V.Xm V.r ⊆ eligibleBatch Vp.X0 V.r`, agreement
equalities), and instantiate it from a thin wrapper with `(V := roundView …)`
`(Vp := roundView …)` — instantiation is application-side unification and pays no
reduction. `acceptItem1_of_views` / `acceptItem1_cross` in `Analysis/Proofs/Exec.lean`
are the worked pair. This is the same force as section 18's "membership lemmas beat
equality lemmas": keep the giant terms on the application side, never in a position
a tactic must normalize.

A second cure for the same disease, when the consumer must produce a conclusion
*spelled* with the view projections (so the abstract-view core cannot state it): write
`rfl` projection lemmas (`roundView_agedVote`, `roundView_Fsel`, `roundView_Fvote`)
and `rw` them across the goal and hypotheses before the big application. The `rfl`s
themselves are cheap — after projection reduction both sides are syntactically equal,
so the checker never falls back to unfolding `agedCandidateTree`/`deriveBlockStates`
bodies — and after the rewrite the application unifies argument-by-argument.
`containment_cross` is the worked example.

A third cure, when a *proof* needs the view under a variable: `set V := roundView … with
hV` does NOT work — a set-bound local definition is delta-transparent and downstream
tactics (`rw`, applications of flat lemmas at `V`) still whnf into the giant term. The
opaque form is

    obtain ⟨V, hV⟩ : ∃ V0 : RoundView …, V0 = roundView x[j][q].st q r := ⟨_, rfl⟩
    rw [← hV] at haeq hpost   -- move the hypotheses onto the opaque variable

after which the proof behaves as if `V` had been an existentially obtained unknown.
Field facts like `V.u = q` close by `subst hV; rfl` (plain `rw [hV]` leaves the goal —
its trailing `rfl` check runs at reducible transparency and `roundView` is a regular
def). `signerSafetyExec` post-`ReleasedAt`-strengthening is the worked example.

## 20. Two validators at one instant: argue from records, not from monotonicity

The recurring wall in the round-agreement proofs is this. Two honest validators run
the *same* activation filter cutoff `a (r−1)`, and the round's derivations filter their
candidates through it. To compare their arg-maxes with the monotonicity lemmas
(`fcw_F_pair_mono`, `fcw_hmax_mono_of_F`, `fcw_hj_mono_of_F`) you must supply

    hfilter : ∀ C k, Activated (p's store) (a (r−1)) C k → Activated (v's store) (a (r−1)) C k

and that is **not derivable and not true in general**. Relay needs `Δ`; the two cutoffs
are the same instant. Several sessions were spent trying to route around it — widening
the crossing, adding a staggering predicate to excuse it, restating the conclusion as a
two-round disjunction. All of that was wasted.

**The move that works: stop comparing arg-maxes and start comparing records.**

    fcw_F_pair_record_of_pos / fcw_J_pair_record_of_pos

say a view's selected pair *is some accepted block's own recorded pair*, in that view's
own candidate set. Then a strict inequality between two validators is not an opaque
arg-max fact — it names a record one holds and the other does not, which is an event you
can charge, and the record relays with `Δ` to spare because it lives in a *view*, not at
an instant. Concretely, at each strict inequality:

1. the higher side's record gives the countable event (`ProcessesFinalizedHeight`,
   `AdmitsJustifiedHeight`);
2. the lower side's absence of a matching record is what
   `first…_of_divergence` needs, and you prove it by contradiction: a record at the lower
   side's cutoff *would* lift its own arg-max (`fcw_h_F_ge_of_record_view`,
   `fcw_h_j_ge_of_cutoff_record`), against the inequality.

Two consequences worth stating separately.

- **Widen the event to the round's widest view.** These predicates should read
  `upTo (Xone r)`, not the activation cutoff, because *both* the selection view
  `before (d r)` and the cutoff view `upTo (a (r−1))` sit inside it, so a record held by
  either validator counts. And the widening is free: `Xone r₀ + Δ = d_{r₀} + 2Δ ≤
  d_{r−1} + 6Δ = a_{r−1}` follows from `d_{r₀} ≤ d_{r−1}` alone, so the crossing works
  at `r₀ = r − 1` with `4Δ` to spare and the bridge still charges the round the
  divergence is observed at. Reading the event at the *cutoff* is what made the
  arithmetic look tight and forced the two-round disjunction.
- **Equal heights do not pin the block.** The arg-max key is height first, hash second,
  and the model does not assume hash injectivity. Identify the blocks through their
  certificates instead — `Witnessed.finCert` / `.justCert` and then Lemma 11 at one
  height (`finalized_unique_exec`) or Lemma 5 (`target_unique_exec`).

`fcw_F_agree_or_case4`, `fcw_J_agree_or_case3` and `roundView_agree_or_case` in
`Analysis/Proofs/Exec.lean` are the worked chain. No `hfilter` appears anywhere in them.

## 21. A charged-round disjunct must name the round

When a dichotomy's other branch is "the round is charged to case N", the disjunct has
to *pin the round*. These two look alike and only the second is worth anything:

    ∃ r₀ ≤ r, ∃ h, FirstProcessedFinalized x r₀ h     -- nearly vacuous
    ∃ h,          FirstProcessedFinalized x r  h     -- charges this round

Every height that is ever processed has a first round, so the first form is implied by
almost any execution and attaches to nothing. Lemma 51's budget is *rounds per distinct
finalized height in the window*; a disjunct that does not say which round is being
charged cannot be counted against it.

The temptation is real, because `exists_first_round` hands you the weak form for free
the moment you have `ProcessesFinalizedHeight x r h`. Resist it: go back and find the
fact that excludes the earlier rounds. In every case so far it was already available —
the validator that *lacks* the record at its own activation cutoff is the missing side
of `first…_of_divergence`, and relay does the rest. When the two sides are the same
validator at two of its own views (selection vs vote, vote vs action), that validator
plays both roles; `firstProcessedFinalized_of_sel_lt` is the worked instance.

Where the round genuinely cannot be pinned, say which two: `r ∨ r + 1` is the paper's
own "two rounds per distinct finalized height" and is countable. `≤ r` is not.

## 22. When to reach for `set_option maxHeartbeats`

Only after sections 19 and 20's cures are all in place. A dichotomy proof that case-splits
three ways, identifies two roots through their certificates, and runs three monotonicity
steps is genuinely large, and at some point the budget is the only thing left.

The order to try: `rfl` projection lemmas so `rw` aligns spellings instead of the unifier
reducing them; a named subset/membership lemma so a `rw [fcw_T]` never happens inside a
goal spelled with a `roundView` projection; each case branch factored into its own
theorem so the branches do not share one budget. `roundView_sel_agree_or_case` has all
three and still needed `set_option maxHeartbeats 800000` — the first in
`Analysis/Proofs/Exec.lean`.

Placement is the same trap as `omit` (section 15): `set_option … in` goes **before** the
docstring. Between docstring and `theorem` it fails with "unexpected token 'set_option';
expected 'lemma'".

## 23. Removing a global assumption: a per-node predicate plus an adapter

An execution-level assumption quantified over all nodes
(`CurrentClockDeliveries x : ∀ i p m, …`) is usually consumed at two or three *named*
nodes per theorem. Removing it wholesale is a 60-signature edit; the move that makes it
a handful is:

1. define the same thing at one node — `CurrentClockAt x p` — in `Spec/`, beside the
   quantified form;
2. give the quantified form an adapter: `CurrentClockDeliveries.atNode : … → ∀ p,
   CurrentClockAt x p`, one line;
3. convert theorems bottom-up, replacing the binder with one `CurrentClockAt` per node
   the proof stamps;
4. at every call site you are *not* converting, pass `hccd.atNode _`. The node is
   inferred, the caller keeps its own hypothesis, and nothing above it changes.

Step 4 is what stops the cascade. Without it each conversion propagates to its callers'
callers and the tree is broken for hours.

**Prefer the derivable form at the top.** The point of the exercise is usually that the
global assumption is *not* derivable while the per-node one is — here
`currentClockAt_of_awake` gets it from `SynchronizedClocks` plus one node being awake
throughout. So a statement that already assumes its nodes awake loses the hypothesis
outright, and one that does not keeps a per-node side condition, which is strictly better
than inventing an awakeness assumption the paper does not make for that node.

**Four costs, each one full build if got wrong.**

- **The new hypothesis must come after the node binder it names.** Dropping it where the
  old binder sat gives `Unknown identifier u`, because `{u v : Node}` is declared later.
  Move the node binder ahead of it:

      {u v : Node} (hcu : CurrentClockAt x u) (hcv : CurrentClockAt x v)
      (hsd : StrictDelivery gst x) (hv : ∀ n : Nat, x.Awake n v)

- **Callers pass it at the node binder's position**, not straight after `x`. Get it wrong
  and the error is an application type mismatch against whatever explicit argument
  preceded the node binder (`expected Synchrony …`), which reads like a different bug.
  Named arguments (`(hcu := …)`) sidestep this entirely and are worth it for a big sweep.
- **The deriving lemma has its own instance requirements.** `currentClockAt_of_awake`
  needs `[DecidableEq Act] [DecidableEq Res]`; machinery theorems that never touched a
  store may lack them, and the failure is `failed to synthesize DecidableEq Act` at the
  *call*, not the declaration.
- **Forward references bite.** If the deriving lemma sits below the section you are
  converting, nothing there can discharge its own stamps. Move the block up first — it is
  a pure relocation — rather than converting half the file and discovering it.

**Where it stops.** A theorem whose stamps are read at a node *obtained inside the proof*
(`obtain ⟨u, …⟩ := hproc`) has no binder to attach a hypothesis to. If the obtained node
carries honesty — `ProcessesFinalizedHeight` does — the stamp is still derivable, but only
through `HonestAwake`, which means adding that to the signature. That is a change of
assumptions, not of spelling, so stop and get it agreed rather than doing two dozen of
them in one diff.

Check the honesty component before assuming you are stuck: the `obtain` pattern in the
existing proof may be discarding it with `-`, which makes the node look anonymous when it
is not.

## 24. `lake env lean` lies about this library: pass `--setup`

Section 6 says to iterate in the scratchpad with `lake env lean <file>`. That is right for a
small file that imports the library. It is **wrong for checking a file of the library
itself**, and the failure mode is expensive: false timeouts.

Measured 2026-08-12 on `Analysis/Proofs/Exec.lean`, one source file, three invocations:

    lean FILE                                   -> 5 errors: whnf timeouts in
                                                   rootAdmitted_cross,
                                                   firstJustificationAdmitted_of_h_j_lt,
                                                   firstJustificationAdmitted_of_h_j_gt,
                                                   plus a kernel "unknown constant" cascade
    lean FILE --setup <module>.setup.json        -> 0 errors
    lake build Sts2MX.Analysis.Proofs.Exec       -> 0 errors, 214s

So `--setup` is necessary and sufficient. Lake generates it per module at
`.lake/build/ir/<Module path>/<Name>.setup.json`; it carries `importArts`, an exact olean
path for every import, where plain `lean` resolves imports through `LEAN_PATH` instead. Its
`options` field is empty here, so this is not an option difference. The mechanism past that
is unmeasured — do not repeat the mistake of reasoning about it instead of testing.

To check one library file faithfully, without Lake's trace machinery:

    lake env lean Protocols/decoupled-consensus/Sts2MX/Analysis/Proofs/Exec.lean \
      --setup .lake/build/ir/Sts2MX/Analysis/Proofs/Exec.setup.json

The setup file has to exist already, so this works only after that module has been built
once. Otherwise use `lake build <module>` — for one module of this library that is minutes,
not the ten of `make decoupled`.

**Also: a green `lake build` is not proof that a file elaborated.** Lake is trace-driven; on
a hash hit it replays stored warnings and still prints `Built X`. Confirm real work by the
elapsed time in the log line, or by the `.olean` mtime moving past the source's. A "decisive"
comparison between `lake env lean` and `lake build` is worthless until you have checked that.

The direction of the discrepancy is worth remembering: `lean` without `--setup` is
*stricter*, so it yields false **failures**, never false passes. A single-file check that
came back clean is still good evidence; one that failed needs re-running properly before you
believe it.
