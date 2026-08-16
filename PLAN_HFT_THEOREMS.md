# Plan: prove Theorems 8, 9, 10 of the companion paper

A working plan for the next sessions (written 2026-08-17 for a fresh model instance).
**Delete this file when the three theorems are proved** — CONTEXT.md carries the durable
record; this is scaffolding.

## Ground rules, before anything else

1. Read `CLAUDE.md` and follow it. In particular: no new `axiom`s, no `native_decide`;
   `sorry` only as working state; write `sorry`/`admit` in backticks inside any comment or
   docstring (the check is a grep); `make dev` to build, `make check` to know you are done.
2. **Invoke the `lean-proof-idioms` skill before the first proof.** Every friction below
   has a section there. Iterate in the scratchpad with `lake env lean <file>` run from the
   repository root; move code in only when it compiles.
3. **Do not change any statement in `lean/Analysis/HftTheorems.lean` without checking with
   Roberto first.** The known risk is recorded in CONTEXT.md (2026-08-16): the disjuncts
   pin their E1 evidence to blocks the store accepted (`∃ Ca ∈ S'.T, IncludedOn a Ca`) or
   to the named chain `B_F`. If a proof cannot place the evidence there, stop and ask.
4. Commit at every proved milestone, `make dev` and `make cites` first (`make check` stays
   red until all three theorems land — say so in commit messages). MAPPING.md status flips
   wait for instruction; CONTEXT.md is updated as you go.
5. The companion paper is `latex-specs/full/height_filter_and_timeouts.tex`; its Section
   3.1 with all the proofs to follow is lines 571–752. Citations use the `hft:` label
   prefix, checked by `make cites`.

## What already exists (verify signatures by reading, do not trust this list blindly)

The three targets are the `sorry`s in `lean/Analysis/HftTheorems.lean`:
`thmFinalityAcceptance` (Thm 8), `thmLockIn` (Thm 9), `thmOrderIndependence` (Thm 10).
Read their docstrings first; each carries the paper's sentence verbatim.

Proved machinery, by file:

* `lean/Analysis/Proofs/Irreversibility.lean` — node-state read-backs over the framework's
  configuration writes; `onBlock_F`/`onBlocks_F` (`F` only descends); `exec_step_F`;
  `localIrreversibility`, `reachesFrom_F` (Theorem 3).
* `lean/Analysis/Proofs/StoreInvariants.lean` — `exec_node_invariant` (the walker: a store
  predicate true at `Store.gen` and preserved by `receive` holds at every held store);
  the `F ⪯ J` chain (`onBlock_FJ`, `reaches_FJ`, `reachable_FJ`); Theorem 7's pieces
  (`F_preceq_R`, `getConfirmed_F`, `forkChoiceConsistency`); the recorded-replay bridge
  (`reaches_recorded`: a held store's `S.σ B = some σB` gives `postState B = .state σB`).
* `lean/Analysis/Proofs/StoreProvenance.lean` — `StoreInv`, the eight-field bundle, with
  `reaches_storeInv`. Fields: `recorded`, `domT` (`B ∈ S.T ↔ (S.σ B).isSome`), `parentT`,
  `jProv` (a recorded state carries `(S.J, S.h_j)`), `fProv` (`S.F` genesis or a recorded
  state's `F`), `keyDom` (recorded justified pairs on the current `F`'s chain have key at
  most the store's), `hmaxLe`/`hmaxEx`. Also the `spec` lemmas (`updateJustified_spec`,
  `updateFinalized_spec` — record equations for the two updates), `replay_postState`,
  `update_keeps`.
* Healing side (already kernel-clean, consumed through the bridge):
  `lemPastFinalized` (Lemma 10) and `lemFinalizedChain` (Lemma 11) in
  `lean/Analysis/Lemmas.lean` — read their exact statements; their internals are in
  `lean/Analysis/Proofs/Finality.lean` (`pastFinalized_evidence` etc.), reusable directly.
  `Certified` and `certified_of_blockPostState` in `lean/Analysis/Proofs/Provenance.lean`
  give, for any `BlockPostState`, the commit/target quorums and **anchors** behind the
  recorded `(J, h_j)` and `(F, h_F)` pairs — anchors are the paper's `hft:lem:fresh-equiv`
  (`σ[J].h = h_j`). `Chained` (`chained_of_blockPostState`, Ancestry.lean) gives
  `F ⪯ J ⪯ L` and `h_F ≤ h_j < h` for every recorded state. `blockPostState_of_postState`
  (Determinism.lean) crosses from the bridge's `postState B = .state σB`.
* Height/slot facts: `postState_h_le` (heights monotone along `⪯` for replayable chains)
  and the slot lemmas (`prec_slot_lt` etc.) in `lean/Analysis/Proofs/ChainTarget.lean`.
* Quorum arithmetic: `quorumIntersection` in `lean/Analysis/Proofs/Weights.lean`.

The paper's own proofs (lines 647–752) are the roadmap: `certchain` (Lem 8), `upgrade`
(Lem 9), `viable-finalized` (Lem 10), then Thms 8–10. Per the selection rule, those
lemmas get **stated** in Lean only if you find naming them as statements of record useful;
otherwise prove their content as `Proofs.` machinery.

## Milestones, in dependency order

Each milestone is one commit. Store-level lemmas should take `(hinv : StoreInv S)` and,
where needed, `(hFJ : S.F ⪯ S.J)` as hypotheses — both are available at every held store
(`reaches_storeInv`, `reaches_FJ`). Do not add fields to `StoreInv` unless unavoidable;
its preservation proof is expensive to rework.

### A. Records persist, `T` grows, records give certificates

Small lemmas the later milestones consume constantly:

1. `onBlock_record_mono : S.σ B = some σB → (onBlock S B').σ B = some σB` — from
   `update_keeps` plus the `onBlock` split (mirror `onBlock_recorded`'s structure); lift
   to `reachesFrom_record : ReachesFrom x p S S' → S.σ B = some σB → S'.σ B = some σB`
   with a step walk like `exec_step_F`'s. Likewise `onBlock_T_mono : S.T ⊆ (onBlock S B').T`
   and its `ReachesFrom` lift.
2. `record_certified`: for `StoreInv S` and `S.σ B = some σB`, package what healing gives:
   `postState B = .state σB` (bridge), `BlockPostState σB`, `Chained σB`, `Certified`'s
   quorums with `IncludedOn · B`. Write one lemma or a small bundle — this is the interface
   every quorum argument below uses. Note `B ∈ S.T` via `domT` (`Option.isSome_iff_exists`).

### B. The upgrade argument (paper Lemma 9, `hft:lem:upgrade`)

Target shape (store-level):

    upgrade : StoreInv S → S.F ⪯ S.J →
      S.σ B = some σB → σB.J = F → σB.h_j = h_f →
      (external finality: postState B_F ≠ invalid, (postState' B_F).F = F,
        (postState' B_F).h_F = h_f) →
      F ⪯ S.J ∨ ⟨evidence: weight ≥ 2q − W of E1 pairs, each message IncludedOn B_F
        or on a block of S.T⟩

Proof route, following the paper's but with `keyDom` replacing the offering history:

1. `h_f = 0`: healing's `Certified.fin0`-analogue on `σB`... check what pins `F` at
   `h_j = 0`; if `σB.h_j = 0 → σB.J = genesis` is not already derivable from `Certified`
   or `Chained`, prove it as a small block-post-state fact first (genesis case of the
   replay). Then `F = genesis ⪯ S.J` by `genesis_preceq`.
2. Case `¬ S.F ⪯ F`: `fProv` gives `S.F` genesis (contradiction: `genesis_preceq`) or a
   recorded finalized pair; `lemFinalizedChain` on that pair versus the external
   `(F, h_f)` pair gives `F ⪯ S.F ⪯ S.J` (done), `S.F ⪯ F` (contradiction), or evidence.
   Watch the direction of `lemFinalizedChain`'s inclusions when relocating evidence.
3. Case `S.F ⪯ F` (that is, `S.F ⪯ σB.J`): `keyDom` gives `h_f ≤ S.h_j`.
   * `h_f < S.h_j`: `jProv` names the recorded `(S.J, S.h_j)`; its `Certified.just`
     anchor puts `postState S.J` at height `S.h_j > h_f`; healing Lemma 10
     (`lemPastFinalized` — read which subject fits; fall back to
     `Proofs.pastFinalized`/`pastFinalized_evidence` internals) yields `F ⪯ S.J` or E1
     evidence against the external commit quorum on `B_F`.
   * `h_f = S.h_j`: target quorum for `(S.h_j, S.J)` (`Certified.just` on `jProv`'s
     record) against commit quorum for `(h_f, F)` (external, on `B_F`):
     `quorumIntersection` gives a `2q − W` set; each signer's pair is E1 unless
     `S.J = F`, in which case done. This is `Finality.lean`'s own pattern — copy it.

### C. Viability (paper Lemma 10, `hft:lem:viable-finalized`) and leaf machinery

1. Leaf existence: in a `StoreInv` store, every `B₀ ∈ S.T` has a leaf `L ∈ S.T` with
   `B₀ ⪯ L` (no proper descendant of `L` in `S.T`). Pick the max-slot element of
   `S.T.filter (B₀ ⪯ ·)` (`Finset.exists_max_image`); a proper `T`-descendant would have a
   strictly larger slot (`prec_slot_lt` needs replayability — every `T` member is
   recorded, hence replayable, via `domT` + bridge) and still sit above `B₀`.
2. `finalized_viable`: under `StoreInv S`, external pair `(F, h_f)` on `B_F` with `h_f ≥ 1`,
   and a recorded `σB` with `σB.J = F, σB.h_j = h_f`: `F ∈ viableTree S` or evidence.
   Route: `Chained σB` gives `σB.h > σB.h_j = h_f`, so `hmaxLe`/`hmaxEx` put
   `S.hmax > h_f`; the `hmaxEx` witness has height `> h_f`, healing Lemma 10 gives
   `F ⪯ witness` or evidence; extend to a leaf via C.1 (heights only grow upward:
   `postState_h_le`), whose height equals `S.hmax ≥ S.hmax − 1`. Unfold `viableTree`'s
   filter — membership needs the leaf recorded (`domT`) for the `Option.any` height read.

### D. Theorem 8 (`thmFinalityAcceptance`)

1. Execution-side: locate the accepting step. Prove
   `exec_step_shape : storeAt x p (i+1) = storeAt x p i ∨
      ∃ m, storeAt x p (i+1) = Decoupled.receive (storeAt x p i) m`
   (same `Step.elim` walk as `exec_step_F`). Then a first-change search between the
   `ReachesFrom` indices: `B ∉ S.T` (hence unrecorded, `domT`) and recorded at the far
   end give a step `k` where `onBlock (storeAt x p k) B'` first records `B`; inside
   `onBlock`'s accept branch the written key is `B'`, so `B' = B` and the written state is
   `σB` (replay determinism through the bridge).
2. Store-side core, at the accepting store `S₀` (which satisfies `StoreInv` and `F ⪯ J`):
   run `updateJustified_spec`/`updateFinalized_spec` on the accept branch. If finalization
   fired, `F₂ = σB.F` and Theorem 3 carries it to `S'`. If not, one of its three
   conditions failed:
   * `¬ S₁.F ≺ σB.F`: either equal (done via Theorem 3) or `¬ S₁.F ⪯ σB.F` — then
     `fProv` + `lemFinalizedChain` (as in B.2) gives `σB.F ⪯ S₁.F` (done) or evidence.
   * `¬ σB.F ⪯ S₁.J`: `σB`'s own chain contains the justification that finalized `σB.F` —
     `Certified.fin` on `σB` provides the commit *and target* quorums at `(σB.h_F, σB.F)`
     with the anchor; use milestone B's argument against `S₁`'s justified pair. Mind that
     `S₁` here is the intermediate store (post-writes, pre- or post-`updateJustified`);
     its `J` is either `S₀.J` (use `jProv` of `S₀`, records unchanged) or `σB.J`
     (then `σB.F ⪯ σB.J` by `Chained` — direct contradiction).
   * not viable: milestone C.2 at `S₁` — its `StoreInv`-components hold (they are the
     `have`s of `storeInv_accept`; either re-derive them or factor `storeInv_accept` so
     the intermediate facts are reusable).
3. Evidence transport: everything found at step `k` moves to `S'` by A.1 (`T` monotone,
   records persist); `IncludedOn` is about chains, not stores, so it moves for free.
4. Wire `thmFinalityAcceptance := Proofs.…`, re-measure axioms, commit.

### E. Theorem 9 (`thmLockIn`)

Mostly composition, **applied at `S'` directly** — do not chase `J` across steps (`J` is
not `⪯`-monotone; the paper's "at all future times" is handled by re-applying upgrade at
the future store, where the record still exists by A.1):

1. `F ⪯ S'.J`: milestone B at `S'` (record persisted, `StoreInv S'`, `reaches_FJ`).
2. `F ∈ viableTree S'`: milestone C.2 at `S'`.
3. `∀ C, GetConfirmed S' C → F ⪯ C`: unfold `GetConfirmed`; cascade cases on `Store.R`:
   * `R = S'.J`: `F ⪯ S'.J ⪯ C` by 1 and the conjunct `S'.R ⪯ C`.
   * `R = S'.F` (so `S'.hmax ≠ S'.h_j + 1`, hence `S'.hmax ≥ S'.h_j + 2 ≥ h_f + 2` using
     `keyDom` for `h_f ≤ S'.h_j`): `C` is recorded (`GetConfirmed`'s `get` conjunct) at
     height `≥ S'.hmax − 1 > h_f`; healing Lemma 10 gives `F ⪯ C` or evidence.

### F. Theorem 10 (`thmOrderIndependence`) — the largest; consider splitting sessions

1. The fold-equals-execution core:
   `storeAt_eq_fold : storeAt x p i = onBlocks Store.gen (deliveredBlocks x p i)` —
   induction on `i` over `exec_step_shape` (D.1); `deliveredBlocks` appends exactly on
   the `deliver`-to-`p` label. Mechanical; do it first, it also retires the header claim
   in `HftTheorems.lean` that a store is the fold of its deliveries.
2. The fold-level order independence, following the paper's four-part proof (lines
   712–737). Map before proving:
   * *`F` part*: `{σB.F : recorded}` is a chain up to evidence (`lemFinalizedChain`
     pairwise); its maximum `F_max` is reached in every order — needs Theorem 8's store
     core (D.2) at the step processing the `F_max`-carrying block, plus Theorem 3.
   * *`hmax` part*: max-height block descends from `F_max` (healing Lemma 10) and is
     accepted in every parent-first order — an induction over the fold using `ParentFirst`.
   * *`J` part*: the lex-max over high descriptors is order-free — `keyDom` plus B's
     equal-height E1 argument.
   * *outputs*: once `(F, J, h_j, hmax)` and the subtree agree, `viableTree` and
     `GetConfirmed` agree — needs recorded-state agreement on the shared subtree, which
     is replay determinism (the bridge, both sides).
   Expect this to demand statements for the paper's Lemma 8 (`hft:lem:certchain`) as
   named machinery. If the induction wants an invariant neither paper states, follow the
   skill's §4 method and record it.
3. Evidence in Theorem 10's disjunct may come from either store; both `T`s are available
   in the statement — check placement before finishing, per ground rule 3.

## Known frictions (all hit while building the existing files — details in CONTEXT.md)

* Goals and hypotheses over record literals: `rw`/`omega` fail on unreduced projections —
  re-ascribe (`have h' : <reduced form> := h`) or `dsimp only at h ⊢`.
* `omega` does not split disjunctive *hypotheses* — `rcases` them first. It also cannot
  see through def-wrapped notation (`w(Q)≥q`); re-ascribe.
* `split_ifs at h` silently closes contradictory branches — do not write bullets for them.
* `set` is delta-transparent; prefer `obtain ⟨V, hV⟩ : ∃ v, v = big := ⟨_, rfl⟩` when a
  term must stay opaque (skill §19).
* The write-confining hook rejects shell heredocs containing `/--` or absolute scratchpad
  paths: write python scripts into the scratchpad with the Write tool and run them by path.
* `lake env lean` needs the repo root as cwd and fresh oleans: after editing a dependency,
  `lake build <module>` before trusting single-file checks.
* Finset membership may elaborate through `SetLike.instMembership`; `Finset.mem_singleton`
  rewrites can need a defeq re-ascription first.

## Definition of done

All three `sorry`s in `HftTheorems.lean` replaced by one-line calls into `Analysis/Proofs/`;
`make check` green; `#print axioms` on each of the six theorems shows
`[propext, Classical.choice, Quot.sound]`; CONTEXT.md updated per milestone; this file
deleted in the closing commit.
