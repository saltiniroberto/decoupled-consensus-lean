module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HeldRelayed
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Relay
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# What an honest validator serves of the class `acObject`, it put on the wire itself

The hypothesis `hrelay` of the bridge from the pushed catch-up to the sync fact
(`syncedWithin_of_envFactsSync`, `Record/Restated/Proofs/Executions/AsyncDelivery.lean`) for the
class `acObject` (the blocks and the Goldfish votes), at the minimal selection `servesMin M S.C`,
which serves no genesis block. The block half is `holdsG_relayed_block`
(`HeldRelayed.lean`); the vote half is `pool_vote_relayed` (`Relay.lean`), which needs the uniform
slot layout and the atomic shape of the trace.

- `pool_vote_relayed_entry`: `pool_vote_relayed` at the step the vote entered the pool, which holds
  it after that step.
- `servesMin_relayed_ac`: `hrelay` at the entry step: an object of the class `acObject` that an
  honest validator serves at a time from its state after a step was put on the wire by that
  validator, honest then, at an earlier step after which it already served it at that time.
- `syncedWithin_servesMin_ac_of_envFactsSync`: the pushed catch-up at `acObject` gives the sync fact
  over `servesMin M S.C` at `acObject`.
- `syncedWithinOutside_servesMin_ac_of_envFactsOutside`: the same, both suspended on one
  asynchronous period `[b₀, b₁)`.
- `syncedWithin_servesMin_ac_of_envFacts`, `syncedWithin_servesMin_fg_of_envFacts`: the same from the
  environment's facts at `Δw = Δ` (the abbreviation `EnvFacts`), at `Δs = Δ`.

A block served after the entry step is served then: the tree holds it from that step on, it is not
the genesis block, and the finalized block after the entry step is an ancestor of the finalized
block after the later step (`F_ancestorEq_of_le`), hence compatible with every block compatible with
the later one. A vote served after the entry step is served then: the pool holds it from that step
on, and the slot test does not read the node state.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions
open Goldilocks.Sts (Setup)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts EnvFactsSync
  SyncedWithin)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts holdsG servesMin)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans ancestorEq_compatible compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- A Goldfish vote of a validator's pool at a step was put on the wire by that validator, as a
Goldfish-vote object, at an earlier step at which it was honest, after which its pool holds the
vote: the step at which the vote entered the pool (`pool_vote_relayed` at that step).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `hWS`: the trace is
  wake-shaped; `k`: the step; `w`: the validator; `s`: the slot; `vote`: the vote; `i`: the step
  of the send.

Read aloud: a vote `w` holds was re-sent by `w`, honest then, at the step after which it first
held it. -/
theorem pool_vote_relayed_entry (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (k : ℕ) (w : V) (s : Slot) (vote : GoldfishVote V)
    -- `w`'s pool of slot `s` holds `vote` after `k` steps
    (hv : vote ∈ M.votesHeldSet (x.st k w) s) :
    ∃ i < k,
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      w ∉ A.corrupted i ∧ vote ∈ M.votesHeldSet (x.st (i + 1) w) s := by
  induction k with
  | zero =>
      obtain ⟨i, hi, -⟩ := (pool_vote_relayed M F U) S A x R E 0 w s vote hv
      exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
      by_cases hk : vote ∈ M.votesHeldSet (x.st k w) s
      · obtain ⟨i, hi, h1, h2, h3⟩ := ih hk
        exact ⟨i, by omega, h1, h2, h3⟩
      · obtain ⟨h1, h2, -⟩ := (step_pool_relayed M F U) S A x R E
          (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv)
          (fun h => hk (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 h))
        exact ⟨k, by omega, h1, h2, hv⟩

/-- `hrelay` at the entry step for the class `acObject` at the minimal selection: a block or a
Goldfish vote that an honest validator serves at `t` from its state after the step `k` was put on
the wire by that validator, honest then, at an earlier step after which it already serves it at
`t`. A served block is not the genesis block, so `tree_block_relayed_entry` applies;
the finalized block only moves to a descendant (`F_ancestorEq_of_le`), so the block is compatible
with the earlier finalized block too. A served vote is held, so `pool_vote_relayed_entry` applies;
the slot test does not read the node state.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `hWS`: the trace is
  wake-shaped; `k`: the step; `u`: the validator; `o`: the object; `t`: the time.

Read aloud: every block and Goldfish vote an honest validator serves it put on the wire itself,
honest then, once it served it. -/
theorem servesMin_relayed_ac (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)

    (k : ℕ) (u : V) (o : NamedObject V) (t : ℕ)
    -- `o` is a block or a Goldfish vote
    (hok : acObject o)
    -- `u` is outside the adversary set at the time of the step `k`
    (hu : u ∉ A.corrupted k)
    -- `u` serves `o` at `t` from its state after `k` steps
    (hh : servesMin M S.C (x.st k u) t o) :
    ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧ servesMin M S.C (x.st (i + 1) u) t o := by
  cases o with
  | block B =>
      obtain ⟨i, hik, hs, hon, -, hin⟩ :=
        (tree_block_relayed_entry M F) x R E (k := k) (v := u) hh.1 hh.2.2
      refine ⟨i, hik, ⟨hs, hon⟩, hin, ?_, hh.2.2⟩
      -- the finalized block after the entry step is an ancestor of the one after `k`
      have hF := (F_ancestorEq_of_le M F) x R E u (Nat.succ_le_of_lt hik)
      rcases (compatible_iff _ _).1 hh.2.1 with h | h
      · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hF h))
      · exact (compatible_iff _ _).2 (ancestorEq_compatible hF h)
  | gfVote vote =>
      obtain ⟨i, hik, hs, hon, hin⟩ :=
        (pool_vote_relayed_entry M F U) x R E k u vote.slot vote hh.1
      exact ⟨i, hik, ⟨hs, hon⟩, hin, hh.2⟩
  | attest a => exact hok.elim

/-- The pushed catch-up at the class `acObject` gives the sync fact over the minimal selection at
`acObject`: `syncedWithin_of_envFactsSync` with `hrelay` from `servesMin_relayed_ac`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `hΔ`: `1 ≤ Δ'`; `E`:
  the synchronous promises at `acObject`;

Read aloud: the pushed catch-up gives the sync fact for the blocks and votes a holder serves. -/
theorem syncedWithin_servesMin_ac_of_envFactsSync (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {Δ' Δw GST : ℕ}

    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ' Δw ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔA : (Δ' : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ' Δw ≤ Δs)
 :
    SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST := by
  exact (syncedWithin_of_envFactsSync M) R E hΔA hΔw
    (fun k u o hok hu hh => by
      obtain ⟨i, hik, hs, hin⟩ := (servesMin_relayed_ac M F U) x R E.toEnvFactsBy k u o (x.clockValue k u) hok hu hh
      exact ⟨i, hik, hs, (servesMin_of_le_clockValue M F) S
        (E.toEnvFactsBy.clockValue_mono (Nat.succ_le_of_lt hik) hu) hin⟩)

/-- The pushed catch-up at the class `acObject`, suspended on the asynchronous period `[b₀, b₁)`,
gives the sync fact over the minimal selection at `acObject` suspended on that period:
`syncedWithinOutside_of_envFactsOutside` with `hrelay` from `servesMin_relayed_ac`, which reads no
delivery promise.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `hΔ`: `1 ≤ Δ'`; `E`:
  the promises at `acObject` suspended on `[b₀, b₁)`;

Read aloud: the suspended pushed catch-up gives the suspended sync fact for the blocks and votes a
holder serves. -/
theorem syncedWithinOutside_servesMin_ac_of_envFactsOutside (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {Δ' Δw GST b₀ b₁ : ℕ}

    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ' Δw ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁)
    {Δs : ℕ} (hΔA : (Δ' : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ' Δw ≤ Δs)
 :
    GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinOutside A x (servesMin M S.C)
      acObject (releaseOf M S.C) ΔRedeliver Δs GST b₀ b₁ := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.syncedWithinOutside_of_envFactsOutside M) R
    E hΔA hΔw
    (fun k u o hok hu hh => by
      obtain ⟨i, hik, hs, hin⟩ := (servesMin_relayed_ac M F U) x R E.toEnvFactsBy k u o (x.clockValue k u) hok hu hh
      exact ⟨i, hik, hs, (servesMin_of_le_clockValue M F) S
        (E.toEnvFactsBy.clockValue_mono (Nat.succ_le_of_lt hik) hu) hin⟩)

/-- The environment's facts at `Δw = Δ` (the abbreviation `EnvFacts`) give the sync fact over the
minimal selection at `acObject`, at the sync delay `Δ S`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts at `Δ S`; `hWS`: the
  trace is wake-shaped.

Read aloud: where a waking validator is promised its backlog within `Δ`, what honest active
validators serve spreads within `Δ`. -/
theorem syncedWithin_servesMin_ac_of_envFacts (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {GST : ℕ}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsSync A x ΔClockAhead ΔClockBehind ΔNet (Δ S) ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
 :
    SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver (Δ S) GST := by
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  have hle : (ΔNet : ℝ) ≤ Δ S := by linarith
  exact (syncedWithin_servesMin_ac_of_envFactsSync M F U) x R E (by linarith)
    (max_le (by exact_mod_cast hle) le_rfl)

/-- The environment's facts at `Δw = Δ_F` for the attestations give the sync fact over the minimal
selection at `fgObject`, at the sync delay `Δ_F S`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E_F`: the environment's facts at `Δ_F S` for the
  attestations; `E`: the environment's facts at `Δ S` for the blocks and votes, which the relay
  facts read;

Read aloud: where a waking validator is promised its attestations within `Δ_F`, the attestations
honest active validators serve spread within `Δ_F`. -/
theorem syncedWithin_servesMin_fg_of_envFacts (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x) {GST GSTe : ℕ}
    {ΔRedeliver} {ΔNet_F : ℕ} {ΔClockAhead ΔClockBehind : ℝ} (E_F : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsSync A x ΔClockAhead ΔClockBehind ΔNet_F (Δ_F S) ΔRedeliver GST (releaseOf M S.C) fgObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
 :
    SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver (Δ_F S) GST := by
  have hA := E_F.ahead_nonneg
  have hB := E_F.behind_nonneg
  have hle : (ΔNet_F : ℝ) ≤ Δ_F S := by linarith
  exact (syncedWithin_servesMin_fg_of_envFactsSync M F) x R E_F (by linarith)
    (max_le (by exact_mod_cast hle) le_rfl) E hNet hSkew hRedeliver

end GoldilocksCorrectness.Record.Proofs.Executions
