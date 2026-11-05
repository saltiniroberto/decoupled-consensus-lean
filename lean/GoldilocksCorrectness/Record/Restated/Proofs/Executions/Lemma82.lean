module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Record
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Proofs.Executions.Wake
public import GoldilocksCorrectness.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeTick

@[expose] public section

/-!
# Lemma82, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma82.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 82, the honest attestations after the
healed round name the honest chain's entries, each at the slot whose update it followed, and its
part (b). The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq supportCutoff_cast
  supportCutoff_eq supportCutoff_slot supportCutoff_succ_times voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_lt_supportCutoff)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry)
open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans tick_attest_awake
  awakeSince_of_record_awake create_attestation_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **The tick that sends an honest attestation ran the update of a slot `s`.** A validator `v`
outside the adversary set after every step read as `t`, whose tick to `t` at step `i`
puts its attestation `a` on the wire, ticks at the support cutoff of some slot `s + 1`; it is an
updater of slot `s`; the attestation's source is a fast block of that update, held by `v` at step
`i` and in the state `v`'s tick to `t` leaves;
that state's saved confirmation of slot `s` is the source or a descendant of it; and `a` names the source's chain-state height and the root of the entry block
of that height on the source's chain.

Why: Lemma 49 over the record (`lem49_tick_attests`) puts the tick at the action time of its
round, which is the support cutoff of the round's second slot (`supportCutoff_succ_times`), with
the tick's input state awake for that slot, so the tick runs the confirmation update
(`tick_supportCutoff_confirmation`); the source is a fast block of the update
(`ac_to_fg_source_fast`), which leads to the saved confirmation
(`update_confirmation_fast_block_saved`), in the state the tick leaves; and the wake rule's test,
which the input state passed, puts `v` in the reader whose window ends at the tick, in its first case
or its second (`awake_of_tickInput_awakeSince_of_tick`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `i`: the step of the tick; `t`: its time; `v`: the attester; `a`: the
  attestation.

Read aloud: an honest attestation is sent by an updater of a slot at that slot's update, and names
the chain of a fast block of that update, which leads to the confirmation the update saved. -/
theorem attest_tick_update_source (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i t : ℕ) (v : V) (a : Attestation V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hl : x.lbl i = Event.tick v t)
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    ∃ (s : ℕ) (source C : Block V), t = M.supportCutoff S.C (s + 1) ∧
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) ∧
      source ∈ (x.tickOutput v t).fastBlocks ∧ source ∈ (x.st i v).tree ∧
      (x.tickOutput v t).savedConfirmation s = some C ∧ source.AncestorEq C ∧
      (M.chainStateOf S.C source).h = a.h ∧ a.T = (M.chainStateOf S.C source).T_h.root := by
  -- the tick, and the attestation it built
  obtain ⟨-, n', sent, hrun, ha, hst, -⟩ := (tick_send_step_outcome_per_step M F R E) hl hSent
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hti : x.tickInput v t = x.st i v := by
    unfold Trace.tickInput
    rw [hts]
  have hto : x.tickOutput v t = n' := by
    unfold Trace.tickOutput
    rw [hts, hst]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v t) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  obtain ⟨hT, hAF, source, head, hsrc, -, hAtt, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ha
  -- the spec's slot of a natural-number time is the layout's (`U`)
  have hsl : ∀ t' : ℕ, S.C.slot ((t' : ℕ) : Int) = M.slot S.C t' := fun t' => by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
  -- the time is the support cutoff of slot `s + 1`, with `s` the first slot of the round
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = S.C.round (M.slot S.C t) * S.C.R := ⟨_, rfl⟩
  obtain ⟨hslot, hround, hact, hcut⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_times M.toSlotLayout F.sched U)
      S (S.C.round (M.slot S.C t)) s hs
  rw [hslot, hround] at hact
  rw [hsl] at hT
  have ht : t = M.supportCutoff S.C (s + 1) := by
    have h : ((t : ℕ) : Int) = ((M.supportCutoff S.C (s + 1) : ℕ) : Int) := hT.trans hact.symm
    exact_mod_cast h
  subst ht
  have hsl1 : S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [hsl]
    exact hslot
  -- the tick ran the confirmation update of slot `s + 1`
  have hc : ((M.supportCutoff S.C (s + 1) : ℕ) : Int) =
      S.C.t_ (S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int)) + 2 * S.C.Δ := by
    rw [hsl]
    exact hcut
  have hUpd := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hrun hInvT hc hAF
  rw [hsl1] at hUpd
  -- the source is a fast block of the update, which leads to the confirmation saved for slot `s`
  have hfast : source ∈ n'.fastBlocks :=
    GoldilocksCorrectness.Record.Proofs.Routines.ac_to_fg_source_fast M _ n' source hsrc
  obtain ⟨C, hC, hsrcC⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 s) hUpd hfast
  rw [Nat.add_sub_cancel] at hC
  -- the wake rule's test passed: `v` is awake from the duty window of slot `s + 1` up to its tick,
  -- the stored wake time being the initial one or the value of a tick after its last restart
  -- (`awake_of_tickInput_awakeSince_of_tick`), the reader's two cases
  obtain ⟨τ, hτ, hτle⟩ := hAF
  rw [hsl1] at hτle
  have hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1))
      (M.supportCutoff S.C (s + 1)) := by
    have hcases := (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨i, hl⟩ hτ
    rw [hts] at hcases
    refine E.mem_activeThroughoutToTick_of_awakeThroughoutToTick ?_
    rcases hcases with ⟨-, hall⟩ | ⟨k₁, τ', hk₁, hl₁, hτ', hawk⟩
    · exact Activity.mem_awakeThroughoutToTick_of_forall hl hall
    · exact Activity.mem_awakeThroughoutToTick_of_tick (hτ' ▸ hτle) hk₁.le hl hl₁ hawk
  -- the source is a block of `v`'s tree at the step of the tick
  have hsT : source ∈ (x.st i v).tree := by
    rw [← hti]
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F _ source).1
      (GoldilocksCorrectness.Record.Proofs.Routines.ac_to_fg_source_mem M F _ n' source hsrc)).1
  -- the attestation's height and root are the source's chain state's
  obtain ⟨τ', -, -, rfl⟩ := hAtt
  refine ⟨s, source, C, rfl, hv, ?_, hsT, ?_, hsrcC, rfl, rfl⟩
  · rw [hto]
    exact hfast
  · rw [hto]
    exact hC

/-- **Lemma 82 (b), the honest attestation's entry at its slot.** The proof; the audited
statement is in `Statements/Executions/HealedAttestationStatements.lean`. Lemma 82
(`lem82_honest_attestations_on_chain`) is this tuple with the updater and its confirmation put
together as `OnHonestChainAt`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `i`: the step of the tick; `t`: its time; `v`: the attester; `a`: the attestation.

Read aloud: the entry an honest attestation names was confirmed by the attester at the slot whose
update the attestation followed, and the attestation was sent at that update's time. -/
theorem lem82b_entry_at_slot (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i t : ℕ) (v : V) (a : Attestation V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hl : x.lbl i = Event.tick v t) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ t)
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    ∃ (s : ℕ) (E C : Block V), s₀ ≤ s ∧ t = M.supportCutoff S.C (s + 1) ∧
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C ∧
      E.AncestorEq C ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = a.h ∧ a.T = E.root := by
  obtain ⟨s, source, C, ht, hv, -, -, hSaved, hsrcC, hh, hT⟩ :=
    (attest_tick_update_source M F U) S A x R i t v a E hl hSent
  subst ht
  -- the healed slot is at most `s`
  have hs₀ : s₀ ≤ s := by
    by_contra hlt
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout
      F.sched) S (show s + 1 < s₀ + 1 by omega)
    omega
  -- the entry block of the source's height on its chain
  obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C source
  exact ⟨s, (M.chainStateOf S.C source).T_h, C, hs₀, rfl, hv, hSaved, ancestorEq_trans hE3 hsrcC,
    hE1, hE2.trans hh, hT⟩

/-- **Lemma 82, the honest attestations after the healed round name the honest chain's
entries, each at the slot whose update it followed.** The proof; the audited statement is in
`Statements/Executions/HealedAttestationStatements.lean`. Lemma 82 (b), `lem82b_entry_at_slot`,
with the updater and its saved confirmation put together as `OnHonestChainAt`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot.

Read aloud: from the action time of the healed round on, every attestation an honest awake validator
sends is sent at the update time of a slot `s`, and names the honest chain's entry block of slot `s`
at the attestation's height. -/
theorem lem82_honest_attestations_on_chain (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    :
    HonestAttestationsOnChain M S A x s₀ (M.supportCutoff S.C (s₀ + 1)) := by
  intro i t v a hl ht₀ _ hSent
  obtain ⟨s, E', C, hs₀, ht, hv, hSaved, hEC, hE, hEh, hEr⟩ :=
    (lem82b_entry_at_slot M F U) S A x R s₀ i t v a E hl ht₀ hSent
  exact ⟨s, E', hs₀, ht, ⟨hs₀, v, hv, C, hSaved, hEC⟩, hE, hEh, hEr⟩

end GoldilocksCorrectness.Record.Proofs.Executions

