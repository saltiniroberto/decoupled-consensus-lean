module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundBaseUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma80UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.RoundBaseUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma80UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Proofs.Executions.NetworkUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89rTargetsUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89rTargetsUpTo.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the round's attestations in the next
proposer's pool, the round's height advancing, and Lemma 89r, each with the premise that every
attestation a member put on the wire at the proposal's height is a target, with the delivery
premises up to the bound the theorems read.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_le_of_le
  slot_add_two_le_of_delivery supportCutoff_eq supportCutoff_le_slotStart_succ supportCutoff_mono
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_pool)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated LocksRevoked)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes FrameShape
  ProposalCountedVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? compatible_of_ancestorEq_compatible ancestorEq_compatible
  genesis_ancestorEq)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **`round_attestations_in_pool` with the targets premise (a copy).** The hypotheses and the
first conjunct of `round_attestations_in_pool` (`Proofs/Executions/Lemma80.lean`); the second
conjunct reads: when every attestation a member of `Q` put on the wire at a tick at a time
`t' ≤ a`, at the height `H` of `B`'s chain state, is
a target, then `q`'s pool before `c₁` holds a target of every member of `Q` at `H` naming `T`.

Why: as the original's first conjunct (Lemma 61 at each member, `record_content_sent` for an
attestation already sent), each attestation found being one of the member's, at a tick up to `a`,
at `H`, so a target by the premise.

The variables: as `round_attestations_in_pool`.

Restated with the delivery premises up to `c₁`: each member's attestation, sent by the support
cutoff of slot `s + 1` and from `tq` on, reaches `q` one delay later, by `c₁`,
as `round_attestations_in_pool_upTo`.

The variables:
- `M`: the model; `F`: its facts.

Read at the validators' own ticks: each member's update, locks, frame, tree and
record are read in the state its tick to the support cutoff of slot `s + 1` (its locks: to the
vote time of slot `s + 1`) starts from, each member ticks to that cutoff active from the trace's
start or from its own tick to a clock value at most `duty_window_start S.C (s + 1)`, and `q`'s
pool is read in the state its tick `kQ` to the clock value `c₁` starts from, `q` active at every
step from the real time `tq` up to that tick.

Read aloud: every member of `Q` attests for `B`'s height and `T_h` root and the attestation is in
the next honest proposer's pool before its slot starts; when every attestation a member put on the
wire at `B`'s height is a target, a target of every member is there, with the delivery premises up
to the bound. -/
theorem round_attestations_in_pool_targets_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST r s c₁ tq : ℕ) (Q : Finset V) (B : Block V) (q : V)
    (φ : V → Height) (ρ : V → Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds are less than one delay (the members' lock entries at their ticks; as
    -- `round_attestations_in_pool_upTo`)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST release fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks c₁) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject release ΔRedeliver Δs_F GST c₁)
    (hs : s = r * S.C.R)
    (hGST : GST ≤ M.supportCutoff S.C (s + 1))
    (ht₁ : M.supportCutoff S.C (s + 1) + Δ_F S ≤ c₁)
    (hBslot : B.slot = s)
    (hv : ∀ v ∈ Q, v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hUpd : ∀ v ∈ Q, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) →
      M.savedConfirmation n' s = some B ∧ B ∈ M.fastBlocks n')
    (hLocks : ∀ v ∈ Q, ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hShape : ∀ v ∈ Q, FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1))) (ρ v) (φ v))
    (hRoot : ∀ v ∈ Q, (ρ v).AncestorEq B)
    (hBin : ∀ v ∈ Q, B ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree)
    (hLockBox : ∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root)
    (hBHeight : ∀ v ∈ Q, φ v ≤ (M.chainStateOf S.C B).h)
    -- `c₁` is at least one FG delay or one sync delay after `GST` and after `tq`
    (hGSTq : GST + max (Δ_F S) Δs_F ≤ c₁)
    (htq : tq + max (Δ_F S) Δs_F ≤ c₁)
    (kQ : ℕ) (hkQ : x.lbl kQ = Event.tick q c₁)
    (hwin : ∀ i : ℕ, (tq : ℝ) ≤ x.time i → i ≤ kQ → q ∈ A.active i)
    -- every member is active through the sync delay after `tq` (the sync fact's holder premise,;
    --, and its justified height just before `tq` is at most `H`
    (hvq : ∀ v ∈ Q, v ∈ A.activeThroughout x tq (tq + Δs_F))
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore tq v) ≤ (M.chainStateOf S.C B).h) :
    (∀ u ∈ Q, ∃ a ∈ (x.st kQ q).attestationsHeld,
      a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root) ∧
    ((∀ u ∈ Q, ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick u t' →
        t' ≤ M.supportCutoff S.C (s + 1) →
        (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
        a.h = (M.chainStateOf S.C B).h → a.τ = false) →
      ∀ u ∈ Q, ∃ a ∈ (x.st kQ q).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧
        a.T = (M.chainStateOf S.C B).T_h.root ∧ a.τ = false) := by
  -- an attestation a member sent at a tick to a clock value at most the support cutoff of slot `s + 1`, at `H`, is
  -- in `q`'s pool at its tick `kQ` (the holder row `hvq`,)
  have hDeliver : ∀ (j t' : ℕ) (v : V) (a : Attestation V), v ∈ Q → a.h = (M.chainStateOf S.C B).h →
      x.lbl j = Event.tick v t' → t' ≤ M.supportCutoff S.C (s + 1) →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      a ∈ (x.st kQ q).attestationsHeld := by
    intro j t' v a hvQ hah hl ht' hsent
    exact (attestation_in_pool_of_tick_send_upTo M F) S A x R GST (M.supportCutoff S.C (s + 1)) c₁ tq q
      E E_F hNet_F hSkew_F Sy_F hGST ht₁ hGSTq htq kQ hkQ hwin j t' v a hl ht' hsent
      (fun _ => hvq v hvQ) (fun _ => by rw [hah]; exact hselq v hvQ)
  -- an outcome of each member's tick to the support cutoff of slot `s + 1`, from its state awake for that slot (the
  -- member's reader from `duty_window_start S.C (s + 1)`)
  have hDuty : duty_window_start S.C (s + 1) < ((M.supportCutoff S.C (s + 1) : ℕ) : Int) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout F.sched U) S (s + 1)
  have hOut : ∀ u ∈ Q, ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput u (M.supportCutoff S.C (s + 1))) (s + 1) := by
    intro u hu
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 (hv u hu)
    obtain ⟨n'', sent, hrun, hAw, -⟩ := (update_state_of_tick M F U) S A x R s u E hk
      ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E (hv u hu) hDuty)
    exact ⟨n'', sent, hrun, hAw⟩
  -- for each member, an attestation at `H` naming `T` it sent at a tick to a clock value at most the support cutoff
  -- of slot `s + 1`: the round's own (Lemma 61) or an earlier one at the same height (`record_content_sent`)
  have hFound : ∀ u ∈ Q, ∃ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick u t' ∧
      t' ≤ M.supportCutoff S.C (s + 1) ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j ∧
      a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root := by
    intro u hu
    obtain ⟨n', sent, hrun, hA⟩ := hOut u hu
    obtain ⟨hS, hF⟩ := hUpd u hu n' sent hrun hA
    have hLk := (update_lock_entries_ancestorEq M F U) S A x R s B u E hSkew (hv u hu) n' sent
      hrun hA hS hBslot (hLocks u hu)
    rcases (lem61_honest_validator_attests_frame M F U) S A x R r s B u (ρ u) (φ u) E hs (hv u hu)
        n' sent hrun hA hS hF hLk (hShape u hu) (hRoot u hu) (hBHeight u hu) (hBin u hu) (hLockBox u hu)
      with ⟨i, a, hl, hsent, hav, hah, haT⟩ | ⟨b, hb, hbh, hbT⟩
    · exact ⟨i, _, a, hl, le_rfl, hsent, hav, hah, haT⟩
    · obtain ⟨j, t', a, hl, ht', -, hsent, hav, hac, -⟩ := (record_content_sent M F) S A x R _ u b E hb
      have hah' : a.h = (M.chainStateOf S.C B).h := by rw [← hbh, ← hac]; rfl
      refine ⟨j, t', a, hl, ht'.le, hsent, hav, hah', ?_⟩
      rw [← hbT, ← hac]
      rfl
  refine ⟨fun u hu => ?_, fun hT u hu => ?_⟩
  · obtain ⟨j, t', a, hl, ht', hsent, hav, hah, haT⟩ := hFound u hu
    exact ⟨a, hDeliver j t' u a hu hah hl ht' hsent, hav, hah, haT⟩
  · -- the attestation found was sent at a tick up to the cutoff at `H`: a target by the hypothesis
    obtain ⟨j, t', a, hl, ht', hsent, hav, hah, haT⟩ := hFound u hu
    exact ⟨a, hDeliver j t' u a hu hah hl ht' hsent, hav, hah, haT, hT u hu j t' a hl ht' hsent hah⟩

open Classical in
/-- **`lem80wq_round_height_advances_steps` with the targets premise (a copy).** The hypotheses
and the first two conjuncts of `lem80wq_round_height_advances_steps`
(`Proofs/Executions/Lemma80.lean`); the third reads: when every attestation a member of `Q` put on
the wire at a tick at a time `t' ≤ a`, at the height
`H` of `B`'s chain state, is a target, then `B'`'s chain state is at least one height above `B`'s,
and, when `B'`'s parent is at `B`'s height, `B'`'s justified block is `B`'s `T_h`.

Why: the original's proof, with `round_attestations_in_pool_targets` for the pool's targets.

The variables: as `lem80wq_round_height_advances_steps`.

Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: as `lem80wq_round_height_advances_steps`:
the base at slot `s`, the round's chain steps, and the next proposal at slot `s'' − 1` read
blocks held up to the support cutoff of slot `s'' − 1`.

Restated with the delivery premises up to `M.supportCutoff S.C (s'' - 1)`, the attestations' up to
`M.slotStart S.C s''`: the blocks and Goldfish votes the proof reads are due by the support cutoff
of slot `s'' − 1` (`round_proposal_extends_upTo`), the attestations by the start of slot `s''`
(`round_attestations_in_pool_targets_upTo`), as `lem80wq_round_height_advances_steps_upTo`.

Beside the hypotheses of `lem80wq_round_height_advances_steps`, two the attestations' sync route reads: `hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot
`s''`; and `hselq`, no member of `Q` has justified past the height of `B`'s chain state before the later of the
duty window's start of slot `s` and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in a round of the phase, when every member's attestation at the proposal's height is a
target, the next honest proposal is one height higher and, when its parent is at the proposal's
height, justifies the proposal's entry, with the delivery premises up to the bound. -/
theorem lem80wq_round_height_advances_steps_targets_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V) (φ : Height) (φw φv : V → Height)
    (ρp : Block V) (ρw ρv : V → Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s'' - 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s'' - 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C s'')) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C s''))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- the frames at the three reading points of slot `s`: `p`'s before the start of slot `s`,
    -- each member's before the vote time of slot `s` and before the action time `a`, with their
    -- roots and `head_height_floor` values
    (hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C s)) ρp φ)
    (hShapeW : ∀ w ∈ Hon s, FrameShape M (x.tickInput w (M.voteTime S.C s)) (ρw w) (φw w))
    (hShapeV : ∀ v ∈ Hon s,
      FrameShape M (x.tickInput v (M.supportCutoff S.C (s + 1))) (ρv v) (φv v))
    -- each member's `head_height_floor` before the vote time is at least the proposer's and at
    -- most the chain-state height of `B`'s parent; before `a`, at most that of `B`
    (hFloorW : ∀ w ∈ Hon s, φ ≤ φw w ∧ φw w ≤ (M.chainStateOf S.C B.parent).h)
    (hFloorV : ∀ v ∈ Hon s, φv v ≤ (M.chainStateOf S.C B).h)
    -- the roots: before the vote time on `B`'s parent's chain, before `a` on `B`'s chain
    (hRootW : ∀ w ∈ Hon s, (ρw w).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon s, (ρv v).AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `ρp`'s chains, reaches `φ`
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ ρp.AncestorEq W ∧ φ ≤ (M.chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the record of every member of `Q` before `a`: the cache `h_j` is less than `H`, or no lock
    -- at `H`, or the lock at `H` is `T`
    (hLockBox : ∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root)
    -- no member of `Q` has justified past the height of `B`'s chain state before the later of the
    -- duty window's start of slot `s` and `GST`
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick u t' →
        t' ≤ M.supportCutoff S.C (s + 1) →
        (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
        a.h = (M.chainStateOf S.C B).h → a.τ = false) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  -- the slots: `s'' = s₂ + 2`, with `s ≤ s₂`
  have hR := S.C.R_ge_two
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_add_two_le_of_delivery M.toSlotLayout F.sched) S hs''
  obtain ⟨s₂, rfl⟩ : ∃ s₂, s'' = s₂ + 2 := ⟨s'' - 2, by omega⟩
  rw [show s₂ + 2 - 1 = s₂ + 1 by omega] at hVotersQ hStepLast hq hRoots hHonLast hHonestQ E Sy
  -- the times
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss : ∀ k, M.slotStart S.C (k + 1) = M.slotStart S.C k + 4 * Δ S := fun k => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hsE : ∀ k, M.slotStart S.C k = 4 * Δ S * k :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hv : ∀ k, M.voteTime S.C k = M.slotStart S.C k + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc : ∀ k, M.supportCutoff S.C k = M.voteTime S.C k + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hsm : s - 1 + 1 = s := by omega
  have hk8 := (slot_times M F U S s).2.2.2.2.2.1
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the bound `hΔs` with the read time `max (2 * Δ S) Δs` of Lemma 12
  have hm2R : ((max (2 * Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
    rcases le_total (2 * Δ S) Δs with h2 | h2
    · rw [max_eq_right h2]
      have : max ((Δ S : ℕ) : ℝ) (Δs : ℝ) = Δs := max_eq_right (by exact_mod_cast (show Δ S ≤ Δs by omega))
      have h' := hΔs
      push_cast at h' ⊢
      rw [this] at h'
      exact h'
    · rw [max_eq_left h2]
      push_cast
      linarith
  have hm2 : max (2 * Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h' : ((max (2 * Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by push_cast; push_cast at hm2R; linarith
    exact_mod_cast h'
  have hm2s := le_max_right (2 * Δ S) Δs
  have hm2l := le_max_left (2 * Δ S) Δs
  have hvs0 := hv (s - 1)
  have hss0 : M.slotStart S.C s = M.slotStart S.C (s - 1) + 4 * Δ S := by rw [← hss (s - 1), hsm]
  have hvs := hv s
  have hss1 := hss s
  have hvs1 := hv (s + 1)
  have hcs1 := hc (s + 1)
  have hm2' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S (show s + 2 ≤ s₂ + 2 by omega)
  have ha : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C (s₂ + 2) := hs''
  have hcut₁ : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (s₂ + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have hcut₂ : M.supportCutoff S.C s₂ ≤ M.supportCutoff S.C (s₂ + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  -- `B` is of slot `s`
  have hPropose₀ : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s - 1 + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
    rw [hsm]
    exact hPropose
  obtain ⟨i₀, hl₀, hsent₀⟩ := hPropose₀
  have hBslot : B.slot = s := by
    rw [← hsm]
    exact ((proposal_parent_walk_end M F U) S A x R E (s - 1) i₀ B p hl₀ hsent₀).1
  -- step 1: the base, at the first slot's set, with the reader start `max tStart (duty_window_start S.C s)`: the
  -- members' readers open at the duty window's start of slot `s`, the proposer's at `tStart`
  have hdwle : duty_window_start S.C s ≤ max tStart (duty_window_start S.C s) := le_max_right _ _
  have htStart' : ((max tStart (duty_window_start S.C s) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rcases le_total tStart (duty_window_start S.C s) with h | h
    · -- the duty window's start `st(s) + Δ − 4Δk` is more than both clock bounds before Lemma 12's read time of
      -- slot `s − 1`, truncated at `0` or not
      rw [max_eq_right h, duty_window_start_real S s]
      have i3A := E.ahead_nonneg
      have i3B := E.behind_nonneg
      have i3D : (0 : ℝ) ≤ Δ S := by positivity
      have i3k8 : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast (slot_times M F U S s).2.2.2.2.2.1
      have i3sE := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
      have i3vT := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
      have i3c := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
      have i3s : (s - 1 : ℕ) + 1 = s := by omega
      have i3ss : M.slotStart S.C (s - 1) + 4 * Δ S = M.slotStart S.C s := by
        rw [i3sE, i3sE, ← i3s, Nat.mul_add, Nat.mul_one, i3s]
      have i3cs : M.supportCutoff S.C (s - 1) + 2 * Δ S = M.slotStart S.C s := by
        have := i3c (s - 1); have := i3vT (s - 1); omega
      have i3cR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) + 2 * Δ S = 4 * (Δ S : ℝ) * (s : ℝ) := by
        have h' : ((M.supportCutoff S.C (s - 1) + 2 * Δ S : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) := by
          rw [i3cs]
        rw [i3sE s] at h'; push_cast at h'; linarith
      have i3mx : (Δs : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_right _ _
      have i3m : ((max (2 * Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
        rcases le_total (2 * Δ S) Δs with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; push_cast; linarith
      rcases le_total (max (2 * Δ S) Δs) (M.supportCutoff S.C (s - 1)) with hle | hle
      · rw [Nat.cast_sub hle]; linarith
      · rw [Nat.sub_eq_zero_of_le hle]
        have hleR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) ≤ ((max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hle
        push_cast
        linarith
    · rw [max_eq_left h]
      exact htStart
  obtain ⟨hHeld, hBase, hUpd⟩ := (round_base_steps_upTo M F U) S A x R GST s (Hon s) (Hs s) (Hs (s - 1)) H X
    B p φ φw ρp ρw (E.mono hcut₁) hNet hSkew hRedeliver (Sy.mono hcut₁) hΔs
    (fun k u c hl hcl => hRoots k u c hl (le_trans hcl hcut₁)) hParent hOwner hs1
    hGST (hHonUpd s le_rfl (by omega)) (hHonTick s le_rfl (by omega)) (max tStart (duty_window_start S.C s)) htStart'
    (Activity.mem_activeThroughoutToTick_of_le (le_max_left tStart (duty_window_start S.C s)) hp) hHoldP
    (fun w hw => Activity.mem_activeThroughoutToTick_of_le hdwle (hHon s le_rfl (by omega) w hw)) hPropose
    hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew (hHs s le_rfl (by omega))
    (fun v hv' => (hVoters s le_rfl (by omega) v hv').2) hHalf hShapeP hShapeW hFloorW
    hRootW (fun v hv => ancestorEq_trans (by rw [← (hShapeV v hv).1]; exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ v) (hRootAr v hv))
    hHeadP
  -- step 2: the invariant through the round, from one slot's set to the next; the members of slot `s₂ + 1` read to
  -- their tick to its vote time inside their update reader of slot `s₂`
  obtain ⟨hInv, hVotes⟩ := (round_honestChainExtends_steps_upTo M F U) S A x R GST s s₂ Hon Hs B (E.mono hcut₂) hNet hSkew hRedeliver (Sy.mono hcut₂) hΔs
    (fun k u c hl hcl => hRoots k u c hl (le_trans hcl hcut₂)) hParent hOwner
    (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.sub_le s 1)))
    (by omega) hHonMono
    (by
      intro s' h1 h2 v hv'
      by_cases hs' : s' + 1 < s₂ + 2
      · exact hHon s' h1 hs' v hv'
      · have he : s' = s₂ + 1 := by omega
        subst he
        have hU := hHonUpd s₂ (by omega) (by omega) v (hHonMono s₂ (by omega) (by omega) hv')
        have hvt := hv (s₂ + 1)
        have hct := hc (s₂ + 1)
        have hdr := duty_window_start_real S (s₂ + 1)
        have hsR : ((M.slotStart S.C (s₂ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s₂ + 1 : ℕ) : ℝ) := by
          exact_mod_cast hsE (s₂ + 1)
        have hvR : ((M.voteTime S.C (s₂ + 1) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + Δ S := by exact_mod_cast hvt
        have hcR : ((M.supportCutoff S.C (s₂ + 1) : ℕ) : ℝ) = (M.voteTime S.C (s₂ + 1) : ℝ) + Δ S := by exact_mod_cast hct
        push_cast at hsR hdr
        refine (mem_activeThroughoutToTick_of_le_end_int M x) R E (by omega) ?_ ?_ hU
        · linarith
        · linarith)
    (fun s' h1 h2 => hHonUpd s' h1 h2) (fun s' h1 h2 => hHonTick s' h1 h2) hHs
    hVoters hStep hStepLast hBase
  -- step 3: the attestations in `q`'s pool at its tick `kQ` to the start of slot `s''`, read from
  -- `tq := max (M.dutyWindowStart S.C s) GST`
  have hmxF1 := le_max_left (Δ_F S) Δs_F
  have hmxF2 := le_max_right (Δ_F S) Δs_F
  have hmxΔ := le_max_left (Δ S) Δs
  have hcm1 := hc (s - 1)
  have hvm1 := hv (s - 1)
  have hdws := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s
  have hssE := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hΔsF : Δs_F ≤ Δ_F S ∨ Δs_F + 3 * Δ S ≤ 4 * Δ S * S.C.k := by
    rcases hΔs_F with h | h
    · left
      exact_mod_cast (show (Δs_F : ℝ) ≤ Δ_F S by linarith)
    · right
      exact_mod_cast (show ((Δs_F + 3 * Δ S : ℕ) : ℝ) ≤ ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have htqF : max (M.dutyWindowStart S.C s) GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C (s₂ + 2) := by
    rcases hdws with h | ⟨h, -⟩
    · have := le_max_left (M.dutyWindowStart S.C s) GST
      have := le_max_right (M.dutyWindowStart S.C s) GST
      rcases max_cases (M.dutyWindowStart S.C s) GST with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases max_cases (Δ_F S) Δs_F with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1, h2] <;> omega
    · rw [h, Nat.zero_max]
      exact hGSTF
  -- `q` ticks to the start of slot `s''` (its reader `hHonLast`)
  obtain ⟨kQ0, hkQ0, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonLast q hq)
  have hkQ : x.lbl (x.tickStep q (M.slotStart S.C (s₂ + 2))) = Event.tick q (M.slotStart S.C (s₂ + 2)) := by
    rw [(tickStep_eq_of_lbl M) x E hkQ0]
    exact hkQ0
  -- each member of `Q` ticks to the vote time of slot `s` before its tick to the support cutoff of slot `s + 1`,
  -- and keeps `B`
  have hBin : ∀ v ∈ Q, B ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree := by
    intro v hvQ
    obtain ⟨k1, hk1, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHon s le_rfl (by omega) v (hQ hvQ))
    obtain ⟨k2, hk2, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd s le_rfl (by omega) v (hQ hvQ))
    have h12 := (tick_lt_of_clock_lt M) x E hk1 hk2 (by omega)
    have hB1 := hHeld v (hQ hvQ)
    unfold Trace.tickInput at hB1 ⊢
    rw [(tickStep_eq_of_lbl M) x E hk1] at hB1
    rw [(tickStep_eq_of_lbl M) x E hk2]
    exact ((grows_of_le M F) x R E v h12.le).1 hB1
  obtain ⟨hPool, hPoolT⟩ := (round_attestations_in_pool_targets_upTo M F U) S A x R GST r s (M.slotStart S.C (s₂ + 2))
    (max (M.dutyWindowStart S.C s) GST) Q B q φv ρv E hSkew E_F hNet_F hSkew_F Sy_F hs
    (by omega) ha hBslot
    (fun v hv' => hHonUpd s le_rfl (by omega) v (hQ hv'))
    (fun v hv' => hUpd v (hQ hv')) (fun v hv' => hBase.2.1 v (hQ hv'))
    (fun v hv' => hShapeV v (hQ hv')) (fun v hv' => hRootAr v (hQ hv'))
    hBin hLockBox
    (fun v hv' => hFloorV v (hQ hv')) hGSTF htqF
    (x.tickStep q (M.slotStart S.C (s₂ + 2))) hkQ hqWin
    (fun v hv' => hHoldF v (hQ hv'))
    hselq
  -- step 4: `q`'s proposal is on `B`'s chain
  have hss₂ : M.slotStart S.C (s₂ + 2) = M.slotStart S.C (s₂ + 1) + 4 * Δ S := hss (s₂ + 1)
  have hqUpd := hHonUpd s₂ (by omega) (by omega) q (hHonMono s₂ (by omega) (by omega) hq)
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hqUpd
  have hRootsQ : RootsNameBlocksUntil M A x (x.time (x.tickStep q (M.supportCutoff S.C (s₂ + 1)))) := by
    rw [(tickStep_eq_of_lbl M) x E hkc]
    exact hRoots kc q _ hkc le_rfl
  -- the voters of slot `s₂ + 1` are active through the sync delay after Lemma 12's read time of slot `s₂ + 1`,
  -- inside their reader to the start of slot `s''`
  have hHoldQ : ∀ u ∈ Hs (s₂ + 1), u ∈ A.activeThroughout x
      ((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
    intro u hu
    have huH := ((hHs (s₂ + 1) (by omega) (by omega)) u hu).1
    have hct := hc (s₂ + 1)
    have hvt := hv (s₂ + 1)
    have hst := hss (s₂ + 1)
    have hsR : ((M.slotStart S.C (s₂ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s₂ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hsE (s₂ + 1)
    have hdr := duty_window_start_real S (s₂ + 1)
    have hle : max (2 * Δ S) Δs ≤ M.supportCutoff S.C (s₂ + 1) := by
      have := le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s - 1 ≤ s₂ + 1 by omega))
      have := le_max_right (Δ S) Δs
      rcases le_total (2 * Δ S) Δs with h2 | h2
      · rw [max_eq_right h2]; omega
      · rw [max_eq_left h2]; omega
    have hcR : ((M.supportCutoff S.C (s₂ + 1) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + 2 * Δ S := by
      exact_mod_cast (show M.supportCutoff S.C (s₂ + 1) = M.slotStart S.C (s₂ + 1) + 2 * Δ S by omega)
    have hs2R : ((M.slotStart S.C (s₂ + 2) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + 4 * Δ S := by
      exact_mod_cast hst
    have hΔsm : (Δs : ℝ) ≤ ((max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm2s
    have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (hHonLast u huH)
      (a' := M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs)
      (e := M.supportCutoff S.C (s₂ + 1) - max (2 * Δ S) Δs + Δs)
      (by push_cast [Nat.cast_sub hle] at hdr hsR hm2R hΔsm hcR ⊢; linarith)
      (by push_cast [Nat.cast_sub hle] at hsR hm2R hΔsm hcR hs2R ⊢; linarith)
    rw [Nat.cast_add] at h
    exact h
  have hBB'p := (round_proposal_extends_upTo M F U) S A x R GST s₂ (Hon (s₂ + 1)) (Hs (s₂ + 1)) B B' q
    E hNet hSkew hRedeliver Sy hΔs hRootsQ hParent hOwner
    (le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s - 1 ≤ s₂ + 1 by omega)))
    ((honestChainExtends_mono M F) S A x (Hon s₂) (Hon (s₂ + 1)) B s₂
      (hHonMono s₂ (by omega) (by omega)) hInv) hVotes hq hqUpd
    (hHs (s₂ + 1) (by omega) (by omega)) hHoldQ
    hHonestQ
    hVotersQ hFrameQ hPropose'
  obtain ⟨i', hl', hsent'⟩ := id hPropose'
  obtain ⟨-, -, hB'par?, -⟩ := (proposal_parent_walk_end M F U) S A x R E (s₂ + 1) i' B' q hl' hsent'
  have hB'p : B'.parent.AncestorEq B' := ancestorEq_of_parent? hB'par?
  have hBB' := ancestorEq_trans hBB'p hB'p
  -- step 5: the certificate
  have hd1 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.1 hBB'p
  have hd2 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B'.parent B').2.2.2.1 hB'p
  by_cases heq : (M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h
  · have hT : (M.chainStateOf S.C B'.parent).T_h = (M.chainStateOf S.C B).T_h :=
      (((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.2 hBB'p heq.symm).symm
    have hPool' : ∀ u ∈ Q, ∃ a ∈ (x.tickInput q (M.slotStart S.C (s₂ + 2))).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C B'.parent).h ∧
        a.T = (M.chainStateOf S.C B'.parent).T_h.root := by
      rw [heq, hT]
      exact hPool
    obtain ⟨h53a, h53b⟩ := (lem53_next_honest_proposal_carries_certificate M F U Fx) S A x R E (s₂ + 2) q B'
      B'.parent Q hPropose' rfl hQuorum hPool'
    rw [heq, hT] at h53a h53b
    refine ⟨hBB', ?_, fun hFresh => ?_⟩
    · rcases h53a with h | h
      · exact Or.inl (by unfold Height at *; omega)
      · exact Or.inr h
    · obtain ⟨h1, h2⟩ := h53b (hPoolT hFresh)
      exact ⟨by unfold Height at *; omega, fun _ => h2⟩
  · have hlt : (M.chainStateOf S.C B).h < (M.chainStateOf S.C B'.parent).h := by
      unfold Height at *
      omega
    have hge : (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h := by
      unfold Height at *
      omega
    exact ⟨hBB', Or.inl hge, fun _ => ⟨hge, fun h => absurd h heq⟩⟩

open Classical in
/-- **`lem89r_quiet_round` with the targets premise (a copy).** The hypotheses and the conclusion
of `lem89r_quiet_round` (`Statements/Executions/Lemma89rStatements.lean`) but its third conjunct,
which reads: when every attestation a member of `Hon s` put on the wire at a tick at a time
`t' ≤ M.supportCutoff S.C (s + 1)`, at the height of
`B`'s chain state, is a target, then `B'`'s chain state is at least one height above `B`'s, and,
when `B'`'s parent is at `B`'s height, `B'`'s justified block is `B`'s `T_h`.

Why: the original's proof, with `lem80wq_round_height_advances_steps_targets` for the round
theorem.

The variables: as `lem89r_quiet_round`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1`.
The form takes `hGSTF`, the attestations' sync delay elapsed after `GST` by the start of slot `s''`, and passes it
to its round theorem; the round theorem's `hselq` it derives from the proposal at slot `s`
.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in a quiet round of the phase, when every member's attestation at the proposal's height
is a target, the next honest proposal is one height higher and, when its parent is at the
proposal's height, justifies the proposal's entry.

Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: as `lem89r_quiet_round`: the round theorem
at slot `s''` reads blocks held up to it, and the chain steps of the slots before `s'' − 1` up
to their support cutoffs, at most it.

Restated with the delivery premises up to `M.supportCutoff S.C (s'' - 1)`: the bound of its roots,
for the votes (`hSync`, `hCatch`); the attestations (`hSyncF`, `hCatchF`) up to
`M.slotStart S.C s''`, the bound `lem80wq_round_height_advances_steps_targets_upTo` reads them at,
as `lem89r_quiet_round_upTo`. -/
theorem lem89r_quiet_round_targets_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST r s s'' : ℕ) (Hon : ℕ → Finset V)
    (𝓒 : Block V → Prop) (B B' : Block V) (p q : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (s'' - 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (s'' - 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C s'')) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C s''))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of the support cutoff of slot `s'' − 1`, and up to the real time of every
    -- validator's tick to a clock value at most that cutoff
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s'' - 1)))
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- fewer than a third of the validators have been in the adversary set up to the real time of each member's own
    -- tick to the support cutoff of slot `s + 1` (rule R3;)
    (hThird : ∀ v ∈ Hon s, A.AdversaryFewerThanThirdUntil x (validator_count V)
        (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hHonMono : ∀ s', s - 1 ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` from `s − 1` to `s'' − 1`, the members of slot `s'` are honest active validators of slot
    -- `s'` (, amending on this statement;
    -- are its instances at `s − 1` and `s'' − 1`)
    (hHon : ∀ s', s - 1 ≤ s' → s' < s'' → Hon s' ⊆ honestActiveAt M S A x s')
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    (hQuorum : quorum V ≤ (Hon s).card)
    (hCommittees : ∀ s', s - 1 ≤ s' → s' < s'' →
      (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon s').card)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer of slot `s` is outside the adversary set at each member's tick to the vote time of slot `s`
    --
    (hpHon : ∀ w ∈ Hon s, p ∉ A.corrupted (x.tickStep w (M.voteTime S.C s)))
    (hq : q ∈ Hon (s'' - 1)) (hps : S.P.proposer s = p) (hqProp : S.P.proposer s'' = q)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hQuiet : QuietRoundOnConfirmations M S A x Hon B s s'')
    (hChain : ChainInvFor M S A x (Hon (s - 1)) 𝓒 (s - 1))
    (hFamLocks : ∀ w ∈ Hon (s - 1), LiveLocksOnFamilyAt M S A x 𝓒 (s - 1) w)
    (hAnchor : 𝓒
        (M.get_anchor (x.tickInput p (M.slotStart S.C s)) ((M.slotStart S.C s : ℕ) : Int)))
    (hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree,
        W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).viable_heads ∧ C.AncestorEq W) :
    (∃ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root = B.root) ∨
    (B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt ∧
        ∃ Q : Finset V, quorum V ≤ Q.card ∧ Q ⊆ (M.chainStateOf S.C B').progress)) ∧
    ((∀ u ∈ Hon s, ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick u t' →
        t' ≤ M.supportCutoff S.C (s + 1) →
        (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
        a.h = (M.chainStateOf S.C B).h → a.τ = false) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) ∧
    (∀ v ∈ Hon s,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) ∧
    ChainInvFor M S A x (Hon (s'' - 1)) (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C)
      (s'' - 1) ∧
    (∀ w ∈ Hon (s'' - 1), LiveLocksOnFamilyAt M S A x (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C)
      (s'' - 1) w)) := by
  -- the collision case
  by_cases hColl : ∃ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root = B.root
  · exact Or.inl hColl
  right
  have hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root :=
    fun B₁ hB₁ he => hColl ⟨B₁, hB₁, he⟩
  -- the slots: `s'' = s₂ + 2`, with `s ≤ s₂`
  have hR := S.C.R_ge_two
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_add_two_le_of_delivery M.toSlotLayout F.sched) S hs''
  obtain ⟨s₂, rfl⟩ : ∃ s₂, s'' = s₂ + 2 := ⟨s'' - 2, by omega⟩
  have h21 : s₂ + 2 - 1 = s₂ + 1 := by omega
  have h22 : s₂ + 2 - 2 = s₂ := by omega
  --: the rows the body reads, derived from the `honestActiveAt` row (re-check 82, section 1.1): the
  -- members of slot `s − 1` and of slot `s'' − 1`, the updaters (`honestActiveAt_window`, its start moved later), the
  -- tick-honesty filter (the set's second exclusion) and the wake rule's reader to the vote time
  have hHonAct := hHon
  have hHonPrev : Hon (s - 1) ⊆ honestActiveAt M S A x (s - 1) := hHonAct (s - 1) le_rfl (by omega)
  have hHonLast : Hon (s₂ + 2 - 1) ⊆ honestActiveAt M S A x (s₂ + 2 - 1) :=
    hHonAct (s₂ + 2 - 1) (by omega) (by omega)
  have hUpdOf : ∀ s', Hon s' ⊆ honestActiveAt M S A x s' → Hon s' ⊆ updaterAt M S A x s' :=
    fun s' h v hv' => Activity.mem_activeThroughoutToTick_of_le
      (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ s'))
      ((honestActiveAt_window M F) S A s' v E (h hv'))
  have hHonUpd : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s' :=
    fun s' h1 h2 v hv' => hUpdOf s' (hHonAct s' (by omega) (by omega)) hv'
  have hHonTick : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) :=
    fun s' h1 h2 u hu hX => (Finset.mem_sdiff.1 (hHonAct s' (by omega) (by omega) hu)).2 (Finset.mem_union_right _ hX)
  have hHon : ∀ s', s ≤ s' → s' + 1 < s₂ + 2 → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s') :=
    fun s' h1 h2 v hv' => (reader_vote_of_honestActiveAt M F U) R E hSkew (hHonAct s' (by omega) (by omega) hv')
  -- the times
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss : ∀ k, M.slotStart S.C (k + 1) = M.slotStart S.C k + 4 * Δ S := fun k => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hsE : ∀ k, M.slotStart S.C k = 4 * Δ S * k :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hv : ∀ k, M.voteTime S.C k = M.slotStart S.C k + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc : ∀ k, M.supportCutoff S.C k = M.voteTime S.C k + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hsm : s - 1 + 1 = s := by omega
  have hk8 := (slot_times M F U S s).2.2.2.2.2.1
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hscm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b :=
    fun a b h => (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hOwner := (votesCastByOwner_of_unforgeability M F) S A x R E
  -- the bounds the `_upTo` callees read the delivery premises at
  have hcutF : M.supportCutoff S.C (s - 1) ≤ M.supportCutoff S.C (s₂ + 2 - 1) := hscm _ _ (by omega)
  have hcutJ : M.slotStart S.C (s - 1 + 1) ≤ M.supportCutoff S.C (s₂ + 2 - 1) := by
    have := hscm s (s₂ + 2 - 1) (by omega); have := hc s; have := hv s; rw [hsm]; omega
  -- the members of every slot of the round tick to its vote time, active from the duty window's start; the last
  -- slot's members within their update window of slot `s₂` (as `lem80wq_round_height_advances_steps`)
  have hHonAll : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s') := by
    intro s' h1 h2 v hv'
    by_cases hs' : s' + 1 < s₂ + 2
    · exact hHon s' h1 hs' v hv'
    · have he : s' = s₂ + 1 := by omega
      subst he
      have hU := hHonUpd s₂ (by omega) (by omega) v (hHonMono s₂ (by omega) (by omega) hv')
      have hvt := hv (s₂ + 1)
      have hct := hc (s₂ + 1)
      have hdr := duty_window_start_real S (s₂ + 1)
      have hsR : ((M.slotStart S.C (s₂ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s₂ + 1 : ℕ) : ℝ) := by
        exact_mod_cast hsE (s₂ + 1)
      have hvR : ((M.voteTime S.C (s₂ + 1) : ℕ) : ℝ) = (M.slotStart S.C (s₂ + 1) : ℝ) + Δ S := by exact_mod_cast hvt
      have hcR : ((M.supportCutoff S.C (s₂ + 1) : ℕ) : ℝ) = (M.voteTime S.C (s₂ + 1) : ℝ) + Δ S := by exact_mod_cast hct
      push_cast at hsR hdr
      refine (mem_activeThroughoutToTick_of_le_end_int M x) R E (by omega) ?_ ?_ hU
      · linarith
      · linarith
  -- the duty window's start of a slot is before its vote time, as clock values
  have hdwv : ∀ s', duty_window_start S.C s' < ((M.voteTime S.C s' : ℕ) : ℤ) := by
    intro s'
    have h0 := duty_window_start_real S s'
    have hvN : M.voteTime S.C s' = 4 * Δ S * s' + Δ S := by rw [hv, hsE]
    have hvR : ((M.voteTime S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) + Δ S := by
      rw [hvN]; push_cast; ring
    have : ((duty_window_start S.C s' : ℤ) : ℝ) < ((M.voteTime S.C s' : ℕ) : ℝ) := by
      rw [h0, hvR]; linarith
    exact_mod_cast this
  -- the honest voters of each slot, and `p`'s anchor
  set Hs : ℕ → Finset V := fun s' => S.P.committee s' ∩ Hon s' with hHsDef
  set X := M.get_anchor (x.tickInput p (M.slotStart S.C s)) ((M.slotStart S.C s : ℕ) : Int) with hXdef
  -- the blocks the voters of slot `s − 1` vote for: descendants of `X` (the chain invariant of the family at `X`)
  have hex : ∀ u ∈ Hs (s - 1), ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq H_u := by
    --: the voter's vote, from the wake rule's reader to its tick to the vote time of slot `s − 1`
    -- (`reader_vote_of_honestActiveAt`), on the chain of the family's block `X` (the chain invariant at slot `s − 1`)
    intro u hu
    have hT := (reader_vote_of_honestActiveAt M F U) R E hSkew (hHonPrev (Finset.mem_inter.1 hu).2)
    obtain ⟨k', hl, -⟩ := Activity.mem_activeThroughoutToTick.1 hT
    obtain ⟨vote, hvi, hvs, hsent⟩ := (honest_votes_of_window M F U) S A x R (s - 1) u E hl
      ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hT (hdwv (s - 1))) (Finset.mem_inter.1 hu).1
    obtain ⟨H_u, hT', hvt, hXH⟩ := (hChain X hAnchor).1 u (Finset.mem_inter.1 hu).2 vote ⟨_, hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨_, hl, hsent⟩, hT', hXH⟩
  choose Hc hHc using hex
  let H : V → Block V := fun u => if h : u ∈ Hs (s - 1) then Hc u h else B
  have hH : ∀ u (hu : u ∈ Hs (s - 1)), H u = Hc u hu := fun u hu => dif_pos hu
  have hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u) := by
    intro u hu
    rw [hH u hu]
    refine ⟨(Finset.mem_inter.1 hu).1, ?_, (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩
    -- each member's tick to the vote time of slot `s` is before the support cutoff of slot `s`, through whose real time
    -- the voter is honest (`hHonPrev`,)
    intro w _
    have ht := (time_tickStep_le_add_behind M F) x R E w (M.voteTime S.C s)
    have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = ((M.voteTime S.C s : ℕ) : ℝ) + Δ S := by exact_mod_cast hc s
    refine (not_corrupted_of_honestActiveAt M F) (hHonPrev (Finset.mem_inter.1 hu).2) ?_
    rw [hsm]; linarith
  have hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
    --: the holder row from the `honestActiveAt` row (`hold_of_honestActiveAt`, under `hGST`)
    intro u hu
    exact (hold_of_honestActiveAt M F U) R E hΔs hSkew hGST (hHonPrev (Finset.mem_inter.1 hu).2)
  have hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card := by
    intro w _ votes sv hC
    have h := ((counting_of_committee_majority_st M F) S A x R E (s - 1) (x.tickStep w (M.voteTime S.C s))
      (Hon (s - 1)) w (hCommittees (s - 1) le_rfl (by omega))).2.2 votes sv
    rw [hsm] at h
    exact h hC
  -- every block of the family is `B`'s parent or an ancestor of it
  -- `p`'s window from Lemma 12's read time of slot `s − 1` to its tick to the start of slot `s`, and its tick to the
  -- support cutoff of slot `s − 1` inside it
  have hcs : M.supportCutoff S.C (s - 1) + 2 * Δ S = M.slotStart S.C s := by
    have h1 := hc (s - 1); have h2 := hv (s - 1); have h3 := hss (s - 1); rw [hsm] at h3; omega
  have hcsR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) + 2 * Δ S = ((M.slotStart S.C s : ℕ) : ℝ) := by
    exact_mod_cast hcs
  have hc2 : 2 * Δ S ≤ M.supportCutoff S.C (s - 1) := by
    have h1 := hc (s - 1); have h2 := hv (s - 1); omega
  have hm2N : M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs + Δ S ≤ M.supportCutoff S.C (s - 1) := by
    have := le_max_left (2 * Δ S) Δs
    omega
  have hm2R : (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)) + Δ S ≤
      ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) := by exact_mod_cast hm2N
  obtain ⟨kP, hkP, hpWin⟩ := (tick_window_of_activeThroughoutToTick_int M x) R E hp
    (t₀ := ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)) (by linarith)
  obtain ⟨-, hkP1, hkP2⟩ := E.tick_active kP p _ hkP
  have hc1 : 1 ≤ M.supportCutoff S.C (s - 1) := by omega
  obtain ⟨iC, hlC, hiC1, hiC2⟩ := E.tick_of_active (M.supportCutoff S.C (s - 1)) hc1 p (fun j h1 h2 =>
    hpWin j (by linarith) ((lt_of_time_lt M) x R (by linarith)).le)
  have hiCk : iC ≤ kP := ((lt_of_time_lt M) x R (by linarith)).le
  -- every block of the family is `B`'s parent or an ancestor of it
  have hFamPar : ∀ C : Block V, 𝓒 C → C.AncestorEq B.parent := by
    have hPropose₁ : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s - 1 + 1)) ∧
        (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
      rw [hsm]; exact hPropose
    have hFrameP₁ : ∀ C : Block V, 𝓒 C →
        ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s - 1 + 1)))).tree,
          W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s - 1 + 1)))).viable_heads ∧ C.AncestorEq W := by
      rw [hsm]; exact hFrameP
    have hAnchor₁ : 𝓒 (M.get_anchor (x.tickInput p (M.slotStart S.C (s - 1 + 1)))
        ((M.slotStart S.C (s - 1 + 1) : ℕ) : Int)) := by
      rw [hsm]; exact hAnchor
    have hti := (tickStep_eq_of_lbl M) x E hkP
    refine (family_ancestorEq_proposal_parent_upTo M F U) S A x R GST (s - 1) (Hs (s - 1)) 𝓒 B p (E.mono hcutF) hNet hSkew
      hRedeliver (Sy.mono hcutF) hΔs ?_ hParent hOwner hGST ?_ ?_ ?_ hHold ⟨iC, hlC, fun j h1 h2 => hpWin j h1 (le_trans h2 hiCk)⟩
      hPropose₁ hFrameP₁ hAnchor₁
    · rw [(tickStep_eq_of_lbl M) x E hlC]
      exact hRootsTick iC p _ hlC (hscm _ _ (by omega))
    · intro u hu
      refine ⟨(Finset.mem_inter.1 hu).1, ?_, _, (hHc u hu).1⟩
      rw [hsm, hti]
      -- `p`'s tick to the start of slot `s` is before the support cutoff of slot `s`, through whose real time the voter
      -- is honest (`hHonPrev`,)
      have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) + 2 * Δ S := by
        have h1 := hc s; have h2 := hv s; exact_mod_cast (show M.supportCutoff S.C s = M.slotStart S.C s + 2 * Δ S by omega)
      refine (not_corrupted_of_honestActiveAt M F) (hHonPrev (Finset.mem_inter.1 hu).2) ?_
      rw [hsm]; linarith
    · intro C hC u hu vote hsend
      exact (hChain C hC).1 u (Finset.mem_inter.1 hu).2 vote hsend
    · rw [hsm]
      exact ((counting_of_committee_majority_st M F) S A x R E (s - 1) (x.tickStep p (M.slotStart S.C s))
        (Hon (s - 1)) p (hCommittees (s - 1) le_rfl (by omega))).2.1
  have hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent := by
    intro w hw n' sent hrun hA e he hl
    have hw' : w ∈ Hon (s - 1) := hHonMono (s - 1) le_rfl (by omega) (by rw [hsm]; exact hw)
    have h := hFamLocks w hw'
    unfold LiveLocksOnFamilyAt at h
    rw [hsm] at h
    obtain ⟨D, hD, heD⟩ := h n' sent hrun hA e he hl
    exact ancestorEq_trans heD (hFamPar D hD)
  have hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B := by
    --: the proposer is outside the adversary set at the member's tick (`only_block_of_unforgeability_st`)
    intro w hw B₁ hB₁ hslot
    exact (only_block_of_unforgeability_st M F U) S A x R E s (x.tickStep w (M.voteTime S.C s)) B B₁ p w (hpHon w hw) hps
      hPropose hB₁ hslot
  have hHs : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i := by
    intro s' h1 h2 u hu
    obtain ⟨hk, huH⟩ := Finset.mem_inter.1 hu
    have hT := hHonAll s' h1 h2 u huH
    obtain ⟨k', hl, -⟩ := Activity.mem_activeThroughoutToTick.1 hT
    obtain ⟨vote, hvi, hvs, hsent⟩ := (honest_votes_of_window M F U) S A x R s' u E hl
      ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hT (hdwv s')) hk
    exact ⟨huH, hk, vote, hvi, hvs, _, hl, hsent⟩
  have hVoters : ∀ s', s ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card := fun s' h1 h2 v _ =>
    ⟨((counting_of_committee_majority_st M F) S A x R E s' (x.tickStep v (M.voteTime S.C (s' + 1)))
        (Hon s') v (hCommittees s' (by omega) h2)).2.2,
      ((counting_of_committee_majority_st M F) S A x R E s' (x.tickStep v (M.supportCutoff S.C (s' + 1)))
        (Hon s') v (hCommittees s' (by omega) h2)).2.1⟩
  have hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      GoldilocksCorrectness.Record.Statements.Routines.ProposalCountedVotes M (x.tickInput q (M.slotStart S.C (s₂ + 2)))
        (s₂ + 2 - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s₂ + 2 - 1)).card := fun votes sv hP => by
    rw [hP.1]
    exact ((counting_of_committee_majority_st M F) S A x R E (s₂ + 2 - 1)
      (x.tickStep q (M.slotStart S.C (s₂ + 2))) (Hon (s₂ + 2 - 1)) q (hCommittees _ (by omega) (by omega))).2.1
  have hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card :=
    ((counting_of_committee_majority M F) S A x R E s 0 (Hon s) p (hCommittees s (by omega) (by omega))).1
  have hFloorW : ∀ w ∈ Hon s, M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤
      M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h := by
    intro w hw
    refine ⟨?_, (hQuiet.1 w hw).2⟩
    -- F-P1-30-4: `floor_le_of_delivery_ticks`, `p` read at its tick `kP` to the start of slot `s` and `w` at its tick to
    -- the vote time of slot `s`; the windows from `a := M.slotStart S.C s - max (Δ S) Δs` (`p`'s `hHoldP`, `w`'s `hHon`)
    have hvs := hv s
    obtain ⟨a, ha⟩ : ∃ a, a = M.slotStart S.C s - max (Δ S) Δs := ⟨_, rfl⟩
    have haN : a + max (Δ S) Δs = M.slotStart S.C s := by omega
    have haR : (a : ℝ) + ((max (Δ S) Δs : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) := by exact_mod_cast haN
    have hmxR : ((max (Δ S) Δs : ℕ) : ℝ) = max (Δ S : ℝ) (Δs : ℝ) := Nat.cast_max _ _
    have hmxΔ : (Δ S : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_left _ _
    have hsR : ((M.slotStart S.C s : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s : ℝ) := by exact_mod_cast hsE s
    have hvR : ((M.voteTime S.C s : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) + Δ S := by exact_mod_cast hvs
    have hdr := duty_window_start_real S s
    -- `w`'s tick to the vote time of slot `s`, active from the real time `a` up to it
    obtain ⟨kw, hkw, hwin⟩ := (tick_window_of_activeThroughoutToTick_int M x) R E (hHonAll s le_rfl (by omega) w hw)
      (t₀ := (a : ℝ)) (by linarith)
    have hkwT := (tickStep_eq_of_lbl M) x E hkw
    obtain ⟨-, -, hkw2⟩ := E.tick_active kw w _ hkw
    -- `w`'s earlier tick to the start of slot `s`
    have hw₂ : w ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s) :=
      (mem_activeThroughoutToTick_of_le_end_int M x) R E (by omega) (by linarith) (by linarith)
        (hHonAll s le_rfl (by omega) w hw)
    obtain ⟨k₂, hk₂, -⟩ := Activity.mem_activeThroughoutToTick.1 hw₂
    -- fewer than a third in the adversary set up to `w`'s tick to the vote time of slot `s`, before its tick to the
    -- support cutoff of slot `s + 1` (`hThird`)
    obtain ⟨kU, hkU, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd s le_rfl (by omega) w hw)
    have htU := (tickStep_eq_of_lbl M) x E hkU
    obtain ⟨-, hkU1, -⟩ := E.tick_active kU w _ hkU
    have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) + 6 * Δ S := by
      have h1 := hc (s + 1); have h2 := hv (s + 1); have h3 := hss s
      exact_mod_cast (show M.supportCutoff S.C (s + 1) = M.slotStart S.C s + 6 * Δ S by omega)
    have hAdvW : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time kw) := by
      refine (hThird w hw).mono ?_
      rw [htU]
      linarith
    -- every block `p` holds at its tick is of a slot at most `s` (its clock value there is less than the slot's start)
    have hslF : ∀ t' : ℕ, M.slot S.C t' = S.C.slot (t' : Int) := fun t' => by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
        GoldilocksCorrectness.Proofs.Routines.slot_natCast]
    have hcvP : x.clockValue kP p < M.slotStart S.C s :=
      (clockValue_lt_of_tick_of_active M F) E hkP (by omega) (fun j h1 h2 => hpWin j (by linarith) h2)
    have hslotP : ∀ Y ∈ (x.st kP p).tree, M.slotStart S.C Y.slot ≤ M.slotStart S.C s := by
      intro Y hY
      have h := (slot_le_clockValue_of_mem_tree M F) R E (E.not_mem_corrupted_of_tick hkP) hY
      have hlt := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_lt_slotStart M.toSlotLayout F.sched) S hcvP
      rw [hslF] at hlt
      exact (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (le_of_lt (h.trans_lt hlt))
    have hfl := (floor_le_of_delivery_ticks M F U Fx) S A x R GST (M.slotStart S.C s) kP a (M.voteTime S.C s)
      (M.slotStart S.C s) kw k₂ p w E hNet hSkew hRedeliver Sy
      (hRootsTick kw w _ hkw (by have := hscm s (s₂ + 2 - 1) (by omega); have := hc s; omega)) hParent hAdvW
      (by omega) (by omega) hkP (by linarith) (by rw [ha]; exact hHoldP) hkw (by omega) hwin hk₂ (by omega)
      hslotP le_rfl (by have := hscm s (s₂ + 2 - 1) (by omega); have := hc s; omega)
    have hTp : x.tickInput p (M.slotStart S.C s) = x.st kP p := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hkP]
    have hTw : x.tickInput w (M.voteTime S.C s) = x.st kw w := by
      unfold Trace.tickInput
      rw [hkwT]
    rw [hTp, hTw]
    exact hfl
  have hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (M.get_fc_root (x.tickInput p (M.slotStart S.C s))).AncestorEq W ∧
      M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤ (M.chainStateOf S.C W).h := by
    have h := (anchor_has_viable_head_st M F) S A x R E (x.tickStep p (M.slotStart S.C s)) p
      (x.st (x.tickStep p (M.slotStart S.C s)) p).lockEntries ((M.slotStart S.C s : ℕ) : Int)
    rw [← GoldilocksCorrectness.Record.get_anchor_eq_anchorAt F.rd] at h
    exact h
  have hStep : ∀ s', s ≤ s' → s' + 3 ≤ s₂ + 2 → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w :=
    fun s' h1 h2 w hw => hQuiet.2.2.1 s' h1 (by omega) w hw
  have hStepLast : ∀ w ∈ Hon (s₂ + 2 - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 2 - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 2 - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s₂ + 2 - 1)))
          (S.C.t_ ((s₂ + 2 - 1) - 1) + 3 * S.C.Δ) (s₂ + 2 - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 2 - 1)))).viable_heads ∧
            B.AncestorEq W) := by
    intro w hw
    rw [h21] at hw ⊢
    have h := hQuiet.2.2.1 s₂ (by omega) le_rfl w hw
    exact ⟨h.1, h.2.1⟩
  have hLockBox : ∀ v ∈ Hon s,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root := fun v hv' =>
    (lockBox_of_frame_tick M F Fx) S A x R E _ v B (hThird v hv') (hQuiet.2.1 v hv').1 (hQuiet.2.1 v hv').2
  have hselq : ∀ v ∈ Hon s, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h := by
    -- `justifiedHeight_le_of_later_proposal` at slot `s − 1`: `p`'s window from `hpWin`, `v`'s tick window `hHon`,
    -- fewer than a third in the adversary set up to one delay after the start of slot `s` (before `v`'s tick to the
    -- support cutoff of slot `s + 1`, `hThird`)
    intro v hv'
    have hti := (tickStep_eq_of_lbl M) x E hkP
    obtain ⟨kU, hkU, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd s le_rfl (by omega) v hv')
    have htU := (tickStep_eq_of_lbl M) x E hkU
    obtain ⟨-, hkU1, -⟩ := E.tick_active kU v _ hkU
    have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) + 6 * Δ S := by
      have h1 := hc (s + 1); have h2 := hv (s + 1); have h3 := hss s
      exact_mod_cast (show M.supportCutoff S.C (s + 1) = M.slotStart S.C s + 6 * Δ S by omega)
    have hThirdV : A.AdversaryFewerThanThirdUntil x (validator_count V)
        ((M.slotStart S.C (s - 1 + 1) + Δ S : ℕ) : ℝ) := by
      refine (hThird v hv').mono ?_
      rw [htU, hsm]
      push_cast
      linarith
    have hPropose₂ : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s - 1 + 1)) ∧
        (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
      rw [hsm]; exact hPropose
    have hmm : M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs ≤ M.supportCutoff S.C (s - 1) - max (Δ S) Δs := by
      have := le_max_left (Δ S) Δs; have := le_max_right (Δ S) Δs
      have := le_max_left (2 * Δ S) Δs; have := le_max_right (2 * Δ S) Δs
      omega
    have hmmR : ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) ≤
        ((M.supportCutoff S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hmm
    have h := (justifiedHeight_le_of_later_proposal_upTo M F U Fx) S A x R GST (s - 1) v p B (E.mono hcutJ) hNet hSkew hRedeliver
      (Sy.mono hcutJ) hΔs
      (by rw [hsm, hti]; exact hRootsTick kP p _ hkP (by
        have := hscm (s + 1) (s₂ + 2 - 1) (by omega); have := hc (s + 1); have := hv (s + 1); have := hss s; omega))
      hParent hThirdV hGST (by rw [hsm]; exact hHon s le_rfl (by omega) v hv')
      (fun i h1 h2 => hpWin i (le_trans hmmR h1) (by rw [hsm, hti] at h2; exact h2)) hPropose₂
    rw [hsm] at h
    exact h
  -- the base of the round and the invariant through it, as `lem80wq_round_height_advances_steps` reads them (its
  -- steps 1 and 2): `B` held by every member at its tick to the vote time of slot `s`, saved at its tick to the
  -- support cutoff of slot `s + 1`, and the chain invariant relative to `B` at slot `s₂`
  have hcut₁ : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (s₂ + 2 - 1) := hscm _ _ (by omega)
  have hcut₂ : M.supportCutoff S.C s₂ ≤ M.supportCutoff S.C (s₂ + 2 - 1) := hscm _ _ (by omega)
  have hdwle : duty_window_start S.C s ≤ max tStart (duty_window_start S.C s) := le_max_right _ _
  have htStart' : ((max tStart (duty_window_start S.C s) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rcases le_total tStart (duty_window_start S.C s) with h | h
    · -- the duty window's start `st(s) + Δ − 4Δk` is more than both clock bounds before Lemma 12's read time of
      -- slot `s − 1`, truncated at `0` or not
      rw [max_eq_right h, duty_window_start_real S s]
      have i3A := E.ahead_nonneg
      have i3B := E.behind_nonneg
      have i3D : (0 : ℝ) ≤ Δ S := by positivity
      have i3k8 : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast (slot_times M F U S s).2.2.2.2.2.1
      have i3sE := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
      have i3vT := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
      have i3c := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
      have i3s : (s - 1 : ℕ) + 1 = s := by omega
      have i3ss : M.slotStart S.C (s - 1) + 4 * Δ S = M.slotStart S.C s := by
        rw [i3sE, i3sE, ← i3s, Nat.mul_add, Nat.mul_one, i3s]
      have i3cs : M.supportCutoff S.C (s - 1) + 2 * Δ S = M.slotStart S.C s := by
        have := i3c (s - 1); have := i3vT (s - 1); omega
      have i3cR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) + 2 * Δ S = 4 * (Δ S : ℝ) * (s : ℝ) := by
        have h' : ((M.supportCutoff S.C (s - 1) + 2 * Δ S : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) := by
          rw [i3cs]
        rw [i3sE s] at h'; push_cast at h'; linarith
      have i3mx : (Δs : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_right _ _
      have i3m : ((max (2 * Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
        rcases le_total (2 * Δ S) Δs with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; push_cast; linarith
      rcases le_total (max (2 * Δ S) Δs) (M.supportCutoff S.C (s - 1)) with hle | hle
      · rw [Nat.cast_sub hle]; linarith
      · rw [Nat.sub_eq_zero_of_le hle]
        have hleR : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) ≤ ((max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hle
        push_cast
        linarith
    · rw [max_eq_left h]
      exact htStart
  obtain ⟨hHeld, hBase, hUpd⟩ := (round_base_steps_upTo M F U) S A x R GST s (Hon s) (Hs s) (Hs (s - 1)) H X
    B p (M.head_height_floor (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.head_height_floor (x.tickInput w (M.voteTime S.C s)))
    (M.get_fc_root (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.get_fc_root (x.tickInput w (M.voteTime S.C s))) (E.mono hcut₁) hNet hSkew hRedeliver (Sy.mono hcut₁) hΔs
    (fun k u c hl hcl => hRootsTick k u c hl (le_trans hcl hcut₁)) hParent hOwner hs1
    hGST (hHonUpd s le_rfl (by omega)) (hHonTick s le_rfl (by omega)) (max tStart (duty_window_start S.C s)) htStart'
    (Activity.mem_activeThroughoutToTick_of_le (le_max_left tStart (duty_window_start S.C s)) hp) hHoldP
    (fun w hw => Activity.mem_activeThroughoutToTick_of_le hdwle (hHon s le_rfl (by omega) w hw)) hPropose
    hHsPrev hHold hVotersPrev (ancestorEq_refl _) hLocksW hOnly hRootNew (hHs s le_rfl (by omega))
    (fun v hv' => (hVoters s le_rfl (by omega) v hv').2) hHalf ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) hFloorW
    (fun w hw => (hQuiet.1 w hw).1)
    (fun v hv' => ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F)
      S A x R E (x.tickStep v (M.supportCutoff S.C (s + 1))) v) (hQuiet.2.1 v hv').1)
    hHeadP
  have hStepLast' : ∀ w ∈ Hon (s₂ + 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s₂ + 1)))
          (S.C.t_ ((s₂ + 1) - 1) + 3 * S.C.Δ) (s₂ + 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₂ + 1)))).viable_heads ∧
            B.AncestorEq W) := by
    intro w hw
    have h := hStepLast w (by rw [h21]; exact hw)
    rw [h21] at h
    exact h
  obtain ⟨hInv, -⟩ := (round_honestChainExtends_steps_upTo M F U) S A x R GST s s₂ Hon Hs B (E.mono hcut₂) hNet hSkew hRedeliver (Sy.mono hcut₂) hΔs
    (fun k u c hl hcl => hRootsTick k u c hl (le_trans hcl hcut₂)) hParent hOwner
    (le_trans hGST (hscm _ _ (Nat.sub_le s 1))) (by omega) (fun s' h1 h2 => hHonMono s' (by omega) h2)
    hHonAll (fun s' h1 h2 => hHonUpd s' h1 h2) (fun s' h1 h2 => hHonTick s' h1 h2) hHs hVoters hStep hStepLast' hBase
  have hChainB : ∀ C : Block V, (∃ v ∈ Hon (s₂ + 2 - 2),
      (x.tickOutput v (M.supportCutoff S.C (s₂ + 2 - 1))).savedConfirmation (s₂ + 2 - 2) = some C) →
      B.AncestorEq C := by
    rintro C ⟨v, hv', hC⟩
    rw [h22] at hv'
    rw [h21, h22] at hC
    exact hInv.2.2 v hv' C hC
  have hFrameQ := (frameQ_of_quietRoundOnConfirmations M F) S A x Hon B s (s₂ + 2) hQuiet hChainB
  rw [hqProp] at hFrameQ
  --: the round theorem's reader of the last slot's members to the start of slot `s''`, and their honesty at
  -- `q`'s tick to it, from the `honestActiveAt` row
  have hHonLastR : ∀ v ∈ Hon (s₂ + 2 - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s₂ + 2 - 1)) (M.slotStart S.C (s₂ + 2)) := by
    intro v hv'
    have h := (reader_slotStart_of_honestActiveAt M F U) R E hSkew (hHonLast hv')
    rwa [show s₂ + 2 - 1 + 1 = s₂ + 2 by omega] at h
  have hHonestQR : ∀ u ∈ Hon (s₂ + 2 - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C (s₂ + 2))) := by
    intro u hu
    have ht := (time_tickStep_le_add_behind M F) x R E q (M.slotStart S.C (s₂ + 2))
    have hcR : ((M.supportCutoff S.C (s₂ + 2) : ℕ) : ℝ) = ((M.slotStart S.C (s₂ + 2) : ℕ) : ℝ) + 2 * Δ S := by
      have h1 := hc (s₂ + 2); have h2 := hv (s₂ + 2)
      exact_mod_cast (show M.supportCutoff S.C (s₂ + 2) = M.slotStart S.C (s₂ + 2) + 2 * Δ S by omega)
    refine (not_corrupted_of_honestActiveAt M F) (hHonLast hu) ?_
    rw [show s₂ + 2 - 1 + 1 = s₂ + 2 by omega]; linarith
  -- the round theorem
  obtain ⟨h80a, h80b, h80c⟩ :=
    (lem80wq_round_height_advances_steps_targets_upTo M F U Fx) S A x R GST r s (s₂ + 2) Hon (Hon s) Hs H X B B' p q
    (M.head_height_floor (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.head_height_floor (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))))
    (M.get_fc_root (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.get_fc_root (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1))))
    E hNet hSkew hRedeliver Sy hΔs hRootsTick hParent hOwner E_F hNet_F hSkew_F Sy_F hΔs_F hs hs1 hs'' hGST hGSTF
    (fun s' h1 h2 => hHonMono s' (by omega) h2) hHon hHonUpd hHonTick hHonLastR
    (fun u hu => hHonestQR u (Finset.mem_inter.1 hu).2) hHold42 hHoldV hHoldF tStart htStart hp hHoldP hPropose
    hHsPrev hHold hVotersPrev (ancestorEq_refl _) hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hFloorW (fun v hv' => (hQuiet.2.1 v hv').2)
    (fun w hw => (hQuiet.1 w hw).1) (fun v hv' => (hQuiet.2.1 v hv').1) hHeadP hStep hStepLast
    (Finset.Subset.refl _) hQuorum hLockBox hselq hq hqWin hFrameQ hPropose'
  -- every member of `Hon s` saves `B` at its tick to the support cutoff of slot `s + 1` (`round_base_steps`)
  have hSaveB : ∀ v ∈ Hon s, (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B := by
    intro v hv'
    have hU := hHonUpd s le_rfl (by omega) v hv'
    obtain ⟨kU, hkU, -⟩ := Activity.mem_activeThroughoutToTick.1 hU
    have hvc : M.voteTime S.C (s + 1) ≤ M.supportCutoff S.C (s + 1) := by have := hc (s + 1); omega
    obtain ⟨n'', sent'', hrun'', hA'', hsave, -⟩ := (update_state_of_tick M F U) S A x R s v E hkU
      ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hU
        (lt_of_lt_of_le (hdwv (s + 1)) (by exact_mod_cast hvc)))
    rw [hsave]
    exact (hUpd v hv' n'' sent'' hrun'' hA'').1
  refine ⟨h80a, ?_, ?_, ?_, ?_, ?_⟩
  · rcases h80b with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h3, Hon s, hQuorum, h2⟩
  · -- the third conjunct: the round theorem's, over the same members
    exact h80c
  · -- every member saves `B` at its tick to the support cutoff of slot `s + 1` (`round_base_steps`)
    exact hSaveB
  · -- the fifth conjunct: the chain step `lem89s_chain_step` iterated from slot `s − 1`, with the
    -- voters `Hon σ`, the members `Hon (σ + 1)` and the updaters `Hon σ` at each slot `σ`, each from the
    -- `honestActiveAt` row, and the lock step carried with it, for `𝓒` and the ancestors of the confirmations of the
    -- slots from `s − 1` to `σ − 1` saved by the members of each slot's own set; `B` joins as a member's confirmation
    -- of slot `s`
    obtain ⟨iB, hlB, hsentB⟩ := id hPropose
    have hlB₁ : x.lbl iB = Event.tick p (M.slotStart S.C (s - 1 + 1)) := by rw [hsm]; exact hlB
    obtain ⟨hBslot, -, hBpar?, -⟩ := (proposal_parent_walk_end M F U) S A x R E (s - 1) iB B p hlB₁ hsentB
    have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
    -- the frame of every member of `Hon s` at slot `s − 1` relative to `B`
    have hStepB₀ : ∀ w ∈ Hon (s - 1 + 1), StepFrameAt M S A x B (s - 1) w := by
      intro w hw
      rw [hsm] at hw
      have hw1 := hQuiet.1 w hw
      have hw2 := (hQuiet.2.1 w hw).1
      refine (stepFrameAt_proposal_of_quiet M F) S A x R E B (s - 1) w hBslot ?_ ?_ ?_ ?_
      · rw [hsm]; exact hHeld w hw
      · rw [hsm]; exact ancestorEq_trans hw1.1 hPB
      · rw [hsm]
        exact le_trans hw1.2 ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hPB)
      · rw [show s - 1 + 2 = s + 1 by omega]; exact hw2
    have hIter : ∀ n, s - 1 + n ≤ s₂ + 1 →
        ChainInvFor M S A x (Hon (s - 1 + n)) (fun C => 𝓒 C ∨ ∃ σ, s - 1 ≤ σ ∧ σ < s - 1 + n ∧
          ∃ v ∈ Hon σ, ∃ C' : Block V,
            (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' ∧
            C.AncestorEq C') (s - 1 + n) ∧
        ∀ u ∈ Hon (s - 1 + n), LiveLocksOnFamilyAt M S A x (fun C => 𝓒 C ∨ ∃ σ, s - 1 ≤ σ ∧ σ < s - 1 + n ∧
          ∃ v ∈ Hon σ, ∃ C' : Block V,
            (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' ∧
            C.AncestorEq C') (s - 1 + n) u := by
      intro n
      induction n with
      | zero =>
        intro _
        refine ⟨?_, ?_⟩
        · intro C hC
          rcases hC with hC | ⟨σ, h1, h2, -⟩
          · exact hChain C hC
          · omega
        · intro u hu n' sent hrun hA e he hl
          obtain ⟨D, hD, heD⟩ := hFamLocks u hu n' sent hrun hA e he hl
          exact ⟨D, Or.inl hD, heD⟩
      | succ n ih =>
        intro hn
        obtain ⟨hI, hL⟩ := ih (by omega)
        have hcN : M.supportCutoff S.C (s - 1 + n + 1) ≤ M.supportCutoff S.C (s₂ + 2 - 1) := hscm _ _ (by omega)
        have hGSTn : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1 + n) :=
          le_trans hGST (hscm _ _ (Nat.le_add_right _ _))
        have hHonN : Hon (s - 1 + n) ⊆ honestActiveAt M S A x (s - 1 + n) := hHonAct (s - 1 + n) (by omega) (by omega)
        have hHonN' : Hon (s - 1 + n + 1) ⊆ honestActiveAt M S A x (s - 1 + n + 1) :=
          hHonAct (s - 1 + n + 1) (by omega) (by omega)
        have hSubN : Hon (s - 1 + n + 1) ⊆ Hon (s - 1 + n) := hHonMono (s - 1 + n) (by omega) (by omega)
        have hStepN : ∀ C : Block V, ((fun C => 𝓒 C ∨ ∃ σ, s - 1 ≤ σ ∧ σ < s - 1 + n ∧
          ∃ v ∈ Hon σ, ∃ C' : Block V,
            (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' ∧
            C.AncestorEq C') C ∨ ∃ v ∈ Hon (s - 1 + n),
            (x.tickOutput v (M.supportCutoff S.C (s - 1 + n + 1))).savedConfirmation (s - 1 + n) = some C) →
            ∀ w ∈ Hon (s - 1 + n + 1), StepFrameAt M S A x C (s - 1 + n) w := by
          intro C hC w hw
          rcases hC with (hC | ⟨σ, h1, h2, v, hv', C', hC', hCC'⟩) | ⟨v, hv', hC⟩
          · -- a block of `𝓒`: `B`'s parent or an ancestor of it
            refine (stepFrameAt_of_ancestorEq M F) S A x B C (s - 1 + n) w
              (ancestorEq_trans (hFamPar C hC) hPB) ?_
            rcases Nat.eq_zero_or_pos n with rfl | hn0
            · exact hStepB₀ w hw
            · exact hQuiet.2.2.1 (s - 1 + n) (by omega) (by omega) w hw
          · -- an ancestor of a member's confirmation of an earlier slot
            exact (stepFrameAt_of_ancestorEq M F) S A x C' C (s - 1 + n) w hCC'
              (hQuiet.2.2.2.1 (s - 1 + n) (by omega) (by omega) σ h1 (by omega) v hv' C' hC' w hw)
          · -- a member's confirmation of slot `s − 1 + n`
            exact hQuiet.2.2.2.1 (s - 1 + n) (by omega) (by omega) (s - 1 + n) (by omega) le_rfl v hv' C hC w hw
        have hP1 := (lem89s_chain_step_upTo M F U) S A x R GST (s - 1 + n) (Hon (s - 1 + n)) (Hon (s - 1 + n + 1))
          (Hon (s - 1 + n)) _ (E.mono hcN) hNet hSkew hRedeliver (Sy.mono hcN) hΔs
          ((GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M) hcN hRoots)
          (fun k u c hl hcl => hRootsTick k u c hl (le_trans hcl hcN)) hParent hOwner hGSTn hHonN hHonN'
          (hUpdOf _ hHonN) hSubN (hCommittees (s - 1 + n) (by omega) (by omega))
          (hCommittees (s - 1 + n + 1) (by omega) (by omega)) hI (fun u hu => Or.inl (hSubN hu)) hL
          (fun C hC v hv C' hC' => (hI C hC).2.2 v hv C' hC') hStepN
        -- the lock invariant at every member of `Hon (s − 1 + n + 1)`: its reader from the `honestActiveAt` row, its
        -- own confirmation joining the family since it is a member of `Hon (s − 1 + n)`
        have hP2 : ∀ u ∈ Hon (s - 1 + n + 1), LiveLocksOnFamilyAt M S A x (fun C => (fun C => 𝓒 C ∨ ∃ σ, s - 1 ≤ σ ∧ σ < s - 1 + n ∧
          ∃ v ∈ Hon σ, ∃ C' : Block V,
            (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' ∧
            C.AncestorEq C') C ∨
            ∃ v ∈ Hon (s - 1 + n), ∃ C' : Block V,
              (x.tickOutput v (M.supportCutoff S.C (s - 1 + n + 1))).savedConfirmation (s - 1 + n) = some C' ∧
              C.AncestorEq C') (s - 1 + n + 1) u := by
          intro u hu
          have hRd := (reader_lock_of_honestActiveAt M F U) R E hSkew (hHonN' hu)
          rw [show s - 1 + n + 1 + 1 = s - 1 + n + 2 by omega] at hRd
          exact (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u <|
            (liveLocksOnFamilyAt_step M F U) S A x R _ _ (s - 1 + n) u E hSkew hRd (fun C hC => Or.inl hC)
              (fun C hC => Or.inr ⟨u, hSubN hu, C, hC, ancestorEq_refl C⟩) (hL u (hSubN hu))
        refine ⟨?_, ?_⟩
        · intro C hC
          refine hP1 C ?_
          rcases hC with hC | ⟨σ, h1, h2, v, hv', C', hC', hCC'⟩
          · exact Or.inl (Or.inl hC)
          · rcases Nat.lt_or_ge σ (s - 1 + n) with hlt | hge
            · exact Or.inl (Or.inr ⟨σ, h1, hlt, v, hv', C', hC', hCC'⟩)
            · obtain rfl : σ = s - 1 + n := by omega
              exact Or.inr ⟨v, hv', C', hC', hCC'⟩
        · intro u hu n' sent hrun hA e he hl
          obtain ⟨D, hD, heD⟩ := hP2 u hu n' sent hrun hA e he hl
          refine ⟨D, ?_, heD⟩
          rcases hD with (hD | ⟨σ, h1, h2, v, hv', C', hC', hDC'⟩) | ⟨v, hv', C', hC', hDC'⟩
          · exact Or.inl hD
          · exact Or.inr ⟨σ, h1, by omega, v, hv', C', hC', hDC'⟩
          · exact Or.inr ⟨s - 1 + n, by omega, by omega, v, hv', C', hC', hDC'⟩
    have hFinal := (hIter (s₂ + 1 - (s - 1)) (by omega)).1
    rw [show s - 1 + (s₂ + 1 - (s - 1)) = s₂ + 1 by omega] at hFinal
    -- a member of `Hon s`, from the committee majority of slot `s`
    obtain ⟨v₀, hv₀⟩ : (S.P.committee s ∩ Hon s).Nonempty :=
      Finset.card_pos.1 (by have := hCommittees s (by omega) (by omega); omega)
    have hv₀' := (Finset.mem_inter.1 hv₀).2
    rw [h21]
    intro C hC
    rcases hC with hC | hCB | ⟨σ, h1, h2, v, hv', hC⟩
    · exact hFinal C (Or.inl hC)
    · rw [hCB]
      exact hFinal B (Or.inr ⟨s, by omega, by omega, v₀, hv₀', B, hSaveB v₀ hv₀', ancestorEq_refl B⟩)
    · exact hFinal C (Or.inr ⟨σ, h1, by omega, v, hv', C, hC, ancestorEq_refl C⟩)
  · -- the sixth conjunct: the lock step `liveLocksOnFamilyAt_step` iterated from slot `s − 1`; a member
    -- of slot `σ + 1` reads its revocation of slot `σ + 2` from its update window of slot `σ + 1` (`hHonUpd`) or, at the
    -- last slot, from the `honestActiveAt` row (`reader_lock_of_honestActiveAt`); its own confirmation of slot `σ` joins
    -- the family
    have hLk : ∀ n, s - 1 + n ≤ s₂ + 1 → ∀ u ∈ Hon (s - 1 + n), LiveLocksOnFamilyAt M S A x (fun C => 𝓒 C ∨ C = B ∨
        ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s₂ + 2 ∧ ∃ v ∈ Hon s',
          (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C) (s - 1 + n) u := by
      intro n
      induction n with
      | zero =>
        intro _ u hu n' sent hrun hA e he hl
        obtain ⟨D, hD, heD⟩ := hFamLocks u hu n' sent hrun hA e he hl
        exact ⟨D, Or.inl hD, heD⟩
      | succ n ih =>
        intro hn u hu
        have hσ : s - 1 + (n + 1) = s - 1 + n + 1 := by omega
        rw [hσ] at hu ⊢
        have hu₀ : u ∈ Hon (s - 1 + n) := hHonMono (s - 1 + n) (by omega) (by omega) hu
        have hRd : u ∈ A.activeThroughoutToTick x (M.dutyWindowStart S.C (s - 1 + n + 2) : ℤ)
            (M.voteTime S.C (s - 1 + n + 2)) := by
          by_cases hlast : s - 1 + n + 1 ≤ s₂
          · -- an updater of slot `s − 1 + n + 1`: its window to the support cutoff of slot `s − 1 + n + 2`, cut at the
            -- vote time of that slot, its start moved to the model's duty window start
            have hU := hHonUpd (s - 1 + n + 1) (by omega) (by omega) u hu
            have hvt := hv (s - 1 + n + 2)
            have hct := hc (s - 1 + n + 2)
            have hdr := duty_window_start_real S (s - 1 + n + 2)
            have hsR : ((M.slotStart S.C (s - 1 + n + 2) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s - 1 + n + 2 : ℕ) : ℝ) := by
              exact_mod_cast hsE (s - 1 + n + 2)
            have hvR : ((M.voteTime S.C (s - 1 + n + 2) : ℕ) : ℝ) = (M.slotStart S.C (s - 1 + n + 2) : ℝ) + Δ S := by
              exact_mod_cast hvt
            have hcR : ((M.supportCutoff S.C (s - 1 + n + 2) : ℕ) : ℝ) = (M.voteTime S.C (s - 1 + n + 2) : ℝ) + Δ S := by
              exact_mod_cast hct
            push_cast at hsR hdr
            have hU' : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s - 1 + n + 2))
                (M.supportCutoff S.C (s - 1 + n + 2)) := hU
            have hR' := (mem_activeThroughoutToTick_of_le_end_int M x) R E (b' := M.voteTime S.C (s - 1 + n + 2))
              (by omega) (by push_cast; linarith) (by linarith) hU'
            exact Activity.mem_activeThroughoutToTick_of_le
              ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout F.sched U) S
                (s - 1 + n + 2)) hR'
          · -- a member of the last slot: the `honestActiveAt` row
            have he : s - 1 + n + 1 = s₂ + 2 - 1 := by omega
            have h := (reader_lock_of_honestActiveAt M F U) R E hSkew (hHonLast (by rw [← he]; exact hu))
            rwa [show s₂ + 2 - 1 + 1 = s - 1 + n + 2 by omega] at h
        refine (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ _ u <|
          (liveLocksOnFamilyAt_step M F U) S A x R _ _ (s - 1 + n) u E hSkew hRd (fun C hC => hC)
            (fun C hC => Or.inr (Or.inr ⟨s - 1 + n, by omega, by omega, u, hu₀, hC⟩)) (ih (by omega) u hu₀)
    have h := hLk (s₂ + 2 - 1 - (s - 1)) (by omega)
    rw [show s - 1 + (s₂ + 2 - 1 - (s - 1)) = s₂ + 2 - 1 by omega] at h
    exact h

end GoldilocksCorrectness.Record.Proofs.Executions

