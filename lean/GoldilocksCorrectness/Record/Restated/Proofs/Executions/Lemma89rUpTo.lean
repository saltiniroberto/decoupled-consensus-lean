module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89r
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma80UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundBaseUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89WaitJUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89r
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma80UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Proofs.Executions.RoundBaseUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89rUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89rUpTo.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the ordered `head_height_floor` under
unordered delivery, the family's blocks against the proposal's parent, and Lemma 89r, with the
delivery premises up to the bound the theorems read.
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
  slot_add_two_le_of_delivery supportCutoff_eq supportCutoff_le_slotStart_succ voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (head_height_floor_initial)

open GoldilocksCorrectness.Proofs.Routines (initial_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)



open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (HeightCacheBounds)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

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
  ancestorEq_compatible genesis_ancestorEq ancestorEq_of_parent?)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- The honest proposal of slot `s₀ + 1` is on the chain of every block of a family whose blocks
every slot-`s₀` vote of `Hs` extends, when the family holds `p`'s anchor and `p`'s frame has a
viable head on the chain of each of its blocks: every block of the family is `B`'s parent or an
ancestor of it.

Why: a vote of a member of `Hs` extends both a block `C` of the family and `p`'s anchor, so the two
are ordered. When `C` is an ancestor of the anchor, the anchor is an ancestor of `B`'s parent
(the walk starts there). Otherwise `p`'s walk passes `C`
(`proposal_parent_extends_majority_block` with `X := C`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s₀`: the slot of the votes;
- `Hs`: the voters; `𝓒`: the family; `B`: the proposal of slot `s₀ + 1`; `p`: its proposer.

Roots name blocks until the real time of `p`'s tick to the support cutoff of slot `s₀`: the proof compares two
blocks a member of `Hs` holds at its tick to the vote time of slot `s₀` (before that tick, by `hSkew`), and the
proposer's walk (`proposal_parent_extends_majority_block_upTo` at slot `s₀`) reads blocks held up to that tick.

Restated: the members' honesty is read at `p`'s tick to
the start of slot `s₀ + 1`, the members are active through the sync window that starts `max (2 * Δ S) Δs` before the
support cutoff of slot `s₀`, and `p` ticks to that cutoff and is active from the window's
start up to that tick: the hypotheses of `proposal_parent_extends_majority_block_upTo`, which the proof calls.

Restated with the delivery premises up to `M.supportCutoff S.C s₀`: the bound of its roots; its
proof reads deliveries through `proposal_parent_extends_majority_block_upTo` at slot `s₀`.

Read aloud: every block of the family is the honest proposal's parent or an ancestor of it, with the
delivery premises up to the bound. -/
theorem family_ancestorEq_proposal_parent_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ : ℕ) (Hs : Finset V) (𝓒 : Block V → Prop)
    (B : Block V) (p : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s₀)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s₀))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `p`'s own tick to the support cutoff of slot `s₀`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.supportCutoff S.C s₀))))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    -- each member of `Hs` is in the committee of slot `s₀`, outside the adversary set at `p`'s tick to the start of
    -- slot `s₀ + 1`, and put a slot-`s₀` vote on the wire at its tick at the vote time of slot `s₀`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s₀ ∧ u ∉ A.corrupted (x.tickStep p (M.slotStart S.C (s₀ + 1))) ∧
      ∃ vote : GoldfishVote V, ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- each such vote names a block its voter holds that descends from every block of the family
    (hExt : ∀ C : Block V, 𝓒 C → ∀ u ∈ Hs, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s₀)).tree,
        vote = GoldfishVote.mk u s₀ H_u.root ∧ C.AncestorEq H_u)
    -- the validators with a slot-`s₀` vote in `p`'s pool before its proposal are fewer than twice
    -- `Hs`
    (hVotersP : M.voters_count
        (M.votesHeldSet (x.tickInput p (M.slotStart S.C (s₀ + 1))) s₀) < 2 * Hs.card)
    -- every member of `Hs` is active at every step at a real time from `max (2 * Δ S) Δs` before the support cutoff
    -- of slot `s₀` to one sync delay after that
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` ticks to the support cutoff of slot `s₀` at `kR` and is active at every step from the real time
    -- `max (2 * Δ S) Δs` before that cutoff up to `kR`
    (hp : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C s₀) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s₀ - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j)
    -- `p` put `B` on the wire at its tick at the start of slot `s₀ + 1`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s₀ + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `p`'s frame has a viable head on the chain of every block of the family
    (hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).tree,
        W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s₀ + 1)))).viable_heads ∧
          C.AncestorEq W)
    -- the family holds `p`'s anchor
    (hAnchor : 𝓒
        (M.get_anchor (x.tickInput p (M.slotStart S.C (s₀ + 1)))
            ((M.slotStart S.C (s₀ + 1) : ℕ) : Int))) :
    ∀ C : Block V, 𝓒 C → C.AncestorEq B.parent := by
  intro C hC
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hv₀ : M.voteTime S.C s₀ = M.slotStart S.C s₀ + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
  have hc₀ : M.supportCutoff S.C s₀ = M.voteTime S.C s₀ + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  obtain ⟨i, hl, hsent⟩ := hPropose
  have hAP := (get_anchor_ancestorEq_proposal_parent M F) S A x R E (s₀ + 1) i B p hl hsent
  obtain ⟨kR, hkR, hpkR⟩ := hp
  have hkRt := (E.tick_active kR p _ hkR).2.1
  have hRootsK : RootsNameBlocksUntil M A x (x.time kR) := by
    rw [← (tickStep_eq_of_lbl M) x E hkR]; exact hRoots
  -- a member's two blocks named by one root are one block
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨-, -, vote₀, i₀, hl₀, hs₀⟩ := hHs u₀ hu₀
  obtain ⟨H₁, hH₁T, hv₁, hCH₁⟩ := hExt C hC u₀ hu₀ vote₀ ⟨i₀, hl₀, hs₀⟩
  obtain ⟨H₂, hH₂T, hv₂, hAH₂⟩ := hExt _ hAnchor u₀ hu₀ vote₀ ⟨i₀, hl₀, hs₀⟩
  have hroot : H₁.root = H₂.root := by
    rw [hv₁] at hv₂
    exact (GoldfishVote.mk.inj hv₂).2.2
  obtain ⟨hu₀a, -, hi₀t⟩ := E.tick_active i₀ u₀ _ hl₀
  have hu₀c : u₀ ∉ A.corrupted i₀ := (Activity.mem_active.1 hu₀a).2
  have hi₀k : x.time i₀ ≤ x.time kR := by
    have : ((M.voteTime S.C s₀ : ℕ) : ℝ) + Δ S = ((M.supportCutoff S.C s₀ : ℕ) : ℝ) := by
      exact_mod_cast hc₀.symm
    linarith
  have hti : x.tickStep u₀ (M.voteTime S.C s₀) = i₀ := (tickStep_eq_of_lbl M) x E hl₀
  have hH₁T' : H₁ ∈ (x.st i₀ u₀).tree := by rw [← hti]; exact hH₁T
  have hH₂T' : H₂ ∈ (x.st i₀ u₀).tree := by rw [← hti]; exact hH₂T
  have hH : H₁ = H₂ := hRootsK _ _ ((inHonestTreeBy_of_st M F) x R E hu₀c hi₀k hH₁T')
    ((inHonestTreeBy_of_st M F) x R E hu₀c hi₀k hH₂T') hroot
  subst hH
  rcases ancestorEq_compatible hCH₁ hAH₂ with hCA | hAC
  · exact ancestorEq_trans hCA hAP
  · -- `p`'s walk passes `C`
    have hex : ∀ u ∈ Hs, ∃ H_u : Block V,
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
          (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ H_u.root)⟩ :
            SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
        H_u ∈ (x.tickInput u (M.voteTime S.C s₀)).tree ∧ C.AncestorEq H_u := by
      intro u hu
      obtain ⟨-, -, vote, i', hl', hs'⟩ := hHs u hu
      obtain ⟨H_u, hT, hv, hCH⟩ := hExt C hC u hu vote ⟨i', hl', hs'⟩
      subst hv
      exact ⟨H_u, ⟨i', hl', hs'⟩, hT, hCH⟩
    choose Hc hHc using hex
    let Hf : V → Block V := fun u => if h : u ∈ Hs then Hc u h else C
    have hHf : ∀ u (hu : u ∈ Hs), Hf u = Hc u hu := fun u hu => dif_pos hu
    exact ((proposal_parent_extends_majority_block_upTo M F U) S A x R GST s₀ i Hs Hf C B p E hNet hSkew hRedeliver Sy
      hΔs hRoots hParent hOwner hGST
      (fun u hu => by
        rw [hHf u hu]
        exact ⟨(hHs u hu).1, (hHs u hu).2.1, (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩)
      (fun votes_p support_p hP => by rw [hP.1]; exact hVotersP) hHold ⟨kR, hkR, hpkR⟩ hl hsent
      (hFrameP C hC) hAC).1

/-- **Before the round's duty window, a member's justified height is at most the proposal's
height.** When `p` proposes `B` at the start of slot `s + 1`, active at every step from `max (Δ S) Δs` before
the support cutoff of slot `s` up to its tick to that start, the network is synchronous from that window's
start (`hGST`), fewer than a third of the validators have been in the adversary set up to one delay after the
start of slot `s + 1`, and `v` ticks to the vote time of slot `s + 1`, active up to that tick from its tick to a clock
value at most the duty window's start of that slot (rule R3; T-P1-114): `v`'s justified height
before the later of the duty window's start of slot `s + 1` and `GST` is at most the height of `B`'s
chain state.

Why: one delay before the proposal, at the vote time of slot `s`, `v`'s justified height is less
than `B`'s height (`h_j_lt_of_later_proposal_upTo`); it does not decrease from the earlier time to that
vote time (`h_j_mono`). `p`'s tick to the view freeze of slot `s`, which that lemma takes, is before its tick to
the start of slot `s + 1` (`hSkew`), so `p` is active around it.

Restated with the delivery premises up to `M.slotStart S.C (s + 1)`, the bound the leaf reads them at.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `GST`: the time
  from which the network is synchronous; `s + 1`: the proposal's slot; `v`: the member; `p`: the
  proposer; `B`: the proposal.

Read aloud: a validator honest through the round's action time had not justified past the round's
proposal when the round's duty window opened. -/
theorem justifiedHeight_le_of_later_proposal_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (v p : V) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.slotStart S.C (s + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the real time of `p`'s tick to the start
    -- of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V)
        ((M.slotStart S.C (s + 1) + Δ S : ℕ) : ℝ))
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- `v` ticks to the vote time of slot `s + 1`, active up to that tick from the trace's start or from its own tick
    -- to a clock value at most the duty window's start of that slot
    (hvW : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.voteTime S.C (s + 1)))
    -- `p` is active at every step from the real time `max (Δ S) Δs` before the support cutoff of slot `s` up to its
    -- tick to the start of slot `s + 1`
    (hp : ∀ i : ℕ, ((M.supportCutoff S.C s - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep p (M.slotStart S.C (s + 1)) → p ∈ A.active i)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C (s + 1)) GST) v) ≤
      (M.chainStateOf S.C B).h := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hs0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hv₀ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc₀ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hc₁ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hc₂ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s + 1 ≤ s + 1 + 1 by omega)
  have hvf := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  -- the sync delay and three delays fit in the slow window
  have hΔsN : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h0 : (0 : ℝ) ≤ (Δ S : ℝ) := by positivity
    have h1 : (Δs : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_right _ _
    have h2 : (Δs : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by linarith
    exact_mod_cast h2
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hk4 : 4 * Δ S ≤ 4 * Δ S * S.C.k := by
    simpa using Nat.mul_le_mul_left (4 * Δ S) (show 1 ≤ S.C.k by omega)
  -- the duty window of slot `s + 1` opens at least `max (Δ S) Δs` before the support cutoff of slot `s`
  have hdws : M.dutyWindowStart S.C (s + 1) + max (Δ S) Δs ≤ M.supportCutoff S.C s := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (s + 1) with
      h | ⟨h, -⟩
    · rw [Nat.mul_add, Nat.mul_one] at h
      omega
    · omega
  have hdv : M.dutyWindowStart S.C (s + 1) ≤ M.voteTime S.C s := by omega
  -- `p`'s tick to the start of slot `s + 1`
  obtain ⟨i, hl, hsent⟩ := hPropose
  have hti : x.tickStep p (M.slotStart S.C (s + 1)) = i := (tickStep_eq_of_lbl M) x E hl
  obtain ⟨-, hi1, hi2⟩ := E.tick_active i p _ hl
  have hsR : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = ((M.voteTime S.C s : ℕ) : ℝ) + 3 * Δ S := by
    exact_mod_cast (show M.slotStart S.C (s + 1) = M.voteTime S.C s + 3 * Δ S by omega)
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = ((M.voteTime S.C s : ℕ) : ℝ) + Δ S := by
    exact_mod_cast hc₀
  have hfR : ((M.viewFreeze S.C s : ℕ) : ℝ) = ((M.voteTime S.C s : ℕ) : ℝ) + 2 * Δ S := by
    exact_mod_cast (show M.viewFreeze S.C s = M.voteTime S.C s + 2 * Δ S by omega)
  -- `p` ticks to the view freeze of slot `s`, before its tick to the start of slot `s + 1`
  have hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s) := by
    obtain ⟨k, hk, -, -⟩ := E.tick_of_active (M.viewFreeze S.C s) (by omega) p (fun j h1 h2 => by
      refine hp j ?_ ?_
      · have : ((M.supportCutoff S.C s - max (Δ S) Δs : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_le _ _
        linarith
      · rw [hti]
        exact ((lt_of_time_lt M) x R (by linarith)).le)
    exact ⟨k, hk⟩
  -- `v` is honest at the vote time of slot `s`, four delays before its tick to the vote time of slot `s + 1`
  have hvR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = ((M.voteTime S.C s : ℕ) : ℝ) + 4 * Δ S := by
    exact_mod_cast (show M.voteTime S.C (s + 1) = M.voteTime S.C s + 4 * Δ S by omega)
  have hvt : v ∉ A.corruptedAtTime x (M.voteTime S.C s) :=
    (not_mem_corruptedAtTime_of_mem_activeThroughoutToTick M F) x R E hvW (by linarith)
  -- `v` is active through the sync delay's window before the support cutoff of slot `s`: it opens more than
  -- `ΔClockBehind` after the duty window's start of slot `s + 1` (`hΔs`)
  have hvH : v ∈ A.activeThroughout x (((M.voteTime S.C s : ℕ) : ℝ) + ((Δ S : ℕ) : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ))
      (((M.voteTime S.C s : ℕ) : ℝ) + ((Δ S : ℕ) : ℝ)) := by
    have hdR := duty_window_start_real S (s + 1)
    have hsN : M.voteTime S.C s + Δ S = 4 * Δ S * s + 2 * Δ S := by omega
    have hsR : ((M.voteTime S.C s : ℕ) : ℝ) + ((Δ S : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s : ℝ) + 2 * Δ S := by
      have : ((M.voteTime S.C s + Δ S : ℕ) : ℝ) = ((4 * Δ S * s + 2 * Δ S : ℕ) : ℝ) := by rw [hsN]
      push_cast at this; linarith
    have hmR : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
      push_cast; exact hΔs
    have ha : ((duty_window_start S.C (s + 1) : ℤ) : ℝ) + ΔClockBehind <
        ((M.voteTime S.C s : ℕ) : ℝ) + ((Δ S : ℕ) : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ) := by
      rw [hsR, hdR]; push_cast; push_cast at hmR; linarith
    -- `mem_activeThroughout_of_mem_activeThroughoutToTick` with a real window start
    obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hvW
    have hk'b := (E.tick_active k' v _ hk').2.1
    refine Activity.mem_activeThroughout_of_forall fun i h1 h2 => ?_
    have hik' : i < k' := (lt_of_time_lt M) x R (by linarith)
    rcases hcase with h | ⟨k, -, c, hca, hk, h⟩
    · exact h i hik'.le
    · have hka := (E.tick_active k v c hk).2.2
      have hca' : (c : ℝ) ≤ ((duty_window_start S.C (s + 1) : ℤ) : ℝ) := by exact_mod_cast hca
      refine h i ?_ hik'.le
      by_contra hc
      have := R.time_mono (show i + 1 ≤ k by omega)
      linarith
  have hlt := (h_j_lt_of_later_proposal_upTo M F U Fx) S A x R GST (M.slotStart S.C (s + 1) + Δ S) (M.voteTime S.C s) s v p
    B E hNet hSkew hRedeliver Sy hRoots hParent hThird (by omega) (by omega)
    (by rw [hti]; exact le_trans hi2 (by push_cast; linarith))
    hvH
    ((not_mem_corrupted_of_le_time M) x R E hvt ((time_stepBefore_le M) x R E _))
    (fun j h1 h2 => hp j (by rw [hc₀]; exact h1) h2) hpv ⟨i, hl, hsent⟩
  have hRootsV : RootsNameBlocksUntil M A x ((M.voteTime S.C s : ℕ) : ℝ) := by
    refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ hRoots
    rw [hti]
    linarith
  have hmono := (h_j_mono M F Fx) S A x R E hRootsV (M.slotStart S.C (s + 1) + Δ S)
    (max (M.dutyWindowStart S.C (s + 1)) GST) (M.voteTime S.C s) v hThird (max_le hdv (by omega)) (by omega) hvt le_rfl
  exact le_trans hmono hlt.le

open Classical in
/-- **Lemma 89r, a quiet round of the phase.** The proof; the audited statement is in
`Statements/Executions/Lemma89rStatements.lean`.

Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: the round theorem
`lem80wq_round_height_advances_steps` at slot `s''` reads blocks held up to it, and the chain
steps of the slots before `s'' − 1` up to their support cutoffs, at most it.

Restated with the delivery premises up to `M.supportCutoff S.C (s'' - 1)`: the bound of its roots,
for the votes (`hSync`, `hCatch`); the attestations (`hSyncF`, `hCatchF`) up to
`M.slotStart S.C s''`, the bound `lem80wq_round_height_advances_steps_upTo` reads them at.
Its adversary bound (`hThird`), its members' windows (`hHon`, `hHonLast`) and its rows `hHonestQ`, `hHold42` are the
audited `lem89r_quiet_round`'s.

The proposer is read up to its tick to the start of slot `s` from `tStart` (`hp`), with its holder row `hHoldP`, the
members' holder row `hHoldV`, and roots named at every tick to a clock value at most `M.supportCutoff S.C (s'' - 1)`
. The form takes `hGSTF`, the attestations' sync delay elapsed after `GST` by the start of slot `s''`, and passes it
to its round theorem; the round theorem's `hselq` it derives from the proposal at slot `s`
.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in a quiet round of the phase relative to its own confirmations, with the proposer's
frame reaching the family's chain, the next honest proposal extends the round's proposal and makes
progress, every member saves the round's proposal, and both invariants hold at the slot before the
next opening for the family, the proposal and every confirmation the round saved, with the delivery
premises up to the bound. -/
theorem lem89r_quiet_round_upTo (U : UniformSchedule M.toSlotLayout)
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
    (tStart : ℕ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x (tStart : ℤ) (M.slotStart S.C s))
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
    ((∀ u ∈ Hon s, ∀ b ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) u).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
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
  -- `tStart` as the integer the callees take
  have htS : (((tStart : ℤ) : ℝ)) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    exact_mod_cast htStart
  clear htStart
  generalize (tStart : ℤ) = tS at hp htS
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
  have hdwle : duty_window_start S.C s ≤ max tS (duty_window_start S.C s) := le_max_right _ _
  have htStart' : ((max tS (duty_window_start S.C s) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rcases le_total tS (duty_window_start S.C s) with h | h
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
      exact htS
  obtain ⟨hHeld, hBase, hUpd⟩ := (round_base_steps_upTo M F U) S A x R GST s (Hon s) (Hs s) (Hs (s - 1)) H X
    B p (M.head_height_floor (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.head_height_floor (x.tickInput w (M.voteTime S.C s)))
    (M.get_fc_root (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.get_fc_root (x.tickInput w (M.voteTime S.C s))) (E.mono hcut₁) hNet hSkew hRedeliver (Sy.mono hcut₁) hΔs
    (fun k u c hl hcl => hRootsTick k u c hl (le_trans hcl hcut₁)) hParent hOwner hs1
    hGST (hHonUpd s le_rfl (by omega)) (hHonTick s le_rfl (by omega)) (max tS (duty_window_start S.C s)) htStart'
    (Activity.mem_activeThroughoutToTick_of_le (le_max_left tS (duty_window_start S.C s)) hp) hHoldP
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
    (lem80wq_round_height_advances_steps_upTo M F U Fx) S A x R GST r s (s₂ + 2) Hon (Hon s) Hs H X B B' p q
    (M.head_height_floor (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.head_height_floor (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))))
    (M.get_fc_root (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.get_fc_root (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1))))
    E hNet hSkew hRedeliver Sy hΔs hRootsTick hParent hOwner E_F hNet_F hSkew_F Sy_F hΔs_F hs hs1 hs'' hGST hGSTF
    (fun s' h1 h2 => hHonMono s' (by omega) h2) hHon hHonUpd hHonTick hHonLastR
    (fun u hu => hHonestQR u (Finset.mem_inter.1 hu).2) hHold42 hHoldV hHoldF tS htS hp hHoldP hPropose
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
  · -- the third conjunct: an attestation in a member's tick input to the support cutoff of slot `s + 1` is in its
    -- record before the real time of that cutoff (`record_tickInput_cutoff_mem_stateBefore`)
    intro hNo
    refine h80c fun u hu b hb => hNo u hu b ?_
    refine (record_tickInput_cutoff_mem_stateBefore M F U) S A x R E ?_ hb
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S s
    have h1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.supportCutoff S.C s : ℕ) : ℝ) + 4 * Δ S := by
      exact_mod_cast h1
    linarith
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

