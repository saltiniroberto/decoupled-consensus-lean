module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastBase
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89fUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma31UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma32UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastLineUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79UpTo
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealingStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastBase
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma31UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastLineUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma79UpTo
public import GoldilocksCorrectness.Statements.Executions.HealingStatementsUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89FastBaseUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89FastBaseUpTo.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: every honest finalized block
compatible with the fast block up to the support cutoff of the round's third slot, and the base at
the slot after the fast block's round, with the delivery premises up to the bound the theorems read.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_voteTime dutyWindowStart_mono
  dutyWindowStart_of_anchor dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  supportCutoff_cast supportCutoff_eq supportCutoff_mono viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated LocksRevoked)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Kit fact, an honest finalized block is compatible with the fast block.** Under unforgeability
and fewer than a third of the validators in the adversary set up to `tAwakeEnd`: when every honest
attestation sent before the support cutoff of slot `s₀ + 1` has height at most `H₂`; `v` is an updater
of slot `s₀` whose update saves `C'` as the confirmation of slot `s₀`, with `L` an ancestor of `C'`
or `C'`, and `v` holds `L`, at the height `H₂ + 1`, at its tick to the support cutoff of slot `s₀ + 1`;
every updater of a slot later than `s₀` whose tick to that slot's support cutoff is before step `j`
has saved, as that slot's confirmation, a block compatible with `L`; and `w` is honest at step `j`:
then `w`'s finalized block at step `j` is compatible with `L`.

Why: `w`'s finalized block is the finalized block of the chain state of a block `D` it holds. At a
finalization height at most `H₂`, Lemma 68 with `v` holding `L` makes it an ancestor of `L`. Past
`H₂`, it is justified on `D`'s chain (Lemma 66), and its certificate names an entry `E` that an
updater `uₐ` of a slot `s_a ≥ s₀` held at its tick to the support cutoff of slot `s_a + 1`, a step
before `j`, `E` being `uₐ`'s saved confirmation of slot `s_a` or an ancestor of it
(`cert_entry_at_slot_saved`); the finalized block is `E` (roots name blocks). At `s_a = s₀`, `uₐ`'s
and `v`'s saved confirmations are compatible (Lemma 32, both updaters of slot `s₀`); at a later slot,
`hLater` gives `uₐ`'s.

The case of a later slot happens under per-node clocks, at clock bounds 0 included: `uₐ`'s tick to
the support cutoff of slot `s₀ + 2` can come before `w`'s tick to the same clock value, and the
attestation it sends can reach `w` first (F-82-1). `hLater` takes that case as a hypothesis; the
caller supplies it by induction over the ticks to that cutoff.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `GST`: the time from
  which the network is synchronous; `tAwakeEnd`: the phase's end; `s₀`: the first slot of the
  round; `H₂`: the bound on the old attestations; `j`: the step; `v`: the updater whose update saves
  `C'`; `w`: the validator whose finalized block is read; `L`: the block; `C'`: the saved
  confirmation.

Roots name blocks until the later of the real times of step `j` and of `v`'s tick to the support
cutoff of slot `s₀ + 1`: the proof compares (Lemma 68) a block `w` holds at step `j` with `L`, held by
`v` at that tick, and, past `H₂`, `w`'s finalized block with the entry an updater held at a step
before `j`.

Restated with the delivery premises up to `M.supportCutoff S.C s₀ + Δ S`, the bound Lemma 32's twin
(`lem32_saved_confirmations_compatible_state_upTo`) reads at slot `s₀`, the one delivery its proof reads.

Read aloud: when every updater of a later slot that ticked to its cutoff before step `j` saved a
confirmation compatible with the fast block, an honest validator's finalized block at step `j` is
compatible with the fast block, with the delivery premises up to the bound. -/
theorem finalized_compatible_fast_block_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tAwakeEnd s₀ H₂ j : ℕ) (v w : V) (L C' : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s₀ + Δ S)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s₀ + Δ S))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the later of the real times of
    -- step `j` and of `v`'s tick to the support cutoff of slot `s₀ + 1`
    (hRoots : RootsNameBlocksUntil M A x
      (max (x.time j) (x.time (x.tickStep v (M.supportCutoff S.C (s₀ + 1))))))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H₂)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s₀)
    -- step `j`, `v`'s tick to the support cutoff of slot `s₀ + 1` and that cutoff are at most `tAwakeEnd`
    (hEnd : max (x.time j) (x.time (x.tickStep v (M.supportCutoff S.C (s₀ + 1)))) ≤ tAwakeEnd)
    (hcEnd : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd)
    -- `v` is an updater of slot `s₀`, its update saves `C'`, and it holds `L` at that tick
    (hv : v ∈ updaterAt M S A x s₀)
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some C')
    (hLC : L.AncestorEq C')
    (hLv : L ∈ (x.tickInput v (M.supportCutoff S.C (s₀ + 1))).tree)
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    -- every updater of a slot `s_a` later than `s₀` that ticks to the support cutoff of slot `s_a + 1`
    -- before step `j` saves, as the confirmation of slot `s_a`, a block compatible with `L`
    (hLater : ∀ (s_a : ℕ) (u : V) (C : Block V), s₀ < s_a → u ∈ updaterAt M S A x s_a →
      x.tickStep u (M.supportCutoff S.C (s_a + 1)) < j →
      (x.tickOutput u (M.supportCutoff S.C (s_a + 1))).savedConfirmation s_a = some C →
      C.compatible L = true)
    (hw : w ∉ A.corrupted j) :
    (x.st j w).finalized.compatible L = true := by
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hkv : x.tickStep v (M.supportCutoff S.C (s₀ + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  have hvk : v ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s₀ + 1))) := by
    rw [hkv]; exact E.not_mem_corrupted_of_tick hk'
  obtain ⟨D, hD, hFD⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E j w
  rw [hFD]
  by_cases hle : (M.chainStateOf S.C D).h_F ≤ H₂
  · -- Lemma 68: the finalized block is `L` or an ancestor of `L`
    have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
        (max (x.time j) (x.time (x.tickStep v (M.supportCutoff S.C (s₀ + 1))))) :=
      hThird.mono hEnd
    have hFL := (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx)
      S A x R E hRoots j _ w v D L hT hw hvk hD hLv (by rw [hL]; exact Nat.lt_succ_of_le hle) le_rfl
    exact (compatible_iff _ _).2 (Or.inl hFL)
  · have hlt : H₂ < (M.chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
    obtain ⟨hJC, -, hFanc, -⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hFT : (M.chainStateOf S.C D).F ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w D _
        hD hFanc
    have hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
        (max (x.time j) (M.supportCutoff S.C (s₀ + 1))) :=
      ((GoldilocksCorrectness.Record.Proofs.Executions.fewerThanQuorum_of_fewerThanThird M F) A x
        tAwakeEnd hThird).mono
        (max_le ((le_max_left _ _).trans hEnd) (by exact_mod_cast hcEnd))
    -- the certificate's entry, held by an updater `uₐ` of a slot `s_a ≥ s₀` at a tick before `j`
    obtain ⟨s_a, uₐ, Eb, hk, hl, hu, -, hEb, hs₀a, -, -, hroot, Cu, hCu, hECu⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Executions.cert_entry_at_slot_saved M F U Fx) S A x R s₀ H₂
        j w D _ _ E hAdvQ hOld hD
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC)
        hlt
    have hkt : x.time (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) ≤ x.time j :=
      (time_mono M) x R hk.le
    -- one root, so one block
    have hFE : (M.chainStateOf S.C D).F = Eb := hRoots _ _
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w)
        hw (le_max_left _ _) hFT)
      ((GoldilocksCorrectness.Record.Proofs.Executions.onHonestChainAt_inHonestTreeBy M F U) S A x R E _
        uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl (hkt.trans (le_max_left _ _)) hEb) hroot
    rw [hFE]
    rcases Nat.lt_or_ge s₀ s_a with hgt | hle'
    · -- a later slot: `hLater`
      exact compatible_of_ancestorEq_compatible hECu (hLater s_a uₐ Cu hgt hu hk hCu)
    · -- slot `s₀`: Lemma 32 between `uₐ` and `v`
      have hsa : s_a = s₀ := le_antisymm hle' hs₀a
      subst hsa
      have hR32 : RootsNameBlocksUntil M A x
          (max (x.time (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))))
            (x.time (x.tickStep v (M.supportCutoff S.C (s_a + 1))))) :=
        (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
          (max_le (hkt.trans (le_max_left _ _)) (le_max_right _ _)) hRoots
      have hcc := (GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state_upTo
        M F U) S A x R GST _ uₐ v Cu C' E hNet hSkew hRedeliver Sy hΔs hR32 hGST hu hv hCu hSaved
      exact compatible_of_ancestorEq_both hECu hLC hcc

/-- **`fast_block_base_upTo`, a member's view of `L`.** Under `fast_block_base_upTo`'s hypotheses, with `C'` the confirmation `v`'s update saves: a validator `w` honest at the support cutoff of slot `r * R + 2` ticks to the vote time of slot `r * R + 1`, its finalized block there is an ancestor of `L`, its fork-choice root is compatible with `L`, and when that root is an ancestor of `L`, `L` is a viable head of its voter tree. Why: `w` holds `L` at its tick to the view freeze of slot `r * R` (`block_at_tick_of_held_tick`, from `v` holding it), its finalized block is an ancestor of `L` up to `v`'s tick (`finalized_ancestor_of_fast_block_le`), `L` has the greatest chain-state height `H₂ + 1` (`held_height_le_before_action`), so the root is an ancestor of `L` (`fc_root_ancestorEq_of_tall`) and `L` a viable head (`proposal_viable_head_at_tick_st`).

The variables: those of `fast_block_base_upTo`; `C'`: the confirmation of slot `r * R` that `v`'s update saves, with `L` an ancestor of it or it; `w`: a validator outside the adversary set at the support cutoff of slot `r * R + 2`.

Read aloud: every honest validator of the next slot votes from a state in which the fast block is held, finalized-compatible, and a viable head. -/
theorem fast_block_base_upTo_member (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (r * S.C.R + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (r * S.C.R + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (r * S.C.R + 2)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `r * R + 2`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hEnd : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `r * R + 2` is at a real time at most `tAwakeEnd`
    --
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      x.time k ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (C' : Block V)
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (r * S.C.R + 1))).savedConfirmation (r * S.C.R) = some C')
    (hLC' : L.AncestorEq C')
    (w : V) (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (r * S.C.R + 2))) :
    ∃ kV : ℕ, x.lbl kV = Event.tick w (M.voteTime S.C (r * S.C.R + 1)) ∧
        (x.tickInput w (M.voteTime S.C (r * S.C.R + 1))).finalized.AncestorEq L ∧
        (M.fg_to_ac (x.tickInput w (M.voteTime S.C (r * S.C.R + 1)))).fc_root.compatible L = true ∧
        ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (r * S.C.R + 1)))).fc_root.AncestorEq L →
          ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (r * S.C.R + 1)))
            (S.C.t_ ((r * S.C.R + 1) - 1) + 3 * S.C.Δ) (r * S.C.R + 1) W ∧ W ∈
              (M.fg_to_ac (x.tickInput w (M.voteTime S.C (r * S.C.R + 1)))).viable_heads ∧
              L.AncestorEq W) := by
  classical
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  set μ := r * S.C.R with hμ
  have haR : aR M S r = M.supportCutoff S.C (μ + 1) := rfl
  -- the times
  obtain ⟨hv0, hc0, hf0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hv2, hc2, hf2, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 3)
  rw [show μ + 1 + 1 = μ + 2 from rfl] at hs1
  rw [show μ + 2 + 1 = μ + 3 from rfl] at hs2
  have hE1 : M.supportCutoff S.C (μ + 1) ≤ M.supportCutoff S.C (μ + 2) := by omega
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd := le_trans hE1 hEnd
  -- the sync bound over the natural numbers, and the duty windows from slot `μ` on
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hdws : ∀ s : ℕ, μ ≤ s → tGAT + Δ S ≤ M.dutyWindowStart S.C s := fun s hs =>
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT μ
      hAnchor) ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S hs)
  have hdw : ∀ s : ℕ, μ ≤ s → M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S := by
    intro s hs
    have hd := hdws s hs
    have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s with
      h | ⟨h, -⟩
    · rw [hss]; exact h
    · omega
  have hd0 := hdws μ le_rfl
  have hd1 := hdws (μ + 1) (by omega)
  have hd2 := hdws (μ + 2) (by omega)
  have hw0 := hdw μ le_rfl
  have hw1 := hdw (μ + 1) (by omega)
  have hw2 := hdw (μ + 2) (by omega)
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hm6 := le_max_left (6 * Δ S) Δs
  have hm6' := le_max_right (6 * Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  have hGv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C μ := by
    rcases hmax1 with h | h <;> rw [h] at h8 ⊢ <;> omega
  have hGc : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (μ + 1) := by omega
  -- `v`: an updater of slot `μ`, its tick to the action time, its update, its saved confirmation `C'`
  have hupd : v ∈ updaterAt M S A x μ := (hActive μ (by omega) hEnd1 v hv).2
  obtain ⟨k₀', hk₀', -⟩ := Activity.mem_activeThroughoutToTick.1 hupd
  have hk₀S : x.tickStep v (aR M S r) = k₀' := (tickStep_eq_of_lbl M) x E hk₀'
  have hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) := by rw [hk₀S]; exact hk₀'
  have hk₀t := E.tick_active _ v _ hk₀
  have hk₀E : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd := hEndTick _ v _ hk₀ hE1
  -- `v` holds `L` at its tick to the support cutoff of slot `μ`, and at its tick to the action time
  obtain ⟨hl₀, hCT, hFC⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.saved_confirmation_held_compatible_supportCutoff
    M F U) S A x R μ v C' E hSkew hupd hSaved
  have hLv0 : L ∈ (x.tickInput v (M.supportCutoff S.C μ)).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ v C' L hCT hLC'
  have hl₀t := E.tick_active _ v _ hl₀
  have hle0 : x.tickStep v (M.supportCutoff S.C μ) ≤ x.tickStep v (aR M S r) := by
    refine ((lt_of_time_lt M) x R ?_).le
    have h6 : ((M.supportCutoff S.C μ + 4 * Δ S : ℕ) : ℝ) ≤ (aR M S r : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C μ + 4 * Δ S ≤ aR M S r by rw [haR]; omega)
    push_cast at h6
    linarith [hl₀t.2.2, hk₀t.2.1]
  have hLv : L ∈ (x.tickInput v (aR M S r)).tree := (mem_T_mono M F) x R E v hle0 hLv0
  -- the old attestations, step by step, before every step whose real time is less than `aR` less `ΔClockAhead`
  have hOldAt : ∀ i : ℕ, (∀ k : ℕ, k < i → x.time k + ΔClockAhead < ((aR M S r : ℕ) : ℝ)) →
      ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < i → x.lbl k = Event.tick u t →
        u ∉ A.corruptedAtTime x tAwakeEnd →
        (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂ :=
    fun i hi => (oldStep_of_clock M F) R E hOld (by rw [haR]; exact hEnd1) hi
  -- a member `w` of slot `μ + 1`: awake and honest from `tGAT` to the support cutoff of slot `μ + 2`
  have hwT : ∀ w : V, w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) →
      w ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (μ + 2)) := fun w hw =>
    (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hEnd hw
  -- its ticks to the view freeze of slot `μ` and to the vote time of slot `μ + 1`
  have hwTick : ∀ w : V, w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) → ∀ c : ℕ,
      tGAT + Δ S ≤ c → c + Δ S ≤ M.supportCutoff S.C (μ + 2) →
      ∃ k : ℕ, x.lbl k = Event.tick w c ∧ (c : ℝ) - ΔClockAhead ≤ x.time k ∧ x.time k ≤ c + ΔClockBehind := by
    intro w hw c hc1 hc2
    have hc1R : ((tGAT + Δ S : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    have hc2R : ((c + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by exact_mod_cast hc2
    push_cast at hc1R hc2R
    exact E.tick_of_active c (by omega) w fun i h1 h2 =>
      Activity.mem_activeThroughout.1 (hwT w hw) i (by linarith) (by linarith [(time_mono M) x R (Nat.le_succ i)])
  -- at every member: its finalized block at a step before `v`'s tick to the action time is an ancestor of `L`
  have hk2 : x.time (x.tickStep v (aR M S r)) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
    have h4 : ((aR M S r + 4 * Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show aR M S r + 4 * Δ S ≤ M.supportCutoff S.C (μ + 2) by rw [haR]; omega)
    push_cast at h4
    linarith [hk₀t.2.2]
  have hFw : ∀ (w : V) (i : ℕ), x.time i + ΔClockAhead < ((aR M S r : ℕ) : ℝ) → w ∉ A.corrupted i →
      (x.st i w).finalized.AncestorEq L := by
    intro w i hi hwi
    have hik : i ≤ x.tickStep v (aR M S r) := ((lt_of_time_lt M) x R (by linarith [hk₀t.2.1])).le
    exact (finalized_ancestor_of_fast_block_le M F Fx) S A x R tAwakeEnd r H₂ (x.tickStep v (aR M S r)) i v w L E
      (tR := M.supportCutoff S.C (μ + 2)) hRoots hk2 hThird hk₀
      (hOldAt i fun k hk => by linarith [(time_mono M) x R hk.le]) hk₀E hLv hL hik hwi
  -- `L`'s slot is at most `μ`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hslotc : S.C.slot ((M.supportCutoff S.C μ : ℕ) : Int) = μ :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hvU0 : v ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C μ)) := E.not_mem_corrupted_of_tick hl₀
  have hLs : L.slot ≤ μ := by
    have h := (slot_le_clockValue_of_mem_tree M F) R E hvU0 hLv0
    rw [← hslotc]
    exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
      (by exact_mod_cast E.clockValue_le_of_set hvU0 (Or.inl hl₀)))
  have hLc₂ : M.slotStart S.C L.slot ≤ M.supportCutoff S.C μ :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hLs)
      (by omega)
  -- `v` as the holder of `L` over the sync delay from one delay or one sync delay before the support cutoff of slot `μ`
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ, a = M.supportCutoff S.C μ - max (Δ S) Δs := ⟨_, rfl⟩
  have hGc0 : GST + max (Δ S) Δs ≤ M.supportCutoff S.C μ := by
    rcases hmax1 with h | h <;> rw [h] at h8 ⊢ <;> omega
  have ha1 : 1 ≤ a := by omega
  have htGa : tGAT ≤ a := by rcases hmax1 with h | h <;> rw [h] at h8 ha_def <;> omega
  have hvcorr : v ∉ A.corruptedAtTime x ((a + Δs : ℕ) : ℝ) :=
    (not_mem_corruptedAtTime_of_le M) x R E (show a + Δs ≤ aR M S r by rw [haR]; omega) hv
  have hvhold : v ∈ A.activeThroughout x a (a + Δs) := by
    have h := (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake (a := a) (b := a + Δs)
      htGa (by omega) hvcorr
    push_cast at h
    exact h
  have hsa : x.stepBefore a ≤ x.tickStep v (M.supportCutoff S.C μ) := by
    have h1 := ((stepBefore_time M) x R E ha1).1
    have ha : ((a : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C μ : ℕ) : ℝ) := by
      exact_mod_cast (show a + Δ S ≤ M.supportCutoff S.C μ by omega)
    exact ((lt_of_time_lt M) x R (by linarith [hl₀t.2.1])).le
  have hFa : (x.st (x.stepBefore a) v).finalized.compatible L = true :=
    compatible_of_ancestorEq_both ((F_ancestorEq_of_le M F) x R E v hsa) hLC' hFC
  -- every member: its ticks, `L` held, its finalized block, its root and a viable head on `L`
  have hMem : ∀ w : V, w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) →
      ∃ kV : ℕ, x.lbl kV = Event.tick w (M.voteTime S.C (μ + 1)) ∧
        (x.tickInput w (M.voteTime S.C (μ + 1))).finalized.AncestorEq L ∧
        (M.fg_to_ac (x.tickInput w (M.voteTime S.C (μ + 1)))).fc_root.compatible L = true ∧
        ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (μ + 1)))).fc_root.AncestorEq L →
          ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (μ + 1)))
            (S.C.t_ ((μ + 1) - 1) + 3 * S.C.Δ) (μ + 1) W ∧ W ∈
              (M.fg_to_ac (x.tickInput w (M.voteTime S.C (μ + 1)))).viable_heads ∧
              L.AncestorEq W) := by
    intro w hw
    have hwA := hwT w hw
    obtain ⟨kF, hkF, hkF1, hkF2⟩ := hwTick w hw (M.viewFreeze S.C μ) (by omega) (by omega)
    obtain ⟨kV, hkV, hkV1, hkV2⟩ := hwTick w hw (M.voteTime S.C (μ + 1)) (by omega) (by omega)
    obtain ⟨k₂, hk₂, -, -⟩ := hwTick w hw (M.supportCutoff S.C μ) (by omega) (by omega)
    have hwkF : w ∉ A.corrupted kF := E.not_mem_corrupted_of_tick hkF
    have hwkV : w ∉ A.corrupted kV := E.not_mem_corrupted_of_tick hkV
    have hfa : ((M.viewFreeze S.C μ : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C μ + Δ S ≤ aR M S r by rw [haR]; omega)
    have hva : ((M.voteTime S.C (μ + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (μ + 1) + Δ S ≤ aR M S r by rw [haR]; omega)
    have hfv : ((M.viewFreeze S.C μ : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (μ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C μ + Δ S ≤ M.voteTime S.C (μ + 1) by omega)
    have hfc2 : ((M.viewFreeze S.C μ : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
    have hFF := hFw w kF (by linarith) hwkF
    have hFV := hFw w kV (by linarith) hwkV
    have hkFV : kF < kV := (lt_of_time_lt M) x R (by linarith)
    -- `w` holds `L` at its tick to the view freeze of slot `μ`
    have hLF : L ∈ (x.st kF w).tree := by
      by_cases hg : L = Block.genesis
      · rw [hg]
        exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
      have hagt : ((tGAT : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast htGa
      refine (block_at_tick_of_held_tick M F U) S A x R GST (M.supportCutoff S.C (μ + 1)) (M.supportCutoff S.C μ)
        (x.tickStep v (M.supportCutoff S.C μ)) a (M.viewFreeze S.C μ) (M.supportCutoff S.C μ) kF k₂ v w L
        E hNet hSkew hRedeliver Sy
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith) hRoots)
        hParent (by omega) (by omega) (by omega) (by omega) hvhold hl₀ hLv0 hFa hg hkF
        (fun i hi hik => Activity.mem_activeThroughout.1 hwA i
          (by linarith [(time_mono M) x R hik]) (le_trans hagt (le_trans hi ((time_mono M) x R (Nat.le_succ i)))))
        hk₂ (by omega) hLc₂ ((compatible_iff _ _).2 (Or.inl hFF))
    have hLV : L ∈ (x.st kV w).tree := (mem_T_mono M F) x R E w hkFV.le hLF
    have hInv := ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F) S A x R E kV w hwkV).1
    have hMaxEq : (M.chainStateOf S.C L).h = hMax M S.C (x.st kV w) := by
      refine le_antisymm (le_hMax M hLV) ?_
      obtain ⟨D, hD, hDh⟩ := GoldilocksCorrectness.Record.Statements.Routines.exists_eq_hMax M (C := S.C) ⟨L, hLV⟩
      rw [← hDh, hL]
      exact (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ kV kV w D hThird
        (hOldAt kV fun k hk => by linarith [(time_mono M) x R hk.le])
        (hEndTick kV w _ hkV (by omega)) le_rfl hD
    have hRootL : (M.get_fc_root (x.st kV w)).AncestorEq L :=
      (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_of_tall M F) S.C S.P S.X (x.st kV w) hInv L hLV
        hFV hMaxEq
    have hks : x.tickStep w (M.voteTime S.C (μ + 1)) = kV := (tickStep_eq_of_lbl M) x E hkV
    have hksF : x.tickStep w (M.viewFreeze S.C μ) = kF := (tickStep_eq_of_lbl M) x E hkF
    have hTI : x.tickInput w (M.voteTime S.C (μ + 1)) = x.st kV w := by
      show x.st (x.tickStep w (M.voteTime S.C (μ + 1))) w = x.st kV w; rw [hks]
    have hTIF : x.tickInput w (M.viewFreeze S.C μ) = x.st kF w := by
      show x.st (x.tickStep w (M.viewFreeze S.C μ)) w = x.st kF w; rw [hksF]
    -- `w`'s clock is less than the view freeze of slot `μ` before its tick to it
    have hlt := (clockValue_lt_of_tick_of_active M F) E hkF (by omega) (fun j hj hjk =>
      Activity.mem_activeThroughout.1 hwA j (by linarith [(time_mono M) x R hjk])
        (by
          have hgf : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.viewFreeze S.C μ : ℕ) : ℝ) := by
            exact_mod_cast (show tGAT + Δ S ≤ M.viewFreeze S.C μ by omega)
          push_cast at hgf
          linarith [(time_mono M) x R (Nat.le_succ j)]))
    have hφ : M.head_height_floor (x.st kV w) ≤ (M.chainStateOf S.C L).h :=
      ((GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_le_h_max M F) S.C S.P S.X _ hInv).trans
        hMaxEq.symm.le
    obtain ⟨hWt, hWv⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_viable_head_at_tick_st M F U) S A x R
      (M.viewFreeze S.C μ) (μ + 1) w L _ _ E kF kV hkF hlt hkFV.le hwkV (by rw [hTIF]; exact hLF)
      (by rw [Nat.add_sub_cancel]) ⟨rfl, rfl⟩ hRootL hφ
    refine ⟨kV, hkV, by rw [hTI]; exact hFV, ?_, fun _ => ?_⟩
    · rw [hTI, (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
      exact (compatible_iff _ _).2 (Or.inl hRootL)
    · rw [hTI]
      exact ⟨L, (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (μ + 1) L).1
        hWt, hWv, ancestorEq_refl L⟩
  exact hMem w hw

/-- **`fast_block_base_upTo`, the windows.** Under `fast_block_base_upTo`'s hypotheses, for a validator `w` honest at the support cutoff of slot `r * R + 2`: the windows of `v` and of `w` that Lemma 36's and Lemma 42's twins read, from the duty window's start of slot `r * R + 1`.

The variables: those of `fast_block_base_upTo`; `w`: a validator outside the adversary set at the support cutoff of slot `r * R + 2`.

Read aloud: the updater and the member are active through the windows the two lemmas read. -/
theorem fast_block_base_upTo_windows (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (r * S.C.R + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (r * S.C.R + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (r * S.C.R + 2)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `r * R + 2`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hEnd : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `r * R + 2` is at a real time at most `tAwakeEnd`
    --
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      x.time k ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (w : V) (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (r * S.C.R + 2))) :
    ((M.dutyWindowStart S.C (r * S.C.R + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (r * S.C.R + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ∧
    v ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (r * S.C.R + 1) : ℕ) : ℤ) (M.supportCutoff S.C (r * S.C.R + 1)) ∧
    v ∈ A.activeThroughout x ((M.viewFreeze S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
    ((M.dutyWindowStart S.C (r * S.C.R + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C (r * S.C.R) - max (3 * Δ S) Δs : ℕ) : ℝ) ∧
    w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (r * S.C.R + 1) : ℕ) : ℤ) (M.viewFreeze S.C (r * S.C.R)) ∧
    w ∈ A.activeThroughout x ((M.supportCutoff S.C (r * S.C.R + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (r * S.C.R + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
  classical
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  set μ := r * S.C.R with hμ
  have haR : aR M S r = M.supportCutoff S.C (μ + 1) := rfl
  -- the times
  obtain ⟨hv0, hc0, hf0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hv2, hc2, hf2, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 3)
  rw [show μ + 1 + 1 = μ + 2 from rfl] at hs1
  rw [show μ + 2 + 1 = μ + 3 from rfl] at hs2
  have hE1 : M.supportCutoff S.C (μ + 1) ≤ M.supportCutoff S.C (μ + 2) := by omega
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd := le_trans hE1 hEnd
  -- the sync bound over the natural numbers, and the duty windows from slot `μ` on
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hdws : ∀ s : ℕ, μ ≤ s → tGAT + Δ S ≤ M.dutyWindowStart S.C s := fun s hs =>
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT μ
      hAnchor) ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S hs)
  have hdw : ∀ s : ℕ, μ ≤ s → M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S := by
    intro s hs
    have hd := hdws s hs
    have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s with
      h | ⟨h, -⟩
    · rw [hss]; exact h
    · omega
  have hd0 := hdws μ le_rfl
  have hd1 := hdws (μ + 1) (by omega)
  have hd2 := hdws (μ + 2) (by omega)
  have hw0 := hdw μ le_rfl
  have hw1 := hdw (μ + 1) (by omega)
  have hw2 := hdw (μ + 2) (by omega)
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hm6 := le_max_left (6 * Δ S) Δs
  have hm6' := le_max_right (6 * Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  have hGv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C μ := by
    rcases hmax1 with h | h <;> rw [h] at h8 ⊢ <;> omega
  have hGc : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (μ + 1) := by omega
  -- `v`: an updater of slot `μ`, its tick to the action time, its update, its saved confirmation `C'`
  have hupd : v ∈ updaterAt M S A x μ := (hActive μ (by omega) hEnd1 v hv).2
  obtain ⟨k₀', hk₀', -⟩ := Activity.mem_activeThroughoutToTick.1 hupd
  have hk₀S : x.tickStep v (aR M S r) = k₀' := (tickStep_eq_of_lbl M) x E hk₀'
  have hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) := by rw [hk₀S]; exact hk₀'
  have hk₀t := E.tick_active _ v _ hk₀
  have hk₀E : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd := hEndTick _ v _ hk₀ hE1
  -- a member `w` of slot `μ + 1`: awake and honest from `tGAT` to the support cutoff of slot `μ + 2`
  have hwT : ∀ w : V, w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) →
      w ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (μ + 2)) := fun w hw =>
    (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hEnd hw
  -- its ticks to the view freeze of slot `μ` and to the vote time of slot `μ + 1`
  -- the windows of `v` and of a member `w` that Lemma 36's twin and Lemma 42's twin read
  have hdwi : duty_window_start S.C (μ + 1) ≤ ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℤ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U) S (μ + 1)]
    exact Int.self_le_toNat _
  have hvA : v ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℤ) (M.supportCutoff S.C (μ + 1)) := by
    obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hupd
    refine Activity.mem_activeThroughoutToTick.2 ⟨k', hk', ?_⟩
    rcases hcase with h | ⟨k, hkk, c, hc, hl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, hkk, c, le_trans hc hdwi, hl, h⟩
  have htStart : ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (μ + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by
    have hN : M.dutyWindowStart S.C (μ + 1) + Δ S ≤ M.supportCutoff S.C (μ + 1) - max (6 * Δ S) Δs := by
      rcases hmax6 with h | h <;> rw [h] <;> omega
    have hR : ((M.dutyWindowStart S.C (μ + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.supportCutoff S.C (μ + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at hR
    linarith
  have hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C μ - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C μ - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    have hN1 : M.dutyWindowStart S.C (μ + 1) + Δ S ≤ M.viewFreeze S.C μ - max (Δ S) Δs := by
      rcases hmax1 with h | h <;> rw [h] <;> omega
    have hN2 : M.viewFreeze S.C μ - max (Δ S) Δs + Δs + 3 * Δ S ≤ M.supportCutoff S.C (μ + 1) := by
      rcases hmax1 with h | h <;> rw [h] <;> omega
    have hw' := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hvA
      (a' := M.viewFreeze S.C μ - max (Δ S) Δs) (e := M.viewFreeze S.C μ - max (Δ S) Δs + Δs)
      (by
        have hR : ((M.dutyWindowStart S.C (μ + 1) + Δ S : ℕ) : ℝ) ≤
            ((M.viewFreeze S.C μ - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hN1
        push_cast at hR ⊢
        linarith)
      (by
        have hR : ((M.viewFreeze S.C μ - max (Δ S) Δs + Δs + 3 * Δ S : ℕ) : ℝ) ≤
            ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) := by exact_mod_cast hN2
        push_cast at hR ⊢
        linarith)
    push_cast at hw'
    exact hw'
  have htStartW : ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C μ - max (3 * Δ S) Δs : ℕ) : ℝ) := by
    have hN : M.dutyWindowStart S.C (μ + 1) + Δ S ≤ M.viewFreeze S.C μ - max (3 * Δ S) Δs := by
      rcases hmax3 with h | h <;> rw [h] <;> omega
    have hR : ((M.dutyWindowStart S.C (μ + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.viewFreeze S.C μ - max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at hR
    linarith
  have hwW : ∀ w : V, w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) →
      w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℤ) (M.viewFreeze S.C μ) := by
    intro w hw
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E (by omega)
      (by exact_mod_cast (show M.dutyWindowStart S.C (μ + 1) ≤ M.viewFreeze S.C μ by omega)) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ (hwT w hw)
    · have hR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (μ + 1) : ℕ) : ℝ) := by exact_mod_cast hd1
      push_cast at hR ⊢
      linarith
    · have hR : ((M.viewFreeze S.C μ + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.viewFreeze S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
      push_cast at hR ⊢
      linarith
  have hw₀ : ∀ w : V, w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) →
      w ∈ A.activeThroughout x ((M.supportCutoff S.C (μ + 1) - max (Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (μ + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    intro w hw
    refine Activity.mem_activeThroughout_of_le ?_ ?_ (hwT w hw)
    · exact_mod_cast (show tGAT ≤ M.supportCutoff S.C (μ + 1) - max (Δ S) Δs by
        rcases hmax1 with h | h <;> rw [h] at h8 ⊢ <;> omega)
    · have hR : ((M.supportCutoff S.C (μ + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤
          ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (μ + 1) - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (μ + 2) by
          rcases hmax1 with h | h <;> rw [h] <;> omega)
      push_cast at hR ⊢
      linarith
  exact ⟨htStart, hvA, hv₀, htStartW, hwW w hw, hw₀ w hw⟩

/-- **`fast_block_base_upTo`, the live locks of slot `r * R + 1`.** Under `fast_block_base_upTo`'s hypotheses, with `C'` the confirmation `v`'s update saves: every lock entry the revocation of slot `r * R + 1` of a validator `w` honest at the support cutoff of slot `r * R + 2` leaves live is compatible with `L` (Lemma 42's twin, with `w`'s finalized block from `fast_block_base_upTo_member`).

The variables: those of `fast_block_base_upTo`; `C'`: the confirmation of slot `r * R` that `v`'s update saves, with `L` an ancestor of it or it; `w`: a validator outside the adversary set at the support cutoff of slot `r * R + 2`.

Read aloud: a member's live locks of the next slot are compatible with the fast block. -/
theorem fast_block_base_upTo_locks (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (r * S.C.R + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (r * S.C.R + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (r * S.C.R + 2)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `r * R + 2`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hEnd : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `r * R + 2` is at a real time at most `tAwakeEnd`
    --
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      x.time k ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (C' : Block V)
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (r * S.C.R + 1))).savedConfirmation (r * S.C.R) = some C')
    (hLC' : L.AncestorEq C')
    (w : V) (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (r * S.C.R + 2))) :
    ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (r * S.C.R + 1)))
        ((M.voteTime S.C (r * S.C.R + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (r * S.C.R + 1))) (r * S.C.R + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (r * S.C.R + 1)))
          ((M.voteTime S.C (r * S.C.R + 1) : ℕ) : Int) e = true → e.B.compatible L = true := by
  classical
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  set μ := r * S.C.R with hμ
  have haR : aR M S r = M.supportCutoff S.C (μ + 1) := rfl
  -- the times
  obtain ⟨hv0, hc0, hf0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hv2, hc2, hf2, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 3)
  rw [show μ + 1 + 1 = μ + 2 from rfl] at hs1
  rw [show μ + 2 + 1 = μ + 3 from rfl] at hs2
  have hE1 : M.supportCutoff S.C (μ + 1) ≤ M.supportCutoff S.C (μ + 2) := by omega
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd := le_trans hE1 hEnd
  -- the sync bound over the natural numbers, and the duty windows from slot `μ` on
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hdws : ∀ s : ℕ, μ ≤ s → tGAT + Δ S ≤ M.dutyWindowStart S.C s := fun s hs =>
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT μ
      hAnchor) ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S hs)
  have hdw : ∀ s : ℕ, μ ≤ s → M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S := by
    intro s hs
    have hd := hdws s hs
    have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s with
      h | ⟨h, -⟩
    · rw [hss]; exact h
    · omega
  have hd0 := hdws μ le_rfl
  have hd1 := hdws (μ + 1) (by omega)
  have hd2 := hdws (μ + 2) (by omega)
  have hw0 := hdw μ le_rfl
  have hw1 := hdw (μ + 1) (by omega)
  have hw2 := hdw (μ + 2) (by omega)
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hm6 := le_max_left (6 * Δ S) Δs
  have hm6' := le_max_right (6 * Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  have hGv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C μ := by
    rcases hmax1 with h | h <;> rw [h] at h8 ⊢ <;> omega
  have hGc : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (μ + 1) := by omega
  -- `v`: an updater of slot `μ`, its tick to the action time, its update, its saved confirmation `C'`
  have hupd : v ∈ updaterAt M S A x μ := (hActive μ (by omega) hEnd1 v hv).2
  obtain ⟨k₀', hk₀', -⟩ := Activity.mem_activeThroughoutToTick.1 hupd
  have hk₀S : x.tickStep v (aR M S r) = k₀' := (tickStep_eq_of_lbl M) x E hk₀'
  have hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) := by rw [hk₀S]; exact hk₀'
  have hk₀t := E.tick_active _ v _ hk₀
  have hk₀E : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd := hEndTick _ v _ hk₀ hE1
  have hU : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (μ + 1)))
      ((M.supportCutoff S.C (μ + 1) : ℕ) : Int) (μ + 1) n' :=
    (confirmationUpdated_of_phase_tick M F U) x R r v n' sent E hupd hUpdate
  have hRoots42 : RootsNameBlocksUntil M A x ((M.viewFreeze S.C μ : ℝ) + ΔClockBehind) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
      (by
        have h : ((M.viewFreeze S.C μ + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
          exact_mod_cast (show M.viewFreeze S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
        push_cast at h
        linarith) hRoots
  intro n'' sent'' hrun hAw e he _
  obtain ⟨kV, hkV, hFV, -, -⟩ := (fast_block_base_upTo_member M F) U Fx S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL C' hSaved hLC' w hw
  obtain ⟨htStart, hvA, hv₀, htStartW, hwW, hw₀⟩ := (fast_block_base_upTo_windows M F) U Fx S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL w hw
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem42_fast_lock_clears_conflicting_locks_upTo M F U)
    S A x R GST μ L v w n' E hNet hSkew hRedeliver Sy hΔs hRoots42 hParent hGv
    (M.dutyWindowStart S.C (μ + 1)) htStart hvA (M.dutyWindowStart S.C (μ + 1)) htStartW hwW hv₀ hw₀
    hU hFast kV hkV ((compatible_iff _ _).2 (Or.inl hFV)) n''
    ((locksRevoked_of_vote_tickInput M F U) x R (μ + 1) w n'' sent'' hrun hAw) e he

/-- **`fast_block_base_upTo`, the votes of slot `r * R + 1`.** Under `fast_block_base_upTo`'s hypotheses, with `C'` the confirmation `v`'s update saves: every vote of slot `r * R + 1` a member put on the wire is for a block of its tick input that is `L` or a descendant of `L` (Lemma 36's twin, with the frame of `fast_block_base_upTo_member` and the locks of `fast_block_base_upTo_locks`).

The variables: those of `fast_block_base_upTo`; `C'`: the confirmation of slot `r * R` that `v`'s update saves, with `L` an ancestor of it or it.

Read aloud: every honest vote of the next slot extends the fast block. -/
theorem fast_block_base_upTo_votes (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (r * S.C.R + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (r * S.C.R + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (r * S.C.R + 2)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `r * R + 2`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hEnd : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `r * R + 2` is at a real time at most `tAwakeEnd`
    --
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      x.time k ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (C' : Block V) (hC' : M.savedConfirmation n' (r * S.C.R) = some C')
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (r * S.C.R + 1))).savedConfirmation (r * S.C.R) = some C')
    (hLC' : L.AncestorEq C') :
    ∀ u ∈ Hon M S A x (r * S.C.R + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (r * S.C.R + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (r * S.C.R + 1))).tree,
        vote = GoldfishVote.mk u (r * S.C.R + 1) H_u.root ∧ L.AncestorEq H_u := by
  classical
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  set μ := r * S.C.R with hμ
  have haR : aR M S r = M.supportCutoff S.C (μ + 1) := rfl
  -- the times
  obtain ⟨hv0, hc0, hf0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hv2, hc2, hf2, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 3)
  rw [show μ + 1 + 1 = μ + 2 from rfl] at hs1
  rw [show μ + 2 + 1 = μ + 3 from rfl] at hs2
  have hE1 : M.supportCutoff S.C (μ + 1) ≤ M.supportCutoff S.C (μ + 2) := by omega
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd := le_trans hE1 hEnd
  -- the sync bound over the natural numbers, and the duty windows from slot `μ` on
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hdws : ∀ s : ℕ, μ ≤ s → tGAT + Δ S ≤ M.dutyWindowStart S.C s := fun s hs =>
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT μ
      hAnchor) ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S hs)
  have hdw : ∀ s : ℕ, μ ≤ s → M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S := by
    intro s hs
    have hd := hdws s hs
    have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s with
      h | ⟨h, -⟩
    · rw [hss]; exact h
    · omega
  have hd0 := hdws μ le_rfl
  have hd1 := hdws (μ + 1) (by omega)
  have hd2 := hdws (μ + 2) (by omega)
  have hw0 := hdw μ le_rfl
  have hw1 := hdw (μ + 1) (by omega)
  have hw2 := hdw (μ + 2) (by omega)
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hm6 := le_max_left (6 * Δ S) Δs
  have hm6' := le_max_right (6 * Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  have hGv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C μ := by
    rcases hmax1 with h | h <;> rw [h] at h8 ⊢ <;> omega
  have hGc : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (μ + 1) := by omega
  -- `v`: an updater of slot `μ`, its tick to the action time, its update, its saved confirmation `C'`
  have hupd : v ∈ updaterAt M S A x μ := (hActive μ (by omega) hEnd1 v hv).2
  obtain ⟨k₀', hk₀', -⟩ := Activity.mem_activeThroughoutToTick.1 hupd
  have hk₀S : x.tickStep v (aR M S r) = k₀' := (tickStep_eq_of_lbl M) x E hk₀'
  have hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) := by rw [hk₀S]; exact hk₀'
  have hk₀t := E.tick_active _ v _ hk₀
  have hk₀E : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd := hEndTick _ v _ hk₀ hE1
  have hU : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (μ + 1)))
      ((M.supportCutoff S.C (μ + 1) : ℕ) : Int) (μ + 1) n' :=
    (confirmationUpdated_of_phase_tick M F U) x R r v n' sent E hupd hUpdate
  have hRoots1 : RootsNameBlocksUntil M A x (M.supportCutoff S.C (μ + 1)) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by exact_mod_cast hE1) hRoots
  intro w hwH vote hSend
  have hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) := by
    unfold Hon roundMembers at hwH
    exact (Finset.mem_sdiff.1 hwH).2
  obtain ⟨-, -, -, hF2, hF3⟩ := (fast_block_base_upTo_member M F) U Fx S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL C' hSaved hLC' w hw
  obtain ⟨htStart, hvA, hv₀, htStartW, hwW, hw₀⟩ := (fast_block_base_upTo_windows M F) U Fx S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL w hw
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem36c_fast_ancestor_extended_held_upTo M F U)
    S A x R GST μ C' L v w n' vote E hNet hSkew hRedeliver Sy hΔs hRoots1 hParent hGv
    (M.dutyWindowStart S.C (μ + 1)) htStart hvA hv₀ (M.dutyWindowStart S.C (μ + 1)) htStartW hwW hw₀
    hU hC' hLC' hF2 hF3 ((fast_block_base_upTo_locks M F) U Fx S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL C' hSaved hLC' w hw) hSend

/-- **`fast_block_base_upTo`, the confirmations of slot `r * R + 1`.** Under `fast_block_base_upTo`'s hypotheses, with `C'` the confirmation `v`'s update saves and the votes clause of slot `r * R + 1` (`hV`): every member's saved confirmation of slot `r * R + 1` is `L` or a descendant of `L`. Why: Lemma 78's twin at every updater of slot `r * R + 1`, its finalized block compatible with `L` by a strong induction over the step of its tick (`finalized_compatible_fast_block_upTo` at each step).

The variables: those of `fast_block_base_upTo`; `C'`: the confirmation of slot `r * R` that `v`'s update saves, with `L` an ancestor of it or it.

Read aloud: every honest confirmation of the next slot extends the fast block. -/
theorem fast_block_base_upTo_confirmations (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (r * S.C.R + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (r * S.C.R + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (r * S.C.R + 2)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `r * R + 2`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hEnd : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `r * R + 2` is at a real time at most `tAwakeEnd`
    --
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      x.time k ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (C' : Block V)
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (r * S.C.R + 1))).savedConfirmation (r * S.C.R) = some C')
    (hLC' : L.AncestorEq C')
    (hV : ∀ u ∈ Hon M S A x (r * S.C.R + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (r * S.C.R + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (r * S.C.R + 1))).tree,
        vote = GoldfishVote.mk u (r * S.C.R + 1) H_u.root ∧ L.AncestorEq H_u) :
    ∀ u ∈ Hon M S A x (r * S.C.R + 1), ∀ C₁ : Block V,
      (x.tickOutput u (M.supportCutoff S.C (r * S.C.R + 1 + 1))).savedConfirmation (r * S.C.R + 1) = some C₁ →
      L.AncestorEq C₁ := by
  classical
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  set μ := r * S.C.R with hμ
  have haR : aR M S r = M.supportCutoff S.C (μ + 1) := rfl
  -- the times
  obtain ⟨hv0, hc0, hf0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hv2, hc2, hf2, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 3)
  rw [show μ + 1 + 1 = μ + 2 from rfl] at hs1
  rw [show μ + 2 + 1 = μ + 3 from rfl] at hs2
  have hE1 : M.supportCutoff S.C (μ + 1) ≤ M.supportCutoff S.C (μ + 2) := by omega
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd := le_trans hE1 hEnd
  -- the sync bound over the natural numbers, and the duty windows from slot `μ` on
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hdws : ∀ s : ℕ, μ ≤ s → tGAT + Δ S ≤ M.dutyWindowStart S.C s := fun s hs =>
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT μ
      hAnchor) ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S hs)
  have hdw : ∀ s : ℕ, μ ≤ s → M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S := by
    intro s hs
    have hd := hdws s hs
    have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s with
      h | ⟨h, -⟩
    · rw [hss]; exact h
    · omega
  have hd0 := hdws μ le_rfl
  have hd1 := hdws (μ + 1) (by omega)
  have hd2 := hdws (μ + 2) (by omega)
  have hw0 := hdw μ le_rfl
  have hw1 := hdw (μ + 1) (by omega)
  have hw2 := hdw (μ + 2) (by omega)
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hm6 := le_max_left (6 * Δ S) Δs
  have hm6' := le_max_right (6 * Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  have hGv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C μ := by
    rcases hmax1 with h | h <;> rw [h] at h8 ⊢ <;> omega
  have hGc : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (μ + 1) := by omega
  -- `v`: an updater of slot `μ`, its tick to the action time, its update, its saved confirmation `C'`
  have hupd : v ∈ updaterAt M S A x μ := (hActive μ (by omega) hEnd1 v hv).2
  obtain ⟨k₀', hk₀', -⟩ := Activity.mem_activeThroughoutToTick.1 hupd
  have hk₀S : x.tickStep v (aR M S r) = k₀' := (tickStep_eq_of_lbl M) x E hk₀'
  have hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) := by rw [hk₀S]; exact hk₀'
  have hk₀t := E.tick_active _ v _ hk₀
  have hk₀E : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd := hEndTick _ v _ hk₀ hE1
  -- `v` holds `L` at its tick to the support cutoff of slot `μ`, and at its tick to the action time
  obtain ⟨hl₀, hCT, hFC⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.saved_confirmation_held_compatible_supportCutoff
    M F U) S A x R μ v C' E hSkew hupd hSaved
  have hLv0 : L ∈ (x.tickInput v (M.supportCutoff S.C μ)).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ v C' L hCT hLC'
  have hl₀t := E.tick_active _ v _ hl₀
  have hle0 : x.tickStep v (M.supportCutoff S.C μ) ≤ x.tickStep v (aR M S r) := by
    refine ((lt_of_time_lt M) x R ?_).le
    have h6 : ((M.supportCutoff S.C μ + 4 * Δ S : ℕ) : ℝ) ≤ (aR M S r : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C μ + 4 * Δ S ≤ aR M S r by rw [haR]; omega)
    push_cast at h6
    linarith [hl₀t.2.2, hk₀t.2.1]
  have hLv : L ∈ (x.tickInput v (aR M S r)).tree := (mem_T_mono M F) x R E v hle0 hLv0
  -- the old attestations, step by step, before every step whose real time is less than `aR` less `ΔClockAhead`
  have hOldAt : ∀ i : ℕ, (∀ k : ℕ, k < i → x.time k + ΔClockAhead < ((aR M S r : ℕ) : ℝ)) →
      ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < i → x.lbl k = Event.tick u t →
        u ∉ A.corruptedAtTime x tAwakeEnd →
        (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂ :=
    fun i hi => (oldStep_of_clock M F) R E hOld (by rw [haR]; exact hEnd1) hi
  have hcμ : M.supportCutoff S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 1) := by omega
  have hHA1 : Hon M S A x (μ + 1) ⊆ honestActiveAt M S A x (μ + 1) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_subset_honestActiveAt M F U) S A tGAT tAwakeEnd
      (μ + 1) R E hActive (by omega) hEnd).1
  have hUp1 : Hon M S A x (μ + 1) ⊆ updaterAt M S A x (μ + 1) := fun u hu => by
    unfold Hon roundMembers at hu
    exact (hActive (μ + 1) (by omega) hEnd u (Finset.mem_sdiff.1 hu).2).2
  have hCom : (S.P.committee (μ + 1)).card < 2 * (S.P.committee (μ + 1) ∩ Hon M S A x (μ + 1)).card :=
    (GoldilocksCorrectness.Record.Proofs.Executions.committee_majority_of_committeeSleepiness M F) S A x
      (anchorCW S tGAT) (μ + 1) hCommittees
      (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (by omega))) hEnd
  have hRootsP : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (μ + 1) →
      RootsNameBlocksUntil M A x (x.time k) := fun k u c hk hc => hRootsTick k u c hk (le_trans hc hE1)
  -- Lemma 78's twin at an updater of slot `μ + 1`, from its finalized block
  have h78 : ∀ u ∈ updaterAt M S A x (μ + 1),
      (x.tickInput u (M.supportCutoff S.C (μ + 1 + 1))).finalized.compatible L = true →
      ∀ C₁ : Block V,
        (x.tickOutput u (M.supportCutoff S.C (μ + 1 + 1))).savedConfirmation (μ + 1) = some C₁ →
        L.AncestorEq C₁ := fun u hu hF =>
    (confirmations_of_votes_clause_upTo M F U) S A x R GST (μ + 1) (Hon M S A x (μ + 1)) L u E hNet hSkew
      hRedeliver Sy hΔs hRootsP hParent ((votesCastByOwner_of_unforgeability M F) S A x R E)
      hGc hHA1 hCom hV hu hF
  -- every updater of slot `μ + 1` reads, at its tick to the support cutoff of slot `μ + 2`, a finalized block
  -- compatible with `L`: by strong induction over the step of that tick
  have hFin : ∀ k : ℕ, ∀ u ∈ updaterAt M S A x (μ + 1),
      x.tickStep u (M.supportCutoff S.C (μ + 2)) = k →
      (x.tickInput u (M.supportCutoff S.C (μ + 2))).finalized.compatible L = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u hu hku
      obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hu
      have hks : x.tickStep u (M.supportCutoff S.C (μ + 2)) = k' := (tickStep_eq_of_lbl M) x E hk'
      have hkk : k' = k := hks.symm.trans hku
      subst hkk
      have hwk : u ∉ A.corrupted k' := E.not_mem_corrupted_of_tick hk'
      have hR68 : RootsNameBlocksUntil M A x
          (max (x.time k') (x.time (x.tickStep v (M.supportCutoff S.C (μ + 1))))) := by
        rcases max_cases (x.time k') (x.time (x.tickStep v (M.supportCutoff S.C (μ + 1)))) with
          ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
        · exact hRootsTick k' u _ hk' le_rfl
        · exact hRootsTick _ v _ hk₀ hE1
      have hEndM : max (x.time k') (x.time (x.tickStep v (M.supportCutoff S.C (μ + 1)))) ≤ tAwakeEnd :=
        max_le (hEndTick k' u _ hk' le_rfl) (hEndTick _ v _ hk₀ hE1)
      show (x.st (x.tickStep u (M.supportCutoff S.C (μ + 2))) u).finalized.compatible L = true
      rw [hks]
      refine (finalized_compatible_fast_block_upTo M F U Fx) S A x R GST tAwakeEnd μ H₂ k' v u L C' (E.mono hcμ)
        hNet hSkew hRedeliver (Sy.mono hcμ) hΔs hR68 hThird hOld hGv hEndM hEnd1 hupd hSaved hLC' hLv hL ?_ hwk
      intro s_a u' C₁ hlt hu' hk'' hC₁
      obtain ⟨k₁, hk₁, -⟩ := Activity.mem_activeThroughoutToTick.1 hu'
      have hks₁ : x.tickStep u' (M.supportCutoff S.C (s_a + 1)) = k₁ := (tickStep_eq_of_lbl M) x E hk₁
      rw [hks₁] at hk''
      rcases Nat.lt_or_ge s_a (μ + 2) with hs | hs
      · -- slot `μ + 1`: the induction hypothesis at `u'`'s earlier tick, and Lemma 78's twin
        obtain rfl : s_a = μ + 1 := by omega
        have hF₁ := ih k₁ hk'' u' hu' hks₁
        exact (compatible_iff _ _).2 (Or.inr (h78 u' hu' hF₁ C₁ hC₁))
      · -- a later slot: its tick to the support cutoff comes after `u`'s
        exfalso
        have h1 := (E.tick_active _ _ _ hk₁).2.1
        have h2 := (E.tick_active _ _ _ hk').2.2
        have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show μ + 3 ≤ s_a + 1 by omega)
        have h4 : ((M.supportCutoff S.C (μ + 3) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s_a + 1) : ℕ) : ℝ) := by
          exact_mod_cast hmono
        have h23 : ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (μ + 3) : ℕ) : ℝ) := by
          exact_mod_cast (show M.supportCutoff S.C (μ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (μ + 3) by omega)
        have hkk := (time_mono M) x R hk''.le
        linarith
  exact fun u hu C₁ hC₁ => h78 u (hUp1 hu) (hFin _ u (hUp1 hu) rfl) C₁ hC₁

/-- **`fast_block_base_upTo`, the live locks of slot `r * R + 2`.** Under `fast_block_base_upTo`'s hypotheses, with `C'` the confirmation `v`'s update saves and the live locks of slot `r * R + 1` at every member (`hL42`): the live locks the revocation of slot `r * R + 2` of a member leaves are compatible with `L` (`locks_step_of_clauses`, with Lemma 32's twin for the member's confirmation of slot `r * R`).

The variables: those of `fast_block_base_upTo`; `C'`: the confirmation of slot `r * R` that `v`'s update saves, with `L` an ancestor of it or it.

Read aloud: a member's live locks of the slot after next are compatible with the fast block. -/
theorem fast_block_base_upTo_live_locks (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (r * S.C.R + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (r * S.C.R + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (r * S.C.R + 2)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `r * R + 2`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hEnd : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `r * R + 2` is at a real time at most `tAwakeEnd`
    --
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      x.time k ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (C' : Block V)
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (r * S.C.R + 1))).savedConfirmation (r * S.C.R) = some C')
    (hLC' : L.AncestorEq C')
    (hL42 : ∀ w : V, w ∉ A.corruptedAtTime x (M.supportCutoff S.C (r * S.C.R + 2)) →
      ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (r * S.C.R + 1)))
        ((M.voteTime S.C (r * S.C.R + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (r * S.C.R + 1))) (r * S.C.R + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (r * S.C.R + 1)))
          ((M.voteTime S.C (r * S.C.R + 1) : ℕ) : Int) e = true → e.B.compatible L = true) :
    ∀ w ∈ Hon M S A x (r * S.C.R + 1), ∀ (n₂ : M.N) (sent₂ : List (NamedObject V)),
      .ok (n₂, sent₂) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (r * S.C.R + 1 + 1)))
        ((M.voteTime S.C (r * S.C.R + 1 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (r * S.C.R + 1 + 1))) (r * S.C.R + 1 + 1) →
      ∀ e ∈ M.lockEntries n₂,
        M.is_live (x.tickInput w (M.voteTime S.C (r * S.C.R + 1 + 1)))
          ((M.voteTime S.C (r * S.C.R + 1 + 1) : ℕ) : Int) e = true → e.B.compatible L = true := by
  classical
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  set μ := r * S.C.R with hμ
  have haR : aR M S r = M.supportCutoff S.C (μ + 1) := rfl
  -- the times
  obtain ⟨hv0, hc0, hf0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hv2, hc2, hf2, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 3)
  rw [show μ + 1 + 1 = μ + 2 from rfl] at hs1
  rw [show μ + 2 + 1 = μ + 3 from rfl] at hs2
  have hE1 : M.supportCutoff S.C (μ + 1) ≤ M.supportCutoff S.C (μ + 2) := by omega
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd := le_trans hE1 hEnd
  -- the sync bound over the natural numbers, and the duty windows from slot `μ` on
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hdws : ∀ s : ℕ, μ ≤ s → tGAT + Δ S ≤ M.dutyWindowStart S.C s := fun s hs =>
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT μ
      hAnchor) ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S hs)
  have hdw : ∀ s : ℕ, μ ≤ s → M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S := by
    intro s hs
    have hd := hdws s hs
    have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s with
      h | ⟨h, -⟩
    · rw [hss]; exact h
    · omega
  have hd0 := hdws μ le_rfl
  have hd1 := hdws (μ + 1) (by omega)
  have hd2 := hdws (μ + 2) (by omega)
  have hw0 := hdw μ le_rfl
  have hw1 := hdw (μ + 1) (by omega)
  have hw2 := hdw (μ + 2) (by omega)
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hm6 := le_max_left (6 * Δ S) Δs
  have hm6' := le_max_right (6 * Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  have hGv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C μ := by
    rcases hmax1 with h | h <;> rw [h] at h8 ⊢ <;> omega
  have hGc : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (μ + 1) := by omega
  -- `v`: an updater of slot `μ`, its tick to the action time, its update, its saved confirmation `C'`
  have hupd : v ∈ updaterAt M S A x μ := (hActive μ (by omega) hEnd1 v hv).2
  obtain ⟨k₀', hk₀', -⟩ := Activity.mem_activeThroughoutToTick.1 hupd
  have hk₀S : x.tickStep v (aR M S r) = k₀' := (tickStep_eq_of_lbl M) x E hk₀'
  have hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) := by rw [hk₀S]; exact hk₀'
  have hk₀t := E.tick_active _ v _ hk₀
  have hk₀E : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd := hEndTick _ v _ hk₀ hE1
  have hcμ : M.supportCutoff S.C μ + Δ S ≤ M.supportCutoff S.C (μ + 1) := by omega
  intro w hw n₂ sent₂ hrun₂ hAw₂ e₂ he₂ hlive₂
  have hwc : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) := (Finset.mem_sdiff.1 hw).2
  have hwU : w ∈ updaterAt M S A x μ :=
    (hActive μ (by omega) hEnd1 w ((not_mem_corruptedAtTime_of_le M) x R E hE1 hwc)).2
  have hL2 := hL42 w hwc
  have htickE : ∀ {u : V} {k c : ℕ}, x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (μ + 1) →
      x.time k ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
    intro u k c hk hc
    have h1 := (E.tick_active k u c hk).2.2
    have h2 : ((c + Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show c + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
    push_cast at h2
    linarith
  -- `w`'s saved confirmation of slot `μ` is compatible with `v`'s (Lemma 32's twin), so with `L`
  have hL3 : ∀ C₁ : Block V,
      (x.tickOutput w (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C₁ → C₁.compatible L = true := by
    intro C₁ hC₁
    obtain ⟨kw, hkw, -⟩ := Activity.mem_activeThroughoutToTick.1 hwU
    have hRoots' : RootsNameBlocksUntil M A x (max (x.time (x.tickStep w (M.supportCutoff S.C (μ + 1))))
        (x.time (x.tickStep v (M.supportCutoff S.C (μ + 1))))) := by
      rw [(tickStep_eq_of_lbl M) x E hkw]
      exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (max_le (htickE hkw le_rfl) (htickE hk₀ le_rfl)) hRoots
    exact compatible_of_ancestorEq_both (ancestorEq_refl C₁) hLC'
      ((GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state_upTo M F U) S A x R
        GST μ w v C₁ C' (E.mono hcμ) hNet hSkew hRedeliver (Sy.mono hcμ) hΔs hRoots' hGv hwU hupd hC₁ hSaved)
  -- `w`'s reader up to its tick to the vote time of slot `μ + 1`, from its window from `tGAT`
  have hHon : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (μ + 2) : ℕ) : ℤ) (M.voteTime S.C (μ + 1)) := by
    have hdv : M.dutyWindowStart S.C (μ + 2) ≤ M.voteTime S.C (μ + 1) := by omega
    have hdR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (μ + 2) : ℕ) : ℝ) := by exact_mod_cast hd2
    push_cast at hdR
    have hve : ((M.voteTime S.C (μ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (μ + 1) + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E (by omega) (by exact_mod_cast hdv) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_
      ((mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hEnd hwc)
    · push_cast; linarith
    · linarith
  exact (locks_step_of_clauses M F U) S A x R L μ w E hL2 hL3 hHon n₂
    ((locksRevoked_of_vote_tickInput M F U) x R (μ + 2) w n₂ sent₂ hrun₂ hAw₂) e₂ he₂ hlive₂

/-- **A5, the slot invariant restricted to `L` at slot `r * R + 1`.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`.

The route, with `s₀ := r * R`: `v`'s update saves a confirmation `C'` of slot `s₀` with `L` an
ancestor of it or it (`update_confirmation_fast_block_saved`), and Lemma 36 at `L` gives the early
supporters `Sup`, not empty by the eligibility test. At every member `w` (honest at the support
cutoff of slot `s₀ + 2`): `w`'s finalized block before the vote time of slot `s₀ + 1` is an
ancestor of `L` (A3); Lemma 63 puts a descendant of `L`, so `L`, in `w`'s tree before the view
freeze of slot `s₀`; so `w`'s greatest chain-state height `hMax M S.C n` is `H₂ + 1` (A2 bounds it,
`L` reaches it), and its root is an ancestor of `L` (`fc_root_ancestorEq_of_tall`); `L` is in its
voter tree and a viable head (`proposal_viable_head_at`); Lemma 42 makes its locks compatible with
`L`; A4 gives the votes. The live locks of slot `s₀ + 1`: `locks_step_of_clauses`, with Lemma 42 for
the entries of earlier slots and Lemma 31 for `w`'s confirmation of slot `s₀`. The confirmations:
Lemma 79c, with the honest committee members of slot `s₀ + 1` among the members, and
`finalized_compatible_fast_block`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the
  bound on the old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast
  block; `n'`, `sent`: an outcome of `v`'s tick at the support cutoff of slot `r * R + 1`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome of `v`'s
tick at the support cutoff from its node state before it (template A2), without A2's hypothesis
that `v` has been awake since the duty window's start of the slot: `hAwake` and `hv` give it
(`v` is awake from `tGAT`, one delay before the duty window of slot `r * R`, to the cutoff).

Roots name blocks until `M.supportCutoff S.C (r * S.C.R + 2)`: `finalized_compatible_fast_block` at
the support cutoff of slot `r * R + 2`, for the confirmations of slot `r * R + 1`; the other
steps read up to the support cutoff of slot `r * R + 1`.

Restated with the delivery premises up to `M.supportCutoff S.C (r * S.C.R + 1)`: Lemmas 63, 42, 36c
and 79c read deliveries due by the support cutoff of slot `r * R + 1`, Lemma 31 and
`finalized_compatible_fast_block_upTo` by one delay after the support cutoff of slot `r * R`.

Read aloud: the slot after the fast block's round, every honest vote, live lock and confirmation
extends the fast block, with the delivery premises up to the bound. -/
theorem fast_block_base_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (r * S.C.R + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (r * S.C.R + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (r * S.C.R + 2)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `r * R + 2`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hEnd : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `r * R + 2` is at a real time at most `tAwakeEnd`
    --
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      x.time k ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    HonestChainExtends M S A x (Hon M S A x (r * S.C.R + 1)) L (r * S.C.R + 1) := by
  classical
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  set μ := r * S.C.R with hμ
  have haR : aR M S r = M.supportCutoff S.C (μ + 1) := rfl
  -- the times
  obtain ⟨hv0, hc0, hf0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨hv2, hc2, hf2, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 3)
  rw [show μ + 1 + 1 = μ + 2 from rfl] at hs1
  rw [show μ + 2 + 1 = μ + 3 from rfl] at hs2
  have hE1 : M.supportCutoff S.C (μ + 1) ≤ M.supportCutoff S.C (μ + 2) := by omega
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd := le_trans hE1 hEnd
  -- the sync bound over the natural numbers, and the duty windows from slot `μ` on
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hdws : ∀ s : ℕ, μ ≤ s → tGAT + Δ S ≤ M.dutyWindowStart S.C s := fun s hs =>
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT μ
      hAnchor) ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S hs)
  have hdw : ∀ s : ℕ, μ ≤ s → M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S := by
    intro s hs
    have hd := hdws s hs
    have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s with
      h | ⟨h, -⟩
    · rw [hss]; exact h
    · omega
  have hd0 := hdws μ le_rfl
  have hd1 := hdws (μ + 1) (by omega)
  have hd2 := hdws (μ + 2) (by omega)
  have hw0 := hdw μ le_rfl
  have hw1 := hdw (μ + 1) (by omega)
  have hw2 := hdw (μ + 2) (by omega)
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hm6 := le_max_left (6 * Δ S) Δs
  have hm6' := le_max_right (6 * Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  have hGv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C μ := by
    rcases hmax1 with h | h <;> rw [h] at h8 ⊢ <;> omega
  have hGc : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (μ + 1) := by omega
  -- `v`: an updater of slot `μ`, its tick to the action time, its update, its saved confirmation `C'`
  have hupd : v ∈ updaterAt M S A x μ := (hActive μ (by omega) hEnd1 v hv).2
  obtain ⟨k₀', hk₀', -⟩ := Activity.mem_activeThroughoutToTick.1 hupd
  have hk₀S : x.tickStep v (aR M S r) = k₀' := (tickStep_eq_of_lbl M) x E hk₀'
  have hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) := by rw [hk₀S]; exact hk₀'
  have hk₀t := E.tick_active _ v _ hk₀
  have hk₀E : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd := hEndTick _ v _ hk₀ hE1
  have hU : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (μ + 1)))
      ((M.supportCutoff S.C (μ + 1) : ℕ) : Int) (μ + 1) n' :=
    (confirmationUpdated_of_phase_tick M F U) x R r v n' sent E hupd hUpdate
  obtain ⟨C', hC', hLC'⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 _) hU hFast
  rw [Nat.add_sub_cancel] at hC'
  have hSaved : (x.tickOutput v (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C' :=
    ((state_saved_of_update M F U) S A x R μ v n' E hupd hU).trans hC'
  have hV := (fast_block_base_upTo_votes M F) U Fx S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL C' hC' hSaved hLC'
  exact ⟨hV, (fast_block_base_upTo_live_locks M F) U Fx S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL C' hSaved hLC'
      (fun w hw => (fast_block_base_upTo_locks M F) U Fx S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL C' hSaved hLC' w hw),
    (fast_block_base_upTo_confirmations M F) U Fx S A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL C' hSaved hLC' hV⟩

end GoldilocksCorrectness.Record.Proofs.Executions

