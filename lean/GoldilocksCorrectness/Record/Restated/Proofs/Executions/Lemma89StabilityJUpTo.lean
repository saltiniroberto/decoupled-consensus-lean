module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityB6UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89StabilityJUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89StabilityJUpTo.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the theorems of
`Lemma89StabilityJ.lean` that name a delivery premise, namely an honest vote extending the finalized
block, a validator's finalized block and fork-choice root compatible with another validator's viable
block, the bundle `B6CtxUpTo` of B6's hypotheses with its readers, and B6 itself,
`stability_fact3_upTo`, with the delivery premises up to the bound the theorems read. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_voteTime dutyWindowStart_mono
  dutyWindowStart_of_anchor dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_mono
  supportCutoff_eq supportCutoff_mono viewFreeze_eq voteTime_eq voteTime_mono)

open GoldilocksCorrectness.Proofs.Routines (compatible_symm')

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The view freeze of slot `σ − 1` is at most the vote time of slot `σ`, for `σ ≥ 1`.

Why: the view freeze is three delays into slot `σ − 1`, and the vote time one delay into slot `σ`, which starts four
delays after slot `σ − 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `σ`: the slot.

Read aloud: the view freeze of the slot before `σ` comes no later than the vote time of slot `σ`. -/
theorem viewFreeze_pred_le_voteTime (U : UniformSchedule M.toSlotLayout) (S : Setup V) {σ : ℕ} (hσ : 1 ≤ σ) :
    M.viewFreeze S.C (σ - 1) ≤ M.voteTime S.C σ := by
  obtain ⟨-, -, hvf, hss, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ - 1)
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  rw [show σ - 1 + 1 = σ by omega] at hss
  omega

/-- **With no fork-choice change, an honest vote of slot `σ` extends the finalized block of a
validator honest at a step `i`** (the step form of `vote_extends_finalized_at_of_no_change`, F-P1-2).
The hypotheses of that theorem, with `v` read at the step `i` in place of before the time `b`: `v`
is honest at `i` and at the time `a₀` (`2Δ` into slot `σ − 1`), `i` is at or after the last step
before `a₀`, the time of `i` is at most `tB`, which is at least one delay after the vote time of slot
`σ` and at most `tEnd`, and `v` has no `ForkChoiceChangeStep` at a step whose real time is at least
`a₀`, before `i` — then `vote` is `u`'s slot-`σ` vote for a block `H_u` it holds at its tick, and
`v`'s finalized block at the step `i` is `H_u` or an ancestor of `H_u`.

Why: `vote_extends_finalized_at_of_no_change`'s argument, with `v`'s states read at steps: the step at
which `v`'s cache reaches `f` lies between the last step before `a₀` and `i` (`exists_crossing_st`),
and `v`'s finalized block at the last step before `a₀` is an ancestor of the one at `i`
(`F_ancestorEq_of_le`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `tB`: the times; `i`: the
  step `v` is read at; `σ`: the slot of the vote; `u`: the voter; `v`: the validator whose finalized
  block is read; `vote`: the vote.

Roots name blocks until `tB`: the proof reads `v`'s blocks at steps up to `i`, `u`'s at its tick to the
vote time of slot `σ`, both at times at most `tB`.

Restated with the delivery premises up to `tE`, at least the view freeze of slot `σ − 1`: the delivery its
proof reads (`mem_T_of_delivery_high_st`, from `2Δ` into slot `σ − 1`) is due by then.


Restated: `v` outside the adversary set to the view freeze of
slot `σ − 1` (`hva`), one delay later than before, so that it holds through the sync window of the delivery read
at `u`'s tick (`mem_T_of_delivery_high_st`).

Read aloud: with no fork-choice change, an honest vote of slot `σ` is for a block that has as
ancestor, or is, the finalized block of a validator honest at a step `i`. -/
theorem vote_extends_finalized_st_of_no_change_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd σ : ℕ) (tB : ℝ) (i : ℕ) (u v : V) (vote : GoldfishVote V)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tB)
    (hParent : ParentHeldAtDelivery M x)
    -- the delivery premises reach the view freeze of slot `σ − 1`
    (htE : M.voteTime S.C σ ≤ tE)
    -- from `a` on, the network is synchronous and every validator outside the adversary set is awake
    -- through `tEnd`; `a` is early enough for the windows the proof reads
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ M.viewFreeze S.C (σ - 1))
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hσ : 1 ≤ σ) (hGST : GST ≤ M.slotStart S.C (σ - 1) + 2 * Δ S)
    (hEnd : tB ≤ (tEnd : ℝ)) (hab : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ tB) (hiB : x.time i ≤ tB)
    (hai : x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) ≤ i)
    (hv : v ∉ A.corrupted i)
    -- `v` is outside the adversary set to the view freeze of slot `σ − 1`, one delay after `a₀`
    (hva : v ∉ A.corruptedAtTime x ((M.viewFreeze S.C (σ - 1) : ℕ) : ℝ))
    (hu : u ∈ A.activeThroughout x (M.slotStart S.C (σ - 1) + 2 * Δ S) (M.voteTime S.C σ))
    (hNoV : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → j < i →
      ¬ ForkChoiceChangeStep M S A x v j)
    (hNoU : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → j < x.tickStep u (M.voteTime S.C σ) →
      ¬ ForkChoiceChangeStep M S A x u j)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree,
      vote = GoldfishVote.mk u σ H_u.root ∧
      (x.st i v).finalized.AncestorEq H_u := by
  -- the times: `a₀`, the view freeze `a₀ + Δ`, the vote time and `b`
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hσ' : σ - 1 + 1 = σ := Nat.sub_add_cancel hσ
  have hss : M.slotStart S.C σ = M.slotStart S.C (σ - 1) + 4 * Δ S := by
    rw [← hσ', (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one, hσ']
  have hfz : M.viewFreeze S.C (σ - 1) = M.slotStart S.C (σ - 1) + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (σ - 1)
  have hvt : M.voteTime S.C σ = M.slotStart S.C σ + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hfzΔ : M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S = M.viewFreeze S.C (σ - 1) := by omega
  -- `u`'s tick to the vote time, at a real time before `b`
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hSend
    exact x.lbl_tickStep ⟨i, hi⟩
  have hkUt := E.tick_active _ u _ hkU
  have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := E.not_mem_corrupted_of_tick hkU
  have hbE : tB ≤ (tEnd : ℝ) := hEnd
  have hvtE : M.voteTime S.C σ ≤ tEnd + Δ S := by
    have h : ((M.voteTime S.C σ : ℕ) : ℝ) ≤ ((tEnd + Δ S : ℕ) : ℝ) := by
      push_cast; linarith [(E.tick_active _ u _ (by obtain ⟨i, hi, -⟩ := hSend; exact x.lbl_tickStep ⟨i, hi⟩)).2.1]
    exact_mod_cast h
  have hkUb : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ (tB : ℝ) := hab
  have hkUE : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ (tEnd : ℝ) := le_trans hkUb hbE
  have hThirdb : A.AdversaryFewerThanThirdUntil x (validator_count V) tB := hThird.mono hEnd
  -- the view freeze's step comes before the tick
  have hvf1 : 1 ≤ M.viewFreeze S.C (σ - 1) := by omega
  obtain ⟨hvfs, hvfs'⟩ := (stepBefore_time M) x R E hvf1
  have hvfU : x.stepBefore (M.viewFreeze S.C (σ - 1)) ≤ x.tickStep u (M.voteTime S.C σ) := by
    apply le_of_lt
    apply (lt_of_time_lt M) x R
    have : ((M.viewFreeze S.C (σ - 1) : ℕ) : ℝ) + 2 * Δ S ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C (σ - 1) + 2 * Δ S ≤ M.voteTime S.C σ by omega)
    linarith [hkUt.2.1]
  have hufz : u ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (σ - 1))) := E.not_mem_corrupted_of_le hvfU huk
  have hInvU := (lem11_node_invariant M F S A x R E (x.tickStep u (M.voteTime S.C σ)) u huk).1
  -- the step before `a₀` comes before the tick, and `u`'s clock value there is less than the view freeze
  have ha1 : 1 ≤ M.slotStart S.C (σ - 1) + 2 * Δ S := by omega
  obtain ⟨has, has'⟩ := (stepBefore_time M) x R E ha1
  have haU : x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) ≤ x.tickStep u (M.voteTime S.C σ) :=
    le_trans ((stepBefore_mono M) x R E (show M.slotStart S.C (σ - 1) + 2 * Δ S ≤ M.viewFreeze S.C (σ - 1) by omega)) hvfU
  have hua : u ∉ A.corrupted (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) := E.not_mem_corrupted_of_le haU huk
  have hcka : x.clockValue (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) u < M.viewFreeze S.C (σ - 1) := by
    have h1 := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) u
    have hvfR : ((M.viewFreeze S.C (σ - 1) : ℕ) : ℝ) = ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) + Δ S := by
      rw [← hfzΔ]; push_cast; ring
    have hvf0 : (0 : ℝ) < ((M.viewFreeze S.C (σ - 1) : ℕ) : ℝ) := by exact_mod_cast (show 0 < M.viewFreeze S.C (σ - 1) by omega)
    have h2 : ((x.clockValue (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) u : ℕ) : ℝ) <
        ((M.viewFreeze S.C (σ - 1) : ℕ) : ℝ) :=
      lt_of_le_of_lt h1 (max_lt hvf0 (by rw [hvfR]; linarith [hSkew]))
    exact_mod_cast h2
  -- the vote
  obtain ⟨H_u, hHT, hvote, hρH, hG⟩ := (honest_vote_spec M F U) S A x R E σ u vote hSend
  refine ⟨H_u, hHT, hvote, ?_⟩
  -- `v`'s finalized block `F'`, finalized by the chain state of `D` at the height `f`
  obtain ⟨D, hD, hF⟩ := (finalizedFromChain_of_exec M F) S A x R E
    i v
  have htbb : x.time i ≤ (tB : ℝ) := hiB
  have hvsb : v ∉ A.corrupted i := hv
  have hmaxb : max (x.time (i)) (x.time (x.tickStep u (M.voteTime S.C σ))) ≤ (tB : ℝ) :=
    max_le htbb hkUb
  have hThirdm : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time (i)) (x.time (x.tickStep u (M.voteTime S.C σ)))) :=
    hThirdb.mono hmaxb
  by_cases hgen : (x.st i v).finalized = Block.genesis
  · rw [hgen]
    exact genesis_ancestorEq H_u
  have hf1 : 1 ≤ (M.chainStateOf S.C D).h_F := by
    by_contra h0
    apply hgen
    rw [hF]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D
      (Nat.lt_one_iff.mp (Nat.lt_of_not_le h0))
  obtain ⟨hcertF, -, hFD, hFh⟩ :=
    ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 hf1
  rw [← hF] at hcertF hFD hFh
  have hFT : (x.st i v).finalized ∈
      (x.st i v).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ v D _ hD hFD
  have hjD : (M.chainStateOf S.C D).h_j ≤
      (x.st i v).justifiedHeight :=
    (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E _ v D hD hFD
  have hFjD := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.2
  -- `G`: when `u`'s `head_height_floor` is greater than `f`, the vote extends `F'`
  have G : (M.chainStateOf S.C D).h_F <
      M.head_height_floor (x.tickInput u (M.voteTime S.C σ)) →
      (x.st i v).finalized.AncestorEq H_u := by
    intro hflf
    obtain ⟨W₀, hW₀⟩ := (frame_has_viable_head M F) S A x R E (M.slotStart S.C (σ - 1) + 2 * Δ S) u
    have hW₀T : W₀ ∈ (x.st (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) u).tree :=
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _
        (lem11_node_invariant M F S A x R E _ u hua).1 _).1 hW₀).1
    have hW₀v : W₀ ∈ (M.fg_to_ac (x.tickInput u (M.voteTime S.C σ))).viable_heads :=
      (viable_head_kept_steps M F Fx) S A x R E hRoots tEnd u W₀ hThird haU hkUE hkUb huk hW₀
        (by
          intro j h1 h2
          rcases eq_or_lt_of_le h1 with heq | hlt
          · intro hc
            apply (state_ne_of_change_step M F) hc
            rw [← heq]
            exact (stepBefore_succ_state_eq M F) x R E ha1 u
          · exact hNoU j (le_trans has' (htime hlt)) h2)
    refine hG (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) W₀ _ haU hW₀T hcka hW₀v ?_ ?_
    · intro W hW
      obtain ⟨hWT, -, -, hWfl⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInvU _).1 hW
      rw [hF]
      exact (lem68_honest_past_finalized M F Fx) S A x R E hRoots (i)
        (x.tickStep u (M.voteTime S.C σ)) v u D W hThirdm hvsb huk hD hWT (lt_of_lt_of_le hflf hWfl) hmaxb
    · intro B hBF hne hBv
      obtain ⟨hBT, -, -, hBfl⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInvU _).1 hBv
      have hBh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B
        (x.st i v).finalized).2.2.2.1 hBF
      rw [hFh] at hBh
      exact absurd (lt_of_lt_of_le hflf (le_trans hBfl hBh)) (lt_irrefl _)
  -- the delivery from `v` at `a₀` to `u` by the view freeze, of a block higher than `f`
  have hjufz : (x.stateBefore (M.viewFreeze S.C (σ - 1)) u).justifiedHeight ≤
      (x.tickInput u (M.voteTime S.C σ)).justifiedHeight :=
    (h_j_mono_st M F Fx) S A x R E hRoots tEnd u hvfU hThird hkUE huk hkUb
  -- `X`: the case where `u`'s cache `h_j` is less than `f`
  have X : (x.tickInput u (M.voteTime S.C σ)).justifiedHeight < (M.chainStateOf S.C D).h_F →
      (x.st i v).finalized.AncestorEq H_u := by
    intro hju
    have hdeliver : ∀ Y : Block V, Y ∈ (x.stateBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) v).tree →
        (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C Y).h →
        Y ∈ (x.tickInput u (M.voteTime S.C σ)).tree := by
      intro Y hY hYh
      have hselY : (x.stateBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) v).finalized.compatible Y = true := by
        have hva₀ : v ∉ A.corrupted (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) :=
          E.not_mem_corrupted_of_le hai hv
        have hta₀ : x.time (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) ≤ x.time i := htime hai
        have h0 := (lem68_honest_past_finalized M F Fx) S A x R E hRoots i
          (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) v v D Y
          (hThirdb.mono (max_le htbb (le_trans hta₀ htbb))) hv hva₀ hD hY hYh
          (max_le htbb (le_trans hta₀ htbb))
        rw [← hF] at h0
        exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E v hai) h0))
      have htN : ((M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S : ℕ) : ℝ) ≤ tB := by
        have : ((M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S : ℕ) : ℝ) + 2 * Δ S ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by
          exact_mod_cast (show M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S + 2 * Δ S ≤ M.voteTime S.C σ by omega)
        linarith [hkUt.2.1]
      have htNE : M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S ≤ tE := by omega
      -- `Y` reaches `u` by its tick to `vt` (`mem_T_of_delivery_high_st`, the receiver read at its tick; F-P1-24-2):
      -- `v` holds it at its last step before `a₀` and is active from `a` through the sync delay after it (outside the
      -- adversary set to the view freeze, `hva`), and `u` ticked to the start of slot `σ`, at least the start of `Y`'s slot
      have hva₀ : v ∉ A.corrupted (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) := E.not_mem_corrupted_of_le hai hv
      have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
          GoldilocksCorrectness.Proofs.Routines.slot_natCast]
      obtain ⟨-, -, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
      have hslotv : S.C.slot ((M.voteTime S.C σ : ℕ) : Int) = σ :=
        hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
          (by omega) (by omega)
      have hckv : x.clockValue (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) v ≤ M.voteTime S.C σ := by
        have h1 := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) v
        have hvt0 : (0 : ℝ) ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by positivity
        have haR : ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by
          exact_mod_cast (show M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S ≤ M.voteTime S.C σ by omega)
        have h2 : ((x.clockValue (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) v : ℕ) : ℝ) ≤
            ((M.voteTime S.C σ : ℕ) : ℝ) :=
          le_trans h1 (max_le hvt0 (by linarith [has]))
        exact_mod_cast h2
      have hYs : Y.slot ≤ σ := by
        have h := (slot_le_clockValue_of_mem_tree M F) R E hva₀ hY
        rw [← hslotv]
        exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hckv))
      have hv₀ : v ∈ A.activeThroughout x a (a + Δs) := by
        have hvA : v ∉ A.corruptedAtTime x ((a + Δs : ℕ) : ℝ) :=
          (not_mem_corruptedAtTime_of_le M) x R E (show a + Δs ≤ M.viewFreeze S.C (σ - 1) by omega) hva
        have h := (activeThroughout_nat_of_awake_from M F) R E hAw hvA (le_refl a) (by omega)
        simpa using h
      have hselA : (x.st (x.stepBefore a) v).finalized.compatible Y = true :=
        GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
          ((F_ancestorEq_of_le M F) x R E v ((stepBefore_mono M) x R E
            (show a ≤ M.slotStart S.C (σ - 1) + 2 * Δ S by omega))) hselY
      have hwinU : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ x.tickStep u (M.voteTime S.C σ) → u ∈ A.active i := by
        intro i h1 h2
        have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_le h2 huk
        exact Activity.mem_active.2 ⟨hAw i u (le_trans (htime h2) hkUE) (le_trans h1 (htime (Nat.le_succ i))) hui, hui⟩
      have hss1 : 1 ≤ M.slotStart S.C σ := by omega
      have hsR : ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) + 2 * Δ S = ((M.slotStart S.C σ : ℕ) : ℝ) := by
        exact_mod_cast (show M.slotStart S.C (σ - 1) + 2 * Δ S + 2 * Δ S = M.slotStart S.C σ by omega)
      have hvR : ((M.slotStart S.C σ : ℕ) : ℝ) + Δ S = ((M.voteTime S.C σ : ℕ) : ℝ) := by exact_mod_cast hvt.symm
      obtain ⟨hk₂u, -, -⟩ := (tickStep_spec M) x R E (t := M.slotStart S.C σ) (v := u) hss1
        (Activity.mem_activeThroughout_of_le (by push_cast at hsR; linarith) (by push_cast at hsR; linarith) hu)
      exact (mem_T_of_delivery_high_st M F U Fx) S A x R GST (M.voteTime S.C σ) tEnd (M.slotStart S.C (σ - 1) + 2 * Δ S)
        (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) a (M.voteTime S.C σ) (M.slotStart S.C σ)
        (x.tickStep u (M.voteTime S.C σ)) (x.tickStep u (M.slotStart S.C σ)) v u Y
        (E.mono htE) hNet hSkew hRedeliver (Sy.mono htE)
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hkUb hRoots) hParent hThird hkUE
        hGSTa (by omega) (by omega) le_rfl hv₀ ((time_stepBefore_le M) x R E _) hva₀ hY hselA hkU hwinU hk₂u (by omega)
        ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hYs)
        (lt_trans hju hYh)
    by_cases hX1 : (M.chainStateOf S.C D).h_F ≤
        (x.stateBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) v).justifiedHeight
    · -- `v`'s cache was at least `f` at `a₀`: its witness reaches `u`
      exfalso
      obtain ⟨⟨Wv, hWv, -, hjWv⟩, -, -⟩ :=
        (cachesWitnessed_of_stateBefore M F) S A x R E (M.slotStart S.C (σ - 1) + 2 * Δ S) v
      have hWvh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Wv Wv).1.2.1
      rw [hjWv] at hX1
      have hWvu := hdeliver Wv hWv (lt_of_le_of_lt hX1 hWvh)
      have hFW := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd _ _ u u Wv hThird
        hkUE hkUE huk huk hWvu (lt_trans (lt_of_lt_of_le hju hX1) hWvh) (max_le hkUb hkUb)
      have hjW := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E _ u Wv hWvu hFW
      exact absurd (lt_of_lt_of_le hju (le_trans hX1 hjW)) (lt_irrefl _)
    push Not at hX1
    -- the step at which `v`'s cache reaches `f`
    obtain ⟨m, hm0b, hmi, hj0', hn₀'⟩ := (exists_crossing_st M F) x v
      (fun n => (M.chainStateOf S.C D).h_F ≤ n.justifiedHeight) hai (Nat.not_le.2 hX1) (le_trans hFjD hjD)
    have hj0 : (x.st m v).justifiedHeight < (M.chainStateOf S.C D).h_F := Nat.lt_of_not_le hj0'
    have hn₀ : (M.chainStateOf S.C D).h_F ≤ (x.st (m + 1) v).justifiedHeight := hn₀'
    have hnem : x.st (m + 1) v ≠ x.st m v := fun h => by rw [h] at hn₀; exact absurd hn₀ (Nat.not_le.2 hj0)
    have hm1t := (le_time_of_state_ne M F) x R E hm0b hnem
    have hnc := hNoV m hm1t hmi
    have hvm1 : v ∉ A.corrupted (m + 1) := E.not_mem_corrupted_of_le (show m + 1 ≤ i by omega) hv
    have hvm0 : v ∉ A.corrupted m := E.not_mem_corrupted_of_le (show m ≤ i by omega) hv
    have hm2t : x.time (m + 1) ≤ (tB : ℝ) := le_trans (htime (show m + 1 ≤ i by omega)) htbb
    have hm2t' : x.time m ≤ (tB : ℝ) := le_trans (htime (show m ≤ i by omega)) htbb
    have hm1 := (h_j_lt_h_max_st M F) S A x R E (m + 1) v
    have hm0 := (h_j_lt_h_max_st M F) S A x R E m v
    have hmm := (h_max_mono_st M F) S A x R E v (show m ≤ m + 1 by omega)
    have hInv0 := (lem11_node_invariant M F S A x R E m v hvm0).1
    have hInv1 := (lem11_node_invariant M F S A x R E (m + 1) v hvm1).1
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st (m + 1) v) (hInv1) with
      ⟨hc1, hme1, hfl1⟩ | ⟨hc1, hfl1⟩
    · -- contested after: `head_height_floor` rises
      exfalso
      apply hnc
      right
      rw [hfl1]
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st m v) (hInv0) with
        ⟨-, hme0, hfl0⟩ | ⟨-, hfl0⟩
      · rw [hfl0, hme0, hme1]
        exact Nat.succ_lt_succ (lt_of_lt_of_le hj0 hn₀)
      · rw [hfl0]
        exact lt_of_lt_of_le (Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le _) hm0) Nat.one_pos) hmm
    by_cases hme1 : hMax M S.C (x.st (m + 1) v) =
        (x.st (m + 1) v).justifiedHeight + 1
    · -- the root moves to the new justified block
      exfalso
      apply hnc
      left
      have hr1 : M.get_fc_root (x.st (m + 1) v) =
          (x.st (m + 1) v).justified := by
        rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st (m + 1) v) (hInv1) with
          ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · rcases h with h | h
          · rw [hc1] at h
            cases h
          · exact absurd hme1 h
      refine ⟨hr1, hme1, ?_⟩
      intro hJr
      rw [hr1] at hJr
      have hr0J : (M.get_fc_root (x.st m v)).AncestorEq
          (x.st m v).justified := by
        rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st m v) (hInv0) with
          ⟨h, -⟩ | ⟨h, -⟩
        · rw [h]
          exact ancestorEq_refl _
        · rw [h]
          exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E _ v
      have hJJ := ancestorEq_trans hJr hr0J
      obtain ⟨⟨W₁, hW₁, hJW₁, hjW₁⟩, -, -⟩ :=
        (cachesWitnessed_of_exec M F) S A x R E (m + 1) v
      obtain ⟨⟨W₀, -, hJW₀, hjW₀⟩, -, -⟩ :=
        (cachesWitnessed_of_exec M F) S A x R E m v
      have h1j : 1 ≤ (M.chainStateOf S.C W₁).h_j := by
        rw [← hjW₁]
        exact le_trans hf1 hn₀
      have hJ1h : (M.chainStateOf S.C
          (x.st (m + 1) v).justified).h =
          (x.st (m + 1) v).justifiedHeight := by
        rw [hJW₁, hjW₁]
        exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C W₁).2.2 h1j
      by_cases h00 : (x.st m v).justifiedHeight = 0
      · -- the earlier justified block is the genesis block
        have hJ0 : (x.st m v).justified = Block.genesis := by
          rw [hJW₀]
          exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C W₀).2.1 (by rw [← hjW₀]; exact h00)
        rw [hJ0] at hJJ
        have hJ1g := (GoldilocksCorrectness.Proofs.Routines.ancestorEq_genesis_iff _).1 hJJ
        have hgF := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Block.genesis
          (x.st i v).finalized).2.2.2.1 (genesis_ancestorEq _)
        rw [hFh] at hgF
        rw [hJ1g] at hJ1h
        have heq : (x.st (m + 1) v).justifiedHeight =
            (M.chainStateOf S.C D).h_F := le_antisymm (hJ1h ▸ hgF) hn₀
        obtain ⟨hcert1, -, -⟩ :=
          ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C W₁).1 h1j
        rw [← hJW₁, ← hjW₁, heq, hJ1g] at hcert1
        have hge := (eq_of_cert_same_height_st M F Fx) S A x R E hRoots tEnd
          (m + 1) (i) v v W₁ D
          Block.genesis _ _ hThird (le_trans hm2t hbE) (le_trans htbb hbE) hvm1
          hvsb hW₁ hD hcert1 hcertF
          ((GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ v) hFT
          (max_le hm2t htbb)
        exact hgen hge.symm
      · have hJ0h : (M.chainStateOf S.C
            (x.st m v).justified).h =
            (x.st m v).justifiedHeight := by
          rw [hJW₀, hjW₀]
          exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C W₀).2.2
            (by rw [← hjW₀]; exact Nat.one_le_iff_ne_zero.mpr h00)
        have hmono := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C _ _).2.2.2.1 hJJ
        rw [hJ1h, hJ0h] at hmono
        exact absurd (lt_of_le_of_lt hmono (lt_of_lt_of_le hj0 hn₀)) (lt_irrefl _)
    -- `v`'s greatest chain-state height after is at least `f + 2`
    have hm2 : (M.chainStateOf S.C D).h_F + 2 ≤
        hMax M S.C (x.st (m + 1) v) := by
      unfold Height at *
      omega
    by_cases hci : (M.chainStateOf S.C D).h_F + 2 ≤
        hMax M S.C (x.stateBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) v)
    · -- already at `a₀`: a block of that height reaches `u`
      obtain ⟨-, ⟨Xb, hXb, hXbh⟩, -⟩ :=
        (cachesWitnessed_of_stateBefore M F) S A x R E (M.slotStart S.C (σ - 1) + 2 * Δ S) v
      have hXu := hdeliver Xb hXb (by rw [hXbh]; unfold Height at *; omega)
      have hhm : (M.chainStateOf S.C Xb).h ≤ hMax M S.C (x.tickInput u (M.voteTime S.C σ)) := le_hMax M hXu
      have hfu := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X
        (x.tickInput u (M.voteTime S.C σ)) hInvU
      apply G
      rw [hXbh] at hhm
      unfold Height at *
      omega
    · -- `v`'s greatest chain-state height reached `f + 2` while its cache was less than `f`
      exfalso
      push Not at hci
      obtain ⟨k, hk0, hkm, hk2', hk3⟩ := (exists_crossing_st M F) x v
        (fun n => (M.chainStateOf S.C D).h_F + 2 ≤ hMax M S.C n)
        (show x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) ≤ m + 1 by omega) (Nat.not_le.2 hci) hm2
      have hk0' : hMax M S.C (x.st k v) < (M.chainStateOf S.C D).h_F + 2 := Nat.lt_of_not_le hk2'
      have hn₁ : (M.chainStateOf S.C D).h_F + 2 ≤ hMax M S.C (x.st (k + 1) v) := hk3
      have hjk : (x.st k v).justifiedHeight < (M.chainStateOf S.C D).h_F :=
        lt_of_le_of_lt ((h_j_mono_st M F Fx) S A x R E hRoots tEnd v (show k ≤ m by omega) hThird
          (le_trans hm2t' hbE) hvm0 hm2t') hj0
      have hne : x.st (k + 1) v ≠ x.st k v := fun h => by rw [h] at hn₁; exact absurd hn₁ (Nat.not_le.2 hk0')
      have hkt := (le_time_of_state_ne M F) x R E hk0 hne
      have hktb : k < i := by omega
      have hvk : v ∉ A.corrupted k := E.not_mem_corrupted_of_le (show k ≤ i by omega) hv
      have hvk1 : v ∉ A.corrupted (k + 1) := E.not_mem_corrupted_of_le (show k + 1 ≤ m + 1 by omega) hvm1
      apply hNoV k hkt hktb
      right
      have hfk1 := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X (x.st (k + 1) v) (lem11_node_invariant M F S A x R E (k + 1) v hvk1).1
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st k v) (lem11_node_invariant M F S A x R E k v hvk).1 with
        ⟨-, hmek, hflk⟩ | ⟨-, hflk⟩
      · rw [hflk]
        unfold Height at *
        omega
      · rw [hflk]
        unfold Height at *
        omega
  -- the cases on `u`'s root
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.tickInput u (M.voteTime S.C σ)) hInvU with ⟨hrJ, -, -⟩ | ⟨-, hcF⟩
  · obtain ⟨⟨Wu, hWu, hJWu0, hjWu0⟩, -, -⟩ :=
      (cachesWitnessed_of_exec M F) S A x R E (x.tickStep u (M.voteTime S.C σ)) u
    have hJWu : (x.tickInput u (M.voteTime S.C σ)).justified = _ := hJWu0
    have hjWu : (x.tickInput u (M.voteTime S.C σ)).justifiedHeight = _ := hjWu0
    have hJT : (x.tickInput u (M.voteTime S.C σ)).justified ∈ (x.tickInput u (M.voteTime S.C σ)).tree :=
      ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E (x.tickStep u (M.voteTime S.C σ)) u).2.2.1
    have hρJ : (x.tickInput u (M.voteTime S.C σ)).justified.AncestorEq H_u := hrJ ▸ hρH
    rcases lt_trichotomy (M.chainStateOf S.C D).h_F (x.tickInput u (M.voteTime S.C σ)).justifiedHeight with
      hlt | heq | hgt
    · -- `u`'s justified block is higher than `f`: Lemma 68
      have h1j : 1 ≤ (M.chainStateOf S.C Wu).h_j := by
        rw [← hjWu]
        exact le_trans hf1 hlt.le
      have hJh : (M.chainStateOf S.C (x.tickInput u (M.voteTime S.C σ)).justified).h =
          (x.tickInput u (M.voteTime S.C σ)).justifiedHeight := by
        rw [hJWu, hjWu]
        exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Wu).2.2 h1j
      have hFJ := (lem68_honest_past_finalized M F Fx) S A x R E hRoots (i)
        (x.tickStep u (M.voteTime S.C σ)) v u D _ hThirdm hvsb huk hD hJT (by rw [hJh]; exact hlt) hmaxb
      rw [hF]
      exact ancestorEq_trans hFJ hρJ
    · -- at the same height: Lemma 76
      have h1j : 1 ≤ (M.chainStateOf S.C Wu).h_j := by
        rw [← hjWu, ← heq]
        exact hf1
      obtain ⟨hcertJ, -, -⟩ :=
        ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Wu).1 h1j
      rw [← hJWu, ← hjWu, ← heq] at hcertJ
      have heqJ := (eq_of_cert_same_height_st M F Fx) S A x R E hRoots tEnd (i)
        (x.tickStep u (M.voteTime S.C σ)) v u D Wu _ _ _
        hThird (le_trans htbb hbE) hkUE hvsb huk hD hWu hcertF hcertJ hFT hJT hmaxb
      rw [heqJ]
      exact hρJ
    · exact X hgt
  · have hfl : (x.tickInput u (M.voteTime S.C σ)).justifiedHeight + 1 ≤
        M.head_height_floor (x.tickInput u (M.voteTime S.C σ)) := by
      have hm : (x.tickInput u (M.voteTime S.C σ)).justifiedHeight <
          hMax M S.C (x.tickInput u (M.voteTime S.C σ)) :=
        (h_j_lt_h_max_st M F) S A x R E (x.tickStep u (M.voteTime S.C σ)) u
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.tickInput u (M.voteTime S.C σ)) hInvU with ⟨-, hme, hfl⟩ | ⟨hc, hfl⟩
      · rw [hfl, hme]
      · rcases hcF with h | h
        · rw [hc] at h
          cases h
        · rw [hfl]
          unfold Height at *
          omega
    by_cases hle : (M.chainStateOf S.C D).h_F ≤ (x.tickInput u (M.voteTime S.C σ)).justifiedHeight
    · exact G (lt_of_le_of_lt hle (Nat.lt_of_succ_le hfl))
    · exact X (Nat.lt_of_not_le hle)


/-- **With no fork-choice change, an honest vote of slot `σ` extends the finalized block of a
validator honest at a time `b` at least one delay after the vote time of slot `σ`.** Under the
execution assumptions and unforgeability, from `GST` on, with fewer than a third of the validators in
the adversary set up to `tEnd`; write `a₀` for the time `2Δ` into slot `σ − 1`, one delay before the
view freeze of slot `σ − 1`: when `v` is honest at `b ≤ tEnd`, `b` at least one delay after the vote
time of slot `σ`, `u` is awake and honest from `a₀` to the vote time of slot `σ`, `v` has no
`ForkChoiceChangeStep` at a step whose real time is from `a₀` to before `b`, `u` has none at a step
whose real time is at least `a₀`, before its tick to the vote time of slot
`σ`, and that tick put `vote` on the wire — then `vote` is `u`'s slot-`σ` vote for a block `H_u` it
holds at that tick, and `v`'s finalized block before `b` is `H_u` or an ancestor of `H_u`.

Why (`F'` is `v`'s finalized block, `f` the finalization height of the chain state that finalized
it, `h_j` is `u`'s cache at its tick): when `u`'s root is its justified block `J_u`, at a
height `h_j`: if `h_j > f`, Lemma 68 puts `F'` on `J_u`'s chain; if `h_j = f`, Lemma 76 makes
`J_u = F'`; and the vote extends the root. When `u`'s root is its finalized block,
`head_height_floor` is greater than `h_j`, and if `h_j ≥ f` every viable head is higher than `f`,
so on `F'`'s chain (Lemma 68), while no strict ancestor of `F'` is viable: the vote extends `F'`
(`honest_vote_spec`, with a viable head held at the last step before `a₀`, where `u`'s clock value
is less than the view freeze since `ΔClockAhead < Δ`, and kept to the tick, `viable_head_kept_steps`). It remains `h_j < f ≤ v`'s cache `h_j` at `b`. If `v`'s cache was at least `f`
at `a₀`, the block witnessing it reaches `u` by the view freeze, against `h_j < f`. Otherwise `v`'s
cache passes `f` at some time `t` from `a₀` to `b`: then `v`'s root moves to its new justified
block, or its `head_height_floor` rises, unless `v`'s greatest chain-state height is then at least
`f + 2`; if that was already so at `a₀`, a block of that height reaches `u` and `u`'s
`head_height_floor` is greater than `f` (the case before); otherwise `v`'s greatest chain-state
height reached `f + 2` while its cache was less than `f`, and its `head_height_floor` rose then.
Each change is against the hypothesis. `u` is read at its tick to the vote time, at a real time at
most `ΔClockBehind` after it, so before `b`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `b`: the times; `σ`: the
  slot of the vote; `u`: the voter; `v`: the validator whose finalized block is read; `vote`: the
  vote.

Roots name blocks until `b`: the proof reads `v`'s blocks before `b`, `u`'s at its tick to the vote
time of slot `σ`, before `b`, and blocks held by `v` at times from `a₀` to `b`.

Restated with the delivery premises up to `b`: the bound of its roots `hRoots`; every delivery its proof reads is due by then.


Read aloud: with no fork-choice change, an honest vote of slot `σ` is for a block that has as
ancestor, or is, the finalized block of a validator honest at a time `b` at least one delay after the
vote time of slot `σ`. -/
theorem vote_extends_finalized_at_of_no_change_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd σ b : ℕ) (u v : V) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x b)
    (hParent : ParentHeldAtDelivery M x)
    -- from `a` on, the network is synchronous and every validator outside the adversary set is awake
    -- through `tEnd`; `a` is early enough for the windows the proof reads
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ M.viewFreeze S.C (σ - 1))
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hσ : 1 ≤ σ) (hGST : GST ≤ M.slotStart S.C (σ - 1) + 2 * Δ S)
    (hEnd : b ≤ tEnd) (hab : M.voteTime S.C σ + Δ S ≤ b)
    (hv : v ∉ A.corruptedAtTime x b)
    (hu : u ∈ A.activeThroughout x (M.slotStart S.C (σ - 1) + 2 * Δ S) (M.voteTime S.C σ))
    (hNoV : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → x.time j < (b : ℝ) →
      ¬ ForkChoiceChangeStep M S A x v j)
    (hNoU : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → j < x.tickStep u (M.voteTime S.C σ) →
      ¬ ForkChoiceChangeStep M S A x u j)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree,
      vote = GoldfishVote.mk u σ H_u.root ∧
      (x.stateBefore (b) v).finalized.AncestorEq H_u := by
  have htbb : x.time (x.stepBefore b) ≤ (b : ℝ) := (time_stepBefore_le M) x R E b
  exact (vote_extends_finalized_st_of_no_change_upTo M F U Fx) S A x R GST tEnd σ b (x.stepBefore b) u v vote E hNet
    hSkew hRedeliver Sy hΔs hRoots hParent
    (by omega) a hGSTa ha hAw hThird hσ hGST (by exact_mod_cast hEnd)
    (by
      obtain ⟨i, hi, -⟩ := hSend
      have hk := (E.tick_active _ u _ (x.lbl_tickStep ⟨i, hi⟩)).2.2
      have : ((M.voteTime S.C σ : ℕ) : ℝ) + Δ S ≤ (b : ℝ) := by exact_mod_cast hab
      linarith [E.ahead_nonneg]) htbb
    ((stepBefore_mono M) x R E (show M.slotStart S.C (σ - 1) + 2 * Δ S ≤ b by
      have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
      have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show σ - 1 ≤ σ by omega)
      omega))
    ((not_mem_corrupted_of_le_time M) x R E hv htbb)
    ((not_mem_corruptedAtTime_of_le M) x R E (show M.viewFreeze S.C (σ - 1) ≤ b by
      have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
      obtain ⟨-, -, hfz1, h4, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ - 1)
      rw [Nat.sub_add_cancel hσ] at h4
      omega) hv)
    hu (fun j h1 h2 => hNoV j h1 (by
      have h := ((lt_stepBefore_iff M) x R E).1 h2
      exact lt_of_le_of_lt ((time_le_succ M) x R j) h)) hNoU hSend

/-- **With no fork-choice change, an honest vote of slot `σ` extends the finalized block of a
validator honest at the update of slot `σ`.** Under the execution assumptions and
unforgeability, from `GST` on, with fewer than a third of the validators in the adversary set up to
`tEnd`; write `a₀` for the time `2Δ` into slot `σ − 1`, one delay before the view freeze of slot
`σ − 1`: when `v` is honest at the support cutoff `b` of slot `σ + 1 ≤ tEnd`, `u` is awake and
honest from `a₀` to the vote time of slot `σ`, `v` has no `ForkChoiceChangeStep` at a step whose real time is from `a₀` to before
`b`, `u` has none at a step whose real time is at least `a₀`, before its
tick to the vote time of slot `σ`, and that tick put `vote` on the wire — then `vote` is `u`'s slot-`σ` vote for a block
`H_u` it holds, and `v`'s finalized block before `b` is `H_u` or an ancestor of `H_u`.

The instance `b := M.supportCutoff S.C (σ + 1)` of
`vote_extends_finalized_at_of_no_change`.

Why (`F'` is `v`'s finalized block, `f` the finalization height of the chain state that finalized
it, `h_j` is `u`'s cache at the vote time): when `u`'s root is its justified block `J_u`, at a
height `h_j`: if `h_j > f`, Lemma 89a puts `F'` on `J_u`'s chain; if `h_j = f`, Lemma 76 makes
`J_u = F'`; and the vote extends the root. When `u`'s root is its finalized block,
`head_height_floor` is greater than `h_j`, and if `h_j ≥ f` every viable head is higher than `f`,
so on `F'`'s chain (Lemma 89a), while no strict ancestor of `F'` is viable: the vote extends `F'`
(`honest_vote_spec`, with a viable head held before the view freeze and kept to the vote time,
`viable_head_kept`). It remains `h_j < f ≤ v`'s cache `h_j` at `b`. If `v`'s cache was at least `f`
at `a₀`, the block witnessing it reaches `u` by the view freeze, against `h_j < f`. Otherwise `v`'s
cache passes `f` at some time `t` from `a₀` to `b`: then `v`'s root moves to its new justified
block, or its `head_height_floor` rises, unless `v`'s greatest chain-state height is then at least
`f + 2`; if that was already so at `a₀`, a block of that height reaches `u` and `u`'s
`head_height_floor` is greater than `f` (the case before); otherwise `v`'s greatest chain-state
height reached `f + 2` while its cache was less than `f`, and its `head_height_floor` rose then.
Each change is against the hypothesis.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`: the times; `σ`: the
  slot of the vote; `u`: the voter; `v`: the validator whose finalized block is read; `vote`: the
  vote.

Roots name blocks until `M.supportCutoff S.C (σ + 1)`: `vote_extends_finalized_at_of_no_change` at
`b := M.supportCutoff S.C (σ + 1)`.

Restated with the delivery premises up to `M.supportCutoff S.C (σ + 1)`: the bound of its roots `hRoots`; every delivery its proof reads is due by then.


Read aloud: with no fork-choice change, an honest vote of slot `σ` is for a block that has as
ancestor, or is, the finalized block of a validator honest at the update of slot `σ`. -/
theorem vote_extends_finalized_of_no_change_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd σ : ℕ) (u v : V) (vote : GoldfishVote V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (σ + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (σ + 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (σ + 1)))
    (hParent : ParentHeldAtDelivery M x)
    -- from `a` on, the network is synchronous and every validator outside the adversary set is awake
    -- through `tEnd`; `a` is early enough for the windows the proof reads
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ M.viewFreeze S.C (σ - 1))
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hσ : 1 ≤ σ) (hGST : GST ≤ M.slotStart S.C (σ - 1) + 2 * Δ S)
    (hEnd : M.supportCutoff S.C (σ + 1) ≤ tEnd)
    (hv : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)))
    (hu : u ∈ A.activeThroughout x (M.slotStart S.C (σ - 1) + 2 * Δ S) (M.voteTime S.C σ))
    (hNoV : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → x.time j < ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) →
      ¬ ForkChoiceChangeStep M S A x v j)
    (hNoU : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → j < x.tickStep u (M.voteTime S.C σ) →
      ¬ ForkChoiceChangeStep M S A x u j)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree,
      vote = GoldfishVote.mk u σ H_u.root ∧
      (x.stateBefore (M.supportCutoff S.C (σ + 1)) v).finalized.AncestorEq H_u :=
  (vote_extends_finalized_at_of_no_change_upTo M F U Fx) S A x R GST tEnd σ (M.supportCutoff S.C (σ + 1)) u v vote
    E hNet hSkew hRedeliver Sy hΔs hRoots hParent a hGSTa ha hAw hThird hσ hGST hEnd
    (le_trans (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U)] <;> omega)
      ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ σ)))
    hv hu hNoV hNoU hSend

/-- **A validator's finalized block one delay before a viable block of another, read at the other's tick, is
compatible with it.** `w` is outside the adversary set up to the time `t₀ ≥ 1`, active from `a` through the sync
delay after it; `u` ticks to `c`, at least `t₀ + Δ S`, at the step `kR`, at a real time at most `tEnd`, is active at
every step from the real time `a` up to that tick, and ticked earlier to `c₂`, at least the start of the slot of
every block `w` holds before `t₀` and one delay before `c`; `W` is a viable head of `u`'s frame at `kR`. Then `w`'s
finalized block before `t₀` is compatible with `W`.

Why (`f` the finalization height of the chain state of a block `D` that finalized `w`'s block):
when `W` is higher than `f`, Lemma 68 at `w`'s last step before `t₀` and `u`'s tick. Otherwise `head_height_floor`
at `u`'s tick is at most `f`, so its cache `h_j` is less than `D`'s height, `D` reaches `u` by its tick
(`mem_T_of_delivery_high_st`) and gives it the cache `h_j = f`: `u` then has `hMax M S.C n = f + 1`, is not contested
(its `head_height_floor` would be `f + 1`, greater than `W`'s height), so its root is its justified block, which is
`w`'s finalized block (`F_eq_J_of_height_st`), an ancestor of the viable `W`.

Restated: `u` read at its tick `kR` (the rows of `mem_T_of_delivery_high_st`) in
place of before the real time `t₀ + Δ S`; moved here from `Lemma89StabilityB6.lean`, beside the step-form kit it
reads.

With the delivery premises up to `tE`, at least the clock value of the receiver's tick (`htE`), and the roots up
to the real time `tR`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`, `tEnd`, `t₀`: the times;
  `w`, `u`: the two validators; `W`: the block; `a`: the start of the windows; `c`, `kR`: the clock value and the
  step of `u`'s tick; `c₂`, `k₂`: those of its earlier tick.

Roots name blocks until `tR`, at least the real time of `kR`: every block the proof compares is held by `w` before
`t₀` or by `u` at its tick.

Read aloud: an honest validator's finalized block one delay before a viable head of another honest validator, read
at its tick, is compatible with that head. -/
theorem finalized_compatible_of_viable_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST : ℕ)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    (tEnd t₀ : ℕ) (w u : V) (W : Block V)
    -- from `a` on, the network is synchronous; `a` is early enough for the windows the proof reads
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t₀ + Δ S)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hw : w ∉ A.corruptedAtTime x t₀)
    -- `w` is active from `a` through the sync delay after it
    (hv₀ : w ∈ A.activeThroughout x a (a + Δs))
    -- `u`'s tick to `c`, at least one delay after `t₀`, at a real time at most `tEnd`, and its window from `a`
    (c c₂ kR k₂ : ℕ) (hkR : x.lbl kR = Event.tick u c) (hcu : t₀ + Δ S ≤ c) (hEnd : x.time kR ≤ tEnd)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → u ∈ A.active i)
    -- an earlier tick of `u` to `c₂`, one delay before `c`, at least the start of every slot of `w`'s blocks
    (hk₂ : x.lbl k₂ = Event.tick u c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.stateBefore t₀ w).tree, M.slotStart S.C Y.slot ≤ c₂)
    (hW : W ∈ (M.fg_to_ac (x.st kR u)).viable_heads)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time kR ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : c ≤ tE) :
    (x.stateBefore t₀ w).finalized.compatible W = true := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hkRt := E.tick_active kR u c hkR
  have huR : u ∉ A.corrupted kR := (Finset.mem_sdiff.1 hkRt.1).2
  have hcuR : ((t₀ + Δ S : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcu
  push_cast at hcuR
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hi₀t := (time_stepBefore_le M) x R E t₀
  have hi₀k : x.time (x.stepBefore t₀) ≤ x.time kR := by linarith [hkRt.2.1]
  have hi₀E : x.time (x.stepBefore t₀) ≤ tEnd := le_trans hi₀k hEnd
  have hmaxR : max (x.time (x.stepBefore t₀)) (x.time kR) ≤ tR := max_le (le_trans hi₀k htR) htR
  have hmaxE : max (x.time (x.stepBefore t₀)) (x.time kR) ≤ tEnd := max_le hi₀E hEnd
  obtain ⟨hWT, -, hrW, hflW⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _
    (show M.nodeInvCore S.C S.P S.X (x.st kR u) from (lem11_node_invariantCore_of_run M F S x R kR u).1) W).1 hW
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hrW
  have hwS : w ∉ A.corrupted (x.stepBefore t₀) :=
    (not_mem_corrupted_of_le_time M) x R E hw (by exact_mod_cast hi₀t)
  have hSt : x.stateBefore t₀ w = x.st (x.stepBefore t₀) w := rfl
  rw [hSt]
  obtain ⟨D, hD, hF⟩ := (finalizedFromChain_of_exec M F) S A x R E (x.stepBefore t₀) w
  by_cases hlt : (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C W).h
  · rw [hF, compatible_iff]
    exact Or.inl ((lem68_honest_past_finalized M F Fx) S A x R E hRoots (x.stepBefore t₀) kR w u D W
      (hThird.mono hmaxE) hwS huR hD hWT hlt hmaxR)
  push Not at hlt
  by_cases hf0 : (M.chainStateOf S.C D).h_F = 0
  · rw [hF, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D hf0, compatible_iff]
    exact Or.inl (genesis_ancestorEq W)
  have hf1 : 1 ≤ (M.chainStateOf S.C D).h_F := Nat.one_le_iff_ne_zero.mpr hf0
  have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1
  have hinvR := (lem11_node_invariant M F S A x R E kR u huR).1
  have hmu := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X (x.st kR u) hinvR
  have hju := (h_j_lt_h_max_st M F) S A x R E kR u
  have hDh : (x.st kR u).justifiedHeight < (M.chainStateOf S.C D).h := by
    unfold Height at *
    omega
  -- `D` reaches `u` by its tick
  have hFDa := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 hf1).2.2.1
  have hsel : (x.st (x.stepBefore a) w).finalized.compatible D = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E w ((stepBefore_mono M) x R E (show a ≤ t₀ by omega)))
      (by rw [hF]; exact (compatible_iff _ _).2 (Or.inl hFDa))
  have hDu := (mem_T_of_delivery_high_st M F U Fx) S A x R GST tE tEnd t₀ (x.stepBefore t₀) a c c₂ kR k₂ w u D
    E hNet hSkew hRedeliver Sy
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htR hRoots) hParent hThird hEnd
    hGSTa (by omega) hcu htE hv₀ hi₀t hwS hD hsel hkR hwin hk₂ hc₂ (hslot D hD) hDh
  have hFuD := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd kR kR u u D
    hThird hEnd hEnd huR huR hDu hDh (max_le htR htR)
  have hjD := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E kR u D hDu hFuD
  have hjeq : (x.st kR u).justifiedHeight = (M.chainStateOf S.C D).h_F := by
    unfold Height at *
    omega
  have hmeq : hMax M S.C (x.st kR u) = (x.st kR u).justifiedHeight + 1 := by
    unfold Height at *
    omega
  have hroot : M.get_fc_root (x.st kR u) = (x.st kR u).justified := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st kR u) hinvR with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exfalso
      rcases h with h | h
      · obtain ⟨-, -, hfl⟩ :=
          (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X _ hinvR h
        rw [hfl] at hflW
        unfold Height at *
        omega
      · exact h hmeq
  have hFJ := (F_eq_J_of_height_st M F Fx) S A x R E hRoots tEnd (x.stepBefore t₀) kR w u D hThird
    hi₀E hEnd hwS huR hD hF hf1 hjeq hmaxR
  rw [hFJ, ← hroot, compatible_iff]
  exact Or.inl hrW


/-- **A validator's fork-choice root one delay before a viable block of another, read at the other's tick, when it
holds that block, is compatible with it.** The hypotheses of `finalized_compatible_of_viable_upTo`, with `W` held by `w`
before `t₀`.

Why: the root is the finalized block (`finalized_compatible_of_viable_upTo`) or the justified block
`J` at a height `j`, with `hMax M S.C n = j + 1` and the state not contested, so
`head_height_floor = j`, at most `W`'s height (`floor_le_of_viable_tick_upTo`), and `W`'s height is at most
`j + 1`. At `j + 1`, `W` is a descendant of the finalized block (Lemma 89a) at the height
`hMax M S.C n`, so of `J` (not contested). At `j`, `J`'s witness reaches `u` by its tick, whose cache becomes
`j` and justified block `J` (`J_eq_of_h_j_eq_st`); `u` is not contested (its `head_height_floor` would be `j + 1`), so
its root is `J`, an ancestor of the viable `W`.

Restated: `u` read at its tick `kR`, as `finalized_compatible_of_viable_upTo`; moved
here from `Lemma89StabilityB6.lean`.

With the delivery premises up to `tE`, at least the clock value of the receiver's tick (`htE`), and the roots up
to the real time `tR`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the others: as `finalized_compatible_of_viable_upTo`.

Roots name blocks until `tR`, at least the real time of `kR`.

Read aloud: an honest validator's fork-choice root one delay before a viable head of another honest validator, read
at its tick, when it holds that head, is compatible with it. -/
theorem root_compatible_of_viable_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST : ℕ)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    (tEnd t₀ : ℕ) (w u : V) (W : Block V)
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t₀ + Δ S)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hw : w ∉ A.corruptedAtTime x t₀)
    (hv₀ : w ∈ A.activeThroughout x a (a + Δs))
    (c c₂ kR k₂ : ℕ) (hkR : x.lbl kR = Event.tick u c) (hcu : t₀ + Δ S ≤ c) (hEnd : x.time kR ≤ tEnd)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → u ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick u c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.stateBefore t₀ w).tree, M.slotStart S.C Y.slot ≤ c₂)
    (hW : W ∈ (M.fg_to_ac (x.st kR u)).viable_heads)
    (hWw : W ∈ (x.stateBefore t₀ w).tree)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time kR ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : c ≤ tE) :
    (M.get_fc_root (x.stateBefore t₀ w)).compatible W = true := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hkRt := E.tick_active kR u c hkR
  have huR : u ∉ A.corrupted kR := (Finset.mem_sdiff.1 hkRt.1).2
  have hcuR : ((t₀ + Δ S : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcu
  push_cast at hcuR
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hi₀t := (time_stepBefore_le M) x R E t₀
  have hi₀k : x.time (x.stepBefore t₀) ≤ x.time kR := by linarith [hkRt.2.1]
  have hi₀E : x.time (x.stepBefore t₀) ≤ tEnd := le_trans hi₀k hEnd
  have htR₀ : x.time (x.stepBefore t₀) ≤ tR := le_trans hi₀k htR
  have hmaxR : max (x.time (x.stepBefore t₀)) (x.time kR) ≤ tR := max_le htR₀ htR
  obtain ⟨-, -, hrW, hflW⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _
    (show M.nodeInvCore S.C S.P S.X (x.st kR u) from (lem11_node_invariantCore_of_run M F S x R kR u).1) W).1 hW
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hrW
  have hwS : w ∉ A.corrupted (x.stepBefore t₀) :=
    (not_mem_corrupted_of_le_time M) x R E hw (by exact_mod_cast hi₀t)
  have hflw := (floor_le_of_viable_tick_upTo M F U Fx) S A x R GST t₀ a c c₂ kR k₂ w u W E hNet hSkew hRedeliver Sy
    hRoots hParent (hThird.mono hEnd) hGSTa ha hv₀ hw hkR hcu hwin hk₂ hc₂ hslot hW htR htE
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.stateBefore t₀ w)
      (show M.nodeInv S.C S.P S.X (x.stateBefore t₀ w) from
          (GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
            (x.stepBefore t₀) w hwS).1) with ⟨hrJ, hmJ, hcJ⟩ | ⟨hrF, -⟩
  · have hfl : M.head_height_floor (x.stateBefore t₀ w) = (x.stateBefore t₀ w).justifiedHeight := by
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.stateBefore t₀ w)
        (show M.nodeInv S.C S.P S.X (x.stateBefore t₀ w) from
          (GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
            (x.stepBefore t₀) w hwS).1) with ⟨hc, -, -⟩ | ⟨-, h⟩
      · rw [hcJ] at hc
        cases hc
      · rw [h, hmJ]
        rfl
    have hWh := (height_le_h_max M F) S A x t₀ w W hWw
    rw [hrJ, compatible_iff]
    by_cases hWj : (M.chainStateOf S.C W).h = (x.stateBefore t₀ w).justifiedHeight + 1
    · -- `W` at the height `h_max`: a descendant of `J`
      left
      have hFW : (x.stateBefore t₀ w).finalized.AncestorEq W :=
        (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd (x.stepBefore t₀) (x.stepBefore t₀) w w W hThird
          hi₀E hi₀E hwS hwS hWw
          (show (x.stateBefore t₀ w).justifiedHeight < (M.chainStateOf S.C W).h by unfold Height at *; omega)
          (max_le htR₀ htR₀)
      by_contra hJW
      have hc := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X (x.stateBefore t₀ w)
        (show M.nodeInv S.C S.P S.X (x.stateBefore t₀ w) from
          (GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
            (x.stepBefore t₀) w hwS).1) W hmJ hWw hFW
        (by rw [hWj, hmJ]) hJW
      rw [hcJ] at hc
      cases hc
    · -- `W` at the height `j`: `J`'s witness reaches `u` by its tick
      left
      have hWj' : (M.chainStateOf S.C W).h = (x.stateBefore t₀ w).justifiedHeight := by
        rw [hfl] at hflw
        unfold Height at *
        omega
      obtain ⟨⟨Y, hY, hJY, hjY⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t₀ w
      have hYh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Y Y).1.2.1
      have hinvR := (lem11_node_invariant M F S A x R E kR u huR).1
      have hmu := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X (x.st kR u) hinvR
      have hju := (h_j_lt_h_max_st M F) S A x R E kR u
      have hYlt : (x.st kR u).justifiedHeight < (M.chainStateOf S.C Y).h := by
        unfold Height at *
        omega
      have hselY : (x.stateBefore t₀ w).finalized.compatible Y = true := by
        have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_stateBefore M F) S A x R E t₀ w
        rw [hJY] at hFJ
        exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Y).1))
      have hsel : (x.st (x.stepBefore a) w).finalized.compatible Y = true :=
        GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
          ((F_ancestorEq_of_le M F) x R E w ((stepBefore_mono M) x R E (show a ≤ t₀ by omega))) hselY
      have hYu := (mem_T_of_delivery_high_st M F U Fx) S A x R GST tE tEnd t₀ (x.stepBefore t₀) a c c₂ kR k₂ w u Y
        E hNet hSkew hRedeliver Sy
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htR hRoots) hParent hThird hEnd
        hGSTa (by omega) hcu htE hv₀ hi₀t hwS hY hsel hkR hwin hk₂ hc₂ (hslot Y hY) hYlt
      have hFuY := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd kR kR u u Y
        hThird hEnd hEnd huR huR hYu hYlt (max_le htR htR)
      have hjY' := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E kR u Y hYu hFuY
      have hjeq : (x.stateBefore t₀ w).justifiedHeight = (x.st kR u).justifiedHeight := by
        unfold Height at *
        omega
      have hmeq : hMax M S.C (x.st kR u) = (x.st kR u).justifiedHeight + 1 := by
        unfold Height at *
        omega
      have hJJ : (x.stateBefore t₀ w).justified = (x.st kR u).justified :=
        (J_eq_of_h_j_eq_st M F Fx) S A x R E hRoots tEnd (x.stepBefore t₀) kR w u hThird hi₀E hEnd hwS huR hjeq hmaxR
      have hroot : M.get_fc_root (x.st kR u) = (x.st kR u).justified := by
        rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st kR u) hinvR
          with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exfalso
          rcases h with h | h
          · obtain ⟨-, -, hfl'⟩ :=
              (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X _ hinvR h
            rw [hfl'] at hflW
            unfold Height at *
            omega
          · exact h hmeq
      rw [hJJ, ← hroot]
      exact hrW
  · rw [hrF]
    exact (finalized_compatible_of_viable_upTo M F U Fx) S A x R GST E hNet hSkew hRedeliver Sy hRoots
      hParent tEnd t₀ w u W a hGSTa ha hThird hw hv₀ c c₂ kR k₂ hkR hcu hEnd hwin hk₂ hc₂ hslot hW htR htE


/-- **A validator's frame stays compatible with a viable block of another while its fork choice
does not change.** The hypotheses of `root_compatible_of_viable`, and: `w` is honest at `b ≥ t₀`,
`b ≤ tEnd`, and `w` has no `ForkChoiceChangeStep` at any step whose real time is from `t₀` to before `b`. Then before
`b`: `w`'s `head_height_floor` is at most `W`'s chain-state height, and `w`'s finalized block and
fork-choice root are compatible with `W`.

Why: `head_height_floor` does not rise (`floor_le_of_no_change`, `floor_le_of_viable_tick`). The
finalized block, finalized at a height `f` by the chain state of a block `D`: when `W` is higher
than `f`, Lemma 89a; otherwise `head_height_floor` makes `hMax M S.C n = f + 1` and `W`'s height
`f`, so the finalized block is the justified block (Lemma 76), and that case is the root's. The root
is the finalized block, or the justified block `J` at a height `j` with `hMax M S.C n = j + 1`, the
state not contested, so `W`'s height is `j` or `j + 1`. At `j + 1`, `W` is a descendant of `J` (not
contested). At `j`: the cache `h_j` did not pass `j` after `t₀` (`J_genesis_of_cache_passes`, or `J`
is the genesis block), so at `t₀` it was `j` with the justified block `J` (Lemma 76) and
`hMax M S.C n = j + 1`; `w` was not contested then (its `head_height_floor` would be greater than
`W`'s height), so its root then was `J`, compatible with `W` (`root_compatible_of_viable`).

Restated: `u` read at its tick `kR` to a clock value `c ≥ t₀ + Δ S` (the rows
of `finalized_compatible_of_viable`: `hkR`, `hcu`, `hEnd`, `hwin`, `hk₂`, `hc₂`, `hslot`, `hW`, with `w` active
from `a` through the sync delay after it, `hv₀`), passed through; `hAw`, `hΔs`, `h1` and `hGST` dropped; the delivery premises up to `tE`, at least
the clock value of that tick (`htE`), and the roots up to the real time `tR`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `t₀ ≤ b`: the times;
  `w`, `u`: the two validators; `W`: the block.

Roots name blocks until `tR`, at least `max (t₀ + Δ S) b`: the proof compares blocks `u` holds
before `t₀ + Δ` and blocks `w` holds before `b`.

Restated with the delivery premises up to `tR`: the bound of its roots `hRoots`; every delivery its proof reads is due by then.


Read aloud: while a validator's fork choice does not change, its `head_height_floor` is at most the
chain-state height of another validator's viable block, and its finalized block and fork-choice root
are compatible with that block. -/
theorem frame_compatible_of_viable_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST : ℕ)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    (tEnd t₀ b : ℕ) (w u : V) (W : Block V)
    -- from `a` on, the network is synchronous and every validator outside the adversary set is awake
    -- through `tEnd`; `a` is early enough for the windows the proof reads
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t₀ + Δ S)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hb : b ≤ tEnd) (ht₀b : t₀ ≤ b)
    (hw : w ∉ A.corruptedAtTime x b)
    (hv₀ : w ∈ A.activeThroughout x a (a + Δs))
    -- `u`'s tick to `c`, at least one delay after `t₀`, at a real time at most `tEnd`, its window from `a`, and
    -- an earlier tick to `c₂`, one delay before `c`, at least the start of every slot of `w`'s blocks before `t₀`
    (c c₂ kR k₂ : ℕ) (hkR : x.lbl kR = Event.tick u c) (hcu : t₀ + Δ S ≤ c) (hEnd : x.time kR ≤ tEnd)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → u ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick u c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.stateBefore t₀ w).tree, M.slotStart S.C Y.slot ≤ c₂)
    (hW : W ∈ (M.fg_to_ac (x.st kR u)).viable_heads)
    (hWw : W ∈ (x.stateBefore t₀ w).tree)
    (hNo : ∀ j : ℕ, (t₀ : ℝ) ≤ x.time j → x.time j < (b : ℝ) → ¬ ForkChoiceChangeStep M S A x w j)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time kR ≤ tR) (htRb : (b : ℝ) ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : c ≤ tE) :
    M.head_height_floor (x.stateBefore b w) ≤ (M.chainStateOf S.C W).h ∧
      (x.stateBefore b w).finalized.compatible W = true ∧
      (M.get_fc_root (x.stateBefore b w)).compatible W = true := by
  have hw₀ : w ∉ A.corruptedAtTime x t₀ := (not_mem_corruptedAtTime_of_le M) x R E (by exact_mod_cast ht₀b) hw
  have hRootsb : RootsNameBlocksUntil M A x ((b : ℕ) : ℝ) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htRb hRoots
  have hflw₀ := (floor_le_of_viable_tick_upTo M F U Fx) S A x R GST t₀ a c c₂ kR k₂ w u W E hNet hSkew hRedeliver Sy
    hRoots hParent (hThird.mono hEnd) hGSTa ha hv₀ hw₀ hkR hcu hwin hk₂ hc₂ hslot hW htR htE
  have hflb : M.head_height_floor (x.stateBefore b w) ≤ (M.chainStateOf S.C W).h :=
    le_trans ((floor_le_of_no_change M F) S A x R E w t₀ b ht₀b hNo) hflw₀
  have hWb : W ∈ (x.stateBefore b w).tree := ((stateBefore_grows M F) x R E w ht₀b).1 hWw
  have hmb := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X (x.stateBefore b w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E le_rfl hw)
  have hjb := (h_j_lt_h_max M F) S A x R E b w
  -- the justified block at `b`, at the height of `W`, is compatible with `W`
  have JW : hMax M S.C (x.stateBefore b w) = (x.stateBefore b w).justifiedHeight + 1 →
      (M.chainStateOf S.C W).h = (x.stateBefore b w).justifiedHeight →
      (x.stateBefore b w).justified.compatible W = true := by
    intro hmJ hWj
    have hj0 := (h_j_mono M F Fx) S A x R E hRootsb tEnd t₀ b w hThird ht₀b hb hw (by omega)
    by_cases hlt : (x.stateBefore t₀ w).justifiedHeight < (x.stateBefore b w).justifiedHeight
    · rw [(J_genesis_of_cache_passes M F Fx) S A x R E hRootsb tEnd t₀ b
        (x.stateBefore b w).justifiedHeight w hThird ht₀b hb hw hNo hlt le_rfl (by rw [hmJ]) (by omega),
        compatible_iff]
      exact Or.inl (genesis_ancestorEq W)
    have hjeq : (x.stateBefore t₀ w).justifiedHeight = (x.stateBefore b w).justifiedHeight := by
      unfold Height at *
      omega
    have hJJ := (J_eq_of_h_j_eq M F Fx) S A x R E hRootsb tEnd t₀ b w w hThird (by omega) hb hw₀
      hw hjeq (by omega)
    have hm₀ := (h_max_mono M F) S A x R E w ht₀b
    have hj₀ := (h_j_lt_h_max M F) S A x R E t₀ w
    have hm₀eq : hMax M S.C (x.stateBefore t₀ w) = (x.stateBefore t₀ w).justifiedHeight + 1 := by
      unfold Height at *
      omega
    have hr₀ : M.get_fc_root (x.stateBefore t₀ w) = (x.stateBefore t₀ w).justified := by
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.stateBefore t₀ w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E ht₀b hw) with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exfalso
        rcases h with h | h
        · obtain ⟨-, -, hfl'⟩ :=
            (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X _ ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E ht₀b hw) h
          rw [hfl'] at hflw₀
          unfold Height at *
          omega
        · exact h hm₀eq
    have hc := (root_compatible_of_viable_upTo M F U Fx) S A x R GST E hNet hSkew hRedeliver Sy hRoots
      hParent tEnd t₀ w u W a hGSTa ha hThird hw₀ hv₀ c c₂ kR k₂ hkR hcu hEnd hwin hk₂ hc₂ hslot hW hWw htR htE
    rw [hr₀, hJJ] at hc
    exact hc
  -- the finalized block at `b`
  have hF : (x.stateBefore b w).finalized.compatible W = true := by
    obtain ⟨D, hD, hFD⟩ := (finalizedFromChain_of_exec M F) S A x R E (x.stepBefore b) w
    have hSt : x.stateBefore b w = x.st (x.stepBefore b) w := rfl
    rw [← hSt] at hD hFD
    by_cases hlt : (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C W).h
    · rw [hFD, compatible_iff]
      exact Or.inl ((finalized_ancestorEq_of_held M F Fx) S A x R E hRootsb tEnd b t₀ w w D W
        hThird hb (by omega) hw hw₀ hD hWw hlt (by omega))
    push Not at hlt
    by_cases hf0 : (M.chainStateOf S.C D).h_F = 0
    · rw [hFD, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D hf0,
        compatible_iff]
      exact Or.inl (genesis_ancestorEq W)
    have hf1 : 1 ≤ (M.chainStateOf S.C D).h_F := Nat.one_le_iff_ne_zero.mpr hf0
    obtain ⟨-, -, hFDa, -⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 hf1
    have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1
    have hFwD : (x.stateBefore b w).finalized.AncestorEq D := by rw [hFD]; exact hFDa
    have hjD := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_stateBefore M F) S A x R E _ w D hD hFwD
    have hjeq : (x.stateBefore b w).justifiedHeight = (M.chainStateOf S.C D).h_F := by
      unfold Height at *
      omega
    have hFJ := (F_eq_J_of_height M F Fx) S A x R E hRootsb tEnd b b w w D hThird hb hb hw hw hD
      hFD hf1 hjeq (by omega)
    rw [hFJ]
    exact JW (by unfold Height at *; omega) (by unfold Height at *; omega)
  refine ⟨hflb, hF, ?_⟩
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.stateBefore b w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E le_rfl hw) with ⟨hrJ, hmJ, hcJ⟩ | ⟨hrF, -⟩
  · rw [hrJ]
    have hfl : M.head_height_floor (x.stateBefore b w) = (x.stateBefore b w).justifiedHeight := by
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.stateBefore b w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E le_rfl hw) with ⟨hc, -, -⟩ | ⟨-, h⟩
      · rw [hcJ] at hc
        cases hc
      · rw [h, hmJ]
        rfl
    have hWh := (height_le_h_max M F) S A x b w W hWb
    by_cases hWj : (M.chainStateOf S.C W).h = (x.stateBefore b w).justifiedHeight + 1
    · rw [compatible_iff]
      left
      have hFW := (F_ancestorEq_of_high M F Fx) S A x R E hRootsb tEnd b b w w W hThird hb hb hw hw
        hWb (by unfold Height at *; omega) (by omega)
      by_contra hJW
      have hc := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X (x.stateBefore b w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E le_rfl hw) W hmJ hWb hFW
        (by rw [hWj, hmJ]) hJW
      rw [hcJ] at hc
      cases hc
    · exact JW hmJ (by rw [hfl] at hflb; unfold Height at *; omega)
  · rw [hrF]
    exact hF

/-- **The frame of a validator with no fork-choice change is compatible with an honest vote's
viable block.** Under the execution assumptions and unforgeability, from `GST` on, with fewer than a
third of the validators in the adversary set up to `tEnd`; write `vt` for the vote time of slot
`σ`: when `u`'s tick at `vt` put `vote` on the wire, `u` ticks to `vt + 3Δ` at a real time at most `tEnd`, with no
`ForkChoiceChangeStep` at a step from its tick to `vt` to before that tick, `w` is
honest at `b ≤ tEnd`, `b ≥ vt + 2Δ`, with no `ForkChoiceChangeStep` at a step whose real time is
from `vt + 2Δ` to before `b`, then `vote` is `u`'s slot-`σ` vote for a block `H_u`, and some block
`W`, `H_u` or a descendant of it, held by `w` at its tick to `vt + Δ`, is such that before `b`: `w`'s
`head_height_floor` is at most `W`'s chain-state height, and `w`'s finalized block and fork-choice
root are compatible with `W`.

Why: `W` is a viable head of `u` at its tick to `vt`, `H_u` or a descendant of `H_u`
(`honest_vote_ancestor_of_viable`), still one at every later step up to its tick to `vt + 3Δ`
(`viable_head_kept_steps`); so `u`'s finalized block at every step before that tick or after it, up
to `vt + 3Δ`, is an ancestor of `W`. `w`'s finalized block before `vt + 2Δ` is compatible with `W`
(`finalized_compatible_of_viable`, `u`'s viable head at its tick to `vt + 3Δ`), so is its finalized block at
its tick to `vt + Δ`, an ancestor of it; `W` reaches `w` by that tick (`block_at_tick_of_held_tick`,
from `u`'s tick to `vt`, `w`'s tick to `vt` one delay earlier), so before `vt + 2Δ`, and
`frame_compatible_of_viable` from `vt + 2Δ` to `b`.

Restated: `u`'s no-change window `hNoU` ends at its own tick to `vt + 3Δ`
(`hkU3`, at a real time at most `tEnd`, `hEnd`) in place of the real time `vt + 3Δ`, and `u` is read at that
tick; `u`'s honesty at the real time `vt + 3Δ` (`hu`) and `hΔs` dropped; the delivery premises up to `tE`, at least
the clock value of that tick (`htE`), and the roots up to the real time `tR`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `b`: the times;
  `σ`: the slot of the vote; `u`: the voter; `w`: the validator whose frame is read; `vote`: the
  vote.

Roots name blocks until `tR`, at least `max (M.voteTime S.C σ + 3 * Δ S) b`: the proof keeps `W`
viable at `u` up to `vt + 3Δ` and reads `w`'s frame before `b`.

Restated with the delivery premises up to `tR`: the bound of its roots `hRoots`; every delivery its proof reads is due by then.


Read aloud: a validator with no fork-choice change has its finalized block and fork-choice root
compatible with the viable block an honest vote is an ancestor of. -/
theorem vote_frame_compatible_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST : ℕ)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    (tEnd σ b : ℕ) (u w : V) (vote : GoldfishVote V)
    -- from `a` on, the network is synchronous and every validator outside the adversary set is awake
    -- through `tEnd`; `a` is early enough for the windows the proof reads
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ M.voteTime S.C σ)
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hb : b ≤ tEnd) (hbσ : M.voteTime S.C σ + 2 * Δ S ≤ b)
    -- `u`'s tick to `vt + 3Δ`, at a real time at most `tEnd`, and no change of `u` from its tick to `vt` to
    -- before that tick
    (hkU3 : x.lbl (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) = Event.tick u (M.voteTime S.C σ + 3 * Δ S))
    (hEnd : x.time (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) ≤ tEnd)
    (hNoU : ∀ j : ℕ, x.tickStep u (M.voteTime S.C σ) ≤ j →
      j < x.tickStep u (M.voteTime S.C σ + 3 * Δ S) → ¬ ForkChoiceChangeStep M S A x u j)
    (hw : w ∉ A.corruptedAtTime x b)
    (hNoW : ∀ j : ℕ, ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → x.time j < (b : ℝ) →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) ≤ tR) (htRb : (b : ℝ) ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : M.voteTime S.C σ + 3 * Δ S ≤ tE) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree, vote = GoldfishVote.mk u σ H_u.root ∧
      ∃ W : Block V, H_u.AncestorEq W ∧ W ∈ (x.tickInput w (M.voteTime S.C σ + Δ S)).tree ∧
        M.head_height_floor (x.stateBefore b w) ≤ (M.chainStateOf S.C W).h ∧
        (x.stateBefore b w).finalized.compatible W = true ∧
        (M.get_fc_root (x.stateBefore b w)).compatible W = true := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hAB : ΔClockAhead < Δ S ∧ ΔClockBehind < Δ S := ⟨by linarith, by linarith⟩
  obtain ⟨H_u, hHT, hvote, W, hWv, hHW⟩ := (honest_vote_ancestor_of_viable M F U) S A x R E σ u vote hSend
  refine ⟨H_u, hHT, hvote, W, hHW, ?_⟩
  -- `u`'s tick to `vt`, and its tick to `vt + 3Δ`
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hSend
    exact x.lbl_tickStep ⟨i, hi⟩
  have hkUt := E.tick_active _ u _ hkU
  have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := E.not_mem_corrupted_of_tick hkU
  have hk3R := (E.tick_active _ u _ hkU3).2.1
  push_cast at hk3R
  have hu3 : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) := E.not_mem_corrupted_of_tick hkU3
  have hle3 : x.tickStep u (M.voteTime S.C σ) ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) :=
    (tick_step_le_of_le M F) E hkU hkU3 (by omega)
  -- `u` is outside the adversary set at every step up to its tick to `vt + 3Δ`
  have huj : ∀ j : ℕ, j ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) → u ∉ A.corrupted j :=
    fun j hj => E.not_mem_corrupted_of_le hj hu3
  -- `W` stays a viable head of `u` at every step from its tick to `vt` up to its tick to `vt + 3Δ`
  have hviab : ∀ i : ℕ, x.tickStep u (M.voteTime S.C σ) ≤ i → i ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) →
      W ∈ (M.fg_to_ac (x.st i u)).viable_heads := fun i hki hi3 =>
    (viable_head_kept_steps M F Fx) S A x R E hRoots tEnd u W hThird
      hki (le_trans (htime hi3) hEnd) (le_trans (htime hi3) htR) (huj i hi3)
      hWv (fun j h1 h2 => hNoU j h1 (lt_of_lt_of_le h2 hi3))
  have hcomp : ∀ i : ℕ, x.tickStep u (M.voteTime S.C σ) ≤ i → i ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) →
      W ∈ (x.st i u).tree ∧ (x.st i u).finalized.AncestorEq W := by
    intro i hki hi3
    have h := hviab i hki hi3
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _
      (lem11_node_invariant M F S A x R E i u (huj i hi3)).1] at h
    exact ⟨h.1, h.2.1⟩
  obtain ⟨hWT, -⟩ := hcomp _ le_rfl hle3
  -- `W` is a viable head of `u` at its tick to `vt + 3Δ`
  have hW3 : W ∈ (M.fg_to_ac (x.st (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) u)).viable_heads :=
    hviab _ hle3 le_rfl
  -- the window start of the delivery kit, one delay or one sync delay before `vt + Δ`
  obtain ⟨a', ha'⟩ : ∃ a' : ℕ, a' = M.voteTime S.C σ + Δ S - max (Δ S) Δs := ⟨_, rfl⟩
  have haa' : a ≤ a' := by omega
  -- a step at a real time at most `vt + Δ` comes before `u`'s tick to `vt + 3Δ`
  have hbefore3 : ∀ j : ℕ, x.time j ≤ ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) →
      j ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) := by
    intro j hj
    by_contra hc
    push_neg at hc
    have h1 := htime hc.le
    push_cast at hj
    linarith
  -- `u`'s finalized block at its last step before `a'` is an ancestor of `W`
  have hFa : (x.st (x.stepBefore a') u).finalized.compatible W = true := by
    refine (compatible_iff _ _).2 (Or.inl ?_)
    rcases le_total (x.stepBefore a') (x.tickStep u (M.voteTime S.C σ)) with hle | hle
    · exact ancestorEq_trans ((F_ancestorEq_of_le M F) x R E u hle) (hcomp _ le_rfl hle3).2
    · refine (hcomp _ hle (hbefore3 _ ?_)).2
      have h := (time_stepBefore_le M) x R E a'
      exact le_trans h (by exact_mod_cast (show a' ≤ M.voteTime S.C σ + Δ S by omega))
  -- `u` is active for one sync delay from `a'`
  have hu₀ : u ∈ A.activeThroughout x a' (a' + Δs) := by
    refine Activity.mem_activeThroughout.2 (fun j h1 h2 => ?_)
    have hjk : j ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) :=
      hbefore3 j (le_trans h1 (by exact_mod_cast (show a' + Δs ≤ M.voteTime S.C σ + Δ S by omega)))
    have hj := huj j hjk
    exact Activity.mem_active.2 ⟨hAw j u (le_trans (htime hjk) hEnd)
      (le_trans (by exact_mod_cast haa') h2) hj, hj⟩
  -- `u` is active at every step from `a` up to its tick to `vt + 3Δ`
  have hwinU : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) → u ∈ A.active i :=
    fun i h1 h2 => Activity.mem_active.2 ⟨hAw i u (le_trans (htime h2) hEnd)
      (le_trans h1 (htime (Nat.le_succ i))) (huj i h2), huj i h2⟩
  -- `w` is active from `a` to `b`, and ticks to `vt` and to `vt + Δ`
  have hwA : w ∈ A.activeThroughout x a b := (activeThroughout_nat_of_awake_from M F) R E hAw hw le_rfl hb
  have hv₀w : w ∈ A.activeThroughout x a (a + Δs) :=
    Activity.mem_activeThroughout_of_le le_rfl (by exact_mod_cast (show a + Δs ≤ b by omega)) hwA
  have haR : ((a : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hbR : ((M.voteTime S.C σ : ℕ) : ℝ) + 2 * Δ S ≤ (b : ℝ) := by exact_mod_cast hbσ
  obtain ⟨hk₂, -, -⟩ := (tickStep_spec M) x R E (t := M.voteTime S.C σ) (v := w) (by omega)
    (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) hwA)
  obtain ⟨hkR, -, hkR2⟩ := (tickStep_spec M) x R E (t := M.voteTime S.C σ + Δ S) (v := w) (by omega)
    (Activity.mem_activeThroughout_of_le (by push_cast; linarith) (by push_cast; linarith) hwA)
  have hwin : ∀ i : ℕ, (a' : ℝ) ≤ x.time i → i ≤ x.tickStep w (M.voteTime S.C σ + Δ S) → w ∈ A.active i := by
    intro i h1 h2
    have hti := htime h2
    exact Activity.mem_activeThroughout.1 hwA i (by push_cast at hkR2; linarith)
      (le_trans (by exact_mod_cast haa') (le_trans h1 (htime (Nat.le_succ i))))
  -- `w`'s tick to `vt + Δ` is before `vt + 2Δ`
  have h2 : 1 ≤ M.voteTime S.C σ + 2 * Δ S := by omega
  obtain ⟨-, hs2'⟩ := (stepBefore_time M) x R E h2
  have hkR2s : x.tickStep w (M.voteTime S.C σ + Δ S) ≤ x.stepBefore (M.voteTime S.C σ + 2 * Δ S) := by
    by_contra hc
    have h := htime (show x.stepBefore (M.voteTime S.C σ + 2 * Δ S) + 1 ≤ x.tickStep w (M.voteTime S.C σ + Δ S) by omega)
    push_cast at hs2' hkR2
    linarith
  have hw₂ : w ∉ A.corruptedAtTime x ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) :=
    (not_mem_corruptedAtTime_of_le M) x R E hbσ hw
  -- the slots: `W`'s, and those of the blocks `w` holds before `vt + 2Δ`, start no later than `vt`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  obtain ⟨-, -, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  have hslotv : S.C.slot ((M.voteTime S.C σ : ℕ) : Int) = σ :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hslot : ∀ Y ∈ (x.stateBefore (M.voteTime S.C σ + 2 * Δ S) w).tree,
      M.slotStart S.C Y.slot ≤ M.voteTime S.C σ := by
    intro Y hY
    have hi2 := (time_stepBefore_le M) x R E (M.voteTime S.C σ + 2 * Δ S)
    have hwS2 : w ∉ A.corrupted (x.stepBefore (M.voteTime S.C σ + 2 * Δ S)) :=
      (not_mem_corrupted_of_le_time M) x R E hw₂ (by exact_mod_cast hi2)
    have h := (slot_le_clockValue_of_mem_tree M F) R E hwS2 hY
    have hcv := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore (M.voteTime S.C σ + 2 * Δ S)) w
    have hcvR : (x.clockValue (x.stepBefore (M.voteTime S.C σ + 2 * Δ S)) w : ℝ) <
        ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) := by
      push_cast at hi2 ⊢
      refine lt_of_le_of_lt hcv (max_lt (by linarith) ?_)
      linarith
    -- the clock value is before the start of slot `σ + 1`, so in a slot at most `σ`
    have hcvN : x.clockValue (x.stepBefore (M.voteTime S.C σ + 2 * Δ S)) w < M.slotStart S.C (σ + 1) := by
      have := Nat.cast_lt.1 hcvR
      have hvtσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
      omega
    have hYs : Y.slot ≤ σ := by
      have hlt := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_lt_slotStart M.toSlotLayout F.sched) S hcvN
      rw [hsl] at hlt
      exact Nat.lt_succ_iff.mp (h.trans_lt hlt)
    exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hYs)
      (by omega)
  -- `w`'s finalized block before `vt + 2Δ`, and so at its tick to `vt + Δ`, is compatible with `W`
  have hFc := (finalized_compatible_of_viable_upTo M F U Fx) S A x R GST E hNet hSkew hRedeliver Sy hRoots
    hParent tEnd (M.voteTime S.C σ + 2 * Δ S) w u W a hGSTa (by omega) hThird hw₂ hv₀w
    (M.voteTime S.C σ + 3 * Δ S) (M.voteTime S.C σ) (x.tickStep u (M.voteTime S.C σ + 3 * Δ S))
    (x.tickStep u (M.voteTime S.C σ)) hkU3 (by omega) hEnd hwinU hkU (by omega) hslot hW3 htR (by omega)
  have hFw : (x.st (x.tickStep w (M.voteTime S.C σ + Δ S)) w).finalized.compatible W = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E w hkR2s) hFc
  -- `W`'s slot starts no later than `vt`
  have hWs : W.slot ≤ σ := by
    have h := (slot_le_clockValue_of_mem_tree M F) R E huk hWT
    rw [← hslotv]
    exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
      (by exact_mod_cast E.clockValue_le_of_set huk (Or.inl hkU)))
  have hDc₂ : M.slotStart S.C W.slot ≤ M.voteTime S.C σ :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hWs)
      (by omega)
  -- `W` reaches `w` by its tick to `vt + Δ`
  have hWw : W ∈ (x.tickInput w (M.voteTime S.C σ + Δ S)).tree := by
    by_cases hg : W = Block.genesis
    · rw [hg]
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
    have hRootsR : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C σ + Δ S))) :=
      (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (by
          push_cast at hkR2
          linarith) hRoots
    exact (block_at_tick_of_held_tick M F U) S A x R GST (M.voteTime S.C σ + Δ S) (M.voteTime S.C σ)
      (x.tickStep u (M.voteTime S.C σ)) a' (M.voteTime S.C σ + Δ S) (M.voteTime S.C σ)
      (x.tickStep w (M.voteTime S.C σ + Δ S)) (x.tickStep w (M.voteTime S.C σ)) u w W
      (E.mono (show M.voteTime S.C σ + Δ S ≤ tE by omega)) hNet hSkew hRedeliver
      (Sy.mono (show M.voteTime S.C σ + Δ S ≤ tE by omega)) hRootsR hParent (by omega) (by omega) le_rfl le_rfl hu₀ hkU hWT hFa hg hkR hwin hk₂
      le_rfl hDc₂ hFw
  have hWw2 : W ∈ (x.stateBefore (M.voteTime S.C σ + 2 * Δ S) w).tree :=
    (mem_T_mono M F) x R E w hkR2s hWw
  exact ⟨hWw, (frame_compatible_of_viable_upTo M F U Fx) S A x R GST E hNet hSkew hRedeliver Sy hRoots
    hParent tEnd (M.voteTime S.C σ + 2 * Δ S) b w u W a hGSTa (by omega) hThird hb hbσ
    hw hv₀w (M.voteTime S.C σ + 3 * Δ S) (M.voteTime S.C σ) (x.tickStep u (M.voteTime S.C σ + 3 * Δ S))
    (x.tickStep u (M.voteTime S.C σ)) hkU3 (by omega) hEnd hwinU hkU (by omega) hslot hW3 hWw2 hNoW htR htRb (by omega)⟩

/-- **With no fork-choice change, an honest vote of slot `σ` extends a validator's justified block
when that block is its root at its tick to a clock value at least one delay after the vote**. Under the execution assumptions and unforgeability, from `GST` on, with fewer
than a third of the validators in the adversary set up to `tEnd`; write `a₀` for the time `2Δ` into slot
`σ − 1` and `vt` for the vote time of slot `σ`: when `u` is awake and honest from `a₀` to `vt` with no
`ForkChoiceChangeStep` at a step whose real time is at least `a₀`, before its tick to `vt`; `w` ticks to a
clock value `c` with `vt + Δ ≤ c` at the step `kR`, at a real time at most `tEnd`, with no
`ForkChoiceChangeStep` at a step whose real time is at least `a₀`, before `kR`; `w`'s state at `kR` has
`hMax M S.C n = h_j + 1` and is not contested, so its root is its justified block; and `u`'s tick at
`vt` put `vote` on the wire — then `vote` is `u`'s slot-`σ` vote for a block `H_u` it holds at its tick,
and `w`'s justified block at `kR` is `H_u` or an ancestor of `H_u`.

Why (`j` is `w`'s cache `h_j` at `kR`, `J` its justified block): `w`'s cache was already `j` at its last
step before `a₀`, with the same `J` (`J_genesis_of_cache_passes_st`, Lemma 76), so `J`'s witness reaches
`u` by the view freeze (`mem_T_of_delivery_high_st`); `u`'s cache at its tick is not more than `j` (its
witness would reach `w` by its tick, `block_at_tick_of_held_tick`, and raise its greatest chain-state
height), so it is `j` and `u`'s justified block is `J`. Then `u`'s root is `J`, which the vote extends,
or `u`'s `head_height_floor` is at least `j + 1`: every viable block of `u` reaches `w` by its tick, at
the greatest chain-state height of `w`, so is a descendant of `J` (not contested), and no strict
ancestor of `J` is viable at `u`; the vote extends `J` (`honest_vote_spec`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`, `tEnd`: the times; `σ`: the slot of the
  vote; `c`, `kR`: the clock value and the step of `w`'s tick; `u`: the voter; `w`: the validator whose
  root is read; `vote`: the vote.

Roots name blocks up to `w`'s tick to `c`: every block the proof compares is held by `u` at steps up to
its tick to `vt`, or by `w` at steps up to `kR`, and `u`'s tick comes first.

Restated with the delivery premises up to `tE`, at least the clock value `c` of `w`'s tick: the deliveries its
proof reads are due by then.


Read aloud: with no fork-choice change, an honest vote of slot `σ` is for a block that has as
ancestor, or is, a validator's justified block when that block is its fork-choice root at its tick to a
clock value at least one delay after the vote time. -/
theorem vote_extends_justified_root_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST : ℕ)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hParent : ParentHeldAtDelivery M x)
    (tEnd σ c kR : ℕ) (u w : V) (vote : GoldfishVote V)
    -- roots name blocks up to `w`'s tick to `c`
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    -- the delivery premises reach the clock value `c` of `w`'s tick
    (htE : c ≤ tE)
    -- from `a` on, the network is synchronous and every validator outside the adversary set is awake
    -- through `tEnd`; `a` is early enough for the windows the proof reads
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ M.viewFreeze S.C (σ - 1))
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hσ : 1 ≤ σ) (hGST : GST ≤ M.slotStart S.C (σ - 1) + 2 * Δ S)
    (hkR : x.lbl kR = Event.tick w c) (hc : M.voteTime S.C σ + Δ S ≤ c) (hEnd : x.time kR ≤ tEnd)
    (hu : u ∈ A.activeThroughout x (M.slotStart S.C (σ - 1) + 2 * Δ S) (M.voteTime S.C σ))
    (hNoU : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → j < x.tickStep u (M.voteTime S.C σ) →
      ¬ ForkChoiceChangeStep M S A x u j)
    (hNoW : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → j < kR →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hmJ : hMax M S.C (x.st kR w) = (x.st kR w).justifiedHeight + 1)
    (hcJ : M.fg_contest (x.st kR w) = false)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree,
      vote = GoldfishVote.mk u σ H_u.root ∧ (x.st kR w).justified.AncestorEq H_u := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hσ' : σ - 1 + 1 = σ := Nat.sub_add_cancel hσ
  have hss : M.slotStart S.C σ = M.slotStart S.C (σ - 1) + 4 * Δ S := by
    rw [← hσ', (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one, hσ']
  have hfz : M.viewFreeze S.C (σ - 1) = M.slotStart S.C (σ - 1) + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (σ - 1)
  have hvt : M.voteTime S.C σ = M.slotStart S.C σ + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨H_u, hHT, hvote, hρH, hG⟩ := (honest_vote_spec M F U) S A x R E σ u vote hSend
  refine ⟨H_u, hHT, hvote, ?_⟩
  have eU : x.tickInput u (M.voteTime S.C σ) = x.st (x.tickStep u (M.voteTime S.C σ)) u := rfl
  rw [eU] at hρH hG
  -- `w`'s tick to `c`, at a real time at least `vt + Δ − ΔClockAhead`
  have hkRt := E.tick_active kR w c hkR
  have hwk : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hcR : ((M.voteTime S.C σ : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hc
  have hkRlo : ((M.voteTime S.C σ : ℕ) : ℝ) + Δ S - ΔClockAhead ≤ x.time kR := by linarith [hkRt.2.1]
  have hwT : ∀ t : ℝ, t < x.time kR → w ∉ A.corruptedAtTime x t := by
    intro t ht
    refine Activity.not_mem_corruptedAtTime.2 fun i hi hvi => hwk ?_
    have hik : i < kR := (lt_of_time_lt M) x R (by linarith)
    exact E.corrupted_mono i kR hik.le hvi
  have hvtE : M.voteTime S.C σ ≤ tEnd := by
    have h : ((M.voteTime S.C σ : ℕ) : ℝ) ≤ (tEnd : ℝ) := by linarith
    exact_mod_cast h
  have hInvW := (lem11_node_invariant M F S A x R E kR w hwk).1
  -- `u`'s tick to `vt`, before `w`'s tick
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hSend
    exact x.lbl_tickStep ⟨i, hi⟩
  have hkUt := E.tick_active _ u _ hkU
  have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := E.not_mem_corrupted_of_tick hkU
  have hkUR : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ x.time kR := by linarith [hkUt.2.2]
  have hkUE : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ (tEnd : ℝ) := le_trans hkUR hEnd
  have hInvU := (lem11_node_invariant M F S A x R E (x.tickStep u (M.voteTime S.C σ)) u huk).1
  have huvt : u ∉ A.corruptedAtTime x ((M.voteTime S.C σ : ℕ) : ℝ) :=
    E.not_mem_corruptedAtTime_of_mem_activeThroughout R.time_zero (fun _ _ h => R.time_mono h)
      (by exact_mod_cast (show M.slotStart S.C (σ - 1) + 2 * Δ S ≤ M.voteTime S.C σ by omega)) hu
  -- the last step before `a₀`
  have ha1 : 1 ≤ M.slotStart S.C (σ - 1) + 2 * Δ S := by omega
  obtain ⟨has, has'⟩ := (stepBefore_time M) x R E ha1
  have haR : ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) + 3 * Δ S = ((M.voteTime S.C σ : ℕ) : ℝ) := by
    have h : M.slotStart S.C (σ - 1) + 2 * Δ S + 3 * Δ S = M.voteTime S.C σ := by omega
    exact_mod_cast h
  have haU : x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) ≤ x.tickStep u (M.voteTime S.C σ) := by
    apply le_of_lt
    apply (lt_of_time_lt M) x R
    linarith [hkUt.2.1]
  have hUkR : x.tickStep u (M.voteTime S.C σ) ≤ kR := by
    by_contra hc'
    have := htime (show kR ≤ x.tickStep u (M.voteTime S.C σ) by omega)
    have hlt : x.time (x.tickStep u (M.voteTime S.C σ)) < x.time kR := by linarith [hkUt.2.2]
    linarith
  have hakR : x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) ≤ kR := le_trans haU hUkR
  have hwa : w ∉ A.corrupted (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) := E.not_mem_corrupted_of_le hakR hwk
  have hua : u ∉ A.corrupted (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) := E.not_mem_corrupted_of_le haU huk
  -- the genesis block is an ancestor of everything
  by_cases hJg : (x.st kR w).justified = Block.genesis
  · rw [hJg]
    exact genesis_ancestorEq H_u
  have hj1 : 1 ≤ (x.st kR w).justifiedHeight := by
    by_contra h0
    exact hJg ((J_genesis_st M F) S A x R E kR w (by unfold Height at *; omega))
  -- `w`'s cache was `j` at its last step before `a₀`
  have hNoWs : ∀ k : ℕ, x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) ≤ k → k < kR →
      ¬ ForkChoiceChangeStep M S A x w k := by
    intro k h1 h2
    rcases eq_or_lt_of_le h1 with heq | hlt
    · intro hch
      apply (state_ne_of_change_step M F) hch
      rw [← heq]
      exact (stepBefore_succ_state_eq M F) x R E ha1 w
    · exact hNoW k (le_trans has' (htime hlt)) h2
  have hja : (x.st (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) w).justifiedHeight ≤
      (x.st kR w).justifiedHeight :=
    (h_j_mono_st M F Fx) S A x R E hRoots tEnd w hakR hThird hEnd hwk le_rfl
  have hjaeq : (x.st (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) w).justifiedHeight =
      (x.st kR w).justifiedHeight := by
    by_contra hne
    exact hJg ((J_genesis_of_cache_passes_st M F Fx) S A x R E hRoots tEnd _ kR
      (x.st kR w).justifiedHeight w hThird hakR hEnd hwk hNoWs (by unfold Height at *; omega) le_rfl
      (by rw [hmJ]) le_rfl)
  -- a block `u` holds at its tick, with `u`'s finalized block there an ancestor of it, of height
  -- greater than `j`, is in `w`'s tree at `kR`, a descendant of `w`'s finalized block there
  obtain ⟨a', ha'⟩ : ∃ a' : ℕ, a' = M.voteTime S.C σ - max (Δ S) Δs := ⟨_, rfl⟩
  have haa' : a ≤ a' := by omega
  have ha'1 : 1 ≤ a' := by omega
  have ha'U : x.stepBefore a' ≤ x.tickStep u (M.voteTime S.C σ) := by
    apply le_of_lt
    apply (lt_of_time_lt M) x R
    have h := ((stepBefore_time M) x R E ha'1).1
    have : (a' : ℝ) + Δ S ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by
      exact_mod_cast (show a' + Δ S ≤ M.voteTime S.C σ by omega)
    linarith [hkUt.2.1]
  have hu₀ : u ∈ A.activeThroughout x a' (a' + Δs) := by
    have h := (activeThroughout_nat_of_awake_from M F) R E hAw huvt haa' hvtE
    exact Activity.mem_activeThroughout_of_le le_rfl
      (by exact_mod_cast (show a' + Δs ≤ M.voteTime S.C σ by omega)) h
  have hwin : ∀ i : ℕ, (a' : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i := by
    intro i h1 h2
    have hwi : w ∉ A.corrupted i := E.not_mem_corrupted_of_le h2 hwk
    exact Activity.mem_active.2 ⟨hAw i w (le_trans (htime h2) hEnd)
      (le_trans (by exact_mod_cast haa') (le_trans h1 (htime (Nat.le_succ i)))) hwi, hwi⟩
  -- `w` ticks to the start of slot `σ`
  have hss1 : 1 ≤ M.slotStart S.C σ := by omega
  have hwS : w ∈ A.activeThroughout x ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ((M.voteTime S.C σ : ℕ) : ℝ) :=
    (activeThroughout_nat_of_awake_from M F) R E hAw (hwT _ (by linarith)) (by omega) hvtE
  have hsR : ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) + 2 * Δ S = ((M.slotStart S.C σ : ℕ) : ℝ) := by
    have h : M.slotStart S.C (σ - 1) + 2 * Δ S + 2 * Δ S = M.slotStart S.C σ := by omega
    exact_mod_cast h
  have hvR : ((M.slotStart S.C σ : ℕ) : ℝ) + Δ S = ((M.voteTime S.C σ : ℕ) : ℝ) := by exact_mod_cast hvt.symm
  obtain ⟨hk₂, -, -⟩ := (tickStep_spec M) x R E (t := M.slotStart S.C σ) (v := w) hss1
    (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) hwS)
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  obtain ⟨-, -, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  have hslotv : S.C.slot ((M.voteTime S.C σ : ℕ) : Int) = σ :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hreach : ∀ Y : Block V, Y ∈ (x.st (x.tickStep u (M.voteTime S.C σ)) u).tree →
      (x.st (x.tickStep u (M.voteTime S.C σ)) u).finalized.AncestorEq Y →
      (x.st kR w).justifiedHeight < (M.chainStateOf S.C Y).h →
      Y ∈ (x.st kR w).tree ∧ (x.st kR w).finalized.AncestorEq Y := by
    intro Y hY hFuY hYh
    have hFwY := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd kR (x.tickStep u (M.voteTime S.C σ))
      w u Y hThird hEnd hkUE hwk huk hY hYh (max_le le_rfl hkUR)
    refine ⟨?_, hFwY⟩
    by_cases hg : Y = Block.genesis
    · rw [hg]
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
    have hYs : Y.slot ≤ σ := by
      have h := (slot_le_clockValue_of_mem_tree M F) R E huk hY
      rw [← hslotv]
      exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
        (by exact_mod_cast E.clockValue_le_of_set huk (Or.inl hkU)))
    exact (block_at_tick_of_held_tick M F U) S A x R GST c (M.voteTime S.C σ)
      (x.tickStep u (M.voteTime S.C σ)) a' c (M.slotStart S.C σ) kR (x.tickStep w (M.slotStart S.C σ)) u w Y
      (E.mono htE) hNet hSkew hRedeliver
      (Sy.mono htE) hRoots hParent (by omega) (by omega) hc le_rfl hu₀ hkU hY
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E u ha'U) hFuY))) hg hkR hwin hk₂
      (by omega) ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hYs)
      ((compatible_iff _ _).2 (Or.inl hFwY))
  -- `u`'s cache at its tick is at most `j`
  have hjuv : (x.st (x.tickStep u (M.voteTime S.C σ)) u).justifiedHeight ≤ (x.st kR w).justifiedHeight := by
    by_contra hgt
    obtain ⟨⟨Yu, hYu, hJYu, hjYu⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E (x.tickStep u (M.voteTime S.C σ)) u
    have hYuh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Yu Yu).1.2.1
    have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E
      (x.tickStep u (M.voteTime S.C σ)) u
    rw [hJYu] at hFJ
    have hr := (hreach Yu hYu (ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Yu).1)
      (by unfold Height at *; omega)).1
    have hh := le_hMax M (C := S.C) hr
    unfold Height at *
    omega
  -- `J`'s witness reaches `u` by the view freeze
  obtain ⟨⟨Y, hY, hJY, hjY⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E (M.slotStart S.C (σ - 1) + 2 * Δ S) w
  have hjY' : (x.st (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) w).justifiedHeight = (M.chainStateOf S.C Y).h_j := hjY
  have hYh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Y Y).1.2.1
  have hvf1 : 1 ≤ M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S := by omega
  have hvfR : ((M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S : ℕ) : ℝ) + 2 * Δ S ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by
    exact_mod_cast (show M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S + 2 * Δ S ≤ M.voteTime S.C σ by omega)
  have hvfU : x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S) ≤ x.tickStep u (M.voteTime S.C σ) := by
    apply le_of_lt
    apply (lt_of_time_lt M) x R
    have h := ((stepBefore_time M) x R E hvf1).1
    linarith [hkUt.2.1]
  have hjuf : (x.stateBefore (M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S) u).justifiedHeight ≤
      (x.st (x.tickStep u (M.voteTime S.C σ)) u).justifiedHeight :=
    (h_j_mono_st M F Fx) S A x R E hRoots tEnd u hvfU hThird hkUE huk hkUR
  have htN : ((M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S : ℕ) : ℝ) ≤ x.time kR := by linarith [hkUt.2.1]
  have htNE : M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S ≤ tE := by
    have := (GoldilocksCorrectness.Record.Proofs.Executions.viewFreeze_pred_le_voteTime M F U) S hσ
    have := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (σ - 1)
    omega
  -- `Y` reaches `u` by its tick to `vt` (`mem_T_of_delivery_high_st`, the receiver read at its tick; F-P1-24-2): `w`
  -- holds it at its last step before `a₀`, is active from `a` through the sync delay after it (honest before `kR`),
  -- and `u` ticked to the start of slot `σ`, at least the start of `Y`'s slot
  have hckw : x.clockValue (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) w ≤ M.voteTime S.C σ := by
    have h1 := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) w
    have hvt0 : (0 : ℝ) ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by positivity
    have h2 : ((x.clockValue (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) w : ℕ) : ℝ) ≤
        ((M.voteTime S.C σ : ℕ) : ℝ) :=
      le_trans h1 (max_le hvt0 (by linarith [has, haR]))
    exact_mod_cast h2
  have hYs : Y.slot ≤ σ := by
    have h := (slot_le_clockValue_of_mem_tree M F) R E hwa hY
    rw [← hslotv]
    exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hckw))
  have hw₀ : w ∈ A.activeThroughout x a (a + Δs) := by
    have hlt : (((a + Δs : ℕ) : ℝ)) < x.time kR := by
      have : ((a + Δs : ℕ) : ℝ) ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by
        exact_mod_cast (show a + Δs ≤ M.voteTime S.C σ by omega)
      linarith [hkRlo]
    have h := (activeThroughout_nat_of_awake_from M F) R E hAw (hwT _ hlt) (le_refl a) (by omega)
    simpa using h
  have hselA : (x.st (x.stepBefore a) w).finalized.compatible Y = true := by
    have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_stateBefore M F) S A x R E
      (M.slotStart S.C (σ - 1) + 2 * Δ S) w
    rw [hJY] at hFJ
    exact GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E w ((stepBefore_mono M) x R E (show a ≤ M.slotStart S.C (σ - 1) + 2 * Δ S by omega)))
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Y).1)))
  have hwinU : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ x.tickStep u (M.voteTime S.C σ) → u ∈ A.active i := by
    intro i h1 h2
    have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_le h2 huk
    exact Activity.mem_active.2 ⟨hAw i u (le_trans (htime h2) hkUE) (le_trans h1 (htime (Nat.le_succ i))) hui, hui⟩
  obtain ⟨hk₂u, -, -⟩ := (tickStep_spec M) x R E (t := M.slotStart S.C σ) (v := u) hss1
    (Activity.mem_activeThroughout_of_le (by push_cast at hsR; linarith) (by push_cast at hsR; linarith) hu)
  have hYv : Y ∈ (x.st (x.tickStep u (M.voteTime S.C σ)) u).tree :=
    (mem_T_of_delivery_high_st M F U Fx) S A x R GST (M.voteTime S.C σ) tEnd (M.slotStart S.C (σ - 1) + 2 * Δ S)
      (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) a (M.voteTime S.C σ) (M.slotStart S.C σ)
      (x.tickStep u (M.voteTime S.C σ)) (x.tickStep u (M.slotStart S.C σ)) w u Y
      (E.mono (show M.voteTime S.C σ ≤ tE by omega)) hNet hSkew hRedeliver
      (Sy.mono (show M.voteTime S.C σ ≤ tE by omega))
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hkUR hRoots) hParent hThird hkUE
      hGSTa (by omega) (by omega) le_rfl hw₀ ((time_stepBefore_le M) x R E _) hwa hY hselA hkU hwinU hk₂u (by omega)
      ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hYs)
      (by unfold Height at *; omega)
  have hFuY := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd (x.tickStep u (M.voteTime S.C σ))
    (x.tickStep u (M.voteTime S.C σ)) u u Y hThird hkUE hkUE huk huk hYv (by unfold Height at *; omega)
    (max_le hkUR hkUR)
  have hjY'' := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E _ u Y hYv hFuY
  have hjueq : (x.st (x.tickStep u (M.voteTime S.C σ)) u).justifiedHeight = (x.st kR w).justifiedHeight := by
    unfold Height at *
    omega
  have hJu : (x.st (x.tickStep u (M.voteTime S.C σ)) u).justified = (x.st kR w).justified :=
    (J_eq_of_h_j_eq_st M F Fx) S A x R E hRoots tEnd (x.tickStep u (M.voteTime S.C σ)) kR u w hThird hkUE hEnd
      huk hwk hjueq (max_le hkUR le_rfl)
  -- the cases on `u`'s root
  by_cases hru : M.get_fc_root (x.st (x.tickStep u (M.voteTime S.C σ)) u) = (x.st (x.tickStep u (M.voteTime S.C σ)) u).justified
  · rw [← hJu, ← hru]
    exact hρH
  have hm : (x.st (x.tickStep u (M.voteTime S.C σ)) u).justifiedHeight + 1 ≤ hMax M S.C (x.st (x.tickStep u (M.voteTime S.C σ)) u) :=
    (h_j_lt_h_max_st M F) S A x R E (x.tickStep u (M.voteTime S.C σ)) u
  have hflu := (GoldilocksCorrectness.Record.Proofs.Routines.floor_of_root_ne_J M F) S.C S.P S.X _ hInvU hm hru
  -- `u`'s clock at its last step before `a₀` is less than the view freeze
  have hcka : x.clockValue (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) u < M.viewFreeze S.C (σ - 1) := by
    have h1 := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) u
    have hvfR' : ((M.viewFreeze S.C (σ - 1) : ℕ) : ℝ) = ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) + Δ S := by
      rw [show M.viewFreeze S.C (σ - 1) = M.slotStart S.C (σ - 1) + 2 * Δ S + Δ S by omega]; push_cast; ring
    have hvf0 : (0 : ℝ) < ((M.viewFreeze S.C (σ - 1) : ℕ) : ℝ) := by exact_mod_cast (show 0 < M.viewFreeze S.C (σ - 1) by omega)
    have h2 : ((x.clockValue (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) u : ℕ) : ℝ) <
        ((M.viewFreeze S.C (σ - 1) : ℕ) : ℝ) :=
      lt_of_le_of_lt h1 (max_lt hvf0 (by rw [hvfR']; linarith [hSkew]))
    exact_mod_cast h2
  obtain ⟨W₀, hW₀⟩ := (frame_has_viable_head M F) S A x R E (M.slotStart S.C (σ - 1) + 2 * Δ S) u
  have hW₀T : W₀ ∈ (x.st (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) u).tree :=
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _
      (lem11_node_invariant M F S A x R E _ u hua).1 _).1 hW₀).1
  have hW₀v : W₀ ∈ (M.fg_to_ac (x.st (x.tickStep u (M.voteTime S.C σ)) u)).viable_heads :=
    (viable_head_kept_steps M F Fx) S A x R E hRoots tEnd u W₀ hThird haU hkUE hkUR huk hW₀
      (by
        intro j h1 h2
        rcases eq_or_lt_of_le h1 with heq | hlt
        · intro hch
          apply (state_ne_of_change_step M F) hch
          rw [← heq]
          exact (stepBefore_succ_state_eq M F) x R E ha1 u
        · exact hNoU j (le_trans has' (htime hlt)) h2)
  refine hG (x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S)) W₀ _ haU hW₀T hcka hW₀v ?_ ?_
  · intro W hW
    obtain ⟨hWT, hFW', -, hWfl⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInvU _).1 hW
    have hWh : (x.st kR w).justifiedHeight < (M.chainStateOf S.C W).h := by
      unfold Height at *
      omega
    obtain ⟨hWt, hFW⟩ := hreach W hWT hFW' hWh
    have hWm := le_hMax M (C := S.C) hWt
    by_contra hJW
    have hc' := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X (x.st kR w) hInvW W hmJ hWt hFW
      (by unfold Height at *; omega) hJW
    rw [hcJ] at hc'
    cases hc'
  · intro B hBJ hne hBv
    obtain ⟨-, -, -, hBfl⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInvU _).1 hBv
    have hBh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B _).2.2.2.1 hBJ
    rw [(J_height_st M F) S A x R E kR w hj1] at hBh
    unfold Height at *
    omega


/-- **A member of slot `σ + 1` saves a confirmation of slot `σ` when no fork choice changes**
(F-P1-2). In the phase from `tGAT` to `tAwakeEnd`, with every validator honest at an update in it an
honest active validator and an updater of the slot, the slot `σ − 1` starting one sync delay and four
delays after `tGAT`, the duty window of slot `σ` starting at or after `tGAT`, more than half of the committee of slot `σ` honest through the support cutoff of
slot `σ + 1`, and no validator honest through that cutoff changing its fork choice at a step whose
real time is from `2Δ` into slot `σ − 1`, before one of its ticks to a clock value at most that cutoff:
every validator `v` honest through the support cutoff of slot `σ + 1` holds,
right after its tick to that cutoff, a confirmation of slot `σ`.

Why: `v` ticks to that cutoff (an updater of slot `σ`), and every honest vote of slot `σ` of a member
of the committee extends `v`'s finalized block there (`vote_extends_finalized_st_of_no_change`, `v` read
at that tick); so the update saves one (`confirmation_saved_of_votes`, the voters
counted at `v`'s tick by `counting_of_committee_majority_st`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`, `tGAT`, `tAwakeEnd`: the phase; `σ`:
  the slot of the votes; `tR`: the end of the no-change window; `v`: the member.

Roots name blocks up to `v`'s own tick to the support cutoff of slot `σ + 1`: the proof
reads `v` at that tick, and the voters at their ticks to the vote time of slot `σ`, which come before it.

Restated with the delivery premises up to `tR`: the bound `tR` of the reads, at least one delay after the support cutoff of slot `σ + 1`; every delivery its proof reads is due by then.


Read aloud: when no honest validator's fork choice changes in the window, every validator honest
through the support cutoff of slot `σ + 1` saves a confirmation of slot `σ` at its update. -/
theorem member_saves_of_no_change_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd σ tR : ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tR) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tR)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hσ : 1 ≤ σ) (hsync : tGAT + max (Δ S) Δs + 4 * Δ S ≤ M.slotStart S.C (σ - 1))
    (hdw : tGAT ≤ M.dutyWindowStart S.C σ)
    (htR : M.supportCutoff S.C (σ + 1) + Δ S ≤ tR) (hRE : tR ≤ tAwakeEnd)
    (hMaj : (S.P.committee σ).card < 2 * (S.P.committee σ ∩ roundMembers M S A x (σ + 1)).card)
    (hNo : ∀ (w : V) (j k' c : ℕ), w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) →
      ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → x.lbl k' = Event.tick w c →
      c ≤ M.supportCutoff S.C (σ + 1) → j < k' → w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j)
    (v : V)
    -- roots name blocks up to `v`'s own tick to the support cutoff of slot `σ + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (σ + 1)))))
    (hv : v ∈ roundMembers M S A x (σ + 1)) :
    ∃ D : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some D := by
  have hvtR : M.voteTime S.C σ ≤ tR := by
    obtain ⟨-, -, -, hs1', -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
    obtain ⟨-, hc1', -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
    omega
  have hcσR : M.supportCutoff S.C σ ≤ tR := by
    obtain ⟨-, hc0', -, hs1', -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
    obtain ⟨-, hc1', -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
    omega
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hmx1 := le_max_left (Δ S) Δs
  have hσ' : σ - 1 + 1 = σ := Nat.sub_add_cancel hσ
  obtain ⟨hvt0, hc0, hfz0, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ - 1)
  obtain ⟨hvt1, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨-, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  rw [hσ'] at hs0
  have hcutE : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd := by omega
  -- the slot's honest members and the duty window
  have hsub := ((roundMembers_subset_honestActiveAt M F U) S A tGAT tAwakeEnd σ R E hActive hdw hcutE).1
  have hcut1 : ∀ w : V, w ∈ roundMembers M S A x (σ + 1) → w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) :=
    fun w hw => (Finset.mem_sdiff.1 hw).2
  -- `v`'s tick to the support cutoff of slot `σ + 1`
  have hvU : v ∈ updaterAt M S A x σ := (hActive σ hdw hcutE v (hcut1 v hv)).2
  have hkV : x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) = Event.tick v (M.supportCutoff S.C (σ + 1)) := by
    classical
    have h := hvU
    unfold updaterAt Activity.activeThroughoutToTick at h
    obtain ⟨k', hk', -⟩ := (Finset.mem_filter.1 h).2
    exact x.lbl_tickStep ⟨k', hk'⟩
  have hkVt := E.tick_active _ v _ hkV
  have hvk : v ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (σ + 1))) := E.not_mem_corrupted_of_tick hkV
  have hkVtR : x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) < (tR : ℝ) := by
    have : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤ (tR : ℝ) := by exact_mod_cast htR
    linarith [hkVt.2.2]
  -- every honest vote of slot `σ` of a member extends `v`'s finalized block at its tick
  have hC1 : ∀ u ∈ S.P.committee σ ∩ roundMembers M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree,
        vote = GoldfishVote.mk u σ H_u.root ∧
        (x.tickInput v (M.supportCutoff S.C (σ + 1))).finalized.AncestorEq H_u := by
    intro u hu vote hSend
    have hu1 := hcut1 u (Finset.mem_inter.1 hu).2
    have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
      obtain ⟨i, hi, -⟩ := hSend
      exact x.lbl_tickStep ⟨i, hi⟩
    have hkUt := E.tick_active _ u _ hkU
    have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := E.not_mem_corrupted_of_tick hkU
    have hstepa : x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) ≤ x.tickStep v (M.supportCutoff S.C (σ + 1)) := by
      apply le_of_lt
      apply (lt_of_time_lt M) x R
      have h := ((stepBefore_time M) x R E (show 1 ≤ M.slotStart S.C (σ - 1) + 2 * Δ S by omega)).1
      have : ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) + 2 * Δ S ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.slotStart S.C (σ - 1) + 2 * Δ S + 2 * Δ S ≤ M.supportCutoff S.C (σ + 1) by omega)
      linarith [hkVt.2.1]
    have hEndV : x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ (tAwakeEnd : ℝ) :=
      le_trans hkVtR.le (by exact_mod_cast hRE)
    have habV : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) := by
      have : ((M.voteTime S.C σ : ℕ) : ℝ) + 2 * Δ S ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C σ + 2 * Δ S ≤ M.supportCutoff S.C (σ + 1) by omega)
      linarith [hkVt.2.1, hkUt.2.2]
    exact (vote_extends_finalized_st_of_no_change_upTo M F U Fx) S A x R GST tAwakeEnd σ
      (x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))))
      (x.tickStep v (M.supportCutoff S.C (σ + 1))) u v vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent
      hvtR tGAT hGST (by omega) hAwake hThird hσ (by omega) hEndV habV le_rfl hstepa hvk
      ((not_mem_corruptedAtTime_of_le M) x R E (by omega) (hcut1 v hv))
      (by
        have h := (activeThroughout_nat_of_awake_from M F) R E hAwake hu1 (b := M.slotStart S.C (σ - 1) + 2 * Δ S) (by omega) hcutE
        exact Activity.mem_activeThroughout_of_le (a' := (M.slotStart S.C (σ - 1) : ℝ) + 2 * (Δ S : ℝ))
          (b' := ((M.voteTime S.C σ : ℕ) : ℝ)) (by push_cast; exact le_rfl)
          (by exact_mod_cast (show M.voteTime S.C σ ≤ M.supportCutoff S.C (σ + 1) by omega)) h)
      (fun j h1 h2 => hNo v j _ _ (hcut1 v hv) h1 hkV le_rfl h2
        (E.not_mem_corrupted_of_le h2.le hvk))
      (fun j h1 h2 => hNo u j _ _ hu1 h1 hkU (by omega) h2
        (E.not_mem_corrupted_of_le h2.le huk))
      hSend
  obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R σ
    (S.P.committee σ ∩ roundMembers M S A x (σ + 1)) _ E hSkew
    (fun u hu => ⟨hsub (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩) hC1
  -- Lemma 12's three inputs: roots up to `v`'s own tick to the support cutoff of slot `σ`, each
  -- voter outside the adversary set at `v`'s tick to the support cutoff of slot `σ + 1` (the second honesty read of
  -- `honestActiveAt`), and each voter active through the sync delay after Lemma 12's read time
  have hRootsσ : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C σ))) := by
    have hvU' := hvU
    unfold updaterAt at hvU'
    obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew hvU'
    rw [(tickStep_eq_of_lbl M) x E hkR]
    have ht := (E.tick_active kR v _ hkR).2.2
    have hle : ((M.supportCutoff S.C σ : ℕ) : ℝ) + 4 * Δ S = ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C σ + 4 * Δ S = M.supportCutoff S.C (σ + 1) by omega)
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith [hkVt.2.1]) hRoots
  have hHonTick : ∀ u ∈ S.P.committee σ ∩ roundMembers M S A x (σ + 1),
      u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (σ + 1))) := by
    intro u hu
    classical
    have hu' := hsub (Finset.mem_inter.1 hu).2
    have hvU' := hvU
    unfold honestActiveAt at hu'
    unfold updaterAt at hvU'
    have hX : u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
        x.lbl k = Event.tick w (M.supportCutoff S.C (σ + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) :=
      fun h => (Finset.mem_sdiff.1 hu').2 (Finset.mem_union.2 (Or.inr h))
    exact (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E hvU' hX
  have hHold : ∀ u ∈ S.P.committee σ ∩ roundMembers M S A x (σ + 1),
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
    intro u hu
    have hu1 := hcut1 u (Finset.mem_inter.1 hu).2
    have hb : tGAT ≤ M.supportCutoff S.C σ - max (2 * Δ S) Δs := by
      rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;>
      rcases max_cases (Δ S) Δs with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] <;> rw [h'] at hsync <;> omega
    have hend : M.supportCutoff S.C σ - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C (σ + 1) := by
      rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
    have h := (activeThroughout_nat_of_awake_from M F) R E hAwake hu1 hb hcutE
    refine Activity.mem_activeThroughout_of_le le_rfl ?_ h
    exact_mod_cast hend
  exact (confirmation_saved_of_votes_upTo M F U) S A x R GST σ
    (S.P.committee σ ∩ roundMembers M S A x (σ + 1)) H v (E.mono hcσR) hNet hSkew hRedeliver (Sy.mono hcσR) hΔs
    hRootsσ
    hParent ((GoldilocksCorrectness.Record.Statements.Executions.votesCastByOwner_of_unforgeability M F) S A x R E)
    (by omega)
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1, hHonTick u hu, (hH u hu).1, (hH u hu).2.1,
      (hH u hu).2.2⟩)
    hHold
    ((counting_of_committee_majority_st M F) S A x R E σ (x.tickStep v (M.supportCutoff S.C (σ + 1)))
      (roundMembers M S A x (σ + 1)) v hMaj).2.1
    hvU

/-- **`frame_compatible_of_viable` read at a step of `w`** (rule R3: a validator's own state is read at its own
steps). The hypotheses of `frame_compatible_of_viable`, with `w` read at the step `i` in place of before the time `b`:
`w` is honest at `t₀` and at `i`, `i` comes at or after `w`'s last step before `t₀` and at a real time at most `tEnd`,
and `w` has no `ForkChoiceChangeStep` at a step from its last step before `t₀` to before `i`. Then at `i`: `w`'s
`head_height_floor` is at most `W`'s chain-state height, and `w`'s finalized block and fork-choice root are compatible
with `W`.

Why: `frame_compatible_of_viable`'s argument with each read before `b` made at `i` (`floor_le_of_no_change_st`,
`grows_of_le`, the step forms of the justified-cache kit, `lem68_honest_past_finalized`, `F_eq_J_of_height_st`,
`F_ancestorEq_of_high_st`).

Restated: `u` read at its tick `kR` to a clock value `c ≥ t₀ + Δ S` (the rows
of `finalized_compatible_of_viable`: `hkR`, `hcu`, `hEnd`, `hwin`, `hk₂`, `hc₂`, `hslot`, `hW`, with `w` active
from `a` through the sync delay after it, `hv₀`), passed through; `hAw`, `hΔs`, `h1` and `hGST` dropped; the delivery premises up to `tE`, at least
the clock value of that tick (`htE`), and the roots up to the real time `tR`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`, `tEnd`, `t₀`: the times; `i`: the step of `w`;
  `w`, `u`: the two validators; `W`: the block.

Roots name blocks until `tR`, at least `t₀ + Δ S` and the real time of `i`: the proof compares blocks `u` holds
before `t₀ + Δ` and blocks `w` holds at `i`.

Restated with the delivery premises up to `tE`, at least one delay after `t₀`: the deliveries its proof reads
are the ones of `floor_le_of_viable_tick_upTo` and `root_compatible_of_viable_upTo` at `t₀`, due by then.


Read aloud: while a validator's fork choice does not change, at each of its later steps its `head_height_floor` is at
most the chain-state height of another validator's viable block, and its finalized block and fork-choice root are
compatible with that block. -/
theorem frame_compatible_of_viable_st_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST : ℕ)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    (tEnd t₀ i : ℕ) (w u : V) (W : Block V)
    -- from `a` on, the network is synchronous and every validator outside the adversary set is awake
    -- through `tEnd`; `a` is early enough for the windows the proof reads
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t₀ + Δ S)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hi : x.time i ≤ tEnd) (hi₀ : x.stepBefore t₀ ≤ i)
    (hw₀ : w ∉ A.corruptedAtTime x t₀) (hw : w ∉ A.corrupted i)
    (hv₀ : w ∈ A.activeThroughout x a (a + Δs))
    -- `u`'s tick to `c`, at least one delay after `t₀`, at a real time at most `tEnd`, its window from `a`, and
    -- an earlier tick to `c₂`, one delay before `c`, at least the start of every slot of `w`'s blocks before `t₀`
    (c c₂ kR k₂ : ℕ) (hkR : x.lbl kR = Event.tick u c) (hcu : t₀ + Δ S ≤ c) (hEnd : x.time kR ≤ tEnd)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → u ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick u c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.stateBefore t₀ w).tree, M.slotStart S.C Y.slot ≤ c₂)
    (hW : W ∈ (M.fg_to_ac (x.st kR u)).viable_heads)
    (hWw : W ∈ (x.stateBefore t₀ w).tree)
    (hNo : ∀ j : ℕ, x.stepBefore t₀ ≤ j → j < i → ¬ ForkChoiceChangeStep M S A x w j)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time kR ≤ tR) (htRi : x.time i ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : c ≤ tE) :
    M.head_height_floor (x.st i w) ≤ (M.chainStateOf S.C W).h ∧
      (x.st i w).finalized.compatible W = true ∧
      (M.get_fc_root (x.st i w)).compatible W = true := by
  have hSt₀ : x.stateBefore t₀ w = x.st (x.stepBefore t₀) w := rfl
  have hi₀t := (time_stepBefore_le M) x R E t₀
  have hw₀' : w ∉ A.corrupted (x.stepBefore t₀) :=
    (not_mem_corrupted_of_le_time M) x R E hw₀ (by exact_mod_cast hi₀t)
  have hi₀E : x.time (x.stepBefore t₀) ≤ tEnd :=
    le_trans (R.time_mono hi₀) hi
  have htR₀ : x.time (x.stepBefore t₀) ≤ tR :=
    le_trans (R.time_mono hi₀) htRi
  have hflw₀ := (floor_le_of_viable_tick_upTo M F U Fx) S A x R GST t₀ a c c₂ kR k₂ w u W E hNet hSkew hRedeliver Sy
    hRoots hParent (hThird.mono hEnd) hGSTa ha hv₀ hw₀ hkR hcu hwin hk₂ hc₂ hslot hW htR htE
  rw [hSt₀] at hflw₀
  have hflb : M.head_height_floor (x.st i w) ≤ (M.chainStateOf S.C W).h :=
    le_trans ((floor_le_of_no_change_st M F) S A x R E w hi₀ hNo) hflw₀
  have hWb : W ∈ (x.st i w).tree := ((grows_of_le M F) x R E w hi₀).1 (by rw [← hSt₀]; exact hWw)
  have hinv := (lem11_node_invariant M F S A x R E i w hw).1
  have hinv₀ := (lem11_node_invariant M F S A x R E (x.stepBefore t₀) w hw₀').1
  have hmb := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X (x.st i w) hinv
  have hjb := (h_j_lt_h_max_st M F) S A x R E i w
  -- the justified block at `i`, at the height of `W`, is compatible with `W`
  have JW : hMax M S.C (x.st i w) = (x.st i w).justifiedHeight + 1 →
      (M.chainStateOf S.C W).h = (x.st i w).justifiedHeight →
      (x.st i w).justified.compatible W = true := by
    intro hmJ hWj
    have hj0 := (h_j_mono_st M F Fx) S A x R E hRoots tEnd w hi₀ hThird hi hw htRi
    by_cases hlt : (x.st (x.stepBefore t₀) w).justifiedHeight < (x.st i w).justifiedHeight
    · rw [(J_genesis_of_cache_passes_st M F Fx) S A x R E hRoots tEnd (x.stepBefore t₀) i
        (x.st i w).justifiedHeight w hThird hi₀ hi hw hNo hlt le_rfl (by rw [hmJ]) htRi, compatible_iff]
      exact Or.inl (genesis_ancestorEq W)
    have hjeq : (x.st (x.stepBefore t₀) w).justifiedHeight = (x.st i w).justifiedHeight := by
      unfold Height at *
      omega
    have hJJ := (J_eq_of_h_j_eq_st M F Fx) S A x R E hRoots tEnd (x.stepBefore t₀) i w w hThird hi₀E hi hw₀'
      hw hjeq (max_le htR₀ htRi)
    have hm₀ := (h_max_mono_st M F) S A x R E w hi₀
    have hj₀ := (h_j_lt_h_max_st M F) S A x R E (x.stepBefore t₀) w
    have hm₀eq : hMax M S.C (x.st (x.stepBefore t₀) w) = (x.st (x.stepBefore t₀) w).justifiedHeight + 1 := by
      unfold Height at *
      omega
    have hr₀ : M.get_fc_root (x.st (x.stepBefore t₀) w) = (x.st (x.stepBefore t₀) w).justified := by
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st (x.stepBefore t₀) w) hinv₀ with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exfalso
        rcases h with h | h
        · obtain ⟨-, -, hfl'⟩ :=
            (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X _ hinv₀ h
          rw [hfl'] at hflw₀
          unfold Height at *
          omega
        · exact h hm₀eq
    have hc := (root_compatible_of_viable_upTo M F U Fx) S A x R GST E hNet hSkew hRedeliver Sy hRoots
      hParent tEnd t₀ w u W a hGSTa ha hThird hw₀ hv₀ c c₂ kR k₂ hkR hcu hEnd hwin hk₂ hc₂ hslot hW hWw htR htE
    rw [hSt₀, hr₀, hJJ] at hc
    exact hc
  -- the finalized block at `i`
  have hF : (x.st i w).finalized.compatible W = true := by
    obtain ⟨D, hD, hFD⟩ := (finalizedFromChain_of_exec M F) S A x R E i w
    by_cases hlt : (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C W).h
    · rw [hFD, compatible_iff]
      exact Or.inl ((lem68_honest_past_finalized M F Fx) S A x R E hRoots i (x.stepBefore t₀) w w D W
        (hThird.mono (max_le hi hi₀E)) hw hw₀' hD (by rw [← hSt₀]; exact hWw) hlt (max_le htRi htR₀))
    push Not at hlt
    by_cases hf0 : (M.chainStateOf S.C D).h_F = 0
    · rw [hFD, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D hf0,
        compatible_iff]
      exact Or.inl (genesis_ancestorEq W)
    have hf1 : 1 ≤ (M.chainStateOf S.C D).h_F := Nat.one_le_iff_ne_zero.mpr hf0
    obtain ⟨-, -, hFDa, -⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 hf1
    have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1
    have hFwD : (x.st i w).finalized.AncestorEq D := by rw [hFD]; exact hFDa
    have hjD := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E i w D hD hFwD
    have hjeq : (x.st i w).justifiedHeight = (M.chainStateOf S.C D).h_F := by
      unfold Height at *
      omega
    have hFJ := (F_eq_J_of_height_st M F Fx) S A x R E hRoots tEnd i i w w D hThird hi hi hw hw hD
      hFD hf1 hjeq (max_le htRi htRi)
    rw [hFJ]
    exact JW (by unfold Height at *; omega) (by unfold Height at *; omega)
  refine ⟨hflb, hF, ?_⟩
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st i w) hinv with ⟨hrJ, hmJ, hcJ⟩ | ⟨hrF, -⟩
  · rw [hrJ]
    have hfl : M.head_height_floor (x.st i w) = (x.st i w).justifiedHeight := by
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st i w) hinv with ⟨hc, -, -⟩ | ⟨-, h⟩
      · rw [hcJ] at hc
        cases hc
      · rw [h, hmJ]
        rfl
    have hWh : (M.chainStateOf S.C W).h ≤ hMax M S.C (x.st i w) := le_hMax M hWb
    by_cases hWj : (M.chainStateOf S.C W).h = (x.st i w).justifiedHeight + 1
    · rw [compatible_iff]
      left
      have hFW := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd i i w w W hThird hi hi hw hw
        hWb (by unfold Height at *; omega) (max_le htRi htRi)
      by_contra hJW
      have hc := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X (x.st i w) hinv W hmJ hWb hFW
        (by rw [hWj, hmJ]) hJW
      rw [hcJ] at hc
      cases hc
    · exact JW hmJ (by rw [hfl] at hflb; unfold Height at *; omega)
  · rw [hrF]
    exact hF

/-- **`vote_frame_compatible` with `w`'s frame read at its step `i`** (rule R3). The hypotheses of
`vote_frame_compatible`, with `w` honest at `b` used for its ticks to `vt` and `vt + Δ`, and its frame read at a step
`i` at or after its last step before `vt + 2Δ`, at a real time at most `tEnd`, honest there, with no
`ForkChoiceChangeStep` from its last step before `vt + 2Δ` to before `i`. Then `vote` is `u`'s slot-`σ` vote for a block
`H_u`, and some block `W`, `H_u` or a descendant of it, held by `w` at its tick to `vt + Δ`, is such that at `i`: `w`'s
`head_height_floor` is at most `W`'s chain-state height, and `w`'s finalized block and fork-choice root are compatible
with `W`.

Why: `vote_frame_compatible`'s argument, ending in `frame_compatible_of_viable_st` from `vt + 2Δ` to `i`.

Restated: `u`'s no-change window `hNoU` ends at its own tick to `vt + 3Δ`
(`hkU3`, at a real time at most `tEnd`, `hEnd`) in place of the real time `vt + 3Δ`, and `u` is read at that
tick; `u`'s honesty at the real time `vt + 3Δ` (`hu`) and `hΔs` dropped; the delivery premises up to `tE`, at least
the clock value of that tick (`htE`), and the roots up to the real time `tR`.

The variables: as `vote_frame_compatible`, with `i` the step of `w` its frame is read at.

Roots name blocks until `tR`, at least `max (M.voteTime S.C σ + 3 * Δ S) b` and the real time of `i`.

Restated with the delivery premises up to `tE`, at least three delays after the vote time of slot `σ`: the
latest delivery its proof reads is due by then.


Read aloud: a validator with no fork-choice change has, at each of its later steps, its finalized block and fork-choice
root compatible with the viable block an honest vote is an ancestor of. -/
theorem vote_frame_compatible_st_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST : ℕ)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    (tEnd σ b : ℕ) (u w : V) (vote : GoldfishVote V)
    -- from `a` on, the network is synchronous and every validator outside the adversary set is awake
    -- through `tEnd`; `a` is early enough for the windows the proof reads
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ M.voteTime S.C σ)
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hb : b ≤ tEnd) (hbσ : M.voteTime S.C σ + 2 * Δ S ≤ b)
    -- `u`'s tick to `vt + 3Δ`, at a real time at most `tEnd`, and no change of `u` from its tick to `vt` to
    -- before that tick
    (hkU3 : x.lbl (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) = Event.tick u (M.voteTime S.C σ + 3 * Δ S))
    (hEnd : x.time (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) ≤ tEnd)
    (hNoU : ∀ j : ℕ, x.tickStep u (M.voteTime S.C σ) ≤ j →
      j < x.tickStep u (M.voteTime S.C σ + 3 * Δ S) → ¬ ForkChoiceChangeStep M S A x u j)
    (hw : w ∉ A.corruptedAtTime x b)
    -- `w` is read at its step `i`, honest there, at or after its last step before `vt + 2Δ`, with no
    -- `ForkChoiceChangeStep` from that step to before `i`
    (i : ℕ) (hi : x.time i ≤ tEnd) (hi₀ : x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ i) (hwi : w ∉ A.corrupted i)
    (hNoW : ∀ j : ℕ, x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ j → j < i → ¬ ForkChoiceChangeStep M S A x w j)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) ≤ tR) (htRi : x.time i ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : M.voteTime S.C σ + 3 * Δ S ≤ tE) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree, vote = GoldfishVote.mk u σ H_u.root ∧
      ∃ W : Block V, H_u.AncestorEq W ∧ W ∈ (x.tickInput w (M.voteTime S.C σ + Δ S)).tree ∧
        M.head_height_floor (x.st i w) ≤ (M.chainStateOf S.C W).h ∧
        (x.st i w).finalized.compatible W = true ∧
        (M.get_fc_root (x.st i w)).compatible W = true := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hAB : ΔClockAhead < Δ S ∧ ΔClockBehind < Δ S := ⟨by linarith, by linarith⟩
  obtain ⟨H_u, hHT, hvote, W, hWv, hHW⟩ := (honest_vote_ancestor_of_viable M F U) S A x R E σ u vote hSend
  refine ⟨H_u, hHT, hvote, W, hHW, ?_⟩
  -- `u`'s tick to `vt`, and its tick to `vt + 3Δ`
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hSend
    exact x.lbl_tickStep ⟨i, hi⟩
  have hkUt := E.tick_active _ u _ hkU
  have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := E.not_mem_corrupted_of_tick hkU
  have hk3R := (E.tick_active _ u _ hkU3).2.1
  push_cast at hk3R
  have hu3 : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) := E.not_mem_corrupted_of_tick hkU3
  have hle3 : x.tickStep u (M.voteTime S.C σ) ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) :=
    (tick_step_le_of_le M F) E hkU hkU3 (by omega)
  -- `u` is outside the adversary set at every step up to its tick to `vt + 3Δ`
  have huj : ∀ j : ℕ, j ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) → u ∉ A.corrupted j :=
    fun j hj => E.not_mem_corrupted_of_le hj hu3
  -- `W` stays a viable head of `u` at every step from its tick to `vt` up to its tick to `vt + 3Δ`
  have hviab : ∀ i : ℕ, x.tickStep u (M.voteTime S.C σ) ≤ i → i ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) →
      W ∈ (M.fg_to_ac (x.st i u)).viable_heads := fun i hki hi3 =>
    (viable_head_kept_steps M F Fx) S A x R E hRoots tEnd u W hThird
      hki (le_trans (htime hi3) hEnd) (le_trans (htime hi3) htR) (huj i hi3)
      hWv (fun j h1 h2 => hNoU j h1 (lt_of_lt_of_le h2 hi3))
  have hcomp : ∀ i : ℕ, x.tickStep u (M.voteTime S.C σ) ≤ i → i ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) →
      W ∈ (x.st i u).tree ∧ (x.st i u).finalized.AncestorEq W := by
    intro i hki hi3
    have h := hviab i hki hi3
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _
      (lem11_node_invariant M F S A x R E i u (huj i hi3)).1] at h
    exact ⟨h.1, h.2.1⟩
  obtain ⟨hWT, -⟩ := hcomp _ le_rfl hle3
  -- `W` is a viable head of `u` at its tick to `vt + 3Δ`
  have hW3 : W ∈ (M.fg_to_ac (x.st (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) u)).viable_heads :=
    hviab _ hle3 le_rfl
  -- the window start of the delivery kit, one delay or one sync delay before `vt + Δ`
  obtain ⟨a', ha'⟩ : ∃ a' : ℕ, a' = M.voteTime S.C σ + Δ S - max (Δ S) Δs := ⟨_, rfl⟩
  have haa' : a ≤ a' := by omega
  -- a step at a real time at most `vt + Δ` comes before `u`'s tick to `vt + 3Δ`
  have hbefore3 : ∀ j : ℕ, x.time j ≤ ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) →
      j ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) := by
    intro j hj
    by_contra hc
    push_neg at hc
    have h1 := htime hc.le
    push_cast at hj
    linarith
  -- `u`'s finalized block at its last step before `a'` is an ancestor of `W`
  have hFa : (x.st (x.stepBefore a') u).finalized.compatible W = true := by
    refine (compatible_iff _ _).2 (Or.inl ?_)
    rcases le_total (x.stepBefore a') (x.tickStep u (M.voteTime S.C σ)) with hle | hle
    · exact ancestorEq_trans ((F_ancestorEq_of_le M F) x R E u hle) (hcomp _ le_rfl hle3).2
    · refine (hcomp _ hle (hbefore3 _ ?_)).2
      have h := (time_stepBefore_le M) x R E a'
      exact le_trans h (by exact_mod_cast (show a' ≤ M.voteTime S.C σ + Δ S by omega))
  -- `u` is active for one sync delay from `a'`
  have hu₀ : u ∈ A.activeThroughout x a' (a' + Δs) := by
    refine Activity.mem_activeThroughout.2 (fun j h1 h2 => ?_)
    have hjk : j ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) :=
      hbefore3 j (le_trans h1 (by exact_mod_cast (show a' + Δs ≤ M.voteTime S.C σ + Δ S by omega)))
    have hj := huj j hjk
    exact Activity.mem_active.2 ⟨hAw j u (le_trans (htime hjk) hEnd)
      (le_trans (by exact_mod_cast haa') h2) hj, hj⟩
  -- `u` is active at every step from `a` up to its tick to `vt + 3Δ`
  have hwinU : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ x.tickStep u (M.voteTime S.C σ + 3 * Δ S) → u ∈ A.active i :=
    fun i h1 h2 => Activity.mem_active.2 ⟨hAw i u (le_trans (htime h2) hEnd)
      (le_trans h1 (htime (Nat.le_succ i))) (huj i h2), huj i h2⟩
  -- `w` is active from `a` to `b`, and ticks to `vt` and to `vt + Δ`
  have hwA : w ∈ A.activeThroughout x a b := (activeThroughout_nat_of_awake_from M F) R E hAw hw le_rfl hb
  have hv₀w : w ∈ A.activeThroughout x a (a + Δs) :=
    Activity.mem_activeThroughout_of_le le_rfl (by exact_mod_cast (show a + Δs ≤ b by omega)) hwA
  have haR : ((a : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hbR : ((M.voteTime S.C σ : ℕ) : ℝ) + 2 * Δ S ≤ (b : ℝ) := by exact_mod_cast hbσ
  obtain ⟨hk₂, -, -⟩ := (tickStep_spec M) x R E (t := M.voteTime S.C σ) (v := w) (by omega)
    (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) hwA)
  obtain ⟨hkR, -, hkR2⟩ := (tickStep_spec M) x R E (t := M.voteTime S.C σ + Δ S) (v := w) (by omega)
    (Activity.mem_activeThroughout_of_le (by push_cast; linarith) (by push_cast; linarith) hwA)
  have hwin : ∀ i : ℕ, (a' : ℝ) ≤ x.time i → i ≤ x.tickStep w (M.voteTime S.C σ + Δ S) → w ∈ A.active i := by
    intro i h1 h2
    have hti := htime h2
    exact Activity.mem_activeThroughout.1 hwA i (by push_cast at hkR2; linarith)
      (le_trans (by exact_mod_cast haa') (le_trans h1 (htime (Nat.le_succ i))))
  -- `w`'s tick to `vt + Δ` is before `vt + 2Δ`
  have h2 : 1 ≤ M.voteTime S.C σ + 2 * Δ S := by omega
  obtain ⟨-, hs2'⟩ := (stepBefore_time M) x R E h2
  have hkR2s : x.tickStep w (M.voteTime S.C σ + Δ S) ≤ x.stepBefore (M.voteTime S.C σ + 2 * Δ S) := by
    by_contra hc
    have h := htime (show x.stepBefore (M.voteTime S.C σ + 2 * Δ S) + 1 ≤ x.tickStep w (M.voteTime S.C σ + Δ S) by omega)
    push_cast at hs2' hkR2
    linarith
  have hw₂ : w ∉ A.corruptedAtTime x ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) :=
    (not_mem_corruptedAtTime_of_le M) x R E hbσ hw
  -- the slots: `W`'s, and those of the blocks `w` holds before `vt + 2Δ`, start no later than `vt`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  obtain ⟨-, -, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  have hslotv : S.C.slot ((M.voteTime S.C σ : ℕ) : Int) = σ :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hslot : ∀ Y ∈ (x.stateBefore (M.voteTime S.C σ + 2 * Δ S) w).tree,
      M.slotStart S.C Y.slot ≤ M.voteTime S.C σ := by
    intro Y hY
    have hi2 := (time_stepBefore_le M) x R E (M.voteTime S.C σ + 2 * Δ S)
    have hwS2 : w ∉ A.corrupted (x.stepBefore (M.voteTime S.C σ + 2 * Δ S)) :=
      (not_mem_corrupted_of_le_time M) x R E hw₂ (by exact_mod_cast hi2)
    have h := (slot_le_clockValue_of_mem_tree M F) R E hwS2 hY
    have hcv := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore (M.voteTime S.C σ + 2 * Δ S)) w
    have hcvR : (x.clockValue (x.stepBefore (M.voteTime S.C σ + 2 * Δ S)) w : ℝ) <
        ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) := by
      push_cast at hi2 ⊢
      refine lt_of_le_of_lt hcv (max_lt (by linarith) ?_)
      linarith
    -- the clock value is before the start of slot `σ + 1`, so in a slot at most `σ`
    have hcvN : x.clockValue (x.stepBefore (M.voteTime S.C σ + 2 * Δ S)) w < M.slotStart S.C (σ + 1) := by
      have := Nat.cast_lt.1 hcvR
      have hvtσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
      omega
    have hYs : Y.slot ≤ σ := by
      have hlt := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_lt_slotStart M.toSlotLayout F.sched) S hcvN
      rw [hsl] at hlt
      exact Nat.lt_succ_iff.mp (h.trans_lt hlt)
    exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hYs)
      (by omega)
  -- `w`'s finalized block before `vt + 2Δ`, and so at its tick to `vt + Δ`, is compatible with `W`
  have hFc := (finalized_compatible_of_viable_upTo M F U Fx) S A x R GST E hNet hSkew hRedeliver Sy hRoots
    hParent tEnd (M.voteTime S.C σ + 2 * Δ S) w u W a hGSTa (by omega) hThird hw₂ hv₀w
    (M.voteTime S.C σ + 3 * Δ S) (M.voteTime S.C σ) (x.tickStep u (M.voteTime S.C σ + 3 * Δ S))
    (x.tickStep u (M.voteTime S.C σ)) hkU3 (by omega) hEnd hwinU hkU (by omega) hslot hW3 htR (by omega)
  have hFw : (x.st (x.tickStep w (M.voteTime S.C σ + Δ S)) w).finalized.compatible W = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E w hkR2s) hFc
  -- `W`'s slot starts no later than `vt`
  have hWs : W.slot ≤ σ := by
    have h := (slot_le_clockValue_of_mem_tree M F) R E huk hWT
    rw [← hslotv]
    exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
      (by exact_mod_cast E.clockValue_le_of_set huk (Or.inl hkU)))
  have hDc₂ : M.slotStart S.C W.slot ≤ M.voteTime S.C σ :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hWs)
      (by omega)
  -- `W` reaches `w` by its tick to `vt + Δ`
  have hWw : W ∈ (x.tickInput w (M.voteTime S.C σ + Δ S)).tree := by
    by_cases hg : W = Block.genesis
    · rw [hg]
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
    have hRootsR : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C σ + Δ S))) :=
      (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (by
          push_cast at hkR2
          linarith) hRoots
    exact (block_at_tick_of_held_tick M F U) S A x R GST (M.voteTime S.C σ + Δ S) (M.voteTime S.C σ)
      (x.tickStep u (M.voteTime S.C σ)) a' (M.voteTime S.C σ + Δ S) (M.voteTime S.C σ)
      (x.tickStep w (M.voteTime S.C σ + Δ S)) (x.tickStep w (M.voteTime S.C σ)) u w W
      (E.mono (show M.voteTime S.C σ + Δ S ≤ tE by omega)) hNet hSkew hRedeliver
      (Sy.mono (show M.voteTime S.C σ + Δ S ≤ tE by omega)) hRootsR hParent (by omega) (by omega) le_rfl le_rfl hu₀ hkU hWT hFa hg hkR hwin hk₂
      le_rfl hDc₂ hFw
  have hWw2 : W ∈ (x.stateBefore (M.voteTime S.C σ + 2 * Δ S) w).tree :=
    (mem_T_mono M F) x R E w hkR2s hWw
  exact ⟨hWw, (frame_compatible_of_viable_st_upTo M F U Fx) S A x R GST E hNet hSkew hRedeliver Sy hRoots
    hParent tEnd (M.voteTime S.C σ + 2 * Δ S) i w u W a hGSTa (by omega) hThird hi hi₀
    hw₂ hwi hv₀w (M.voteTime S.C σ + 3 * Δ S) (M.voteTime S.C σ) (x.tickStep u (M.voteTime S.C σ + 3 * Δ S))
    (x.tickStep u (M.voteTime S.C σ)) hkU3 (by omega) hEnd hwinU hkU (by omega) hslot hW3 hWw2 hNoW htR htRi (by omega)⟩

/-- `B6Ctx M S Sched x GST tGAT tAwakeEnd r s`: B6's hypotheses that its proof reads, and the
negation of its conclusion: no validator outside the adversary set has a `ForkChoiceChangeStep` at a
step from the validator's own tick to the vote time of slot `s − k − 1` to before the support cutoff of slot `s`.

Roots name blocks until `M.supportCutoff S.C s`: the window's end; every reader of the bundle
compares blocks held up to it.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of its roots `hRoots`,
the window's end; every reader of the bundle reads deliveries due by then.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: B6's hypotheses that its proof reads hold, and no validator outside the adversary set
has a fork-choice change from its own tick to the vote time of slot `s − k − 1` to before the support cutoff of slot
`s`, with the delivery premises up to the support cutoff of slot `s`. -/
structure B6CtxUpTo (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (GST tGAT tAwakeEnd r s : ℕ) (Δs : ℕ) (release : (NamedObject V) → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (ΔNet : ℕ) : Prop where
  /-- Blocks and Goldfish votes due by the bound are delivered within `Δ` after `GST`. -/
  E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST release acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)
  /-- The network delay and the two clock bounds fit in the delay `Δ S`. -/
  hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- The two clock bounds together are less than one delay `Δ S`. -/
  hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S
  /-- A re-delivery after the receiver's clock reaches an object's release clock value, plus both clock bounds, fits in one delay `Δ S`. -/
  hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- What an honest validator active at a time `t` would serve at `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST`, when that is at most the bound. -/
  Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject release ΔRedeliver Δs GST (M.supportCutoff S.C s)
  /-- The sync delay is at most the protocol's slow window less three delays. -/
  hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k
  /-- Roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
. -/
  hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
    RootsNameBlocksUntil M A x (x.time k)
  hParent : ParentHeldAtDelivery M x
  hGST : GST ≤ tGAT
  hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd
  hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
    v ∉ A.corrupted i → v ∈ A.awake i
  /-- At every slot of the phase, every validator honest at the slot's update is an honest active validator and an
  updater of the slot. -/
  hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
    ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
      v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s
  hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd
  hEnd : aR M S r ≤ tAwakeEnd
  hk : S.C.k + 1 ≤ s
  hBefore : M.supportCutoff S.C s ≤ aR M S r
  /-- Every validator's tick to a clock value at most the support cutoff of slot `s` is in the phase
. -/
  hTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
    x.time k ≤ (tAwakeEnd : ℝ)
  hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (s - S.C.k)
  /-- No change at a step from a validator's own tick to the window's start value to before one of its own ticks
  to a clock value at most the support cutoff of slot `s`. -/
  hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (s - S.C.k - 1)) → k ≤ j →
    x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s → j < k' →
    w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j

namespace B6CtxUpTo
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r s : ℕ}

/-- The window's last support cutoff is in the phase.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the window's last support cutoff is at most `tAwakeEnd`. -/
theorem tEnd
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) : M.supportCutoff S.C s ≤ tAwakeEnd :=
  le_trans C.hBefore C.hEnd

/-- The window's slots start after `tGAT`.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle.

Read aloud: the window's first slot starts at `tGAT` or later. -/
theorem tGAT_le (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) :
    tGAT ≤ M.slotStart S.C (s - S.C.k - 1) := by
  have h := C.hAnchor
  have hk := C.hk
  have hΔ := one_le_Δ S
  have e : M.slotStart S.C (s - S.C.k - 1 + 1) = M.slotStart S.C (s - S.C.k - 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  rw [show s - S.C.k - 1 + 1 = s - S.C.k by omega] at e
  have h4 : 4 * Δ S ≤ 4 * Δ S * (S.C.k + 2) := Nat.le_mul_of_pos_right _ (by omega)
  rw [anchorCW_eq] at h
  omega

/-- A slot of the window has its committee premise and its duty window in the phase.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle.

Read aloud: a slot of the window has its committee premise and its duty window from one delay after
`tGAT`. -/
theorem slot_facts (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) :
    anchorCW S tGAT ≤ M.slotStart S.C (σ + 1) ∧ tGAT + Δ S ≤ M.dutyWindowStart S.C σ := by
  have h1 : anchorCW S tGAT ≤ M.slotStart S.C (σ + 1) :=
    le_trans C.hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  exact ⟨h1, (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT σ h1⟩

/-- The window's slots start one sync delay and four delays after `tGAT` (`tGAT_sync_of_anchor`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle; `σ`: the slot.

Read aloud: every slot of the window starts one sync delay and four delays after `tGAT`. -/
theorem syncStart (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) : tGAT + max (Δ S) Δs + 4 * Δ S ≤ M.slotStart S.C σ :=
  (tGAT_sync_of_anchor M F U) C.hAnchor C.hk C.E.ahead_nonneg C.E.behind_nonneg C.hΔs hσ

/-- A validator honest at `b` in the phase is awake and honest from any time from `tGAT` on to
`b`.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a validator honest at `b` in the phase is awake and honest at every time from `t₁` to
`b`. -/
theorem awakeHonest (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {Δs : ℕ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (w : V) {t₁ b : ℕ}
    (h1 : tGAT ≤ t₁) (hb : b ≤ tAwakeEnd) (hw : w ∉ A.corruptedAtTime x b) :
    w ∈ A.activeThroughout x t₁ b :=
  (mem_activeThroughout_of_hAwake_honest_at M F) R E C.hAwake h1 hb hw

/-- A validator honest at `b` has no fork-choice change at a step from its own tick to the window's
start clock value (the vote time of slot `s − k − 1`) to before `b`, when `b` is at most the support
cutoff of slot `s`.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle; `w`: the validator; `k`: the step of `w`'s tick to
  the vote time of slot `s − k − 1`; `b`: the time at which `w` is honest.

Read aloud: a validator honest at `b` has no fork-choice change at a step from its tick to the
window's start to before `b`.
-/
theorem noChange (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {Δs : ℕ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (w : V) {k k' c : ℕ}
    (hk : x.lbl k = Event.tick w (M.voteTime S.C (s - S.C.k - 1)))
    (hk' : x.lbl k' = Event.tick w c) (hc : c ≤ M.supportCutoff S.C s) :
    ∀ j : ℕ, k ≤ j → j < k' → ¬ ForkChoiceChangeStep M S A x w j :=
  fun j hkj hjk => C.hNo w j k k' c hk hkj hk' hc hjk
    (E.not_mem_corrupted_of_le hjk.le ((Activity.mem_active.1 (E.tick_active k' w c hk').1).2))


/-- **`noChange` before a real time** (the re-check's theorem 9, F-RC56-2). A validator with a tick `k'` to a
clock value at most the support cutoff of slot `s`, at a real time at least `b`, has no fork-choice change at
a step from its own tick to the window's start value to before the real time `b`.

Why: a step at a real time less than `b` comes before `k'` (`lt_of_time_lt`); `noChange`.

The variables:
- `M`: the model; `F`: its facts; `R`: the run's facts; `C`: the bundle; `w`: the validator; `k`: the step of
  `w`'s tick to the window's start; `k'`, `c`: the step and the clock value of a later tick of `w`; `b`: the
  real time.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.


Read aloud: a validator that ticks, at or after the real time `b`, to a clock value at most the support cutoff of
slot `s` has no fork-choice change from its tick to the window's start to before `b`. -/
theorem noChange_before {Δs : ℕ} {release ΔRedeliver} (R : RunFacts M S x) {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (w : V) {k k' c : ℕ}
    (hk : x.lbl k = Event.tick w (M.voteTime S.C (s - S.C.k - 1)))
    (hk' : x.lbl k' = Event.tick w c) (hc : c ≤ M.supportCutoff S.C s) {b : ℝ} (hb : b ≤ x.time k') :
    ∀ j : ℕ, k ≤ j → x.time j < b → ¬ ForkChoiceChangeStep M S A x w j :=
  fun j hkj hjb => C.noChange M F R C.E w hk hk' hc j hkj ((lt_of_time_lt M) x R (lt_of_lt_of_le hjb hb))

/-- At a slot `σ` of the window with `σ + 1 ≤ s`, the members of slot `σ` are honest active at
`σ`, and they hold more than half of the committee of slot `σ`.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle.

Read aloud: the members of a window slot are honest active and hold more than half of its committee.
-/
theorem members {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (R : RunFacts M S x) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 1 ≤ s) :
    roundMembers M S A x (σ + 1) ⊆ honestActiveAt M S A x σ ∧
      (S.P.committee σ).card < 2 * (S.P.committee σ ∩ roundMembers M S A x (σ + 1)).card := by
  obtain ⟨hA, hdw⟩ := (C.slot_facts M F U) hσ
  have hsub := ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_subset_honestActiveAt M F U) S A tGAT tAwakeEnd σ R E C.hActive
    (by omega) (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hσs) (C.tEnd M F))).1
  exact ⟨hsub, (GoldilocksCorrectness.Record.Proofs.Executions.committee_majority_of_committeeSleepiness M F) S A x (anchorCW S tGAT) σ
    C.hCommittees hA (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hσs) (C.tEnd M F))⟩

/-- **A confirmation saved by a member at a window slot has an honest supporter.** At a slot
`σ` of the window with `σ + 2 ≤ s`, when the confirmation read on the state of a member `v` of
slot `σ + 1` right after the support cutoff of slot `σ + 1` is `X`, some honest validator `u`,
honest active at `σ`, put on the wire at the vote time of slot `σ` its vote for a block it held,
`X` or a descendant of `X` (`honest_supporter_of_saved`).

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `C`: the bundle.

Read aloud: a confirmation a member saved at a window slot has an honest supporter. -/
theorem supporter_saved (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 2 ≤ s) (v : V)
    (hv : v ∈ roundMembers M S A x (σ + 1)) (X : Block V)
    (hX : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X) :
    ∃ u ∈ honestActiveAt M S A x σ, ∃ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) ∧
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree, vote = GoldfishVote.mk u σ H_u.root ∧
        X.AncestorEq H_u := by
  have hΔ := one_le_Δ S
  obtain ⟨hsub, hMaj⟩ := (C.members M F E U R) hσ (by omega)
  obtain ⟨-, hdw⟩ := (C.slot_facts M F U) hσ
  have hcE : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) (C.tEnd M F)
  have hvh : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) := (Finset.mem_sdiff.1 hv).2
  have hGSTσ : GST + max (Δ S) Δs ≤ M.supportCutoff S.C σ := by
    have := (C.syncStart M F U) hσ
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
    have := C.hGST
    omega
  have hvU : v ∈ updaterAt M S A x σ := (C.hActive σ (by omega) hcE v hvh).2
  have hkV : x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) = Event.tick v (M.supportCutoff S.C (σ + 1)) := by
    classical
    have h := hvU
    unfold updaterAt Activity.activeThroughoutToTick at h
    obtain ⟨k', hk', -⟩ := (Finset.mem_filter.1 h).2
    exact x.lbl_tickStep ⟨k', hk'⟩
  have hcσS : M.supportCutoff S.C σ ≤ M.supportCutoff S.C s :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  obtain ⟨u, hu, vote, hsend, H_u, hHT, hvote, hXH⟩ := (honest_supporter_of_saved_upTo M F U) S A x R GST σ v
    (S.P.committee σ ∩ roundMembers M S A x (σ + 1)) (C.E.mono hcσS) C.hNet C.hSkew C.hRedeliver (C.Sy.mono hcσS) C.hΔs
    (C.hRoots _ v _ hkV ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)))
    ((GoldilocksCorrectness.Record.Statements.Executions.votesCastByOwner_of_unforgeability M F) S A x R E) hGSTσ
    (fun u hu => ⟨hsub (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
    ((counting_of_committee_majority_st M F) S A x R E σ (x.tickStep v (M.supportCutoff S.C (σ + 1)))
      (roundMembers M S A x (σ + 1)) v hMaj).2.1
    hvU X hX
  exact ⟨u, hsub (Finset.mem_inter.1 hu).2, vote, hsend, H_u, hHT, hvote, hXH⟩

/-- **A frame with no change is compatible with the viable block of an honest voter of a window
slot.** At a slot `σ` of the window with `σ + 2 ≤ s`, for an honest active voter `u` of slot `σ`
whose tick put `vote` on the wire, and `w` honest at `b`, from two delays after the vote time of
slot `σ` to the support cutoff of slot `s`: `vote_frame_compatible`, with `W` held by `w` at its tick
to one delay after the vote time.

Why: `u` and `w` tick to the window's start (both honest after it, awake from `tGAT`), so the bundle's
`hNo` gives `u` no change from its tick to the vote time of slot `σ` (a later clock value,
`tick_step_le_of_le`) and `w` none from two delays after that vote time (`tick_le_of_time_ge`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.


Read aloud: a validator with no fork-choice change has its finalized block and fork-choice root
compatible with the viable block of an honest voter of a window slot. -/
theorem frame (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 2 ≤ s) (u : V) (hu : u ∈ honestActiveAt M S A x σ)
    (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (w : V) (b : ℕ) (hbσ : M.voteTime S.C σ + 2 * Δ S ≤ b) (hb : b ≤ M.supportCutoff S.C s)
    (hw : w ∉ A.corruptedAtTime x b)
    -- `w` ticks, at or after the real time `b`, to a clock value at most the support cutoff of slot `s`
    (kw cw : ℕ) (hkw : x.lbl kw = Event.tick w cw) (hcw : cw ≤ M.supportCutoff S.C s) (hbkw : (b : ℝ) ≤ x.time kw) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree, vote = GoldfishVote.mk u σ H_u.root ∧
      ∃ W : Block V, H_u.AncestorEq W ∧ W ∈ (x.tickInput w (M.voteTime S.C σ + Δ S)).tree ∧
        M.head_height_floor (x.stateBefore b w) ≤ (M.chainStateOf S.C W).h ∧
        (x.stateBefore b w).finalized.compatible W = true ∧
        (M.get_fc_root (x.stateBefore b w)).compatible W = true := by
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hmx1 := le_max_left (Δ S) Δs
  have hsync := (C.syncStart M F U) hσ
  have hsync0 := (C.syncStart M F U) (le_refl (s - S.C.k - 1))
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hvt0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
    (s - S.C.k - 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hσ
  obtain ⟨-, hc1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨-, -, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  have hcut1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show σ + 1 ≤ s by omega)
  have hEnd' := C.tEnd M F
  -- `u` is honest at the support cutoff of slot `σ + 1`, so at `vt + 3Δ`
  have hu1 : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) := by
    unfold honestActiveAt at hu
    exact fun h => (Finset.mem_sdiff.1 hu).2 (Finset.mem_union_left _ h)
  have hu3 : u ∉ A.corruptedAtTime x ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) :=
    (not_mem_corruptedAtTime_of_le M) x R C.E (by omega) hu1
  -- a validator honest at `e`, at least one delay after the window's start, ticks to that start
  have htick0 : ∀ (v : V) (e : ℕ), M.voteTime S.C (s - S.C.k - 1) + Δ S ≤ e → e ≤ tAwakeEnd →
      v ∉ A.corruptedAtTime x e →
      x.lbl (x.tickStep v (M.voteTime S.C (s - S.C.k - 1))) = Event.tick v (M.voteTime S.C (s - S.C.k - 1)) := by
    intro v e he1 he2 hv
    have h := (C.awakeHonest M F) R C.E v le_rfl he2 hv
    have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (s - S.C.k - 1) by omega)
    have h2R : ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ (e : ℝ) := by exact_mod_cast he1
    exact ((tickStep_spec M) x R C.E (t := M.voteTime S.C (s - S.C.k - 1)) (v := v) (by omega)
      (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) h)).1
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hSend
    exact x.lbl_tickStep ⟨i, hi⟩
  have hk0u := htick0 u _ (by omega) (by omega) hu3
  have hk0w := htick0 w b (by omega) (by omega) hw
  have hle : x.tickStep u (M.voteTime S.C (s - S.C.k - 1)) ≤ x.tickStep u (M.voteTime S.C σ) :=
    (tick_step_le_of_le M F) C.E hk0u hkU (by omega)
  -- `u` ticks to three delays after the vote time of slot `σ`, a clock value at most the support cutoff of slot `s`
  have hkU3 := (tickStep_spec M) x R C.E (t := M.voteTime S.C σ + 3 * Δ S) (v := u) (by omega)
    (by
      have h := (C.awakeHonest M F) R C.E u (t₁ := tGAT) (b := M.supportCutoff S.C (σ + 1)) le_rfl
        (le_trans hcut1 hEnd') hu1
      have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) := by
        exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C σ + 3 * Δ S by omega)
      have h2R : ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C σ + 3 * Δ S + Δ S ≤ M.supportCutoff S.C (σ + 1) by omega)
      exact Activity.mem_activeThroughout_of_le (by linarith) (by linarith) h)
  have hcU3 : M.voteTime S.C σ + 3 * Δ S ≤ M.supportCutoff S.C s := by omega
  have hu3k : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) := C.E.not_mem_corrupted_of_tick hkU3.1
  -- roots up to the later of `u`'s tick to `vt + 3Δ` and `b`, from the two ticks (the bundle's per-tick roots)
  have hRootsM : RootsNameBlocksUntil M A x (max (x.time (x.tickStep u (M.voteTime S.C σ + 3 * Δ S))) (b : ℝ)) := by
    rcases le_total (x.time (x.tickStep u (M.voteTime S.C σ + 3 * Δ S))) (b : ℝ) with h | h
    · rw [max_eq_right h]
      exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hbkw (C.hRoots kw w cw hkw hcw)
    · rw [max_eq_left h]
      exact C.hRoots _ u _ hkU3.1 hcU3
  refine (vote_frame_compatible_upTo M F U Fx) S A x R GST C.E C.hNet C.hSkew C.hRedeliver C.Sy hRootsM
    C.hParent tAwakeEnd σ b u w vote tGAT C.hGST (by omega) C.hAwake C.hThird (by omega) hbσ
    hkU3.1 (C.hTick _ u _ hkU3.1 hcU3) ?_ hw ?_ hSend (le_max_left _ _) (le_max_right _ _) hcU3
  · intro j hj hj3
    exact C.hNo u j _ _ _ hk0u (le_trans hle hj) hkU3.1 hcU3 hj3 (C.E.not_mem_corrupted_of_le hj3.le hu3k)
  · intro j hj hjb
    have hk0j := (tick_le_of_time_ge M F) R C.E (d := Δ S) (by linarith) hk0w
      (le_trans (by exact_mod_cast (show M.voteTime S.C (s - S.C.k - 1) + Δ S ≤ M.voteTime S.C σ + 2 * Δ S by omega)) hj)
    exact (C.noChange_before M F R) w hk0w hkw hcw hbkw j hk0j hjb

/-- **`frame` with `w`'s frame read at its step `i`** (rule R3). At a slot `σ` of the window with `σ + 2 ≤ s`, for an
honest active voter `u` of slot `σ` whose tick put `vote` on the wire, and `w` honest at `b`, from two delays after the
vote time of slot `σ` to the support cutoff of slot `s`: `vote_frame_compatible_st` at a step `i` of `w`, at or after
its last step before `vt + 2Δ`, honest there, with no `ForkChoiceChangeStep` from that step to before `i`, and roots
naming blocks up to the real time of `i`.

Why: `frame`'s argument; `u`'s steps from its tick to the vote time of slot `σ` are covered by the bundle's `hNo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle; `i`: the step of `w`; `tR`: the bound of the roots.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.


Read aloud: a validator with no fork-choice change up to its step `i` has there its finalized block and fork-choice
root compatible with the viable block of an honest voter of a window slot. -/
theorem frame_st (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hσ : s - S.C.k - 1 ≤ σ) (hσs : σ + 2 ≤ s) (u : V) (hu : u ∈ honestActiveAt M S A x σ)
    (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (w : V) (b : ℕ) (hbσ : M.voteTime S.C σ + 2 * Δ S ≤ b) (hb : b ≤ M.supportCutoff S.C s)
    (hw : w ∉ A.corruptedAtTime x b)
    -- `w` is read at its step `i`: honest there, at or after its last step before `vt + 2Δ`, with no
    -- `ForkChoiceChangeStep` from that step to before `i`, and roots name blocks up to `tR`, at least the real time
    -- of `i`
    (i : ℕ) (hi : x.time i ≤ tAwakeEnd) (hi₀ : x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ i)
    (hwi : w ∉ A.corrupted i)
    (hNoW : ∀ j : ℕ, x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ j → j < i → ¬ ForkChoiceChangeStep M S A x w j)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR) (htRi : x.time i ≤ tR) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree, vote = GoldfishVote.mk u σ H_u.root ∧
      ∃ W : Block V, H_u.AncestorEq W ∧ W ∈ (x.tickInput w (M.voteTime S.C σ + Δ S)).tree ∧
        M.head_height_floor (x.st i w) ≤ (M.chainStateOf S.C W).h ∧
        (x.st i w).finalized.compatible W = true ∧
        (M.get_fc_root (x.st i w)).compatible W = true := by
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hmx1 := le_max_left (Δ S) Δs
  have hsync := (C.syncStart M F U) hσ
  have hsync0 := (C.syncStart M F U) (le_refl (s - S.C.k - 1))
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hvt0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
    (s - S.C.k - 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hσ
  obtain ⟨-, hc1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨-, -, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  have hcut1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show σ + 1 ≤ s by omega)
  have hEnd' := C.tEnd M F
  -- `u` is honest at the support cutoff of slot `σ + 1`, so at `vt + 3Δ`
  have hu1 : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) := by
    unfold honestActiveAt at hu
    exact fun h => (Finset.mem_sdiff.1 hu).2 (Finset.mem_union_left _ h)
  have hu3 : u ∉ A.corruptedAtTime x ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) :=
    (not_mem_corruptedAtTime_of_le M) x R C.E (by omega) hu1
  -- a validator honest at `e`, at least one delay after the window's start, ticks to that start
  have htick0 : ∀ (v : V) (e : ℕ), M.voteTime S.C (s - S.C.k - 1) + Δ S ≤ e → e ≤ tAwakeEnd →
      v ∉ A.corruptedAtTime x e →
      x.lbl (x.tickStep v (M.voteTime S.C (s - S.C.k - 1))) = Event.tick v (M.voteTime S.C (s - S.C.k - 1)) := by
    intro v e he1 he2 hv
    have h := (C.awakeHonest M F) R C.E v le_rfl he2 hv
    have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (s - S.C.k - 1) by omega)
    have h2R : ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ (e : ℝ) := by exact_mod_cast he1
    exact ((tickStep_spec M) x R C.E (t := M.voteTime S.C (s - S.C.k - 1)) (v := v) (by omega)
      (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) h)).1
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hSend
    exact x.lbl_tickStep ⟨i, hi⟩
  have hk0u := htick0 u _ (by omega) (by omega) hu3
  have hle : x.tickStep u (M.voteTime S.C (s - S.C.k - 1)) ≤ x.tickStep u (M.voteTime S.C σ) :=
    (tick_step_le_of_le M F) C.E hk0u hkU (by omega)
  -- `u` ticks to three delays after the vote time of slot `σ`, a clock value at most the support cutoff of slot `s`
  have hkU3 := (tickStep_spec M) x R C.E (t := M.voteTime S.C σ + 3 * Δ S) (v := u) (by omega)
    (by
      have h := (C.awakeHonest M F) R C.E u (t₁ := tGAT) (b := M.supportCutoff S.C (σ + 1)) le_rfl
        (le_trans hcut1 hEnd') hu1
      have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) := by
        exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C σ + 3 * Δ S by omega)
      have h2R : ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C σ + 3 * Δ S + Δ S ≤ M.supportCutoff S.C (σ + 1) by omega)
      exact Activity.mem_activeThroughout_of_le (by linarith) (by linarith) h)
  have hcU3 : M.voteTime S.C σ + 3 * Δ S ≤ M.supportCutoff S.C s := by omega
  have hu3k : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ + 3 * Δ S)) := C.E.not_mem_corrupted_of_tick hkU3.1
  -- roots up to the later of `u`'s tick to `vt + 3Δ` and `tR`
  have hRootsM : RootsNameBlocksUntil M A x (max (x.time (x.tickStep u (M.voteTime S.C σ + 3 * Δ S))) tR) := by
    rcases le_total (x.time (x.tickStep u (M.voteTime S.C σ + 3 * Δ S))) tR with h | h
    · rw [max_eq_right h]
      exact hRoots
    · rw [max_eq_left h]
      exact C.hRoots _ u _ hkU3.1 hcU3
  refine (vote_frame_compatible_st_upTo M F U Fx) S A x R GST C.E C.hNet C.hSkew C.hRedeliver C.Sy hRootsM
    C.hParent tAwakeEnd σ b u w vote tGAT C.hGST (by omega) C.hAwake C.hThird (by omega) hbσ
    hkU3.1 (C.hTick _ u _ hkU3.1 hcU3) ?_ hw i hi hi₀ hwi hNoW hSend (le_max_left _ _)
    (le_trans htRi (le_max_right _ _)) (by omega)
  intro j hj hj3
  exact C.hNo u j _ _ _ hk0u (le_trans hle hj) hkU3.1 hcU3 hj3 (C.E.not_mem_corrupted_of_le hj3.le hu3k)

/-- **Clause 1 of `FrontWindowStable`, given `w`'s window up to its tick to the support cutoff of slot `s₁ + 2`.**
`stepFrame`'s conclusion, under three more hypotheses on `w` that the bundle gives only when that tick is before the
real time `M.supportCutoff S.C s`: roots name blocks up to `tR`, at least the real time of `w`'s tick to the support
cutoff of slot `s₁ + 2`; that tick is at a real time at most `tAwakeEnd`; and `w` has no `ForkChoiceChangeStep` at a step from its tick to the window's start value
(the vote time of slot `s − k − 1`) to before its tick to the support cutoff of slot `s₁ + 2`.

Why: `X` has an honest supporter `u` (`supporter_saved`), whose vote is an ancestor of a viable block `W` of `u` that
reaches `w` by its tick to one delay after the vote time of slot `σ` (`frame_st`). At `w`'s tick to the vote time of
slot `s₁ + 1` (inside the bundle's window), `w`'s root is compatible with `W`, so with `X`; when the root is `X` or an
ancestor of it, `W` is a viable head of `w` and in its voter tree (`mem_voter_tree_st`: `W` entered `w`'s tree at a clock
value at most one delay after the vote time of slot `σ`, before the view freeze of slot `s₁`). At `w`'s tick to the
support cutoff of slot `s₁ + 2`, `w`'s finalized block is compatible with `W`, so with `X` (`frame_st`, from the two
hypotheses).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle; `tR`: the bound of the roots.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.


Read aloud: clause 1 of `FrontWindowStable` holds for a member `w` of slot `s₁ + 1` whose fork choice does not change
up to its tick to the support cutoff of slot `s₁ + 2`, with roots naming blocks up to that tick. -/
theorem stepFrame_of_noChange (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s₁ σ : ℕ}
    (h1 : s - S.C.k - 1 ≤ σ) (h2 : σ ≤ s₁) (h3 : s₁ + 2 ≤ s) (v : V)
    (hv : v ∈ Hon M S A x (σ + 1)) (X : Block V)
    (hX : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X)
    (w : V) (hw : w ∈ Hon M S A x (s₁ + 1))
    -- roots name blocks up to `tR`, at least the real time of `w`'s tick to the support cutoff of slot `s₁ + 2`
    {tR : ℝ} (hRootsT : RootsNameBlocksUntil M A x tR)
    (htRT : x.time (x.tickStep w (M.supportCutoff S.C (s₁ + 2))) ≤ tR)
    -- that tick is in the phase
    (htE : x.time (x.tickStep w (M.supportCutoff S.C (s₁ + 2))) ≤ (tAwakeEnd : ℝ))
    -- `w` has no `ForkChoiceChangeStep` from its tick to the window's start value to before its tick to the support
    -- cutoff of slot `s₁ + 2`
    (hNoT : ∀ j : ℕ, x.tickStep w (M.voteTime S.C (s - S.C.k - 1)) ≤ j →
      j < x.tickStep w (M.supportCutoff S.C (s₁ + 2)) → w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j) :
    StepFrameAt M S A x X s₁ w := by
  have hk2 := S.C.k_ge_two
  have hkk := C.hk
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hcE : M.supportCutoff S.C s ≤ tAwakeEnd := C.tEnd M F
  obtain ⟨hvtσ, hcσ, -, hsσ, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨-, -, -, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₁
  obtain ⟨hvt1, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₁ + 1)
  obtain ⟨hvt2, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₁ + 2)
  rw [show s₁ + 1 + 1 = s₁ + 2 from rfl] at hs1
  have hssσ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h2
  have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h1
  have hvt0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s - S.C.k - 1)
  have hsync0 := (C.syncStart M F U) (le_refl (s - S.C.k - 1))
  have hmx1 := le_max_left (Δ S) Δs
  have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h3
  have hcE2 : M.supportCutoff S.C (s₁ + 2) ≤ tAwakeEnd := le_trans hcs hcE
  -- the supporter `u` of `X`
  have hv' : v ∈ roundMembers M S A x (σ + 1) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A (σ + 1) (σ + 2) tAwakeEnd R C.E
      (Nat.le_succ _) (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (by omega)) hcE)).1 hv
  obtain ⟨u, huA, vote, hsend, H_u, hHT, hvote, hXH⟩ :=
    (C.supporter_saved M F R C.E U) h1 (by omega) v hv' X hX
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hsend
    exact x.lbl_tickStep ⟨i, hi⟩
  have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := C.E.not_mem_corrupted_of_tick hkU
  have hkUs : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by
    have h := (C.E.tick_active _ u _ hkU).2.2
    have : ((M.voteTime S.C σ : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C σ + Δ S ≤ M.supportCutoff S.C s by omega)
    linarith
  -- `w`'s ticks
  have hwb : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 2)) := (Finset.mem_sdiff.1 hw).2
  have htickW : ∀ c : ℕ, tGAT + Δ S ≤ c → c + Δ S ≤ M.supportCutoff S.C (s₁ + 2) →
      x.lbl (x.tickStep w c) = Event.tick w c := by
    intro c hc1' hc2'
    have h := (C.awakeHonest M F) R C.E w (t₁ := tGAT) (b := M.supportCutoff S.C (s₁ + 2)) le_rfl hcE2 hwb
    have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hc1'
    have h2R : (c : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₁ + 2) : ℕ) : ℝ) := by exact_mod_cast hc2'
    exact ((tickStep_spec M) x R C.E (t := c) (v := w) (by omega)
      (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) h)).1
  have hk0 := htickW (M.voteTime S.C (s - S.C.k - 1)) (by omega) (by omega)
  have hkσ := htickW (M.voteTime S.C σ + Δ S) (by omega) (by omega)
  have hk₁ := htickW (M.voteTime S.C (s₁ + 1)) (by omega) (by omega)
  have hdw : tGAT ≤ M.dutyWindowStart S.C (s₁ + 1) := by
    have := ((C.slot_facts M F U) (show s - S.C.k - 1 ≤ s₁ + 1 by omega)).2; omega
  have hvU : w ∈ updaterAt M S A x (s₁ + 1) := (C.hActive (s₁ + 1) hdw hcE2 w hwb).2
  have hk₂ : x.lbl (x.tickStep w (M.supportCutoff S.C (s₁ + 2))) = Event.tick w (M.supportCutoff S.C (s₁ + 2)) := by
    have hvU' := hvU
    unfold updaterAt at hvU'
    obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hvU'
    exact x.lbl_tickStep ⟨k', hk'⟩
  have hwk₁ : w ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s₁ + 1))) := C.E.not_mem_corrupted_of_tick hk₁
  have hwk₂ : w ∉ A.corrupted (x.tickStep w (M.supportCutoff S.C (s₁ + 2))) := C.E.not_mem_corrupted_of_tick hk₂
  have hwkσ : w ∉ A.corrupted (x.tickStep w (M.voteTime S.C σ + Δ S)) := C.E.not_mem_corrupted_of_tick hkσ
  have hk₁t := C.E.tick_active _ w _ hk₁
  have hk₂t := C.E.tick_active _ w _ hk₂
  -- `w`'s tick to the window's start comes at or before its last step before `vt + 2Δ`, which comes before its
  -- ticks to the vote time of slot `s₁ + 1` and to the support cutoff of slot `s₁ + 2`
  have ha1 : 1 ≤ M.voteTime S.C σ + 2 * Δ S := by omega
  have hsb := (stepBefore_time M) x R C.E ha1
  have hk0m : x.tickStep w (M.voteTime S.C (s - S.C.k - 1)) ≤ x.stepBefore (M.voteTime S.C σ + 2 * Δ S) := by
    by_contra hc
    have h := htime (show x.stepBefore (M.voteTime S.C σ + 2 * Δ S) + 1 ≤ x.tickStep w (M.voteTime S.C (s - S.C.k - 1)) by omega)
    have ht0 := (C.E.tick_active _ w _ hk0).2.2
    have : ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (s - S.C.k - 1) + Δ S ≤ M.voteTime S.C σ + 2 * Δ S by omega)
    linarith [hsb.2]
  have hm₁ : x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ x.tickStep w (M.voteTime S.C (s₁ + 1)) := by
    apply le_of_lt
    apply (lt_of_time_lt M) x R
    have : ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s₁ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C σ + 2 * Δ S + Δ S ≤ M.voteTime S.C (s₁ + 1) by omega)
    linarith [hsb.1, hk₁t.2.1]
  have hm₂ : x.stepBefore (M.voteTime S.C σ + 2 * Δ S) ≤ x.tickStep w (M.supportCutoff S.C (s₁ + 2)) := by
    apply le_of_lt
    apply (lt_of_time_lt M) x R
    have : ((M.voteTime S.C σ + 2 * Δ S : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₁ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C σ + 2 * Δ S + Δ S ≤ M.supportCutoff S.C (s₁ + 2) by omega)
    linarith [hsb.1, hk₂t.2.1]
  have hk₁s : x.time (x.tickStep w (M.voteTime S.C (s₁ + 1))) < ((M.supportCutoff S.C s : ℕ) : ℝ) := by
    have : ((M.voteTime S.C (s₁ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (s₁ + 1) + Δ S ≤ M.supportCutoff S.C s by omega)
    linarith [hk₁t.2.2]
  have hk₁E : x.time (x.tickStep w (M.voteTime S.C (s₁ + 1))) ≤ (tAwakeEnd : ℝ) :=
    le_trans hk₁s.le (by exact_mod_cast hcE)
  -- three delays after the vote time of slot `σ` is before `w`'s two ticks
  have h3k₁ : ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) ≤ x.time (x.tickStep w (M.voteTime S.C (s₁ + 1))) := by
    have : ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s₁ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C σ + 3 * Δ S + Δ S ≤ M.voteTime S.C (s₁ + 1) by omega)
    linarith [hk₁t.2.1]
  have h3k₂ : ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) ≤ x.time (x.tickStep w (M.supportCutoff S.C (s₁ + 2))) := by
    have : ((M.voteTime S.C σ + 3 * Δ S : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₁ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C σ + 3 * Δ S + Δ S ≤ M.supportCutoff S.C (s₁ + 2) by omega)
    linarith [hk₂t.2.1]
  -- the frame at the two ticks
  obtain ⟨H₁, hH₁T, hv₁, W₁, hHW₁, hW₁T, hfl₁, -, hr₁⟩ :=
    (C.frame_st M F R U Fx) h1 (by omega) u huA vote hsend w (M.supportCutoff S.C (s₁ + 2)) (by omega) hcs hwb
      (x.tickStep w (M.voteTime S.C (s₁ + 1))) hk₁E hm₁ hwk₁
      (fun j hj1 hj2 => C.hNo w j _ _ _ hk0 (le_trans hk0m hj1) hk₁ (by omega) hj2
        (C.E.not_mem_corrupted_of_le hj2.le hwk₁))
      (C.hRoots _ w _ hk₁ (by omega)) le_rfl
  obtain ⟨H₂, hH₂T, hv₂, W₂, hHW₂, -, -, hF₂, -⟩ :=
    (C.frame_st M F R U Fx) h1 (by omega) u huA vote hsend w (M.supportCutoff S.C (s₁ + 2)) (by omega) hcs hwb
      (x.tickStep w (M.supportCutoff S.C (s₁ + 2))) htE hm₂ hwk₂
      (fun j hj1 hj2 => hNoT j (le_trans hk0m hj1) hj2 (C.E.not_mem_corrupted_of_le hj2.le hwk₂))
      hRootsT htRT
  -- `vote` names one block of `u`'s tree at its tick
  have hroot : ∀ H : Block V, H ∈ (x.tickInput u (M.voteTime S.C σ)).tree →
      vote = GoldfishVote.mk u σ H.root → H = H_u := by
    intro H hH hvH
    rw [hvote] at hvH
    simp only [GoldfishVote.mk.injEq, true_and] at hvH
    exact C.hRoots _ u _ hkU (by omega) H H_u ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R C.E (v := u) huk le_rfl hH) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R C.E (v := u) huk le_rfl hHT) hvH.symm
  rw [hroot H₁ hH₁T hv₁] at hHW₁
  rw [hroot H₂ hH₂T hv₂] at hHW₂
  have hXW₁ := ancestorEq_trans hXH hHW₁
  have hXW₂ := ancestorEq_trans hXH hHW₂
  have hinv₁ := (lem11_node_invariant M F S A x R C.E _ w hwk₁).1
  refine ⟨?_, ?_, ?_⟩
  · exact compatible_symm'
      (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hXW₁
        (compatible_symm' (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hr₁)))
  · intro hRX
    have hRX' : (M.get_fc_root (x.st (x.tickStep w (M.voteTime S.C (s₁ + 1))) w)).AncestorEq X := by
      rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hRX
    have hRW := ancestorEq_trans hRX' hXW₁
    have hFW := ancestorEq_trans
      ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R C.E _ w) hRW
    have hkk1 : x.tickStep w (M.voteTime S.C σ + Δ S) ≤ x.tickStep w (M.voteTime S.C (s₁ + 1)) :=
      (tick_step_le_of_le M F) C.E hkσ hk₁ (by omega)
    have hW₁a : W₁ ∈ (x.st (x.tickStep w (M.voteTime S.C (s₁ + 1))) w).tree :=
      ((GoldilocksCorrectness.Record.Proofs.Executions.grows_of_le M F) x R C.E w hkk1).1 hW₁T
    have hck : x.clockValue (x.tickStep w (M.voteTime S.C σ + Δ S)) w < M.viewFreeze S.C (s₁ + 1 - 1) := by
      have h := C.E.clockValue_le_of_set hwkσ (Or.inl hkσ)
      rw [Nat.add_sub_cancel, (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s₁]
      have : M.voteTime S.C σ + Δ S < M.slotStart S.C s₁ + 3 * Δ S := by omega
      omega
    refine ⟨W₁, ?_, ?_, hXW₁⟩
    · have hVT := (mem_voter_tree_st M F U) (s' := s₁ + 1) S A x R C.E hkk1 hwk₁ hW₁T hck hFW
      classical
      exact (Finset.mem_filter.1 hVT).2
    · show W₁ ∈ (M.fg_to_ac (x.st (x.tickStep w (M.voteTime S.C (s₁ + 1))) w)).viable_heads
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hinv₁,
        (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
      exact ⟨hW₁a, hFW, hRW, hfl₁⟩
  · exact compatible_symm'
      (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hXW₂ (compatible_symm' hF₂))


/-- **Clause 1 of `FrontWindowStable`.** At a slot `s₁` from `s − k − 1` to `s − 2`, every member
`w` of slot `s₁ + 1` satisfies `StepFrameAt` relative to every confirmation `X` a member saved for
a slot `σ` from `s − k − 1` to `s₁`.

Why: `X` has an honest supporter `u` (`supporter_saved`), whose vote is an ancestor of a viable
block `W` of `u` that reaches `w` by the support cutoff of slot `σ` (`frame`). Before the vote time
of slot `s₁ + 1`, `w`'s root is compatible with `W`, so with `X`; when the root is `X` or an
ancestor of it, `W` is viable at `w` and in its voter tree (held before the view freeze of slot
`s₁`). Before the support cutoff of slot `s₁ + 2`, `w`'s finalized block is compatible with `W`,
so with `X`.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle.

Read aloud: clause 1 of `FrontWindowStable`: every member of slot `s₁ + 1` satisfies `StepFrameAt`
relative to every confirmation a member saved for a window slot up to `s₁`. -/
theorem stepFrame (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s₁ σ : ℕ}
    (h1 : s - S.C.k - 1 ≤ σ) (h2 : σ ≤ s₁) (h3 : s₁ + 2 ≤ s) (v : V)
    (hv : v ∈ Hon M S A x (σ + 1)) (X : Block V)
    (hX : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X)
    (w : V) (hw : w ∈ Hon M S A x (s₁ + 1)) :
    StepFrameAt M S A x X s₁ w := by
  --: the three facts `stepFrame_of_noChange` reads at `w`'s tick to the support cutoff of slot `s₁ + 2`
  -- are the bundle's per-tick roots, phase and window at that tick
  have hk2 := S.C.k_ge_two
  have hkk := C.hk
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hcE : M.supportCutoff S.C s ≤ tAwakeEnd := C.tEnd M F
  obtain ⟨-, -, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₁ + 1)
  obtain ⟨-, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₁ + 2)
  rw [show s₁ + 1 + 1 = s₁ + 2 from rfl] at hs1
  have hvt0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s - S.C.k - 1)
  have hsync0 := (C.syncStart M F U) (le_refl (s - S.C.k - 1))
  have hmx1 := le_max_left (Δ S) Δs
  have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h3
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s - S.C.k - 1 ≤ s₁ + 1 by omega)
  have hcE2 : M.supportCutoff S.C (s₁ + 2) ≤ tAwakeEnd := le_trans hcs hcE
  have hwb : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 2)) := (Finset.mem_sdiff.1 hw).2
  have hdw : tGAT ≤ M.dutyWindowStart S.C (s₁ + 1) := by
    have := ((C.slot_facts M F U) (show s - S.C.k - 1 ≤ s₁ + 1 by omega)).2; omega
  have hvU : w ∈ updaterAt M S A x (s₁ + 1) := (C.hActive (s₁ + 1) hdw hcE2 w hwb).2
  have hk₂ : x.lbl (x.tickStep w (M.supportCutoff S.C (s₁ + 2))) = Event.tick w (M.supportCutoff S.C (s₁ + 2)) := by
    have hvU' := hvU
    unfold updaterAt at hvU'
    obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hvU'
    exact x.lbl_tickStep ⟨k', hk'⟩
  have hk0 : x.lbl (x.tickStep w (M.voteTime S.C (s - S.C.k - 1))) = Event.tick w (M.voteTime S.C (s - S.C.k - 1)) := by
    have h := (C.awakeHonest M F) R C.E w (t₁ := tGAT) (b := M.supportCutoff S.C (s₁ + 2)) le_rfl hcE2 hwb
    have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
    have hSk := C.hSkew
    have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (s - S.C.k - 1) by omega)
    have h2R : ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₁ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (s - S.C.k - 1) + Δ S ≤ M.supportCutoff S.C (s₁ + 2) by omega)
    exact ((tickStep_spec M) x R C.E (t := M.voteTime S.C (s - S.C.k - 1)) (v := w) (by omega)
      (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) h)).1
  exact (C.stepFrame_of_noChange M F R U Fx) h1 h2 h3 v hv X hX w hw
    (C.hRoots _ w _ hk₂ hcs) le_rfl (C.hTick _ w _ hk₂ hcs)
    (fun j hj1 hj2 hwj => C.hNo w j _ _ _ hk0 hj1 hk₂ hcs hj2 hwj)

/-- **Every member of a window slot saves a confirmation.** At a slot `σ` from `s − k` with
`σ + 2 ≤ s`, every member `v` of slot `σ` holds right after the support cutoff of slot `σ + 1`
some confirmation of slot `σ`: every honest vote of slot `σ` extends `v`'s finalized block
(`vote_extends_finalized_of_no_change`), so the update saves one (`confirmation_saved_of_votes`).
B5's argument (`window_last_confirmation_exists_of_no_change`) at any member and any such slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.


Read aloud: every member of a window slot holds a confirmation of that slot right after the support
cutoff of the next slot. -/
theorem member_saves (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hσ : s - S.C.k ≤ σ) (hσs : σ + 2 ≤ s) (v : V)
    (hv : v ∈ roundMembers M S A x (σ + 1)) :
    ∃ D : Block V,
      (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some D := by
  have hk2 := S.C.k_ge_two
  have hk := C.hk
  have hΔ := one_le_Δ S
  have hσ1 : 1 ≤ σ := by omega
  obtain ⟨-, hdw⟩ := (C.slot_facts M F U) (show s - S.C.k - 1 ≤ σ by omega)
  have hsync := (C.syncStart M F U) (show s - S.C.k - 1 ≤ σ - 1 by omega)
  have hsync0 := (C.syncStart M F U) (le_refl (s - S.C.k - 1))
  have hvt0 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s - S.C.k - 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s - S.C.k - 1 ≤ σ - 1 by omega)
  obtain ⟨-, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨-, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  rw [show σ + 1 + 1 = σ + 2 from rfl] at hs1
  obtain ⟨-, -, -, hs0, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ - 1)
  rw [show σ - 1 + 1 = σ by omega] at hs0
  obtain ⟨-, -, -, hsσ, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show σ + 2 ≤ s by omega)
  have hmx1 := le_max_left (Δ S) Δs
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hcutE : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd := le_trans (by omega) (C.tEnd M F)
  -- a validator honest through the support cutoff of slot `σ + 1` ticks to the window's start, so the
  -- bundle's `hNo` covers its steps from `2Δ` into slot `σ − 1`
  have hNoR : ∀ (w : V) (j k' c : ℕ), w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) →
      ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → x.lbl k' = Event.tick w c →
      c ≤ M.supportCutoff S.C (σ + 1) → j < k' → w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j := by
    intro w j k' c hw h1 hk' hc h2 hwj
    have h := (C.awakeHonest M F) R C.E w le_rfl hcutE hw
    have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (s - S.C.k - 1) by omega)
    have h2R : ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (s - S.C.k - 1) + Δ S ≤ M.supportCutoff S.C (σ + 1) by omega)
    have hk0 := ((tickStep_spec M) x R C.E (t := M.voteTime S.C (s - S.C.k - 1)) (v := w) (by omega)
      (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) h)).1
    have hkj := (tick_le_of_time_ge M F) R C.E (d := Δ S) (by linarith) hk0
      (le_trans (by exact_mod_cast (show M.voteTime S.C (s - S.C.k - 1) + Δ S ≤ M.slotStart S.C (σ - 1) + 2 * Δ S by omega)) h1)
    exact C.hNo w j _ _ _ hk0 hkj hk' (by omega) h2 hwj
  -- roots at `v`'s tick to the support cutoff of slot `σ + 1`, a tick to a clock value at most the support cutoff
  -- of slot `s` (the bundle's per-tick roots,)
  have hdwσ : tGAT ≤ M.dutyWindowStart S.C σ := by omega
  have hkV := (tick_lbl_of_roundMember M F) C.hActive hdwσ hcutE hv
  have hRootsV : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (σ + 1)))) :=
    C.hRoots _ v _ hkV (by omega)
  exact (member_saves_of_no_change_upTo M F U Fx) S A x R GST tGAT tAwakeEnd σ
    (M.supportCutoff S.C s) C.E C.hNet C.hSkew C.hRedeliver C.Sy C.hΔs C.hParent C.hGST C.hThird
    C.hAwake C.hActive hσ1 hsync hdwσ (by omega) (C.tEnd M F)
    ((C.members M F C.E U R (σ := σ) (by omega) (by omega)).2) hNoR v hRootsV hv

/-- **An honest vote of a window slot extends every root read at a tick one delay or more after it**
. At a slot `σ` from `s − k` with `σ + 2 ≤ s`, an honest active
voter `u` of slot `σ` whose tick put `vote` on the wire votes for a block `H_u` of which the root of
every validator `w`, at its tick `kR` to a clock value `c` from one delay after the vote time of slot
`σ` to one delay before the support cutoff of slot `s`, is an ancestor, or which it is: the root is the
finalized block (`vote_extends_finalized_st_of_no_change`) or the justified block
(`vote_extends_justified_root`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle; `c`, `kR`: the clock value and the step of `w`'s tick.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.


Read aloud: an honest vote of a window slot is for a block that has as ancestor, or is, every
fork-choice root read at a validator's tick to a clock value one delay or more after the vote. -/
theorem vote_extends_root (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    (hσ : s - S.C.k ≤ σ) (hσs : σ + 2 ≤ s) (u : V) (hu : u ∈ honestActiveAt M S A x σ)
    (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (w : V) (c kR : ℕ) (hkR : x.lbl kR = Event.tick w c) (hc : M.voteTime S.C σ + Δ S ≤ c)
    (hcb : c + Δ S ≤ M.supportCutoff S.C s) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree,
      vote = GoldfishVote.mk u σ H_u.root ∧
        (M.get_fc_root (x.st kR w)).AncestorEq H_u := by
  have hk2 := S.C.k_ge_two
  have hkk := C.hk
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hσ1 : 1 ≤ σ := by omega
  have hσ' : σ - 1 + 1 = σ := Nat.sub_add_cancel hσ1
  have hss : M.slotStart S.C σ = M.slotStart S.C (σ - 1) + 4 * Δ S := by
    rw [← hσ', (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one, hσ']
  have hvσ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hfz : M.viewFreeze S.C (σ - 1) = M.slotStart S.C (σ - 1) + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (σ - 1)
  have hμ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s - S.C.k - 1)
  have hμσ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s - S.C.k - 1 ≤ σ - 1 by omega)
  have hsc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ + 1 ≤ s by omega)
  have hsc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hss' : M.slotStart S.C (σ + 1) = M.slotStart S.C σ + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hcE : M.supportCutoff S.C s ≤ tAwakeEnd := C.tEnd M F
  have hsync0 := (C.syncStart M F U) (le_refl (s - S.C.k - 1))
  have hGa : GST ≤ M.slotStart S.C (σ - 1) + 2 * Δ S := by
    have := C.hGST; have := (C.tGAT_le M F U); omega
  -- `w`'s tick to `c`, before the support cutoff of slot `s`
  have hkRt := C.E.tick_active kR w c hkR
  have hwk : w ∉ A.corrupted kR := C.E.not_mem_corrupted_of_tick hkR
  have hcR : (c : ℝ) + Δ S ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by exact_mod_cast hcb
  have hvc : ((M.voteTime S.C σ : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hc
  have hkRs : x.time kR < ((M.supportCutoff S.C s : ℕ) : ℝ) := by linarith [hkRt.2.2]
  have hkRE : x.time kR ≤ (tAwakeEnd : ℝ) := le_trans hkRs.le (by exact_mod_cast hcE)
  have hwT : ∀ t : ℝ, t < x.time kR → w ∉ A.corruptedAtTime x t := by
    intro t ht
    refine Activity.not_mem_corruptedAtTime.2 fun i hi hvi => hwk ?_
    have hik : i < kR := (lt_of_time_lt M) x R (by linarith)
    exact C.E.corrupted_mono i kR hik.le hvi
  have hcs : c ≤ M.supportCutoff S.C s := by omega
  have hRootsR : RootsNameBlocksUntil M A x (x.time kR) := C.hRoots kR w c hkR hcs
  -- no fork-choice change from `2Δ` into slot `σ − 1` to before one of the validator's ticks to a clock value at
  -- most the support cutoff of slot `s`, for a validator honest at a natural time at least one delay after the
  -- window's start value: its tick to that value comes first (the bundle's `hNo`)
  have hNoE : ∀ (v : V) (e j k' c' : ℕ), M.voteTime S.C (s - S.C.k - 1) + Δ S ≤ e → e ≤ tAwakeEnd →
      v ∉ A.corruptedAtTime x e → ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j →
      x.lbl k' = Event.tick v c' → c' ≤ M.supportCutoff S.C s → j < k' →
      v ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x v j := by
    intro v e j k' c' he heE hv h1 hk' hc' h2 hvj
    have h := (C.awakeHonest M F) R C.E v le_rfl heE hv
    have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.voteTime S.C (s - S.C.k - 1) by omega)
    have h2R : ((M.voteTime S.C (s - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ (e : ℝ) := by exact_mod_cast he
    have hk0 := ((tickStep_spec M) x R C.E (t := M.voteTime S.C (s - S.C.k - 1)) (v := v) (by omega)
      (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) h)).1
    have hkj := (tick_le_of_time_ge M F) R C.E (d := Δ S) (by linarith) hk0
      (le_trans (by exact_mod_cast (show M.voteTime S.C (s - S.C.k - 1) + Δ S ≤ M.slotStart S.C (σ - 1) + 2 * Δ S by omega)) h1)
    exact C.hNo v j _ _ _ hk0 hkj hk' hc' h2 hvj
  -- the voter
  have huc : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) :=
    fun h => (Finset.mem_sdiff.1 hu).2 (Finset.mem_union_left _ h)
  have huvt : u ∉ A.corruptedAtTime x (M.voteTime S.C σ) :=
    (not_mem_corruptedAtTime_of_le M) x R C.E (by omega) huc
  have huA : u ∈ A.activeThroughout x (M.slotStart S.C (σ - 1) + 2 * Δ S) (M.voteTime S.C σ) := by
    have h := (C.awakeHonest M F) R C.E u (t₁ := M.slotStart S.C (σ - 1) + 2 * Δ S) (b := M.voteTime S.C σ)
      (by have := (C.tGAT_le M F U); omega) (by omega) huvt
    push_cast at h
    exact h
  have hkU : x.lbl (x.tickStep u (M.voteTime S.C σ)) = Event.tick u (M.voteTime S.C σ) := by
    obtain ⟨i, hi, -⟩ := hSend
    exact x.lbl_tickStep ⟨i, hi⟩
  have hkUt := C.E.tick_active _ u _ hkU
  have huk : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C σ)) := C.E.not_mem_corrupted_of_tick hkU
  have hkUR : x.time (x.tickStep u (M.voteTime S.C σ)) ≤ x.time kR := by linarith [hkUt.2.2]
  have hNoU : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → j < x.tickStep u (M.voteTime S.C σ) →
      ¬ ForkChoiceChangeStep M S A x u j := fun j h1 h2 =>
    hNoE u (M.voteTime S.C σ) j _ _ (by omega) (by omega) huvt h1 hkU (by omega) h2
      (C.E.not_mem_corrupted_of_le h2.le huk)
  have hNoW : ∀ j : ℕ, ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) ≤ x.time j → j < kR →
      ¬ ForkChoiceChangeStep M S A x w j := fun j h1 h2 =>
    hNoE w (M.voteTime S.C σ) j _ _ (by omega) (by omega) (hwT _ (by linarith [hkRt.2.1])) h1 hkR hcs h2
      (C.E.not_mem_corrupted_of_le h2.le hwk)
  have ha : tGAT + max (Δ S) Δs ≤ M.viewFreeze S.C (σ - 1) := by
    have := C.syncStart M F U (σ := σ - 1) (by omega); omega
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st kR w)
      (lem11_node_invariant M F S A x R C.E kR w hwk).1 with ⟨hrJ, hmJ, hcJ⟩ | ⟨hrF, -⟩
  · obtain ⟨H_u, hHT, hvote, hJH⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.vote_extends_justified_root_upTo M F U Fx) S A x R GST
      C.E C.hNet C.hSkew C.hRedeliver C.Sy C.hΔs C.hParent tAwakeEnd σ c kR u w vote hRootsR (by omega) tGAT C.hGST ha
      C.hAwake C.hThird hσ1 hGa hkR hc hkRE huA hNoU hNoW hmJ hcJ hSend
    exact ⟨H_u, hHT, hvote, hrJ ▸ hJH⟩
  · have ha1 : 1 ≤ M.slotStart S.C (σ - 1) + 2 * Δ S := by omega
    have hai : x.stepBefore (M.slotStart S.C (σ - 1) + 2 * Δ S) ≤ kR := by
      apply le_of_lt
      apply (lt_of_time_lt M) x R
      have h := ((stepBefore_time M) x R C.E ha1).1
      have : ((M.slotStart S.C (σ - 1) + 2 * Δ S : ℕ) : ℝ) + 3 * Δ S ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by
        exact_mod_cast (show M.slotStart S.C (σ - 1) + 2 * Δ S + 3 * Δ S ≤ M.voteTime S.C σ by omega)
      linarith [hkRt.2.1]
    obtain ⟨H_u, hHT, hvote, hFH⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.vote_extends_finalized_st_of_no_change_upTo M F U Fx)
      S A x R GST tAwakeEnd σ (x.time kR) kR u w vote C.E C.hNet C.hSkew C.hRedeliver C.Sy C.hΔs hRootsR C.hParent
      (by omega)
      tGAT C.hGST ha C.hAwake C.hThird hσ1 hGa hkRE hkUR le_rfl hai hwk
      (hwT _ (by
        have : ((M.viewFreeze S.C (σ - 1) : ℕ) : ℝ) + 2 * Δ S ≤ ((M.voteTime S.C σ : ℕ) : ℝ) := by
          exact_mod_cast (show M.viewFreeze S.C (σ - 1) + 2 * Δ S ≤ M.voteTime S.C σ by omega)
        linarith [hkRt.2.1]))
      huA hNoW hNoU hSend
    exact ⟨H_u, hHT, hvote, hrF ▸ hFH⟩


/-- **`rootChain` read at `w`'s tick to a clock value `c` from the support cutoff of slot `σ + 1` to one delay
before that of slot `σ + 2`.** With `s = σ + 2`, every member `w` of slot `σ + 1` saved a confirmation `D` of slot `σ`
(`member_saves`), and its root at its tick input to `c` is `D` or an ancestor of `D`: every honest vote of slot `σ`
extends that root (`vote_extends_root`, at `w`'s tick to `c`), and Lemma 78 at `w`. `rootChain` is the case `c` the
vote time of slot `σ + 2`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle; `σ`: the slot; `w`: the member; `c`: the clock value.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.


Read aloud: a member of slot `σ + 1` saved a confirmation `D` of slot `σ`, and its fork-choice root at its tick to
any clock value from the support cutoff of slot `σ + 1` to one delay before that of slot `σ + 2` is `D` or an
ancestor of `D`.
-/
theorem rootChain_at (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ} (hs : s = σ + 2)
    (w : V) (hw : w ∈ Hon M S A x (σ + 1)) (c : ℕ) (hc1 : M.supportCutoff S.C (σ + 1) ≤ c)
    (hc2 : c + Δ S ≤ M.supportCutoff S.C (σ + 2)) :
    ∃ D : Block V,
      (x.tickOutput w (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some D ∧
      (M.get_fc_root (x.tickInput w c)).AncestorEq D := by
  have hcσS : M.supportCutoff S.C σ ≤ M.supportCutoff S.C s :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ ≤ s by omega)
  subst hs
  have hk2 := S.C.k_ge_two
  have hkk := C.hk
  have hΔ := one_le_Δ S
  have hA0 := C.E.ahead_nonneg
  have hB0 := C.E.behind_nonneg
  have hSk := C.hSkew
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hmx1 := le_max_left (Δ S) Δs
  have hσ : σ + 2 - S.C.k ≤ σ := by omega
  have hσ1 : 1 ≤ σ := by omega
  have hcE : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd := C.tEnd M F
  obtain ⟨hvt1, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvt2, hc2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hvt3, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  rw [show σ + 1 + 1 = σ + 2 from rfl] at hs2
  have hsyncσ : tGAT + max (Δ S) Δs + 4 * Δ S ≤ M.slotStart S.C σ := (C.syncStart M F U) (by omega)
  have hcut1E : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd := le_trans (by omega) hcE
  -- `w` is a member of slot `σ`, so it saved a confirmation `D` of slot `σ`
  have hw' : w ∈ roundMembers M S A x (σ + 1) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A (σ + 1) (σ + 2) tAwakeEnd R C.E
      (Nat.le_succ _) hcE).1 hw
  obtain ⟨D, hD⟩ := (C.member_saves M F R U Fx) hσ le_rfl w hw'
  refine ⟨D, hD, ?_⟩
  obtain ⟨hsub, hMaj⟩ := C.members M F C.E U R (σ := σ) (by omega) (by omega)
  have hcut1 : ∀ u : V, u ∈ roundMembers M S A x (σ + 1) → u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) :=
    fun u hu => (Finset.mem_sdiff.1 hu).2
  -- `w` updates at slot `σ` (`updaterAt`), and ticks to the vote time of slot `σ + 2`
  have hdw : tGAT ≤ M.dutyWindowStart S.C σ := by
    have := ((C.slot_facts M F U) (show σ + 2 - S.C.k - 1 ≤ σ by omega)).2; omega
  have hvU : w ∈ updaterAt M S A x σ := (C.hActive σ hdw hcut1E w (hcut1 w hw')).2
  have hw2 : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 2)) := (Finset.mem_sdiff.1 hw).2
  have hkW : x.lbl (x.tickStep w (c)) = Event.tick w (c) := by
    have h := (C.awakeHonest M F) R C.E w (t₁ := tGAT) (b := M.supportCutoff S.C (σ + 2)) le_rfl hcE hw2
    have h1R : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((c : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ c by omega)
    have h2R : ((c : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show c + Δ S ≤ M.supportCutoff S.C (σ + 2) by omega)
    exact ((tickStep_spec M) x R C.E (t := c) (v := w) (by omega)
      (Activity.mem_activeThroughout_of_le (by linarith) (by linarith) h)).1
  -- every honest vote of slot `σ` of a member extends `w`'s root at that tick
  have hC1 : ∀ u ∈ S.P.committee σ ∩ roundMembers M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree,
        vote = GoldfishVote.mk u σ H_u.root ∧
        (M.get_fc_root (x.tickInput w (c))).AncestorEq H_u :=
    fun u hu vote hSend => (C.vote_extends_root M F R U Fx) hσ le_rfl u
      (hsub (Finset.mem_inter.1 hu).2) vote hSend w (c) _ hkW (by omega) (by omega)
  obtain ⟨H, hH⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.voters_of_votes_clause M F U) S A x R σ
    (S.P.committee σ ∩ roundMembers M S A x (σ + 1)) _ C.E C.hSkew
    (fun u hu => ⟨hsub (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩) hC1
  -- Lemma 78's three inputs (, supplied as supplies them): roots up to `w`'s own tick to
  -- the support cutoff of slot `σ`, each voter outside the adversary set at `w`'s tick to the support cutoff of
  -- slot `σ + 1`, and each voter active through the sync delay after Lemma 12's read time
  have hRootsσ : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C σ))) := by
    have hvU' := hvU
    unfold updaterAt at hvU'
    obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x R C.E C.hΔs C.hSkew hvU'
    rw [(tickStep_eq_of_lbl M) x C.E hkR]
    have ht := (C.E.tick_active kR w _ hkR).2.2
    exact C.hRoots kR w _ hkR (by omega)
  have hHonTick : ∀ u ∈ S.P.committee σ ∩ roundMembers M S A x (σ + 1),
      u ∉ A.corrupted (x.tickStep w (M.supportCutoff S.C (σ + 1))) := by
    intro u hu
    classical
    have hu' := hsub (Finset.mem_inter.1 hu).2
    have hvU' := hvU
    unfold honestActiveAt at hu'
    unfold updaterAt at hvU'
    have hX : u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
        x.lbl k = Event.tick w (M.supportCutoff S.C (σ + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) :=
      fun h => (Finset.mem_sdiff.1 hu').2 (Finset.mem_union.2 (Or.inr h))
    exact (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x C.E hvU' hX
  have hHold : ∀ u ∈ S.P.committee σ ∩ roundMembers M S A x (σ + 1),
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
    intro u hu
    have hu1 := hcut1 u (Finset.mem_inter.1 hu).2
    have hb : tGAT ≤ M.supportCutoff S.C σ - max (2 * Δ S) Δs := by
      rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;>
      rcases max_cases (Δ S) Δs with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] <;> rw [h'] at hsyncσ <;> omega
    have hend : M.supportCutoff S.C σ - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C (σ + 1) := by
      rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;>
      rcases max_cases (Δ S) Δs with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] <;> rw [h'] at hsyncσ <;> omega
    have h := (activeThroughout_nat_of_awake_from M F) R C.E C.hAwake hu1 hb hcut1E
    refine Activity.mem_activeThroughout_of_le le_rfl ?_ h
    exact_mod_cast hend
  -- `w`'s finalized block at its tick to the support cutoff of slot `σ + 1` is an ancestor of, or is, its root at
  -- its later tick to the vote time of slot `σ + 2`
  have hF : (x.tickInput w (M.supportCutoff S.C (σ + 1))).finalized.compatible
      (M.get_fc_root (x.tickInput w (c))) = true := by
    have hvU' := hvU
    unfold updaterAt at hvU'
    obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hvU'
    have hle := (tick_step_le_of_le M F) C.E hkc hkW (by omega)
    have h1 : x.tickInput w (M.supportCutoff S.C (σ + 1)) = x.st kc w := by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x C.E hkc]
    have h2 : x.tickInput w (c) = x.st (x.tickStep w (c)) w := by
      unfold Trace.tickInput; rfl
    rw [h1, h2]
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      ((GoldilocksCorrectness.Record.Proofs.Executions.grows_of_le M F) x R C.E w hle).2.1
      ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R C.E _ w)))
  have hGσ : GST + max (Δ S) Δs ≤ M.supportCutoff S.C σ := by
    have := C.hGST
    omega
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem78_update_confirmation_extends_voter_majority_chain_upTo M F U)
    S A x R GST σ (S.P.committee σ ∩ roundMembers M S A x (σ + 1)) H _ w (C.E.mono hcσS) C.hNet C.hSkew C.hRedeliver (C.Sy.mono hcσS) C.hΔs
    hRootsσ C.hParent ((GoldilocksCorrectness.Record.Statements.Executions.votesCastByOwner_of_unforgeability M F) S A x R C.E)
    hGσ
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1, hHonTick u hu, (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    hHold
    ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R C.E σ
      (x.tickStep w (M.supportCutoff S.C (σ + 1))) (roundMembers M S A x (σ + 1)) w hMaj).2.1
    hvU hF D hD


/-- **Clause 2 of `FrontWindowStable`, at a member's own confirmation.** With `s = σ + 2`, every
member `w` of slot `σ + 1` saved a confirmation `D` of slot `σ` (`member_saves`), and its root
at its tick input to the vote time of slot `σ + 2` (the state its tick to that clock value starts from,
where clause 2 of `FrontWindowStable` reads it) is `D` or an ancestor of `D`: every honest vote of slot `σ`
extends that root (`vote_extends_root`), and Lemma 78 at `w`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
  `C`: the bundle.

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of the bundle
`B6CtxUpTo`.


Read aloud: clause 2 of `FrontWindowStable`: every member of slot `σ + 1` saved a confirmation `D`
of slot `σ` whose ancestor, or itself, is its fork-choice root at its tick to the vote time of slot
`σ + 2`.
-/
theorem rootChain (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ} (hs : s = σ + 2)
    (w : V) (hw : w ∈ Hon M S A x (σ + 1)) :
    ∃ D : Block V,
      (x.tickOutput w (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some D ∧
      (M.get_fc_root (x.tickInput w (M.voteTime S.C (σ + 2)))).AncestorEq D := by
  have hk2 := S.C.k_ge_two
  obtain ⟨-, -, -, hs3, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hv3, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨-, hc2', -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  rw [show σ + 1 + 1 = σ + 2 from rfl] at hs3
  exact (C.rootChain_at M F R U Fx) hs w hw _ (by omega) (by omega)
end B6CtxUpTo

/-- **B6, the stability fact.** The proof; the audited
statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: by contradiction. With no validator outside the adversary set having a
`ForkChoiceChangeStep` at a step from the validator's own tick to the vote time of slot `s − k − 1` to before the support cutoff of slot
`s`, the two clauses of `FrontWindowStable` hold
(`(GoldilocksCorrectness.Record.Proofs.Executions.B6Ctx.stepFrame M F U Fx)`,
`(GoldilocksCorrectness.Record.Proofs.Executions.B6Ctx.rootChain M F U Fx)`), against `hFail`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  phase; `r`: the round; `s`: the honest round opening slot.

Roots name blocks until `M.supportCutoff S.C s`: every block the proof compares is held before the
support cutoff of slot `s`, the window's end (the bundle `B6Ctx` carries the premise at that
time).

Restated with the delivery premises up to `M.supportCutoff S.C s`: the bound of its roots `hRoots`;
every delivery its proof reads is due by then.

Read aloud: before the fast block's round, a window breaks only when some honest validator's root
moves to its justified block, other than an ancestor of its old root, or its `head_height_floor`
rises, at a time from the vote time of the window's second slot to before the support cutoff of slot
`s`, with the delivery premises up to the bound. -/
theorem stability_fact3_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r s : ℕ)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
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
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hk : S.C.k + 1 ≤ s)
    (hBefore : M.supportCutoff S.C s ≤ aR M S r)
    -- every validator's tick to a clock value at most the support cutoff of slot `s` is in the phase
    (hTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      x.time k ≤ (tAwakeEnd : ℝ))
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (s - S.C.k))
    (hFail : ¬ FrontWindowStable M S A x (Hon M S A x) (s - 2 * S.C.k) (s - 1)) :
    ∃ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (s - S.C.k - 1)) ∧ k ≤ j ∧
      x.lbl k' = Event.tick w c ∧ c ≤ M.supportCutoff S.C s ∧ j < k' ∧ w ∉ A.corrupted j ∧
      ForkChoiceChangeStep M S A x w j := by
  by_contra hcon
  have hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (s - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j :=
    fun w j k k' c h1 h2 h3 h4 h5 h6 h7 => hcon ⟨w, j, k, k', c, h1, h2, h3, h4, h5, h6, h7⟩
  have C : B6CtxUpTo M S A x GST tGAT tAwakeEnd r s Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet :=
    ⟨E, hNet, hSkew, hRedeliver, Sy, hΔs, hRoots, hParent, hGST, hThird, hAwake, hActive,
      hCommittees, hEnd, hk, hBefore, hTick, hAnchor, hNo⟩
  have hk2 := S.C.k_ge_two
  apply hFail
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 2 := ⟨s - 2, by omega⟩
  refine ⟨?_, ?_⟩
  · intro s₁ h1 h2 σ' hσ1 hσ2 v hv X hX w hw
    exact (B6CtxUpTo.stepFrame M F R U Fx C) (by omega) hσ2 (by omega)
      v hv X hX w hw
  · intro w hw
    rw [show σ + 2 - 1 = σ + 1 from rfl] at hw ⊢
    obtain ⟨D, hD, hRD⟩ := (B6CtxUpTo.rootChain M F R U Fx C) rfl w hw
    exact ⟨D, Or.inr ⟨w, hw, hD⟩, hRD⟩

end GoldilocksCorrectness.Record.Proofs.Executions

