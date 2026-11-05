module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ProposalViabilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FrameStatementsFGState
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Statements.Executions.ProposalViabilityStatements

@[expose] public section

/-!
# Boxes, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Boxes.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the box instances of Lemmas 59 and 61, read with
the greatest chain-state height `hMax M S.C n` of the node's tree in place of the cache `h_max`. The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (BoxOne BoxThree BoxTwo FrameShape
  JustifiedHeight hMax)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- In box 2 with a justified block `J₀` other than the genesis block, the justification height
`justifiedHeight` of a validator's node state before the time `t` is `J₀`'s chain-state height
(Lemma 57, with Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `J₀`: the justified block.

Read aloud: in box 2 with a justified block `J₀` other than the genesis block, the node's justified
height is `J₀`'s chain-state height. -/
theorem h_j_eq_of_boxTwo (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (v : V) (J₀ : Block V)
    (hBox : BoxTwo M S.C (x.stateBefore t v) J₀)
    (hJ₀ : J₀ ≠ Block.genesis) :
    (x.stateBefore t v).justifiedHeight = (M.chainStateOf S.C J₀).h := by
  obtain ⟨-, hJH, -, -, -⟩ := (GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E (x.stepBefore t) v
  have hJ : (x.stateBefore t v).justified = J₀ := hBox.2.2
  have hJH' : JustifiedHeight M S.C (x.stateBefore t v) := hJH
  rcases hJH' with hg | hh
  · exact absurd (hJ.symm.trans hg) hJ₀
  · rw [hJ] at hh
    exact hh.symm

/-- `lem59_boxOne` with `w`'s state read at its tick to a clock value `c` in place of its
tick to the vote time of slot `s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 1 at both states, with one greatest chain-state height, the two least viable
heights are that height minus one and the honest proposal reaches it; the root condition is the
hypothesis on `w`'s finalized block. `lem59_boxOne` is its instance at `c := voteTime S (s + 1)`.
-/
theorem lem59_boxOne_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s c : ℕ) (X B : Block V) (p w : V)
    -- `w` ticks to the clock value `c` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w c)
    (hBoxP : BoxOne M S.C (x.tickInput p (M.slotStart S.C (s + 1))))
    (hBoxW : BoxOne M S.C (x.tickInput w c))
    (hHmax : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) =
      hMax M S.C (x.tickInput w c))
    (hFw : (x.tickInput w c).finalized.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C W).h) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1)))
        (x.tickInput p (M.slotStart S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      FrameShape M (x.tickInput w c)
        (x.tickInput w c).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      (x.tickInput w c).finalized.AncestorEq B ∧
      (∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
        X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq W ∧
          hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C W).h) ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h := by
  have ⟨iP, hlP, _⟩ := hPropose
  have hInvP := (lem11_node_invariant M F S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p
    (by rw [(tickStep_eq_of_lbl M) x E hlP]; exact E.not_mem_corrupted_of_tick hlP)).1
  have hInvW := (lem11_node_invariant M F S A x R E (x.tickStep w c) w
    (by rw [(tickStep_eq_of_lbl M) x E hkW]; exact E.not_mem_corrupted_of_tick hkW)).1
  have hP := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxOne M F) S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) hInvP hBoxP).2
  have hW := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxOne M F) S.C S.P S.X (x.tickInput w c) hInvW hBoxW).2
  rw [← hHmax] at hW
  have hfl := (proposal_viable M F U) S A x R E s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, hFw, hHeadP, hfl⟩

/-- Lemma 59 in box 1. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem59_boxOne_at` at `c := M.voteTime S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 1 at both states, with one greatest chain-state height, the two least viable
heights are that height minus one and the honest proposal reaches it; the root condition is the
hypothesis on `w`'s finalized block. -/
theorem lem59_boxOne (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (X B : Block V) (p w : V)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)))
    (hBoxP : BoxOne M S.C (x.tickInput p (M.slotStart S.C (s + 1))))
    (hBoxW : BoxOne M S.C (x.tickInput w (M.voteTime S.C (s + 1))))
    (hHmax : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) =
      hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))))
    (hFw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C W).h) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1)))
        (x.tickInput p (M.slotStart S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      FrameShape M (x.tickInput w (M.voteTime S.C (s + 1)))
        (x.tickInput w (M.voteTime S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B ∧
      (∃ W ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree,
        X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq W ∧
          hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C W).h) ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h :=
  (lem59_boxOne_at M F U) S A x R E s (M.voteTime S.C (s + 1)) X B p w kW hkW hBoxP hBoxW hHmax hFw hPropose hParentIn
    hHeadP

/-- `lem59_boxTwo` with `w`'s state read at its tick to a clock value `c` in place of its
tick to the vote time of slot `s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 2 at both states the root condition is free, and the two least viable heights are
equal because both come from the one justified block. `lem59_boxTwo` is its instance at
`c := voteTime S (s + 1)`. -/
theorem lem59_boxTwo_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s c : ℕ) (B J₀ : Block V) (p w : V)
    -- `w` ticks to the clock value `c` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w c)
    (hBoxP : BoxTwo M S.C (x.tickInput p (M.slotStart S.C (s + 1))) J₀)
    (hBoxW : BoxTwo M S.C (x.tickInput w c) J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      FrameShape M (x.tickInput w c) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      J₀.AncestorEq B.parent ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h := by
  have ⟨iP, hlP, _⟩ := hPropose
  have hInvP := (lem11_node_invariant M F S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p
    (by rw [(tickStep_eq_of_lbl M) x E hlP]; exact E.not_mem_corrupted_of_tick hlP)).1
  have hInvW := (lem11_node_invariant M F S A x R E (x.tickStep w c) w
    (by rw [(tickStep_eq_of_lbl M) x E hkW]; exact E.not_mem_corrupted_of_tick hkW)).1
  have hP := (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxTwo M F) S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) hInvP _ hBoxP
  have hW := (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxTwo M F) S.C S.P S.X (x.tickInput w c) hInvW _ hBoxW
  -- the justified height of a state in box 2 with `J₀` is `J₀`'s chain-state height
  have hJH : ∀ (u : V) (c' : ℕ), BoxTwo M S.C (x.tickInput u c') J₀ →
      (x.tickInput u c').justifiedHeight = (M.chainStateOf S.C J₀).h := fun u c' hBox => by
    obtain ⟨-, hJH, -, -, -⟩ := (GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E (x.tickStep u c') u
    have hJ : (x.tickInput u c').justified = J₀ := hBox.2.2
    have hJH' : JustifiedHeight M S.C (x.tickInput u c') := hJH
    rcases hJH' with hg | hh
    · exact absurd (hJ.symm.trans hg) hJ₀
    · rw [hJ] at hh
      exact hh.symm
  -- the two greatest chain-state heights are `J₀`'s height plus one
  have hmax : hMax M S.C (x.tickInput w c) = hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) := by
    rw [hBoxW.1, hBoxP.1, hJH w c hBoxW, hJH p _ hBoxP]
  rw [hmax] at hW
  -- `B`'s parent is in `p`'s viable tree, so the root `J₀` is an ancestor of it
  have hJP : J₀.AncestorEq B.parent := by
    have hR := ((GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F) S.C S.P S.X
        (x.tickInput p (M.slotStart S.C (s + 1))) hInvP _ _ hP).1
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F)] at hParentIn
    obtain ⟨-, hRB, -⟩ := hParentIn
    rw [hR] at hRB
    exact hRB
  have hfl := (proposal_viable M F U) S A x R E s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, hJP, hfl⟩

/-- Lemma 59 in box 2. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem59_boxTwo_at` at `c := M.voteTime S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 2 at both states the root condition is free, and the two least viable heights are
equal because both come from the one justified block. -/
theorem lem59_boxTwo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B J₀ : Block V) (p w : V)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)))
    (hBoxP : BoxTwo M S.C (x.tickInput p (M.slotStart S.C (s + 1))) J₀)
    (hBoxW : BoxTwo M S.C (x.tickInput w (M.voteTime S.C (s + 1))) J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1))) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      FrameShape M (x.tickInput w (M.voteTime S.C (s + 1))) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1) ∧
      J₀.AncestorEq B.parent ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) - 1 ≤ (M.chainStateOf S.C B).h :=
  (lem59_boxTwo_at M F U) S A x R E s (M.voteTime S.C (s + 1)) B J₀ p w kW hkW hBoxP hBoxW hJ₀ hPropose hParentIn

/-- `lem59_boxThree` with `w`'s state read at its tick to a clock value `c` in place of its
tick to the vote time of slot `s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 3 at both states, with one greatest chain-state height, the two least viable
heights are that height and the honest proposal reaches it; the root condition is the hypothesis on
`w`'s finalized block. `lem59_boxThree` is its instance at `c := voteTime S (s + 1)`. -/
theorem lem59_boxThree_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s c : ℕ) (B : Block V) (p w : V)
    -- `w` ticks to the clock value `c` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w c)
    (hBoxP : BoxThree M (x.tickInput p (M.slotStart S.C (s + 1))))
    (hBoxW : BoxThree M (x.tickInput w c))
    (hHmax : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) =
      hMax M S.C (x.tickInput w c))
    (hFw : (x.tickInput w c).finalized.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1)))
        (x.tickInput p (M.slotStart S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1)))) ∧
      FrameShape M (x.tickInput w c)
        (x.tickInput w c).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1)))) ∧
      (x.tickInput w c).finalized.AncestorEq B ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤ (M.chainStateOf S.C B).h := by
  have ⟨iP, hlP, _⟩ := hPropose
  have hInvP := (lem11_node_invariant M F S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p
    (by rw [(tickStep_eq_of_lbl M) x E hlP]; exact E.not_mem_corrupted_of_tick hlP)).1
  have hInvW := (lem11_node_invariant M F S A x R E (x.tickStep w c) w
    (by rw [(tickStep_eq_of_lbl M) x E hkW]; exact E.not_mem_corrupted_of_tick hkW)).1
  have hP := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) hInvP hBoxP).2
  have hW := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X (x.tickInput w c) hInvW hBoxW).2
  rw [← hHmax] at hW
  have hfl := (proposal_viable M F U) S A x R E s B p hPropose hParentIn
  rw [hP.2] at hfl
  exact ⟨hP, hW, hFw, hfl⟩

/-- Lemma 59 in box 3. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem59_boxThree_at` at `c := M.voteTime S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 3 at both states, with one greatest chain-state height, the two least viable
heights are that height and the honest proposal reaches it; the root condition is the hypothesis on
`w`'s finalized block. -/
theorem lem59_boxThree (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (p w : V)
    -- `w` ticks to the vote time of slot `s + 1` at the step `kW`
    (kW : ℕ) (hkW : x.lbl kW = Event.tick w (M.voteTime S.C (s + 1)))
    (hBoxP : BoxThree M (x.tickInput p (M.slotStart S.C (s + 1))))
    (hBoxW : BoxThree M (x.tickInput w (M.voteTime S.C (s + 1))))
    (hHmax : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) =
      hMax M S.C (x.tickInput w (M.voteTime S.C (s + 1))))
    (hFw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) :
    FrameShape M (x.tickInput p (M.slotStart S.C (s + 1)))
        (x.tickInput p (M.slotStart S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1)))) ∧
      FrameShape M (x.tickInput w (M.voteTime S.C (s + 1)))
        (x.tickInput w (M.voteTime S.C (s + 1))).finalized
        (hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1)))) ∧
      (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq B ∧
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) ≤ (M.chainStateOf S.C B).h :=
  (lem59_boxThree_at M F U) S A x R E s (M.voteTime S.C (s + 1)) B p w kW hkW hBoxP hBoxW hHmax hFw hPropose hParentIn

/-- The hypotheses of Lemma 55 on the viable tree and the record, from `FrameShape` of `v`'s FG
state before a time `t`: `lem61_frame_hypotheses` with `t` in place of the support cutoff of slot
`s + 1`, which its proof does not read.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time `v`'s state is read;
- `B`: the block; `v`: the validator; `ρ`, `φ`: the root and the `head_height_floor` value that
  `FrameShape` gives.

Read aloud: a frame shape at `v`'s state before `t` with its root `B` or an ancestor of `B` and its
least viable height at most `B`'s chain-state height puts `B` in `v`'s viable tree, and the
condition on the justified height or the lock at `B`'s height gives Lemma 55's lock hypothesis. -/
theorem frame_hypotheses_at (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (B : Block V) (v : V) (ρ : Block V) (φ : Height)
    (hShape : FrameShape M (x.stateBefore t v) ρ φ)
    (hRootV : ρ.AncestorEq B)
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h)
    (hBin : B ∈ (x.stateBefore t v).tree)
    (hLockBox : (x.stateBefore t v).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.stateBefore t v).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.stateBefore t v).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore t v)) (M.fg_to_ac (x.stateBefore t v)).tree ∧
      ((x.stateBefore t v).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.stateBefore t v).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.stateBefore t v).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) := by
  refine ⟨(mem_viable_tree_of_frameShape_of_stateBefore M F) S A x R E _ v B ρ φ hShape hRootV hBHeight
    hBin, ?_⟩
  rcases hLockBox with hlt | hnone | hlock
  · exact Or.inl ((GoldilocksCorrectness.Record.Statements.Executions.lock_none_of_h_j_lt_of_stateBefore M F) S A x R E _ v _ hlt)
  · exact Or.inl hnone
  · exact Or.inr ⟨hlock, (GoldilocksCorrectness.Record.Statements.Executions.lockNamesSent_of_stateBefore M F) S A x R E _ v _ _ hlock⟩

/-- `lem61_boxOne` with `v`'s state read before a time `t_v` in place of the support cutoff of slot
`s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 1 the node holds no lock at `B`'s height, because its justified height is less
than its least viable height, which is at most `B`'s height. `lem61_boxOne` is its instance at
`t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxOne_at (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t_v : ℕ) (B : Block V) (v : V)
    (hBox : BoxOne M S.C (x.stateBefore t_v v))
    (hFv : (x.stateBefore t_v v).finalized.AncestorEq B)
    (hBHeight : hMax M S.C (x.stateBefore t_v v) - 1 ≤ (M.chainStateOf S.C B).h)
    (hBin : B ∈ (x.stateBefore t_v v).tree) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore t_v v))
        (M.fg_to_ac (x.stateBefore t_v v)).tree ∧
      ((x.stateBefore t_v v).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.stateBefore t_v v).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.stateBefore t_v v).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) := by
  have hInv := (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t_v) v).1
  have hShape := ((GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxOne_of_core M F) S.C S.P S.X
        (x.stateBefore t_v v) hInv hBox).2
  have hb : (x.stateBefore t_v v).justifiedHeight + 1 <
      hMax M S.C (x.stateBefore t_v v) := hBox
  have hlt : (x.stateBefore t_v v).justifiedHeight < (M.chainStateOf S.C B).h := by
    unfold Height at *
    omega
  exact (frame_hypotheses_at M F) S A x R E t_v B v _ _
    hShape hFv hBHeight hBin (Or.inl hlt)

/-- Lemma 61 in box 1. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem61_boxOne_at` at `t_v := M.supportCutoff S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 1 the node holds no lock at `B`'s height, because its justified height is less
than its least viable height, which is at most `B`'s height. -/
theorem lem61_boxOne (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s : ℕ) (B : Block V) (v : V)
    (hBox : BoxOne M S.C (x.stateBefore (M.supportCutoff S.C (s + 1)) v))
    (hFv : (x.stateBefore (M.supportCutoff S.C (s + 1)) v).finalized.AncestorEq B)
    (hBHeight : hMax M S.C (x.stateBefore (M.supportCutoff S.C (s + 1)) v) - 1 ≤
      (M.chainStateOf S.C B).h)
    (hBin : B ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).tree) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v))
        (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v)).tree ∧
      ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) :=
  (lem61_boxOne_at M F) S A x R E (M.supportCutoff S.C (s + 1)) B v hBox hFv hBHeight hBin

/-- `lem61_boxTwo` with `v`'s state read before a time `t_v` in place of the support cutoff of slot
`s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 2 the lock at `B`'s height, when that height is the greatest chain-state height
minus one, is on the entry block of `B`'s height, as the hypothesis on the lock says. `lem61_boxTwo`
is its instance at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxTwo_at (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t_v : ℕ) (B J₀ : Block V) (v : V)
    (hBox : BoxTwo M S.C (x.stateBefore t_v v) J₀)
    (hJB : J₀.AncestorEq B)
    (hBHeight : hMax M S.C (x.stateBefore t_v v) - 1 ≤ (M.chainStateOf S.C B).h)
    (hLockT : ∀ T' : BlockId,
      (x.stateBefore t_v v).sentLock
        (hMax M S.C (x.stateBefore t_v v) - 1) = some T' →
      T' = (M.chainStateOf S.C B).T_h.root)
    (hBin : B ∈ (x.stateBefore t_v v).tree) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore t_v v))
        (M.fg_to_ac (x.stateBefore t_v v)).tree ∧
      ((x.stateBefore t_v v).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.stateBefore t_v v).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.stateBefore t_v v).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) := by
  have hInv := (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t_v) v).1
  have hShape := (GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxTwo_of_core M F) S.C S.P S.X
        (x.stateBefore t_v v) hInv _ hBox
  have hmax := hBox.1
  by_cases hlt : (x.stateBefore t_v v).justifiedHeight < (M.chainStateOf S.C B).h
  · exact (frame_hypotheses_at M F) S A x R E t_v B v _ _
      hShape hJB hBHeight hBin (Or.inl hlt)
  · -- `B`'s height is the greatest chain-state height minus one, the justification height
    have hH : (M.chainStateOf S.C B).h =
        hMax M S.C (x.stateBefore t_v v) - 1 := by
      unfold Height at *
      omega
    by_cases hl : (x.stateBefore t_v v).sentLock (M.chainStateOf S.C B).h = none
    · exact (frame_hypotheses_at M F) S A x R E t_v B v _ _
        hShape hJB hBHeight hBin (Or.inr (Or.inl hl))
    · obtain ⟨T', hT'⟩ := Option.ne_none_iff_exists'.1 hl
      have hTT : T' = (M.chainStateOf S.C B).T_h.root := hLockT T' (by rw [← hH]; exact hT')
      rw [hTT] at hT'
      exact (frame_hypotheses_at M F) S A x R E t_v B v _ _
        hShape hJB hBHeight hBin (Or.inr (Or.inr hT'))

/-- Lemma 61 in box 2. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem61_boxTwo_at` at `t_v := M.supportCutoff S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 2 the lock at `B`'s height, when that height is the greatest chain-state height
minus one, is on the entry block of `B`'s height, as the hypothesis on the lock says. -/
theorem lem61_boxTwo (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s : ℕ) (B J₀ : Block V) (v : V)
    (hBox : BoxTwo M S.C (x.stateBefore (M.supportCutoff S.C (s + 1)) v) J₀)
    (hJB : J₀.AncestorEq B)
    (hBHeight : hMax M S.C (x.stateBefore (M.supportCutoff S.C (s + 1)) v) - 1 ≤
      (M.chainStateOf S.C B).h)
    (hLockT : ∀ T' : BlockId,
      (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock
        (hMax M S.C (x.stateBefore (M.supportCutoff S.C (s + 1)) v) - 1) = some T' →
      T' = (M.chainStateOf S.C B).T_h.root)
    (hBin : B ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).tree) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v))
        (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v)).tree ∧
      ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) :=
  (lem61_boxTwo_at M F) S A x R E (M.supportCutoff S.C (s + 1)) B J₀ v hBox hJB hBHeight hLockT hBin

/-- `lem61_boxThree` with `v`'s state read before a time `t_v` in place of the support cutoff of
slot `s + 1`. The proof; the audited statement is in `Statements/Executions/BoxStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 3 the node holds no lock at `B`'s height, because its justified height is the
greatest chain-state height minus one and `B`'s height is at least the greatest. `lem61_boxThree` is
its instance at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxThree_at (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t_v : ℕ) (B : Block V) (v : V)
    (hBox : BoxThree M (x.stateBefore t_v v))
    (hFv : (x.stateBefore t_v v).finalized.AncestorEq B)
    (hBHeight : hMax M S.C (x.stateBefore t_v v) ≤ (M.chainStateOf S.C B).h)
    (hBin : B ∈ (x.stateBefore t_v v).tree) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore t_v v))
        (M.fg_to_ac (x.stateBefore t_v v)).tree ∧
      ((x.stateBefore t_v v).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.stateBefore t_v v).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.stateBefore t_v v).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) := by
  have hInv := (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t_v) v).1
  obtain ⟨hmax, hShape⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxThree_of_core M F) S.C S.P S.X
        (x.stateBefore t_v v) hInv hBox
  have hlt : (x.stateBefore t_v v).justifiedHeight < (M.chainStateOf S.C B).h := by
    unfold Height at *
    omega
  exact (frame_hypotheses_at M F) S A x R E t_v B v _ _
    hShape hFv hBHeight hBin (Or.inl hlt)

/-- Lemma 61 in box 3. The proof; the audited statement is in
`Statements/Executions/BoxStatements.lean`.

It is the instance of `lem61_boxThree_at` at `t_v := M.supportCutoff S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: in box 3 the node holds no lock at `B`'s height, because its justified height is the
greatest chain-state height minus one and `B`'s height is at least the greatest. -/
theorem lem61_boxThree (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s : ℕ) (B : Block V) (v : V)
    (hBox : BoxThree M (x.stateBefore (M.supportCutoff S.C (s + 1)) v))
    (hFv : (x.stateBefore (M.supportCutoff S.C (s + 1)) v).finalized.AncestorEq B)
    (hBHeight : hMax M S.C (x.stateBefore (M.supportCutoff S.C (s + 1)) v) ≤
      (M.chainStateOf S.C B).h)
    (hBin : B ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).tree) :
    B ∈ M.viable_tree (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v))
        (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v)).tree ∧
      ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentLock (M.chainStateOf S.C B).h =
            some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) v).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) :=
  (lem61_boxThree_at M F) S A x R E (M.supportCutoff S.C (s + 1)) B v hBox hFv hBHeight hBin

end GoldilocksCorrectness.Record.Proofs.Executions

