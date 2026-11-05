module
public import GoldilocksCorrectness.Statements.Executions.PhaseDefs

@[expose] public section

/-!
# A quiet round relative to its own confirmations

`QuietRoundOnConfirmations S Sched x Hon B s s''`: the clauses of `QuietRound S Sched x Hon B s s''`
and two more, the frames of the members relative to the confirmations the round's members save,
and the next proposer's fork choice before the start of slot `s''` relative to a confirmation of
slot `s'' − 2`; and `quietRound_of_quietRoundOnConfirmations`, that it implies `QuietRound`.

 the
confirmations of each slot are those the members of the slot's own set save.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `QuietRoundOnConfirmations S Sched x Hon B s s''`: the round whose first slot is `s`, whose
proposal is `B` and whose next honest round opening slot is `s''` is quiet relative to its own
confirmations, through the next proposal:

- before the vote time of slot `s`, every member of `Hon s` has its fork-choice root `B.parent`
  or an ancestor of it, and its `head_height_floor` at most the chain-state height of `B.parent`;
- before the action time `supportCutoff S (s + 1)`, every member of `Hon s` has its fork-choice
  root `B` or an ancestor of `B`, and its `head_height_floor` at most the chain-state height of
  `B`;
- for every slot `s'` of the round with `s ≤ s'` and `s' + 2 ≤ s''`, every member of
  `Hon (s' + 1)` satisfies `StepFrameAt S Sched x B s'`;
- for every slot `s'` from `s − 1` with `s' + 2 ≤ s''`, every member of `Hon (s' + 1)` satisfies
  `StepFrameAt S Sched x C s'` for every confirmation `C` that a member of `Hon σ` saved for a
  slot `σ` from `s − 1` to `s'`: the members of the slot's own set, the updaters of the slot in
  the phase;
- before the start of slot `s''`, the proposer `S.P.proposer s''` has its fork-choice root an
  ancestor of, or equal to, some confirmation `C` of slot `s'' − 2` saved by a member of
  `Hon (s'' − 2)`, the members of the slot's own set, the updaters of the slot in the phase
, and some viable head of its frame is `C` or a descendant of `C`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot.

Read aloud: the members' frames follow the proposal and every confirmation the round saves, and
the next proposer starts its walk on the chain of the last confirmation.

  -/
def QuietRoundOnConfirmations (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ) : Prop :=
  (∀ w ∈ Hon s, (get_fc_root (stateBefore x (voteTime S s) w).S).AncestorEq B.parent ∧
    head_height_floor (stateBefore x (voteTime S s) w).S ≤ (chainStateOf S.C B.parent).h) ∧
  (∀ v ∈ Hon s, (get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S).AncestorEq B ∧
    head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S ≤ (chainStateOf S.C B).h) ∧
  (∀ s', s ≤ s' → s' + 2 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w) ∧
  (∀ s', s - 1 ≤ s' → s' + 2 ≤ s'' → ∀ σ, s - 1 ≤ σ → σ ≤ s' → ∀ v ∈ Hon σ,
    ∀ C : Block V, (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C →
    ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x C s' w) ∧
  (∃ C : Block V,
    (∃ v ∈ Hon (s'' - 2),
      (stateBefore x (supportCutoff S (s'' - 1) + 1) v).A.saved_confirmation (s'' - 2) = some C) ∧
    (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).fc_root.AncestorEq C ∧
    ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).viable_heads ∧
      C.AncestorEq W)

/-- A quiet round relative to its own confirmations is a quiet round: its first three clauses.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot.

Read aloud: `QuietRoundOnConfirmations` implies `QuietRound`. -/
theorem quietRound_of_quietRoundOnConfirmations (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ)
    (h : QuietRoundOnConfirmations S Sched x Hon B s s'') : QuietRound S Sched x Hon B s s'' :=
  ⟨h.1, h.2.1, h.2.2.1⟩

end GoldilocksCorrectness.Statements.Executions
