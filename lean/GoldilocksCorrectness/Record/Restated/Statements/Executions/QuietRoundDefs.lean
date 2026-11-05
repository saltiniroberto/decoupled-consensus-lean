module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseDefs
public import GoldilocksCorrectness.Statements.Executions.QuietRoundDefs

@[expose] public section

/-!
# QuietRoundDefs, over a model

The definition of `GoldilocksCorrectness/Statements/Executions/QuietRoundDefs.lean` over a model
`M`, for an execution `x` of `protocolOf M S`: the quiet round relative to its own confirmations,
through the next proposal.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `QuietRoundOnConfirmations M S Sched x Hon B s s''`: the round whose first slot is `s`, whose
proposal is `B` and whose next honest round opening slot is `s''` is quiet relative to its own
confirmations, through the next proposal:

- in the state its tick to the vote time of slot `s` starts from, every member of `Hon s` has its
  fork-choice root `B.parent` or an ancestor of it, and its `head_height_floor` at most the
  chain-state height of `B.parent`;
- in the state its tick to `M.supportCutoff S.C (s + 1)` starts from, every member of `Hon s` has
  its fork-choice root `B` or an ancestor of `B`, and its `head_height_floor` at most the
  chain-state height of `B`;
- for every slot `s'` of the round with `s ≤ s'` and `s' + 2 ≤ s''`, every member of
  `Hon (s' + 1)` satisfies `StepFrameAt M S Sched x B s'`;
- for every slot `s'` from `s − 1` with `s' + 2 ≤ s''`, every member of `Hon (s' + 1)` satisfies
  `StepFrameAt M S Sched x C s'` for every confirmation `C` that a member of `Hon σ` saved for a
  slot `σ` from `s − 1` to `s'`: the members of the slot's own set, the updaters of the slot in
  the phase;
- in the state its tick to the start of slot `s''` starts from, the proposer `S.P.proposer s''`
  has its fork-choice root an ancestor of, or equal to, some confirmation `C` of slot `s'' − 2`
  saved by a member of `Hon (s'' − 2)`, the members of the slot's own set, the updaters of the slot in the phase
, and some viable head of its frame is `C` or a descendant of `C`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot.

Read aloud: the members' frames follow the proposal and every confirmation the round saves, and
the next proposer starts its walk on the chain of the last confirmation.

  The first, second and fifth clauses read each
validator's own state at its own tick. -/
def QuietRoundOnConfirmations (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ) : Prop :=
  (∀ w ∈ Hon s, (M.get_fc_root (x.tickInput w (M.voteTime S.C s))).AncestorEq B.parent ∧
    M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h) ∧
  (∀ v ∈ Hon s, (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1)))).AncestorEq B ∧
    M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤
      (M.chainStateOf S.C B).h) ∧
  (∀ s', s ≤ s' → s' + 2 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w) ∧
  (∀ s', s - 1 ≤ s' → s' + 2 ≤ s'' → ∀ σ, s - 1 ≤ σ → σ ≤ s' → ∀ v ∈ Hon σ,
    ∀ C : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ =
      some C →
    ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x C s' w) ∧
  (∃ C : Block V,
    (∃ v ∈ Hon (s'' - 2),
      (x.tickOutput v (M.supportCutoff S.C (s'' - 1))).savedConfirmation (s'' - 2) =
          some C) ∧
    (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).fc_root.AncestorEq C ∧
    ∃ W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).tree,
      W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).viable_heads ∧
      C.AncestorEq W)

/-- A quiet round relative to its own confirmations is a quiet round: its first three clauses.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot.

Read aloud: `QuietRoundOnConfirmations` implies `QuietRound`. -/
theorem quietRound_of_quietRoundOnConfirmations (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ)
    (h : QuietRoundOnConfirmations M S A x Hon B s s'') : QuietRound M S A x Hon B s s'' :=
  ⟨h.1, h.2.1, h.2.2.1⟩

end GoldilocksCorrectness.Record.Statements.Executions

