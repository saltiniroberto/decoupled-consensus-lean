module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainDefs

@[expose] public section

/-!
# HonestChainDefs, over a model

The definition of `GoldilocksCorrectness/Statements/Executions/HonestChainDefs.lean` over a model
`M`, for an execution `x` of `protocolOf M S`: the slot invariant at slot `s'` restricted to a block
`B`, read at the members of a set `Hon`. Its second clause, the live locks the revocation of slot
`s' + 1` leaves, reads every outcome of the model's tick at the vote time of slot `s' + 1` from a
member that has been awake since that slot's duty window's start (`AwakeFor`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (VoterTreeAt AwakeFor ResolvesAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `HonestChainExtends M S Sched x Hon B s'`: the slot invariant at slot `s'` restricted to the
block `B`, read at the members of `Hon`. Three clauses:

1. every slot-`s'` Goldfish vote a member `u` of `Hon` put on the wire at its tick at the vote time
   of slot `s'` is `u`'s slot-`s'` vote for a block `H_u` of the tree in the state that tick starts
   from (`x.tickInput u (M.voteTime S.C s')`), and `H_u` is `B` or a descendant of `B`;
2. for every member `w` of `Hon` and every answer `A'` of `w`'s revocation of slot `s' + 1`, run on
   the state `w`'s tick to the vote time of slot `s' + 1` starts from
   (`x.tickInput w (M.voteTime S.C (s' + 1))`) with its expired entries removed, the block of every
   lock entry of `A'` live at that vote time is compatible with `B`;
3. every confirmation of slot `s'` a member `v` of `Hon` holds right after the support cutoff of
   slot `s' + 1` (where its update of slot `s' + 1` runs) is `B` or a descendant of `B`.

The definition says nothing about the members' honesty; the theorems that read it assume it.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `Hon`: the validators the clauses are read at; `B`: the block; `s'`: the slot.

Read aloud: at slot `s'`, the votes of the members of `Hon` extend `B`, their live locks do not
conflict with `B`, and their saved confirmations extend `B`.

Clauses 1 and 2 read the state each member's own tick starts from, not the configuration in force at
the vote time's real time: under the two clock bounds the tick to a clock value can come before or
after that real time. -/
def HonestChainExtends (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : Finset V) (B : Block V) (s' : ℕ) : Prop :=
  (∀ u ∈ Hon, ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) →
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u) ∧
  (∀ w ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) →
    ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput w (M.voteTime S.C (s' + 1)))
        ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true → e.B.compatible B = true) ∧
  (∀ v ∈ Hon, ∀ C' : Block V,
    (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
    B.AncestorEq C')

end GoldilocksCorrectness.Record.Statements.Executions

