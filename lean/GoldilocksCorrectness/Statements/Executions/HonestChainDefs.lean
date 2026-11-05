module
public import GoldilocksCorrectness.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Statements.Routines.TickDefs

@[expose] public section

/-!
# The slot invariant restricted to a block: the definition

`HonestChainExtends S Sched x Hon B s'`: at slot `s'`, the votes, the live locks and the saved
confirmations of the members of a set `Hon` of validators are on `B`'s chain or compatible with
`B`. Lemma 79 (`GoldilocksCorrectness/Statements/Executions/HonestChainStatements.lean`) carries it
from slot `s'` to slot `s' + 1`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `HonestChainExtends S Sched x Hon B s'`: the slot invariant at slot `s'` restricted to the
block `B`, read at the members of `Hon`. Three clauses:

1. every slot-`s'` Goldfish vote a member `u` of `Hon` put on the wire at its tick at the vote time
   of slot `s'` is `u`'s slot-`s'` vote for a block `H_u` it holds then, and `H_u` is `B` or a
   descendant of `B`;
2. for every member `w` of `Hon` and every answer `A'` of `w`'s revocation of slot `s' + 1` at the
   vote time of slot `s' + 1`, run on `w`'s AC state then with its expired entries removed, the
   block of every lock entry of `A'` live at that time is compatible with `B`;
3. every confirmation of slot `s'` a member `v` of `Hon` holds right after the support cutoff of
   slot `s' + 1` (where its update of slot `s' + 1` runs) is `B` or a descendant of `B`.

The definition says nothing about the members' honesty; the theorems that read it assume it.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `Hon`: the validators the clauses are read at; `B`: the block; `s'`: the slot.

Read aloud: at slot `s'`, the votes of the members of `Hon` extend `B`, their live locks do not
conflict with `B`, and their saved confirmations extend `B`. -/
def HonestChainExtends (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : Finset V) (B : Block V) (s' : ℕ) : Prop :=
  (∀ u ∈ Hon, ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) →
    ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
      vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u) ∧
  (∀ w ∈ Hon, ∀ A' : ACState V,
    revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 1)) w).A
      ((voteTime S (s' + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
      ((voteTime S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A' →
    ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
        ((voteTime S (s' + 1) : ℕ) : Int) e = true → e.B.compatible B = true) ∧
  (∀ v ∈ Hon, ∀ C' : Block V,
    (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
    B.AncestorEq C')

end GoldilocksCorrectness.Statements.Executions
