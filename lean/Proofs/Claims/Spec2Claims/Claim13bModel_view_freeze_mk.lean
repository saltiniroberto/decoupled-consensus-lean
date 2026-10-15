module
public import Model.Vocabulary.Protocol.Schedule
public import Proofs.Claims.ModelIrreducible
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Facts on `Protocol.view_freeze` against the support cutoff

The view freeze of a slot compared with the slot's support cutoff.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.view_freeze
  DecoupledConsensusModel.Protocol.support_cutoff

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The support cutoff of slot `s` is strictly before its view freeze: `t_s + 2Δ < t_s + 3Δ`. -/
theorem support_cutoff_lt_view_freeze (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s < Protocol.view_freeze E s := by
  have hd := E.Δ_pos
  show (E.t s + 2 * E.Δ : Int) < E.t s + 3 * E.Δ
  linarith

end DecoupledConsensusModel.Sts
