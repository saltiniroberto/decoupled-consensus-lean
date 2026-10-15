module
public import Model.Vocabulary.Protocol.ForkChoice.Views
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_beforeCutoff
public import Proofs.Claims.Spec2Claims.Claim13bModel_stampedBefore
public import Proofs.Claims.Spec2Claims.Claim13bModel_GoldfishStore_tau_mk

@[expose] public section

/-!
# Facts on `Protocol.voter_view` and `Protocol.voter_support_view` for a module

The votes of a Goldfish store's slot-`s` bucket that enter the slot-`(s + 1)` voter views.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.voter_view
  DecoupledConsensusModel.Protocol.voter_support_view

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A vote of `gs.pool s` stamped before the view freeze of slot `s` is in the slot-`(s + 1)` raw
    voter view of `gs`. -/
theorem mem_voter_view_of_pool (E : Env V) (gs : Protocol.GoldfishStore V) (s : Slot)
    {u : GoldfishVote V} (hu : u ∈ gs.pool s) {τ : Stamp}
    (hτ : gs.timestamp_vote u = some τ)
    (hlt : τ < ((Protocol.view_freeze E s : Int) : Stamp)) :
    u ∈ Protocol.voter_view E gs (s + 1) := by
  simp only [Protocol.voter_view, Nat.add_sub_cancel, Finset.mem_union]
  refine Or.inl ?_
  rw [mem_beforeCutoff_iff]
  exact ⟨hu, stampedBefore_of_lt hτ hlt⟩

/-- A vote of `gs.pool s` whose head resolves, with both the vote's stamp and its head's stamp
    before the view freeze of slot `s`, is in the slot-`(s + 1)` support voter view of `gs`. -/
theorem mem_voter_support_view_of_pool (E : Env V) (gs : Protocol.GoldfishStore V) (s : Slot)
    {u : GoldfishVote V} (hu : u ∈ gs.pool s) {τ : Stamp}
    (hτ : gs.timestamp_vote u = some τ)
    (hlt : τ < ((Protocol.view_freeze E s : Int) : Stamp))
    {X : Block V} (hX : Block.find? gs.T u.head = some X) (hXs : X.slot ≤ u.slot)
    {σ : Stamp} (hσ : gs.timestamp_block X = some σ)
    (hσlt : σ < ((Protocol.view_freeze E s : Int) : Stamp)) :
    u ∈ Protocol.voter_support_view E gs (s + 1) := by
  simp only [Protocol.voter_support_view, Nat.add_sub_cancel, Finset.mem_union]
  refine Or.inl ?_
  rw [mem_beforeCutoff_iff]
  exact ⟨hu, stampedBefore_of_lt (tau_eq_max_gf gs hX hXs hτ hσ) (max_lt hlt hσlt)⟩

end DecoupledConsensusModel.Sts
