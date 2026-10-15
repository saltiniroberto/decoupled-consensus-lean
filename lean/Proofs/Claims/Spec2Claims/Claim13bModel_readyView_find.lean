import Proofs.Claims.Spec2Claims.Claim13bModel_token

/-!
# Facts about `Protocol.readyView`: a ready token's root resolves

A token is ready only when its attestation passes the body condition `Protocol.bodyReady`, which
fails for an attestation naming a root that does not resolve in the view's tree.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.bodyReady
  DecoupledConsensusModel.Protocol.interpretedInputs DecoupledConsensusModel.Protocol.latest_window
  DecoupledConsensusModel.Protocol.rawInputs DecoupledConsensusModel.Protocol.readyView

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the token `tok` is in `v`'s ready view of the grade view `gv` for round `r` at the cutoff `c`
    and names the root `root`, then `root` resolves in `gv`'s tree to some block. -/
theorem find_of_mem_readyView (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (c : Time) (v : V) {tok : Protocol.Token (Option BlockId)} {root : BlockId}
    (htok : tok ∈ Protocol.readyView gv F η r c v) (hkey : tok.key = some root) :
    ∃ H : Block V, Block.find? gv.T root = some H := by
  unfold Protocol.readyView Protocol.interpretedInputs at htok
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp htok
  have hready := (Finset.mem_filter.mp hy).2
  rw [token_key] at hkey
  unfold Protocol.bodyReady at hready
  rw [hkey] at hready
  dsimp only at hready
  cases hf : Block.find? gv.T root with
  | none => rw [hf] at hready; exact absurd hready (by simp)
  | some H => exact ⟨H, rfl⟩

end DecoupledConsensusModel.Sts
