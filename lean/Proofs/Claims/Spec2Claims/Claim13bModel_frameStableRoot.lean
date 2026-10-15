import Proofs.Claims.Spec2Claims.Claim13bStepSG

/-!
# Facts about `Protocol.frameStableRoot`

The stable root of a round under the frame contract.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.activePrefix DecoupledConsensusModel.Protocol.frameStableRoot
  DecoupledConsensusModel.Protocol.readFrame

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the stable root of `c` at `st` for round `r` is `G`, then `G` is the store's `get_fg_root`,
    or the frame `Protocol.readFrame c st r` holds a grade-2 root `root` with `G ⪯ root`. -/
theorem frameStableRoot_cases (c : Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) {G : Block V}
    (h : Protocol.frameStableRoot c E hc st r = some G) :
    G = Protocol.get_fg_root st.toFG ∨
      ∃ root : Block V, (Protocol.readFrame c st r).g2 = some (some root) ∧
        Block.Preceq G root := by
  unfold Protocol.frameStableRoot at h
  cases hg : (Protocol.readFrame c st r).g2 with
  | none =>
      simp only [hg, Option.bind_none] at h
      exact Or.inl (Option.some.inj h).symm
  | some o =>
      cases o with
      | none =>
          simp only [hg, Option.bind_some] at h
          exact Or.inl (Option.some.inj h).symm
      | some root =>
          cases hp : Protocol.activePrefix (Protocol.get_filtered_block_tree st.toFG) root with
          | none =>
              simp only [hg, hp, Option.bind_some, id_eq] at h
              exact Or.inl (Option.some.inj h).symm
          | some G' =>
              simp only [hg, hp, Option.bind_some, id_eq] at h
              obtain rfl := Option.some.inj h
              exact Or.inr ⟨root, rfl, activePrefix_preceq hp⟩

/-- If projecting the grade-2 root of the frame `Protocol.readFrame c st r` onto the store's
    candidate tree gives `G`, then the stable root of `c` at `st` for round `r` is `G`. -/
theorem frameStableRoot_of_projection (c : Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) {G : Block V}
    (h : ((Protocol.readFrame c st r).g2.bind id).bind
      (Protocol.activePrefix (Protocol.get_filtered_block_tree st.toFG)) = some G) :
    Protocol.frameStableRoot c E hc st r = some G := by
  unfold Protocol.frameStableRoot
  rw [h]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The stable root `frameStableRoot c E hc st r` is always `some G` for some block `G`. -/
theorem frameStableRoot_exists (c : Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) :
    ∃ G : Block V, Protocol.frameStableRoot c E hc st r = some G := by
  unfold Protocol.frameStableRoot
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end DecoupledConsensusModel.Sts
