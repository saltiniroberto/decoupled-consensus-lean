import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalWalkTransportCore
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.ghost`

Lemmas that unfold the walk `Protocol.ghost` and the definitions it is written over
(`Protocol.ghost_walk`, `Protocol.ghost_step`, `Protocol.ghost_children`), including the transfer of
one walk's result to another walk when the two scores agree on the descendants of the block the
comparison starts from.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Execution.RootInjectiveBelow DecoupledConsensusModel.Protocol.ghost
  DecoupledConsensusModel.Protocol.ghost_children DecoupledConsensusModel.Protocol.ghost_walk

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If `A ⪯ C`, `C ≠ A`, and `C` is an ancestor of the result of the fuelled walk from `A` through
    `tree`, then `C` is in `tree`. -/
theorem mem_tree_of_between_ghost_walk {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} :
    ∀ (n : Nat) (A C : Block V), Block.Preceq A C →
      Block.Preceq C (Protocol.ghost_walk tree score eligible n A) → C ≠ A → C ∈ tree := by
  intro n
  induction n with
  | zero =>
      intro A C hAC hCw hne
      simp only [Protocol.ghost_walk] at hCw
      exact absurd (Block.preceq_antisymm hCw hAC) hne
  | succ n ih =>
      intro A C hAC hCw hne
      cases hstep : Protocol.ghost_step tree score eligible A with
      | none =>
          simp only [Protocol.ghost_walk, hstep] at hCw
          exact absurd (Block.preceq_antisymm hCw hAC) hne
      | some D =>
          have hw : Protocol.ghost_walk tree score eligible (n + 1) A =
              Protocol.ghost_walk tree score eligible n D := by
            simp only [Protocol.ghost_walk, hstep]
          rw [hw] at hCw
          obtain ⟨hDmem, hDpar, -⟩ := Protocol.ghost_step_child hstep
          have hDw := Protocol.ghost_walk_preceq tree score eligible n D
          rcases Block.preceq_linear hCw hDw with hCD | hDC
          · have hdD : D.depth = A.depth + 1 := Protocol.depth_of_parent? hDpar
            have hle := Block.preceq_depth_le hAC
            have hAC' : A.depth ≠ C.depth := fun heq =>
              hne (Block.preceq_eq_of_depth_le hAC (by omega)).symm
            have hCd := Block.preceq_depth_le hCD
            have hEq : C = D := Block.preceq_eq_of_depth_le hCD (by omega)
            rw [hEq]
            exact hDmem
          · by_cases hCD : C = D
            · rw [hCD]
              exact hDmem
            · exact ih D C hDC hCw hCD

omit [Fintype V] in
/-- If `A ⪯ C`, `C ≠ A`, and `C` is an ancestor of `Protocol.ghost A tree score eligible`, then `C`
    is in `tree`. -/
theorem mem_tree_of_between_ghost {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {A C : Block V} (hAC : Block.Preceq A C)
    (hCw : Block.Preceq C (Protocol.ghost A tree score eligible)) (hne : C ≠ A) :
    C ∈ tree :=
  mem_tree_of_between_ghost_walk tree.card A C hAC hCw hne

omit [Fintype V] in
/-- If the walk from `A` through `tree` returns a descendant of `pivot`, then from every block `X`
    with `A ⪯ X ⪯ pivot` and `X ≠ pivot` the walk's next step is a child `C` of `X` with
    `C ⪯ pivot`. -/
theorem ghost_step_toward_of_passes {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {A pivot X : Block V}
    (hpasses : Block.Preceq pivot (Protocol.ghost A tree score eligible))
    (hAX : Block.Preceq A X) (hXP : Block.Preceq X pivot) (hne : X ≠ pivot) :
    ∃ C, Protocol.ghost_step tree score eligible X = some C ∧ Block.Preceq C pivot := by
  let R := Protocol.ghost A tree score eligible
  have hPR : Block.Preceq pivot R := hpasses
  have hXR : Block.Preceq X R := Block.preceq_trans hXP hPR
  have hXneR : X ≠ R := by
    intro hEq
    have hPX : Block.Preceq pivot X := by
      rw [hEq]
      exact hPR
    exact hne (Block.preceq_antisymm hXP hPX)
  obtain ⟨C, hstep, hCR⟩ := Protocol.ghost_walk_step_towards_result
    tree.card A R X (by rfl) hAX hXR hXneR
  refine ⟨C, hstep, ?_⟩
  rcases Block.preceq_linear hCR hPR with hCP | hPC
  · exact hCP
  · have hchild := Protocol.ghost_step_child hstep
    have hCdepth : C.depth = X.depth + 1 := Protocol.depth_of_parent? hchild.2.1
    have hXdepth : X.depth < pivot.depth := by
      have hle := Block.preceq_depth_le hXP
      have hneq : X.depth ≠ pivot.depth := by
        intro heq
        exact hne (Block.preceq_eq_of_depth_le hXP (by omega))
      omega
    have hEq : pivot = C := Block.preceq_eq_of_depth_le hPC (by omega)
    rw [← hEq]
    exact Block.preceq_self pivot

omit [Fintype V] in
/-- If `B`'s parent is `P` and `X ≠ P`, the walk's step from `X` through `tree` with `B` removed
    equals its step from `X` through `tree`. -/
theorem ghost_step_erase_of_ne {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {B P X : Block V} (hpar : B.parent? = some P) (hne : X ≠ P) :
    Protocol.ghost_step (tree.erase B) score eligible X =
      Protocol.ghost_step tree score eligible X := by
  have hch : Protocol.ghost_children (tree.erase B) eligible X =
      Protocol.ghost_children tree eligible X := by
    ext C
    simp only [Protocol.ghost_children, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hC⟩, h⟩
      exact ⟨hC, h⟩
    · rintro ⟨hC, hp, he⟩
      refine ⟨⟨?_, hC⟩, hp, he⟩
      rintro rfl
      rw [hpar, Option.some.injEq] at hp
      exact hne hp.symm
  rw [Protocol.ghost_step, Protocol.ghost_step, hch]

omit [Fintype V] in
/-- If the source walk from `sourceAnchor` returns `H`, `sourceAnchor ⪯ targetAnchor ⪯ H`, the chain
    from `targetAnchor` to `H` lies in the target tree, along that chain the child the source walk
    takes is one the target admits and every child the target admits is one the source admits, and
    the two scores agree on the descendants of `targetAnchor`, then the target walk from
    `targetAnchor` returns `H` and admits no child of `H` in the target tree. -/
theorem ghost_transport_of_source_scoresFrom
    {sourceTree targetTree : Finset (Block V)}
    {sourceScore targetScore : Block V → Nat}
    {sourceEligible targetEligible : Block V → Bool}
    {sourceAnchor targetAnchor H : Block V}
    (hsourceRoot : RootInjectiveBelow sourceTree)
    (htargetRoot : RootInjectiveBelow targetTree)
    (hsource : Protocol.ghost sourceAnchor sourceTree sourceScore sourceEligible = H)
    (hanchors : Block.Preceq sourceAnchor targetAnchor ∧ Block.Preceq targetAnchor H)
    (hpath : ∀ C : Block V,
      Block.Preceq targetAnchor C → C ≠ targetAnchor → Block.Preceq C H → C ∈ targetTree)
    (hpersist : ∀ X C : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      Protocol.ghost_step sourceTree sourceScore sourceEligible X = some C →
      Block.Preceq C H →
      C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ X C : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H →
      C ∈ targetTree → C.parent? = some X → targetEligible C = true →
      C ∈ sourceTree ∧ sourceEligible C = true)
    (hscore : ∀ C, Block.Preceq targetAnchor C → C ∈ sourceTree → C ∈ targetTree →
      targetScore C = sourceScore C) :
    (∀ C ∈ targetTree, C.parent? = some H → targetEligible C = false) ∧
      Protocol.ghost targetAnchor targetTree targetScore targetEligible = H := by
  have hsourceSteps : ∀ X : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      ∃ C, Protocol.ghost_step sourceTree sourceScore sourceEligible X = some C ∧
        Block.Preceq C H := by
    intro X hAX hXH hne
    apply Protocol.ghost_walk_step_towards_result sourceTree.card sourceAnchor H X
    · simpa only [Protocol.ghost] using hsource
    · exact Block.preceq_trans hanchors.1 hAX
    · exact hXH
    · exact hne
  have htargetStep : ∀ X : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      ∃ C, Protocol.ghost_step targetTree targetScore targetEligible X = some C ∧
        Block.Preceq C H := by
    intro X hAX hXH hne
    obtain ⟨C, hsourceStep, hCH⟩ := hsourceSteps X hAX hXH hne
    have hkeep := hpersist X C hAX hXH hne hsourceStep hCH
    have hsourceChild := Protocol.ghost_step_child hsourceStep
    refine ⟨C, ?_, hCH⟩
    rw [Protocol.ghost_step] at hsourceStep ⊢
    have htargetChildRoot : RootInjectiveBelow
        (Protocol.ghost_children targetTree targetEligible X) := by
      intro A D hA hD hroot
      apply htargetRoot A D
      · obtain ⟨Y, hY, hAY⟩ := hA
        exact ⟨Y, (Finset.mem_filter.mp hY).1, hAY⟩
      · obtain ⟨Y, hY, hDY⟩ := hD
        exact ⟨Y, (Finset.mem_filter.mp hY).1, hDY⟩
      · exact hroot
    apply Protocol.argmax?_transport_of_subset htargetChildRoot hsourceStep
    · rw [Protocol.ghost_children, Finset.mem_filter]
      exact ⟨hkeep.1, hsourceChild.2.1, hkeep.2⟩
    · intro D hD
      rw [Protocol.ghost_children, Finset.mem_filter] at hD ⊢
      have href := hreflect X D hAX hXH hD.1 hD.2.1 hD.2.2
      exact ⟨href.1, hD.2.1, href.2⟩
    · intro D hD
      rw [Protocol.ghost_children, Finset.mem_filter] at hD
      have href := hreflect X D hAX hXH hD.1 hD.2.1 hD.2.2
      exact hscore D (Block.preceq_trans hAX (Protocol.preceq_of_parent? hD.2.1)) href.1 hD.1
  have hstopped : ∀ C ∈ targetTree,
      C.parent? = some H → targetEligible C = false := by
    intro C hC hparent
    cases helig : targetEligible C with
    | false => rfl
    | true =>
        have href := hreflect H C hanchors.2 (Block.preceq_self H) hC hparent helig
        have hfalse := Proofs.HealingSurface.eligible_child_false_at_ghost_result
          hsourceRoot href.1 (show C.parent? = some
            (Protocol.ghost sourceAnchor sourceTree sourceScore sourceEligible) by
              rw [hsource]
              exact hparent)
        rw [href.2] at hfalse
        contradiction
  refine ⟨hstopped, ?_⟩
  exact Protocol.ghost_reaches hanchors.2 hpath (Protocol.ghost_step_none hstopped) htargetStep

omit [Fintype V] in
/-- If the source walk from `sourceAnchor` returns `H`, `sourceAnchor ⪯ pivot`,
    `targetAnchor ⪯ pivot ⪯ H`, the target walk steps toward `pivot` from every block of the chain
    strictly before it, from `pivot` on the two walks have matching children, and the two scores
    agree on the descendants of `pivot`, then the target walk from `targetAnchor` returns `H` and
    admits no child of `H` in the target tree. -/
theorem ghost_transport_via_pivot_scoresFrom
    {sourceTree targetTree : Finset (Block V)}
    {sourceScore targetScore : Block V → Nat}
    {sourceEligible targetEligible : Block V → Bool}
    {sourceAnchor targetAnchor pivot H : Block V}
    (hsourceRoot : RootInjectiveBelow sourceTree)
    (htargetRoot : RootInjectiveBelow targetTree)
    (hsource : Protocol.ghost sourceAnchor sourceTree sourceScore sourceEligible = H)
    (hanchors : Block.Preceq sourceAnchor pivot ∧
      Block.Preceq targetAnchor pivot ∧ Block.Preceq pivot H)
    (hpath : ∀ C : Block V,
      Block.Preceq targetAnchor C → C ≠ targetAnchor → Block.Preceq C H → C ∈ targetTree)
    (hprefix : ∀ X : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X pivot → X ≠ pivot →
      ∃ C, Protocol.ghost_step targetTree targetScore targetEligible X = some C ∧
        Block.Preceq C pivot)
    (hpersist : ∀ X C : Block V,
      Block.Preceq pivot X → Block.Preceq X H → X ≠ H →
      Protocol.ghost_step sourceTree sourceScore sourceEligible X = some C →
      Block.Preceq C H →
      C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ X C : Block V,
      Block.Preceq pivot X → Block.Preceq X H →
      C ∈ targetTree → C.parent? = some X → targetEligible C = true →
      C ∈ sourceTree ∧ sourceEligible C = true)
    (hscore : ∀ C, Block.Preceq pivot C → C ∈ sourceTree → C ∈ targetTree →
      targetScore C = sourceScore C) :
    (∀ C ∈ targetTree, C.parent? = some H → targetEligible C = false) ∧
      Protocol.ghost targetAnchor targetTree targetScore targetEligible = H := by
  have hpathPivot : ∀ C : Block V,
      Block.Preceq pivot C → C ≠ pivot → Block.Preceq C H → C ∈ targetTree := by
    intro C hPC hne hCH
    apply hpath C (Block.preceq_trans hanchors.2.1 hPC) _ hCH
    intro hCt
    subst C
    exact hne (Block.preceq_antisymm hanchors.2.1 hPC)
  obtain ⟨hstopped, hsuffix⟩ := ghost_transport_of_source_scoresFrom
    hsourceRoot htargetRoot hsource ⟨hanchors.1, hanchors.2.2⟩
      hpathPivot hpersist hreflect hscore
  have hsuffixStep : ∀ X : Block V,
      Block.Preceq pivot X → Block.Preceq X H → X ≠ H →
      ∃ C, Protocol.ghost_step targetTree targetScore targetEligible X = some C ∧
        Block.Preceq C H := by
    intro X hPX hXH hne
    apply Protocol.ghost_walk_step_towards_result targetTree.card pivot H X
    · simpa only [Protocol.ghost] using hsuffix
    · exact hPX
    · exact hXH
    · exact hne
  have htargetStep : ∀ X : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      ∃ C, Protocol.ghost_step targetTree targetScore targetEligible X = some C ∧
        Block.Preceq C H := by
    intro X hAX hXH hne
    rcases Block.preceq_linear hXH hanchors.2.2 with hXP | hPX
    · by_cases hEq : X = pivot
      · subst X
        exact hsuffixStep pivot (Block.preceq_self pivot) hanchors.2.2 hne
      · obtain ⟨C, hstep, hCP⟩ := hprefix X hAX hXP hEq
        exact ⟨C, hstep, Block.preceq_trans hCP hanchors.2.2⟩
    · exact hsuffixStep X hPX hXH hne
  refine ⟨hstopped, ?_⟩
  exact Protocol.ghost_reaches
    (Block.preceq_trans hanchors.2.1 hanchors.2.2) hpath
      (Protocol.ghost_step_none hstopped) htargetStep

omit [Fintype V] in
/-- If the source walk from `Ap` through `Tp` returns `P`, the target walk from `Av` through `Tv`
    returns a descendant of `Y` with `Y ⪯ P`, the two walks have matching children on the chain
    from `Y` to `P`, the scores agree on the descendants of `Y`, and `B` is a child of `P` in `Tv`
    admitted by the target and the parent of no block of `Tv`, then the target walk from `Av`
    through `Tv` returns `B`. -/
theorem ghost_eq_child_of_pivot
    {Tp Tv : Finset (Block V)} {scp scv : Block V → Nat} {elp elv : Block V → Bool}
    {Ap Av Y P B : Block V}
    (hrootP : RootInjectiveBelow Tp) (hrootV : RootInjectiveBelow Tv)
    (hsource : Protocol.ghost Ap Tp scp elp = P)
    (hApY : Block.Preceq Ap Y) (hAvY : Block.Preceq Av Y) (hYP : Block.Preceq Y P)
    (hpasses : Block.Preceq Y (Protocol.ghost Av Tv scv elv))
    (hpathV : ∀ C, Block.Preceq Y C → C ≠ Y → Block.Preceq C P → C ∈ Tv)
    (hpersist : ∀ X C, Block.Preceq Y X → Block.Preceq X P → C.parent? = some X →
      C ∈ Tp → elp C = true → Block.Preceq C P → elv C = true)
    (hreflect : ∀ X C, Block.Preceq Y X → Block.Preceq X P → C ∈ Tv → C ≠ B →
      C.parent? = some X → elv C = true → C ∈ Tp ∧ elp C = true)
    (hscore : ∀ C, Block.Preceq Y C → C ∈ Tp → C ∈ Tv → scv C = scp C)
    (hB : B ∈ Tv) (hBpar : B.parent? = some P) (hBel : elv B = true)
    (hfresh : ∀ C ∈ Tv, C.parent? ≠ some B) :
    Protocol.ghost Av Tv scv elv = B := by
  have hBdepth : B.depth = P.depth + 1 := Protocol.depth_of_parent? hBpar
  have hneB : ∀ C, Block.Preceq C P → C ≠ B := by
    intro C hCP hCB
    subst hCB
    have := Block.preceq_depth_le hCP
    omega
  have hrootV' : RootInjectiveBelow (Tv.erase B) := by
    intro A C hA hC hroot
    apply hrootV A C
    · obtain ⟨D, hD, hAD⟩ := hA
      exact ⟨D, Finset.mem_of_mem_erase hD, hAD⟩
    · obtain ⟨D, hD, hCD⟩ := hC
      exact ⟨D, Finset.mem_of_mem_erase hD, hCD⟩
    · exact hroot
  have hpath' : ∀ C : Block V, Block.Preceq Av C → C ≠ Av → Block.Preceq C P →
      C ∈ Tv.erase B := by
    intro C hAC hne hCP
    refine Finset.mem_erase.mpr ⟨hneB C hCP, ?_⟩
    have hprefixMem : Block.Preceq C Y → C ∈ Tv := fun hCY =>
      mem_tree_of_between_ghost hAC (Block.preceq_trans hCY hpasses) hne
    rcases Block.preceq_linear hCP hYP with hCY | hYC
    · exact hprefixMem hCY
    · by_cases hCYeq : C = Y
      · subst hCYeq
        exact hprefixMem (Block.preceq_self _)
      · exact hpathV C hYC hCYeq hCP
  have hprefix' : ∀ X : Block V, Block.Preceq Av X → Block.Preceq X Y → X ≠ Y →
      ∃ C, Protocol.ghost_step (Tv.erase B) scv elv X = some C ∧ Block.Preceq C Y := by
    intro X hAX hXY hne
    have hXP : X ≠ P := by
      intro hXP
      subst hXP
      exact hne (Block.preceq_antisymm hXY hYP)
    rw [ghost_step_erase_of_ne hBpar hXP]
    exact ghost_step_toward_of_passes hpasses hAX hXY hne
  have hpersist' : ∀ X C : Block V, Block.Preceq Y X → Block.Preceq X P → X ≠ P →
      Protocol.ghost_step Tp scp elp X = some C → Block.Preceq C P →
      C ∈ Tv.erase B ∧ elv C = true := by
    intro X C hYX hXP _ hstep hCP
    obtain ⟨hCTp, hCpar, hCel⟩ := Protocol.ghost_step_child hstep
    have hXC : Block.Preceq X C := Protocol.preceq_of_parent? hCpar
    have hYC : Block.Preceq Y C := Block.preceq_trans hYX hXC
    have hCY : C ≠ Y := by
      intro hCY
      subst hCY
      have h1 := Protocol.depth_of_parent? hCpar
      have h2 := Block.preceq_depth_le hYX
      omega
    exact ⟨Finset.mem_erase.mpr ⟨hneB C hCP, hpathV C hYC hCY hCP⟩,
      hpersist X C hYX hXP hCpar hCTp hCel hCP⟩
  have hreflect' : ∀ X C : Block V, Block.Preceq Y X → Block.Preceq X P →
      C ∈ Tv.erase B → C.parent? = some X → elv C = true → C ∈ Tp ∧ elp C = true := by
    intro X C hYX hXP hC hpar hel
    obtain ⟨hCB, hCTv⟩ := Finset.mem_erase.mp hC
    exact hreflect X C hYX hXP hCTv hCB hpar hel
  have hscore' : ∀ C, Block.Preceq Y C → C ∈ Tp → C ∈ Tv.erase B → scv C = scp C :=
    fun C hYC hCp hCv => hscore C hYC hCp (Finset.mem_of_mem_erase hCv)
  obtain ⟨hstopped, hwalk⟩ := ghost_transport_via_pivot_scoresFrom hrootP hrootV' hsource
    ⟨hApY, hAvY, hYP⟩ hpath' hprefix' hpersist' hreflect' hscore'
  have hfresh' : ∀ C ∈ Tv.erase B, C.parent? ≠ some B :=
    fun C hC => hfresh C (Finset.mem_of_mem_erase hC)
  have hins := Proofs.Optimistic.ghost_insert_eq hBpar hBel (Tv.notMem_erase B) hstopped
    hfresh' hwalk
  rw [Finset.insert_erase hB] at hins
  exact hins

end DecoupledConsensusModel.Sts
