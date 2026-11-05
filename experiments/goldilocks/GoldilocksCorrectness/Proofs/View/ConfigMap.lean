module
public import GoldilocksCorrectness.Statements.View.NodeViewDefs
public import StsRefinement.IdCase

@[expose] public section

/-!
# The projection of a configuration and the refinement library's map

`projectConfig f c` (`Statements/View/NodeViewDefs.lean`) maps every node state of `c` by `f` and
keeps the rest. The refinement library's `StsRefinement.Config.map α μ c` maps every node state by
`α` and every message, in the views and in the sent log, by `μ`. This page proves:

- `projectConfig_eq_map`: `projectConfig f c` is `StsRefinement.Config.map f id c`, the map that
  changes the node states only;
- `projectConfig_map`: projecting by `g` a configuration the refinement library mapped by `α` and
  `μ` is mapping it by `g ∘ α` and `μ`, by `rfl`; so a protocol that refines another reads the
  other's statements on the views through `g ∘ α`.

The projection is defined on the view page rather than as `StsRefinement.Config.map f id`, because
that map rebuilds the views with `Finset.image` and the sent log with `Multiset.map`, which read
back as the originals only by a lemma, while `projectConfig` reads back by `rfl`.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Proofs.View

open Framework.StsMultisetLog (Config SignedMsg)
open GoldilocksCorrectness.Statements.View

variable {Node : Type} [DecidableEq Node]

/-- `projectConfig f c` is the refinement library's `Config.map f id c`: the configuration with
every node state mapped by `f` and every message mapped by the identity.

Why: mapping a signed message's object by the identity gives the signed message back, so the views
(`Finset.image_id`) and the sent log (`Multiset.map_id`) come back unchanged.

The variables:
- `f`: the map of node states; `c`: the configuration.

Read aloud: the projection is the refinement library's map that changes only the node states. -/
theorem projectConfig_eq_map {Msg St St' : Type} [DecidableEq Msg] (f : (n : St) → St')
    (c : Config Node Msg St) : projectConfig f c = StsRefinement.Config.map f id c := by
  have hid : StsRefinement.SignedMsg.mapMsg (Node := Node) (id : Msg → Msg) = id :=
    funext fun _ => rfl
  simp only [projectConfig, StsRefinement.Config.map, hid, Finset.image_id, Multiset.map_id]

/-- Projecting by `g` the configuration `StsRefinement.Config.map α μ c` is
`StsRefinement.Config.map (g ∘ α) μ c`.

The variables:
- `g`: the map of the refined protocol's node states; `α`: the map of node states of a refinement;
  `μ`: its map of messages; `c`: a configuration of the refining protocol.

Read aloud: a refining protocol's configuration, mapped to the refined protocol and then read
through `g`, is its own configuration read through `g ∘ α`. -/
theorem projectConfig_map {Msg₁ Msg₂ St₁ St₂ St₃ : Type} [DecidableEq Msg₁] [DecidableEq Msg₂]
    (g : (n : St₂) → St₃) (α : (n : St₁) → St₂) (μ : (m : Msg₁) → Msg₂)
    (c : Config Node Msg₁ St₁) :
    projectConfig g (StsRefinement.Config.map α μ c) = StsRefinement.Config.map (g ∘ α) μ c :=
  rfl

end GoldilocksCorrectness.Proofs.View
