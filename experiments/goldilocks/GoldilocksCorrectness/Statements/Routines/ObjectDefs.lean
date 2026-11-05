module
public import Goldilocks.Broadcast

@[expose] public section

/-!
# Objects a block carries, and duties that answer

`carries o o'`: the object `o` is a block and `o'` is one of the Goldfish votes or attestations
it includes; `Wiring.DREBOutcomesOk d`: the failure is not among the outcomes of the duty `d`, and
an outcome exists. Nothing is proved here.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- `carries o o'`: the object `o` is a block and `o'` is one of the Goldfish votes it includes,
as a Goldfish-vote object, or one of the attestations it includes, as an attestation object.

The variables:
- `o`: the carrying object; `o'`: the carried object.

Read aloud: a block carries each Goldfish vote and each attestation it includes; nothing else
carries anything. -/
def carries : NamedObject V → NamedObject V → Prop
  | .block B, o' =>
      (∃ vote ∈ B.votes, o' = NamedObject.gfVote vote) ∨
        (∃ a ∈ B.attestations, o' = NamedObject.attest a)
  | _, _ => False

end

end GoldilocksCorrectness.Statements.Routines

namespace GoldilocksCorrectness.Wiring

section

open Goldilocks (NamedObject DREB)

/-- `DREBOutcomesOk d`: the failure is not among the outcomes of `d`, and an outcome exists.

Read aloud: whatever the duty does, it answers; and it does something. -/
def DREBOutcomesOk {V α : Type} (d : DREB V α) : Prop :=
  (∀ r ∈ d.outcomes, ∃ p : α × List (NamedObject V), r = .ok p) ∧ d.outcomes.Nonempty

end

end GoldilocksCorrectness.Wiring
