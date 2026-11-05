module
public import GoldilocksCorrectness.Record.SlotLayout
public import GoldilocksCorrectness.Statements.Executions.ExecutionDefs
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The spec's slot layout against the library's times

One theorem per member of `SlotLayout`: the library's definition of that time (or the spec's
validator set and quorum) is the member of `SlotLayout.goldilocks` at the setup's parameters
`S.C`. Each holds by definition.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (quorum)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff viewFreeze
  lateVoteCutoff dutyWindowStart proposalWindowStart)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The library's `slotStart S s` is the layout's start of slot `s` at `S.C`.

Read aloud: slot `s` starts where the spec's layout says. -/
theorem slotStart_goldilocks (S : Setup V) (s : ℕ) :
    slotStart S s = (SlotLayout.goldilocks : SlotLayout V).slotStart S.C s := by rfl

/-- The library's `voteTime S s` is the layout's vote time of slot `s` at `S.C`.

Read aloud: slot `s`'s vote time is where the spec's layout says. -/
theorem voteTime_goldilocks (S : Setup V) (s : ℕ) :
    voteTime S s = (SlotLayout.goldilocks : SlotLayout V).voteTime S.C s := by rfl

/-- The library's `supportCutoff S s` is the layout's support cutoff of slot `s` at `S.C`.

Read aloud: slot `s`'s support cutoff is where the spec's layout says. -/
theorem supportCutoff_goldilocks (S : Setup V) (s : ℕ) :
    supportCutoff S s = (SlotLayout.goldilocks : SlotLayout V).supportCutoff S.C s := by rfl

/-- The library's `viewFreeze S s` is the layout's view freeze of slot `s` at `S.C`.

Read aloud: slot `s`'s view freeze is where the spec's layout says. -/
theorem viewFreeze_goldilocks (S : Setup V) (s : ℕ) :
    viewFreeze S s = (SlotLayout.goldilocks : SlotLayout V).viewFreeze S.C s := by rfl

/-- The library's `lateVoteCutoff S s` is the layout's late-vote cutoff of slot `s` at `S.C`.

Read aloud: slot `s`'s late-vote cutoff is where the spec's layout says. -/
theorem lateVoteCutoff_goldilocks (S : Setup V) (s : ℕ) :
    lateVoteCutoff S s = (SlotLayout.goldilocks : SlotLayout V).lateVoteCutoff S.C s := by rfl

/-- The library's `dutyWindowStart S s` is the layout's start of slot `s`'s duty window at `S.C`.

Read aloud: slot `s`'s duty window starts where the spec's layout says. -/
theorem dutyWindowStart_goldilocks (S : Setup V) (s : ℕ) :
    dutyWindowStart S s = (SlotLayout.goldilocks : SlotLayout V).dutyWindowStart S.C s := by rfl

/-- The library's `proposalWindowStart S s` is the layout's start of slot `s`'s proposal window
at `S.C`.

Read aloud: slot `s`'s proposal window starts where the spec's layout says. -/
theorem proposalWindowStart_goldilocks (S : Setup V) (s : ℕ) :
    proposalWindowStart S s =
      (SlotLayout.goldilocks : SlotLayout V).proposalWindowStart S.C s := by rfl

/-- The library's slot of a natural-number time, `S.C.slot (t : Int)`, is the layout's slot of
`t` at `S.C`.

Read aloud: the time `t` is in the slot the spec's layout says. -/
theorem slot_goldilocks (S : Setup V) (t : ℕ) :
    S.C.slot (t : Int) = (SlotLayout.goldilocks : SlotLayout V).slot S.C t := rfl

/-- Every validator is in the layout's validator set of every block.

Read aloud: the spec's layout gives every block all the validators. -/
theorem validators_goldilocks (B : Goldilocks.Block V) :
    (Finset.univ : Finset V) = (SlotLayout.goldilocks : SlotLayout V).validators B := rfl

/-- The layout's quorum at every block is the spec's `quorum V`.

Read aloud: the spec's layout gives every block the quorum `quorum V`. -/
theorem quorumAt_goldilocks (B : Goldilocks.Block V) :
    quorum V = (SlotLayout.goldilocks : SlotLayout V).quorumAt B := rfl

end GoldilocksCorrectness.Record
