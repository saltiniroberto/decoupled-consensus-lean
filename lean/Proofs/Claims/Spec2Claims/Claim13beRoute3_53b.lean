import Proofs.Claims.Spec2Claims.Claim13beRoute3_50
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_parent_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_parent
import Proofs.Claims.Spec2Claims.Claim13bModel_select
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_with
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_fork_choice
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RetainedRows
import Proofs.Claims.Spec2Claims.Claim13bModel_derive_named
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_early
import Proofs.Claims.Spec2Claims.Claim13bModel_interpretedInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_late
import Proofs.Claims.Spec2Claims.Claim13bModel_rawInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_rawView
import Proofs.Claims.Spec2Claims.Claim13bModel_readyView
import Proofs.Claims.Spec2Claims.Claim13bModel_token
import Proofs.Claims.Spec2Claims.Claim13bModel_Supports
import Proofs.Claims.Spec2Claims.Claim13bModel_Opposes
import Proofs.Claims.Spec2Claims.Claim13bModel_CleanFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_positive
import Proofs.Claims.Spec2Claims.Claim13bModel_opposing
import Proofs.Claims.Spec2Claims.Claim13bModel_localCovers
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool
import Proofs.Claims.Spec2Claims.Claim13bModel_bodyReady
import Proofs.Claims.Spec2Claims.Claim13bModel_actionReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Vocabulary.ModelProperties.grade2_block_with

/-!
# Raw inputs of a round's window

A raw input of round `r`'s window places the lower instant `lo` at or before every cutoff from
`opening r − 5Δ` on.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

section RelativeCrossReaderFinality

local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

end RelativeCrossReaderFinality

section RelativeCrossReaderGuards

local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

end RelativeCrossReaderGuards

section RelativeCrossReaderTransport

open DecoupledConsensusModel.Proofs.NamedRawRelay

local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `lo ≤ opening (r − η_SG)`, `opening r − 5Δ ≤ c`, and `u` is a raw input of round `r` for some
    sender at some cutoff, then `lo ≤ c`. -/
theorem lo_le_of_rawInputs_l53 (S : Setup V) {lo : Int} {r : Round} {c : Time}
    (hlow : lo ≤ opening S.E S.hc (r - S.hc.η_SG))
    (hc : opening S.E S.hc r - 5 * S.E.Δ ≤ c)
    {gv : Protocol.GradeView V} {c' : Time} {sender : V} {u : Protocol.SGVote V}
    (hraw : u ∈ DecoupledConsensusModel.Protocol.rawInputs gv S.hc.η_SG r c' sender) :
    lo ≤ c := by
  obtain ⟨k, hk, -⟩ := exists_window_of_mem_rawInputs hraw
  exact lo_le_cut_of_window S hlow hk hc

end RelativeCrossReaderTransport

section RelativeCrossReaderG1G0

open DecoupledConsensusModel.Proofs.NamedRawRelay

local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

end RelativeCrossReaderG1G0

end DecoupledConsensusModel.Sts
