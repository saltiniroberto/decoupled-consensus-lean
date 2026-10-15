import Proofs.Claims.Spec2Claims.Claim13beRoute3_42c
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedHeightPair_erase
import Proofs.Claims.Spec2Claims.Claim13beRoute3_47
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_initial_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_sg_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_interpretedInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_localCovers
import Proofs.Claims.Spec2Claims.Claim13bModel_bodyReady
import Proofs.Claims.Spec2Claims.Claim13bModel_readyView
import Proofs.Claims.Spec2Claims.Claim13bModel_rawView
import Proofs.Claims.Spec2Claims.Claim13bModel_token
import Proofs.Claims.Spec2Claims.Claim13bModel_freezeRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_anchor
import Proofs.Claims.Spec2Claims.Claim13bModel_occurrenceBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_author
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Claims.Spec2Claims.Claim13bModel_grade2Block
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_against
import Proofs.Claims.Spec2Claims.Claim13bModel_head_covers
import Proofs.Claims.Spec2Claims.Claim13bModel_early

/-!
# Per-instant forms of the action-source lemmas

The action tick, its read and its emission, over a run whose premises are given by the bundle
`AdmissibleFieldsOn`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

section ActionSources

open DecoupledConsensusModel.Proofs.NamedActionSources
open DecoupledConsensusModel.Execution.NamedActionReads

/-- A tick of `v` at `S.a r` at index `i` reads `v`'s state strictly before `S.a r`. -/
theorem action_read_indexOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} (hf : AdmissibleFieldsOn S rho Hs Xb lo) :
    ∀ i v r, rho.events[i]? = some (.tick v (S.a r)) →
      NamedRun.stateBefore S rho i v = NamedRun.stateBeforeTime S rho (S.a r) v := by
  intro i v r hi
  exact Proofs.NamedRuntime.tick_prefix_eq_strict_of_fields S rho hf.sorted hf.tickIndexUnique hi

/-- The tick of `v` at `S.a r` at index `i` emits `v`'s action attestation of `r` when `v` is
    flagged awake for `r`, and nothing otherwise. -/
theorem action_emissionOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} (hf : AdmissibleFieldsOn S rho Hs Xb lo) :
    ∀ i v r, rho.events[i]? = some (.tick v (S.a r)) →
      (NamedRun.emittedAt S rho i v (S.a r) =
        if (S.node v).awake r = true then
          [.attest (Proofs.HealingSurface.actionAttestationAt S rho v r)] else []) := by
  intro i v r hi
  unfold NamedRun.emittedAt
  rw [tick_at_action, action_read_indexOn S rho Hs Xb hf i v r hi]
  rfl

/-- `v` emits the attestation `row` at `S.a r` exactly when `v` ticks at `S.a r`, is flagged awake
    for `r`, and `row` is its action attestation of `r`. -/
theorem action_run_emissionOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} (hf : AdmissibleFieldsOn S rho Hs Xb lo) :
    ∀ v r (row : NamedAttestation V), NamedRun.emits S rho v (.attest row) (S.a r) ↔
      (∃ i : Nat, rho.events[i]? = some (NamedEvent.tick v (S.a r))) ∧
      (S.node v).awake r = true ∧ row = Proofs.HealingSurface.actionAttestationAt S rho v r := by
  intro v r row
  constructor
  · rintro ⟨i, hi, hrow⟩
    rw [action_emissionOn S rho Hs Xb hf i v r hi] at hrow
    by_cases hawake : (S.node v).awake r = true
    · simp only [if_pos hawake, List.mem_singleton, NamedObject.attest.injEq] at hrow
      exact ⟨⟨i, hi⟩, hawake, hrow⟩
    · simp only [if_neg hawake, List.not_mem_nil] at hrow
  · rintro ⟨⟨i, hi⟩, hawake, rfl⟩
    refine ⟨i, hi, ?_⟩
    rw [action_emissionOn S rho Hs Xb hf i v r hi, if_pos hawake]
    exact List.mem_singleton_self _

end ActionSources

section SGArrival

open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedSGArrival

local macro "sga% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.SGArrival)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedSGArrival ++ n.getId)))

end SGArrival

section RawSource

open DecoupledConsensusModel.Proofs.NamedRawSource

local macro "rs% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.RawSource)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawSource ++ n.getId)))

end RawSource

end DecoupledConsensusModel.Sts
