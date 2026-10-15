import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Redelivery
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_CrossTransport

/-!
# Bodies held before a public time

When a body enters a store and with which stamp, the store clock after a tick, that a body stamped
before a public time `c` is already held at the step before the tick at `c`, and that two honest
stores resolve one root to one block. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom EquivocationAt)
local macro "pcsg% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.PublicCutSG)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutSG ++ n.getId)))
local macro "pcb% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.PublicCutBody)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutBody ++ n.getId)))
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If the named block `B` is absent from `v`'s bodies after `i` steps and present after `i + 1`,
    then `v`'s store stamps `B`'s erasure with exactly the clock it reads after `i + 1` steps. -/
theorem body_entry_stamp (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i : Nat} {v : V} {B : NamedBlock V}
    (h0 : B ∉ (x[i][v].st).st.bodies) (h1 : B ∈ (x[i + 1][v].st).st.bodies) :
    (x[i + 1][v].st).st.core.timestamp_block B.erase
      = some (((x[i + 1][v].st).st.core.t : Int) : Stamp) := by
  rcases Record.st_succ_cases M S Sched x v i with hst | hst | ⟨t, out, hout | hout, hst⟩ | ⟨o, ho⟩
  · rw [hst] at h1; exact absurd h1 h0
  · rw [hst, (facts.nd.wake_st_record _).1] at h1; exact absurd h1 h0
  · rw [hst] at h1 ⊢
    rw [(facts.nd.tick_clock (Setup.alwaysAwake S) v (x[i][v].st) t out hout).1]
    exact facts.nd.node_tick_body_stamp (Setup.alwaysAwake S) v (x[i][v].st) t out hout B h0 h1
  · rw [hst] at h1 ⊢
    rw [(facts.nd.tick_clock (Setup.alwaysAwake S) v (M.wake (x[i][v].st)) t out hout).1]
    have h0' : B ∉ (M.wake (x[i][v].st)).st.bodies := by
      rw [(facts.nd.wake_st_record _).1]; exact h0
    exact facts.nd.node_tick_body_stamp (Setup.alwaysAwake S) v (M.wake (x[i][v].st)) t out hout
      B h0' h1
  · rw [(facts.nd.process_clock (Setup.alwaysAwake S) (x[i][v].st) o _ ho).1]
    exact facts.nd.node_process_body_stamp (Setup.alwaysAwake S) (x[i][v].st) o _ ho B h0 h1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom EquivocationAt)
local macro "pcsg% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.PublicCutSG)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutSG ++ n.getId)))
local macro "pcb% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.PublicCutBody)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutBody ++ n.getId)))
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If step `n` is the tick at `c`, `c` is a multiple of `Δ`, `w` is awake and not held by the
    adversary at `c`, and `w`'s tick at step `n` has an outcome, then `w`'s clock after any number
    of steps beyond `n` is at or after `c`. -/
theorem clock_ge_of_tick_lt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {n m : Nat} {c : Int} {w : V} (hn : Restated.tickStepAt M x n c)
    (haw : w ∈ Sched.awake c \ Sched.adv c) (hdvd : c % S.E.Δ = 0)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched c x[n] w) c ⇢ out)
    (hnm : n < m) :
    c ≤ (x[m][w].st).st.core.t :=
  Restated.clock_ge_of_tickStepAt_awake_sts facts S Sched x hn haw hne (Nat.succ_le_of_lt hnm)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom EquivocationAt)
local macro "pcsg% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.PublicCutSG)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutSG ++ n.getId)))
local macro "pcb% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.PublicCutBody)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutBody ++ n.getId)))
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `w` holds the named block `B` after `m` steps, with the stamp of `B`'s erasure strictly
    before `c`, step `n` is the tick at `c`, `c` is a multiple of `Δ`, `w` is awake and not held by
    the adversary at `c`, and `w`'s tick at step `n` has an outcome, then `w` holds `B` after `n`
    steps. -/
theorem body_held_before_cut (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {m n : Nat} {c : Int} {w : V} {B : NamedBlock V}
    (hB : B ∈ (x[m][w].st).st.bodies) {σ : Stamp}
    (hσ : (x[m][w].st).st.core.timestamp_block B.erase = some σ) (hσc : σ < (c : Stamp))
    (hn : Restated.tickStepAt M x n c) (haw : w ∈ Sched.awake c \ Sched.adv c) (hdvd : c % S.E.Δ = 0)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched c x[n] w) c ⇢ out) :
    B ∈ (x[n][w].st).st.bodies := by
  by_cases hgen : B = NamedBlock.genesis
  · subst hgen
    exact ((Restated.nodeInvariant_sts facts S Sched x n w).1.1.1.2.2.1).1
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][w].st).st (NamedObject.block B)
      = false := by
    rw [Record.st_zero M S Sched x w]
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not]
    rw [facts.nd.initial_st, facts.hd.initial_bodies, Finset.mem_singleton]
    exact hgen
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_flip_of_processed facts S Sched x w (NamedObject.block B) h0
      (by simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hB)
  have hb0 : B ∉ (x[i][w].st).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using hf0
  have hb1 : B ∈ (x[i + 1][w].st).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hf1
  have hst1 := Restated.body_entry_stamp facts S Sched x hb0 hb1
  have hcarry := Restated.block_stamp_carry facts S Sched x (Nat.succ_le_of_lt him) w hst1
  rw [hσ] at hcarry
  have hlt : (x[i + 1][w].st).st.core.t < c := by
    have h := Option.some.inj hcarry
    rw [h] at hσc
    exact WithBot.coe_lt_coe.mp hσc
  have hin : i + 1 ≤ n := by
    by_contra hcon
    have hni : n < i + 1 := by omega
    exact absurd (Restated.clock_ge_of_tick_lt facts S Sched x hn haw hdvd hne hni) (not_le.mpr hlt)
  have h := Restated.processed_mono facts S Sched x w (NamedObject.block B) hin hf1
  simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom EquivocationAt)
local macro "pcsg% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.PublicCutSG)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutSG ++ n.getId)))
local macro "pcb% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.PublicCutBody)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedPublicCutBody ++ n.getId)))
local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `v₁` is honest through step `m₁`, `v₂` through step `m₂`, and their trees resolve the root
    `root` to `H` and `K`, then `H = K`. -/
theorem find_agree_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m₁ m₂ : Nat} {v₁ v₂ : V} (hv₁ : Restated.HonestThrough M Sched x m₁ v₁)
    (hv₂ : Restated.HonestThrough M Sched x m₂ v₂) {root : BlockId} {H K : Block V}
    (hH : Block.find? (x[m₁][v₁].st).st.core.T root = some H)
    (hK : Block.find? (x[m₂][v₂].st).st.core.T root = some K) : H = K := by
  have hHmem := Proofs.HealingLemmas.find?_mem hH
  have hKmem := Proofs.HealingLemmas.find?_mem hK
  have hHr := Proofs.HealingLemmas.find?_root hH
  have hKr := Proofs.HealingLemmas.find?_root hK
  obtain ⟨C, hC, hCe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m₁ v₁ hHmem
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m₂ v₂ hKmem
  have hinj := Restated.rootInjectiveOnAncestors_of_collisionFreeInLog facts S Sched x hexec.idealization C D
    (Restated.blockInLog_of_mem_bodies facts S Sched hv₁ hC) (Restated.blockInLog_of_mem_bodies facts S Sched hv₂ hD)
  refine RootInjectiveOnAncestors.eq_of_root_eq hinj (A := H) (C := K) ?_ ?_ ?_
  · rw [hCe]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · rw [hDe]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · rw [hHr, hKr]

end

end DecoupledConsensusModel.Sts.Restated
