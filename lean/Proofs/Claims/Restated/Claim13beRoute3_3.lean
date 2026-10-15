import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13beRoute3_23
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Blocks
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Claim13bStepCone
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Blocks and block stamps along the execution

Every step keeps every block and block stamp of every store, stamps are at or before the store's
clock, a non-genesis block a store holds came from a delivery or from the validator's own tick, and
re-sends and tick emissions of blocks are honest sends. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m >>= k` can return `b`, then `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_elim {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β)
    (h : (m >>= k) ⇢ b) : ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_bind, Set.bind_def] at h
  obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
  cases e with
  | ok a => exact ⟨a, he, hb⟩
  | error err => simp at hb

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `k` is the tick at `t`, then either the step took an outcome `out` of `v`'s tick from a
    node state whose store is `v`'s store after `k` steps, and `v`'s node state after `k + 1` steps
    is `out`'s, or `v`'s store after `k + 1` steps is its store after `k` steps. -/
private theorem tick_step_st_cases_blocks (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {k t : Nat} (v : V)
    (hl : x.lbl k = AtomicAction.tickAllAwake t) :
    (∃ (n₀ : M.N) (out : M.N × List (NamedObject V)), n₀.st = (x[k][v].st).st ∧
        (M.reachedNode n₀ ∧ M.runs_as n₀ v) ∧
        M.tick (Setup.alwaysAwake S) v n₀ (t : Int) ⇢ out ∧ x[k + 1][v].st = out.1) ∨
      (x[k + 1][v].st).st = (x[k][v].st).st := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  have hwst : ((w v).state).st = (x[k][v].st).st := by
    have hww := hwake v
    unfold TickAllAwakeWake at hww
    by_cases he : v ∈ entrants Sched t
    · rw [if_pos he] at hww
      rw [Record.protocolOf_step_wake M S hww]
      exact (facts.nd.wake_st_record _).1
    · rw [if_neg he] at hww
      rw [hww]
  by_cases haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
  · have hx1 : x[k + 1][v].st = (tk v).state := by
      have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
      rw [h2, tickAllAwakeUpdate_getElem_react haw]
    rcases Record.protocolOf_step_tick M S (htick v haw) with ⟨-, out, hout, hres⟩ | ⟨-, hres⟩
    · have hwS : (w v).state = Record.wakeStage M Sched (t : Int) x[k] v :=
        Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake v)
      exact Or.inl ⟨(w v).state, out, hwst,
        ⟨by rw [hwS]; exact Record.reachedNode_wakeStage facts S Sched x k v t,
          by rw [hwS]; exact Record.runs_as_wakeStage facts S Sched x k v t⟩, hout, by rw [hx1, hres]⟩
    · exact Or.inr (by rw [hx1, hres, hwst])
  · refine Or.inr ?_
    have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_st_of_not_react haw]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every outcome `n₁` of the receipt of `o` from a node state `n` that a run reaches makes a
    `BlockStep` from `n`'s core store: it keeps every block and every block stamp. -/
theorem blockStep_node_process (facts : Record.Facts M) (S' : Setup V) (n : M.N) (o : NamedObject V) : ∀ n₁, M.process S' n o ⇢ n₁ →
    ∀ (hn : M.reachedNode n := by trivial),
    Restated.Vocabulary.Protocol.BlockStep M n.st.core n₁.st.core := by
  intro n₁ hn₁ _hn h
  obtain ⟨⟨hmem, hstamp⟩, hs₁, hs₂, hs₃⟩ :=
    facts.ndRun.blockStep_process S' n o n₁ hn₁ ⟨h.stamped, h.stored, h.bounded⟩
  exact ⟨⟨hmem, hstamp⟩, ⟨hs₁, hs₂, hs₃⟩⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every step makes a `BlockStep` at every validator's core store: the store after it keeps every
    block and every block stamp of the store before it. -/
theorem blockStep_sts_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) :
    Restated.Vocabulary.Protocol.BlockStep M (x[i][w].st).st.core (x[i + 1][w].st).st.core := by
  cases hl : x.lbl i with
  | tickAllAwake τ =>
      rcases tick_step_st_cases_blocks facts S Sched x w hl with
        ⟨n₀, out₁, hn₀, ⟨_hr₀, _hv₀⟩, hout, hst⟩ | hst
      · obtain ⟨hten, -⟩ := Restated.tickAllAwake_time facts S Sched x hl
        have hle : n₀.st.core.t ≤ (τ : Int) := by
          rw [hn₀]
          have h1 := Restated.clock_le_time_sts facts S Sched x i w
          have h2 : (x[i].time : Int) + 1 = (τ : Int) := by exact_mod_cast hten
          linarith
        rw [hst, ← hn₀]
        intro h
        obtain ⟨⟨hmem, hstamp⟩, hs₁, hs₂, hs₃⟩ :=
          facts.ndRun.blockStep_tick (Setup.alwaysAwake S) w n₀ (τ : Int) out₁ hout hle
            ⟨h.stamped, h.stored, h.bounded⟩
        exact ⟨⟨hmem, hstamp⟩, ⟨hs₁, hs₂, hs₃⟩⟩
      · rw [hst]; exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
  | deliver p sm =>
      by_cases hp : p = w
      · subst hp
        rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
        · have _hr_s1 := Record.reachedNode_sts facts S Sched x (i) p
          exact Restated.blockStep_node_process facts (Setup.alwaysAwake S) (x[i][p].st) sm.msg
            _ hproc
        · rw [hst]; exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
      · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]
        exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
  | custom p ev => exact ev.elim
  | adversarial p mm =>
      rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]
      exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
  | forward p mm =>
      rw [Restated.getElem_succ_of_forward facts S Sched x hl]
      exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ j`, the core store a validator holds after `j` steps makes a `BlockStep` from the one
    it held after `i` steps: it keeps every block and every block stamp. -/
theorem blockStep_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {i j : Nat} (hij : i ≤ j) (w : V) :
    Restated.Vocabulary.Protocol.BlockStep M (x[i][w].st).st.core (x[j][w].st).st.core := by
  induction j, hij using Nat.le_induction with
  | base => exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
  | succ n hn ih => exact Restated.Vocabulary.Protocol.BlockStep.trans' facts ih (Restated.blockStep_sts_succ facts S Sched x n w)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every validator's core store satisfies `BlockStamps`: it gives a
    stamp to exactly the blocks of its tree, and no stamp is later than its own clock. -/
theorem blockStamps_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) : Restated.Vocabulary.Protocol.BlockStamps M (x[m][w].st).st.core := by
  induction m with
  | zero =>
      rw [Record.st_zero M S Sched x w, facts.nd.initial_st_inclG2]
      obtain ⟨hs₁, hs₂, hs₃⟩ := facts.hd.blockStamps_init
      exact ⟨hs₁, hs₂, hs₃⟩
  | succ i ih => exact (Restated.blockStep_sts_succ facts S Sched x i w ih).2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A block in a store's tree carries a stamp, and that stamp is at or before that store's own
    clock. -/
theorem stamp_le_clock_block (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) {B : Block V}
    (hB : B ∈ (x[m][w].st).st.core.T) :
    ∃ σ : Stamp, (x[m][w].st).st.core.timestamp_block B = some σ ∧
      σ ≤ ((x[m][w].st).st.core.t : Stamp) := by
  have hbs := Restated.blockStamps_sts facts S Sched x m w
  have hs := hbs.stamped B hB
  cases hcase : (x[m][w].st).st.core.timestamp_block B with
  | none => rw [hcase] at hs; simp at hs
  | some c => exact ⟨c, rfl, hbs.bounded B c hcase⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a validator's store gives a block the stamp `σ` after `i` steps, it still gives that block
    the stamp `σ` after every later number of steps `j`. -/
theorem block_stamp_carry (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {i j : Nat} (hij : i ≤ j) (w : V) {B : Block V} {σ : Stamp}
    (h : (x[i][w].st).st.core.timestamp_block B = some σ) :
    (x[j][w].st).st.core.timestamp_block B = some σ :=
  ((Restated.blockStep_sts facts S Sched x hij w) (Restated.blockStamps_sts facts S Sched x i w)).1.stamp B σ h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A block in a store's tree after `m` steps, with `x[m].time < Γ`, carries a stamp strictly before
    `Γ`. -/
theorem block_stamp_lt_of_time (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (w : V) {B : Block V} {Γ : Int}
    (hB : B ∈ (x[m][w].st).st.core.T) (hlt : (x[m].time : Int) < Γ) :
    ∃ σ : Stamp, (x[m][w].st).st.core.timestamp_block B = some σ ∧ σ < (Γ : Stamp) := by
  obtain ⟨σ, hσ, hle⟩ := Restated.stamp_le_clock_block facts S Sched x m w hB
  refine ⟨σ, hσ, lt_of_le_of_lt hle ?_⟩
  exact WithBot.coe_lt_coe.mpr (lt_of_le_of_lt (Restated.clock_le_time_sts facts S Sched x m w) hlt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every block in a store's tree is the erasure of a named block among its bodies. -/
theorem exists_named_of_mem_tree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (n : Nat) (w : V) {X : Block V}
    (hX : X ∈ (x[n][w].st).st.core.T) :
    ∃ D : NamedBlock V, D ∈ (x[n][w].st).st.bodies ∧ D.erase = X := by
  rw [Restated.bodies_image_eq_T facts S Sched x n w] at hX
  obtain ⟨D, hD, hDe⟩ := Finset.mem_image.mp hX
  exact ⟨D, hD, hDe⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A named block other than genesis among `q`'s bodies after `m` steps entered at some step
    `i < m`, which is either a delivery to `q` of a message whose payload is that block, or `q`'s
    own tick at a time `τ` that is a whole multiple of `S.E.Δ`, at which `q` is awake and not
    adversarial, whose outcome taken at step `i` sends the block. -/
theorem block_sent_of_mem_tree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {m : Nat} {q : V} {B : NamedBlock V}
    (hne : B ≠ NamedBlock.genesis) (hB : B ∈ (x[m][q].st).st.bodies) :
    ∃ i : Nat, i < m ∧
      ((∃ sm : SignedMsg V (NamedObject V), x.lbl i = AtomicAction.deliver q sm ∧
          sm.msg = NamedObject.block B) ∨
        (∃ τ : Nat, x.lbl i = AtomicAction.tickAllAwake τ ∧
          q ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) ∧ (τ : Int) % S.E.Δ = 0 ∧
          ∃ out₁, M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (τ : Int) x[i] q) (τ : Int) ⇢ out₁ ∧
            x[i + 1][q].st = out₁.1 ∧ NamedObject.block B ∈ out₁.2)) := by
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][q].st).st
      (NamedObject.block B) = false := by
    rw [Record.st_zero M S Sched x q]
    simp only [Restated.Vocabulary.Execution.Object.processed, facts.nd.initial_st,
      facts.hd.initial_bodies, Finset.mem_singleton]
    exact decide_eq_false hne
  have hm : Restated.Vocabulary.Execution.Object.processed M (x[m][q].st).st
      (NamedObject.block B) = true := by
    simp only [Restated.Vocabulary.Execution.Object.processed]
    exact decide_eq_true hB
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_flip_of_processed facts S Sched x q (NamedObject.block B) h0 hm
  refine ⟨i, him, ?_⟩
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, hdvd, out₁, hout₁, hst, hem⟩
  · rcases hpay with hmsg | ⟨Bl, -, hcc⟩
    · exact Or.inl ⟨sm, hlbl, hmsg⟩
    · exact hcc.elim
  · rcases hem with hmem | ⟨Bl, -, hcc⟩
    · exact Or.inr ⟨τ, hlbl, haw, hdvd, out₁, hout₁, hst, hmem⟩
    · exact hcc.elim

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the adversary has held `w` at no time up to step `n`, then `Block.find?` on `w`'s tree at
    step `n`, asked for the root of a block of that tree, answers with that very block. -/
theorem find_of_mem_tree_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {n : Nat} {w : V} (hw : Restated.HonestThrough M Sched x n w) {X : Block V}
    (hX : X ∈ (x[n][w].st).st.core.T) :
    Block.find? (x[n][w].st).st.core.T X.root = some X := by
  have hroot : Restated.RootCollisionFreeInLog M S Sched x := hexec.idealization
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x n w hX
  refine Proofs.Optimistic.find?_eq_some_of_unique hX ?_
  intro Y hY hYroot
  obtain ⟨C, hC, hCe⟩ := Restated.exists_named_of_mem_tree facts S Sched x n w hY
  have hinj := Restated.rootInjectiveOnAncestors_of_collisionFreeInLog facts S Sched x hroot C D
    (Restated.blockInLog_of_mem_bodies facts S Sched hw hC) (Restated.blockInLog_of_mem_bodies facts S Sched hw hD)
  refine RootInjectiveOnAncestors.eq_of_root_eq hinj (A := Y) (C := X) ?_ ?_ ?_
  · rw [hCe]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · rw [hDe]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · exact hYroot

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every block the slot-`s` fork choice of the store a validator holds after `m` steps can return
    is one of the blocks that store holds. -/
theorem gfHeadFrom_mem_tree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (m : Nat) (q : V) (s : Slot) :
    ∀ H, Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H → H ∈ (x[m][q].st).st.core.T := by
  intro H hH
  obtain ⟨n, hn, hH⟩ := returns_bind_elim _ _ _ hH
  obtain ⟨c, -, rfl⟩ := returns_map_elim _ _ _ hn
  rewrite [facts.nd.mkNode_st] at hH; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hH; rw [facts.nd.mkNode_cache] at hH
  have hinvPre : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg (x[m][q].st).st :=
    (Restated.nodeInvariant_sts facts S Sched x m q).1
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg
      (M.ns_setClock S.E (x[m][q].st).st (M.vote_time S.E s)) :=
    facts.hd.invariant_clock S.E S.cfg (x[m][q].st).st (M.vote_time S.E s) hinvPre
  have hroot :
      M.get_fg_root (M.toHealing (Restated.voteStoreAt M S (x[m][q].st) s)).toFG
        ∈ (Restated.voteStoreAt M S (x[m][q].st) s).T :=
    Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts _ hinv.1.2
  have hT : (Restated.voteStoreAt M S (x[m][q].st) s).T = (x[m][q].st).st.core.T := by
    rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_T]
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc
    (M.toHealing (Restated.voteStoreAt M S (x[m][q].st) s))
    (M.round_of S.hc (Restated.voteStoreAt M S (x[m][q].st) s).s)
    (M.readFrame c (M.toHealing (Restated.voteStoreAt M S (x[m][q].st) s))
      (M.round_of S.hc (Restated.voteStoreAt M S (x[m][q].st) s).s)).g1
  have hamem : a ∈ (Restated.voteStoreAt M S (x[m][q].st) s).T := by
    rw [← facts.sto.toHealing_gs_T (Restated.voteStoreAt M S (x[m][q].st) s)]
    exact Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc _ _ _
      (by rw [Record.Model.HS.T, facts.sto.toHealing_gs_T]; exact hroot) a ha
  have hA : M.get_sg_root_with (M.gradeContract c)
      S.E S.hc (M.toHealing (Restated.voteStoreAt M S (x[m][q].st) s))
      (M.round_of S.hc
        (M.toHealing (Restated.voteStoreAt M S (x[m][q].st) s)).toFG.toSG.toGoldfishStore.s) ⇢ a := by
    rw [facts.sto.toHealing_s, facts.nd.gradeContract_sgRoot_eq_frameAnchor]
    exact ha
  obtain ⟨Tr, hTr, hH⟩ := returns_bind_elim _ _ _ hH
  have hTr' : M.voter_filtered_block_tree S.E (Restated.voteStoreAt M S (x[m][q].st) s)
      (Restated.voteStoreAt M S (x[m][q].st) s).s ⇢ Tr := by
    have h := hTr
    simp only [Restated.voteTreeOf, facts.nd.store_with_cache_core_s,
      facts.nd.store_with_cache_voter_filtered_block_tree] at h
    exact h
  obtain ⟨W, -, hH⟩ := returns_bind_elim _ _ _ hH
  obtain ⟨U, -, hH⟩ := returns_bind_elim _ _ _ hH
  rw [facts.hd.get_head_in_tree_with_eq_layer] at hH
  simp only [facts.nd.mkNode_cache, facts.nd.store_with_cache_get_head_in_tree_with_layer,
    facts.nd.store_with_cache_core_s] at hH
  rw [← hT]
  exact facts.fc.Sts_get_head_in_tree_with_layer_mem _ S.E S.hc _ _ _ _ _ a hA hamem
    (facts.hd.Sts_voter_filtered_block_tree_subset S.E _ _ Tr hTr') H hH

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `i`, inside the phase, delivers a block `B` to a validator `q` and `q`'s receipt of `B`
    has an outcome (`hne`), then `q`'s re-send `⟨q, B⟩` is an honest send at a step with the same
    time. -/
theorem block_onWire_of_deliver_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {i : Nat} {q u : V} {B : NamedBlock V}
    (hlbl : x.lbl i
      = AtomicAction.deliver q (⟨u, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (_hqh : Restated.HonestThrough M Sched x i q) (_hqaw : AtomicAwake x i q)
    -- `q`'s receipt of `B` at step `i` has an outcome
    (hne : ∃ n' : M.N,
      M.process (Setup.alwaysAwake S) (x[i][q].st) (NamedObject.block B) ⇢ n') :
    ∃ k : Nat, (x[k].time : Int) = (x[i].time : Int) ∧
      Restated.HonestSendAt M S x k (⟨q, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) :=
  ⟨i, rfl, Restated.honestSendAt_of_deliver_relay facts S Sched x hlbl
    ((mem_relayedObjects_iff _ _).2 (Or.inl rfl))
    hne⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `i` is the tick of `τ`, `q` is awake and not adversarial at `τ`, `τ` is a whole multiple
    of the delay, the outcome of `q`'s tick taken at step `i` sends the named block `B`, and the
    adversary has held `q` at no time up to step `i`, then step `i` is an honest send of `⟨q, B⟩`. -/
theorem block_honestSend_at_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {i : Nat} {q : V} {B : NamedBlock V} {τ : Nat}
    (hqh : Restated.HonestThrough M Sched x i q)
    (hlbl : x.lbl i = AtomicAction.tickAllAwake τ)
    (haw : q ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int)) (hdvd : (τ : Int) % S.E.Δ = 0)
    (hemit : ∃ out₁, M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (τ : Int) x[i] q) (τ : Int) ⇢ out₁ ∧
      x[i + 1][q].st = out₁.1 ∧ NamedObject.block B ∈ out₁.2) :
    Restated.HonestSendAt M S x i (⟨q, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) := by
  obtain ⟨out₁, hout, hst, hmem⟩ := hemit
  exact And.intro
    (Restated.mem_sent_diff_of_tick_of_state facts S Sched x hlbl haw hdvd
      (facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) q
        (Record.wakeStage M Sched (τ : Int) x[i] q) (τ : Int))
      hout hst hmem)
    (hqh _ (le_refl _))

end

end DecoupledConsensusModel.Sts.Restated
