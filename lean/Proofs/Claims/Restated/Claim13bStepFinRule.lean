import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bW_ScheduleRule

/-!
# The next round's anchor over the honest active attesters, under the awake-test rule

The lemmas of `Claim13bStepFin.lean` that bound the targets of height votes by the round-`(r + 1)`
anchor, with the compatibility hypotheses on confirmed and grade-2 blocks asked of `HonRound S Sched
(r + 1)` only, and the activity of a round-`(r + 1)` sender read off the attestation it sent.
Stated over a model `M : Record.Model V`, its facts `facts : Record.Facts M`, whose field `ndWake` holds the converse awake facts.
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

/-- The attestations `v`'s round-`r` action read can compute from the node state `v`'s tick reads at
    time `t` from configuration `c` are those it can compute from `v`'s node state in `c`. -/
private theorem actionAttestationFrom_wakeStageFin (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (t : Int) (c : Config V (NamedObject V) M.N) (v : V) (r : Round) :
    Restated.actionAttestationFrom M S (Record.wakeStage M Sched t c v) v r =
      Restated.actionAttestationFrom M S (c[v].st) v r := by
  unfold Restated.actionAttestationFrom Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, Record.wakeStage_record facts]

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_fin {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
    (b : β) : (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

/-- The finality-gadget source read has an outcome at every node state. -/
private theorem actionFGSource_nonempty_fin (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff_fin _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- From every node state, validator `v`'s round-`r` action read can compute some attestation. -/
private theorem actionAttestationFrom_nonempty_fin (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (v : V) (r : Round) :
    ∃ a, a ∈ Restated.actionAttestationFrom M S before v r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st before.record c).cache)
    S.E S.hc (S.node v) (M.mkNode st before.record c).st (M.mkNode st before.record c).record
  exact ⟨D.2.2, M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, D.1, D.2.1, hD⟩

/-- If every healing store of the round-`r₁` action read from `before` has a confirmed block on one
    chain with `B`, and every frame of that read has its grade-2 block, when there is one, on one
    chain with `B`, then every block the finality-gadget source can return at a node state of that
    read is on one chain with `B`. -/
private theorem source_compatible_fin (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r₁ : Round) (B : Block V)
    (hconf : ∀ hs ∈ Restated.actionHealingStore M S before r₁,
      Block.compatible (hs : M.HS).live_confirmed B = true)
    (hg2 : ∀ f ∈ Restated.actionFrame M S before r₁, ∀ root : Block V,
      (f : M.Frame).g2 = some (some root) → Block.compatible root B = true)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      before r₁)
    (Cfg : Block V)
    (hCfg : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢
      some Cfg) :
    Block.compatible Cfg B = true := by
  rcases Restated.source_cases facts S before r₁ n hn Cfg hCfg with hlc | hQ
  · exact Protocol.compatible_of_preceq_of_compatible hlc (hconf _ ⟨n, hn, rfl⟩)
  · obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) r₁
    have hgQ : g.Q2 = some Cfg := hQ g ((facts.nd.gradeContract_read _ _ _ _ _ _).1 hg)
    obtain ⟨o, ho⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
      (M.readFrame n.cache (M.toHealing n.st.core) r₁)
    have hgo : g.Q2 = o :=
      facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc (M.toHealing n.st.core) r₁
        g hg o ho
    exact facts.gr.Q2_compatible (hg2 _ ⟨n, hn, rfl⟩) o ho (by rw [← hgo, hgQ])

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For a choice `att` of the round-`(r + 1)` action attestations, if the action reads of the members
    of `HonRound S Sched (r + 1)` have confirmed blocks and grade-2 blocks on one chain with the round-`(r + 1)` anchor
    `newAnchor`, and `att q` of a member `q` of `freshAttestersW` is a height vote at height `h₀`
    with root `entry`, then every block in the sent log whose root is `entry` is an ancestor of that
    anchor. -/
theorem newRound_target_under_new_anchor_rule (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    {T : NamedBlock V}
    (hT : Restated.blockInLog M S Sched x T)
    (hconf : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][q].st) (r + 1),
        Block.compatible (hs : M.HS).live_confirmed
          (Restated.newAnchor M S Sched x r n' att T).erase = true)
    (hg2 : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][q].st) (r + 1), ∀ root : Block V,
        (f : M.Frame).g2 = some (some root) →
        Block.compatible root (Restated.newAnchor M S Sched x r n' att T).erase = true)
    {q : V} (hqW : q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1))
    {h₀ : Height} {entry : BlockId} {tmo : Bool}
    (hvote : (att q).height_pair = NamedHeightPair.vote h₀ entry tmo)
    {C : NamedBlock V} (hC : Restated.blockInLog M S Sched x C) (hCroot : C.root = entry) :
    Block.Preceq C.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  classical
  have hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1) :=
    Restated.freshAttestersW_subset_freshAttesters facts S Sched x (r + 1) (n' + 1) hqW
  have hhon : Restated.HonestThrough M Sched x n' q := by
    intro t ht
    exact Restated.honestThrough_of_mem_freshAttesters facts hq t
      (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n')))
  have hqR : q ∈ Restated.HonRound M S Sched (r + 1) :=
    Restated.freshAttestersW_subset_honRound facts S Sched x
      (le_of_eq (Restated.tickStepAt_time facts x hn').1.symm) hqW
  have hatq := hatt q hqW
  obtain ⟨-, -, -, C₀, hC₀mem, hC₀root, hC₀h, hC₀entry⟩ :=
    Restated.vote_entry_of_fresh facts S Sched x hn' hq hatq hvote
  obtain ⟨n, hn, ns, rec, hD⟩ := hatq
  obtain ⟨o, ho⟩ := actionFGSource_nonempty_fin facts (Setup.alwaysAwake S) n
  obtain ⟨Cfg, rfl, hpre⟩ := Restated.entry_preceq_source facts S Sched x hexec hn' hq
    hC₀mem hC₀root n hn (ns, rec, att q) hD hvote o ho
  have hCfgc : Block.compatible Cfg (Restated.newAnchor M S Sched x r n' att T).erase = true :=
    source_compatible_fin facts S (x[n'][q].st) (r + 1) _ (hconf q hqR) (hg2 q hqR) n hn Cfg ho
  have hC₀c : Block.compatible C₀.erase (Restated.newAnchor M S Sched x r n' att T).erase = true :=
    Protocol.compatible_of_preceq_of_compatible hpre hCfgc
  have hmemh : h₀ ∈ Restated.freshVoteHeights M S Sched x r n' att :=
    (Restated.mem_freshVoteHeights facts).mpr ⟨q, hqW, entry, tmo, hvote⟩
  have hhle : h₀ ≤ (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h := by
    rw [Restated.newAnchor_height facts S Sched x hn' hatt T]
    exact le_trans (Finset.le_sup (f := id) hmemh) (le_max_right _ _)
  have hC₀log : Restated.blockInLog M S Sched x C₀ := Restated.blockInLog_of_mem_bodies facts S Sched hhon hC₀mem
  have hC₀T : Block.Preceq C₀.erase (Restated.newAnchor M S Sched x r n' att T).erase :=
    Restated.preceq_of_entry_compatible_sts facts S Sched x hexec.idealization hC₀log
      (Restated.newAnchor_blockInLog facts S Sched x hT) hC₀entry hC₀c (by rw [hC₀h]; exact hhle)
  have hCC₀ : C = C₀ :=
    hexec.idealization.root_injective C C₀ hC hC₀log C C₀
      (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self C₀))
      (by rw [hCroot, hC₀root])
  rw [hCC₀]
  exact hC₀T

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a validator `q` meeting the signer condition `P` at step `n₁`, at most the round-`(r + 1)`
    tick's successor, has in the sent log a height vote `a` at height `h₀` with root `entry`, then
    every block in the sent log whose root is `entry` is an ancestor of the round-`(r + 1)` anchor
    `newAnchor` along the choice `att`. The hypothesis `hactive` says that every validator honest
    through its tick at round `r + 1`'s action instant whose tick there sends an attestation of
    round `r + 1` is in `HonRound S Sched (r + 1)`; `hceil` and `htargets` are the round-`r`
    bounds on height votes and their targets. -/
theorem target_under_new_anchor_ofActiveVoters_rule (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hactive : ∀ (q : V) (k : Nat) (a : NamedAttestation V) (out : M.N × List (NamedObject V)),
      Restated.tickStepAt M x k (Restated.Vocabulary.Execution.Setup.a M S a.round) →
      q ∈ Sched.awake (Restated.Vocabulary.Execution.Setup.a M S a.round) \
        Sched.adv (Restated.Vocabulary.Execution.Setup.a M S a.round) →
      Restated.HonestThrough M Sched x (k + 1) q →
      M.tick (Setup.alwaysAwake S) q
        (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S a.round) x[k] q)
        (Restated.Vocabulary.Execution.Setup.a M S a.round) ⇢ out →
      NamedObject.attest a ∈ out.2 → a.round = r + 1 →
      q ∈ Restated.HonRound M S Sched (r + 1))
    (hT : Restated.blockInLog M S Sched x T)
    (hold : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase)
    (hconf : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][q].st) (r + 1),
        Block.compatible (hs : M.HS).live_confirmed
          (Restated.newAnchor M S Sched x r n' att T).erase = true)
    (hg2 : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][q].st) (r + 1), ∀ root : Block V,
        (f : M.Frame).g2 = some (some root) →
        Block.compatible root (Restated.newAnchor M S Sched x r n' att T).erase = true)
    {P : V → Nat → Prop}
    (hPhon : ∀ (w : V) (m : Nat), P w m → Restated.HonestThrough M Sched x m w)
    (hPanti : ∀ (w : V) (m m' : Nat), m ≤ m' → P w m' → P w m)
    (hceil : ∀ (w : V) (n₂ : Nat) (b : NamedAttestation V) (h₂ : Height) (entry₂ : BlockId)
      (tmo₂ : Bool), n₂ ≤ n + 1 → P w n₂ → b.val_index = w →
      (⟨w, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      b.height_pair = NamedHeightPair.vote h₂ entry₂ tmo₂ →
      h₂ ≤ (M.derive_named S.E S.cfg T).h)
    {q : V} {n₁ : Nat} {a : NamedAttestation V} {h₀ : Height} {entry : BlockId} {tmo : Bool}
    (htargets : h₀ ≤ (M.derive_named S.E S.cfg T).h →
      ∀ (w : V) (n₂ : Nat) (b : NamedAttestation V) (entry₂ : BlockId) (tmo₂ : Bool),
      n₂ ≤ n + 1 → P w n₂ → b.val_index = w →
      (⟨w, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      b.height_pair = NamedHeightPair.vote h₀ entry₂ tmo₂ →
      ∀ C₂ : NamedBlock V, Restated.blockInLog M S Sched x C₂ → C₂.root = entry₂ →
      Block.Preceq C₂.erase T.erase)
    (hn₁ : n₁ ≤ n' + 1) (hq : P q n₁) (hidx : a.val_index = q)
    (hlog : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₁].sent)
    (hpair : a.height_pair = NamedHeightPair.vote h₀ entry tmo)
    {C : NamedBlock V} (hC : Restated.blockInLog M S Sched x C) (hCroot : C.root = entry) :
    Block.Preceq C.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  have _hr_0 : M.reachedNode (x[n'][q].st) := Record.reachedNode_sts facts S Sched x n' q
  have _hv_0 : M.runs_as (x[n'][q].st) q := Record.runs_as_sts facts S Sched x n' q
  classical
  have hqhon : Restated.HonestThrough M Sched x n₁ q := hPhon q n₁ hq
  have hhonT : HonestThroughTime Sched ((x[n₁].time : Int)) q := fun t ht => hqhon t ht
  obtain ⟨-, k, hkn₁, htick, hawk, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x (tB := (x[n₁].time : Int)) hhonT
      hexec.toUnforgeability hidx (le_refl _) hlog
  have heq : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][q].st) q a.round,
      a = a' := by
    rw [← actionAttestationFrom_wakeStageFin facts (Setup.alwaysAwake S) Sched
      (Restated.Vocabulary.Execution.Setup.a M S a.round) x[k] q a.round]
    have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
    have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
    exact Restated.attest_of_tick_eq facts S q _ a.round hout hemit
  obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_fin facts (Setup.alwaysAwake S) (x[k][q].st) q
    a.round
  have hqkP : P q (k + 1) := hPanti q (k + 1) n₁ (Nat.succ_le_of_lt hkn₁) hq
  have hqk : Restated.HonestThrough M Sched x (k + 1) q := hPhon q (k + 1) hqkP
  have hsent : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
    rw [heq a₁ ha₁]
    exact Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩
      (facts.nd.tick_attestation_fields (Setup.alwaysAwake S) q _ _ (Record.runs_as_wakeStage facts S Sched x _ _ _) out hout a hemit).2.1 a₁ ha₁
  have hkn' : k ≤ n' := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hkn₁ hn₁)
  have hround : a.round ≤ r + 1 := Restated.round_le_of_tick_le facts S Sched x htick hn' hkn'
  rcases Nat.lt_or_ge a.round (r + 1) with hlt | hge
  ·
    have hle : a.round ≤ r := Nat.le_of_lt_succ hlt
    have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x htick hn hle
    have hstep : k + 1 ≤ n + 1 := Nat.succ_le_succ hkn
    have hh : h₀ ≤ (M.derive_named S.E S.cfg T).h :=
      hceil q (k + 1) a h₀ entry tmo hstep hqkP hidx hsent hpair
    exact preceq_trans_Preceq
      (htargets hh q (k + 1) a entry tmo hstep hqkP hidx hsent hpair C hC hCroot) hold
  ·
    have hreq : a.round = r + 1 := le_antisymm hround hge
    have htick' : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := by rw [← hreq]; exact htick
    have hkeq : k = n' := Restated.tickStepAt_unique facts x htick' hn'
    have hawk' : q ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := by rw [← hreq]; exact (Finset.mem_sdiff.1 hawk).1
    have hqk' : Restated.HonestThrough M Sched x (n' + 1) q := by rw [← hkeq]; exact hqk
    have heq' : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][q].st) q
        (r + 1), a = a' := by
      rw [← hreq, ← hkeq]; exact heq
    have ha₁' : a₁ ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][q].st) q
        (r + 1) := by
      rw [← hreq, ← hkeq]; exact ha₁
    have hqfresh : q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1) :=
      (Restated.mem_freshAttestersW facts).mpr
        ⟨(Finset.mem_sdiff.1 (hactive q k a out htick hawk hqk hout hemit hreq)).1, hqk'⟩
    have hvote : (att q).height_pair = NamedHeightPair.vote h₀ entry tmo := by
      rw [← heq' (att q) (hatt q hqfresh)]; exact hpair
    exact Restated.newRound_target_under_new_anchor_rule facts S Sched x hexec hn' hatt hT hconf hg2
      hqfresh hvote hC hCroot

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `target_under_new_anchor_ofActiveVoters_rule` with its hypothesis `hactive` discharged: a
    validator whose tick at round `r + 1`'s action instant sends an attestation of round `r + 1` is
    in `HonRound S Sched (r + 1)`, by the converse awake facts `facts.ndWake`. -/
theorem target_under_new_anchor_rule (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hT : Restated.blockInLog M S Sched x T)
    (hold : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase)
    (hconf : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][q].st) (r + 1),
        Block.compatible (hs : M.HS).live_confirmed
          (Restated.newAnchor M S Sched x r n' att T).erase = true)
    (hg2 : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][q].st) (r + 1), ∀ root : Block V,
        (f : M.Frame).g2 = some (some root) →
        Block.compatible root (Restated.newAnchor M S Sched x r n' att T).erase = true)
    {P : V → Nat → Prop}
    (hPhon : ∀ (w : V) (m : Nat), P w m → Restated.HonestThrough M Sched x m w)
    (hPanti : ∀ (w : V) (m m' : Nat), m ≤ m' → P w m' → P w m)
    (hceil : ∀ (w : V) (n₂ : Nat) (b : NamedAttestation V) (h₂ : Height) (entry₂ : BlockId)
      (tmo₂ : Bool), n₂ ≤ n + 1 → P w n₂ → b.val_index = w →
      (⟨w, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      b.height_pair = NamedHeightPair.vote h₂ entry₂ tmo₂ →
      h₂ ≤ (M.derive_named S.E S.cfg T).h)
    {q : V} {n₁ : Nat} {a : NamedAttestation V} {h₀ : Height} {entry : BlockId} {tmo : Bool}
    (htargets : h₀ ≤ (M.derive_named S.E S.cfg T).h →
      ∀ (w : V) (n₂ : Nat) (b : NamedAttestation V) (entry₂ : BlockId) (tmo₂ : Bool),
      n₂ ≤ n + 1 → P w n₂ → b.val_index = w →
      (⟨w, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      b.height_pair = NamedHeightPair.vote h₀ entry₂ tmo₂ →
      ∀ C₂ : NamedBlock V, Restated.blockInLog M S Sched x C₂ → C₂.root = entry₂ →
      Block.Preceq C₂.erase T.erase)
    (hn₁ : n₁ ≤ n' + 1) (hq : P q n₁) (hidx : a.val_index = q)
    (hlog : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₁].sent)
    (hpair : a.height_pair = NamedHeightPair.vote h₀ entry tmo)
    {C : NamedBlock V} (hC : Restated.blockInLog M S Sched x C) (hCroot : C.root = entry) :
    Block.Preceq C.erase (Restated.newAnchor M S Sched x r n' att T).erase :=
  Restated.target_under_new_anchor_ofActiveVoters_rule facts S Sched x hexec hn hn' hatt
    (fun q' k a' out htick hawk hqk hout hemit hround => by
      have htime := (Restated.tickStepAt_time facts x htick).1
      have h := Restated.honRound_of_attestation_sent facts S Sched x htick
        (by rw [hround]; exact Restated.early_g2_sub_delta_nonneg facts S (Nat.le_add_left 1 r))
        hawk (fun t ht => hqk t (by rw [htime]; exact ht)) hout hemit rfl
      rw [hround] at h
      exact h)
    hT hold hconf hg2 hPhon hPanti hceil htargets hn₁ hq hidx hlog hpair hC hCroot

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every height vote absent from
    `x[n_W].sent`, sent by a validator honest through its send at a step up to the round-`r` tick's
    successor, at a height at most the anchor `T`'s, names only blocks that are ancestors of `T`,
    then the same holds up to the round-`(r + 1)` tick's successor with the anchor `newAnchor` in
    place of `T`. -/
theorem targetsSince_field_at_succ_rule (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n n' n_W : Nat} {T : NamedBlock V}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hT : Restated.blockInLog M S Sched x T)
    (hold : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase)
    (hconf : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][q].st) (r + 1),
        Block.compatible (hs : M.HS).live_confirmed
          (Restated.newAnchor M S Sched x r n' att T).erase = true)
    (hg2 : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][q].st) (r + 1), ∀ root : Block V,
        (f : M.Frame).g2 = some (some root) →
        Block.compatible root (Restated.newAnchor M S Sched x r n' att T).erase = true)
    (hceil : ∀ (w : V) (n₂ : Nat) (b : NamedAttestation V) (h₂ : Height) (entry₂ : BlockId)
      (tmo₂ : Bool), n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ w → b.val_index = w →
      (⟨w, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      b.height_pair = NamedHeightPair.vote h₂ entry₂ tmo₂ →
      h₂ ≤ (M.derive_named S.E S.cfg T).h)
    (htgt : ∀ (w : V) (n₂ : Nat) (b : NamedAttestation V) (h₂ : Height) (entry₂ : BlockId)
      (tmo₂ : Bool),
      n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ w → b.val_index = w →
      (⟨w, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      (⟨w, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∉ x[n_W].sent →
      b.height_pair = NamedHeightPair.vote h₂ entry₂ tmo₂ →
      h₂ ≤ (M.derive_named S.E S.cfg T).h →
      ∀ C₂ : NamedBlock V, Restated.blockInLog M S Sched x C₂ → C₂.root = entry₂ →
      Block.Preceq C₂.erase T.erase) :
    ∀ (w : V) (n₁ : Nat) (a : NamedAttestation V) (h' : Height) (entry : BlockId) (tmo : Bool),
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ w → a.val_index = w →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₁].sent →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x[n_W].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
      Block.Preceq C.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  classical
  intro q n₁ a h₀ entry tmo hn₁ hqhon hidx hlog hW hpair _ C hC hCroot
  have hhonT : HonestThroughTime Sched ((x[n₁].time : Int)) q := fun t ht => hqhon t ht
  obtain ⟨-, k, hkn₁, htick, hawk, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x (tB := (x[n₁].time : Int)) hhonT
      hexec.toUnforgeability hidx (le_refl _) hlog
  have heq : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][q].st) q a.round,
      a = a' := by
    rw [← actionAttestationFrom_wakeStageFin facts (Setup.alwaysAwake S) Sched
      (Restated.Vocabulary.Execution.Setup.a M S a.round) x[k] q a.round]
    have _hr_s3 := Record.reachedNode_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
    have _hv_s4 := Record.runs_as_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
    exact Restated.attest_of_tick_eq facts S q _ a.round hout hemit
  obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_fin facts (Setup.alwaysAwake S) (x[k][q].st) q
    a.round
  have hqk : Restated.HonestThrough M Sched x (k + 1) q := fun t ht =>
    hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hkn₁)))
  have hsent : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
    rw [heq a₁ ha₁]
    exact Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩
      (facts.nd.tick_attestation_fields (Setup.alwaysAwake S) q _ _ (Record.runs_as_wakeStage facts S Sched x _ _ _) out hout a hemit).2.1 a₁ ha₁
  have hkn' : k ≤ n' := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hkn₁ hn₁)
  have hround : a.round ≤ r + 1 := Restated.round_le_of_tick_le facts S Sched x htick hn' hkn'
  rcases Nat.lt_or_ge a.round (r + 1) with hlt | hge
  ·
    have hle : a.round ≤ r := Nat.le_of_lt_succ hlt
    have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x htick hn hle
    have hstep : k + 1 ≤ n + 1 := Nat.succ_le_succ hkn
    have hh : h₀ ≤ (M.derive_named S.E S.cfg T).h :=
      hceil q (k + 1) a h₀ entry tmo hstep hqk hidx hsent hpair
    exact preceq_trans_Preceq
      (htgt q (k + 1) a h₀ entry tmo hstep hqk hidx hsent hW hpair hh C hC hCroot) hold
  ·
    have hreq : a.round = r + 1 := le_antisymm hround hge
    have htick' : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := by rw [← hreq]; exact htick
    have hkeq : k = n' := Restated.tickStepAt_unique facts x htick' hn'
    have hawk' : q ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := by rw [← hreq]; exact (Finset.mem_sdiff.1 hawk).1
    have hqk' : Restated.HonestThrough M Sched x (n' + 1) q := by rw [← hkeq]; exact hqk
    have heq' : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][q].st) q
        (r + 1), a = a' := by
      rw [← hreq, ← hkeq]; exact heq
    have ha₁' : a₁ ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][q].st) q
        (r + 1) := by
      rw [← hreq, ← hkeq]; exact ha₁
    have hqfresh : q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1) :=
      (Restated.mem_freshAttestersW facts).mpr
        ⟨by
          have htime := (Restated.tickStepAt_time facts x htick).1
          have h := Restated.honRound_of_attestation_sent facts S Sched x htick
            (by rw [hreq]; exact Restated.early_g2_sub_delta_nonneg facts S (Nat.le_add_left 1 r))
            hawk (fun t ht => hqk t (by rw [htime]; exact ht)) hout hemit rfl
          rw [hreq] at h
          exact (Finset.mem_sdiff.1 h).1, hqk'⟩
    have hvote : (att q).height_pair = NamedHeightPair.vote h₀ entry tmo := by
      rw [← heq' (att q) (hatt q hqfresh)]; exact hpair
    exact Restated.newRound_target_under_new_anchor_rule facts S Sched x hexec hn' hatt hT hconf hg2
      hqfresh hvote hC hCroot

end

end DecoupledConsensusModel.Sts.Restated
