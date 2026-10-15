import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_54b
import Proofs.Claims.Restated.Claim13beRoute3_57
import Proofs.Claims.Restated.Claim13beRoute3_63
import Proofs.Claims.Restated.Claim13beRoute3_69b
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_70b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The FG root against the previous heads after the deadline

The greatest common ancestor of the heads of one slot, and the bound that puts a reader's FG root,
at a read after the progress deadline, as an ancestor of every honest head of a later slot. Stated
over a model `M : Record.Model V` along a path `W` of the run.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Under the bundle along `W` and the committee majority over the family, if `0 < d`, `vote_time d`
    is in the horizon, `lo ≤ vote_time d`, and every committee member of `d` in the set for
    `vote_time d` passes the grade-1 awake test of `d`'s round at each of its ticks at
    `vote_time d`, then for every choice `head` of one outcome of the slot-`d` head computation per
    member of the set for `vote_time d`, some run block `E` read through `Xb` is an ancestor of
    `head w` for every member `w`, and every block that is an ancestor of `head w` for every member
    `w` is an ancestor of `E`. -/
theorem exists_namedGreatestPreviousHeadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {d : Slot} (hd : 0 < d)
    (hhor : M.vote_time S.E d ≤ rho.horizon)
    (hgat : lo ≤ M.vote_time S.E d)
    (head : V → Block V)
    (hhead : ∀ w ∈ Hs (M.vote_time S.E d), ∃ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c ∧
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
      ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T ∧
      ∃ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
      ∃ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
      M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ head w)
    (hrun : ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    ∃ E : NamedBlock V,
      Restated.RunBlockOn M S rho W Xb E ∧
      (∀ w ∈ Hs (M.vote_time S.E d), Block.Preceq E.erase (head w)) ∧
      (∀ B : Block V,
        (∀ w ∈ Hs (M.vote_time S.E d), Block.Preceq B (head w)) →
        Block.Preceq B E.erase) := by
  classical
  have hxcPos : 0 < ((S.E.committee d) ∩ Hs (M.confirmation_time S.E d)).card := by
    have hc := hcom d
    omega
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hxcPos
  have hx0c := (Finset.mem_inter.mp hx0).1
  have hx0v : x0 ∈ Hs (M.vote_time S.E d) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E d) (Finset.mem_inter.mp hx0).2
  let Pred : Block V → Prop := fun B =>
    ∀ w, w ∈ Hs (M.vote_time S.E d) → Block.Preceq B (head w)
  obtain ⟨G, hG, hmax⟩ := greatest_member_of_common_ancestor_bound
    Pred (D := Block.genesis) (H := head x0)
      (fun _ _ => (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)))
      (fun B hB => hB x0 hx0v)
  obtain ⟨c, hc, T, hT, L, hL, L', hL', hHd⟩ := hhead x0 hx0v
  obtain ⟨X, hXerase, hXrun, -⟩ :=
    Restated.voterHead_runBlock_and_emitsOn facts S Hs Xb hf hHsXb hx0v hd hx0c hhor hgat
      c hc (hrun x0 hx0c hx0v) T hT L hL L' hL' (head x0) hHd
  have hGX : Block.Preceq G X.erase := by
    rw [hXerase]
    exact hG x0 hx0v
  obtain ⟨E, hEX, hEerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hGX
  have hErun : Restated.RunBlockOn M S rho W Xb E :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hXrun hEX
  refine ⟨E, hErun, ?_, ?_⟩
  · intro w hw
    rw [hEerase]
    exact hG w hw
  · intro B hB
    rw [hEerase]
    exact hmax B hB

end

/-! ## The theorems about named height regimes -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- The round-`r` action read computed from `before` can give some node state. -/
private theorem actionReadFrom_nonempty₈₆bn (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- If round `r`'s action instant is strictly before slot `s`'s confirmation instant, then `s` is
    after round `r`'s opening slot. -/
private theorem firstInterior_le_of_action_lt_confirmation₈₆bn (facts : Record.Facts M)
    (S : Setup V) {r : Round} {s : Slot}
    (h : Restated.Vocabulary.Execution.Setup.a M S r < M.confirmation_time S.E s) :
    M.opening_slot S.hc r + 1 ≤ s := by
  by_contra hnot
  have hle : s ≤ M.opening_slot S.hc r := Nat.le_of_lt_succ (Nat.lt_of_not_le hnot)
  have hmono := facts.sch.confirmation_time_mono S hle
  have ha : Restated.Vocabulary.Execution.Setup.a M S r =
      M.confirmation_time S.E (M.opening_slot S.hc r) :=
    facts.sch.a_eq_confirmation_time S.hc S.E r
  rw [ha] at h
  exact (not_le_of_gt h) hmono

/-- Under the bundle with path `W`, the committee majority and the weight bound, for a run-scoped
    named regime along `W` with `lo ≤ opening (a.round − η_SG)` and every member of the set for
    `S.a k + Δ` awake at `k`, every read at or after `S.a a.round` in the horizon has the FG root of
    the store, in the world of `W` strictly before the read, of every member of the set for the read
    on one chain with the checkpoint `T`. -/
theorem NamedHeightRegimeRunOn.fgRoot_compatible_after_source_run_l86b (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    {read : Time} (hread : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ read)
    (hreadHor : read ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs read)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Block.compatible
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG) T.erase =
        true :=
  Restated.PrefixFGSelectorConeAtOn.fgRoot_compatible_of_recentWitnessHistory_of_frame_run facts
    hf hHs hHsXb hX hXXb hcom hbelow
    h.seed h.crossing h.frame h.c0le h.ready h.postPrev h.pred h.minimal hread
    (fun r hr ht v hv B hB => by
      obtain ⟨n, hn⟩ := actionReadFrom_nonempty₈₆bn facts S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r
      obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts S n
      exact ((Restated.NamedHeightRegimeRunOn.laterHistory_main facts hf hHs hHsXb hX hXXb
        hcom hbelow h hr hlo hA).2 (ht.le.trans hreadHor)).2 v hv n hn B (hB n hn o ho))
    hw hreadHor hlo hA

/-- Under the bundle with path `W` and the weight bound, with `X` containing every set of the family
    from instant `0` and inside `Xb`: if `gstLagged ≤ Γ_neg1 r0`, the `lo` bounds hold, and a
    run-scoped named base holds along `W` at `blocked` with its first crossing by the inclusive
    index of `S.a deadline`, then some run-scoped named regime of the base along `W` has its source
    round at or before `deadline`. -/
theorem NamedHeightRegimeBaseRunOn.exists_regime_before_deadline (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hbelow : BelowOneThirdOn S rho Hs)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (h : Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first Tprev)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    {deadline : Round}
    (hdeadline : first ≤
      inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline)) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time) (Cfg T : NamedBlock V),
      Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
        Hs X Xb r0 blocked first i a ta Cfg T Tprev a.round ∧
        a.round ≤ deadline := by
  obtain ⟨i, a, ta, Cfg, T, hreg⟩ :=
    Restated.NamedHeightRegimeBaseRunOn.exists_regime_closed facts hf hHs hHsXb hX hXXb
      hbelow hgst h hgstLo hloOpen
  refine ⟨i, a, ta, Cfg, T, hreg, ?_⟩
  have hi : i < inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline) :=
    hreg.seed.indexLtStop.trans_le hdeadline
  have hfilter :
      rho.events.filter
          (fun e => decide (e.time ≤ Restated.Vocabulary.Execution.Setup.a M S deadline)) =
        rho.events.take
          (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline)) := by
    simpa only [inclusiveEventIndex] using
      Restated.filter_eq_takeOn facts S Hs Xb hf _
        (Restated.downward_le (Restated.Vocabulary.Execution.Setup.a M S deadline))
  have hmem : Record.Event.tick a.val_index ta ∈
      rho.events.take
        (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline)) := by
    apply List.mem_of_getElem? (i := i)
    rw [List.getElem?_take_of_lt hi]
    exact hreg.seed.exactTick
  rw [← hfilter] at hmem
  apply (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).le_iff_le.mp
  simpa only [Record.Event.time, hreg.seed.actionTime_eq, decide_eq_true_eq, Record.Event.time] using
    (List.mem_filter.mp hmem).2

/-- Under the bundle with path `W`, the committee majority and the weight bound, with `X` containing
    every set of the family from instant `0` and inside `Xb`: if `gstLagged ≤ Γ_neg1 r0`, a
    run-scoped named base holds along `W` at `blocked` whose first crossing is by the inclusive
    index of `S.a deadline`, `read` is between `S.a deadline` and the horizon, `s` is after the
    deadline's opening slot with `read ≤ confirmation_time s` and `vote_time s + Δ` in the horizon,
    `u` is in the set for `read`, and the `lo` bounds hold, then the FG root of `u`'s store in the
    world of `W` strictly before `read` is an ancestor of every head that every member of the set
    for `vote_time s` can vote at `s`. -/
theorem NamedHeightRegimeBaseRunOn.fgRoot_preceq_previousHead_through_confirmation_after_deadline
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (h : Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first Tprev)
    {deadline : Round}
    (hdeadline : first ≤
      inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline))
    {read : Time} (hread : Restated.Vocabulary.Execution.Setup.a M S deadline ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot} (hs : M.opening_slot S.hc deadline + 1 ≤ s)
    (hnext : read ≤ M.confirmation_time S.E s)
    (hshor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs read)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ w ∈ Hs (M.vote_time S.E s), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
        (M.vote_time S.E s)
        (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
          (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq
          (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) H := by
  intro w hw cc hcc n Tr hTr L hL L' hL' H hH
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hbelow
  rcases Restated.fgRoot_confirmationWitness_at_readOn facts S Hs Xb hf hHs hHsXb hmajority
      (hHsXb _ hu) read hhor with
    hgen | ⟨C, hC, hJ, b, tb, hb, hemit, hbt, hpair, hW⟩
  · rw [hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
  · by_cases hsmall : (M.derive_named S.E S.cfg C).h_j ≤ blocked
    · obtain ⟨i, a, ta, Cfg, T, hreg, ha⟩ :=
        Restated.NamedHeightRegimeBaseRunOn.exists_regime_before_deadline facts hf hHs
          hHsXb hX hXXb hbelow hgst h hgstLo hloOpen hdeadline
      have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
      have hRT := Restated.NamedHeightRegimeRunOn.fgRoot_compatible_after_source_run_l86b
        facts hf hHs hHsXb hX hXXb hcom hbelow hreg
        (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone ha).trans
          hread) hhor hu hlo hA
      have hRTpre : Block.Preceq
          (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG)
          T.erase := by
        by_cases hz : (M.derive_named S.E S.cfg C).h_j = 0
        · have hgenJ := facts.cs.justified_zero_is_genesis S.E S.cfg C hz
          rw [← hJ, hgenJ]
          exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
        · obtain ⟨J, hJC, hJerase, hJheight⟩ :=
            (facts.cs.justified_ancestor_height S.E S.cfg C).resolve_left hz
          have hCrun : Restated.RunBlockOn M S rho W Xb C :=
            Restated.lifecycle_runBlock_of_mem_storeBeforeTimeOn facts S Hs Xb hf (hHsXb _ hu) hC
          have hJrun : Restated.RunBlockOn M S rho W Xb J :=
            Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hJC
          obtain ⟨hTrun, hTheight⟩ :=
            Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb hreg
          rcases (show Block.Preceq
                (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG)
                T.erase ∨
              Block.Preceq T.erase
                (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) from
            compatible_cases hRT) with
            hRT' | hTR
          · exact hRT'
          · have hTJ : NamedBlock.Preceq T J :=
              Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTrun hJrun
                (by rw [hJerase, hJ]; exact hTR)
            have hmono := facts.cs.derive_height_mono S.E S.cfg hTJ
            rw [hTheight, hJheight] at hmono
            exact False.elim (Nat.not_succ_le_self blocked (hmono.trans hsmall))
      exact preceq_trans_Preceq hRTpre
        (Restated.NamedHeightRegimeRunOn.heads_from_firstInterior facts hf hHs hHsXb hX
          hXXb hcom hbelow hreg
          ((Nat.add_le_add_right (facts.gr.opening_slot_le_of_le S.hc ha) 1).trans hs)
          hshor hlo hA w hw cc hcc Tr hTr L hL L' hL' H hH)
    · let m := (M.derive_named S.E S.cfg C).h_j - (blocked + 1)
      have heq : blocked + m + 1 = (M.derive_named S.E S.cfg C).h_j := by
        calc
          _ = m + (blocked + 1) := by ac_rfl
          _ = (M.derive_named S.E S.cfg C).h_j :=
            Nat.sub_add_cancel (Nat.lt_of_not_ge hsmall)
      have hrow : b.height_pair.erase.height? = some (blocked + m + 1) := by
        rw [hpair]
        exact congrArg some heq.symm
      have hbT : b.val_index ∈ Hs tb := hHs _ _ hbt.le hb
      obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
        Restated.NamedHeightRegimeBaseRunOn.exists_regime_of_row_named facts hf hHs hHsXb
          hX hXXb hcom hbelow hgst h m hbT hemit hrow hgstLo hloOpen hA
      have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
      obtain ⟨nb, hnb⟩ := actionReadFrom_nonempty₈₆bn facts S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
        b.round
      obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts S nb
      have hTR : T.erase =
          M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG :=
        (Option.some.inj
          (Restated.NamedHeightRegimeRunOn.witness_eq facts hf hHs hHsXb hX hXXb hcom
            hbelow hreg hbT hemit hrow hlo hA nb hnb _ (hW nb hnb o ho))).symm
      have hact : Restated.Vocabulary.Execution.Setup.a M S b.round < read := by
        rw [← (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath
          hemit).2]
        exact hbt
      have hbs := firstInterior_le_of_action_lt_confirmation₈₆bn facts S (hact.trans_le hnext)
      have hab : a.round ≤ b.round := hreg.minimal b tb hbT hemit hrow
      have hopen : M.opening_slot S.hc a.round + 1 ≤ s :=
        (Nat.add_le_add_right (facts.gr.opening_slot_le_of_le S.hc hab) 1).trans hbs
      rw [← hTR]
      exact Restated.NamedHeightRegimeRunOn.heads_from_firstInterior facts hf hHs hHsXb hX
        hXXb hcom hbelow hreg hopen hshor hlo hA w hw cc hcc Tr hTr L hL L' hL' H hH

/-- Under the bundle with path `W`, the committee majority and weight bound per instant, the
    recurrence of carrier rounds within `gap` from `t₀` and the timeout delay bound, with
    `t_GST ≤ S.a rGST`: for a read at or after the action instant of the progress deadline from
    `rGST` within the horizon, a slot `s` after the deadline's opening slot with
    `read ≤ confirmation_time s` and `vote_time s + Δ` within the horizon, and a reader `u` in the
    set for `read`, if `lo ≤ S.a rGST`, `lo ≤ opening (rGST + 2 − η_SG)`, `t₀ ≤ S.a (rGST + 2)` and
    every member of the set for `S.a k + Δ` is awake at `k`, then the FG root of `u`'s store in the
    world of `W` strictly before `read` is an ancestor of every head that every member of the set
    for `vote_time s` can vote at `s`. -/
theorem fgRoot_preceq_previousHead_through_confirmation_after_GSTOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {read : Time}
    (hread : (Restated.Vocabulary.Execution.Setup.a M S
      (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot}
    (hs : (M.opening_slot S.hc)
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hnext : read ≤ M.confirmation_time S.E s)
    (hshor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs read)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ w ∈ Hs (M.vote_time S.E s), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
        (M.vote_time S.E s)
        (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
          (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq
          (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) H := by
  have hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ Xb := fun t _ => hHsXb t
  have hXXb : Xb ⊆ Xb := Finset.Subset.refl _
  have hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)) :=
    hloPost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right rGST 2))
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn facts
      S Hs Xb Xb hf hHs hHsXb hX hXXb hcom hbelow hrec hdelay hpost (hread.trans hhor)
      hlo hloOpen ht₀ hA
  exact Restated.NamedHeightRegimeBaseRunOn.fgRoot_preceq_previousHead_through_confirmation_after_deadline
    facts hf hHs hHsXb hX hXXb hcom hbelow
    (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S rGST hpost)
    hbase hfirst hread hhor hs hnext hshor hu
    (Restated.lo_add_lag_le_Γ_neg1_l71 facts S rGST hloPost) hloOpen hA

end

end DecoupledConsensusModel.Sts.Restated
