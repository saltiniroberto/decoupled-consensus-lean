import Model.Record.Wiring
import Model.Record.ModelSpellings
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Spec2Claims.Claim13bModel_domain
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption
import Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
import Proofs.Vocabulary.Protocol.Duties.Inputs.ActionSources
import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions
import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
import Proofs.Vocabulary.Execution.BodyRetention
import Proofs.Vocabulary.Protocol.Store.RawSource
import Proofs.Vocabulary.Protocol.Grades.Interpolation
import Proofs.Vocabulary.Protocol.Handlers.HMaxMonotone
import Proofs.Vocabulary.Protocol.Handlers.NumericStore
import Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
import Proofs.Vocabulary.Protocol.Schedule.ReceiptCallsF1
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOld
import Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_early_mk
import Proofs.Vocabulary.Protocol.Grades.CacheProvenance
import Proofs.Vocabulary.Protocol.Grades.JointHistoryProducers
import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.ProcessedFlip
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_mk_s4
import Proofs.Claims.Spec2Claims.Claim13bModel_a
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOldHeads
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_score
import Proofs.Vocabulary.Protocol.Store.PublicCutSG
import Proofs.Vocabulary.Protocol.Grades.Q10Frame
import Proofs.Vocabulary.Protocol.Grades.FrameCompleted
import Proofs.Claims.Spec2Claims.Claim13bModel_early
import Proofs.Claims.Spec2Claims.Claim13bModel_late
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_Opposes

/-!
# The facts of the grades routines

`GradesFacts` holds the facts about the grades routines of a model `M` that the proofs over the
record call: the order of a round's cutoffs and domain instants, the slot arithmetic of rounds, and
what the grade test, the frames, the caches and the SG walk guarantee on any input. `GradesRunFacts`
holds the facts about runs of the same routines.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Engine
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Internal.PhaseGrades DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes)
open DecoupledConsensusModel.Proofs.HealingLemmas
open Execution (Setup)
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open Execution
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (HeightConfig)
open Protocol (own_lock)
open Internal.HealingSurface
open Proofs.HealingLemmas
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.ModelProperties
open DecoupledConsensusModel.Proofs.NamedConfirmationMembership
open Protocol
open Execution Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Execution Internal.NamedOutageEntry DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)
open Internal Execution Internal.PhaseGrades DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes)
open DecoupledConsensusModel.Proofs.NamedProposalParent
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)
open scoped DC

/-- The facts about the grades routines of `M`: the order of a round's cutoffs and domain instants,
    the slot arithmetic of rounds, and what the grade test, the frames, the caches and the SG walk
    guarantee on any input. -/
structure GradesFacts (M : Model V) : Prop where
  /-- A round's phase domain instant is at or before that round's action instant. -/
  domain_le_action : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase),
    M.domain S.E S.hc r p ≤ M.a S.hc S.E.Δ r
  /-- The action instant of round `r + 1` is the action instant of round `r` plus the round length
      `4ΔR`. -/
  healA_succ_round : ∀ (hc : Protocol.HealConfig) (Δ : Int) (r : Round),
    M.a hc Δ (r + 1) = M.a hc Δ r + 4 * Δ * (hc.R : Int)
  /-- The opening instant of round `r + k` is the opening instant of round `r` plus `k` times the
      round length `4ΔR`. -/
  opening_add : ∀ (E : Env V) (hc : Protocol.HealConfig) (r k : Round),
    M.opening E hc (r + k) = M.opening E hc r + (k : Int) * (4 * E.Δ * (hc.R : Int))
  /-- The opening instant of round `r` is the proposal instant of round `r`'s opening slot. -/
  opening_eq_proposal_time : ∀ (E : Env V) (hc : Protocol.HealConfig) (r : Round), M.opening E hc r = M.proposal_time E (M.opening_slot hc r)
  /-- A round's G2 early cutoff is at or before the round's opening instant. -/
  early_g2_le_opening : ∀ (S : Setup V) (r : Round),
    M.early S.E S.hc r .g2 ≤ M.opening S.E S.hc r
  /-- Round `r + 1`'s action instant is `4 * S.hc.R * S.E.Δ` after round `r`'s. -/
  action_succ_eq_add_rounds : ∀ (S : Setup V) (r : Round),
    Restated.Vocabulary.Execution.Setup.a M S (r + 1) =
      Restated.Vocabulary.Execution.Setup.a M S r + 4 * (S.hc.R : Int) * S.E.Δ
  /-- The instant at which round `r`'s grade `p` is computed is at or before round `r`'s action
      instant. -/
  domain_le_a : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase),
    M.domain S.E S.hc r p ≤ M.a S.hc S.E.Δ r
  /-- If `tGAT + 8RΔ ≤ tE' ≤ opening r₀ < tE` and `1 ≤ r₀`, then the attestation window
      `[a (r₀ − 1) − wAttest, a (r₀ − 1)]` lies inside `[tGAT, tE]`, and its end is at or before
      `opening (r₀ + 1)`. -/
  attestWindow_prev_inPhase : ∀ (S : Setup V) (tGAT tE tE' : Int) {r₀ : Nat}
    (hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE') (hr1 : 1 ≤ r₀)
    (hr' : tE' ≤ M.opening S.E S.hc r₀) (hrE : M.opening S.E S.hc r₀ < tE),
    tGAT ≤ (M.a S.hc S.E.Δ (r₀ - 1)) - wAttest S ∧
      (M.a S.hc S.E.Δ (r₀ - 1)) ≤ tE ∧
      (M.a S.hc S.E.Δ (r₀ - 1)) ≤ M.opening S.E S.hc (r₀ + 1)
  /-- Round `r + tE.toNat` opens at or after `tE`. -/
  le_opening_add_toNat : ∀ (S : Setup V) (r : Nat) (tE : Int),
    tE ≤ M.opening S.E S.hc (r + tE.toNat)
  /-- For every phase `p`, round `r`'s domain instant for `p`, plus five delays, is at or before
      round `r`'s action instant. -/
  domain_add_five_delta_le_action : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase),
    M.domain S.E S.hc r p + 5 * S.E.Δ ≤ M.a S.hc S.E.Δ r
  /-- Source support for `B` is target support for `B`, when the source tokens are nested early in
      late in raw, the target early tokens are among the target late tokens, every source early
      token covering `B` reaches the target early tokens or a target raw equivocation at its round,
      and every target late token and raw equivocation comes back as a source one. -/
  supports_transport_with_cap : ∀ {Key Blk : Type} (covers : Key → Blk → Prop)
    {se sl sr te tl tr : Finset (Token Key)} {B : Blk}
    (hSourceLate : se ⊆ sl) (hSourceRaw : sl ⊆ sr) (hTargetLate : te ⊆ tl)
    (hForward : ∀ u ∈ se, covers u.key B → u ∈ te ∨ DecoupledConsensusModel.Protocol.EquivocationAt tr u.round)
    (hLateBack : ∀ x ∈ tl, x ∈ sl ∨ DecoupledConsensusModel.Protocol.EquivocationAt sr x.round)
    (hEqBack : ∀ k, DecoupledConsensusModel.Protocol.EquivocationAt tr k → DecoupledConsensusModel.Protocol.EquivocationAt sr k)
    (h : M.Supports covers se sl sr B), M.Supports covers te tl tr B
  /-- Target opposition to `B` is source opposition to `B`, when the source early tokens are among
      the source late tokens, every source early token covering `B` reaches the target early tokens
      or a target raw equivocation at its round, and every target late token and raw equivocation
      comes back as a source one. -/
  opposition_back_with_cap : ∀ {Key Blk : Type} (covers : Key → Blk → Prop)
    {se sl sr te tl tr : Finset (Token Key)} {B : Blk}
    (hSourceLate : se ⊆ sl)
    (hForward : ∀ u ∈ se, covers u.key B → u ∈ te ∨ DecoupledConsensusModel.Protocol.EquivocationAt tr u.round)
    (hLateBack : ∀ x ∈ tl, x ∈ sl ∨ DecoupledConsensusModel.Protocol.EquivocationAt sr x.round)
    (hEqBack : ∀ k, DecoupledConsensusModel.Protocol.EquivocationAt tr k → DecoupledConsensusModel.Protocol.EquivocationAt sr k)
    (h : M.Opposes covers te tl tr B), M.Opposes covers se sl sr B
  /-- The grade-2 early cutoff of round `r` is `11Δ` before round `r`'s action instant. -/
  early_g2_eq : ∀ (S : Setup V) (r : Round), M.early S.E S.hc r .g2 = M.a S.hc S.E.Δ r - 11 * S.E.Δ
  /-- The grade-1 early cutoff of round `r` is `10Δ` before round `r`'s action instant. -/
  early_g1_eq : ∀ (S : Setup V) (r : Round), M.early S.E S.hc r .g1 = M.a S.hc S.E.Δ r - 10 * S.E.Δ
  /-- One delay after the action instant of round `r` is at or before the earliest grade cutoff of
      round `r + 1`, one delay before the start of that round's opening slot. -/
  action_add_delta_le_next_Γ_neg1 : ∀ (S : Setup V) (r : Round),
    M.a S.hc S.E.Δ r + S.E.Δ ≤ slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) - S.E.Δ
  /-- The earliest grade cutoff of round `r + 1`, one delay before the start of its opening slot, is
      the G2 domain instant of round `r + 1`. -/
  gammaNeg1_eq_domain_g2_succ : ∀ (S : Setup V) (r : Round),
    slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) - S.E.Δ = M.domain S.E S.hc (r + 1) .g2
  /-- With at least three slots per round, one delay after the action instant of round `q` is at or
      before the G2 early cutoff of any later round `r`. -/
  action_delta_le_early : ∀ (S : Setup V) {q r : Round} (hR : 3 ≤ S.hc.R) (hqr : q < r),
    M.a S.hc S.E.Δ q + S.E.Δ ≤ M.early S.E S.hc r .g2
  /-- The action instant of round `r + k` is the action instant of round `r` plus `k` round lengths
      of `4Δ·R` each. -/
  a_add_rounds : ∀ (S : Setup V) (r k : Round), M.a S.hc S.E.Δ (r + k) = M.a S.hc S.E.Δ r + 4 * S.E.Δ * ((S.hc.R * k : Nat) : Time)
  /-- If `floor` is absent or an ancestor of `B` (or `B` itself), `B` is on the chain of `C`, and
      `B` passes `test`, then the deepest clear ancestor of `C` from `floor` exists. -/
  deepest_clear_isSome_of_mem : ∀ {floor : Option (DecoupledConsensusModel.Block V)} {C B : DecoupledConsensusModel.Block V} {test : DecoupledConsensusModel.Block V → Bool}, (floor.elim True fun a ↦ a.preceq B = Bool.true) → B ∈ M.chain_of C → test B = Bool.true → (M.deepest_clear floor C test).isSome = Bool.true
  /-- The grade view does not read the clock or the slot of the store. -/
  gradeView_toHealing_clock : ∀ (st : M.S) (t : DecoupledConsensusModel.Time) (s : DecoupledConsensusModel.Slot), (M.gradeView (M.toHealing (M.store_with_t_s st t s))) = (M.gradeView (M.toHealing st))
  /-- A phase result present in the cache aligned to the tick's round survives the preparation at
      the tick, clipped to the store's finalized block, in every outcome. -/
  onPhaseTick_phase_of_align : ∀ (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.HS) (t : DecoupledConsensusModel.Time) (c : M.Cache) (r : DecoupledConsensusModel.Round) (p : DecoupledConsensusModel.Protocol.Phase), M.phaseResult (M.cacheAtRound (M.alignRound c ((M.round_of hc (E.slotOf t)))) r) p ≠ Option.none → ∀ c'' : M.Cache, M.onPhaseTick E hc st t c ⇢ c'' → ∀ (hn : M.reachedRead st c := by trivial), M.phaseResult (M.cacheAtRound c'' r) p = M.clipResult st.toFG.F (M.phaseResult (M.cacheAtRound (M.alignRound c ((M.round_of hc (E.slotOf t)))) r) p)
  /-- If the early tokens are among the late tokens and are not empty, then the tokens either oppose
      `B` or support `B`. -/
  q10_supports_of_not_opposes : ∀ {Key : Type} {Blk : Type} (c : Key → Blk → Prop) {e l raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, e ⊆ l → e.Nonempty → ¬M.Opposes c e l raw B → M.Supports c e l raw B
  /-- If the cover tests `c` and `c'` agree on `B` for the key of every late token, then tokens that
      oppose `B` under `c` oppose it under `c'`. -/
  opposes_congr : ∀ {Key : Type} {Blk : Type} (c c' : Key → Blk → Prop) {e l raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, (∀ x ∈ l, c x.key B ↔ c' x.key B) → M.Opposes c e l raw B → M.Opposes c' e l raw B
  /-- If the early tokens are among the late tokens and the cover tests `c` and `c'` agree on `B`
      for the key of every late token, then tokens that support `B` under `c` support it under `c'`. -/
  supports_congr : ∀ {Key : Type} {Blk : Type} (c c' : Key → Blk → Prop) {e l raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, e ⊆ l → (∀ x ∈ l, c x.key B ↔ c' x.key B) → M.Supports c e l raw B → M.Supports c' e l raw B
  /-- Aligning a cache to round `r₀` sets its round to `r₀`. -/
  alignRound_round : ∀ (c : M.Cache) (r₀ : DecoupledConsensusModel.Round), (M.alignRound c r₀).round = r₀
  /-- Every outcome `A` of `M.anchor` at a grade-1 result `g1` is the store's `M.get_fg_root`, or
      `g1` is a completed grade-1 root and `A` is an ancestor of it. -/
  Sts_anchor_cases : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (stH : M.HS) (r₁ : DecoupledConsensusModel.Round) (g1 : Option (Option (DecoupledConsensusModel.Block V))) (A : DecoupledConsensusModel.Block V), M.anchor S.E S.hc stH r₁ g1 ⇢ A → A = M.get_fg_root stH.toFG ∨ ∃ root, g1 = Option.some (Option.some root) ∧ A.Preceq root
  /-- Every outcome of `M.anchor` is compatible with `T` when every grade-1 root in `g1` and the
      store's `M.get_fg_root` are. -/
  anchor_compatible : ∀ (S : DecoupledConsensusModel.Execution.Setup V) {stH : M.HS} {T : DecoupledConsensusModel.Block V} {r₁ : DecoupledConsensusModel.Round} {g1 : Option (Option (DecoupledConsensusModel.Block V))}, (∀ (root : DecoupledConsensusModel.Block V), g1 = Option.some (Option.some root) → root.compatible T = Bool.true) → (M.get_fg_root stH.toFG).compatible T = Bool.true → ∀ A : DecoupledConsensusModel.Block V, M.anchor S.E S.hc stH r₁ g1 ⇢ A → A.compatible T = Bool.true
  /-- If the SG vote `u` names a root that the grade view's tree does not hold, every outcome of the
      body condition for `u` is `false`. -/
  bodyReady_eq_false_of_find_none : ∀ (gv : M.GV) (F : DecoupledConsensusModel.Block V) (cutoff : DecoupledConsensusModel.Time) (u : DecoupledConsensusModel.Protocol.SGVote V) {root : DecoupledConsensusModel.BlockId}, u.confirmed = Option.some root → DecoupledConsensusModel.Block.find? gv.T root = Option.none → ∀ b : Bool, M.bodyReady gv F cutoff u ⇢ b → b = Bool.false
  /-- If the SG vote `u` confirms no root, every outcome of the body condition for `u` is `true`. -/
  bodyReady_of_confirmed_none : ∀ {gv : M.GV} {F : DecoupledConsensusModel.Block V} {cutoff : DecoupledConsensusModel.Time} {u : DecoupledConsensusModel.Protocol.SGVote V}, u.confirmed = Option.none → ∀ b : Bool, M.bodyReady gv F cutoff u ⇢ b → b = Bool.true
  /-- If the SG vote `u` names a root that resolves in the grade view's tree to a block `H` stamped
      before `cutoff` and compatible with `F`, every outcome of the body condition for `u` is
      `true`. -/
  bodyReady_of_find : ∀ {gv : M.GV} {F : DecoupledConsensusModel.Block V} {cutoff : DecoupledConsensusModel.Time} {u : DecoupledConsensusModel.Protocol.SGVote V} {root : DecoupledConsensusModel.BlockId} {H : DecoupledConsensusModel.Block V}, u.confirmed = Option.some root → DecoupledConsensusModel.Block.find? gv.T root = Option.some H → DecoupledConsensusModel.stampedBefore gv.timestamp_block cutoff H = Bool.true → H.compatible F = Bool.true → ∀ b : Bool, M.bodyReady gv F cutoff u ⇢ b → b = Bool.true
  /-- If the SG vote `u` names a root that resolves in the grade view's tree to a block `H` stamped
      before `cutoff` and compatible with `F`, every outcome of the body condition for `u` is
      `true`. -/
  bodyReady_of_head : ∀ (gv : M.GV) (F : DecoupledConsensusModel.Block V) (cutoff : ℤ) (u : DecoupledConsensusModel.Protocol.SGVote V) {root : DecoupledConsensusModel.BlockId} {H : DecoupledConsensusModel.Block V}, u.confirmed = Option.some root → DecoupledConsensusModel.Block.find? gv.T root = Option.some H → DecoupledConsensusModel.stampedBefore gv.timestamp_block cutoff H = Bool.true → H.compatible F = Bool.true → ∀ b : Bool, M.bodyReady gv F cutoff u ⇢ b → b = Bool.true
  /-- If the SG vote `u` names no root, every outcome of the body condition for `u` is `true`. -/
  bodyReady_of_no_head : ∀ (gv : M.GV) (F : DecoupledConsensusModel.Block V) (cutoff : ℤ) (u : DecoupledConsensusModel.Protocol.SGVote V), u.confirmed = Option.none → ∀ b : Bool, M.bodyReady gv F cutoff u ⇢ b → b = Bool.true
  /-- If an outcome of the body condition for the SG vote `u` is `true` and `u` names the root
      `root`, then the grade view's tree resolves `root` to a block `H`, stamped before `cutoff` and
      compatible with `F`. -/
  bodyReady_parts : ∀ {gv : M.GV} {F : DecoupledConsensusModel.Block V} {cutoff : DecoupledConsensusModel.Time} {u : DecoupledConsensusModel.Protocol.SGVote V} {root : DecoupledConsensusModel.BlockId} (b : Bool), M.bodyReady gv F cutoff u ⇢ b → b = Bool.true → u.confirmed = Option.some root → ∃ H, DecoupledConsensusModel.Block.find? gv.T root = Option.some H ∧ DecoupledConsensusModel.stampedBefore gv.timestamp_block cutoff H = Bool.true ∧ H.compatible F = Bool.true
  /-- If any two tokens of `raw` of one round, at least `k`, carry the same key, then `raw` is clean
      from round `k` on. -/
  cleanFrom_intro : ∀ {Key : Type} {raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {k : ℕ}, (∀ x ∈ raw, ∀ y ∈ raw, k ≤ x.round → x.round = y.round → x.key = y.key) → M.CleanFrom raw k
  /-- If the frame's grade-0 entry is the root `root`, the frame's test at `B` answers whether `B`
      is compatible with `root`. -/
  clear_of_g0 : ∀ {frame : M.Frame} {root : DecoupledConsensusModel.Block V}, frame.g0 = Option.some (Option.some root) → ∀ (B : DecoupledConsensusModel.Block V), M.clear frame B = B.compatible root
  /-- If the frame's grade-0 entry is a completed phase with no root, every block passes the frame's
      test. -/
  clear_of_g0_some_none : ∀ {frame : M.Frame}, frame.g0 = Option.some Option.none → ∀ (B : DecoupledConsensusModel.Block V), M.clear frame B = Bool.true
  /-- If the frame's grade-0 entry is no root, every block passes the frame's test. -/
  clear_of_g0_ne : ∀ {frame : M.Frame}, (∀ root : DecoupledConsensusModel.Block V, frame.g0 ≠ Option.some (Option.some root)) → ∀ (B : DecoupledConsensusModel.Block V), M.clear frame B = Bool.true
  /-- A block that passes a frame's test is compatible with the frame's grade-0 root. -/
  compatible_of_clear : ∀ {frame : M.Frame} {B root : DecoupledConsensusModel.Block V}, M.clear frame B = Bool.true → frame.g0 = Option.some (Option.some root) → B.compatible root = Bool.true
  /-- If the clearing walk from the anchor finds no block on the store's confirmed chain and the
      grade read offers the grade-2 candidate `Q`, the SG walk returns `Q`. -/
  Sts_currentSGVote_of_Q2 : ∀ {stH : M.HS} {grades : DecoupledConsensusModel.Protocol.GradeRead V} {Q : DecoupledConsensusModel.Block V}, M.deepest_clear (Option.some grades.anchor) stH.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = Option.none → grades.Q2 = Option.some Q → M.currentSGVote stH grades = Q
  /-- If the clearing walk finds no block and the grade read offers no grade-2 candidate, the SG
      walk returns the store's `M.get_fg_root` or the grade read's anchor. -/
  currentSGVote_of_none_none : ∀ {stH : M.HS} {grades : DecoupledConsensusModel.Protocol.GradeRead V}, M.deepest_clear (Option.some grades.anchor) stH.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = Option.none → grades.Q2 = Option.none → M.currentSGVote stH grades = M.get_fg_root stH.toFG ∨ M.currentSGVote stH grades = grades.anchor
  /-- If the SG vote `u` names the root `root` and an outcome of the body condition for `u` is
      `true`, then `root` resolves in the grade view's tree to a block `H`, stamped before `cutoff`
      and compatible with `F`. -/
  exists_find_of_bodyReady : ∀ {gv : M.GV} {F : DecoupledConsensusModel.Block V} {cutoff : DecoupledConsensusModel.Time} {u : DecoupledConsensusModel.Protocol.SGVote V} {root : DecoupledConsensusModel.BlockId}, u.confirmed = Option.some root → ∀ b : Bool, M.bodyReady gv F cutoff u ⇢ b → b = Bool.true → ∃ H, DecoupledConsensusModel.Block.find? gv.T root = Option.some H ∧ DecoupledConsensusModel.stampedBefore gv.timestamp_block cutoff H = Bool.true ∧ H.compatible F = Bool.true
  /-- A token in an outcome of `v`'s raw view of a grade is the token of some attestation in every
      outcome of `v`'s raw inputs to that grade. -/
  exists_rawInputs_of_mem_rawView : ∀ {gv : M.GV} {η r : DecoupledConsensusModel.Round} {c : DecoupledConsensusModel.Time} {v : V} {tok : DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId)} (X : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.rawView gv η r c v ⇢ X → tok ∈ X → ∀ Y : Finset (DecoupledConsensusModel.Protocol.SGVote V), M.rawInputs gv η r c v ⇢ Y → ∃ y ∈ Y, M.token y = tok
  /-- The anchor of every outcome of `M.frameGradeRead` is every outcome of `M.anchor` at the
      grade-1 result of the frame read from the cache. -/
  frameGradeRead_anchor : ∀ (c : M.Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.HS) (r : DecoupledConsensusModel.Round), ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, M.frameGradeRead c E hc st r ⇢ g → ∀ a : DecoupledConsensusModel.Block V, M.anchor E hc st r (M.readFrame c st r).g1 ⇢ a → g.anchor = a
  /-- The test of every outcome of `M.frameGradeRead` is `M.clear` of the round-`r` frame read from
      the cache. -/
  frameGradeRead_clear : ∀ (c : M.Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.HS) (r : DecoupledConsensusModel.Round), ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, M.frameGradeRead c E hc st r ⇢ g → g.clear = M.clear (M.readFrame c st r)
  /-- If `raw` is clean from round `k` on, any two of its tokens of one round, at least `k`, carry
      the same key. -/
  key_eq_of_cleanFrom : ∀ {Key : Type} {raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {k : ℕ}, M.CleanFrom raw k → ∀ x ∈ raw, ∀ y ∈ raw, k ≤ x.round → x.round = y.round → x.key = y.key
  /-- An attestation is in an outcome of `v`'s interpreted inputs exactly when it is in the raw
      inputs and passes the body condition. -/
  mem_interpretedInputs_iff : ∀ {gv : M.GV} {F : DecoupledConsensusModel.Block V} {η r : DecoupledConsensusModel.Round} {c : DecoupledConsensusModel.Time} {v : V} {y : DecoupledConsensusModel.Protocol.SGVote V}
    (I : Finset (DecoupledConsensusModel.Protocol.SGVote V)) (hI : M.interpretedInputs gv F η r c v ⇢ I)
    (R : Finset (DecoupledConsensusModel.Protocol.SGVote V)) (hR : M.rawInputs gv η r c v ⇢ R)
    (b : Bool) (hb : M.bodyReady gv F c y ⇢ b),
    y ∈ I ↔ y ∈ R ∧ b = Bool.true
  /-- The opening slot of round `r + k` is the opening slot of round `r` plus `k * R`. -/
  opening_slot_add_mk : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (r k : DecoupledConsensusModel.Round), (M.opening_slot hc (r + k)) = (M.opening_slot hc r) + k * hc.R
  /-- The opening slot of round `r + 1` is the opening slot of round `r` plus `R`. -/
  opening_slot_succ_mk : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round), (M.opening_slot hc (r + 1)) = (M.opening_slot hc r) + hc.R
  /-- The opening slot of round `0` is slot `0`. -/
  opening_slot_zero_mk : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig), (M.opening_slot hc 0) = 0
  /-- If the tokens oppose `B`, either some late token, of a round at least every early token's,
      does not cover `B`, or two raw tokens of one round, at least every early token's, carry
      different keys. -/
  opposes_cases : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, M.Opposes covers early late raw B → (∃ x ∈ late, (∀ u ∈ early, u.round ≤ x.round) ∧ ¬covers x.key B) ∨ ∃ x ∈ raw, ∃ y ∈ raw, (∀ u ∈ early, u.round ≤ x.round) ∧ x.round = y.round ∧ x.key ≠ y.key
  /-- A late token whose round is at least every early token's and whose key does not cover `B`
      makes the tokens oppose `B`. -/
  opposes_of_late : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, ∀ x ∈ late, (∀ u ∈ early, u.round ≤ x.round) → ¬covers x.key B → M.Opposes covers early late raw B
  /-- If an outcome of the opposition test of the sender `u` for `B` is `true`, then `u`'s early
      ready, late ready and late raw tokens oppose `B`, for every choice of outcomes of the cover
      test and of those views. -/
  opposes_of_opposing : ∀ {gv : M.GV} {F : DecoupledConsensusModel.Block V} {η r : DecoupledConsensusModel.Round} {early late : DecoupledConsensusModel.Time} {u : V} {B : DecoupledConsensusModel.Block V} (o : Bool), M.opposing gv F η r early late u B ⇢ o → o = Bool.true →
    ∀ (cov : Option DecoupledConsensusModel.BlockId → DecoupledConsensusModel.Block V → Bool), (∀ k b, M.localCovers gv k b ⇢ cov k b) →
    ∀ (Re : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.readyView gv F η r early u ⇢ Re →
    ∀ (Rl : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.readyView gv F η r late u ⇢ Rl →
    ∀ (W : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.rawView gv η r late u ⇢ W →
    M.Opposes (fun k b ↦ cov k b = Bool.true) Re Rl W B
  /-- If `u`'s early ready, late ready and late raw tokens oppose `B` under a choice `cov` of
      outcomes of the cover test, every outcome of the opposition test of `u` for `B` is `true`. -/
  opposing_of_Opposes : ∀ (gv : M.GV) (F : DecoupledConsensusModel.Block V) (η r : DecoupledConsensusModel.Round) (early late : DecoupledConsensusModel.Time) (u : V) (B : DecoupledConsensusModel.Block V)
    (cov : Option DecoupledConsensusModel.BlockId → DecoupledConsensusModel.Block V → Bool), (∀ k b, M.localCovers gv k b ⇢ cov k b) →
    ∀ (Re : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.readyView gv F η r early u ⇢ Re →
    ∀ (Rl : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.readyView gv F η r late u ⇢ Rl →
    ∀ (W : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.rawView gv η r late u ⇢ W →
    M.Opposes (fun k b ↦ cov k b = Bool.true) Re Rl W B → ∀ o : Bool, M.opposing gv F η r early late u B ⇢ o → o = Bool.true
  /-- If `u`'s early ready, late ready and late raw tokens support `B` under a choice `cov` of
      outcomes of the cover test, every outcome of the support test of `u` for `B` is `true`. -/
  positive_of_Supports : ∀ (gv : M.GV) (F : DecoupledConsensusModel.Block V) (η r : DecoupledConsensusModel.Round) (early late : DecoupledConsensusModel.Time) (u : V) (B : DecoupledConsensusModel.Block V)
    (cov : Option DecoupledConsensusModel.BlockId → DecoupledConsensusModel.Block V → Bool), (∀ k b, M.localCovers gv k b ⇢ cov k b) →
    ∀ (Re : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.readyView gv F η r early u ⇢ Re →
    ∀ (Rl : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.readyView gv F η r late u ⇢ Rl →
    ∀ (W : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.rawView gv η r late u ⇢ W →
    M.Supports (fun k b ↦ cov k b = Bool.true) Re Rl W B → ∀ p : Bool, M.positive gv F η r early late u B ⇢ p → p = Bool.true
  /-- An attestation in an outcome of a round-`r` grade's raw inputs of `sender` is held by the
      grade view for a round of `M.latest_window eta r`, is signed by `sender`, and was recorded
      before the cutoff. -/
  rawInputs_mem_window : ∀ (gv : M.GV) (eta r : DecoupledConsensusModel.Round) (cutoff : ℤ) (sender : V) {u : DecoupledConsensusModel.Protocol.SGVote V} (X : Finset (DecoupledConsensusModel.Protocol.SGVote V)), M.rawInputs gv eta r cutoff sender ⇢ X → u ∈ X → (∃ k ∈ M.latest_window eta r, u ∈ gv.sg_votes k) ∧ u.val_index = sender ∧ DecoupledConsensusModel.occurrenceBefore (gv.timestamp_sg_vote u) cutoff = Bool.true
  /-- The SG walk's output is compatible with `T` when the store's confirmed block, every grade-2
      candidate of the grade read, the grade read's anchor and the store's `M.get_fg_root` are. -/
  sgVote_compatible : ∀ {stH : M.HS} {grades : DecoupledConsensusModel.Protocol.GradeRead V} {T : DecoupledConsensusModel.Block V}, stH.toFG.toSG.toGoldfishStore.live_confirmed.compatible T = Bool.true → (∀ (Q : DecoupledConsensusModel.Block V), grades.Q2 = Option.some Q → Q.compatible T = Bool.true) → grades.anchor.compatible T = Bool.true → (M.get_fg_root stH.toFG).compatible T = Bool.true → (M.currentSGVote stH grades).compatible T = Bool.true
  /-- If the tokens support `B`, some early token `u` has the largest round among the early tokens
      and covers `B`, the raw tokens are clean from `u`'s round on, and every late token of a larger
      round covers `B`. -/
  supports_elim : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, M.Supports covers early late raw B → ∃ u ∈ early, (∀ x ∈ early, x.round ≤ u.round) ∧ covers u.key B ∧ M.CleanFrom raw u.round ∧ ∀ x ∈ late, u.round < x.round → covers x.key B
  /-- If the early token `u` has the largest round among the early tokens and covers `B`, the raw
      tokens are clean from `u`'s round on, and every late token of a larger round covers `B`, then
      the tokens support `B`. -/
  supports_intro : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk}, ∀ u ∈ early, (∀ x ∈ early, x.round ≤ u.round) → covers u.key B → M.CleanFrom raw u.round → (∀ x ∈ late, u.round < x.round → covers x.key B) → M.Supports covers early late raw B
  /-- If an outcome of the support test of the sender `u` for `B` is `true`, then `u`'s early ready,
      late ready and late raw tokens support `B`, for every choice of outcomes of the cover test and
      of those views. -/
  supports_of_positive : ∀ {gv : M.GV} {F : DecoupledConsensusModel.Block V} {η r : DecoupledConsensusModel.Round} {early late : DecoupledConsensusModel.Time} {u : V} {B : DecoupledConsensusModel.Block V} (p : Bool), M.positive gv F η r early late u B ⇢ p → p = Bool.true →
    ∀ (cov : Option DecoupledConsensusModel.BlockId → DecoupledConsensusModel.Block V → Bool), (∀ k b, M.localCovers gv k b ⇢ cov k b) →
    ∀ (Re : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.readyView gv F η r early u ⇢ Re →
    ∀ (Rl : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.readyView gv F η r late u ⇢ Rl →
    ∀ (W : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId))), M.rawView gv η r late u ⇢ W →
    M.Supports (fun k b ↦ cov k b = Bool.true) Re Rl W B
  /-- If the attestation `y` is in an outcome of `v`'s raw inputs and passes the body condition, the
      token of `y` is in every outcome of `v`'s ready view at that cutoff. -/
  token_mem_readyView : ∀ (gv : M.GV) (F : DecoupledConsensusModel.Block V) (η r : DecoupledConsensusModel.Round) (c : DecoupledConsensusModel.Time) (v : V) {y : DecoupledConsensusModel.Protocol.SGVote V} (X : Finset (DecoupledConsensusModel.Protocol.SGVote V)), M.rawInputs gv η r c v ⇢ X → y ∈ X → ∀ b : Bool, M.bodyReady gv F c y ⇢ b → b = Bool.true → ∀ Y : Finset (DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId)), M.readyView gv F η r c v ⇢ Y → M.token y ∈ Y
  /-- If the deepest clear ancestor of `C` from `floor` with the test `test` is `B`, then `B` is an
      ancestor of `C` or `C` itself. -/
  deepest_clear_preceq : ∀ {floor : Option (Block V)} {C B : Block V} {test : Block V → Bool} (h : M.deepest_clear floor C test = some B), Block.preceq B C = true
  /-- Round `r`'s grade-2 early cutoff is at or before its grade-0 early cutoff. -/
  early_g2_le_early_g0 : ∀ (E : Env V) (hc : Protocol.HealConfig) (r : Round), M.early E hc r .g2 ≤ M.early E hc r .g0
  /-- Round `r`'s grade-2 early cutoff is at or before its grade-1 early cutoff. -/
  early_g2_le_early_g1 : ∀ (E : Env V) (hc : Protocol.HealConfig) (r : Round), M.early E hc r .g2 ≤ M.early E hc r .g1
  /-- Round `r`'s early cutoff of phase `p` is at or before its late cutoff of `p`. -/
  early_le_late : ∀ (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase), M.early E hc r p ≤ M.late E hc r p
  /-- The raw inputs of `sender` grow with the cutoff: if `c ≤ d`, every outcome at `c` is contained
      in every outcome at `d`. -/
  rawInputs_mono : ∀ (gv : M.GV) (eta r : Round) {c d : Time} (hcd : c ≤ d) (sender : V)
    (X : Finset (Protocol.SGVote V)), M.rawInputs gv eta r c sender ⇢ X →
    ∀ Y : Finset (Protocol.SGVote V), M.rawInputs gv eta r d sender ⇢ Y → X ⊆ Y
  /-- `v`'s raw view grows with the cutoff: if `c ≤ d`, every outcome at `c` is contained in every
      outcome at `d`. -/
  rawView_mono : ∀ (gv : M.GV) (eta r : Round) {c d : Time} (hcd : c ≤ d) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), M.rawView gv eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), M.rawView gv eta r d v ⇢ Y → X ⊆ Y
  /-- `v`'s ready view grows with the cutoff: if `c ≤ d`, every outcome at `c` is contained in every
      outcome at `d`. -/
  readyView_mono : ∀ (gv : M.GV) (F : Block V) (eta r : Round) {c d : Time} (hcd : c ≤ d) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), M.readyView gv F eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), M.readyView gv F eta r d v ⇢ Y → X ⊆ Y
  /-- Every outcome of `v`'s ready view is contained in every outcome of `v`'s raw view for the same
      round, window length and cutoff. -/
  readyView_subset_rawView : ∀ (gv : M.GV) (F : Block V) (eta r : Round) (c : Time) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), M.readyView gv F eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), M.rawView gv eta r c v ⇢ Y → X ⊆ Y
  /-- The slot after round `r`'s opening slot belongs to round `r`. -/
  ActionRound_round_of_opening_succ : ∀ (hc : HealConfig) (r : Round), (M.round_of hc ((M.opening_slot hc r) + 1)) = r
  /-- If an outcome of the cover test of the optional root `H` for `B` in the tree `T` is `true`,
      then `H` is a root that resolves in `T` to a block `head` of `T`, and `B` is an ancestor of
      `head` or `head` itself. -/
  exists_head_of_head_covers : ∀ {T : Finset (Block V)} {B : Block V} {H : Option BlockId} (b : Bool) (hb : M.head_covers T B H ⇢ b) (h : b = true), ∃ (root : BlockId) (head : Block V), H = some root ∧
    Block.find? T root = some head ∧ head ∈ T ∧ Block.preceq B head = true
  /-- The slot after round `r`'s opening slot belongs to round `r`. -/
  HealingLemmas_round_of_opening_succ : ∀ (hc : HealConfig) (r : Round), (M.round_of hc ((M.opening_slot hc r) + 1)) = r
  /-- If `C` is a descendant of `floor` or `floor` itself (when `floor` is some block) and `C`
      passes `test`, the deepest clear ancestor of `C` from `floor` is `C`. -/
  deepest_clear_eq_tip : ∀ {floor : Option (Block V)} {C : Block V} {test : Block V → Bool} (hfloor : floor.elim True (fun a => Block.preceq a C = true)) (htest : test C = true), M.deepest_clear floor C test = some C
  /-- For a positive round `q` and `r = q − 1`, the slot `s` before `q`'s opening slot lies after
      `r`'s opening slot and before `r + 1`'s, and `s + 1` is `q`'s opening slot. -/
  lastInteriorSlot_before_opening : ∀ (hc : Protocol.HealConfig) {q : Round} (hq : 0 < q),
    let r := q - 1
    let s := M.opening_slot hc q - 1
    M.opening_slot hc r + 1 ≤ s ∧
      s < M.opening_slot hc (r + 1) ∧
      s + 1 = M.opening_slot hc q
  /-- Round `q + 1`'s opening slot is round `q`'s opening slot plus `R`. -/
  opening_slot_succ_eq : ∀ (hc : Protocol.HealConfig) (q : Round), (M.opening_slot hc (q + 1)) = (M.opening_slot hc q) + hc.R
  /-- If the validators outside `Hon` weigh strictly less than `Hon`, every member of `Hon` passes
      the support test for `C`, and every validator passing the opposition test for `C` is outside
      `Hon`, then every outcome of the grade test for `C` is `true`. -/
  phaseGrade_of_honestPositiveSupport : ∀ (E : Env V) (gv : M.GV) (F : Block V) (Hon : Finset V) (eta r : Round) (ea la : Time) (C : Block V)
    (pos : V → Bool) (hpos : ∀ v, M.positive gv F eta r ea la v C ⇢ pos v)
    (opp : V → Bool) (hopp : ∀ v, M.opposing gv F eta r ea la v C ⇢ opp v)
    (hmajority : E.electorate.weightOf (Finset.univ \ Hon) <
    E.electorate.weightOf Hon) (hpositive : ∀ v ∈ Hon,
    pos v = true) (hopposing : ∀ v,
    opp v = true →
    v ∉ Hon) (g : Bool) (hg : M.gradeBool E gv F eta r ea la C ⇢ g), g = true
  /-- Every slot from the slot after round `q`'s opening slot up to, and not including, round
      `q + 1`'s opening slot belongs to round `q`. -/
  round_of_eq_of_opening_succ_le_of_lt_next_opening : ∀ (hc : Protocol.HealConfig) {q k : Nat} (hlo : (M.opening_slot hc q) + 1 ≤ k) (hhi : k < (M.opening_slot hc (q + 1))), (M.round_of hc k) = q
  /-- Round `r`'s opening slot belongs to round `r`. -/
  round_of_opening_slot_eq : ∀ (hc : Protocol.HealConfig) (r : Round), (M.round_of hc ((M.opening_slot hc r))) = r
  /-- Round `q`'s opening slot belongs to round `q`. -/
  round_of_opening_slot_eq_schedule : ∀ (hc : Protocol.HealConfig) (q : Round), (M.round_of hc ((M.opening_slot hc q))) = q
  /-- Every outcome of `M.anchor` at the grade-1 result `g1` is the store's `M.get_fg_root`, or `g1`
      holds a root whose active prefix in the store's filtered tree is that outcome. -/
  anchor_cases : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (g1 : Option (Option (Block V)))
    (a : Block V), M.anchor E hc st r g1 ⇢ a → a = M.get_fg_root st.toFG ∨
    ∃ root A, g1 = some (some root) ∧
    M.activePrefix
    (M.get_filtered_block_tree st.toFG) root = some A ∧
    a = A
  /-- Two stores with the same filtered tree and the same `M.get_fg_root` have the same outcomes of
      `M.anchor` at the same grade-1 result. -/
  anchor_eq_of_filtered_fg_root : ∀ (E : Env V) (hc : Protocol.HealConfig) {st st' : M.HS} (r : Round) (g1 : Option (Option (Block V))) (htree : M.get_filtered_block_tree st.toFG =
    M.get_filtered_block_tree st'.toFG) (hroot : M.get_fg_root st.toFG = M.get_fg_root st'.toFG) (x : Block V), M.anchor E hc st r g1 ⇢ x ↔
    M.anchor E hc st' r g1 ⇢ x
  /-- If no block on the store's live confirmed chain descends from the grade read's anchor and
      passes its test, and the grade-2 candidate is `Q`, the SG walk returns `Q`. -/
  currentSGVote_of_Q2 : ∀ {st : M.HS} {grades : Protocol.GradeRead V} {Q : Block V} (h : M.deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = none) (hQ : grades.Q2 = some Q), M.currentSGVote st grades = Q
  /-- If the deepest block on the store's live confirmed chain that descends from the grade read's
      anchor and passes its test is `B`, the SG walk returns `B`. -/
  ModelProperties_currentSGVote_of_deepest_clear : ∀ {st : M.HS} {grades : Protocol.GradeRead V} {B : Block V} (h : M.deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = some B), M.currentSGVote st grades = B
  /-- If no block on the store's live confirmed chain descends from the grade read's anchor and
      passes its test, there is no grade-2 candidate and no raw grade-2 result, the SG walk returns
      the anchor. -/
  currentSGVote_of_not_rawG2 : ∀ {st : M.HS} {grades : Protocol.GradeRead V} (h : M.deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = none) (hQ : grades.Q2 = none) (hraw : ¬ grades.rawG2), M.currentSGVote st grades = grades.anchor
  /-- If no block on the store's live confirmed chain descends from the grade read's anchor and
      passes its test, there is no grade-2 candidate and there is a raw grade-2 result, the SG walk
      returns the store's `M.get_fg_root`. -/
  currentSGVote_of_rawG2 : ∀ {st : M.HS} {grades : Protocol.GradeRead V} (h : M.deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = none) (hQ : grades.Q2 = none) (hraw : grades.rawG2), M.currentSGVote st grades = M.get_fg_root st.toFG
  /-- If the deepest clear ancestor of `C` from `floor` is `B`, then `B` is an ancestor of `C` or
      `C` itself. -/
  deepest_clear_Preceq : ∀ {floor : Option (Block V)} {C B : Block V} {test : Block V → Bool} (h : M.deepest_clear floor C test = some B), Block.Preceq B C
  /-- If the deepest clear ancestor of `C` from the block `A` is `B`, then `A` is an ancestor of `B`
      or `B` itself. -/
  deepest_clear_floor_Preceq : ∀ {A C B : Block V} {test : Block V → Bool} (h : M.deepest_clear (some A) C test = some B), Block.Preceq A B
  /-- If the deepest clear ancestor of `C` from `floor` with the test `test` is `B`, then `B` passes
      `test`. -/
  deepest_clear_test : ∀ {floor : Option (Block V)} {C B : Block V} {test : Block V → Bool} (h : M.deepest_clear floor C test = some B), test B = true
  /-- If an outcome of the grade test of `Q` at the healing store `st` is `true`, some block of
      `st`'s tree is `Q` or a descendant of `Q`. -/
  ModelProperties_exists_mem_T_preceq_of_gradeBool : ∀ (E : Env V) (st : M.HS) (F : Block V) (eta r : Round) (early late : Time) {Q : Block V} (b : Bool) (hb : M.gradeBool E (M.gradeView st) F eta r early late Q ⇢ b) (h : b = true), ∃ H ∈ st.toFG.toSG.toGoldfishStore.T, Block.Preceq Q H
  /-- If an outcome of the grade-2 block of `frame` at `st` is `some Q`, the frame's grade-2 result
      is a completed root `clipped` and `Q` is an ancestor of `clipped` or `clipped` itself. -/
  grade2Block_some : ∀ {st : M.HS} {frame : M.Frame} {Q : Block V} (o : Option (Block V)) (ho : M.grade2Block st frame ⇢ o) (h : o = some Q), ∃ clipped : Block V, frame.g2 = some (some clipped) ∧ Block.Preceq Q clipped
  /-- Two frames with the same grade-0, grade-1 and grade-2 results have the same outcomes of the
      grade-2 block on every store. -/
  grade2Block_eq_of_phases : ∀ {st : M.HS} {frame frame' : M.Frame}, frame.g0 = frame'.g0 →
    frame.g1 = frame'.g1 → frame.g2 = frame'.g2 →
    ∀ o, M.grade2Block st frame ⇢ o ↔ M.grade2Block st frame' ⇢ o
  /-- The block tree of the grade view of `st` is the block tree of `st`. -/
  ModelProperties_gradeView_T : ∀ (st : M.HS), (M.gradeView st).T = st.toFG.toSG.toGoldfishStore.T
  /-- If an outcome of the grade-2 block of `frame` at `st` is `some Q`, then `Q` is in `st`'s
      filtered tree. -/
  mem_filtered_of_grade2Block : ∀ {st : M.HS} {frame : M.Frame} {Q : Block V} (o : Option (Block V)) (ho : M.grade2Block st frame ⇢ o) (h : o = some Q), Q ∈ M.get_filtered_block_tree st.toFG
  /-- The grade-2 phase result of a frame is its grade-2 result. -/
  ModelProperties_phaseResult_g2 : ∀ (f : M.Frame), M.phaseResult f .g2 = f.g2
  /-- The grade-2 result of the round-`r` frame read from the cache `c` at `st` is `c`'s round-`r`
      grade-2 result clipped to `st`'s finalized block. -/
  readFrame_g2 : ∀ (c : M.Cache) (st : M.HS) (r : Round), (M.readFrame c st r).g2 =
    M.clipResult st.toFG.F
    (M.cacheAtRound c r).g2
  /-- For every phase `p`, the result for `p` of the round-`r` frame read from the cache `c` at `st`
      is `c`'s round-`r` result for `p` clipped to `st`'s finalized block. -/
  readFrame_phase : ∀ (c : M.Cache) (st : M.HS) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase), M.phaseResult
    (M.readFrame c st r) p =
    M.clipResult st.toFG.F
    (M.phaseResult
    (M.cacheAtRound c r) p)
  /-- The grade-2 candidate of every outcome of the cache's frame contract read at `st` is in `st`'s
      tree. -/
  runtime_Q2_mem : ∀ (cache : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (B : Block V) (g : Protocol.GradeRead V) (hg : (M.frameContract cache).read E hc st r ⇢ g) (h : g.Q2 = some B), B ∈ st.toFG.toSG.toGoldfishStore.T
  /-- If `P` is in `tree` and is an ancestor of `root` or `root` itself, the active prefix of `root`
      in `tree` is some block `G`, and `P` is an ancestor of `G` or `G` itself. -/
  activePrefix_covers : ∀ {tree : Finset (Block V)} {root P : Block V} (hPT : P ∈ tree) (hPr : Block.Preceq P root), ∃ G, M.activePrefix tree root = some G ∧ Block.Preceq P G
  /-- Round `q`'s grade-2 early cutoff is at or before its grade-2 domain instant. -/
  early_le_domain : ∀ (S : Setup V) (q : Round), M.early S.E S.hc q .g2 ≤ M.domain S.E S.hc q .g2
  /-- If `q ≤ r`, round `q` opens at or before round `r`. -/
  NamedOutageClosure_opening_mono : ∀ (S : Setup V) {q r : Round} (h : q ≤ r), M.opening S.E S.hc q ≤ M.opening S.E S.hc r
  /-- The clip of `g` at `F` is an ancestor of `g` or `g` itself. -/
  q10_clip_preceq : ∀ (g F : Block V), Block.Preceq (M.clipGrade g F) g
  /-- Round `r`'s grade-2 domain instant is strictly before its grade-1 domain instant. -/
  q10_domain_g2_lt_domain_g1 : ∀ (S : Setup V) (r : Round), M.domain S.E S.hc r .g2 < M.domain S.E S.hc r .g1
  /-- Round `r`'s grade-1 early cutoff is at or before its grade-2 domain instant. -/
  q10_early_g1_le_domain_g2 : ∀ (S : Setup V) (r : Round), M.early S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g2
  /-- For a positive round `r`, round `r`'s grade-1 early cutoff is a whole number of delays
      `S.E.Δ`. -/
  q10_early_g1_public : ∀ (S : Setup V) (r : Round) (hr : 0 < r), PublicTime S (M.early S.E S.hc r .g1)
  /-- Round `r`'s grade-2 early cutoff is at or before its grade-1 early cutoff. -/
  q10_early_g2_le_early_g1 : ∀ (S : Setup V) (r : Round), M.early S.E S.hc r .g2 ≤ M.early S.E S.hc r .g1
  /-- Round `r`'s early cutoff of phase `p` is at or before its late cutoff of `p`. -/
  q10_early_le_late : ∀ (S : Setup V) (r : Round) (p : Phase), M.early S.E S.hc r p ≤ M.late S.E S.hc r p
  /-- If `e ≤ l`, `B` is in the grade view's tree and an outcome of the grade test for `B` is
      `true`, every outcome of the frozen root is some block that is `B` or a descendant of `B`. -/
  q10_freeze_of_graded : ∀ (E : Env V) (gv : M.GV) (F : Block V) (eta r : Round) {e l : Time} (hel : e ≤ l) {B : Block V} (hmem : B ∈ gv.T) (b : Bool) (hb : M.gradeBool E gv F eta r e l B ⇢ b) (hgrade : b = true) (fr : Option (Block V)) (hfr : M.freezeRoot E gv F eta r e l ⇢ fr), ∃ raw : Block V, fr = some raw ∧ Block.Preceq B raw
  /-- A passing grade test for `B` in the grade view `gva` transfers to `gvb` when the chosen ready
      and raw views are nested as the hypotheses state, the early ready tokens covering `B` in `gva`
      are among `gvb`'s, and every key covering `B` in `gva` covers it in `gvb`. -/
  q10_gradeBool_transport : ∀ (E : Env V) (gva gvb : M.GV) (Fa Fb : Block V) (eta r : Round) (ea la eb lb : Time) (B : Block V)
    (Rea : V → Finset (Protocol.Token (Option BlockId))) (hRea : ∀ w, M.readyView gva Fa eta r ea w ⇢ Rea w)
    (Rla : V → Finset (Protocol.Token (Option BlockId))) (hRla : ∀ w, M.readyView gva Fa eta r la w ⇢ Rla w)
    (Wa : V → Finset (Protocol.Token (Option BlockId))) (hWa : ∀ w, M.rawView gva eta r la w ⇢ Wa w)
    (Reb : V → Finset (Protocol.Token (Option BlockId))) (hReb : ∀ w, M.readyView gvb Fb eta r eb w ⇢ Reb w)
    (Rlb : V → Finset (Protocol.Token (Option BlockId))) (hRlb : ∀ w, M.readyView gvb Fb eta r lb w ⇢ Rlb w)
    (Wb : V → Finset (Protocol.Token (Option BlockId))) (hWb : ∀ w, M.rawView gvb eta r lb w ⇢ Wb w)
    (cva : Option BlockId → Bool) (hcva : ∀ k, M.localCovers gva k B ⇢ cva k)
    (cvb : Option BlockId → Bool) (hcvb : ∀ k, M.localCovers gvb k B ⇢ cvb k)
    (hea_la : ∀ w, Rea w ⊆ Rla w) (hla_ra : ∀ w, Rla w ⊆ Wa w) (heb_lb : ∀ w, Reb w ⊆ Rlb w) (hlb_rb : ∀ w, Rlb w ⊆ Wb w) (heb_la : ∀ w, Reb w ⊆ Rla w) (hlb_la : ∀ w, Rlb w ⊆ Rla w) (hrb_ra : ∀ w, Wb w ⊆ Wa w) (hkeep : ∀ w, ∀ u ∈ Rea w,
    cva u.key = true → u ∈ Reb w) (hcov : ∀ k, cva k = true → cvb k = true) (ga : Bool) (hga : M.gradeBool E gva Fa eta r ea la B ⇢ ga) (hgrade : ga = true) (gb : Bool) (hgb : M.gradeBool E gvb Fb eta r eb lb B ⇢ gb), gb = true
  /-- If `e ≤ l` and the grade test of one grade view passes for both `B` and `B'`, then `B` and
      `B'` are compatible. -/
  q10_graded_compatible : ∀ (E : Env V) (gv : M.GV) (F : Block V) (eta r : Round) {e l : Time} (hel : e ≤ l) {B B' : Block V} (b : Bool) (hb : M.gradeBool E gv F eta r e l B ⇢ b) (hB : b = true) (b' : Bool) (hb' : M.gradeBool E gv F eta r e l B' ⇢ b') (hB' : b' = true), Block.compatible B B' = true
  /-- The interpreted inputs of `sender` grow with the cutoff: if `c ≤ d`, every outcome at `c` is
      contained in every outcome at `d`. -/
  q10_interpreted_cut : ∀ (gv : M.GV) (F : Block V) (eta r : Round) {c d : Time} (hcd : c ≤ d) (sender : V)
    (X : Finset (Protocol.SGVote V)), M.interpretedInputs gv F eta r c sender ⇢ X →
    ∀ Y : Finset (Protocol.SGVote V), M.interpretedInputs gv F eta r d sender ⇢ Y → X ⊆ Y
  /-- Round `r`'s grade-1 late cutoff is at or before its grade-2 domain instant. -/
  q10_late_g1_le_domain_g2 : ∀ (S : Setup V) (r : Round), M.late S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g2
  /-- For a positive round `r`, round `r`'s grade-1 late cutoff is a whole number of delays `S.E.Δ`. -/
  q10_late_g1_public : ∀ (S : Setup V) (r : Round) (hr : 0 < r), PublicTime S (M.late S.E S.hc r .g1)
  /-- `v`'s raw view grows with the cutoff: if `c ≤ d`, every outcome at `c` is contained in every
      outcome at `d`. -/
  q10_rawView_cut : ∀ (gv : M.GV) (eta r : Round) {c d : Time} (hcd : c ≤ d) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), M.rawView gv eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), M.rawView gv eta r d v ⇢ Y → X ⊆ Y
  /-- `v`'s ready view grows with the cutoff: if `c ≤ d`, every outcome at `c` is contained in every
      outcome at `d`. -/
  q10_readyView_cut : ∀ (gv : M.GV) (F : Block V) (eta r : Round) {c d : Time} (hcd : c ≤ d) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), M.readyView gv F eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), M.readyView gv F eta r d v ⇢ Y → X ⊆ Y
  /-- Every outcome of `v`'s ready view is contained in every outcome of `v`'s raw view for the same
      round, window length and cutoff. -/
  q10_ready_subset_raw : ∀ (gv : M.GV) (F : Block V) (eta r : Round) (c : Time) (v : V)
    (X : Finset (Protocol.Token (Option BlockId))), M.readyView gv F eta r c v ⇢ X →
    ∀ Y : Finset (Protocol.Token (Option BlockId)), M.rawView gv eta r c v ⇢ Y → X ⊆ Y
  /-- If `B` is compatible with `F`, then `B` is an ancestor of the clip of `g` at `F` (or that
      block itself) exactly when `B` is an ancestor of `g` or `g` itself. -/
  q10_retained_prefix : ∀ (g F B : Block V) (hBF : Block.compatible B F = true), Block.Preceq B (M.clipGrade g F) ↔ Block.Preceq B g
  /-- Round `r`'s grade-2 domain instant is at or before its grade-1 domain instant. -/
  domain_g2_le_domain_g1 : ∀ (S : Setup V) (r : Round), M.domain S.E S.hc r .g2 ≤ M.domain S.E S.hc r .g1
  /-- Round `r`'s grade-1 early cutoff is at or before its grade-1 domain instant. -/
  early_g1_le_domain_g1 : ∀ (S : Setup V) (r : Round), M.early S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g1
  /-- Round `r`'s grade-1 early cutoff is at or before its grade-1 late cutoff. -/
  early_g1_le_late_g1 : ∀ (S : Setup V) (r : Round), M.early S.E S.hc r .g1 ≤ M.late S.E S.hc r .g1
  /-- Round `r`'s grade-2 early cutoff is at or before its grade-2 late cutoff. -/
  early_g2_le_late_g2 : ∀ (S : Setup V) (r : Round), M.early S.E S.hc r .g2 ≤ M.late S.E S.hc r .g2
  /-- For a positive round `s`, round `s`'s grade-2 early cutoff is a whole number of delays
      `S.E.Δ`. -/
  early_g2_public : ∀ (S : Setup V) (s : Round) (hs : 0 < s), PublicTime S (M.early S.E S.hc s .g2)
  /-- If the active prefix of `root` in `tree` is `B`, then `B` is in `tree`. -/
  activePrefix_mem : ∀ (tree : Finset (Block V)) (root B : Block V) (h : M.activePrefix tree root = some B), B ∈ tree
  /-- For `0 < r` and `lo ≤ opening (r - η_SG)`, every domain instant of round `r` is at or after
      `lo`. -/
  lo_le_domain_of_window_start : ∀ (S : Setup V) {r : Round} (hr : 0 < r) {lo : Time} (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) (p : Phase), lo ≤ M.domain S.E S.hc r p
  /-- For `0 < r` and `lo ≤ opening (r - η_SG)`, round `r`'s grade-2 early cutoff is at or after
      `lo`. -/
  lo_le_early_g2_of_window_start : ∀ (S : Setup V) {r : Round} (hr : 0 < r) {lo : Time} (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)), lo ≤ M.early S.E S.hc r .g2
  /-- If `q < r`, then `opening q + 8 * Δ ≤ opening r`. -/
  opening_add_le_of_lt : ∀ (S : Setup V) {q r : Round} (h : q < r), M.opening S.E S.hc q + 8 * S.E.Δ ≤ M.opening S.E S.hc r
  /-- A grade-2 candidate `Q` that an outcome of the frame's grade-2 block offers is compatible with
      `T` when the frame's grade-2 root is. -/
  Q2_compatible : ∀ {stH : M.HS} {T : Block V} {frame : M.Frame} (hg2 : ∀ root : Block V, frame.g2 = some (some root) → Block.compatible root T = true) {Q : Block V} (o : Option (Block V)) (ho : M.grade2Block stH frame ⇢ o) (hQ : o = some Q), Block.compatible Q T = true
  /-- The active prefix of a root is an ancestor of that root or the root itself. -/
  activePrefix_preceq : ∀ {tree : Finset (Block V)} {root B : Block V} (h : M.activePrefix tree root = some B), Block.preceq B root = true
  /-- If the grade-1 result is the completed root `root` and the active prefix of `root` in the
      store's filtered tree is `A`, every outcome of `M.anchor` is `A`. -/
  anchor_of_activePrefix : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {root A : Block V} (h : M.activePrefix (M.get_filtered_block_tree st.toFG) root = some A) (a : Block V), M.anchor E hc st r (some (some root)) ⇢ a → a = A
  /-- Clipping a cache to `F` leaves its round unchanged. -/
  clipCache_round : ∀ (F : Block V) (c : M.Cache), (M.clipCache F c).round = c.round
  /-- Clipping at `F` a completed phase result whose root is already clipped at `F` changes nothing. -/
  clipResult_some_map_clipGrade : ∀ (F : Block V) (o : Option (Block V)), M.clipResult F (some (o.map (fun B => M.clipGrade B F)))
    = some (o.map (fun B => M.clipGrade B F))
  /-- Two blocks that pass the grade test of one grade view at one phase of one round are
      compatible. -/
  compatible_of_gradeBool_phase : ∀ (E : Env V) (hc : Protocol.HealConfig) (gv : M.GV) (F : Block V) (r : Round) (p : Protocol.Phase) {B B' : Block V} (b : Bool) (hb : M.gradeBool E gv F hc.η_SG r (M.early E hc r p)
    (M.late E hc r p) B ⇢ b) (hB : b = true) (b' : Bool) (hb' : M.gradeBool E gv F hc.η_SG r (M.early E hc r p)
    (M.late E hc r p) B' ⇢ b') (hB' : b' = true), Block.compatible B B' = true
  /-- If an outcome of the opposition test of `u` for `B` is `true`, then, for every choice of
      outcomes of `u`'s views and of the cover test, either some late ready token of a round at
      least every early token's does not cover `B`, or two raw tokens of one such round carry
      different keys. -/
  conditions_of_opposing : ∀ (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (o : Bool) (ho : M.opposing gv F η r early late u B ⇢ o) (h : o = true)
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : M.readyView gv F η r early u ⇢ Re)
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : M.readyView gv F η r late u ⇢ Rl)
    (W : Finset (Protocol.Token (Option BlockId))) (hW : M.rawView gv η r late u ⇢ W)
    (cov : Option BlockId → Bool) (hcov : ∀ k, M.head_covers gv.T B k ⇢ cov k), (∃ x ∈ Rl,
    (∀ y ∈ Re, y.round ≤ x.round) ∧
    ¬ cov x.key = true) ∨
    ∃ x ∈ W, ∃ y ∈ W,
    (∀ z ∈ Re, z.round ≤ x.round) ∧
    x.round = y.round ∧ x.key ≠ y.key
  /-- If an outcome of the support test of `u` for `B` is `true`, then, for every choice of outcomes
      of `u`'s views and of the cover test, some early ready token of the largest round covers `B`,
      no two raw tokens of one round at least its own carry different keys, and every late ready
      token of a larger round covers `B`. -/
  conditions_of_positive : ∀ (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (p : Bool) (hp : M.positive gv F η r early late u B ⇢ p) (h : p = true)
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : M.readyView gv F η r early u ⇢ Re)
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : M.readyView gv F η r late u ⇢ Rl)
    (W : Finset (Protocol.Token (Option BlockId))) (hW : M.rawView gv η r late u ⇢ W)
    (cov : Option BlockId → Bool) (hcov : ∀ k, M.head_covers gv.T B k ⇢ cov k), ∃ u₀ ∈ Re,
    (∀ x ∈ Re, x.round ≤ u₀.round) ∧
    cov u₀.key = true ∧
    (∀ x ∈ W, ∀ y ∈ W,
    u₀.round ≤ x.round → x.round = y.round → x.key = y.key) ∧
    (∀ x ∈ Rl, u₀.round < x.round →
    cov x.key = true)
  /-- If the deepest clear ancestor of the store's `live_confirmed` from the grade read's anchor is
      `D`, the SG walk returns `D`. -/
  Sts_currentSGVote_of_deepest_clear : ∀ {st : M.HS} {grades : Protocol.GradeRead V} {D : Block V} (h : M.deepest_clear (some grades.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed grades.clear = some D), M.currentSGVote st grades = D
  /-- A round's grade-2 domain instant is at or before its domain instant for every phase. -/
  domain_g2_le_domain_l67 : ∀ (S : Setup V) (q : Round) (p : Phase), M.domain S.E S.hc q .g2 ≤
    M.domain S.E S.hc q p
  /-- A round's domain instant for every phase is at or before its G0 domain instant. -/
  domain_le_domain_g0 : ∀ (S : Setup V) (r : Round) (p : Phase), M.domain S.E S.hc r p ≤ M.domain S.E S.hc r .g0
  /-- For every round `r` and phase `p`, the early cutoff plus two delays is at or before the domain
      instant. -/
  early_add_two_delta_le_domain : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase), M.early S.E S.hc r p + 2 * S.E.Δ ≤ M.domain S.E S.hc r p
  /-- A round's G2 early cutoff is strictly before its domain instant for every phase. -/
  early_g2_lt_domain : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase), M.early S.E S.hc r .g2 < M.domain S.E S.hc r p
  /-- If an outcome of the cover test of `root` for `X` in the tree `T` is `true`, `root` resolves
      in `T` to a block `H` that is `X` or a descendant of `X`. -/
  exists_find_of_head_covers : ∀ {T : Finset (Block V)} {X : Block V} {root : BlockId} (b : Bool) (hb : M.head_covers T X (some root) ⇢ b) (h : b = true), ∃ H : Block V, Block.find? T root = some H ∧ Block.Preceq X H
  /-- If an outcome of the cover test of the key `some root` for `B` in the grade view `gv` is
      `true`, `root` resolves in `gv`'s tree to a block `H` that is `B` or a descendant of `B`. -/
  exists_find_of_localCovers : ∀ {gv : M.GV} {root : BlockId} {B : Block V} (b : Bool) (hb : M.localCovers gv (some root) B ⇢ b) (hcov : b = true), ∃ H : Block V, Block.find? gv.T root = some H ∧ Block.Preceq B H
  /-- If an outcome of the grade test for `B` is `true`, the grade view's tree holds `B` or a
      descendant of `B`. -/
  Sts_exists_mem_T_preceq_of_gradeBool : ∀ (E : Env V) (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (B : Block V) (b : Bool) (hb : M.gradeBool E gv F η r early late B ⇢ b) (h : b = true), ∃ H ∈ gv.T, Block.Preceq B H
  /-- For every slot `s` at or after round `r`'s opening slot plus 2, there is a `k` with `s`
      between round `(r + k)`'s opening slot plus 2 and round `(r + k + 1)`'s opening slot plus 1. -/
  exists_round_of_slot : ∀ (hc : Protocol.HealConfig) (r : Round) {s : Nat} (hs : (M.opening_slot hc r) + 2 ≤ s), ∃ k : Nat, (M.opening_slot hc (r + k)) + 2 ≤ s ∧ s ≤ (M.opening_slot hc (r + k + 1)) + 1
  /-- Every SG vote in an outcome of `sender`'s raw inputs is one the grade view holds for some
      round of `M.latest_window eta r`. -/
  exists_window_of_mem_rawInputs : ∀ {gv : M.GV} {eta r : Round} {cutoff : Time} {sender : V} {u : Protocol.SGVote V} (X : Finset (Protocol.SGVote V)) (hX : M.rawInputs gv eta r cutoff sender ⇢ X) (hu : u ∈ X), ∃ k, k ∈ M.latest_window eta r ∧ u ∈ gv.sg_votes k
  /-- If an outcome of the frame's grade-2 block at `st` is `some q`, then the store's
      `M.get_fg_root` is an ancestor of `q` or `q` itself. -/
  fgRoot_preceq_grade2Block : ∀ {st : M.HS} {frame : M.Frame} {q : Block V} (o : Option (Block V)) (ho : M.grade2Block st frame ⇢ o) (h : o = some q), Block.Preceq (M.get_fg_root st.toFG) q
  /-- The root that a token of an outcome of `v`'s ready view names resolves in the grade view's
      tree. -/
  find_of_mem_readyView : ∀ (gv : M.GV) (F : Block V) (η r : Round) (c : Time) (v : V) {tok : Protocol.Token (Option BlockId)} {root : BlockId} (X : Finset (Protocol.Token (Option BlockId))) (hX : M.readyView gv F η r c v ⇢ X) (htok : tok ∈ X) (hkey : tok.key = some root), ∃ H : Block V, Block.find? gv.T root = some H
  /-- The slot after round `r`'s opening slot is before round `r + 1`'s opening slot. -/
  firstInterior_lt_nextOpening_l86e : ∀ (S : Setup V) (r : Round), (M.opening_slot S.hc r) + 1 < (M.opening_slot S.hc (r + 1))
  /-- If an outcome of the select candidate of the cache `c` at `st` is `some G`, every outcome of
      the stable root of `c` at `st` for the round of `st`'s slot is `some G`. -/
  frameSGCandidate_stableRoot : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (slot : Slot) {G : Block V} (o : Option (Block V)) (ho : M.frameSGCandidate c E hc (M.toHealing st) slot ⇢ o) (h : o = some G) (x : Option (Block V)), M.frameStableRoot c E hc (M.toHealing st) ((M.round_of hc st.s)) ⇢ x → x = some G
  /-- If an outcome of the stable root of the cache `c` at `st` for round `r` is `some G`, then `G`
      is the store's `M.get_fg_root`, or the round-`r` frame read from `c` at `st` holds a grade-2
      root `root` and `G` is an ancestor of `root`. -/
  frameStableRoot_cases : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {G : Block V} (x : Option (Block V)) (hx : M.frameStableRoot c E hc st r ⇢ x) (h : x = some G), G = M.get_fg_root st.toFG ∨
    ∃ root : Block V, (M.readFrame c st r).g2 = some (some root) ∧
    Block.Preceq G root
  /-- Every outcome of the stable root of a frame is some block. -/
  frameStableRoot_exists : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (x : Option (Block V)), M.frameStableRoot c E hc st r ⇢ x → ∃ G : Block V, x = some G
  /-- If `st` and `st'` have the same finalized block and the same filtered tree, and an outcome of
      the grade-2 block of the frame read at `st'` is `some Q`, every outcome of the stable root at
      `st` is `some Q`. -/
  frameStableRoot_of_grade2Block : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st st' : M.HS) (r : Round) (hF : st'.toFG.F = st.toFG.F) (htree : M.get_filtered_block_tree st'.toFG = M.get_filtered_block_tree st.toFG) {Q : Block V} (o : Option (Block V)) (ho : M.grade2Block st' (M.readFrame c st' r) ⇢ o) (h : o = some Q) (x : Option (Block V)), M.frameStableRoot c E hc st r ⇢ x → x = some Q
  /-- The head computed at the healing store `st` is the Goldfish fork choice over `st`'s filtered
      tree, started from the SG root the contract reads for the round of `st`'s slot, in every
      outcome. -/
  get_head_with_eq_fork_choice : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (votes support : Finset (GoldfishVote V)) (s : Slot)
    (R : Block V), M.get_sg_root_with contract E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ R →
    ∀ X : Block V, M.get_head_with contract E hc st votes support s ⇢ X ↔
    M.goldfish_fork_choice E st.toFG.σ st.toFG.h_max st.toFG.toSG.toGoldfishStore.T st.toFG.toSG.toGoldfishStore.s
    R
    (M.get_filtered_block_tree st.toFG) votes support s ⇢ X
  /-- Two healing stores with the same filtered tree give the same outcomes of the grade-2 block of
      any frame. -/
  grade2Block_eq_of_filtered_eq : ∀ {st st' : M.HS} (frame : M.Frame) (h : M.get_filtered_block_tree st.toFG = M.get_filtered_block_tree st'.toFG) (x : Option (Block V)), M.grade2Block st frame ⇢ x ↔ M.grade2Block st' frame ⇢ x
  /-- If an outcome of the grade-2 block of `frame` is `some Q`, the frame's grade-2 entry is a
      block `root` and `Q` is an ancestor of `root` or `root` itself. -/
  grade2Block_preceq_root : ∀ {stH : M.HS} {frame : M.Frame} {Q : Block V} (o : Option (Block V)) (ho : M.grade2Block stH frame ⇢ o) (hQ : o = some Q), ∃ root : Block V, frame.g2 = some (some root) ∧ Block.Preceq Q root
  /-- If the validators passing the support test for `B` weigh at most as much as those passing the
      opposition test, every outcome of the grade test for `B` is `false`. -/
  gradeBool_eq_false_of_weight_le : ∀ (E : Env V) (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (B : Block V)
    (pos : V → Bool) (hpos : ∀ u, M.positive gv F η r early late u B ⇢ pos u)
    (opp : V → Bool) (hopp : ∀ u, M.opposing gv F η r early late u B ⇢ opp u) (h : E.electorate.weightOf
    (Finset.univ.filter fun u => pos u = true)
    ≤ E.electorate.weightOf
    (Finset.univ.filter fun u => opp u = true)) (g : Bool) (hg : M.gradeBool E gv F η r early late B ⇢ g), g = false
  /-- If an outcome of the frozen root of the grade view is `some D`, every outcome of the grade
      test for `D` with the same arguments is `true`. -/
  gradeBool_of_freezeRoot_eq_some : ∀ {E : Env V} {gv : M.GV} {F : Block V} {η r : Round} {early late : Time} {D : Block V} (fr : Option (Block V)) (hfr : M.freezeRoot E gv F η r early late ⇢ fr) (h : fr = some D) (g : Bool), M.gradeBool E gv F η r early late D ⇢ g → g = true
  /-- If the grade test passes for `B` in `gv`, every validator opposing `B'` in `gv'` opposes `B`
      in `gv`, and every validator supporting `B` in `gv` supports `B'` in `gv'`, then the grade
      test passes for `B'` in `gv'`. -/
  gradeBool_of_subsets : ∀ (E : Env V) {gv gv' : M.GV} {F F' : Block V} {η r : Round} {early late early' late' : Time} {B B' : Block V}
    (opp' : V → Bool) (hopp' : ∀ u, M.opposing gv' F' η r early' late' u B' ⇢ opp' u)
    (opp : V → Bool) (hopp'' : ∀ u, M.opposing gv F η r early late u B ⇢ opp u)
    (pos : V → Bool) (hpos' : ∀ u, M.positive gv F η r early late u B ⇢ pos u)
    (pos' : V → Bool) (hpos'' : ∀ u, M.positive gv' F' η r early' late' u B' ⇢ pos' u)
    (hopp : (Finset.univ.filter fun u => opp' u = true) ⊆
    Finset.univ.filter fun u => opp u = true) (hpos : (Finset.univ.filter fun u => pos u = true) ⊆
    Finset.univ.filter fun u => pos' u = true) (g : Bool) (hg : M.gradeBool E gv F η r early late B ⇢ g) (h : g = true) (g' : Bool), M.gradeBool E gv' F' η r early' late' B' ⇢ g' → g' = true
  /-- If `early ≤ late`, every member of `H` passes the support test for `B`, and the validators
      outside `H` with a non-empty raw view at `late` weigh strictly less than `H`, every outcome of
      the grade test for `B` is `true`. -/
  gradeBool_of_supporters : ∀ (E : Env V) (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (B : Block V) (H : Finset V)
    (pos : V → Bool) (hpos' : ∀ u, M.positive gv F η r early late u B ⇢ pos u)
    (W : V → Finset (Protocol.Token (Option BlockId))) (hW : ∀ u, M.rawView gv η r late u ⇢ W u)
    (hel : early ≤ late) (hpos : ∀ u ∈ H, pos u = true) (hw : E.electorate.weightOf
    ((Finset.univ.filter fun u => (W u).Nonempty) \ H)
    < E.electorate.weightOf H) (g : Bool), M.gradeBool E gv F η r early late B ⇢ g → g = true
  /-- If the validators passing the opposition test for `B` weigh strictly less than those passing
      the support test, every outcome of the grade test for `B` is `true`. -/
  gradeBool_of_weight_lt : ∀ (E : Env V) (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (B : Block V)
    (opp : V → Bool) (hopp : ∀ u, M.opposing gv F η r early late u B ⇢ opp u)
    (pos : V → Bool) (hpos : ∀ u, M.positive gv F η r early late u B ⇢ pos u) (h : E.electorate.weightOf
    (Finset.univ.filter fun u => opp u = true)
    < E.electorate.weightOf
    (Finset.univ.filter fun u => pos u = true)) (g : Bool) (hg : M.gradeBool E gv F η r early late B ⇢ g), g = true
  /-- Every outcome of the grade test of round `0` is `false` for every block. -/
  gradeBool_round_zero : ∀ (E : Env V) (gv : M.GV) (F : Block V) (η : Round) (early late : Time) (B : Block V) (g : Bool), M.gradeBool E gv F η 0 early late B ⇢ g → g = false
  /-- The tree of the grade view read from a store's healing view is that store's tree. -/
  Sts_gradeView_T : ∀ (st : M.S), (M.gradeView (M.toHealing st)).T = st.T
  /-- The SG votes of round `r` in the grade view read from a store's healing view are the SG votes
      of that store's attestations of round `r`. -/
  gradeView_sg_votes : ∀ (st : M.S) (r : Round), (M.gradeView (M.toHealing st)).sg_votes r = ((M.store_sg_pool st r)).image M.sgVote
  /-- The block timestamp map of the grade view read from a store's healing view is that store's
      block timestamp map. -/
  gradeView_timestamp_block : ∀ (st : M.S), (M.gradeView (M.toHealing st)).timestamp_block = st.timestamp_block
  /-- The SG vote timestamp map of the grade view read from a store's healing view is that store's
      SG vote timestamp map. -/
  gradeView_timestamp_sg_vote : ∀ (st : M.S), (M.gradeView (M.toHealing st)).timestamp_sg_vote = st.timestamp_sg_vote
  /-- The filtered tree of the grade view of the healing store `hs` is the filtered block tree of
      `hs`. -/
  gradeView_tree : ∀ (hs : M.HS), (M.gradeView hs).tree = M.get_filtered_block_tree hs.toFG
  /-- If `root` resolves in the tree `T` to a block `H` that is `X` or a descendant of `X`, every
      outcome of the cover test of `root` for `X` in `T` is `true`. -/
  head_covers_of_find : ∀ {T : Finset (Block V)} {X H : Block V} {root : BlockId} (hfind : Block.find? T root = some H) (hXH : Block.Preceq X H) (b : Bool), M.head_covers T X (some root) ⇢ b → b = true
  /-- A round's late cutoff of phase `p` is at or before its domain instant for `p`. -/
  late_le_domain : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase), M.late S.E S.hc r p ≤ M.domain S.E S.hc r p
  /-- `sEnd ≤ opening_slot (round_of (sEnd − 2) + 1) + 1`. -/
  le_opening_round_of_sub_two : ∀ (hc : Protocol.HealConfig) (sEnd : Nat), sEnd ≤ (M.opening_slot hc ((M.round_of hc (sEnd - 2)) + 1)) + 1
  /-- Every slot `s` is at or before round `(r + 1 + s + 1)`'s opening slot. -/
  le_opening_slot_far : ∀ (hc : Protocol.HealConfig) (r s : Nat), s ≤ (M.opening_slot hc (r + 1 + s + 1))
  /-- If `opening_slot ρ + 2 ≤ sEnd`, then `ρ ≤ round_of (sEnd − 2)`. -/
  le_round_of_sub_two : ∀ (hc : Protocol.HealConfig) {ρ : Nat} {sEnd : Nat} (h : (M.opening_slot hc ρ) + 2 ≤ sEnd), ρ ≤ (M.round_of hc (sEnd - 2))
  /-- If `lo ≤ opening (r − η_SG)` and `opening r − 5Δ ≤ c`, and some SG vote is in an outcome of
      the raw inputs of round `r`, then `lo ≤ c`. -/
  lo_le_of_rawInputs_l53 : ∀ (S : Setup V) {lo : Int} {r : Round} {c : Time} (hlow : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) (hc : M.opening S.E S.hc r - 5 * S.E.Δ ≤ c) {gv : M.GV} {c' : Time} {sender : V} {u : Protocol.SGVote V} (X : Finset (Protocol.SGVote V)) (hX : M.rawInputs gv S.hc.η_SG r c' sender ⇢ X) (hraw : u ∈ X), lo ≤ c
  /-- The grade view's cover test of a key for `B` passes exactly when the head cover test of that
      key for `B` over the view's tree does, in every outcome. -/
  localCovers_eq_true_iff : ∀ (gv : M.GV) (k : Option BlockId) (B : Block V) (b : Bool), M.localCovers gv k B ⇢ b → ∀ b' : Bool, M.head_covers gv.T B k ⇢ b' → (b = true ↔ b' = true)
  /-- Every outcome of the cover test of the empty key for a block is `false`. -/
  localCovers_none : ∀ (gv : M.GV) (B : Block V) (b : Bool), M.localCovers gv none B ⇢ b → b = false
  /-- If `root` resolves in the grade view's tree to a block `H` that is `B` or a descendant of `B`,
      every outcome of the cover test of `some root` for `B` is `true`. -/
  localCovers_of_find : ∀ {gv : M.GV} {root : BlockId} {B H : Block V} (hfind : Block.find? gv.T root = some H) (hBH : Block.Preceq B H) (b : Bool), M.localCovers gv (some root) B ⇢ b → b = true
  /-- If `key` resolves in the grade view's tree to `H`, an outcome of the cover test of `some key`
      for `B` is `true` exactly when `B` is an ancestor of `H` or `H` itself. -/
  localCovers_some_iff_of_find : ∀ {gv : M.GV} {key : BlockId} {B H : Block V} (hfind : Block.find? gv.T key = some H) (b : Bool) (hb : M.localCovers gv (some key) B ⇢ b), b = true ↔ Block.Preceq B H
  /-- A slot is before the opening slot of the round after its own round. -/
  lt_opening_slot_round_of_succ : ∀ (hc : Protocol.HealConfig) (s : Slot), s < (M.opening_slot hc ((M.round_of hc s) + 1))
  /-- If an outcome of the frozen root of the grade view `gv` is `some D`, then `D` is in `gv`'s
      tree. -/
  mem_T_of_freezeRoot_eq_some : ∀ {E : Env V} {gv : M.GV} {F : Block V} {η r : Round} {early late : Time} {D : Block V} (fr : Option (Block V)) (hfr : M.freezeRoot E gv F η r early late ⇢ fr) (h : fr = some D), D ∈ gv.T
  /-- An SG vote the grade view holds for a round of `M.latest_window eta r`, signed by `sender`,
      whose stamp occurs before `cutoff`, is in every outcome of `sender`'s raw inputs at that
      cutoff. -/
  mem_rawInputs_of_occurrenceBefore : ∀ (gv : M.GV) (eta r k : Round) (cutoff : Time) (sender : V) {u : Protocol.SGVote V} (hk : k ∈ M.latest_window eta r) (hu : u ∈ gv.sg_votes k) (hidx : u.val_index = sender) (hocc : occurrenceBefore (gv.timestamp_sg_vote u) cutoff = true) (X : Finset (Protocol.SGVote V)), M.rawInputs gv eta r cutoff sender ⇢ X → u ∈ X
  /-- An SG vote the grade view holds for a round of `M.latest_window eta r`, signed by `sender` and
      stamped strictly before `cutoff`, is in every outcome of `sender`'s raw inputs at that cutoff. -/
  mem_rawInputs_of_stamp : ∀ (gv : M.GV) (eta r k : Round) (cutoff : Time) (sender : V) {u : Protocol.SGVote V} (hk : k ∈ M.latest_window eta r) (hu : u ∈ gv.sg_votes k) (hidx : u.val_index = sender) {stamp : Time} (hts : gv.timestamp_sg_vote u = some (stamp : Stamp)) (hlt : stamp < cutoff) (X : Finset (Protocol.SGVote V)), M.rawInputs gv eta r cutoff sender ⇢ X → u ∈ X
  /-- A token is in an outcome of `v`'s raw view exactly when it is the token of an attestation in
      an outcome of `v`'s raw inputs at the same cutoff. -/
  mem_rawView_iff : ∀ (gv : M.GV) (η r : Round) (c : Time) (v : V) (tok : Protocol.Token (Option BlockId))
    (X : Finset (Protocol.Token (Option BlockId))) (hX : M.rawView gv η r c v ⇢ X)
    (Y : Finset (Protocol.SGVote V)) (hY : M.rawInputs gv η r c v ⇢ Y), tok ∈ X ↔
    ∃ y ∈ Y, M.token y = tok
  /-- A token is in an outcome of `v`'s ready view exactly when it is the token of an attestation in
      an outcome of `v`'s interpreted inputs at the same cutoff. -/
  mem_readyView_iff : ∀ {gv : M.GV} {F : Block V} {η r : Round} {c : Time} {v : V} {tok : Protocol.Token (Option BlockId)}
    (X : Finset (Protocol.Token (Option BlockId))) (hX : M.readyView gv F η r c v ⇢ X)
    (Y : Finset (Protocol.SGVote V)) (hY : M.interpretedInputs gv F η r c v ⇢ Y), tok ∈ X ↔
    ∃ y ∈ Y, M.token y = tok
  /-- Every SG vote in an outcome of `sender`'s raw inputs is one the grade view holds for some
      round of `M.latest_window eta r`. -/
  mem_sg_votes_of_mem_rawInputs : ∀ {gv : M.GV} {eta r : Round} {cutoff : Time} {sender : V} {u : Protocol.SGVote V} (X : Finset (Protocol.SGVote V)) (hX : M.rawInputs gv eta r cutoff sender ⇢ X) (hu : u ∈ X), ∃ k ∈ M.latest_window eta r, u ∈ gv.sg_votes k
  /-- Every outcome of the cache a phase tick at `t` leaves has the round of `t`'s slot as its
      round. -/
  onPhaseTick_round : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (t : Int) (c : M.Cache) (c' : M.Cache), M.onPhaseTick E hc st t c ⇢ c' → c'.round = (M.round_of hc (E.slotOf t))
  /-- The opening slot of a positive round is positive. -/
  openingSlot_pos_l58 : ∀ (S : Setup V) {q : Round} (hq : 0 < q), 0 < (M.opening_slot S.hc q)
  /-- The slot before the opening slot of a positive round is positive. -/
  openingSlot_pred_pos_l58 : ∀ (S : Setup V) {q : Round} (hq : 0 < q), 0 < (M.opening_slot S.hc q) - 1
  /-- If `D + 2 ≤ m`, slot and round bounds on round `m`'s opening slot `start` and the slot
      `d = start − 1` hold, among them `opening_slot D + 2 ≤ d`, `opening_slot (m − 1) + 1 ≤ d`,
      `0 < d`, `d + 1 = start` and `D ≤ m − 2`. -/
  openingSlots_l86f : ∀ (S : Setup V) {D m : Round} (hm : D + 2 ≤ m), (M.opening_slot S.hc D) + 1 ≤ (M.opening_slot S.hc m) - 1 ∧
    (M.opening_slot S.hc D) + 2 ≤ (M.opening_slot S.hc m) ∧
    (M.opening_slot S.hc (m - 1)) + 1 ≤ (M.opening_slot S.hc m) - 1 ∧
    0 < (M.opening_slot S.hc m) - 1 ∧
    (M.opening_slot S.hc m) - 1 + 1 = (M.opening_slot S.hc m) ∧
    m - 2 + 1 = m - 1 ∧ m - 1 + 1 = m ∧ D ≤ m - 2 ∧
    (M.opening_slot S.hc D) + 2 ≤ (M.opening_slot S.hc m) - 1
  /-- Two environments with the same delay `Δ` give every round the same opening instant. -/
  opening_eq_of_delta_eq : ∀ {E E' : Env V} (h : E.Δ = E'.Δ) (hc : Protocol.HealConfig) (r : Round), M.opening E hc r = M.opening E' hc r
  /-- For `r ≤ r'`, round `r` opens at or before round `r'`. -/
  Sts_opening_mono : ∀ (S : Setup V) {r r' : Round} (h : r ≤ r'), M.opening S.E S.hc r ≤ M.opening S.E S.hc r'
  /-- The opening slot of round `r + k` is the opening slot of round `r` plus `k * R`. -/
  opening_slot_add : ∀ (hc : Protocol.HealConfig) (r k : Round), (M.opening_slot hc (r + k)) = (M.opening_slot hc r) + k * hc.R
  /-- For `r ≤ r'`, round `r`'s opening slot is at or before round `r'`'s. -/
  opening_slot_le_of_le : ∀ (hc : Protocol.HealConfig) {r r' : Round} (h : r ≤ r'), (M.opening_slot hc r) ≤ (M.opening_slot hc r')
  /-- If round `r` is at or before the round of slot `s`, then the opening slot of `r` is at or
      before `s`. -/
  opening_slot_le_of_le_round_of : ∀ (hc : Protocol.HealConfig) {r : Round} {s : Slot} (h : r ≤ (M.round_of hc s)), (M.opening_slot hc r) ≤ s
  /-- For `r ≤ r'`, round `r`'s opening slot is at or before round `r'`'s. -/
  opening_slot_mono : ∀ (S : Setup V) {r r' : Round} (h : r ≤ r'), (M.opening_slot S.hc r) ≤ (M.opening_slot S.hc r')
  /-- A positive round opens at a positive slot. -/
  opening_slot_pos : ∀ (S : Setup V) {r : Round} (hr : 0 < r), 0 < (M.opening_slot S.hc r)
  /-- A positive round opens at a positive slot. -/
  opening_slot_pos_of_round_pos : ∀ (hc : Protocol.HealConfig) {r : Round} (h : 0 < r), 0 < (M.opening_slot hc r)
  /-- The opening slot of the round of `s` is at or before `s`. -/
  opening_slot_round_of_le_slot : ∀ (hc : Protocol.HealConfig) (s : Slot), (M.opening_slot hc ((M.round_of hc s))) ≤ s
  /-- The opening slot of round `r + 1` is the opening slot of round `r` plus `R`. -/
  opening_slot_succ : ∀ (hc : Protocol.HealConfig) (r : Round), (M.opening_slot hc (r + 1)) = (M.opening_slot hc r) + hc.R
  /-- `opening_slot a + 1 ≤ opening_slot (a + 1)`. -/
  opening_slot_succ_le_l78 : ∀ (S : Setup V) (a : Round), (M.opening_slot S.hc a) + 1 ≤ (M.opening_slot S.hc (a + 1))
  /-- `opening_slot r + 1 < opening_slot (r + 1)`. -/
  opening_slot_succ_lt_l78 : ∀ (S : Setup V) (r : Round), (M.opening_slot S.hc r) + 1 < (M.opening_slot S.hc (r + 1))
  /-- `opening_slot (c + 1) + 1 ≤ opening_slot (c + 2)`. -/
  opening_slot_succ_lt_l88 : ∀ (S : Setup V) (c : Round), (M.opening_slot S.hc (c + 1)) + 1 ≤ (M.opening_slot S.hc (c + 2))
  /-- If an outcome of the opposition test of `u` for `B` is `true`, then, for every choice of
      outcomes of `u`'s views and of the cover test, either some late ready token of a round at
      least every early token's does not cover `B`, or two raw tokens of one such round carry
      different keys. -/
  opposing_cases : ∀ (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (o : Bool) (ho : M.opposing gv F η r early late u B ⇢ o) (h : o = true)
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : M.readyView gv F η r early u ⇢ Re)
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : M.readyView gv F η r late u ⇢ Rl)
    (W : Finset (Protocol.Token (Option BlockId))) (hW : M.rawView gv η r late u ⇢ W)
    (cov : Option BlockId → Bool) (hcov : ∀ k, M.localCovers gv k B ⇢ cov k), (∃ x ∈ Rl,
    (∀ y ∈ Re, y.round ≤ x.round) ∧
    ¬ cov x.key = true) ∨
    ∃ x ∈ W, ∃ y ∈ W,
    (∀ z ∈ Re, z.round ≤ x.round) ∧
    x.round = y.round ∧ x.key ≠ y.key
  /-- If `early ≤ late` and an outcome of the support test of `u` for `B` is `true`, every outcome
      of the opposition test of `u` for `B` is `false`. -/
  opposing_false_of_positive : ∀ (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (hel : early ≤ late) (p : Bool) (hp : M.positive gv F η r early late u B ⇢ p) (h : p = true) (o : Bool), M.opposing gv F η r early late u B ⇢ o → o = false
  /-- If a late ready token of `u` has a round at least every early ready token's and its key does
      not cover `B`, every outcome of the opposition test of `u` for `B` is `true`. -/
  opposing_of_late_not_covers : ∀ (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) {x : Protocol.Token (Option BlockId)}
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : M.readyView gv F η r late u ⇢ Rl) (hx : x ∈ Rl)
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : M.readyView gv F η r early u ⇢ Re) (hle : ∀ y ∈ Re, y.round ≤ x.round)
    (b : Bool) (hb : M.head_covers gv.T B x.key ⇢ b) (hnot : ¬ b = true) (o : Bool), M.opposing gv F η r early late u B ⇢ o → o = true
  /-- If `early ≤ late`, an outcome of the support test of `u` for `B` is `true`, and `B'` is not
      compatible with `B`, every outcome of the opposition test of `u` for `B'` is `true`. -/
  opposing_of_positive_not_compatible : ∀ (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (u : V) {B B' : Block V} (hel : early ≤ late) (hBB' : ¬ Block.Compatible B B') (p : Bool) (hp : M.positive gv F η r early late u B ⇢ p) (h : p = true) (o : Bool), M.opposing gv F η r early late u B' ⇢ o → o = true
  /-- If the cache clipped to `F` holds the root `root` for round `r₁` and phase `p`, the cache
      before clipping holds there a root that is `root` or a descendant of it. -/
  phaseResult_clipCache : ∀ {F : Block V} {c : M.Cache} {r₁ : Round} {p : Protocol.Phase} {root : Block V} (h : M.phaseResult (M.cacheAtRound (M.clipCache F c) r₁) p
    = some (some root)), ∃ root₀ : Block V,
    M.phaseResult (M.cacheAtRound c r₁) p = some (some root₀) ∧
    Block.Preceq root root₀
  /-- If the cache clipped to `F` holds a result for round `r` and phase `p`, the cache before
      clipping holds one there. -/
  phaseResult_clipCache_isSome : ∀ {F : Block V} {c : M.Cache} {r : Round} {p : Protocol.Phase} {o : Option (Block V)} (h : M.phaseResult (M.cacheAtRound (M.clipCache F c) r) p = some o), ∃ o', M.phaseResult (M.cacheAtRound c r) p = some o'
  /-- If the cache `c` holds the root `e` for round `r` and phase `p`, the cache clipped to `F`
      holds the clip of `e` at `F` there. -/
  phaseResult_clipCache_some : ∀ {F : Block V} {c : M.Cache} {r : Round} {p : Protocol.Phase} {e : Block V} (h : M.phaseResult (M.cacheAtRound c r) p = some (some e)), M.phaseResult (M.cacheAtRound (M.clipCache F c) r) p
    = some (some (M.clipGrade e F))
  /-- A frame's phase result at `g0` is its grade-0 field. -/
  phaseResult_g0 : ∀ (f : M.Frame), M.phaseResult f .g0 = f.g0
  /-- A frame's phase result at `g1` is its grade-1 field. -/
  phaseResult_g1 : ∀ (f : M.Frame), M.phaseResult f .g1 = f.g1
  /-- A frame's phase result at `g2` is its grade-2 field. -/
  Sts_phaseResult_g2 : ∀ (f : M.Frame), M.phaseResult f .g2 = f.g2
  /-- If an outcome of the cache a phase tick at `t` leaves holds the root `root` for round `r₁` and
      phase `p`, either the cache before held there a root that is `root` or a descendant of it, or
      `t` is that phase's domain instant and `root` is an ancestor of a block passing the grade
      test. -/
  phaseResult_onPhaseTick : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (t : Int) (c : M.Cache) {r₁ : Round} {p : Protocol.Phase} {root : Block V}
    (c' : M.Cache) (hc' : M.onPhaseTick E hc st t c ⇢ c') (h : M.phaseResult (M.cacheAtRound c' r₁) p
    = some (some root)) (g : Block V → Bool) (hg : ∀ B, M.gradeBool E (M.gradeView st) st.toFG.F hc.η_SG r₁ (M.early E hc r₁ p)
    (M.late E hc r₁ p) B ⇢ g B), (∃ root₀ : Block V,
    M.phaseResult (M.cacheAtRound c r₁) p = some (some root₀) ∧
    Block.Preceq root root₀) ∨
    (t = M.domain E hc r₁ p ∧ ∃ B : Block V,
    g B = true ∧ Block.Preceq root B)
  /-- If `t` is the domain instant for phase `p` of the round `r` after `t`'s round and the cache
      holds no result there, every outcome of the phase tick at `t` holds there the frozen root of
      `st`, clipped to `st`'s finalized block. -/
  phaseResult_onPhaseTick_domain : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (t : Int) (c : M.Cache) {r : Round} {p : Protocol.Phase} (hρ : (M.round_of hc (E.slotOf t)) + 1 = r) (ht : t = M.domain E hc r p) (h : M.phaseResult (M.cacheAtRound c r) p = none)
    (c' : M.Cache) (hc' : M.onPhaseTick E hc st t c ⇢ c')
    (fr : Option (Block V)) (hfr : M.freezeRoot E (M.gradeView st) st.toFG.F hc.η_SG r (M.early E hc r p)
    (M.late E hc r p) ⇢ fr), M.phaseResult (M.cacheAtRound c' r) p
    = some (fr.map (fun B => M.clipGrade B st.toFG.F))
  /-- If `0 ≤ t`, `t` is the domain instant for phase `p` of `t`'s own round `r` and the cache holds
      no result there, every outcome of the phase tick at `t` holds there the frozen root of `st`,
      clipped to `st`'s finalized block. -/
  phaseResult_onPhaseTick_domain_current : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (t : Int) (ht0 : 0 ≤ t) (c : M.Cache) {r : Round} {p : Protocol.Phase} (hρ : (M.round_of hc (E.slotOf t)) = r) (ht : t = M.domain E hc r p) (h : M.phaseResult (M.cacheAtRound c r) p = none)
    (c' : M.Cache) (hc' : M.onPhaseTick E hc st t c ⇢ c')
    (fr : Option (Block V)) (hfr : M.freezeRoot E (M.gradeView st) st.toFG.F hc.η_SG r (M.early E hc r p)
    (M.late E hc r p) ⇢ fr), M.phaseResult (M.cacheAtRound c' r) p
    = some (fr.map (fun B => M.clipGrade B st.toFG.F))
  /-- If `0 ≤ t`, `r` is `t`'s round or the next, and `t` is round `r`'s domain instant for phase
      `p`, every outcome of the phase tick at `t` holds a result for round `r` and phase `p`. -/
  phaseResult_onPhaseTick_domain_ne_none : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (t : Int) (ht0 : 0 ≤ t) (c : M.Cache) {r : Round} {p : Protocol.Phase} (hr : r = (M.round_of hc (E.slotOf t)) ∨ r = (M.round_of hc (E.slotOf t)) + 1) (ht : t = M.domain E hc r p) (c' : M.Cache), M.onPhaseTick E hc st t c ⇢ c' → M.phaseResult (M.cacheAtRound c' r) p ≠ none
  /-- A phase tick keeps a root the cache holds for a round it does not drop, clipped to the store's
      finalized block, in every outcome. -/
  phaseResult_onPhaseTick_kept : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (t : Int) (c : M.Cache) {r : Round} {p : Protocol.Phase} {e : Block V} (h : M.phaseResult (M.cacheAtRound c r) p = some (some e)) (hr : ((M.round_of hc (E.slotOf t)) = c.round ∧ (r = c.round ∨ r = c.round + 1)) ∨
    ((M.round_of hc (E.slotOf t)) = c.round + 1 ∧ r = c.round + 1)) (c' : M.Cache), M.onPhaseTick E hc st t c ⇢ c' → ∀ (hn : M.reachedRead st c := by trivial), M.phaseResult (M.cacheAtRound c' r) p
    = some (some (M.clipGrade e st.toFG.F))
  /-- If an outcome of the phase tick at `t` holds a result for round `r` and phase `p`, then `r` is
      `t`'s round, or `t` is that phase's domain instant, or the cache before held a result there. -/
  phaseResult_onPhaseTick_some_cases : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (t : Int) (c : M.Cache) {r : Round} {p : Protocol.Phase} {o : Option (Block V)} (c' : M.Cache) (hc' : M.onPhaseTick E hc st t c ⇢ c') (h : M.phaseResult (M.cacheAtRound c' r) p
    = some o), r = (M.round_of hc (E.slotOf t)) ∨ t = M.domain E hc r p ∨
    ∃ o', M.phaseResult (M.cacheAtRound c r) p = some o'
  /-- If an outcome of the phase tick at `t` holds a result for round `r` and phase `p`, then `t` is
      round `r`'s domain instant for `p`, or the cache before held a result there. -/
  phaseResult_onPhaseTick_some_domain_or_kept : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (t : Int) (c : M.Cache) {r : Round} {p : Protocol.Phase} {o : Option (Block V)} (c' : M.Cache) (hc' : M.onPhaseTick E hc st t c ⇢ c') (h : M.phaseResult (M.cacheAtRound c' r) p
    = some o), t = M.domain E hc r p ∨
    ∃ o', M.phaseResult (M.cacheAtRound c r) p = some o'
  /-- `opening_slot q + 2 ≤ opening_slot (q + 1)`. -/
  plusTwo_slot_le_nextOpening_l53 : ∀ (S : Setup V) (q : Round), (M.opening_slot S.hc q) + 2 ≤ (M.opening_slot S.hc (q + 1))
  /-- If an early ready token `u₀` of `u` has the largest round among them and covers `B`, no two
      raw tokens of one round at least `u₀`'s carry different keys, and every late ready token of a
      larger round covers `B`, every outcome of the support test of `u` for `B` is `true`. -/
  positive_of_conditions : ∀ (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V) (u₀ : Protocol.Token (Option BlockId))
    (Re : Finset (Protocol.Token (Option BlockId))) (hRe : M.readyView gv F η r early u ⇢ Re)
    (hmem : u₀ ∈ Re) (hlatest : ∀ x ∈ Re, x.round ≤ u₀.round)
    (cov : Option BlockId → Bool) (hcov' : ∀ k, M.head_covers gv.T B k ⇢ cov k)
    (hcov : cov u₀.key = true)
    (W : Finset (Protocol.Token (Option BlockId))) (hW : M.rawView gv η r late u ⇢ W)
    (hclean : ∀ x ∈ W, ∀ y ∈ W,
    u₀.round ≤ x.round → x.round = y.round → x.key = y.key)
    (Rl : Finset (Protocol.Token (Option BlockId))) (hRl : M.readyView gv F η r late u ⇢ Rl)
    (hlater : ∀ x ∈ Rl, u₀.round < x.round →
    cov x.key = true) (p : Bool), M.positive gv F η r early late u B ⇢ p → p = true
  /-- If `P` is an ancestor of the store's `M.get_fg_root` or that block itself, `P` is an ancestor
      of every outcome of `M.anchor` or that outcome itself. -/
  preceq_anchor_of_fgRoot : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (g1 : Option (Option (Block V))) {P : Block V} (hP : Block.Preceq P (M.get_fg_root st.toFG)) (a : Block V), M.anchor E hc st r g1 ⇢ a → Block.Preceq P a
  /-- If `P` is in the store's filtered tree and is an ancestor of `e` or `e` itself, `P` is an
      ancestor of every outcome of `M.anchor` at the grade-1 result `e`, or that outcome itself. -/
  preceq_anchor_of_g1 : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {P e : Block V} (hPt : P ∈ M.get_filtered_block_tree st.toFG) (hPe : Block.Preceq P e) (a : Block V), M.anchor E hc st r (some (some e)) ⇢ a → Block.Preceq P a
  /-- If `X` is compatible with `F` and is an ancestor of `g` or `g` itself, `X` is an ancestor of
      the clip of `g` at `F` or that block itself. -/
  preceq_clipGrade : ∀ {X F : Block V} (hXF : Block.compatible X F = true), ∀ g : Block V, Block.Preceq X g → Block.Preceq X (M.clipGrade g F)
  /-- If `P` is an ancestor of the grade read's anchor, of its grade-2 candidate when there is one,
      and of the store's `M.get_fg_root` when there is none, `P` is an ancestor of the SG walk's
      output or that block itself. -/
  preceq_currentSGVote_of_cases : ∀ {st : M.HS} {grades : Protocol.GradeRead V} {P : Block V} (hA : Block.Preceq P grades.anchor) (hQ : ∀ q : Block V, grades.Q2 = some q → Block.Preceq P q) (hR : grades.Q2 = none → Block.Preceq P (M.get_fg_root st.toFG)), Block.Preceq P (M.currentSGVote st grades)
  /-- If `floor ⪯ B ⪯ C` and `B` passes `test`, the deepest clear ancestor of `C` from `floor` is
      some block `D` with `B ⪯ D`. -/
  preceq_deepest_clear : ∀ {floor C B : Block V} {test : Block V → Bool} (hBC : Block.Preceq B C) (hfloor : Block.Preceq floor B) (htest : test B = true), ∃ D : Block V, M.deepest_clear (some floor) C test = some D ∧ Block.Preceq B D
  /-- If the round-`r` frame read from `c` at `st` holds the grade-2 root `e`, and `X ⪯ e` is in the
      store's filtered tree or is an ancestor of its `M.get_fg_root`, every stable root an outcome
      names is `X` or a descendant of `X`. -/
  preceq_frameStableRoot : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {X e G : Block V} (he : (M.readFrame c st r).g2 = some (some e)) (hXe : Block.Preceq X e) (hX : X ∈ M.get_filtered_block_tree st.toFG ∨
    Block.Preceq X (M.get_fg_root st.toFG)) (x : Option (Block V)) (hx : M.frameStableRoot c E hc st r ⇢ x) (hG : x = some G), Block.Preceq X G
  /-- If `X` is in the grade view's tree and passes the grade test, and every two blocks of the tree
      passing it are compatible, every outcome of the frozen root is some block that is `X` or a
      descendant of `X`. -/
  preceq_freezeRoot : ∀ (E : Env V) (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) {X : Block V}
    (g : Block V → Bool) (hg : ∀ B, M.gradeBool E gv F η r early late B ⇢ g B)
    (hXT : X ∈ gv.T) (hX : g X = true) (hcmp : ∀ D ∈ gv.T, ∀ D' ∈ gv.T, g D = true →
    g D' = true → Block.compatible D D' = true) (fr : Option (Block V)), M.freezeRoot E gv F η r early late ⇢ fr → ∃ D : Block V, fr = some D ∧ Block.Preceq X D
  /-- If the frame holds grade-0 and grade-1 results and the grade-2 root `e`, and `P` is in the
      store's filtered tree with `P ⪯ e`, every outcome of the frame's grade-2 block is some block
      that is `P` or a descendant of `P`. -/
  preceq_grade2Block_of_g2 : ∀ {st : M.HS} {frame : M.Frame} {o₀ o₁ : Option (Block V)} {P e : Block V} (h₀ : frame.g0 = some o₀) (h₁ : frame.g1 = some o₁) (h₂ : frame.g2 = some (some e)) (hPt : P ∈ M.get_filtered_block_tree st.toFG) (hPe : Block.Preceq P e) (o : Option (Block V)), M.grade2Block st frame ⇢ o → ∃ q : Block V, o = some q ∧ Block.Preceq P q
  /-- If the active prefix of `root` in `tree` is `L`, then `L` is an ancestor of `root` or `root`
      itself. -/
  preceq_of_activePrefix_eq_some : ∀ {tree : Finset (Block V)} {root L : Block V} (h : M.activePrefix tree root = some L), Block.Preceq L root
  /-- If an outcome of the cover test of `root` for `X` in the tree `T` is `true` and `root`
      resolves in `T` to `H`, then `X` is an ancestor of `H` or `H` itself. -/
  preceq_of_head_covers_of_find : ∀ {T : Finset (Block V)} {X H : Block V} {root : BlockId} (b : Bool) (hb : M.head_covers T X (some root) ⇢ b) (h : b = true) (hfind : Block.find? T root = some H), Block.Preceq X H
  /-- If an outcome of the cover test of `some root` for `B` in the grade view is `true` and `root`
      resolves in the view's tree to `H`, then `B` is an ancestor of `H` or `H` itself. -/
  preceq_of_localCovers_of_find : ∀ {gv : M.GV} {root : BlockId} {B H : Block V} (b : Bool) (hb : M.localCovers gv (some root) B ⇢ b) (hcov : b = true) (hfind : Block.find? gv.T root = some H), Block.Preceq B H
  /-- If the cache `c` holds the grade-1 root `e` for round `r`, the round-`r` frame read from `c`
      at `st` holds the clip of `e` at `st`'s finalized block as its grade-1 root. -/
  readFrame_g1_of_cache : ∀ {c : M.Cache} {st : M.HS} {r : Round} {e : Block V} (h : M.phaseResult (M.cacheAtRound c r) .g1 = some (some e)), (M.readFrame c st r).g1 = some (some (M.clipGrade e st.toFG.F))
  /-- If the round-`r` frame read from the cache `c` at `st` holds the grade-1 root `root`, the
      cache's own round-`r` frame holds a grade-1 root that is `root` or a descendant of it. -/
  readFrame_g1_provenance : ∀ (c : M.Cache) (st : M.HS) (r : Round) {root : Block V} (h : (M.readFrame c st r).g1 = some (some root)), ∃ root₀ : Block V,
    M.phaseResult (M.cacheAtRound c r) .g1 = some (some root₀) ∧
    Block.Preceq root root₀
  /-- If the cache `c` holds the grade-2 root `e` for round `r`, the round-`r` frame read from `c`
      at `st` holds the clip of `e` at `st`'s finalized block as its grade-2 root. -/
  readFrame_g2_of_cache : ∀ {c : M.Cache} {st : M.HS} {r : Round} {e : Block V} (h : M.phaseResult (M.cacheAtRound c r) .g2 = some (some e)), (M.readFrame c st r).g2 = some (some (M.clipGrade e st.toFG.F))
  /-- If the round-`r` frame read from the cache `c` at `st` holds the grade-2 root `root`, the
      cache's own round-`r` frame holds a grade-2 root that is `root` or a descendant of it. -/
  readFrame_g2_provenance : ∀ (c : M.Cache) (st : M.HS) (r : Round) {root : Block V} (h : (M.readFrame c st r).g2 = some (some root)), ∃ root₀ : Block V,
    M.phaseResult (M.cacheAtRound c r) .g2 = some (some root₀) ∧
    Block.Preceq root root₀
  /-- If the cache `c` holds the root `e` for round `r` and phase `p`, the round-`r` frame read from
      `c` at `st` holds the clip of `e` at `st`'s finalized block for `p`. -/
  readFrame_phase_of_cache : ∀ {c : M.Cache} {st : M.HS} {r : Round} {p : Protocol.Phase} {e : Block V} (h : M.phaseResult (M.cacheAtRound c r) p = some (some e)), M.phaseResult (M.readFrame c st r) p
    = some (some (M.clipGrade e st.toFG.F))
  /-- If the round-`r` frame read from the cache `c` at `st` holds the root `root` for phase `p`,
      the cache's own round-`r` frame holds for `p` a root that is `root` or a descendant of it. -/
  readFrame_phase_provenance : ∀ (c : M.Cache) (st : M.HS) (r : Round) {p : Protocol.Phase} {root : Block V} (h : M.phaseResult (M.readFrame c st r) p = some (some root)), ∃ root₀ : Block V,
    M.phaseResult (M.cacheAtRound c r) p = some (some root₀) ∧
    Block.Preceq root root₀
  /-- If `s ≤ s'`, the round of `s` is at or before the round of `s'`. -/
  round_of_mono : ∀ (hc : Protocol.HealConfig) {s s' : Slot} (h : s ≤ s'), (M.round_of hc s) ≤ (M.round_of hc s')
  /-- If `s_0 ≤ s_1`, the round of `s_0` is at or before the round of `s_1`. -/
  round_of_mono_sts : ∀ (hc : Protocol.HealConfig) {s_0 s_1 : Slot} (h : s_0 ≤ s_1), (M.round_of hc s_0) ≤ (M.round_of hc s_1)
  /-- For `j < R`, the slot `j` places after round `ρ`'s opening slot is in round `ρ`. -/
  round_of_opening_slot_add : ∀ (hc : Protocol.HealConfig) (ρ : Round) {j : Nat} (hj : j < hc.R), (M.round_of hc ((M.opening_slot hc ρ) + j)) = ρ
  /-- If `0 < ρ` and `sEnd ≤ opening_slot ρ + 1`, then `round_of (sEnd − 2) < ρ`. -/
  round_of_sub_two_lt : ∀ (hc : Protocol.HealConfig) {ρ : Nat} {sEnd : Nat} (hρ : 0 < ρ) (h : sEnd ≤ (M.opening_slot hc ρ) + 1), (M.round_of hc (sEnd - 2)) < ρ
  /-- `opening_slot (round_of s) ≤ s < opening_slot (round_of s + 1)`. -/
  slot_round_bounds_l86e : ∀ (S : Setup V) (s : Slot), (M.opening_slot S.hc ((M.round_of S.hc s))) ≤ s ∧
    s < (M.opening_slot S.hc ((M.round_of S.hc s) + 1))
  /-- The key of the token of the attestation `y` is the root `y` names as confirmed. -/
  token_key : ∀ (y : Protocol.SGVote V), (M.token y).key = y.confirmed
  /-- The round of the token of the attestation `y` is `y`'s round. -/
  token_round : ∀ (y : Protocol.SGVote V), (M.token y).round = y.round
  /-- Every attestation in an outcome of `sender`'s raw inputs is signed by `sender`. -/
  val_index_of_mem_rawInputs : ∀ {gv : M.GV} {eta r : Round} {cutoff : Time} {sender : V} {u : Protocol.SGVote V} (X : Finset (Protocol.SGVote V)) (hX : M.rawInputs gv eta r cutoff sender ⇢ X) (hu : u ∈ X), u.val_index = sender
  /-- Every support test has an outcome. -/
  positive_nonempty : ∀ (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V),
    ∃ p : Bool, M.positive gv F η r early late u B ⇢ p
  /-- Every opposition test has an outcome. -/
  opposing_nonempty : ∀ (gv : M.GV) (F : Block V) (η r : Round) (early late : Time) (u : V) (B : Block V),
    ∃ o : Bool, M.opposing gv F η r early late u B ⇢ o
  /-- Every raw view has an outcome. -/
  rawView_nonempty : ∀ (gv : M.GV) (η r : Round) (c : Time) (u : V),
    ∃ X : Finset (Protocol.Token (Option BlockId)), M.rawView gv η r c u ⇢ X
  /-- Every ready view has an outcome. -/
  readyView_nonempty : ∀ (gv : M.GV) (F : Block V) (η r : Round) (c : Time) (u : V),
    ∃ X : Finset (Protocol.Token (Option BlockId)), M.readyView gv F η r c u ⇢ X
  /-- Every head cover test has an outcome. -/
  head_covers_nonempty : ∀ (T : Finset (Block V)) (B : Block V) (k : Option BlockId),
    ∃ b : Bool, M.head_covers T B k ⇢ b
  /-- Every phase tick has an outcome. -/
  onPhaseTick_nonempty : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (t : Int) (c : M.Cache),
    ∃ c' : M.Cache, M.onPhaseTick E hc st t c ⇢ c'
  /-- Every raw input computation has an outcome. -/
  rawInputs_nonempty : ∀ (gv : M.GV) (η r : Round) (c : Time) (u : V),
    ∃ Y : Finset (Protocol.SGVote V), M.rawInputs gv η r c u ⇢ Y
  /-- Every grade read of a contract has an outcome. -/
  read_nonempty : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round),
    ∃ G, gc.read E hc st r ⇢ G
  /-- Every anchor computation has an outcome. -/
  anchor_nonempty : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (g1 : Option (Option (Block V))),
    ∃ a, M.anchor E hc st r g1 ⇢ a
  /-- Every grade-2 block computation of a frame has an outcome. -/
  grade2Block_nonempty : ∀ (st : M.HS) (frame : M.Frame),
    ∃ o : Option (Block V), M.grade2Block st frame ⇢ o
  /-- Every grade test has an outcome. -/
  gradeBool_nonempty : ∀ (E : Env V) (gv : M.GV) (F : Block V) (η r : Round) (early late : Time)
    (B : Block V), ∃ b : Bool, M.gradeBool E gv F η r early late B ⇢ b
  /-- Every body condition has an outcome. -/
  bodyReady_nonempty : ∀ (gv : M.GV) (F : Block V) (c : Time) (u : Protocol.SGVote V),
    ∃ b : Bool, M.bodyReady gv F c u ⇢ b
  /-- A round's grade-2 early cutoff is at least one delay before its grade-1 early cutoff. -/
  early_g2_add_delta_le_early_g1 : ∀ (S : Setup V) (r : Round), M.early S.E S.hc r .g2 + S.E.Δ ≤ M.early S.E S.hc r .g1
  /-- A round's grade-1 early cutoff is at least one delay before its grade-0 early cutoff. -/
  early_g1_add_delta_le_early_g0 : ∀ (S : Setup V) (r : Round), M.early S.E S.hc r .g1 + S.E.Δ ≤ M.early S.E S.hc r .g0
  /-- A round's grade-1 late cutoff is at least one delay before its grade-2 late cutoff. -/
  late_g1_add_delta_le_late_g2 : ∀ (S : Setup V) (r : Round), M.late S.E S.hc r .g1 + S.E.Δ ≤ M.late S.E S.hc r .g2
  /-- A round's grade-0 late cutoff is at least one delay before its grade-1 late cutoff. -/
  late_g0_add_delta_le_late_g1 : ∀ (S : Setup V) (r : Round), M.late S.E S.hc r .g0 + S.E.Δ ≤ M.late S.E S.hc r .g1
  /-- A round's grade-2 early cutoff is at most five delays before its opening instant. -/
  opening_sub_five_delta_le_early_g2 : ∀ (S : Setup V) (r : Round), M.opening S.E S.hc r - 5 * S.E.Δ ≤ M.early S.E S.hc r .g2
  /-- One delay after a round's grade-1 late cutoff is strictly before its opening instant. -/
  late_g1_add_delta_lt_opening : ∀ (S : Setup V) (r : Round), M.late S.E S.hc r .g1 + S.E.Δ < M.opening S.E S.hc r
  /-- Two raw tokens of one round, at least every early token's, with different keys make the tokens
      oppose `B`. -/
  opposes_of_raw : ∀ {Key : Type} {Blk : Type} {covers : Key → Blk → Prop} {early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)} {B : Blk} (x : DecoupledConsensusModel.Protocol.Token Key), x ∈ raw → ∀ (y : DecoupledConsensusModel.Protocol.Token Key), y ∈ raw → (∀ u ∈ early, u.round ≤ x.round) → x.round = y.round → x.key ≠ y.key → M.Opposes covers early late raw B
  /-- If the cache `c` has a result for round `r` and phase `p`, the cache clipped to `F` has a
      result there. -/
  phaseResult_clipCache_ne_none : ∀ (F : Block V) (c : M.Cache) (r : Round) (p : Protocol.Phase),
    M.phaseResult (M.cacheAtRound c r) p ≠ none →
    M.phaseResult (M.cacheAtRound (M.clipCache F c) r) p ≠ none
  /-- A positive round `r` is the round of the slot of its domain instant for any phase, or that
      round plus one. -/
  round_of_slotOf_domain : ∀ (S : Setup V) {r : Round} (hr : 0 < r) (p : Protocol.Phase),
    r = M.round_of S.hc (S.E.slotOf (M.domain S.E S.hc r p)) ∨
    r = M.round_of S.hc (S.E.slotOf (M.domain S.E S.hc r p)) + 1
  /-- Every phase domain instant of a positive round is a whole number of delays `S.E.Δ`. -/
  publicTime_domain : ∀ (S : Setup V) {r : Round} (hr : 0 < r) (p : Protocol.Phase),
    PublicTime S (M.domain S.E S.hc r p)
  /-- The G0 late cutoff of a positive round is a whole number of delays `S.E.Δ`. -/
  late_g0_public : ∀ (S : Setup V) (s : Round) (hs : 0 < s), PublicTime S (M.late S.E S.hc s .g0)
  /-- A round's G2 domain instant is at or before its G2 late cutoff. -/
  q10_domain_g2_le_late_g2 : ∀ (S : Setup V) (r : Round), M.domain S.E S.hc r .g2 ≤ M.late S.E S.hc r .g2
  /-- For every round `r` and phase `p`, round `r`'s action instant plus three delays is at or
      before the late cutoff of phase `p` of round `r + 1`. -/
  action_add_three_delta_le_late_succ : ∀ (S : Setup V) (r : Round) (p : Protocol.Phase),
    M.a S.hc S.E.Δ r + 3 * S.E.Δ ≤ M.late S.E S.hc (r + 1) p
  /-- If the round of `c` is at most the round of `t`'s slot, which is at most `r`, and `c` has a
      result for round `r` and phase `p`, every outcome of the phase tick at `t` has a result there. -/
  phaseResult_onPhaseTick_ne_none_of_le : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.HS)
    (t : Time) (c : M.Cache) (r : Round) (p : Protocol.Phase),
    c.round ≤ M.round_of hc (E.slotOf t) → M.round_of hc (E.slotOf t) ≤ r →
    M.phaseResult (M.cacheAtRound c r) p ≠ none →
    ∀ c' : M.Cache, M.onPhaseTick E hc st t c ⇢ c' →
    M.phaseResult (M.cacheAtRound c' r) p ≠ none
  /-- Every cover test of a grade view has an outcome. -/
  localCovers_nonempty : ∀ (gv : M.GV) (k : Option BlockId) (B : Block V),
    ∃ b : Bool, M.localCovers gv k B ⇢ b
  /-- Every interpreted-input computation has an outcome. -/
  interpretedInputs_nonempty : ∀ (gv : M.GV) (F : Block V) (η r : Round) (c : Time) (u : V),
    ∃ Y : Finset (Protocol.SGVote V), M.interpretedInputs gv F η r c u ⇢ Y
  /-- Every frozen-root computation has an outcome. -/
  freezeRoot_nonempty : ∀ (E : Env V) (gv : M.GV) (F : Block V) (η r : Round) (early late : Time),
    ∃ fr : Option (Block V), M.freezeRoot E gv F η r early late ⇢ fr
  /-- A round's grade-2 domain instant is at least one delay before its grade-1 domain instant. -/
  domain_g2_add_delta_le_domain_g1 : ∀ (S : Setup V) (r : Round), M.domain S.E S.hc r .g2 + S.E.Δ ≤ M.domain S.E S.hc r .g1
  /-- One delay after a round's grade-1 domain instant is at or before its grade-0 domain instant. -/
  domain_g1_add_delta_le_domain_g0 : ∀ (S : Setup V) (r : Round), M.domain S.E S.hc r .g1 + S.E.Δ ≤ M.domain S.E S.hc r .g0
  /-- A round's grade-1 domain instant is its opening instant. -/
  Sts_domain_g1_eq_opening : ∀ (S : Setup V) (r : Round), M.domain S.E S.hc r .g1 = M.opening S.E S.hc r
  /-- If, for every choice of outcomes of the interpreted inputs at the early cutoff, the weight
      outside `Hon` is less than the weight of the members of `Hon` with a nonempty input, and the
      grade test of `B` passes, some member of `Hon` passes the support test for `B` with a latest
      interpreted input whose confirmed root resolves to a descendant of `B` or `B` itself. -/
  exists_honest_max_positive_supporter_of_relativeGrade : ∀ (E : Env V) (hc : Protocol.HealConfig)
    {gv : M.GV} {F : Block V} {Hon : Finset V} {r : Round} {B : Block V} {p : Protocol.Phase},
    (∀ ins : V → Finset (Protocol.SGVote V),
      (∀ v, M.interpretedInputs gv F hc.η_SG r (M.early E hc r p) v ⇢ ins v) →
      E.electorate.weightOf (Finset.univ \ Hon) <
        E.electorate.weightOf (Hon.filter fun v => (ins v).Nonempty)) →
    ∀ g : Bool, M.gradeBool E gv F hc.η_SG r (M.early E hc r p) (M.late E hc r p) B ⇢ g →
    g = true →
    ∃ v ∈ Hon, ∃ I : Finset (Protocol.SGVote V),
      M.interpretedInputs gv F hc.η_SG r (M.early E hc r p) v ⇢ I ∧
      ∃ u ∈ I, ∃ head : Block V, u.confirmed = some head.root ∧
        Block.find? gv.T head.root = some head ∧ head ∈ gv.T ∧ Block.Preceq B head ∧
        (∀ b : Bool, M.positive gv F hc.η_SG r (M.early E hc r p) (M.late E hc r p) v B ⇢ b →
          b = true) ∧
        ∀ x ∈ I, x.round ≤ u.round
  /-- Every stable-root computation of a frame has an outcome. -/
  frameStableRoot_nonempty : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS)
    (r : Round), ∃ x : Option (Block V), M.frameStableRoot c E hc st r ⇢ x
  /-- A round's grade-0 domain instant is one delay after its opening instant. -/
  domain_g0_eq_opening : ∀ (S : Setup V) (r : Round),
    M.domain S.E S.hc r .g0 = M.opening S.E S.hc r + S.E.Δ
  /-- A round's late grade-0 cutoff is its early grade-0 cutoff. -/
  allPhasesCutoff_eq_early_g0 : ∀ (S : Setup V) (q : Round),
    M.late S.E S.hc q .g0 = M.early S.E S.hc q .g0

/-- The facts about runs of the grades routines of `M`. -/
structure GradesRunFacts (M : Model V) : Prop where
  /-- A completed phase result in `v`'s cache before event `i` of `rho` is the empty round-0 result,
      or was captured by an earlier tick of `v` at that phase's domain instant: the frozen root of
      `v`'s store then, clipped to the current finalized block. -/
  completed_phase_origin : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) (r : Round)
    (p : Protocol.Phase) (root : Option (Block V)), ∀ w₁ ∈ stateBeforeOf M S rho i,
    M.phaseResult (M.cacheAtRound (w₁ v).cache r) p = some root →
    (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
      j < i ∧ rho.events[j]? = some (.tick v t) ∧ t = M.domain S.E S.hc r p ∧
      ∃ w ∈ stateBeforeOf M S rho j,
      w₁ ∈ ((rho.events.drop j).take (i - j)).foldlM (worldStepOf M S) w ∧
      ∀ fr : Option (Block V), M.freezeRoot S.E
        (M.gradeView (M.toHealing (w v).st.core))
        (w v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r p) (M.late S.E S.hc r p) ⇢ fr →
      root = fr.map (fun B => M.clipGrade B (w₁ v).st.core.F)
  /-- The cache of a validator's initial node state holds results for round `0` only. -/
  phaseResult_initial_some : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V) (x : Framework.StsMultisetLog.AtomicExec (Record.protocolOf M S) Sched) (v : V) {r : Round} {p : Protocol.Phase} {o : Option (Block V)} (h : M.phaseResult (M.cacheAtRound (x[0][v].st).cache r) p = some o), r = 0
  /-- The grade-2 block read at round `r`'s action instant by `v` before event `i` of `rho` is an
      ancestor of a G2 root that `v` froze at an earlier tick at round `r`'s G2 domain instant. -/
  q2_capture_at_action_read : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) (r : Round)
    (q : Block V), ∀ w₁ ∈ stateBeforeOf M S rho i,
    ∀ (c : M.Cache), M.onPhaseTick S.E S.hc (w₁ v).st.core.toHealing (M.a S.hc S.E.Δ r)
      (w₁ v).cache ⇢ c →
    ∀ (st : M.NS), M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (w₁ v).st (M.a S.hc S.E.Δ r)) (S.E.slotOf (M.a S.hc S.E.Δ r) - 1) ⇢ st →
    M.grade2_block_with (M.gradeContract (M.mkNode st (w₁ v).record c).cache) S.E S.hc
      (M.toHealing (M.mkNode st (w₁ v).record c).st.core) r ⇢ some q →
    ∃ (j : Nat) (raw : Block V),
      j < i ∧
      rho.events[j]? = some (.tick v (M.domain S.E S.hc r .g2)) ∧
      ∃ w ∈ stateBeforeOf M S rho j,
      w₁ ∈ ((rho.events.drop j).take (i - j)).foldlM (worldStepOf M S) w ∧
      (∀ fr : Option (Block V), M.freezeRoot S.E (M.gradeView (M.toHealing (w v).st.core))
        (w v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) ⇢ fr → fr = some raw) ∧
      Block.Preceq q raw
  /-- If `u`'s slot is in round `r`, the phase tick at `u` keeps the result for phase `p` of the
      round-`r` frame of `v`'s node state, in every outcome. -/
  frame_phase_prepared_eq_of_outcomes : ∀ (S : Setup V) (rho : Record.Run V) (v : V) (r : Round)
    (p : Protocol.Phase) (u : Time) (hround : M.round_of S.hc (S.E.slotOf u) = r)
    (root : Option (Block V)) (w : V → M.N)
    (hw : w ∈ (rho.events.filter (fun e => decide (e.time < u))).foldlM (worldStepOf M S)
      (fun x => M.initial S x))
    (hbase : M.phaseResult (M.readFrame (w v).cache (M.toHealing (w v).st.core) r) p = some root)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (w v).st.core.toHealing u (w v).cache ⇢ c),
    M.phaseResult (M.readFrame c (M.toHealing (M.ns_setClock S.E (w v).st u).core) r) p = some root
  /-- Along a path `W` of `rho`, a completed phase result in `v`'s cache at `W i` is the empty
      round-0 result, or is the frozen root of `v`'s store at an earlier tick `j` of `v` at that
      phase's domain instant, clipped to the finalized block at `W i`. -/
  completed_phase_origin_along : ∀ (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N),
    (∀ i : Nat, W i ∈ stateBeforeOf M S rho i ∧
      W (i + 1) ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (worldStepOf M S) (W i)) →
    ∀ (i : Nat) (v : V) (r : Round) (p : Protocol.Phase) (root : Option (Block V)),
    M.phaseResult (M.cacheAtRound (W i v).cache r) p = some root →
    (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
      j < i ∧ rho.events[j]? = some (.tick v t) ∧ t = M.domain S.E S.hc r p ∧
      ∀ fr : Option (Block V), M.freezeRoot S.E
        (M.gradeView (M.toHealing (W j v).st.core))
        (W j v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r p) (M.late S.E S.hc r p) ⇢ fr →
      root = fr.map (fun B => M.clipGrade B (W i v).st.core.F)
  /-- Along a path `W` of `rho`, the grade-2 block read at round `r`'s action instant by `v` at
      `W i` is an ancestor of the G2 root frozen from `v`'s store at an earlier tick `j` of `v` at
      round `r`'s G2 domain instant. -/
  q2_capture_at_action_read_along : ∀ (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N),
    (∀ i : Nat, W i ∈ stateBeforeOf M S rho i ∧
      W (i + 1) ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (worldStepOf M S) (W i)) →
    ∀ (i : Nat) (v : V) (r : Round) (q : Block V),
    ∀ (c : M.Cache), M.onPhaseTick S.E S.hc (W i v).st.core.toHealing (M.a S.hc S.E.Δ r)
      (W i v).cache ⇢ c →
    ∀ (st : M.NS), M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (W i v).st (M.a S.hc S.E.Δ r)) (S.E.slotOf (M.a S.hc S.E.Δ r) - 1) ⇢ st →
    M.grade2_block_with (M.gradeContract (M.mkNode st (W i v).record c).cache) S.E S.hc
      (M.toHealing (M.mkNode st (W i v).record c).st.core) r ⇢ some q →
    ∃ (j : Nat) (raw : Block V),
      j < i ∧
      rho.events[j]? = some (.tick v (M.domain S.E S.hc r .g2)) ∧
      (∀ fr : Option (Block V), M.freezeRoot S.E (M.gradeView (M.toHealing (W j v).st.core))
        (W j v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) ⇢ fr → fr = some raw) ∧
      Block.Preceq q raw

/-! ## Frame reads compared through the finalized block -/

/-- If two healing stores have the same finalized block, the round-`r` frames read from one cache at
    the two stores have the same result at every phase. -/
theorem GradesFacts.readFrame_phase_eq_of_F {M : Model V} (gr : GradesFacts M) (c : M.Cache)
    {st st' : M.HS} (r : Round) (hF : st.toFG.F = st'.toFG.F) (p : Protocol.Phase) :
    M.phaseResult (M.readFrame c st r) p = M.phaseResult (M.readFrame c st' r) p := by
  rw [gr.readFrame_phase, gr.readFrame_phase, hF]

/-- If two healing stores have the same finalized block, the round-`r` frames read from one cache at
    the two stores have the same grade-1 result. -/
theorem GradesFacts.readFrame_g1_eq_of_F {M : Model V} (gr : GradesFacts M) (c : M.Cache)
    {st st' : M.HS} (r : Round) (hF : st.toFG.F = st'.toFG.F) :
    (M.readFrame c st r).g1 = (M.readFrame c st' r).g1 := by
  rw [← gr.phaseResult_g1, ← gr.phaseResult_g1]
  exact gr.readFrame_phase_eq_of_F c r hF .g1

end DecoupledConsensusModel.Sts.Record
