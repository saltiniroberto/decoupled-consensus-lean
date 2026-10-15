import Proofs.Claims.Spec2Claims.Claim13bModel_ghost
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_fork_choice
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_with
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesDelivery
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_parent_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG5

/-!
# The voter's Goldfish fork choice returns the proposal

The Goldfish eligibility test carried from one store to another, and the theorem that a voter's
Goldfish fork choice returns the child `B` of the proposer's result when the two stores agree on
scores and trees; with small facts on ancestors and slots.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The Goldfish fork choice -/

/-- If `C` is a child of `X`, the first store's `h_max` minus one is at most `X`'s chain-state
    height there, the two participant counts are equal, the two scores of `C` are equal, and the
    first store's eligibility test admits `C`, then the second store's test with the same store slot
    admits `C`. -/
theorem goldfish_eligible_transfer (E : Env V) {σ σ' : Block V → Protocol.ChainState V}
    {h h' : Height} {T T' : Finset (Block V)} {cur : Slot}
    {votes support votes' support' : Finset (GoldfishVote V)} {s' : Slot} {C X : Block V}
    (hpar : C.parent? = some X) (hh : h - 1 ≤ (σ X).h)
    (hcount : Protocol.voters_count E votes' s' = Protocol.voters_count E votes s')
    (hscore : Protocol.goldfish_score E T' votes' support' s' C =
      Protocol.goldfish_score E T votes support s' C)
    (hel : Protocol.goldfish_eligible E σ h T cur votes support s' C = true) :
    Protocol.goldfish_eligible E σ' h' T' cur votes' support' s' C = true := by
  rw [Proofs.Optimistic.goldfish_eligible_iff] at hel ⊢
  have hCX : C.parent = X := Proofs.parent_eq_of_parent? hpar
  rcases hel with h1 | h2 | h3
  · rw [hCX] at h1
    exact absurd h1 (Nat.not_lt.mpr hh)
  · exact Or.inr (Or.inl (by rw [hcount, hscore]; exact h2))
  · exact Or.inr (Or.inr h3)

/-- Suppose the proposer's Goldfish fork choice from `Ap` through `Tp` returns `P`; `Ap ⪯ Y`,
    `Av ⪯ Y`, `Y ⪯ P`; the voter's fork choice from `Av` through `Tv` returns a descendant of `Y`;
    at both stores `h_max − 1` is at most the chain-state height of every block `X` with
    `Y ⪯ X ⪯ P`; the two stores give every descendant of `Y` the same score and have the same
    participant count; every block `C ≠ Y` with `Y ⪯ C ⪯ P` is in `Tv`; every child in `Tv` of such
    an `X` that is not of the store slot `cur` is in `Tp`; `B` is the only block of `Tv` of slot
    `cur`, is in `Tv`, is a child of `P`, and is the parent of no block of `Tv`. Then the voter's
    fork choice returns `B`. -/
theorem goldfish_fork_choice_eq_child_of_pivot (E : Env V)
    {σp σv : Block V → Protocol.ChainState V} {hp hv : Height}
    {TPs TVs Tp Tv : Finset (Block V)} {cur : Slot}
    {votesP supportP votesV supportV : Finset (GoldfishVote V)} {s' : Slot}
    {Ap Av Y P B : Block V}
    (hrootP : RootInjectiveBelow Tp) (hrootV : RootInjectiveBelow Tv)
    (hsource : Protocol.goldfish_fork_choice E σp hp TPs cur Ap Tp votesP supportP s' = P)
    (hApY : Block.Preceq Ap Y) (hAvY : Block.Preceq Av Y) (hYP : Block.Preceq Y P)
    (hpasses : Block.Preceq Y
      (Protocol.goldfish_fork_choice E σv hv TVs cur Av Tv votesV supportV s'))
    (hhP : ∀ X, Block.Preceq Y X → Block.Preceq X P → hp - 1 ≤ (σp X).h)
    (hhV : ∀ X, Block.Preceq Y X → Block.Preceq X P → hv - 1 ≤ (σv X).h)
    (hscore : ∀ C, Block.Preceq Y C →
      Protocol.goldfish_score E TVs votesV supportV s' C =
        Protocol.goldfish_score E TPs votesP supportP s' C)
    (hcount : Protocol.voters_count E votesV s' = Protocol.voters_count E votesP s')
    (hpathV : ∀ C, Block.Preceq Y C → C ≠ Y → Block.Preceq C P → C ∈ Tv)
    (hchildV : ∀ X C, Block.Preceq Y X → Block.Preceq X P → C ∈ Tv → C.parent? = some X →
      C.slot ≠ cur → C ∈ Tp)
    (hBonly : ∀ C ∈ Tv, C.slot = cur → C = B)
    (hB : B ∈ Tv) (hBpar : B.parent? = some P) (hBslot : B.slot = cur)
    (hfresh : ∀ C ∈ Tv, C.parent? ≠ some B) :
    Protocol.goldfish_fork_choice E σv hv TVs cur Av Tv votesV supportV s' = B := by
  rw [goldfish_fork_choice_eq_ghost] at hsource hpasses ⊢
  refine ghost_eq_child_of_pivot hrootP hrootV hsource hApY hAvY hYP hpasses hpathV ?_ ?_ ?_ hB
    hBpar ?_ hfresh
  · intro X C hYX hXP hpar _ hel hCP
    have hYC : Block.Preceq Y C := Proofs.ModelProperties.Preceq_trans hYX (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Protocol.preceq_of_parent? hpar))
    exact goldfish_eligible_transfer E hpar (hhP X hYX hXP) hcount (hscore C hYC) hel
  · intro X C hYX hXP hC hCB hpar hel
    have hYC : Block.Preceq Y C := Proofs.ModelProperties.Preceq_trans hYX (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Protocol.preceq_of_parent? hpar))
    have hslot : C.slot ≠ cur := fun h => hCB (hBonly C hC h)
    exact ⟨hchildV X C hYX hXP hC hpar hslot,
      goldfish_eligible_transfer E hpar (hhV X hYX hXP) hcount.symm (hscore C hYC).symm hel⟩
  · intro C hYC _ _
    exact hscore C hYC
  · exact Proofs.Optimistic.goldfish_eligible_current E σv hv TVs cur votesV supportV s' hBslot

/-! ## Small facts -/

omit [Fintype V] in
/-- Of two ancestors `a` and `b` of one block `H`, one is a descendant of both and an ancestor of
    `H`. -/
theorem exists_deeper_of_two {a b H : Block V} (ha : Block.Preceq a H) (hb : Block.Preceq b H) :
    ∃ Y, Block.Preceq a Y ∧ Block.Preceq b Y ∧ Block.Preceq Y H ∧ (Y = a ∨ Y = b) := by
  rcases Proofs.ModelProperties.Preceq_linear ha hb with hab | hba
  · exact ⟨b, hab, Proofs.ModelProperties.Preceq_self b, hb, Or.inr rfl⟩
  · exact ⟨a, Proofs.ModelProperties.Preceq_self a, hba, ha, Or.inl rfl⟩

omit [Fintype V] in
/-- Of three ancestors of one block `H`, one is a descendant of the other two and an ancestor of
    `H`. -/
theorem exists_deepest_of_three {a b c H : Block V} (ha : Block.Preceq a H)
    (hb : Block.Preceq b H) (hc : Block.Preceq c H) :
    ∃ Y, Block.Preceq a Y ∧ Block.Preceq b Y ∧ Block.Preceq c Y ∧ (Y = a ∨ Y = b ∨ Y = c) := by
  obtain ⟨Y₁, haY, hbY, hYH, hY₁⟩ := exists_deeper_of_two ha hb
  obtain ⟨Y, hY₁Y, hcY, -, hY⟩ := exists_deeper_of_two hYH hc
  refine ⟨Y, Proofs.ModelProperties.Preceq_trans haY hY₁Y, Proofs.ModelProperties.Preceq_trans hbY hY₁Y, hcY, ?_⟩
  rcases hY with rfl | rfl
  · rcases hY₁ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- If `3 ≤ R` and `o + R ≤ s`, then `o + 2 ≤ s` and `o + 2 ≤ s − 1`, over `Nat`. -/
theorem nat_opening_le_g5 {o R s : Nat} (hR : 3 ≤ R) (h : o + R ≤ s) :
    o + 2 ≤ s ∧ o + 2 ≤ s - 1 := by omega

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section PremisesG4

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (tE : Int)
    (hexec : ExecutionValid S Sched (interface S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : TimeDiverges x)
    (hcatch : CatchUpOnWake S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + healingLengthη S gap ≤ tE)
    (hsync : SynchronyFromWake S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : roundSleepinessW S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : CommonViewOfFinalizedDescendantsAt S Sched x tGAT)
    (hcs : committeeSleepinessW S Sched tE)
    (hcom : HonestCommittees S Sched (interface S Sched))
    (hw : WakesAtActionInstants S Sched) (hs : SleepsAfterActionInstants S Sched)
    (hrec : strongOpeningsRecurFrom S Sched tGAT tE gap)
    (hprev : ∀ r : Round, rebasedDeadlineRoundW S tGAT gap ≤ r → r ≤ switchRound S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      S.a r ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      NamedHeightRegimeRunOn (Setup.alwaysAwake S)
        ({ runAll S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Run V)
        (notHeldAt Sched) Finset.univ Finset.univ
        (roundAt S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → BasePreviousRoundSGCompatibleWithAnchorAtRound S Sched x v r N T)
    (hclear : ∀ r : Round, rebasedDeadlineRoundW S tGAT gap ≤ r → r ≤ switchRound S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      S.a r ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      NamedHeightRegimeRunOn (Setup.alwaysAwake S)
        ({ runAll S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Run V)
        (notHeldAt Sched) Finset.univ Finset.univ
        (roundAt S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → tickStepAt x n₀ (S.a r) →
      BaseClearFGSourceCompatibleWithAnchorAtRound S Sched x r n₀ T)
    (hB' : BaseJustifiedHighAtSwitchRoundW S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : tickStepAt x n_W (S.a (switchRound S tE)))
    {T_W : NamedBlock V} (hAW : AnchorAtRound S Sched x tGAT tE (switchRound S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      Protocol.vote_time S.E (S.hc.opening_slot (switchRound S tE) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → HonestThrough Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)

include hexec hmono htd hcatch hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec
  hprev hclear hB' hnW hAW hJswitch

end PremisesG4

end DecoupledConsensusModel.Sts
