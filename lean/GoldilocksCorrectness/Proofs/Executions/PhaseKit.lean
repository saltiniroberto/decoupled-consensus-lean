module
public import GoldilocksCorrectness.Statements.Executions.PhaseDefs
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Statements.Routines.FrameStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityStatements
public import GoldilocksCorrectness.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Proofs.Executions.ProposalPropagation
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.HeightInvariant
public import GoldilocksCorrectness.Proofs.Executions.FinalizedFromChain
public import GoldilocksCorrectness.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Proofs.Routines.Lemma19
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import GoldilocksCorrectness.Proofs.Routines.FGCaches
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeReach
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# The kit of the phase

The proofs of the statements of `Statements/Executions/PhaseKitStatements.lean`: an honest
Goldfish vote names a block on the chain of its voter's fork-choice root; the only slot-`s` block
an honest validator holds is the honest proposer's; every frame of a node state has a viable
head; a record lock at the justified height of a state in box 2 is on its justified block; the
counting hypotheses of a round from a committee majority in a set of validators; the `head_height_floor` values (the least chain-state height a viable block may have) are
ordered by delivery; and the restrictions of the round's members and of the chain invariant.

## The kit

- `CachesWitnessed C S`: the justified block and its height are those of the chain state of a
  block of the tree, some block of the tree has the chain-state height `h_max`, and some block of
  the tree on the finalized block's chain has a chain-state height at least `h_max − 1`; carried
  along every execution (`cachesWitnessed_of_exec`).


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_cast slotStart_eq supportCutoff_eq
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure chainStateOf_J_spec forIn_yield_inv
  lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (CachesWitnessed exists_viable_head_of_witnessed
  fg_on_attestation_witness_keeps fg_on_block_eq fg_on_block_witnessed h_max_le_floor_add_one
  head_height_floor_initial mem_fg_to_ac_tree)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed HeightCacheBounds)

open GoldilocksCorrectness.Proofs.Routines (ac_to_fg_head_mem get_anchor_mem_T)

open GoldilocksCorrectness.Proofs.Routines (WitnessedFrom on_attestation_witness_keeps
  on_block_witnessedFrom tick_block_unique tick_witnessedFrom witnessedFrom_of_frame
  witnessedFrom_refl witnessedFrom_trans)

open GoldilocksCorrectness.Proofs.Routines (fgState_initial_eq initial_eq wake_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_genesis_J chainStateOf_genesis_h
  fg_contest_spec fg_contest_true_of goldfish_fork_choice_eq head_height_floor_of_not_contested)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq mem_viable_tree_iff)

open GoldilocksCorrectness.Proofs.Routines (receive_witnessedFrom)

open GoldilocksCorrectness.Proofs.Routines (supportCutoff_mono)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (CountedVotes BoxTwo expireLocks
  lem66_chain_state_certified)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq voters_count_lt_of_committee_majority mem_voter_block_tree_iff
  fc_root_ancestorEq_get_anchor)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The restriction facts -/

omit [RootOrder] in
/-- A later round's members are among an earlier round's, and the validators honest at a later
time are among every round's. The proof; the audited statement is in
`Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `s'' ≤ s'''`: the two slots; `tAwakeEnd`: the time. -/
theorem roundMembers_mono (S : Setup V) (Sched : Schedule V) (s'' s''' tAwakeEnd : ℕ)
    (hMono : Sched.MonotoneCorruption) (h : s'' ≤ s''')
    (hEnd : supportCutoff S s''' ≤ tAwakeEnd) :
    roundMembers S Sched s''' ⊆ roundMembers S Sched s'' ∧
      Finset.univ \ Sched.adv (tAwakeEnd : Int) ⊆ roundMembers S Sched s''' := by
  have hle : supportCutoff S s'' ≤ supportCutoff S s''' := supportCutoff_mono S h
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · simp only [roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
    exact fun ha => hv (hMono _ _ (by exact_mod_cast hle) ha)
  · simp only [roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
    exact fun ha => hv (hMono _ _ (by exact_mod_cast hEnd) ha)

/-- `HonestChainExtends` restricts to a subset of the members. The proof; the audited statement
is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon' ⊆ Hon`: the two sets;
  `B`: the block; `s'`: the slot. -/
theorem honestChainExtends_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon Hon' : Finset V) (B : Block V) (s' : ℕ)
    (hSub : Hon' ⊆ Hon) (hInv : HonestChainExtends S Sched x Hon B s') :
    HonestChainExtends S Sched x Hon' B s' :=
  ⟨fun u hu => hInv.1 u (hSub hu), fun w hw => hInv.2.1 w (hSub hw),
    fun v hv => hInv.2.2 v (hSub hv)⟩

/-- The chain invariant restricts to a subset of the members. The proof; the audited statement
is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon' ⊆ Hon`: the two sets;
  `𝓒`: the family; `s'`: the slot. -/
theorem chainInvFor_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon Hon' : Finset V) (𝓒 : Block V → Prop) (s' : ℕ)
    (hSub : Hon' ⊆ Hon) (hInv : ChainInvFor S Sched x Hon 𝓒 s') :
    ChainInvFor S Sched x Hon' 𝓒 s' :=
  fun C hC => honestChainExtends_mono S Sched x Hon Hon' C s' hSub (hInv C hC)

/-! ## The counting hypotheses -/

/-- The counting hypotheses of a round from a committee majority in `Hon`. The proof; the audited
statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `t`: the time;
  `Hon`: the validators; `v`: the validator whose state is read. -/
theorem counting_of_committee_majority (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t : ℕ) (Hon : Finset V) (v : V)
    (hMaj : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card) :
    (S.P.committee s).card ≤ 2 * (S.P.committee s ∩ Hon).card ∧
    voters_count ((stateBefore x t v).A.pool s) < 2 * (S.P.committee s ∩ Hon).card ∧
    (∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x t v).A (fg_to_ac (stateBefore x t v).S) (s + 1)
        votes support_votes →
      voters_count votes < 2 * (S.P.committee s ∩ Hon).card) := by
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left (s₁ := S.P.committee s) (s₂ := Hon))
  have hMaj' : (S.P.committee s \ (S.P.committee s ∩ Hon)).card <
      (S.P.committee s ∩ Hon).card := by omega
  refine ⟨Nat.le_of_lt hMaj, ?_, ?_⟩
  · exact voters_count_lt_of_committee_majority (pool_committee_of_stateBefore S Sched x t v s)
      hMaj'
  · intro votes support_votes hC
    exact voters_count_lt_of_committee_majority
      (countedVotes_committee S Sched x t s v votes support_votes hC) hMaj'

/-! ## The committee majority and the members of a slot -/

omit [RootOrder] in
/-- From committee sleepiness at slot `s + 1`, more than half of the committee of slot `s` is
among the validators honest at the support cutoff of slot `s + 1`. The proof; the audited
statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which committee sleepiness
  holds; `s`: the slot. -/
theorem committee_majority_of_committeeSleepiness (S : Setup V) (Sched : Schedule V)
    (anchor s : ℕ) (hSleepK : CommitteeSleepiness S Sched anchor)
    (hs : anchor ≤ slotStart S (s + 1)) :
    (S.P.committee s).card < 2 * (S.P.committee s ∩ roundMembers S Sched (s + 1)).card := by
  have hK := hSleepK (s + 1) (by omega) hs
  rw [Nat.add_sub_cancel, Finset.inter_comm] at hK
  have hsplit := Finset.card_sdiff_add_card_inter (S.P.committee s) (honestActiveAt S Sched s)
  have hsub : S.P.committee s ∩ honestActiveAt S Sched s ⊆
      S.P.committee s ∩ roundMembers S Sched (s + 1) := by
    refine Finset.inter_subset_inter (subset_refl _) (fun v hv => ?_)
    simp only [honestActiveAt, roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and]
      at hv ⊢
    exact hv.2
  have hle := Finset.card_le_card hsub
  omega

omit [RootOrder] in
/-- In the phase, the validators honest at the support cutoff of slot `s + 1` are honest active
at slot `s`, and those honest at the support cutoff of slot `s + 2` are among them. The proof;
the audited statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `tGAT`, `tAwakeEnd`: the ends of the interval in which
  every honest validator is awake; `s`: the slot. -/
theorem roundMembers_subset_honestActiveAt (S : Setup V) (Sched : Schedule V)
    (tGAT tAwakeEnd s : ℕ)
    (hMono : Sched.MonotoneCorruption)
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hsw : tGAT ≤ dutyWindowStart S s)
    (hEnd : supportCutoff S (s + 1) ≤ tAwakeEnd) :
    roundMembers S Sched (s + 1) ⊆ honestActiveAt S Sched s ∧
    roundMembers S Sched (s + 2) ⊆ roundMembers S Sched (s + 1) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · simp only [roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
    simp only [honestActiveAt, activeAt, Finset.mem_sdiff]
    refine ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => ?_), hv⟩
    exact hAwake t (by omega) (by omega) v
      (fun ha => hv (hMono _ _ (by exact_mod_cast h2) ha))
  · have hmul : 4 * Δ S * (s + 1) ≤ 4 * Δ S * (s + 2) := Nat.mul_le_mul_left _ (by omega)
    have hle : supportCutoff S (s + 1) ≤ supportCutoff S (s + 2) := by
      rw [supportCutoff_eq, supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq,
        slotStart_eq]
      omega
    simp only [roundMembers, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
    exact fun ha => hv (hMono _ _ (by exact_mod_cast hle) ha)

/-! ## The only block of a slot -/

/-- The time of the configuration `stepBefore x t` is at most `t`.

The variables:
- `x`: the execution; `t`: the time. -/
theorem time_stepBefore_le {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)
    (t : ℕ) : x[stepBefore x t].time ≤ t := by
  classical
  unfold stepBefore
  split
  · rename_i h
    have := (time_of_lbl_tickAllAwake x (Nat.find_spec h)).1
    omega
  · have h0 : x[0].time = 0 := x.init.1
    omega

/-- The only slot-`s` block an honest validator holds is the honest proposer's. The proof; the
audited statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `s`: the slot;
  `t`: the time; `B`: the proposal; `B₁`: the held block; `p`: the proposer; `w`: the holder. -/
theorem only_block_of_unforgeability (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (s t : ℕ) (B B₁ : Block V)
    (p w : V)
    (hp : HonestThroughTime Sched (t : Int) p) (hps : S.P.proposer s = p)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hB₁ : B₁ ∈ (stateBefore x t w).S.T) (hslot : B₁.slot = s) :
    B₁ = B := by
  obtain ⟨iB, hlB, hmB⟩ := hPropose
  -- the slot is positive: a tick runs at a time at least `1`
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h1 := (time_of_lbl_tickAllAwake x hlB).1
    rw [slotStart_eq, Nat.mul_zero] at h1
    omega
  have hg : B₁ ≠ Block.genesis := by
    rintro rfl
    exact hs0 hslot.symm
  -- `w`'s own relay of `B₁`, and the proposer of `B₁`
  obtain ⟨i, hi, hsendw, -, -⟩ := tree_block_relayed x (k := stepBefore x t) hB₁ hg
  have hprop := ((lem11_node_invariant S Sched x (stepBefore x t) w).1.2.2.1.2 B₁ hB₁ hg).2.2.1
  rw [hslot, hps] at hprop
  have hauth : author (NamedObject.block B₁) = some p := hprop
  have hti : x[i + 1].time ≤ t :=
    le_trans (time_mono x (by omega : i + 1 ≤ stepBefore x t)) (time_stepBefore_le x t)
  have hH : HonestThrough x (i + 1) p := fun t' ht' => hp t' (le_trans ht' (by exact_mod_cast hti))
  have hm := hU.unforgeable (i + 1) _ p (mem_sent_of_mem_sub x hsendw) hauth hH
  -- `p`'s own tick sent `B₁`, at the start of slot `s`
  obtain ⟨k', -, t'', hl', hdiff⟩ := authored_from_own_tick x hU hauth hm hH
  obtain ⟨-, n1, sent1, hrun1, hmem1⟩ := tick_send_of_honestSendAt hl' hdiff
  obtain ⟨-, ht'', -, H, votes, sv, -, -, -, hB1eq⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n1 _ sent1 B₁
      hrun1 hmem1
  have hsl : S.C.slot ((t'' : ℕ) : Int) = s := by
    rw [← hslot, hB1eq]
    rfl
  have htt : t'' = slotStart S s := by
    have h := slotStart_cast S s
    rw [hsl] at ht''
    exact_mod_cast ht''.trans h.symm
  subst htt
  have hk : k' = iB := (stepBefore_eq_of_lbl x hl').symm.trans (stepBefore_eq_of_lbl x hlB)
  subst hk
  obtain ⟨-, n2, sent2, hrun2, hmem2, -, hall⟩ := tick_send_step_outcome hlB hmB
  exact tick_block_unique S.C S.P S.X _ n2 _ sent2 B₁ B hrun2 (hall _ hdiff) hmem2

/-! ## The witnessed caches -/

section Witnessed

section Execution

open Framework.StsMultisetLog (AtomicStep Event TickAllAwakeWake tickAllAwakeUpdate_getElem_react
  tickAllAwakeUpdate_getElem_st_of_not_react applyNodeStepResult_getElem receive_getElem
  NodeStepResult View)
open GoldilocksCorrectness.Wiring (step_tick_iff step_wake_iff step_recv_iff)

/-- Every step of the wiring on one event, from a node state whose chain states of its tree are
the blocks' own, relates the node state to the step's state: a tick step is an answer of the
node's tick or keeps the state, a delivery runs the dispatch, a wake writes `awakeSince` only.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `e`: the event; `res`: the step result. -/
theorem reaction_witnessedFrom (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (NodeState V) (NamedObject V))
    (hstep : (protocol S).step p r view n e res) (hCS : ChainStatesComputed S.C n.S) :
    WitnessedFrom S.C n res.state := by
  cases e with
  | tick =>
      rcases (step_tick_iff S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
      · exact DREBPost.of_outcome (tick_witnessedFrom S.C S.P S.X n (r : Int) hCS) hok
      · exact witnessedFrom_refl S.C _
  | recv m =>
      rw [(step_recv_iff S p r view n m res).1 hstep]
      exact receive_witnessedFrom S.C S.P S.X n m.msg hCS
  | wake =>
      rw [(step_wake_iff S p r view n res).1 hstep, wake_eq]
      exact witnessedFrom_of_frame S.C rfl rfl rfl rfl rfl
  | custom ev => exact ev.elim

/-- Every step of the atomic semantics relates every validator's node state before the step to
its node state after. -/
theorem atomicStep_witnessedFrom {S : Setup V} {Sched : Schedule V}
    {a : AtomicAction V (NamedObject V) Empty}
    {c c' : Framework.StsMultisetLog.Config V (NamedObject V) (NodeState V)}
    (h : AtomicStep (protocol S) Sched a c c') (v : V)
    (hCS : ChainStatesComputed S.C c[v].st.S) :
    WitnessedFrom S.C c[v].st c'[v].st := by
  refine AtomicStep.elim (motive := fun _ d d' =>
      ChainStatesComputed S.C d[v].st.S → WitnessedFrom S.C d[v].st d'[v].st) h ?_ ?_ ?_ ?_ ?_
      hCS
  · intro d t w tk _ hw htk hCS'
    by_cases hv : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
    · rw [tickAllAwakeUpdate_getElem_react hv]
      have hwv : WitnessedFrom S.C d[v].st (w v).state ∧ (w v).state.S = d[v].st.S := by
        have hw' := hw v
        unfold TickAllAwakeWake at hw'
        split at hw'
        · rw [(step_wake_iff S _ _ _ _ _).1 hw', wake_eq]
          exact ⟨witnessedFrom_of_frame S.C rfl rfl rfl rfl rfl, rfl⟩
        · rw [hw']
          exact ⟨witnessedFrom_refl S.C _, rfl⟩
      show WitnessedFrom S.C d[v].st (tk v).state
      exact witnessedFrom_trans S.C hwv.1
        (reaction_witnessedFrom S _ _ _ _ _ _ (htk v hv) (by rw [hwv.2]; exact hCS'))
    · rw [tickAllAwakeUpdate_getElem_st_of_not_react hv]
      exact witnessedFrom_refl S.C _
  · intro d p m res _ hres hCS'
    rw [applyNodeStepResult_getElem]
    split
    · rename_i hp
      subst hp
      have hst : (Framework.StsMultisetLog.receive p m d)[p].st = d[p].st := by
        rw [receive_getElem, if_pos rfl]
      show WitnessedFrom S.C d[p].st res.state
      rw [hst] at hres
      exact reaction_witnessedFrom S _ _ _ _ _ _ hres hCS'
    · rw [receive_getElem, if_neg (by assumption)]
      exact witnessedFrom_refl S.C _
  · intro d p ev
    exact ev.elim
  · intro d p m _ _
    exact witnessedFrom_refl S.C _
  · intro d p m _ _
    exact witnessedFrom_refl S.C _

/-- At every step of every execution, every validator's FG state satisfies `CachesWitnessed`.
By induction on the step: the initial FG state does (the genesis block witnesses all three
clauses), and every step relates the node state before to the node state after, the chain
states of the tree before being the blocks' own (Lemma 11).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator. -/
theorem cachesWitnessed_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    CachesWitnessed S.C (x[i][v].st).S := by
  induction i with
  | zero =>
      obtain ⟨-, hn, -⟩ := x.init
      show CachesWitnessed S.C ((x.cfg 0)[v].st).S
      rw [hn v, show (protocol S).init v = initial S.C v from rfl, initial_eq, fgState_initial_eq]
      exact ⟨⟨Block.genesis, Finset.mem_singleton_self _, (chainStateOf_genesis_J S.C).1.symm,
          (chainStateOf_genesis_J S.C).2.symm⟩,
        ⟨Block.genesis, Finset.mem_singleton_self _, chainStateOf_genesis_h S.C⟩,
        ⟨Block.genesis, Finset.mem_singleton_self _, ancestorEq_refl _, Nat.zero_le _⟩⟩
  | succ i ih =>
      exact (atomicStep_witnessedFrom (x.step i) v
        (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.1).2 ih

/-- `cachesWitnessed_of_exec` before the time `t`. -/
theorem cachesWitnessed_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    CachesWitnessed S.C (stateBefore x t v).S :=
  cachesWitnessed_of_exec S Sched x (stepBefore x t) v

end Execution

end Witnessed

/-! ## Every frame has a viable head -/

/-- Every frame of a node state has a viable head. The proof; the audited statement is in
`Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the
  validator. -/
theorem frame_has_viable_head (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    ∃ W : Block V, W ∈ (fg_to_ac (stateBefore x t v).S).viable_heads := by
  have hInv := (lem11_node_invariant S Sched x (stepBefore x t) v).1
  exact exists_viable_head_of_witnessed S.C _ hInv.2.2.2.2.2.1
    (F_ancestorEq_J_of_stateBefore S Sched x t v)
    (lem57_justification_cache_and_record S Sched x (stepBefore x t) v).2.2.1
    (cachesWitnessed_of_stateBefore S Sched x t v)

/-! ## The locks in box 2 -/

/-- A record lock is the root of the justified block of the chain state of a block the validator
held at an earlier step, justified at the lock's height, which is at least `1`: the lock was
written by an attestation of the validator's tick, whose finality pair is its head's justification.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `k`: the step; `v`: the validator;
  `h`: the height; `T'`: the lock. -/
theorem lock_justified_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (k : ℕ) (v : V) (h : Height) (T' : BlockId)
    (hLock : (x[k][v].st).Λ.lock h = some T') :
    ∃ j < k, ∃ D ∈ (x[j][v].st).S.T, 1 ≤ h ∧ (chainStateOf S.C D).h_j = h ∧
      (chainStateOf S.C D).J.root = T' := by
  obtain ⟨c, hc, hcfp⟩ := ((recordConsistent_of_exec S Sched x k v).lockRec h T').1 hLock
  obtain ⟨j, t', a, hj, hl, -, -, hsent, -, hac, -⟩ := record_content_sent_step S Sched x v k c hc
  obtain ⟨-, n', sent, hrun, ha⟩ := tick_send_of_honestSendAt hl hsent
  obtain ⟨-, fi, source, hfi, -, hca, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  have hSeq := (tickInputState_frame x j t' v).1
  have hInv := (lem11_node_invariant S Sched x j v).1
  have hhead := ac_to_fg_head_mem S.C n'.A (tickInputState x j t' v).S _
    (by rw [hSeq]; exact hInv.2.2.2.1)
    (by rw [hSeq]; exact (lem57_justification_cache_and_record S Sched x j v).2.2.1)
    (by rw [hSeq]; exact F_ancestorEq_J_of_exec S Sched x j v) fi hfi
  rw [hSeq] at hhead hca
  have hσ := hInv.2.2.2.2.2.1 fi.head hhead.1
  rw [hσ] at hca
  rcases GoldilocksCorrectness.Proofs.Routines.create_attestation_cases _ _ _ _ _ _ _ with
    h0 | ⟨τ, fp', -, -, hfp', heq⟩
  · rw [h0] at hca
    cases hca
  · rw [heq] at hca
    have ha' := (Option.some.inj hca).symm
    subst ha'
    have hfp : fp' = some ⟨h, T'⟩ := by
      rw [← hcfp, ← hac]
      rfl
    obtain ⟨hq, hlt⟩ := hfp' _ hfp
    obtain ⟨hpair, hFj, -, -, -⟩ := GoldilocksCorrectness.Proofs.Routines.finality_pair_some hq
    injection hpair with hh hT
    refine ⟨j, hj, fi.head, hhead.1, ?_, hh.symm, hT.symm⟩
    rw [hh]
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hFj

/-- When `p` is in box 2 with the justified block `J₀`, every lock at `p`'s `h_max − 1` is on
`J₀`. The proof; the audited statement is in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `t`: the time;
  `v`: the validator whose record is read; `p`: the validator in box 2; `J₀`: its justified block;
  `T'`: the lock. -/
theorem lockBox_of_one_justification (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (t : ℕ) (v p : V)
    (J₀ : Block V) (T' : BlockId)
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (t : Int))
    (hBox : BoxTwo (stateBefore x t p).S J₀)
    (hLock : (stateBefore x t v).Λ.lock ((stateBefore x t p).S.h_max - 1) = some T') :
    T' = J₀.root := by
  obtain ⟨hbox, -, hJ⟩ := hBox
  rw [hbox, Nat.add_sub_cancel] at hLock
  obtain ⟨j, hj, D', hD'T, h1, hD'j, hD'J⟩ := lock_justified_of_exec S Sched x _ v _ T' hLock
  obtain ⟨⟨D, hDT, hDJ, hDj⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t p
  have hcert' := ((lem66_chain_state_certified S.C D').1 (hD'j ▸ h1)).1
  have hcert := ((lem66_chain_state_certified S.C D).1 (hDj ▸ h1)).1
  rw [hD'j] at hcert'
  rw [← hDj] at hcert
  have hAdv' : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[j].time : Int) (x[stepBefore x t].time : Int)) := by
    have hk := time_stepBefore_le x t
    have hjk := time_mono x (Nat.le_of_lt hj)
    exact adversaryFewerThanThirdUntil_of_le (max_le (by omega) (by omega)) hAdv
  have hroot := lem76_honest_one_justification S Sched x hU j (stepBefore x t) v p hAdv' D' D
    hD'T hDT _ _ _ hcert' hcert
  rw [← hD'J, hroot, ← hDJ, hJ]

/-! ## The `head_height_floor` values ordered by delivery -/

/-- A validator awake and honest for one delay after `t`, whose finalized block is an ancestor of
`p`'s fork-choice root before `t`, has a `head_height_floor` value at least the one at `p`. The proof; the audited statement is
in `Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `t`: the time `p`'s state is read before; `p`, `w`: the two
  validators.

Roots name blocks until `t + Δ S`: the proof compares blocks `w` holds before `t + Δ S` with
blocks `p` holds before `t`. -/
theorem floor_le_of_delivery (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST t : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) ((t + Δ S : ℕ) : Int))
    (hGST : GST ≤ t)
    (hp : p ∉ Sched.adv (t : Int))
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S → w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hF : (stateBefore x (t + Δ S) w).S.F.AncestorEq (get_fc_root (stateBefore x t p).S)) :
    head_height_floor (stateBefore x t p).S ≤ head_height_floor (stateBefore x (t + Δ S) w).S := by
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · subst ht0
    have h0 : (stateBefore x 0 p).S = FGState.initial := by
      unfold stateBefore
      rw [stepBefore_zero]
      obtain ⟨-, hn, -⟩ := x.init
      show ((x.cfg 0)[p].st).S = _
      rw [hn p, show (protocol S).init p = initial S.C p from rfl, initial_eq]
    rw [h0, head_height_floor_initial]
    exact Nat.zero_le _
  have hΔ := one_le_Δ S
  set kp := stepBefore x t with hkp
  set kw := stepBefore x (t + Δ S) with hkw
  have hkpt : x[kp].time ≤ t := time_stepBefore_le x t
  have hkwt : x[kw].time ≤ t + Δ S := time_stepBefore_le x (t + Δ S)
  have hpk : p ∉ Sched.adv (x[kp].time : Int) := fun h =>
    hp (hMono _ _ (by exact_mod_cast hkpt) h)
  have hwk : w ∉ Sched.adv (x[kw].time : Int) := fun h =>
    (hw (t + Δ S) (by omega) le_rfl).2 (hMono _ _ (by exact_mod_cast hkwt) h)
  have hThird : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[kw].time : Int) (x[kp].time : Int)) :=
    adversaryFewerThanThirdUntil_of_le (max_le (by omega) (by omega)) hAdv
  have hThird' : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[kp].time : Int) (x[kw].time : Int)) :=
    adversaryFewerThanThirdUntil_of_le (max_le (by omega) (by omega)) hAdv
  -- the invariants of the two states
  have hInvP := (lem11_node_invariant S Sched x kp p).1
  have hInvW := (lem11_node_invariant S Sched x kw w).1
  have hCSp : ChainStatesComputed S.C (stateBefore x t p).S := hInvP.2.2.2.2.2.1
  have hCSw : ChainStatesComputed S.C (stateBefore x (t + Δ S) w).S := hInvW.2.2.2.2.2.1
  have hCacheW : HeightCacheBounds (stateBefore x (t + Δ S) w).S :=
    (lem46_finality_caches S Sched x kw w).2
  -- every block `p` holds before `t` that is compatible with `w`'s finalized block reaches `w`
  have hreach : ∀ Y ∈ (stateBefore x t p).S.T,
      (stateBefore x (t + Δ S) w).S.F.compatible Y = true →
      Y ∈ (stateBefore x (t + Δ S) w).S.T := fun Y hY hc =>
    mem_T_before_add_delay_of_held hDiv hMono hSync hCatch hRoots hParent
      (t₁ := t) (t := t) ht1 le_rfl hGST hp hY hw hc
  -- step A: `p`'s `h_max` is at most `w`'s
  obtain ⟨⟨Dp, hDpT, hDpJ, hDpj⟩, ⟨X, hXT, hXh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t p
  obtain ⟨⟨Dw, hDwT, hDwJ, hDwj⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x (t + Δ S) w
  have hm : (stateBefore x t p).S.h_max ≤ (stateBefore x (t + Δ S) w).S.h_max := by
    by_contra hcon
    have hcon' : (stateBefore x (t + Δ S) w).S.h_max < (chainStateOf S.C X).h := by
      rw [hXh]
      exact Nat.lt_of_not_le hcon
    obtain ⟨Bw, hBw, hFw⟩ := finalizedFromChain_of_exec S Sched x kw w
    have hBwh : (chainStateOf S.C Bw).h ≤ (stateBefore x (t + Δ S) w).S.h_max := by
      rw [← hCSw Bw hBw]
      exact hCacheW Bw hBw
    have h47 := (lem47_chain_state_heights S.C Bw Bw).1
    have hlt : (chainStateOf S.C Bw).h_F < (chainStateOf S.C X).h :=
      lt_of_le_of_lt h47.2.2 (lt_trans h47.2.1 (lt_of_le_of_lt hBwh hcon'))
    have hFX := lem68_honest_past_finalized S Sched x hU hRoots kw kp w p Bw X hThird hwk hpk
      hBw hXT hlt (max_le hkwt (by omega))
    have hc : (stateBefore x (t + Δ S) w).S.F.compatible X = true := by
      show (x[kw][w].st).S.F.compatible X = true
      rw [hFw]
      exact (compatible_iff _ _).2 (Or.inl hFX)
    have hXw := hreach X hXT hc
    have h1 := hCacheW X hXw
    rw [hCSw X hXw] at h1
    have h2 : (chainStateOf S.C X).h ≤ (stateBefore x (t + Δ S) w).S.h_max := h1
    exact absurd h2 (Nat.not_le.2 hcon')
  have hfw := h_max_le_floor_add_one (stateBefore x (t + Δ S) w).S
  have key1 : ∀ a b c : ℕ, a ≤ b → b ≤ c + 1 → a - 1 ≤ c := by intros; omega
  have key2 : ∀ a b c : ℕ, a < b → b ≤ c + 1 → a ≤ c := by intros; omega
  have key3 : ∀ a m hj bj bh hm : ℕ, a = m - 1 → a ≤ hj → hj = bj → bj < bh → bh ≤ hm →
      hm = m → hj = m - 1 := by intros; omega
  have key4 : ∀ m hj hm : ℕ, hm = m → hj = m - 1 → 1 ≤ m - 1 → hm = hj + 1 := by intros; omega
  -- step B: by `p`'s box
  cases hcp : fg_contest (stateBefore x t p).S with
  | false =>
      have hfloor : head_height_floor (stateBefore x t p).S =
          (stateBefore x t p).S.h_max - 1 := by
        exact head_height_floor_of_not_contested _ hcp
      rw [hfloor]
      exact key1 _ _ _ hm hfw
  | true =>
      obtain ⟨hbox, hroot, hfloor⟩ :=
        GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree _ hcp
      rw [hfloor]
      -- the block that makes `p` contested
      obtain ⟨-, B', hB'T, hFB', hB'h, hJB'⟩ := fg_contest_spec _ hcp
      rw [hroot] at hF
      have hFwB' : (stateBefore x (t + Δ S) w).S.F.AncestorEq B' := ancestorEq_trans hF hFB'
      have hB'w := hreach B' hB'T ((compatible_iff _ _).2 (Or.inl hFwB'))
      rcases Nat.lt_or_ge (stateBefore x t p).S.h_max
          (stateBefore x (t + Δ S) w).S.h_max with hlt | hge
      · exact key2 _ _ _ hlt hfw
      have heq : (stateBefore x (t + Δ S) w).S.h_max = (stateBefore x t p).S.h_max :=
        le_antisymm hge hm
      -- `p`'s justified block is justified at `h_max − 1 ≥ 1`
      have hjp : (chainStateOf S.C Dp).h_j = (stateBefore x t p).S.h_max - 1 := by
        rw [← hDpj, hbox, Nat.add_sub_cancel]
      have hj1 : 1 ≤ (chainStateOf S.C Dp).h_j := by
        rcases Nat.eq_zero_or_pos (chainStateOf S.C Dp).h_j with h0 | hpos
        · exfalso
          have hg := (chainStateOf_J_spec S.C Dp).2.1 h0
          rw [← hDpJ] at hg
          rw [hg] at hJB'
          exact hJB' (genesis_ancestorEq _)
        · exact hpos
      -- `Dp` reaches `w`, so `w`'s justification height is at least `h_max − 1`
      have hFpJ := F_ancestorEq_J_of_stateBefore S Sched x t p
      have hJDp := (chainStateOf_J_spec S.C Dp).1
      rw [← hDpJ] at hJDp
      have hFwDp : (stateBefore x (t + Δ S) w).S.F.AncestorEq Dp :=
        ancestorEq_trans hF (ancestorEq_trans hFpJ hJDp)
      have hDpw := hreach Dp hDpT ((compatible_iff _ _).2 (Or.inl hFwDp))
      have hjw1 := h_j_of_mem_T_of_stateBefore S Sched x (t + Δ S) w Dp hDpw hFwDp
      rw [hCSw Dp hDpw] at hjw1
      -- and at most `h_max − 1`
      have hDwh := hCacheW Dw hDwT
      rw [hCSw Dw hDwT] at hDwh
      have h47w := (lem47_chain_state_heights S.C Dw Dw).1.2.1
      have hjw : (stateBefore x (t + Δ S) w).S.h_j = (stateBefore x t p).S.h_max - 1 :=
        key3 _ _ _ _ _ _ hjp hjw1 hDwj h47w hDwh heq
      -- the two justified blocks are one block
      have hcertP := ((lem66_chain_state_certified S.C Dp).1 hj1).1
      have hjj : (chainStateOf S.C Dw).h_j = (chainStateOf S.C Dp).h_j :=
        hDwj.symm.trans (hjw.trans hjp.symm)
      have hj1w : 1 ≤ (chainStateOf S.C Dw).h_j := hjj ▸ hj1
      have hcertW := ((lem66_chain_state_certified S.C Dw).1 hj1w).1
      rw [hjj] at hcertW
      have hroots := lem76_honest_one_justification S Sched x hU kw kp w p hThird Dw Dp hDwT hDpT
        _ _ _ hcertW hcertP
      have hJwT := (lem57_justification_cache_and_record S Sched x kw w).2.2.1
      have hJpT := (lem57_justification_cache_and_record S Sched x kp p).2.2.1
      have hJJ : (stateBefore x (t + Δ S) w).S.J = (stateBefore x t p).S.J := by
        rw [hDwJ, hDpJ]
        refine hRoots _ _ ⟨kw, w, hwk, hkwt, ?_⟩ ⟨kp, p, hpk, by omega, ?_⟩ hroots
        · rw [← hDwJ]
          exact hJwT
        · rw [← hDpJ]
          exact hJpT
      -- `w` is contested by `B'`
      have hcw : fg_contest (stateBefore x (t + Δ S) w).S = true := by
        refine fg_contest_true_of _ B' (key4 _ _ _ heq hjw (hjp ▸ hj1)) hB'w hFwB' ?_ ?_
        · show ((stateBefore x (t + Δ S) w).S.σ B').h = _
          rw [hCSw B' hB'w, heq, ← hCSp B' hB'T]
          exact hB'h
        · rw [hJJ]
          exact hJB'
      obtain ⟨-, -, hfloorw⟩ :=
        GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree _ hcw
      rw [hfloorw, heq]

/-! ## An honest vote extends its voter's root -/

/-- An honest Goldfish vote names a block its voter holds, on the chain of the voter's own
fork-choice root. The proof; the audited statement is in
`Statements/Executions/PhaseKitStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the voter;
  `vote`: the vote. -/
theorem vote_extends_own_root (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' : ℕ) (u : V) (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T, vote.head = H_u.root ∧
      (get_fc_root (stateBefore x (voteTime S s') u).S).AncestorEq H_u := by
  obtain ⟨i, hl, hm⟩ := hSend
  have hi : stepBefore x (voteTime S s') = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
  have hS : (tickInputState x i (voteTime S s') u).S = (stateBefore x (voteTime S s') u).S := by
    rw [(tickInputState_frame x i _ u).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, -, -, -, A', votes, support_votes, vbt, H_u, -, -, hvbt, hWalk, hhead, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  rw [hS] at hvbt hWalk
  refine ⟨H_u, ?_, hhead, ?_⟩
  · rcases GoldilocksCorrectness.Proofs.Routines.ghost_mem_tree_or_eq ((goldfish_fork_choice_eq ..).symm.trans hWalk) with h | h
    · rw [h]
      exact get_anchor_mem_T _ _ _
        (lem11_node_invariant S Sched x (stepBefore x (voteTime S s')) u).1.2.2.2.1
        (lem57_justification_cache_and_record S Sched x (stepBefore x (voteTime S s')) u).2.2.1
    · have h1 := ((mem_viable_tree_iff _ _ _).1 h).1
      have h2 := ((mem_voter_block_tree_iff S.C _ _ _ vbt hvbt H_u).1 h1).1
      exact ((mem_fg_to_ac_tree _ _).1 h2).1
  · have hAH : (get_anchor A' (fg_to_ac (stateBefore x (voteTime S s') u).S)
        ((voteTime S s' : ℕ) : Int)).AncestorEq H_u := by
      rcases GoldilocksCorrectness.Proofs.Routines.ghost_spec ((goldfish_fork_choice_eq ..).symm.trans hWalk) with hH | ⟨hAH, -⟩
      · rw [hH]
        exact ancestorEq_refl _
      · exact hAH
    exact ancestorEq_trans
      (by rw [← fc_root_eq]; exact fc_root_ancestorEq_get_anchor A' (fg_to_ac (stateBefore x (voteTime S s') u).S) _)
        hAH

end GoldilocksCorrectness.Proofs.Executions
