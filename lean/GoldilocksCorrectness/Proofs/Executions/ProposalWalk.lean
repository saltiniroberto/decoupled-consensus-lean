module
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.WalkStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd

@[expose] public section

/-! Write
`t₁ := slotStart S (s + 1)`, the time of `p`'s proposal; `A_p`, `Φ_p` for the AC state and the
frame of `p`'s state before `t₁`; `anchor_p := get_anchor A_p Φ_p t₁` and
`tree_p := viable_tree Φ_p Φ_p.tree`, the start and the tree of `p`'s walk.

`proposal_parent_extends_majority_block` states what steps 0, 1, 3, 6 and 7 of `lem20`'s proof
(`GoldilocksCorrectness/Proofs/Executions/Lemma20.lean`) derive at `p`: `B`'s parent is `X` or a
descendant of `X`, `B` is a non-genesis block of slot `s + 1` whose parent link names that parent,
and that parent, where `p`'s walk ended, is in `tree_p` or is `anchor_p`. The steps are repeated
here, not called (decision G0F-3 (a) of the plan): `lem20`'s proof does not export them.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor
  ProposalCountedVotes)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff
  fc_root_ancestorEq_get_anchor ancestorEq_of_parent? proposalCountedVotes_of_lists
  ghost_mem_tree_or_eq)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The honest proposal of slot `s + 1` extends the block `X` the slot-`s` majority extends. In an
execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest at the
start of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at the vote
time of slot `s`, and holds `H u`, a block that is `X` or a descendant of `X`, in its tree then;
the validators with a slot-`s` vote in `p`'s pool before `t₁` are fewer than twice `Hs`; `p` is
awake and honest at every time from the
vote time of slot `s` to its support cutoff; the step `i` is the tick of every awake validator at
the start `t₁` of slot `s + 1`, at which `p` put the block `B` on the wire; and on `p`'s node state
before `t₁`, some block of its frame's tree that is `X` or a descendant of `X` is a viable head, and
its anchor at `t₁` is `X` or an ancestor of `X` — then `X` is `B`'s parent or an ancestor of it, `B`
is a block of slot `s + 1` other than the genesis block, its parent link names its parent, and its
parent is in `p`'s viable tree or is `p`'s anchor at `t₁`.



The hypotheses are those of `lem20_goldfish_vote_names_honest_proposal` that concern `p`, with
`hPropose` given by its step `i` (`hl`, `hsent`); the proof repeats `lem20`'s steps 0, 1, 3, 6 and
7, then reads the end of `p`'s walk off `ghost_mem_tree_or_eq`. the committee
majority gives it through the admission invariant. The walk is Lemma 2's, with `Sup := Hs`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes; `i`: the step
  of `p`'s tick at the start of slot `s + 1`;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`; `p`: the proposer of slot `s + 1`.

Read aloud: the honest proposal of slot `s + 1` is a non-genesis block of that slot whose parent
is `X` or a descendant of `X`, and that parent, where `p`'s walk ended, is a block of `p`'s viable
tree or `p`'s anchor.

Roots name blocks until `supportCutoff S s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to. -/
theorem proposal_parent_extends_majority_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s i : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (slotStart S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    -- the validators with a slot-`s` vote in `p`'s pool before `t₁` are fewer than twice `Hs`
    (hVotersP : ∀ votes_p support_p : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s votes_p support_p →
      voters_count votes_p < 2 * Hs.card)
    -- the proposer `p`
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, and put `B` on the wire
    (hl : x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    -- the finality-gadget condition at `p`, on its state before `slotStart S (s + 1)`
    (hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X) :
    X.AncestorEq B.parent ∧ B.slot = s + 1 ∧ B ≠ Block.genesis ∧
      B.parent? = some B.parent ∧
      (B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
          (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree ∨
        B.parent = get_anchor (stateBefore x (slotStart S (s + 1)) p).A
          (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
          ((slotStart S (s + 1) : ℕ) : Int)) := by
  have hF2p : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (slotStart S (s + 1)) p
  -- step 0 of `lem20`: the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hc₀ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hslot₁ : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (le_refl _) (by omega)
  -- step 1 of `lem20`: `p`'s run and proposal, at the step `i`
  have hi : stepBefore x (slotStart S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  have hti : x[i].time + 1 = slotStart S (s + 1) := (time_of_lbl_tickAllAwake x hl).1
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := tick_send_of_honestSendAt hl hsent
  have hRootsΦp : RootsNameBlocksIn (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ p
  have hAp : (tickInputState x i (slotStart S (s + 1)) p).A =
      (stateBefore x (slotStart S (s + 1)) p).A := by
    rw [(tickInputState_frame x i _ p).2.1]
    unfold stateBefore
    rw [hi]
  have hSp : (tickInputState x i (slotStart S (s + 1)) p).S =
      (stateBefore x (slotStart S (s + 1)) p).S := by
    rw [(tickInputState_frame x i _ p).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, -, -, Hp, votes_pl, support_pl, hvl, hsl, hWalkP, hBdef⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hB₁
  rw [hslot₁, Nat.add_sub_cancel, hAp] at hvl
  rw [hAp, hSp] at hsl
  rw [hslot₁, Nat.add_sub_cancel, hAp, hSp] at hWalkP
  rw [hslot₁] at hBdef
  have hPCV : ProposalCountedVotes (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s votes_pl.toFinset
      support_pl.toFinset :=
    proposalCountedVotes_of_lists _ _ s votes_pl support_pl hvl hsl
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  have hBslot : B.slot = s + 1 := by rw [hBdef]; rfl
  have hBne : B ≠ Block.genesis := by rw [hBdef]; exact fun h => by cases h
  have hBpar? : B.parent? = some Hp := by rw [hBdef]; rfl
  -- step 3 of `lem20`: the delivered votes, at `p` before `t₁`
  have hHeldP : ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s (H u) u :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_until S Sched x GST s
      (slotStart S (s + 1)) Hs H p hDiv hMono hSync hCatch hRoots hParent hOwner hGST
      (by omega)
      (fun u hu => ⟨(hHs u hu).1, (hHs u hu).2.1,
        (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩) hp
      (fun u hu => ancestorEq_trans hF2p (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _)
        (ancestorEq_trans hApX (hHs u hu).2.2.2.2)))
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty :=
    Finset.card_pos.1 (by
      have := hVotersP votes_pl.toFinset support_pl.toFinset hPCV
      omega)
  -- step 6 of `lem20`: `p`'s start
  have hHu₀T : H u₀ ∈ (stateBefore x (slotStart S (s + 1)) p).S.T :=
    ((mem_fg_to_ac_tree _ _).1 (hHeldP u₀ hu₀).2.2.1).1
  have hStartP : StartsTowards (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) ((slotStart S (s + 1) : ℕ) : Int)) X
      (viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) := by
    obtain ⟨W, hW, hWv, hXW⟩ := hF3p
    refine GoldilocksCorrectness.Statements.Routines.lem7_startsTowards_of_compatible _ _ _ X W
      ((compatible_iff _ _).2 (Or.inl hApX)) (fc_root_ancestorEq_get_anchor _ _ _) ?_ ⟨hW, hWv⟩
      hXW
    intro P hAP _ hPX
    have hPH : P.AncestorEq (H u₀) := ancestorEq_trans hPX (hHs u₀ hu₀).2.2.2.2
    have hPT : P ∈ (stateBefore x (slotStart S (s + 1)) p).S.T :=
      ancestors_mem_T_of_exec S Sched x _ p _ P hHu₀T hPH
    have hFP : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq P :=
      ancestorEq_trans hF2p (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hAP)
    exact (mem_fg_to_ac_tree _ _).2 ⟨hPT, hFP⟩
  -- step 7 of `lem20`: `p`'s fork choice, so `X` is `B`'s parent or an ancestor of it
  have hSupportP : support_pl.toFinset ⊆ votes_pl.toFinset := by
    intro vote' hv
    rw [hPCV.1]
    exact ((hPCV.2 vote').1 hv).1
  have hVotesP : ∀ u ∈ Hs, VotesOnceFor (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      votes_pl.toFinset support_pl.toFinset s X u := by
    intro u hu
    obtain ⟨hpool, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeldP u hu
    refine ⟨GoldfishVote.mk u s (H u).root, (hPCV.2 _).2 ⟨hpool, y, hy⟩, rfl, rfl,
      ⟨H u, hHΦ, rfl, (hHs u hu).2.2.2.2⟩, ?_⟩
    intro vote' hv' hi'
    rw [hPCV.1] at hv'
    exact huniq vote' hv' hi'
  have hXH : X.AncestorEq Hp :=
    GoldilocksCorrectness.Statements.Routines.lem2_goldfish_fork_choice_extends_majority_block
      S.C _ _ votes_pl.toFinset support_pl.toFinset s _ X Hp _ Hs hStartP hRootsΦp hSupportP
      hVotesP (hVotersP votes_pl.toFinset support_pl.toFinset hPCV) hWalkP
  -- the end of `p`'s walk: `goldfish_fork_choice` is `ghost` by definition (trap T17)
  have hEnd := ghost_mem_tree_or_eq ((goldfish_fork_choice_eq ..).symm.trans hWalkP)
  rw [hBpar]
  exact ⟨hXH, hBslot, hBne, hBpar?, hEnd.symm⟩

end GoldilocksCorrectness.Proofs.Executions
