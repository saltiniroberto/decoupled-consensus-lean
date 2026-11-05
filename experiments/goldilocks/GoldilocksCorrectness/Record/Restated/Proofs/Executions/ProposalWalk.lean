module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.LockStatementsForkChoice
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.TickFrameForkChoice
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Statements.Routines.WalkEndStatements
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.WalkStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ProposalWalk, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/ProposalWalk.lean` over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the honest proposal of slot `s + 1`
extends the block the slot-`s` majority extends. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ProposalCountedVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff ancestorEq_of_parent?
  ghost_mem_tree_or_eq)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- The honest proposal of slot `s + 1` extends the block `X` the slot-`s` majority extends. In an
execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, outside the adversary set at
`p`'s tick to the start of slot `s + 1`, active through the sync delay after Lemma 12's read time,
put its slot-`s` vote for `H u` on the wire at its tick at the vote
time of slot `s`, and holds `H u`, a block that is `X` or a descendant of `X`, in its tree then;
the validators with a slot-`s` vote in `p`'s pool before `t₁` are fewer than twice `Hs`; `p` is
ticks to the support cutoff of slot `s`
and is active at every step from Lemma 12's read time up to that tick; the step `i` is the tick of every awake validator at
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes; `i`: the step
  of `p`'s tick at the start of slot `s + 1`;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`; `p`: the proposer of slot `s + 1`.

Read aloud: the honest proposal of slot `s + 1` is a non-genesis block of that slot whose parent
is `X` or a descendant of `X`, and that parent, where `p`'s walk ended, is a block of `p`'s viable
tree or `p`'s anchor.

Roots name blocks until the real time of `p`'s own tick to `M.supportCutoff S.C s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to. -/
theorem proposal_parent_extends_majority_block (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s i : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `p`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep p (M.slotStart S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ X.AncestorEq (H u))
    -- the validators with a slot-`s` vote in `p`'s pool before `t₁` are fewer than twice `Hs`
    (hVotersP : ∀ votes_p support_p : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput p (M.slotStart S.C (s + 1))) s votes_p support_p →
      M.voters_count votes_p < 2 * Hs.card)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer `p` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` up to `kR`
    (hp : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j)
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, and put `B` on the wire
    (hl : x.lbl i = Event.tick p (M.slotStart S.C (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    -- the finality-gadget condition at `p`, on its state before `slotStart S (s + 1)`
    (hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
      ((M.slotStart S.C (s + 1) : ℕ) : Int)).AncestorEq X) :
    X.AncestorEq B.parent ∧ B.slot = s + 1 ∧ B ≠ Block.genesis ∧
      B.parent? = some B.parent ∧
      (B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1))))
          (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree ∨
        B.parent = M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1)))
          ((M.slotStart S.C (s + 1) : ℕ) : Int)) := by
  -- step 0 of `lem20`: the times
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc₀ : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  -- the slot of `t₁`, read by the spec's clock (the model's slot of a natural-number time is the
  -- spec's, `U`)
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _) (by omega)
  -- step 1 of `lem20`: `p`'s run and proposal, from the state its tick at the step `i` starts from (Lemma 19 over
  -- the record, from the tick's input state, which satisfies the node invariant: `p` is active at its tick)
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  have hpi : p ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hti : x.tickInput p (M.slotStart S.C (s + 1)) = x.st i p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hRootsΦp : RootsNameBlocksIn (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree := by
    rw [hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E i p
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x R E i p hpi).1
  have hF2p : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E i p
  obtain ⟨-, -, -, -, Hp, votes_pl, support_pl, -, -, hWalkP, hBdef⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hInv hB₁
  rw [hslot₁, Nat.add_sub_cancel] at hWalkP
  rw [hslot₁] at hBdef
  -- the walk counts `p`'s slot-`s` votes and those that resolve (`ProposalCountedVotes`)
  obtain ⟨votes_p, support_p, hPCV, hW⟩ := hWalkP
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  have hBslot : B.slot = s + 1 := by rw [hBdef]; rfl
  have hBne : B ≠ Block.genesis := by rw [hBdef]; exact fun h => by cases h
  have hBpar? : B.parent? = some Hp := by rw [hBdef]; rfl
  -- step 3 of `lem20`: the delivered votes, at `p`'s tick input (Lemma 12's step form at `p`'s tick `i`)
  have hHeldP : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput p (M.slotStart S.C (s + 1))) s (H u) u :=
    (lem12_honest_vote_delivered_until_of_steps M F U) S A x R GST s (M.slotStart S.C (s + 1)) Hs H p
      E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST (by omega) i hl
      (fun u hu => ⟨(hHs u hu).1, (tickStep_eq_of_lbl M) x E hl ▸ (hHs u hu).2.1, (hHs u hu).2.2.1,
        (hHs u hu).2.2.2.1⟩)
      hHold hp
      (fun u hu => ancestorEq_trans hF2p (ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _)
        (ancestorEq_trans hApX (hHs u hu).2.2.2.2)))
  have hVotersP' : M.voters_count votes_p < 2 * Hs.card := hVotersP votes_p support_p hPCV
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  -- step 6 of `lem20`: `p`'s start
  have hHu₀T : H u₀ ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree :=
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (hHeldP u₀ hu₀).2.2.1).1
  have hStartP : StartsTowards (M.get_anchor (x.tickInput p (M.slotStart S.C (s + 1))) ((M.slotStart S.C (s + 1) : ℕ) : Int)) X
      (M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).tree) := by
    obtain ⟨W, hW, hWv, hXW⟩ := hF3p
    refine (GoldilocksCorrectness.Record.Statements.Routines.lem7_startsTowards_of_compatible M F) _ _ _ X W
      ((compatible_iff _ _).2 (Or.inl hApX)) ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _) ?_ ⟨hW, hWv⟩
      hXW
    intro P hAP _ hPX
    have hPH : P.AncestorEq (H u₀) := ancestorEq_trans hPX (hHs u₀ hu₀).2.2.2.2
    have hPT : P ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p _ P hHu₀T hPH
    have hFP : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.AncestorEq P :=
      ancestorEq_trans hF2p (ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_get_anchor M F) _ _) hAP)
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hPT, hFP⟩
  -- step 7 of `lem20`: `p`'s walk, so `X` is `B`'s parent or an ancestor of it (Lemma 2 over the
  -- walk predicate, at the model's tie-break)
  have hSupportP : support_p ⊆ votes_p := by
    intro vote' hv
    rw [hPCV.1]
    exact ((hPCV.2 vote').1 hv).1
  have hVotesP : ∀ u ∈ Hs, VotesOnceFor (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))) votes_p support_p s X u := by
    intro u hu
    obtain ⟨hpool, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeldP u hu
    refine ⟨GoldfishVote.mk u s (H u).root, (hPCV.2 _).2 ⟨hpool, y, hy⟩, rfl, rfl,
      ⟨H u, hHΦ, rfl, (hHs u hu).2.2.2.2⟩, ?_⟩
    intro vote' hv' hi'
    rw [hPCV.1] at hv'
    exact huniq vote' hv' hi'
  have hXH : X.AncestorEq Hp :=
    @GoldilocksCorrectness.Statements.Routines.lem2_goldfish_walkEnd_extends_majority_block V _ _
      M.tieBreak S.C _ _ votes_p support_p s _ X Hp _ Hs hStartP hRootsΦp hSupportP hVotesP
      (by rw [← GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq_spec F]; exact hVotersP') hW
  -- the end of `p`'s walk: its start or a block of the tree walked
  have hEnd := @GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq V _ M.tieBreak _ _ _ _ _ hW
  rw [hBpar]
  exact ⟨hXH, hBslot, hBne, hBpar?, hEnd.symm⟩

end GoldilocksCorrectness.Record.Proofs.Executions

