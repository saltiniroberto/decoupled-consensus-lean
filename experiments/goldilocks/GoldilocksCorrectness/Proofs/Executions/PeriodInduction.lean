module
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Statements.Executions.PeriodChainBlockStatements
public import GoldilocksCorrectness.Statements.Executions.PeriodInductionDefs
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-! Every
landed definition and statement of record stays byte-identical; The
audited statements are in `Statements/Executions/PeriodInductionStatements.lean`.

- `AsyncHypsOfChainBlockGSTBeforeVotes`, the copy of `AsyncHypsOfChainBlock` with `GST` at or
  before the vote time of slot `s + 1`, and its two conversions `toAsyncHypsOfChainBlock`,
  `toAsyncHyps`: every landed step lemma is called through them;
- `exists_votes_on_chain`, `voters_on_chain_majority`: the voters of a slot whose votes
  `VotesExtendAt` puts on `B`'s chain, their blocks, and their majority of the committee;
  statement 1′'s core (`vote_compatible_of_timely_view_ofExtend`) and Lemma 99 read them.

 Statement 2
(`confirmation_extends_B_of_timely_votes`), the original of statement 2′
`confirmation_compatible_of_timely_votes` (`Proofs/Executions/PeriodInductionCompat.lean`), was
deleted then.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono slotStart_mono supportCutoff_eq
  voteTime_mono')

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Period

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁`:
`AsyncHypsOfChainBlock S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁` with `GST` at or before the
vote time of slot `s + 1`, the first votes after the hand-over proposal, in place of `GST` at or
before `b₀`.


With `GST = b₀` after the support cutoff of slot `s + 1`, the slot-`(s + 1)` honest votes are due
only after the view freeze of `s + 1`, so a voter of slot `s + 2` outside the lock holders may be
shown only the adversary's votes and vote off `B`'s chain while every other hypothesis of the
timely-view statement holds. The old field follows from the new one
(`voteTime S (s + 1) < supportCutoff S (s + 1) ≤ b₀`): `toAsyncHypsOfChainBlock` and `toAsyncHyps`
give the landed bundles, so every landed step lemma is called through them. Lemma 105 builds it from its spelled-out
hypotheses with `GST ≤ voteTime S (s + 1)` in place of `GST ≤ b₀`, and the top statement derives
that from `GST ≤ tGAT`, the honest round opening slots and `tAwakeEnd < slotStart S s`
(`gst_le_voteTime_succ_of_top`, `scratch/goldilocks_async/probe_ar4_replan.lean`). No top-level
claim changes. -/
structure AsyncHypsOfChainBlockGSTBeforeVotes (GST s : ℕ) (B : Block V)
    (H t₀ anchor tAwakeEnd b₀ b₁ : ℕ) : Prop where
  /-- Every time is reached. -/
  hDiv : TimeDiverges x.toTrace
  /-- Corruption is permanent. -/
  hMono : Sched.MonotoneCorruption
  /-- Blocks and Goldfish votes are delivered as in the synchronous network outside `[b₀, b₁)`. -/
  hSync : SynchronyFromWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁
  /-- A waking validator catches up on blocks and Goldfish votes outside `[b₀, b₁)`. -/
  hCatch : CatchUpOnWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁
  /-- Attestations are delivered as in the synchronous network outside `[b₀, b₁)`. -/
  hSyncF : SynchronyFromWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁
  /-- A waking validator catches up on attestations outside `[b₀, b₁)`. -/
  hCatchF : CatchUpOnWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁
  /-- A block reaches a validator only once the validator holds its parent. -/
  hParent : ParentHeldAtDelivery S Sched x
  /-- Nobody votes in an honest validator's name. -/
  hOwner : VotesCastByOwner S Sched x
  /-- Nobody signs in an honest validator's name. -/
  hU : Unforgeability Vocab.goldilocks Sched x.toTrace
  /-- Fewer than a quorum have been corrupted up to any time. -/
  hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t
  /-- From `anchor` on, the honest active members of each committee outnumber the rest. -/
  hSleepK : CommitteeSleepiness S Sched anchor
  /-- `anchor` is at or before the start of slot `s + 1`. -/
  hAnchor : anchor ≤ slotStart S (s + 1)
  /-- The network is synchronous from the vote time of slot `s + 1` on, outside the period. -/
  hGST : GST ≤ voteTime S (s + 1)
  /-- The period starts at or after the hand-over update. -/
  hb₀ : supportCutoff S (s + 1) ≤ b₀
  /-- The period is an interval. -/
  hb : b₀ ≤ b₁
  /-- The period ends one delay before the vote time of slot `s + k`. -/
  hb₁ : b₁ + Δ S ≤ voteTime S (s + S.C.k)
  /-- Wherever the previous votes are owed inside the period, the lock holders outweigh the
  rest of the committee. -/
  hHold : HoldersOutweighWhereOwed S Sched s b₀ b₁
  /-- `t₀` is at or before the hand-over cutoff. -/
  ht₀ : t₀ ≤ supportCutoff S (s + 1)
  /-- The hand-over facts, over the copied certificate and attestation clauses. -/
  hHand : HandoverFactsOfChainBlock S Sched x s B H t₀ tAwakeEnd

end Period

end GoldilocksCorrectness.Statements.Executions

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg AtomicHonest)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The bundle's conversions -/

/-- The copied bundle gives `AsyncHypsOfChainBlock`: `GST ≤ b₀` from `GST ≤ voteTime S (s + 1)`,
`voteTime S (s + 1) < supportCutoff S (s + 1)` and `supportCutoff S (s + 1) ≤ b₀`.

The variables:
- `P`: the copied hypotheses. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock {S : Setup V}
    {Sched : Schedule V} {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    AsyncHypsOfChainBlock S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ := by
  have h1 := supportCutoff_eq S (s + 1)
  have h2 := P.hGST
  have h3 := P.hb₀
  exact ⟨P.hDiv, P.hMono, P.hSync, P.hCatch, P.hSyncF, P.hCatchF, P.hParent, P.hOwner, P.hU,
    P.hAdvQ, P.hSleepK, P.hAnchor, by omega, P.hb₀, P.hb, P.hb₁, P.hHold, P.ht₀, P.hHand⟩

/-- The copied bundle gives `AsyncHyps`, through `AsyncHypsOfChainBlock`.

The variables:
- `P`: the copied hypotheses. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHyps {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    AsyncHyps S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ :=
  (AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock P).toAsyncHyps

/-! ## The voters of a slot on `B`'s chain -/

/-- The members of a set `Q` of honest active committee members of slot `σ`, each of whose slot-`σ`
votes is for a block it holds on `B`'s chain, have such a vote: a block `H u` for each, `u`'s
slot-`σ` vote for `H u` is on the wire at its tick at the vote time of `σ`, `u` holds `H u` then,
`H u` is `B` or a descendant of `B`, and `u` is a committee member honest at the support cutoff of
slot `σ + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `σ`: the slot; `Q`: the voters;
  `B`: the block. -/
theorem exists_votes_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (σ : ℕ) (Q : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hQ : Q ⊆ honestActiveAt S Sched σ ∩ S.P.committee σ)
    (hExt : ∀ u ∈ Q, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
        vote = GoldfishVote.mk u σ H_u.root ∧ B.AncestorEq H_u) :
    ∃ H : V → Block V, ∀ u ∈ Q, u ∈ S.P.committee σ ∧
      u ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u σ (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S σ) u).S.T ∧ B.AncestorEq (H u) := by
  classical
  have key : ∀ u ∈ Q, ∃ Hu : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u σ Hu.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      Hu ∈ (stateBefore x (voteTime S σ) u).S.T ∧ B.AncestorEq Hu := by
    intro u hu
    obtain ⟨hA, hK⟩ := Finset.mem_inter.1 (hQ hu)
    obtain ⟨i, vote, hl, -, -, hsent⟩ :=
      GoldilocksCorrectness.Statements.Executions.honest_active_votes S Sched x σ u hDiv hMono hA hK
    obtain ⟨Hu, hHuT, hveq, hBH⟩ := hExt u hu vote ⟨i, hl, hsent⟩
    exact ⟨Hu, ⟨i, hl, hveq ▸ hsent⟩, hHuT, hBH⟩
  refine ⟨fun u => if h : u ∈ Q then Classical.choose (key u h) else B, fun u hu => ?_⟩
  obtain ⟨hA, hK⟩ := Finset.mem_inter.1 (hQ hu)
  have hspec := Classical.choose_spec (key u hu)
  simp only [dif_pos hu]
  exact ⟨hK, (Finset.mem_sdiff.1 hA).2, hspec⟩

/-- The voters of slot `s'` whose votes `VotesExtendAt` puts on `B`'s chain outweigh the rest of the
committee: the lock holders' members of the committee when the previous votes were owed inside the
period (`P.hHold`), and the honest active members otherwise (`P.hSleepK`).

The variables:
- `P`: the hypotheses; `s'`: the slot. -/
theorem voters_on_chain_majority {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) (s' : ℕ)
    (hs' : s + 1 ≤ s') (hVotes : VotesExtendAt S Sched x s B b₀ b₁ s') :
    ∃ Q : Finset V, Q ⊆ honestActiveAt S Sched s' ∩ S.P.committee s' ∧
      (∀ u ∈ Q, ∀ vote : GoldfishVote V,
        (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent) →
        ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
          vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u) ∧
      (S.P.committee s' \ Q).card < Q.card := by
  classical
  by_cases hOwed : VotesOwedInPeriod S b₀ b₁ s'
  · have hs2 : s + 2 ≤ s' := by
      by_contra hc
      have h1 : s' - 1 ≤ s + 1 := by omega
      have h2 := supportCutoff_eq S (s' - 1)
      have h3 := supportCutoff_eq S (s + 1)
      have h4 := voteTime_mono' S h1
      have h5 := P.hb₀
      exact absurd hOwed.1 (by omega)
    have hlt := P.hHold s' hs2 hOwed.1 hOwed.2
    refine ⟨holdersAt S Sched s s' ∩ S.P.committee s', ?_,
      fun u hu => hVotes.1 u (Finset.mem_inter.1 hu).1, ?_⟩
    · intro u hu
      simp only [holdersAt, Finset.mem_inter] at hu ⊢
      exact ⟨hu.1.2, hu.2⟩
    · have heq : S.P.committee s' \ (holdersAt S Sched s s' ∩ S.P.committee s') =
          S.P.committee s' \ holdersAt S Sched s s' := by
        ext u
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [heq]
      exact hlt
  · refine ⟨honestActiveAt S Sched s' ∩ S.P.committee s', subset_rfl,
      fun u hu => hVotes.2 hOwed u (Finset.mem_inter.1 hu).1, ?_⟩
    have hanchor : anchor ≤ slotStart S (s' + 1) :=
      le_trans P.hAnchor (slotStart_mono S (by omega))
    have hK := P.hSleepK (s' + 1) (by omega) hanchor
    rw [Nat.add_sub_cancel] at hK
    have hsub : S.P.committee s' \ (honestActiveAt S Sched s' ∩ S.P.committee s') ⊆
        S.P.committee s' \ honestActiveAt S Sched s' := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_inter] at hw ⊢
      tauto
    exact lt_of_le_of_lt (Finset.card_le_card hsub) hK

end GoldilocksCorrectness.Proofs.Executions
