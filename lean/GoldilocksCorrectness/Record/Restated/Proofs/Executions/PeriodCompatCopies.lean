module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PeriodCompatDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Statements.Executions.PeriodCompatDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f

@[expose] public section

/-!
# PeriodCompatCopies, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodCompatCopies.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the asynchronous period's step
lemmas with the compatible vote clause, namely a slot owed inside the period at most `s + k`, the
two conjuncts of the compatible vote clause, and the copies of the step lemmas whose step reading a
vote on `B`'s chain reads a vote compatible with `B`. The page's routine-level theorems are the
facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff
  expireLocks_keepsVotes fast_test_eq_ok_true_iff goldfish_fork_choice_eq t_eq_mul wake_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith ConfirmationUpdated LocksRevoked
  Opposes OpponentsOf LockedViableBlocks)
open GoldilocksCorrectness.Record.Statements.Routines (SupportVotes EarlyVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Proofs.Routines
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_antisymm ancestorEq_compatible
  ancestorEq_refl ancestorEq_trans ancestorStrict_iff compatible_iff
  compatible_of_ancestorEq_compatible conflicts_iff dutyWindowStart_succ_lt_supportCutoff
  expireLocks_keepsVotes fast_test_eq_ok_true_iff genesis_ancestorEq goldfish_fork_choice_eq
  one_le_Δ t_eq_mul wake_eq)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Reading the compatible vote clause -/

omit [RootOrder] in
/-- **A slot whose previous votes were owed inside the period is at most `s + k`.** When the
period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`, a slot `s'` with
`M.supportCutoff S.C (s' − 1) + Δ S < b₁ + max (Δ S) Δs` has `s' ≤ s + k`.

Why: `M.voteTime S.C (s' − 1) + 2Δ = M.supportCutoff S.C (s' − 1) + Δ < b₁ + max (Δ S) Δs ≤
M.voteTime S.C (s + k)`, so `s' − 1 < s + k`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s`: the hand-over slot; `Δs`: the sync delay; `b₀`, `b₁`: the start and the end
  of the period; `s'`: the slot.

Read aloud: the votes owed inside the period are all owed during the hand-over lock's life. -/
theorem owed_slot_le_k (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {s b₀ b₁ s' Δs : ℕ}
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)) (h : VotesOwedInPeriod M S Δs b₀ b₁ s') :
    s' ≤ s + S.C.k := by
  have hΔ := one_le_Δ S
  obtain ⟨-, h2⟩ := h
  by_contra hc
  have hle : s + S.C.k ≤ s' - 1 := by omega
  have h3 : M.voteTime S.C (s + S.C.k) ≤ M.voteTime S.C (s' - 1) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hle) _
  have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' - 1)
  omega

/-- The holders' conjunct of `VotesCompatibleAt`, at a slot `s' ≤ s + k`, read as "the vote's
block is compatible with `B`".

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `b₀`, `b₁`: the start and the end of the period; `s'`: the slot of the votes.

Read aloud: at a slot at most `s + k`, every vote a lock holder put on the wire is for a block
compatible with `B`. -/
theorem holders_vote_compatible_of_votesCompatibleAt {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {s : ℕ} {B : Block V} {b₀ b₁ s' Δs : ℕ}
    (h : VotesCompatibleAt M S A x s B Δs b₀ b₁ s') (hk : s' ≤ s + S.C.k) :
    ∀ u ∈ holdersAt M S A x s s', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
        vote = GoldfishVote.mk u s' H_u.root ∧ H_u.compatible B = true := by
  intro u hu vote hsend
  obtain ⟨H_u, hT, hv, hB⟩ := h.1 hk u hu vote hsend
  exact ⟨H_u, hT, hv, (compatible_iff _ _).2 (Or.inr hB)⟩

/-- The honest active voters' conjunct of `VotesCompatibleAt`, at a slot whose previous votes
were not owed inside the period, read as "the vote's block is compatible with `B`".

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `b₀`, `b₁`: the start and the end of the period; `s'`: the slot of the votes.

Read aloud: at a slot whose previous votes were not owed inside the period, every vote an honest
active voter put on the wire is for a block compatible with `B`. -/
theorem active_vote_compatible_of_votesCompatibleAt {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {s : ℕ} {B : Block V} {b₀ b₁ s' Δs : ℕ}
    (h : VotesCompatibleAt M S A x s B Δs b₀ b₁ s') (hgood : ¬ VotesOwedInPeriod M S Δs b₀ b₁ s') :
    ∀ u ∈ honestActiveAt M S A x s', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
        vote = GoldfishVote.mk u s' H_u.root ∧ H_u.compatible B = true := by
  intro u hu vote hsend
  obtain ⟨H_u, hT, hv, hB⟩ := h.2 hgood u hu vote hsend
  refine ⟨H_u, hT, hv, ?_⟩
  rcases hB with hB | ⟨hc, -⟩
  · exact (compatible_iff _ _).2 (Or.inr hB)
  · exact hc

/-! ## The copies -/

/-- **The votes a set of validators casts for blocks compatible with `B` do not count
for a block that conflicts with `B`.** `score_set_outside` with each member's vote for a block
`H_u` compatible with `B` in place of `B` or a descendant of `B`: the equivocators of `sv` and
the validators whose vote in `sv` supports a block `D` conflicting with `B` are members of the
committee of slot `s'` outside `G`.

 The one change is
the premise `hGv`, which concludes `H_u.compatible B = true` in place of `B.AncestorEq H_u`, and the
step that reads it: `D` an ancestor of `H_u`, compatible with `B`, is compatible with `B`
(`compatible_of_ancestorEq_compatible`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `B`: the protected
  block; `D`: the conflicting block; `u`: the validator whose pool it is; `c`: the time; `G`: the
  set of validators; `sv`: the votes counted.

The equivocators and the supporters are the spec's routines `equivocators` and `supportersOf` on
the frame of `u`'s node state: the counting of the fast test `fast_test` that the record's update
runs (`confirmationUpdated_fast_cases`), which `fast_test_fails_of_minority` reads.

Roots name blocks up to `u`'s own tick to `c`: the block of the tree of `M.fg_to_ac` of the state that tick starts
from which a supporter's vote names is compared with the block the supporter held at its own tick to the vote time
of `s'`, before `u`'s tick (`hc` and `hSkew`). Read at `u`'s tick input to `c`.

Read aloud: votes for blocks compatible with `B` do not count for a block conflicting with `B`: the
validators whose votes count for it are committee members outside the voting set. -/
theorem score_set_outside_ofCompat (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hOwner : VotesCastByOwner M A x) {s' c : ℕ} {B D : Block V} {u : V}
    (hc : M.supportCutoff S.C s' ≤ c)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep u c)))
    -- `u` is honest at the step of its tick to `c` (the state whose pool and frame are counted)
    (hu : u ∉ A.corrupted (x.tickStep u c))
    (G : Finset V) (hG : ∀ v' ∈ G, v' ∉ A.corrupted (x.tickStep u c))
    (hGv : ∀ v' ∈ G, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick v' (M.voteTime S.C s') ∧
        (⟨v', NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput v' (M.voteTime S.C s')).tree,
        vote = GoldfishVote.mk v' s' H_u.root ∧ H_u.compatible B = true)
    (sv : Finset (GoldfishVote V)) (hsv : sv ⊆ M.votesHeldSet (x.tickInput u c) s')
    (hDB : ¬ D.compatible B = true) :
    equivocators sv ∪
      GoldilocksCorrectness.Proofs.Routines.supportersOf (M.fg_to_ac (x.tickInput u c)) sv sv s'
        D ⊆
      S.P.committee s' \ G := by
  classical
  have hcomm : ∀ vote ∈ sv, vote.val_index ∈ S.P.committee s' := fun vote hvote =>
    (GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E _ u s' vote (hsv hvote)
  -- a vote of a member of `G` in the pool was cast by that member at its tick to the vote time of `s'`, at a step
  -- before the pool's step, for a block compatible with `B`
  have hExt : ∀ vote ∈ sv, vote.val_index ∈ G →
      ∃ k' : ℕ, k' < x.tickStep u c ∧ ∃ H_u ∈ (x.st k' vote.val_index).tree,
        vote = GoldfishVote.mk vote.val_index s' H_u.root ∧ H_u.compatible B = true := by
    intro vote hvote hvG
    obtain ⟨i, hik, sm, hsm, hcarry⟩ := (pool_vote_sent M F) x R E (hsv hvote)
    have hhon : vote.val_index ∉ A.corrupted i := fun h =>
      hG _ hvG (E.corrupted_mono i _ hik.le h)
    obtain ⟨k', t', hk'i, hlk, hsk⟩ := hOwner i sm vote hsm hcarry hhon
    obtain ⟨-, n', sent, hrun, hsent⟩ := (tick_send_of_honestSendAt M F R E) hlk hsk
    have hTI_k : x.tickInput vote.val_index t' = x.st k' vote.val_index := by
      show x.st (x.tickStep vote.val_index t') vote.val_index = x.st k' vote.val_index
      rw [(tickStep_eq_of_lbl M) x E hlk]
    have hInvT : M.nodeInv S.C S.P S.X (x.tickInput vote.val_index t') := by
      rw [hTI_k]
      exact ((lem11_node_invariant M F) S A x R E k' _ (E.not_mem_corrupted_of_tick hlk)).1
    -- Lemma 14 over the record: the tick sends a vote only at the vote time of the slot of `t'`, for that slot
    obtain ⟨ht'', -, hvs, -⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote
        hrun hInvT hsent
    have hslot := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E _ u s' vote (hsv hvote)
    have hvt : t' = M.voteTime S.C s' := by
      have hslt : S.C.slot (t' : Int) = s' := by rw [← hvs, hslot]
      have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S s'
      rw [hslt] at ht''
      rw [← ht''] at h1
      exact_mod_cast h1.symm
    rw [hvt] at hlk
    obtain ⟨H_u, hHuT, hveq, hBH⟩ := hGv _ hvG vote ⟨k', hlk, hsk⟩
    have hTI' : x.tickInput vote.val_index (M.voteTime S.C s') = x.st k' vote.val_index := by
      show x.st (x.tickStep vote.val_index (M.voteTime S.C s')) vote.val_index = x.st k' vote.val_index
      rw [(tickStep_eq_of_lbl M) x E hlk]
    exact ⟨k', lt_of_le_of_lt hk'i hik, H_u, hTI' ▸ hHuT, hveq, hBH⟩
  intro v hv
  rcases Finset.mem_union.1 hv with hE | hS
  · -- an equivocator: two distinct votes of `v` in the pool, so `v` is not outside the adversary set at the pool's step
    rw [GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff] at hE
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega :
      1 < (votes_by sv v).card)
    simp only [GoldilocksCorrectness.Proofs.Routines.mem_votes_by_iff] at ha hb
    refine Finset.mem_sdiff.2 ⟨ha.2 ▸ hcomm a ha.1, fun hvG => hab ?_⟩
    exact (unique_vote_of_owner_at M F R) E hOwner (hG v hvG) (hsv ha.1) (hsv hb.1) ha.2 hb.2
  · -- a supporter of `D`: its vote's head names a block of which `D` is an ancestor
    obtain ⟨vote, hvote, hval, -, -, H, hH, hHr, hDH⟩ := (GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_iff _ _ _ _ _ _).1 hS
    refine Finset.mem_sdiff.2 ⟨hval ▸ hcomm vote hvote, fun hvG => hDB ?_⟩
    obtain ⟨k', hk'k, H_u, hHuT, hveq, hBH⟩ := hExt vote hvote (hval ▸ hvG)
    have hHH : H = H_u := by
      refine hRoots H H_u ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.tickStep u c) (v := u) hu le_rfl ((((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hH).1))
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k') (v := vote.val_index) (fun h => hG _ (hval ▸ hvG) (E.corrupted_mono k' _ hk'k.le h)) (R.time_mono hk'k.le) hHuT)
        (by rw [hHr, hveq])
    rw [hHH] at hDH
    exact compatible_of_ancestorEq_compatible hDH hBH

/-- **No block that conflicts with `B` is a fast block of an updater's update of a slot
`s' ≥ s + 1`, under the compatible vote clause.** `fast_blocks_compatible_of_votes_updater` with
`VotesCompatibleAt` in place of `VotesExtendAt`: the counted set `G` (the lock holders when the
votes of slot `s' − 1` were owed inside the period, else the honest active validators of `s'`)
votes for blocks compatible with `B`, which is all `score_set_outside_ofCompat` needs.

 The one change is the premise `hVotes`; the holders' conjunct is read at a slot whose
previous votes were owed, so at most `s + k` (`owed_slot_le_k`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot of the update; `u`: the updater.
- `T`: the time up to which `P`'s premises are read; `hT`: the support cutoff of `s' + 1` is at most `T`, so the committee of `s'` is
  among those `P.hSleepK` covers.

Roots name blocks up to `u`'s own tick to `M.supportCutoff S.C (s' + 1)`: the block of the tree of `M.fg_to_ac` of the
state that tick starts from which a supporter's vote names is compared with the block the supporter held at its own tick
to the vote time, before `u`'s tick (`hSkew`).

Read aloud: under the compatible vote clause, no block conflicting with `B` is a fast block of an
updater's update of a slot after the hand-over. -/
theorem fast_blocks_compatible_of_votes_updater_ofCompat (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    (P : AsyncHypsUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind) (s' : ℕ) (u : V)
    -- the committee of slot `s'` is among those `P` counts
    (hT : M.supportCutoff S.C (s' + 1) ≤ T)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep u (M.supportCutoff S.C (s' + 1)))))
    (hs' : s + 1 ≤ s')
    -- `u` ticks to the support cutoff of slot `s' + 1`, awake and honest from the duty window's
    -- start of slot `s' + 1` up to that tick
    (hu : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.supportCutoff S.C (s' + 1)))
    (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    ∀ D ∈ (x.tickOutput u (M.supportCutoff S.C (s' + 1))).fastBlocks,
      D.compatible B = true := by
  intro D hD
  have hΔ := one_le_Δ S
  -- `u`'s tick `K` to the support cutoff `c` of slot `s' + 1`, honest there
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hu
  have huK : u ∉ A.corrupted K := E.not_mem_corrupted_of_tick hlK
  have hKs : x.tickStep u (M.supportCutoff S.C (s' + 1)) = K := (tickStep_eq_of_lbl M) x E hlK
  have hTI : x.tickInput u (M.supportCutoff S.C (s' + 1)) = x.st K u := by
    unfold Trace.tickInput; rw [hKs]
  -- the duty window's start, read as an integer, is at most the model's natural-number start
  have hdwz : (Goldilocks.duty_window_start S.C (s' + 1) : ℤ) ≤
      ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℤ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U)]
    exact Int.self_le_toNat _
  -- the update `u`'s tick ran, and the fast test `D` passed
  obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hu
    (by
      have h := (dutyWindowStart_succ_lt_supportCutoff M F U) S s'
      have h' : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℤ) < ((M.supportCutoff S.C (s' + 1) : ℕ) : ℤ) := by
        exact_mod_cast h
      exact lt_of_le_of_lt hdwz h')
  obtain ⟨n'', sent, hrun, hAwF, -, hfb, -, -⟩ :=
    (update_state_of_tick M F U) S A x R s' u E hlK ⟨τ, hτ, hτle⟩
  rw [hfb] at hD
  have hCU := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' u n'' sent hrun hAwF
  obtain ⟨-, -, -, -, -, -, hfast⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_fast_cases (Nat.le_add_left 1 s')
      hCU hD
  simp only [Nat.add_sub_cancel] at hfast
  by_contra hDB
  set sv := SupportVotes M S.C (x.tickInput u (M.supportCutoff S.C (s' + 1))) s' with hsv_def
  have hRΦ : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (M.fg_to_ac (x.tickInput u (M.supportCutoff S.C (s' + 1)))).tree := by
    rw [hTI]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E K u
  rw [fast_test_eq_ok_true_iff _ hRΦ] at hfast
  -- the votes counted are votes of `u`'s pool of slot `s'` at its tick (the early votes are held votes)
  have hsv : sv ⊆ M.votesHeldSet (x.tickInput u (M.supportCutoff S.C (s' + 1))) s' := by
    intro vote hvote
    simp only [hsv_def, SupportVotes, EarlyVotes, Finset.mem_filter] at hvote
    exact hvote.1.1
  have hvc : M.supportCutoff S.C s' ≤ M.supportCutoff S.C (s' + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have huc : u ∉ A.corrupted (x.tickStep u (M.supportCutoff S.C (s' + 1))) := by rw [hKs]; exact huK
  -- an honest active validator of `s'` is outside the adversary set at `u`'s tick (`honestActiveAt`'s second read)
  have hGA : ∀ v' ∈ honestActiveAt M S A x s', v' ∉ A.corrupted (x.tickStep u (M.supportCutoff S.C (s' + 1))) := by
    intro v' hv' hc
    have h2 := (Finset.mem_sdiff.1 hv').2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at h2
    exact h2.2 ⟨K, u, hlK, huK, hKs ▸ hc⟩
  have hdisj : Disjoint (GoldilocksCorrectness.Proofs.Routines.supportersOf
      (M.fg_to_ac (x.tickInput u (M.supportCutoff S.C (s' + 1)))) sv sv s' D) (equivocators sv) :=
    GoldilocksCorrectness.Proofs.Routines.disjoint_supportersOf_equivocators
  have hcard := Finset.card_union_of_disjoint hdisj.symm
  by_cases hOwed : VotesOwedInPeriod M S Δs b₀ b₁ s'
  · -- the votes of slot `s' − 1` were owed inside the period: the lock holders' majority
    have hs2 : s + 2 ≤ s' := by
      by_contra hc
      have h1 : s' - 1 ≤ s := by omega
      have h2 : M.supportCutoff S.C (s' - 1) < M.supportCutoff S.C (s + 1) := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
          (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
        have := Nat.mul_le_mul_left (4 * Δ S) h1
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have := P.hb₀
      exact absurd hOwed.1 (by omega)
    have hlt := P.hHold s' hs2 hOwed.1 hOwed.2
    have hsub := (score_set_outside_ofCompat M F U) S A x R E
      ((GoldilocksCorrectness.Record.Statements.Executions.votesCastByOwner_of_unforgeability M F) S A x R E) hvc hRoots
      huc (holdersAt M S A x s s')
      (fun v' hv' => hGA v' (Finset.mem_inter.1 hv').2)
      ((holders_vote_compatible_of_votesCompatibleAt M F) hVotes ((owed_slot_le_k M F U) P.hb₁ hOwed))
      _ hsv hDB
    refine GoldilocksCorrectness.Proofs.Executions.fast_test_fails_of_minority _ _ _ hsub hlt ?_
    rw [hcard]
    exact hfast
  · -- otherwise every honest active voter of slot `s'` voted for a block compatible with `B`
    have hlt := P.hSleepK (s' + 1) (by omega) (le_trans P.hAnchor (by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]; exact Nat.mul_le_mul_left _ (by omega))) hT
    simp only [Nat.add_sub_cancel] at hlt
    have hsub := (score_set_outside_ofCompat M F U) S A x R E
      ((GoldilocksCorrectness.Record.Statements.Executions.votesCastByOwner_of_unforgeability M F) S A x R E) hvc hRoots
      huc (honestActiveAt M S A x s') hGA
      ((active_vote_compatible_of_votesCompatibleAt M F) hVotes hOwed) _ hsv hDB
    refine GoldilocksCorrectness.Proofs.Executions.fast_test_fails_of_minority _ _ _ hsub hlt ?_
    rw [hcard]
    exact hfast

/-- **Lemma 101, the step, over the copied attestation clause and the compatible vote
clause.** `attestations_step_ofHeldEntry` with `VotesCompatibleAt` in place of `VotesExtendAt`:
the fast block an attestation's entry is taken from is compatible with `B` by
`fast_blocks_compatible_of_votes_updater_ofCompat`.

 The one
change is the premise `hVotes`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `j`: the step.
- `T`: the time up to which `P`'s premises are read; `hTt`: when step `j` is a tick, its clock value
  is at most `T` (read at the tick, rule R3; the real time of step `j + 1` until the ninth launch).
- `hWin`: some configuration's real time lies in the hand-over facts' window.

Roots name blocks until `x[j + 1].time`: as `attestations_step_ofHeldEntry`.

A configuration in the hand-over window: a tick at step `j` to a clock value at most the
hand-over cutoff is covered by the fifth clause of the hand-over facts at that configuration when the
step is before the cutoff's real time, and is a tick to the cutoff by an updater of slot `s`, whose fast
blocks are compatible with `B` by the holders' clause, otherwise.

Read aloud: every honest attestation after the hand-over names a chain compatible with `B`, through
an entry an honest validator holds, when the honest votes do not conflict with `B`. -/
theorem attestations_step_ofHeldEntry_ofCompat (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind tW) (j : ℕ)
    -- when step `j` is a tick, its clock value is at most `T`
    (hTt : ∀ (v : V) (c : ℕ), x.lbl j = Event.tick v c → c ≤ T)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    -- the hand-over facts cover the whole window
    (hcW : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤ tW)
    (hRoots : RootsNameBlocksUntil M A x (x.time (j + 1)))
    (hAtt : AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H t₀ j)
    (hVotes : ∀ s' : ℕ, s + 1 ≤ s' → M.supportCutoff S.C s' ≤ x.time j →
      VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H t₀ (j + 1) := by
  intro i t v a hi hl hsent
  rcases Nat.lt_or_ge i j with hij | hij
  · exact hAtt i t v a hij hl hsent
  have hij' : i = j := by omega
  subst hij'
  have hΔ := one_le_Δ S
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
  -- the attestation's source: a fast block of the update the tick to the support cutoff of a slot `s' + 1` ran
  obtain ⟨s', Eb, Fb, ht, hv, hF, hFT, hEF, hE1, hE2, hE3⟩ :=
    (attest_source_fast_block_updater_inTree M F U) S A x R i t v a E hl hsent
  have hti := E.tick_active i v t hl
  have hkey : (M.supportCutoff S.C (s + 1) : ℕ) ≤ t → t₀ ≤ t := fun h => le_trans P.ht₀ h
  rcases Nat.lt_or_ge s' s with hlt | hge
  · -- a tick to an earlier cutoff: before the cutoff's real time, so before the configuration `hWin` names, whose
    -- hand-over facts' fifth clause covers it
    obtain ⟨j₀, hj₀a, hj₀b⟩ := hWin
    have hc : t ≤ M.supportCutoff S.C s := by
      rw [ht, (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
      have := Nat.mul_le_mul_left (4 * Δ S) (show s' + 1 ≤ s by omega)
      omega
    have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S s
    have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = (M.supportCutoff S.C s : ℕ) + 4 * Δ S := by
      rw [hcs]; push_cast; ring
    have htR : (t : ℝ) ≤ (M.supportCutoff S.C s : ℕ) := by exact_mod_cast hc
    have hlt' : x.time i < ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by linarith [hti.2.2]
    have hij₀ : i < j₀ := by
      by_contra hle
      have h := (time_mono M) x R (not_lt.1 hle)
      linarith
    exact P.hHand.2.2.2.2.1 j₀ hj₀a (le_trans hj₀b hcW) i t v a hij₀ hl hsent
  -- the attestation's entry is held by `v` before the tick, honest there
  have hET : Eb ∈ (x.st i v).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i v Fb Eb hFT hEF
  have hvi : x.Honest A i v := E.not_mem_corrupted_of_tick hl
  have hheld : inHonestTreeBy M A x (x.time i) Eb := ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := i) (v := v) hvi le_rfl hET)
  have hcut : M.supportCutoff S.C (s + 1) ≤ t := by
    rw [ht, (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    have := Nat.mul_le_mul_left (4 * Δ S) (show s + 1 ≤ s' + 1 by omega)
    omega
  -- the fast block `Fb` the entry is taken from is compatible with `B`
  have hFB : Fb.compatible B = true := by
    rcases Nat.lt_or_ge s s' with hs' | hss
    · -- an update of a later slot: `fast_blocks_compatible_of_votes_updater_ofCompat`, as `dev`
      have hs1 : s + 1 ≤ s' := hs'
      have hk : x.tickStep v (M.supportCutoff S.C (s' + 1)) = i := by
        rw [← ht]; exact (tickStep_eq_of_lbl M) x E hl
      have hvt : M.supportCutoff S.C s' ≤ x.time i := by
        have h1 : M.supportCutoff S.C (s' + 1) = M.supportCutoff S.C s' + 4 * Δ S :=
          (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S s'
        have h2 : ((M.supportCutoff S.C s' : ℕ) : ℝ) + 4 * Δ S ≤ (t : ℝ) := by
          rw [ht, h1]; push_cast; ring_nf; exact le_rfl
        have hsk : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S := hSkew
        linarith [hti.2.1]
      have hRi : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)))) := by
        rw [hk]
        exact GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M
          ((time_mono M) x R (Nat.le_succ i)) hRoots
      have hTs : M.supportCutoff S.C (s' + 1) ≤ T := by rw [← ht]; exact hTt v t hl
      exact (fast_blocks_compatible_of_votes_updater_ofCompat M F U R E)
        ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockUntil.toAsyncHypsUntil M F R E
          hNet hSkew hRedeliver) P (le_trans hcut (hTt v t hl))) s' v hTs hRi
        hs1 hv (hVotes s' hs1 hvt) Fb (by rw [ht] at hF; exact hF)
    · -- the hand-over update itself: `v` is an updater of slot `s`, whose fast blocks are compatible with `B` by
      -- the holders' clause of the hand-over facts
      have hss' : s' = s := by omega
      subst hss'
      have hInvv := (P.hHand.2.1 v hv).2.2
      exact hInvv.2.2.2.1 Fb (by rw [ht] at hF; exact hF)
  refine ⟨fun h _ => absurd (hkey hcut) (Nat.not_le.mpr h), fun _ _ => ?_⟩
  exact ⟨Eb, (compatible_iff Eb B).1 (compatible_of_ancestorEq_compatible hEF hFB), hE1, hE2, hE3, hheld⟩
/-- **An opponent of `B` at a revocation is a committee member whose vote was not for a
block compatible with `B`.** `opponent_not_extender` with "for a block it holds that is
compatible with `B`" in place of "that is `B` or a descendant of `B`": an opponent `u` of `B`
among the votes of slot `s' − 1` that `w` holds is in that slot's committee; and when `u` is
honest active at slot `s' − 1`, it is not the case that every slot-`(s' − 1)` vote `u` put on the
wire at its tick at the vote time is for a block it holds that is compatible with `B`.

 The one change
is the premise of the second conjunct, `H_u.compatible B = true` in place of `B.AncestorEq H_u`, and
the last step, which reads it through `compatible_iff`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the locked block; `s'`: the slot
  of the revocation; `i`: the step of the tick; `w`: the revoking validator; `opp`: the opponents;
`u`: one of them; `tR`: the bound of the roots premise.

The landed statement reads the opponents as the answer of the spec's `opponents` on an AC state
`A` with `w`'s pool; the twin reads them as a set `opp` of validators each with a vote among
`w`'s slot-`(s' − 1)` votes that opposes `B` (`Opposes`), what the proof uses: the record's
revocation (`LocksRevoked`) counts its opponents over `w`'s node state (`OpponentsOf`), whose
members have such votes (`exists_vote_of_mem_opponentsOf`).

Roots name blocks up to `x.time i`, the real time of `w`'s tick to the vote time of `s'`: `w`'s
block at `i` against the opponent's block at its own tick, a step before the relay of its vote into
`w`'s held votes (`M.votesHeldSet`).

Read aloud: an opponent of `B` at a revocation is a committee member that, when honest active, did
not vote only for held blocks compatible with `B`. -/
theorem opponent_not_compatible (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {tR : ℝ}
    (hRoots : RootsNameBlocksUntil M A x tR) (hOwner : VotesCastByOwner M A x)
    (B : Block V) (s' i : ℕ) (w : V) (opp : Finset V)
    (hs' : 2 ≤ s')
    -- step `i` is `w`'s tick to the vote time of `s'`
    (hi : x.lbl i = Event.tick w (M.voteTime S.C s'))
    (hopp : ∀ u ∈ opp, ∃ vote ∈ M.votesHeldSet (x.st i w) (s' - 1), vote.val_index = u ∧
      Opposes M (x.st i w) B vote)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time i ≤ tR)
    (u : V) (hu : u ∈ opp) :
    u ∈ S.P.committee (s' - 1) ∧
      (u ∈ honestActiveAt M S A x (s' - 1) →
        (∀ vote : GoldfishVote V,
          (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' - 1)) ∧
            (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
              x.sent (i + 1) - x.sent i) →
          ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' - 1))).tree,
            vote = GoldfishVote.mk u (s' - 1) H_u.root ∧ H_u.compatible B = true) →
              False) := by
  obtain ⟨vote, hvote, hvu, hvopp⟩ := hopp u hu
  have hw : w ∉ A.corrupted i := E.not_mem_corrupted_of_tick hi
  refine ⟨hvu ▸ (GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E i w (s' - 1) vote hvote, fun hHon hExt => ?_⟩
  -- the vote is relayed into `w`'s held votes at a step before `i`
  obtain ⟨i', hi', hnew, -, -⟩ := (pool_vote_relayed M F U) S A x R E i w (s' - 1) vote hvote
  have hsc : M.supportCutoff S.C (s' - 1 + 1) = M.voteTime S.C s' + Δ S := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s')]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
  -- `u` is outside the adversary set at every step up to `w`'s tick (`honestActiveAt`'s first read, `hSkew`)
  have hHonT : u ∉ A.corruptedAtTime x ((M.supportCutoff S.C (s' - 1 + 1) : ℕ) : ℝ) := fun h =>
    (Finset.mem_sdiff.1 hHon).2 (Finset.mem_union_left _ h)
  have hti : x.time i ≤ (M.voteTime S.C s' : ℝ) + ΔClockBehind := (E.tick_active i w _ hi).2.2
  have hA := E.ahead_nonneg
  have hHonk : ∀ k : ℕ, k ≤ i → u ∉ A.corrupted k := by
    intro k hk
    rw [Activity.not_mem_corruptedAtTime] at hHonT
    refine hHonT k ?_
    have := (time_mono M) x R hk
    rw [hsc]; push_cast; linarith
  have huadv : vote.val_index ∉ A.corrupted i' := by rw [hvu]; exact hHonk i' hi'.le
  -- the vote is `u`'s own, sent at its tick at the vote time of slot `s' − 1`
  obtain ⟨k, t'', hki', hlk, hmk⟩ := hOwner i' _ vote hnew (Or.inl rfl) huadv
  obtain ⟨-, n', sent, hrun, hsent⟩ := (tick_send_of_honestSendAt M F R E) hlk hmk
  have hTI_k : x.tickInput vote.val_index t'' = x.st k vote.val_index := by
    show x.st (x.tickStep vote.val_index t'') vote.val_index = x.st k vote.val_index
    rw [(tickStep_eq_of_lbl M) x E hlk]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput vote.val_index t'') := by
    rw [hTI_k]
    exact (lem11_node_invariant M F S A x R E k vote.val_index (E.not_mem_corrupted_of_tick hlk)).1
  obtain ⟨ht'', -, hvs, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote
      hrun hInvT hsent
  have hslot := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E i w (s' - 1) vote hvote
  have hvt : t'' = M.voteTime S.C (s' - 1) := by
    have hslt : S.C.slot (t'' : Int) = s' - 1 := by rw [← hvs, hslot]
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s' - 1)
    rw [hslt] at ht''
    rw [← ht''] at h1
    exact_mod_cast h1.symm
  rw [hvt] at hlk hTI_k
  rw [hvu] at hmk hlk hTI_k
  obtain ⟨H_u, hHuT, hveq, hBH⟩ := hExt vote ⟨k, hlk, hmk⟩
  -- the vote's head names `H'` in `w`'s frame tree, which conflicts with `B` (`Opposes`)
  obtain ⟨H', hH', hroot, hconf⟩ := hvopp
  have hkt : x.time k ≤ x.time i := (time_mono M) x R (by omega)
  have hHuH' : H' = H_u := by
    refine hRoots H' H_u ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := i) (v := w) hw htR ((((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hH').1))
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k) (v := u) (hHonk k (by omega)) (le_trans hkt htR) (by rw [← hTI_k]; exact hHuT)) (by rw [hroot, hveq])
  rw [hHuH', conflicts_iff, compatible_iff] at hconf
  exact hconf ((compatible_iff _ _).1 hBH)

/-- **The opponents of `B` at a revocation inside the period are fewer than half of the
committee, under the compatible vote clause.** `opponents_fewer_than_half` with `VotesCompatibleAt`
in place of `VotesExtendAt`: the opponents are committee members outside the voters whose votes
are for blocks compatible with `B` (`opponent_not_compatible`).

 The one
change is the premise `hVotes`; the holders' conjunct is read at a slot `s' − 1` whose previous
votes were owed, so at most `s + k` (`owed_slot_le_k`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot of the revocation; `i`: the step of the tick; `w`: the
  revoking validator.
- `T`: the time up to which `P`'s premises are read; `hT`: the support cutoff of `s'` is at most `T`, so the committee of `s' − 1` is
  among those `P.hSleepK` covers.

The landed statement reads the opponents as the answer of the spec's `opponents` on an AC state
`A` with `w`'s pool; the twin reads them as a set `opp` of validators each with a vote among
`w`'s slot-`(s' − 1)` votes that opposes `B` (`Opposes`), what the proof uses: the record's
revocation (`LocksRevoked`) counts its opponents over `w`'s node state (`OpponentsOf`), whose
members have such votes (`exists_vote_of_mem_opponentsOf`).

Roots name blocks up to `x.time i`, the real time of `w`'s tick to the vote time of `s'`: `w`'s
block at `i` against the opponent's block at its own tick, a step before the relay of its vote into
`w`'s held votes (`M.votesHeldSet`).

Read aloud: under the compatible vote clause, the opponents of `B` at a revocation inside the period
are fewer than half of the committee. -/
theorem opponents_fewer_than_half_ofCompat (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    (P : AsyncHypsUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind) (s' i : ℕ) (w : V)
    -- the committee of slot `s' − 1` is among those `P` counts
    (hT : M.supportCutoff S.C s' ≤ T)
    (hRoots : RootsNameBlocksUntil M A x (x.time i))
    (hs' : s + 2 ≤ s')
    -- step `i` is `w`'s tick to the vote time of `s'`
    (hi : x.lbl i = Event.tick w (M.voteTime S.C s'))
    (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ (s' - 1)) :
    ∀ opp : Finset V, (∀ u ∈ opp, ∃ vote ∈ M.votesHeldSet (x.st i w) (s' - 1),
      vote.val_index = u ∧ Opposes M (x.st i w) B vote) →
      2 * |opp| < |S.P.committee (s' - 1)| := by
  intro opp hopp
  have hK := (opponent_not_compatible M F U) S A x R E hSkew hRoots ((GoldilocksCorrectness.Record.Statements.Executions.votesCastByOwner_of_unforgeability M F) S A x R E) B s' i w
    opp (by omega) hi hopp le_rfl
  by_cases hOwed : VotesOwedInPeriod M S Δs b₀ b₁ (s' - 1)
  · -- the votes of slot `s' − 2` were owed inside the period: the lock holders' majority
    have hs3 : s + 2 ≤ s' - 1 := by
      by_contra hc
      have h1 : s' - 1 - 1 ≤ s := by omega
      have h2 : M.supportCutoff S.C (s' - 1 - 1) < M.supportCutoff S.C (s + 1) := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
          (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
        have := Nat.mul_le_mul_left (4 * Δ S) h1
        have := one_le_Δ S
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have := P.hb₀
      exact absurd hOwed.1 (by omega)
    have hlt := P.hHold (s' - 1) hs3 hOwed.1 hOwed.2
    refine GoldilocksCorrectness.Proofs.Executions.double_lt_of_sdiff (fun u hu => ?_) hlt
    obtain ⟨hC, hN⟩ := hK u hu
    refine Finset.mem_sdiff.2 ⟨hC, fun hG => hN (Finset.mem_inter.1 hG).2 ?_⟩
    exact fun vote hsend => (holders_vote_compatible_of_votesCompatibleAt M F) hVotes
      ((owed_slot_le_k M F U) P.hb₁ hOwed) u hG vote hsend
  · -- otherwise every honest active voter of slot `s' − 1` voted on `B`'s chain
    have hlt := P.hSleepK s' (by omega) (le_trans P.hAnchor (by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]; exact Nat.mul_le_mul_left _ (by omega))) hT
    refine GoldilocksCorrectness.Proofs.Executions.double_lt_of_sdiff (fun u hu => ?_) hlt
    obtain ⟨hC, hN⟩ := hK u hu
    exact Finset.mem_sdiff.2 ⟨hC, fun hG => hN hG (fun vote hsend =>
      (active_vote_compatible_of_votesCompatibleAt M F) hVotes hOwed u hG vote hsend)⟩

/-- **The fgroot of a frame is an ancestor of the anchor over it.** For every set of lock entries `E`
and every time `t`, the fgroot of the frame `Φ` is `AnchorAt M Φ E t` or an ancestor of it: the
anchor is the fgroot or a block of the viable tree, whose blocks descend from the fgroot.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `E`: the lock entries; `t`: the time.

Read aloud: the walk of a duty starts from the fgroot or from a descendant of it. -/
theorem fc_root_ancestorEq_anchorAt (Φ : Frame V) (E : Finset M.LE) (t : Time) :
    Φ.fc_root.AncestorEq (AnchorAt M Φ E t) := by
  rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M Φ E t with h | h
  · rw [h]
    exact ancestorEq_refl _
  · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).2.1

/-- **The anchor over a lock holder's frame is `B` or a descendant of `B`, with the finality gadget
not contested or two past `B`.** The record form of `anchor_extends_B_of_inv_orTwoPast`
(`GoldilocksCorrectness/Proofs/Routines/Wiring.lean`), over the node state `n` satisfying the
model's node invariant and a set `E` of lock entries: when `E` holds an entry on `B` live at `t`
(`B` in the tree of `n`'s frame), every entry of `E` live at `t` is on a block compatible with `B`,
the caches of `n` are compatible with `B`, every block of `n`'s tree at a chain-state height at
least two past `B`'s descends from `B`, and `n` is not contested or its greatest chain-state height
is at least two past `B`'s, then `AnchorAt M (M.fg_to_ac n) E t` is `B` or a descendant of `B`.

Why: the fgroot is compatible with `B` (the caches); when `B` is the fgroot or an ancestor of it,
the anchor descends from the fgroot. Otherwise `B` is a block of the viable tree (a viable head
descends from `B`: the held block at the greatest chain-state height when that height is two past
`B`'s, `B` itself otherwise, `head_height_floor` being then one less than that height), locked by
the entry on `B`; so the anchor is the deepest locked block of the viable tree, locked by an entry
compatible with `B` and at least as deep as `B`, hence `B` or a descendant of `B`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `n`: the node state; `E`: the lock entries; `B`: the locked block; `t`: the time;
  `H`: the threshold of the caches.

Read aloud: the walk of a lock holder starts from `B` or from a descendant of `B`. -/
theorem anchorAt_extends_B (S : Setup V) (n : M.N) (hI : M.nodeInv S.C S.P S.X n) (E : Finset M.LE)
    (B : Block V) (t : Time) (H : ℕ)
    (hlock : ∃ e ∈ E, e.B = B ∧ t < e.d)
    (hBΦ : B ∈ (M.fg_to_ac n).tree)
    (hlocks : ∀ e ∈ E, t < e.d → e.B ∈ (M.fg_to_ac n).tree → e.B.compatible B = true)
    (hC : CachesCompatibleWith M S B H n)
    (hTwo : ∀ D ∈ n.tree, (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D)
    (hNC : M.fg_contest n = false ∨ (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C n) :
    B.AncestorEq (AnchorAt M (M.fg_to_ac n) E t) := by
  have hJB := hC.2.1
  have hFJ := hC.2.2.2.2
  -- the fgroot is compatible with `B`
  have hrB : (M.fg_to_ac n).fc_root.AncestorEq B ∨ B.AncestorEq (M.fg_to_ac n).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X n hI with
      ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hJB
    · rcases hJB with hJB | hBJ
      · exact Or.inl (ancestorEq_trans hFJ hJB)
      · exact ancestorEq_compatible hFJ hBJ
  rcases hrB with hrB | hBr
  swap
  · exact ancestorEq_trans hBr ((fc_root_ancestorEq_anchorAt M F) _ E t)
  have hBT := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hBΦ
  -- a viable head that is `B` or a descendant of `B`
  have hW : ∃ W ∈ (M.fg_to_ac n).tree ∩ (M.fg_to_ac n).viable_heads, B.AncestorEq W := by
    have hviable : ∀ W : Block V, W ∈ n.tree → B.AncestorEq W →
        M.head_height_floor n ≤ (M.chainStateOf S.C W).h →
        W ∈ (M.fg_to_ac n).tree ∩ (M.fg_to_ac n).viable_heads := by
      intro W hWT hBW hWh
      have hFW := ancestorEq_trans hBT.2 hBW
      refine Finset.mem_inter.2
        ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hWT, hFW⟩, ?_⟩
      exact ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X n hI W).2
        ⟨hWT, hFW, ancestorEq_trans hrB hBW, hWh⟩
    obtain ⟨D, hD, hDh⟩ := GoldilocksCorrectness.Record.Statements.Routines.exists_eq_hMax M (C := S.C)
      ⟨_, F.nd.nodeInv_finalized_mem_tree hI⟩
    have hfloor_le : M.head_height_floor n ≤ hMax M S.C n := by
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X n hI with
        ⟨-, -, h⟩ | ⟨-, h⟩ <;> rw [h]
      exact Nat.sub_le _ _
    by_cases h2 : (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C n
    · -- the held block at the greatest chain-state height descends from `B`, and is viable
      have hBD := hTwo D hD (by rw [hDh]; exact h2)
      exact ⟨D, hviable D hD hBD (by rw [hDh]; exact hfloor_le), hBD⟩
    · -- not contested: `head_height_floor` is one less than the greatest height, and `B` is viable
      have hNC' : M.fg_contest n = false := hNC.resolve_right h2
      have hfloor : M.head_height_floor n = hMax M S.C n - 1 := by
        rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X n hI with
          ⟨hc, -, -⟩ | ⟨-, h⟩
        · rw [hNC'] at hc
          cases hc
        · exact h
      exact ⟨B, hviable B hBT.1 (ancestorEq_refl B) (by rw [hfloor]; unfold Height at *; omega),
        ancestorEq_refl B⟩
  -- `B` is a locked block of the viable tree
  obtain ⟨e₀, he₀, he₀B, he₀d⟩ := hlock
  have hBL : B ∈ LockedViableBlocks M (M.fg_to_ac n) E t := by
    rw [GoldilocksCorrectness.Record.Proofs.Routines.mem_lockedViableBlocks]
    refine ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).2
      ⟨hBΦ, hrB, hW⟩, e₀, he₀, he₀d, by rw [he₀B]; exact hBΦ, by rw [he₀B]; exact ancestorEq_refl B⟩
  -- no two locked blocks of the viable tree share a root
  have hRL : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (LockedViableBlocks M (M.fg_to_ac n) E t) := by
    intro X hX Y hY hXY
    have hX' := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1
      ((GoldilocksCorrectness.Record.Proofs.Routines.mem_lockedViableBlocks M _ E t X).1 hX).1).1
    have hY' := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1
      ((GoldilocksCorrectness.Record.Proofs.Routines.mem_lockedViableBlocks M _ E t Y).1 hY).1).1
    exact F.nd.nodeInv_rootsNameBlocksIn hI X
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hX').1
      Y (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hY').1 hXY
  obtain ⟨X, hX⟩ := GoldilocksCorrectness.Proofs.Routines.deepest?_isSome _ ⟨B, hBL⟩ hRL
  have hanc : AnchorAt M (M.fg_to_ac n) E t = X := by
    simp only [AnchorAt, hX, ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
      Option.get_some]
  rw [hanc]
  -- `X` is locked by an entry compatible with `B`, and at least as deep as `B`
  have hXL := GoldilocksCorrectness.Proofs.Routines.deepest?_mem hX
  obtain ⟨-, e, he, hed, heT, hXe⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.mem_lockedViableBlocks M _ E t X).1 hXL
  have hXB := compatible_of_ancestorEq_compatible hXe (hlocks e he hed heT)
  have hdeep := (GoldilocksCorrectness.Proofs.Routines.mem_of_pickUnique?_eq_some hX).2
  simp only [Block.isDeepestIn, decide_eq_true_eq] at hdeep
  have hBX := hdeep B hBL
  simp only [Block.deeper, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_imp,
    decide_eq_true_eq] at hBX
  rcases (compatible_iff X B).1 hXB with hXB' | hBX'
  · have hdle := GoldilocksCorrectness.Proofs.Routines.depth_le_of_ancestorEq hXB'
    have : X = B := GoldilocksCorrectness.Proofs.Routines.eq_of_ancestorEq_of_depth hXB' (by omega)
    rw [this]
    exact ancestorEq_refl B
  · exact hBX'

/-- **A lock holder's vote inside the hand-over lock's life is on `B`'s chain, under the
compatible vote clause.** `holder_vote_extends_B_orTwoPast` with `VotesCompatibleAt` in place of
`VotesExtendAt` for the previous slot: the revocation keeps the lock on `B` because the opponents
of `B` are fewer than half of the committee (`opponents_fewer_than_half_ofCompat`).

 The
one change is the premise `hVotes`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot of the vote; `w`: the voter.
- `T`: the time up to which `P`'s premises are read; `hT`: the support cutoff of `s'` is at most `T`, so the committee of `s' − 1` is among those
  `P.hSleepK` covers.

Roots name blocks up to `w`'s own tick to `M.voteTime S.C s'`: `opponents_fewer_than_half_ofCompat`
at the revocation `w`'s tick runs, which reads `w`'s state at that step and each opponent's block at
the opponent's own earlier tick.

Read aloud: a validator holding the lock votes on `B`'s chain at every slot of the lock's life, when
the previous slot's honest votes do not conflict with `B`. -/
theorem holder_vote_extends_B_orTwoPast_ofCompat (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    (P : AsyncHypsUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind) (s' : ℕ) (w : V)
    -- the support cutoff of `s'` is at most `T`
    (hT : M.supportCutoff S.C s' ≤ T)
    -- roots name blocks among what honest validators hold up to the real time of `w`'s own tick to the vote time of `s'`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C s'))))
    (hs' : s + 2 ≤ s') (hs'k : s' ≤ s + S.C.k)
    (hInv : HolderInvAt M S x s B (x.tickStep w (M.voteTime S.C s')) w)
    (hC : CachesCompatibleWith M S B H (x.tickInput w (M.voteTime S.C s')))
    (hTwo : ∀ D ∈ (x.tickInput w (M.voteTime S.C s')).tree,
      (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D)
    (hNC : M.fg_contest (x.tickInput w (M.voteTime S.C s')) = false ∨
      (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C (x.tickInput w (M.voteTime S.C s')))
    (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ (s' - 1)) :
    ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C s') ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput w (M.voteTime S.C s')).tree,
        vote = GoldfishVote.mk w s' H_u.root ∧ B.AncestorEq H_u := by
  intro vote ⟨i, hl, hm⟩
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  have hΔ := one_le_Δ S
  have hv₃ : M.voteTime S.C s' = M.slotStart S.C s' + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
  have hss : M.slotStart S.C (s' + 1) = M.slotStart S.C s' + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hslot : S.C.slot ((M.voteTime S.C s' : ℕ) : Int) = s' := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  obtain ⟨-, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F R E) hl hm
  -- the revocation and the vote read `w`'s state at its tick step `i` (rule R3)
  have hwi : w ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hts : x.tickStep w (M.voteTime S.C s') = i := (tickStep_eq_of_lbl M) x E hl
  have hTI_i : x.tickInput w (M.voteTime S.C s') = x.st i w := by
    show x.st (x.tickStep w (M.voteTime S.C s')) w = x.st i w
    rw [hts]
  have hInvN : M.nodeInv S.C S.P S.X (x.st i w) := (lem11_node_invariant M F S A x R E i w hwi).1
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C s')) := by
    rw [hTI_i]; exact hInvN
  -- Lemma 14 over the record (the field `tick_vote_head` of `F.tk3`): the vote is `w`'s, of slot
  -- `s'`, for the end `H_u` of the walk through the viable part of `w`'s voter tree from the anchor
  -- over `w`'s frame with the lock entries the tick left (`HeadOf`); its revocation is the record's
  -- (the field `tick_voteTime_locks` of `F.tk2`)
  obtain ⟨hvt, hvi, hvs, -, hAwT, H_u, ⟨votes, support_votes, -, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote
      hrun hInvT hvote
  have hrev := F.tk2.tick_voteTime_locks S.C S.P S.X _ _ n' sent hrun hInvT hvt hAwT
  obtain ⟨τ, hτ, -⟩ := hAwT
  have hnv : (x.tickInput w (M.voteTime S.C s')).v = w := by
    rw [hTI_i]
    exact (lem11_node_invariant M F S A x R E i w hwi).2.1
  rw [hnv] at hvi
  rw [hslot] at hvs
  rw [hTI_i, hslot] at hWalk
  rw [hTI_i, hslot] at hrev
  rw [hTI_i] at hτ hC hTwo hNC
  rw [hts] at hInv hRoots
  have hvote' : vote = GoldfishVote.mk w s' H_u.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the walk's end is a block `w` holds: a block of the viable part of the voter's tree, or the
  -- anchor, which is the fgroot (the justified or the finalized block) or a block of the viable tree
  have hmemT : ∀ D ∈ (M.fg_to_ac (x.st i w)).tree, D ∈ (x.st i w).tree :=
    fun D hD => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
  have hHT : H_u ∈ (x.st i w).tree := by
    rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
    · rw [h]
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
          (M.fg_to_ac (x.st i w)) n'.lockEntries
          ((M.voteTime S.C s' : ℕ) : Int) with h' | h'
      · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), F.ndAdded.get_fc_root_eq hInvN]
        split
        · exact F.nd.nodeInv_justifiedInTree hInvN
        · exact F.nd.nodeInv_finalized_mem_tree hInvN
      · exact hmemT _ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h').1
    · have h1 := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1
      exact hmemT _ ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _
        H_u).1 h1).1
  -- the walk ends at the anchor or a descendant of it
  have hAH := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hWalk.1
  refine ⟨H_u, by rw [hTI_i]; exact hHT, hvote', ancestorEq_trans ?_ hAH⟩
  -- the anchor over `w`'s frame with the lock entries the revocation left is `B` or a descendant of
  -- `B`
  by_cases hgen : B = Block.genesis
  · rw [hgen]
    exact genesis_ancestorEq _
  -- `w`'s clock at its tick step is less than the vote time
  have hclk : x.clockValue i w ≤ M.voteTime S.C s' :=
    le_of_lt ((clockValue_lt_of_tick_awakeSince_some M F) R E hl (by omega) hτ)
  have hBT : B ∈ (x.st i w).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i w _ B
      hInv.2.2.1 hInv.2.1
  have hJB := hC.2.1
  have hFJ := hC.2.2.2.2
  by_cases hBΦ : B ∈ (M.fg_to_ac (x.st i w)).tree
  · -- the entry on `B` is live at the vote time, and the revocation keeps it
    have htd : ((M.voteTime S.C s' : ℕ) : Int) < S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
      have h1 : M.voteTime S.C s' ≤ M.voteTime S.C (s + S.C.k) := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U),
          (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U),
          (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
          (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hs'k) _
      have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s + S.C.k)
      have h3 : ((M.voteTime S.C s' : ℕ) : Int) ≤ ((M.voteTime S.C (s + S.C.k) : ℕ) : Int) := by
        exact_mod_cast h1
      have h4 := S.C.Δ_pos
      have key : ∀ a b c δ : Int, a ≤ b → b = c + δ → 0 < δ → a < c + 5 * δ := by
        intro a b c δ h1 h2 h3; omega
      exact key _ _ _ _ h3 h2 h4
    -- `B` is in the frame's tree, so not a strict ancestor of the finalized block: `w` holds the
    -- entry on `B`
    obtain ⟨e₀, he₀, heB, hed⟩ : ∃ e ∈ (x.st i w).lockEntries, M.le_B e = B ∧
        M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) :=
      hInv.1.resolve_right fun h => by
        obtain ⟨hne, hBF⟩ := ancestorStrict_iff.1 h
        exact hne (ancestorEq_antisymm hBF (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hBΦ).2)
    have hlive : M.is_live (x.st i w) ((M.voteTime S.C s' : ℕ) : Int) e₀ = true := by
      simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
      exact ⟨lt_of_lt_of_eq htd hed.symm, by show M.le_B e₀ ∈ _; rw [heB]; exact hBΦ⟩
    -- the opponents of `B` in `w`'s revocation are fewer than half of the committee
    have hopp : ∀ o : Finset V, OpponentsOf M (x.st i w) (M.votesHeldSet (x.st i w) (s' - 1))
        (M.equivocators (M.votesHeldSet (x.st i w) (s' - 1))) e₀.B o →
        2 * o.card < (S.P.committee (s' - 1)).card := by
      intro o ho
      rw [show e₀.B = B from heB] at ho
      exact (opponents_fewer_than_half_ofCompat M F U R E hSkew) P s' i w hT hRoots hs' hl hVotes o
        (fun u hu => exists_vote_of_mem_opponentsOf ho hu)
    obtain ⟨e', he', he'B, he'd⟩ := (GoldilocksCorrectness.Record.Statements.Routines.revoke_locks_keeps_entry F) e₀
      (show (s' : ℕ) ≠ 0 by omega) hrev he₀ hlive (by show M.le_B e₀ ≠ _; rw [heB]; exact hgen) hopp
    -- every entry the revocation left, live at the vote time, is on a block compatible with `B`
    have hlocks : ∀ e ∈ n'.lockEntries, ((M.voteTime S.C s' : ℕ) : Int) < e.d →
        e.B ∈ (M.fg_to_ac (x.st i w)).tree → e.B.compatible B = true := by
      intro e heA _ _
      obtain ⟨e₁, he₁, hl₁, -, heB₁, -⟩ :=
        GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved
          (show 1 ≤ (s' : ℕ) by omega) hrev e heA
      exact compatible_of_ancestorEq_compatible heB₁ (hInv.2.2.2.2 e₁ he₁ _ hclk hl₁)
    exact (anchorAt_extends_B M F) S (x.st i w) hInvN n'.lockEntries B _ H
      ⟨e', he', he'B.trans heB, lt_of_lt_of_eq htd (he'd.trans hed).symm⟩ hBΦ hlocks hC hTwo hNC
  · -- `B` is a strict ancestor of the finalized block, an ancestor of the anchor
    have hFB : ¬ (x.st i w).finalized.AncestorEq B := fun h =>
      hBΦ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hBT, h⟩)
    have hBF : B.AncestorEq (x.st i w).finalized := by
      rcases hJB with hJB | hBJ
      · exact absurd (ancestorEq_trans hFJ hJB) hFB
      · rcases ancestorEq_compatible hFJ hBJ with h | h
        · exact absurd h hFB
        · exact h
    exact ancestorEq_trans hBF (ancestorEq_trans
      ((GoldilocksCorrectness.Record.Proofs.Routines.F_ancestorEq_get_fc_root M F) S.C S.P S.X _ hInvN hFJ)
      (by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
          exact (fc_root_ancestorEq_anchorAt M F) _ _ _))

section Steps

variable {S : Setup V} {A : Activity V}

/-- **Lemma 100, the step of the lock holder's invariant, under the compatible vote
clause.** `holderInv_step` with `VotesCompatibleAt` in place of `VotesExtendAt`: the revocation
keeps the lock on `B` by `opponents_fewer_than_half_ofCompat`.

 The one change is
the premise `hVotes`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `j`: the step; `w`: the lock holder.
- `T`: the time up to which `P`'s premises are read; `hT`: the time of step `j + 1` is at most `T`;
  `hTv`: when step `j` is `w`'s tick to the vote time of a slot `s'`, the support cutoff of `s'` is
  at most `T`.
- `hjT`: when step `j` is `w`'s tick, its clock value is at least the hand-over cutoff; `hR`: when step `j` is `w`'s restart, it does not
  set `w`'s clock back.
- `hjd`: when step `j` is `w`'s tick, its clock value is less than the lock's deadline.

Roots name blocks until `x[j + 1].time`: as `holderInv_step`.

Read aloud: nothing that happens to a lock holder before the lock's deadline moves its lock or its
record off `B`'s chain, when the honest votes do not conflict with `B`. -/
theorem holderInv_step_ofCompat (U : UniformSchedule M.toSlotLayout)
    {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (P : AsyncHypsUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind) (j : ℕ) (w : V)
    -- the time of step `j + 1` is at most `T`
    (hT : x.time (j + 1) ≤ T)
    -- when step `j` is `w`'s tick to the vote time of a slot `s'`, the support cutoff of `s'` is at most `T`
    (hTv : ∀ s' : ℕ, x.lbl j = Event.tick w (M.voteTime S.C s') → M.supportCutoff S.C s' ≤ T)
    (hRoots : RootsNameBlocksUntil M A x (x.time (j + 1)))
    -- when step `j` is `w`'s tick, its clock value is at least the hand-over cutoff
    (hjT : ∀ c : ℕ, x.lbl j = Event.tick w c → M.supportCutoff S.C (s + 1) ≤ c)
    -- when step `j` is `w`'s restart, its clock value is at least `w`'s clock value before it
    (hR : ∀ (c : ℕ) (keep : Bool), x.lbl j = Event.restart w c keep → x.clockValue j w ≤ c)
    -- when step `j` is `w`'s tick, its clock value is less than the lock's deadline
    (hjd : ∀ c : ℕ, x.lbl j = Event.tick w c → c < M.voteTime S.C (s + S.C.k + 1))
    (hInv : HolderInvAt M S x s B j w)
    (hC : CachesCompatibleWith M S B H (x.st j w))
    (hVotes : ∀ s' : ℕ, s + 1 ≤ s' → M.supportCutoff S.C s' ≤ x.time (j + 1) →
      VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    HolderInvAt M S x s B (j + 1) w := by
  have hΔ := one_le_Δ S
  -- the deadline of the entry on `B` is the vote time of slot `s + k + 1`
  have hdd : ((M.voteTime S.C (s + S.C.k + 1) : ℕ) : Int) = S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U)]
    simp only [t_eq_mul]
    push_cast
    rw [Int.mul_add]
    have key : ∀ a d : Int, a + 4 * d * 1 + d = a + 5 * d := fun a d => by omega
    exact key _ _
  have htj : x.time j ≤ x.time (j + 1) := (time_mono M) x R (Nat.le_succ j)
  -- `w`'s clock value does not go back at step `j`
  have hcv : x.clockValue j w ≤ x.clockValue (j + 1) w := by
    by_cases ht : ∃ c : ℕ, x.lbl j = Event.tick w c
    · obtain ⟨c, ht⟩ := ht
      rw [x.clockValue_succ_of_tick ht]
      exact E.clockValue_le_of_set (E.not_mem_corrupted_of_tick ht) (Or.inl ht)
    by_cases hr : ∃ (c : ℕ) (keep : Bool), x.lbl j = Event.restart w c keep
    · obtain ⟨c, keep, hr⟩ := hr
      rw [x.clockValue_succ_of_restart hr]
      exact hR c keep hr
    · rw [x.clockValue_succ_of_not (fun c h => ht ⟨c, h⟩) (fun c keep h => hr ⟨c, keep, h⟩)]
  have hFF : (x.st j w).finalized.AncestorEq (x.st (j + 1) w).finalized := (F_ancestorEq_of_le M F) x R E w (Nat.le_succ j)
  have hBT : B ∈ (x.st j w).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w _ B hInv.2.2.1 hInv.2.1
  -- `B` is in the frame's tree at `j`, or a strict ancestor of the finalized block
  have hdich : B ∈ (M.fg_to_ac (x.st j w)).tree ∨
      (B.AncestorEq (x.st j w).finalized ∧ B ≠ (x.st j w).finalized) := by
    by_cases hFB : (x.st j w).finalized.AncestorEq B
    · exact Or.inl (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hBT, hFB⟩)
    · refine Or.inr ⟨?_, fun h => hFB (by rw [← h]; exact ancestorEq_refl _)⟩
      rcases hC.2.1 with hJB | hBJ
      · exact absurd (ancestorEq_trans hC.2.2.2.2 hJB) hFB
      · rcases ancestorEq_compatible hC.2.2.2.2 hBJ with h | h
        · exact absurd h hFB
        · exact h
  -- a strict ancestor of the finalized block stays one
  have hstrict : B.AncestorEq (x.st j w).finalized → B ≠ (x.st j w).finalized →
      B.ancestorStrict (x.st (j + 1) w).finalized = true := by
    intro h1 h2
    refine ancestorStrict_iff.2 ⟨fun h => h2 (ancestorEq_antisymm h1 ?_), ancestorEq_trans h1 hFF⟩
    rw [h]
    exact hFF
  have hInv1 : (∃ e ∈ (x.st j w).lockEntries, M.le_B e = B ∧ M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) ∨
      (B.AncestorEq (x.st j w).finalized ∧ B ≠ (x.st j w).finalized) := by
    rcases hInv.1 with h | h
    · exact Or.inl h
    · obtain ⟨h1, h2⟩ := ancestorStrict_iff.1 h
      exact Or.inr ⟨h2, h1⟩
  -- in the frame's tree, `w` holds the entry on `B`
  have hent : B ∈ (M.fg_to_ac (x.st j w)).tree →
      (∃ e ∈ (x.st j w).lockEntries, M.le_B e = B ∧ M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) :=
    fun hBΦ => hInv1.resolve_right fun ⟨h1, h2⟩ =>
      h2 (ancestorEq_antisymm h1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hBΦ).2)
  -- an entry `w` held at `j` and live at `j + 1` was live at `j`
  have hback : ∀ e ∈ (x.st j w).lockEntries, ∀ t : ℕ,
      M.is_live (x.st (j + 1) w) (t : Int) e = true →
      M.is_live (x.st j w) (t : Int) e = true := by
    intro e he t hl
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl ⊢
    have hT := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hl.2
    refine ⟨hl.1, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
      ⟨(lock_entry_mem_T_of_exec M F) S A x R E w j e he, ancestorEq_trans hFF hT.2⟩⟩
  -- with `B` an ancestor of the finalized block, every live entry is on a descendant of `B`
  have hc5strict : B.AncestorEq (x.st j w).finalized → ∀ e ∈ (x.st (j + 1) w).lockEntries,
      ∀ t : ℕ, x.clockValue (j + 1) w ≤ t → M.is_live (x.st (j + 1) w) (t : Int) e = true →
      e.B.compatible B = true := by
    intro hBF e _ t _ hl
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl
    exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans (ancestorEq_trans hBF hFF)
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hl.2).2))
  have hc2T := (latest_confirmed_mem_T_of_exec M F U) x R E (j + 1) w
  rcases (step_cases_period M F) x R E j w with ⟨hLE, hLC, hFB⟩ | ⟨t, hl, hmem, hcase⟩
  · -- the step keeps the lock entries, the record and the fast blocks
    refine ⟨?_, by rw [hLC]; exact hInv.2.1, hc2T, by rw [hFB]; exact hInv.2.2.2.1, ?_⟩
    · rcases hInv1 with h | ⟨h1, h2⟩
      · exact Or.inl (by rw [hLE]; exact h)
      · exact Or.inr (hstrict h1 h2)
    · intro e he t' ht' hl
      rw [hLE] at he
      exact hInv.2.2.2.2 e he t' (le_trans hcv ht') (hback e he t' hl)
  -- the tick's clock value is less than the lock's deadline and at least the hand-over cutoff
  have htt : ((t : ℕ) : Int) < S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
    rw [← hdd]
    exact_mod_cast hjd t hl
  have hjT' : M.supportCutoff S.C (s + 1) ≤ t := hjT t hl
  have hwj : w ∉ A.corrupted j := E.not_mem_corrupted_of_tick hl
  have hjt : x.clockValue j w ≤ t := E.clockValue_le_of_set hwj (Or.inl hl)
  -- the tick's three cases over the record (part 20a-B's `step_cases_period`): the expiry, the
  -- revocation of the slot of `t` from a node state awake for it (`LocksRevoked`), or the confirmation
  -- update of that slot (`ConfirmationUpdated`); a tick from a node state awake for the slot runs from
  -- `w`'s node state at step `j` (`tickInputState_eq_of_awakeSince_some`)
  rcases hcase with ⟨hLE, hLC, hFB⟩ | ⟨hvt, hAw, hrev, hLC, hFB⟩ | ⟨hct, hAw, hCU⟩
  · -- the tick deletes the expired entries only
    refine ⟨?_, by rw [hLC]; exact hInv.2.1, hc2T, by rw [hFB]; exact hInv.2.2.2.1, ?_⟩
    · rcases hInv1 with ⟨e₀, he₀, heB, hed⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨e₀, by rw [hLE]; exact Finset.mem_filter.2 ⟨he₀, lt_of_lt_of_eq htt hed.symm⟩, heB, hed⟩
      · exact Or.inr (hstrict h1 h2)
    · intro e he t' ht' hl
      rw [hLE] at he
      have he' := (Finset.mem_filter.1 he).1
      exact hInv.2.2.2.2 e he' t' (le_trans hcv ht') (hback e he' t' hl)
  · -- the revocation at the vote time of the slot `s'` of `t`
    obtain ⟨τ, hτ, -⟩ := hAw
    rw [show x.tickInput w t = x.st j w from by
      show x.st (x.tickStep w t) w = x.st j w
      rw [(tickStep_eq_of_lbl M) x E hl]] at hrev
    obtain ⟨s', hs'⟩ : ∃ s' : ℕ, S.C.slot (t : Int) = s' := ⟨_, rfl⟩
    have hvt' : t = M.voteTime S.C s' := by
      have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S s'
      rw [hs'] at hvt
      have : (t : Int) = ((M.voteTime S.C s' : ℕ) : Int) := by rw [h1]; exact hvt
      exact_mod_cast this
    rw [hs'] at hrev
    have hss : ∀ a b : ℕ, a ≤ b → M.slotStart S.C a ≤ M.slotStart S.C b := fun a b hab => by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
      exact Nat.mul_le_mul_left _ hab
    have hs2 : s + 2 ≤ s' := by
      by_contra hc
      have h1 := hss s' (s + 1) (by omega)
      have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
      have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
      have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
      omega
    -- the support cutoff of `s' − 1` is `3 * Δ S` before the vote time of `s'`, so before the tick's real time
    have hvlt : M.supportCutoff S.C (s' - 1) ≤ x.time (j + 1) := by
      have hvt1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ' M.toSlotLayout F.sched U) S (s' - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ s')] at hvt1
      have hsc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' - 1)
      have := one_le_Δ S
      have hle : M.supportCutoff S.C (s' - 1) + Δ S ≤ t := by rw [hvt']; omega
      have hle' : ((M.supportCutoff S.C (s' - 1) : ℕ) : ℝ) + (Δ S : ℝ) ≤ (t : ℝ) := by exact_mod_cast hle
      have h1 := (E.tick_active j w t hl).2.1
      have hA := E.ahead_nonneg
      have hB := E.behind_nonneg
      linarith
    refine ⟨?_, by rw [hLC]; exact hInv.2.1, hc2T, by rw [hFB]; exact hInv.2.2.2.1, ?_⟩
    · rcases hdich with hBΦ | ⟨h1, h2⟩
      · left
        obtain ⟨e₀, he₀, heB, hed⟩ := hent hBΦ
        have hlive : M.is_live (x.st j w) (t : Int) e₀ = true := by
          simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
          exact ⟨lt_of_lt_of_eq htt hed.symm, by show M.le_B e₀ ∈ _; rw [heB]; exact hBΦ⟩
        -- the opponents of `B` in `w`'s revocation are fewer than half of the committee
        have hopp : ∀ o : Finset V, OpponentsOf M (x.st j w) (M.votesHeldSet (x.st j w) (s' - 1))
            (M.equivocators (M.votesHeldSet (x.st j w) (s' - 1))) e₀.B o →
            2 * o.card < (S.P.committee (s' - 1)).card := by
          intro o ho
          rw [show e₀.B = B from heB] at ho
          exact (opponents_fewer_than_half_ofCompat M F U R E hSkew) P s' j w
            (hTv s' (by rw [← hvt']; exact hl))
            (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M htj hRoots)
            hs2 (by rw [← hvt']; exact hl)
            (hVotes (s' - 1) (by omega) hvlt) o
            (fun u hu => exists_vote_of_mem_opponentsOf ho hu)
        obtain ⟨e', he', he'B, he'd⟩ := (GoldilocksCorrectness.Record.Statements.Routines.revoke_locks_keeps_entry F) e₀
          (show (s' : ℕ) ≠ 0 by omega) hrev he₀ hlive ((lock_entry_ne_genesis_of_exec M F) x R E w j e₀ he₀) hopp
        exact ⟨e', he', he'B.trans heB, he'd.trans hed⟩
      · exact Or.inr (hstrict h1 h2)
    · intro e he t' _ _
      obtain ⟨e₁, he₁, hl₁, -, heB, -⟩ :=
        GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved
          (show 1 ≤ (s' : ℕ) by omega) hrev e he
      exact compatible_of_ancestorEq_compatible heB (hInv.2.2.2.2 e₁ he₁ t hjt hl₁)
  · -- the confirmation update at the support cutoff of the slot of `t`
    obtain ⟨τ, hτ, -⟩ := hAw
    rw [show x.tickInput w t = x.st j w from by
      show x.st (x.tickStep w t) w = x.st j w
      rw [(tickStep_eq_of_lbl M) x E hl]] at hCU
    have hs0 : S.C.slot (t : Int) ≠ 0 := by
      intro h0
      rw [h0] at hct
      have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S (s + 1)
      have h3 : @Eq Int (S.C.t_ 0) 0 := by
        rw [t_eq_mul]
        simp
      have h2 : @LT.lt Int _ 0 (S.C.t_ (s + 1)) := by
        rw [t_eq_mul]
        have := S.C.Δ_pos
        positivity
      have h4 : ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ≤ ((t : ℕ) : Int) := by exact_mod_cast hjT'
      have h5 : @LT.lt Int _ 0 S.C.Δ := S.C.Δ_pos
      have h6 : @Eq Int (t : Int) (S.C.t_ 0 + 2 * S.C.Δ) := hct
      have h7 : @Eq Int ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (S.C.t_ (s + 1) + 2 * S.C.Δ) := h1
      omega
    rcases hdich with hBΦ | ⟨h1, h2⟩
    · -- `B` in the frame's tree: the update under the live lock on `B`
      obtain ⟨e₀, he₀, heB, hed⟩ := hent hBΦ
      have hlive : M.is_live (x.st j w) (t : Int) e₀ = true := by
        simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
        exact ⟨lt_of_lt_of_eq htt hed.symm, by show M.le_B e₀ ∈ _; rw [heB]; exact hBΦ⟩
      have hin : (x.st j w).latestConfirmed ∈ (M.fg_to_ac (x.st j w)).tree :=
        ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
          ⟨hInv.2.2.1, ancestorEq_trans (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hBΦ).2 hInv.2.1⟩
      obtain ⟨hR1, hR2, hR3, -⟩ :=
        (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_with_live_lock_of_mem F) e₀ hs0 hCU he₀ hlive hin
          (by show (M.le_B e₀).AncestorEq _; rw [heB]; exact hInv.2.1)
      have hsub := ((GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_in_frame F) hCU).2.2.2
      refine ⟨Or.inl ⟨e₀, hsub e₀ he₀ (lt_of_lt_of_eq htt hed.symm), heB, hed⟩, by rw [← heB]; exact hR1, hc2T,
        by rw [← heB]; exact hR2, ?_⟩
      intro e he' t' ht' hl
      rcases hR3 e he' with h | h
      · exact hInv.2.2.2.2 e h t' (le_trans hcv ht') (hback e h t' hl)
      · rw [← heB]; exact h
    · -- `B` a strict ancestor of the finalized block: the update stays among its descendants
      obtain ⟨hR1, hR2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_in_frame F) hCU
      have hΦF : (M.fg_to_ac (x.st j w)).F = (x.st j w).finalized := (GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F) _
      rw [hΦF] at hR1
      refine ⟨Or.inr (hstrict h1 h2), ?_, hc2T, ?_, hc5strict h1⟩
      · rcases hR1 with h | h
        · rw [h]
          exact hInv.2.1
        · exact ancestorEq_trans h1 h
      · intro D hD
        rcases hR2 D hD with h | h
        · exact hInv.2.2.2.1 D h
        · exact (compatible_iff _ _).2
            (Or.inr (ancestorEq_trans h1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 h).2))

/-- **Lemma 100's step at a tick to a clock value at which the protocol does nothing but expire
locks.** When step `j` is `w`'s tick to a clock value `c'` that is no slot's vote time and no slot's
support cutoff, and less than the lock's deadline, `HolderInvAt` at `j` gives it at `j + 1`.

Why: the tick can only delete the lock entries whose deadline has passed (`step_cases_period`: the
revocation runs at a vote time and the confirmation update at a support cutoff); the entry on `B`
expires at the lock's deadline, after `c'`; the record and the fast blocks are kept; the finalized
block only grows; `w`'s clock does not go back at its own tick.

A proof-page helper: the
period induction's carry calls it for a tick of an updater at a real time before the hand-over
cutoff, where the caches premise of `holderInv_step_ofCompat` is not available.

The variables:
- `M`: the model; `F`: its facts;
- `j`: the step; `w`: the lock holder; `c'`: the clock value of its tick at `j`.

Read aloud: a lock holder's tick at which the protocol only drops expired locks keeps its lock on
`B` (or its finalized block past `B`) and its record on `B`'s chain. -/
theorem holderInv_step_idle_tick (U : UniformSchedule M.toSlotLayout)
    {s : ℕ} {B : Block V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (j : ℕ) (w : V) (c' : ℕ)
    -- step `j` is `w`'s tick to the clock value `c'`
    (hl : x.lbl j = Event.tick w c')
    -- `c'` is no slot's vote time and no slot's support cutoff
    (hno : ∀ s' : ℕ, c' ≠ M.voteTime S.C s' ∧ c' ≠ M.supportCutoff S.C s')
    -- `c'` is less than the lock's deadline
    (hjd : c' < M.voteTime S.C (s + S.C.k + 1))
    (hInv : HolderInvAt M S x s B j w) :
    HolderInvAt M S x s B (j + 1) w := by
  -- the deadline of the entry on `B` is the vote time of slot `s + k + 1`
  have hdd : ((M.voteTime S.C (s + S.C.k + 1) : ℕ) : Int) = S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U)]
    simp only [t_eq_mul]
    push_cast
    rw [Int.mul_add]
    have key : ∀ a d : Int, a + 4 * d * 1 + d = a + 5 * d := fun a d => by omega
    exact key _ _
  have hcv : x.clockValue j w ≤ x.clockValue (j + 1) w := by
    rw [x.clockValue_succ_of_tick hl]
    exact E.clockValue_le_of_set (E.not_mem_corrupted_of_tick hl) (Or.inl hl)
  have hFF : (x.st j w).finalized.AncestorEq (x.st (j + 1) w).finalized := (F_ancestorEq_of_le M F) x R E w (Nat.le_succ j)
  -- a strict ancestor of the finalized block stays one
  have hstrict : B.AncestorEq (x.st j w).finalized → B ≠ (x.st j w).finalized →
      B.ancestorStrict (x.st (j + 1) w).finalized = true := by
    intro h1 h2
    refine ancestorStrict_iff.2 ⟨fun h => h2 (ancestorEq_antisymm h1 ?_), ancestorEq_trans h1 hFF⟩
    rw [h]
    exact hFF
  have hInv1 : (∃ e ∈ (x.st j w).lockEntries, M.le_B e = B ∧ M.le_d e = (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) ∨
      (B.AncestorEq (x.st j w).finalized ∧ B ≠ (x.st j w).finalized) := by
    rcases hInv.1 with h | h
    · exact Or.inl h
    · obtain ⟨h1, h2⟩ := ancestorStrict_iff.1 h
      exact Or.inr ⟨h2, h1⟩
  -- an entry `w` held at `j` and live at `j + 1` was live at `j`
  have hback : ∀ e ∈ (x.st j w).lockEntries, ∀ t : ℕ,
      M.is_live (x.st (j + 1) w) (t : Int) e = true →
      M.is_live (x.st j w) (t : Int) e = true := by
    intro e he t hl
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl ⊢
    have hT := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hl.2
    refine ⟨hl.1, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
      ⟨(lock_entry_mem_T_of_exec M F) S A x R E w j e he, ancestorEq_trans hFF hT.2⟩⟩
  have hc2T := (latest_confirmed_mem_T_of_exec M F U) x R E (j + 1) w
  rcases (step_cases_period M F) x R E j w with ⟨hLE, hLC, hFB⟩ | ⟨t, hl', -, hcase⟩
  · refine ⟨?_, by rw [hLC]; exact hInv.2.1, hc2T, by rw [hFB]; exact hInv.2.2.2.1, ?_⟩
    · rcases hInv1 with h | ⟨h1, h2⟩
      · exact Or.inl (by rw [hLE]; exact h)
      · exact Or.inr (hstrict h1 h2)
    · intro e he t' ht' hl
      rw [hLE] at he
      exact hInv.2.2.2.2 e he t' (le_trans hcv ht') (hback e he t' hl)
  obtain rfl : t = c' := by
    rw [hl] at hl'
    exact (Event.tick.inj hl').2.symm
  have htt : ((t : ℕ) : Int) < S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
    rw [← hdd]
    exact_mod_cast hjd
  rcases hcase with ⟨hLE, hLC, hFB⟩ | ⟨hvt, -⟩ | ⟨hct, -⟩
  · -- the tick deletes the expired entries only
    refine ⟨?_, by rw [hLC]; exact hInv.2.1, hc2T, by rw [hFB]; exact hInv.2.2.2.1, ?_⟩
    · rcases hInv1 with ⟨e₀, he₀, heB, hed⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨e₀, by rw [hLE]; exact Finset.mem_filter.2 ⟨he₀, lt_of_lt_of_eq htt hed.symm⟩, heB, hed⟩
      · exact Or.inr (hstrict h1 h2)
    · intro e he t' ht' hl
      rw [hLE] at he
      have he' := (Finset.mem_filter.1 he).1
      exact hInv.2.2.2.2 e he' t' (le_trans hcv ht') (hback e he' t' hl)
  · -- a revocation runs at a vote time, which `t` is not
    exfalso
    obtain ⟨s', hs'⟩ : ∃ s' : ℕ, S.C.slot (t : Int) = s' := ⟨_, rfl⟩
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S s'
    rw [hs'] at hvt
    have : (t : Int) = ((M.voteTime S.C s' : ℕ) : Int) := by rw [h1]; exact hvt
    exact (hno s').1 (by exact_mod_cast this)
  · -- a confirmation update runs at a support cutoff, which `t` is not
    exfalso
    obtain ⟨s', hs'⟩ : ∃ s' : ℕ, S.C.slot (t : Int) = s' := ⟨_, rfl⟩
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S s'
    rw [hs'] at hct
    have : (t : Int) = ((M.supportCutoff S.C s' : ℕ) : Int) := by rw [h1]; exact hct
    exact (hno s').2 (by exact_mod_cast this)

/-- **A clock value strictly between the hand-over cutoff and one `Δ S` after it is no slot's vote
time and no slot's support cutoff.** With the uniform layout, the vote times and support cutoffs
nearest the support cutoff `c` of slot `s + 1` are `c − Δ S` (the vote time of `s + 1`), `c`,
`c + 3 · Δ S` (the vote time of `s + 2`) and `c + 4 · Δ S`.

A proof-page helper of the period induction's carry.

Read aloud: nothing is due at a clock value strictly inside the first `Δ S` after the hand-over cutoff. -/
theorem not_duty_of_cutoff_lt_lt (U : UniformSchedule M.toSlotLayout) (s c' : ℕ)
    -- `c'` is after the support cutoff of slot `s + 1`
    (hlo : M.supportCutoff S.C (s + 1) < c')
    -- `c'` is less than that cutoff plus `Δ S`
    (hhi : c' < M.supportCutoff S.C (s + 1) + Δ S) :
    ∀ s' : ℕ, c' ≠ M.voteTime S.C s' ∧ c' ≠ M.supportCutoff S.C s' := by
  intro s'
  have hss : ∀ a b : ℕ, a ≤ b → M.slotStart S.C a ≤ M.slotStart S.C b := fun a b hab => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    exact Nat.mul_le_mul_left _ hab
  have h2 : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    ring
  have hv := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  rcases le_or_gt s' (s + 1) with hle | hlt
  · have := hss s' (s + 1) hle
    constructor <;> omega
  · have := hss (s + 1 + 1) s' (by omega)
    constructor <;> omega

/-- **Lemma 100 at every step from `i₀` to `j`.** A lock holder's invariant at step `i₀` carries to
step `j + 1`, when every step from `i₀` to `j` satisfies the hypotheses of
`holderInv_step_ofCompat`: the time of step `j + 1` is at most `T`, every slot whose vote time is
at most that time has its support cutoff at most `T`, the caches of `w` at each of those steps are
compatible with `B`, and the honest votes of every slot whose support cutoff is at most the time of
step `j + 1` do not conflict with `B`.

Why: induction on the number of steps, `holderInv_step_ofCompat` at each; every step `k` from `i₀`
to `j` has its time and the time of step `k + 1` at most the time of step `j + 1`.

A proof-page helper of the period induction: clause 1 of the
period invariant is asserted at a step only when every slot whose vote time has come has reached
its support cutoff; the induction carries the invariant from such a step `i₀` over the steps from a
vote time to before its support cutoff, where clause 1 is not asserted.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `i₀`: the step the invariant is known at; `j`: the last step taken; `w`: the
  lock holder.
- `T`: the time up to which `P`'s premises are read; `hT`: the time of step `j + 1` is at most `T`;
  `hTv`: every slot to whose vote time `w` ticks at a step from `i₀` to `j` has its support cutoff
  at most `T` (per tick since F-RC57-1); `hjd`: every tick of `w` at a step from `i₀` to `j` is to a clock
  value less than the lock's deadline; `hjT`: every such tick is to a clock value at least the hand-over
  cutoff, and `hR`: no restart of `w` at those steps sets its clock back.

Roots name blocks until `x[j + 1].time`: as `holderInv_step_ofCompat` at each step.

Read aloud: a lock holder keeps the lock on `B` (or has finalized past it) and its latest confirmed
block on `B`'s chain over any run of steps before the lock's deadline, when the committees counted
on the way are among those the premises cover and the honest votes do not conflict with `B`. -/
theorem holderInv_steps_ofCompat (U : UniformSchedule M.toSlotLayout)
    {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T : ℕ}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (P : AsyncHypsUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T release ΔRedeliver ΔClockAhead ΔClockBehind) (i₀ j : ℕ) (w : V)
    (hij : i₀ ≤ j + 1)
    -- the time of step `j + 1` is at most `T`
    (hT : x.time (j + 1) ≤ T)
    -- every slot to whose vote time `w` ticks at a step from `i₀` to `j` has its support cutoff at most `T`
    (hTv : ∀ (k s' : ℕ), i₀ ≤ k → k ≤ j → x.lbl k = Event.tick w (M.voteTime S.C s') →
      M.supportCutoff S.C s' ≤ T)
    (hRoots : RootsNameBlocksUntil M A x (x.time (j + 1)))
    -- every tick of `w` at a step from `i₀` to `j` is to a clock value at least the hand-over cutoff
    --
    (hjT : ∀ (k c : ℕ), i₀ ≤ k → k ≤ j → x.lbl k = Event.tick w c → M.supportCutoff S.C (s + 1) ≤ c)
    -- no restart of `w` at a step from `i₀` to `j` sets its clock back
    (hR : ∀ (k c : ℕ) (keep : Bool), i₀ ≤ k → k ≤ j → x.lbl k = Event.restart w c keep → x.clockValue k w ≤ c)
    -- every tick of `w` at a step from `i₀` to `j` is to a clock value less than the lock's deadline
    (hjd : ∀ (k c : ℕ), i₀ ≤ k → k ≤ j → x.lbl k = Event.tick w c → c < M.voteTime S.C (s + S.C.k + 1))
    (hInv : HolderInvAt M S x s B i₀ w)
    (hC : ∀ k : ℕ, i₀ ≤ k → k ≤ j → CachesCompatibleWith M S B H (x.st k w))
    (hVotes : ∀ s' : ℕ, s + 1 ≤ s' → M.supportCutoff S.C s' ≤ x.time (j + 1) →
      VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    HolderInvAt M S x s B (j + 1) w := by
  have key : ∀ n : ℕ, i₀ + n ≤ j + 1 → HolderInvAt M S x s B (i₀ + n) w := by
    intro n
    induction n with
    | zero => intro _; simpa using hInv
    | succ n ih =>
      intro hn
      have hk1 : x.time (i₀ + n + 1) ≤ x.time (j + 1) := (time_mono M) x R (by omega)
      exact (holderInv_step_ofCompat M F U R E hSkew) P (i₀ + n) w (le_trans hk1 hT)
        (fun s' h => hTv (i₀ + n) s' (by omega) (by omega) h)
        (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M hk1 hRoots)
        (fun c h => hjT (i₀ + n) c (by omega) (by omega) h)
        (fun c keep h => hR (i₀ + n) c keep (by omega) (by omega) h)
        (fun c h => hjd (i₀ + n) c (by omega) (by omega) h) (ih (by omega))
        (hC _ (by omega) (by omega)) (fun s' hs' h => hVotes s' hs' (le_trans h hk1))
  have h := key (j + 1 - i₀) (by omega)
  rwa [show i₀ + (j + 1 - i₀) = j + 1 by omega] at h

/-- **The lock holder's invariant carries over steps that keep its confirmation state.** When `w`'s
node state at step `j` has the lock entries, saved confirmations, fast blocks and confirmed tip of its
state at an earlier step `i` (`KeepsConfirmation`), `HolderInvAt` at `i` gives it at `j`: the lock
entries and the confirmed tip are the same, the finalized block only grows (`F_ancestorEq_of_le`), the
confirmed tip is held (`latest_confirmed_mem_T_of_exec`), and an entry live at a clock value no earlier
than `w`'s clock value at `j` in the later state is live at that clock value in the earlier one, whose
clock value is at most `w`'s at `j` (`clockValue_mono`, `w` outside the adversary set at `j`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s`: the hand-over slot;
  `B`: the protected block; `i`, `j`: the steps, `i ≤ j`; `w`: the lock holder, outside the adversary set
  at `j`.

Read aloud: steps that leave a lock holder's locks and confirmations alone keep its invariant. -/
theorem holderInv_of_keepsConfirmation (U : UniformSchedule M.toSlotLayout)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {B : Block V} {i j : ℕ} {w : V} (hij : i ≤ j)
    -- `w` is outside the adversary set after `j` steps (its clock value only grows up to `j`)
    (hw : w ∉ A.corrupted j)
    (hK : KeepsConfirmation M (x.st i w) (x.st j w))
    (hInv : HolderInvAt M S x s B i w) :
    HolderInvAt M S x s B j w := by
  obtain ⟨hLE, -, hFB, hLC⟩ := hK
  have hFF : (x.st i w).finalized.AncestorEq (x.st j w).finalized := (F_ancestorEq_of_le M F) x R E w hij
  have htij : x.clockValue i w ≤ x.clockValue j w := E.clockValue_mono hij hw
  refine ⟨?_, by rw [hLC]; exact hInv.2.1, (latest_confirmed_mem_T_of_exec M F U) x R E j w,
    by rw [hFB]; exact hInv.2.2.2.1, ?_⟩
  · rcases hInv.1 with h | h
    · exact Or.inl (by rw [hLE]; exact h)
    · obtain ⟨hne, hBF⟩ := ancestorStrict_iff.1 h
      refine Or.inr (ancestorStrict_iff.2 ⟨fun he => hne (ancestorEq_antisymm hBF ?_), ancestorEq_trans hBF hFF⟩)
      rw [he]
      exact hFF
  · intro e he t ht hl
    rw [hLE] at he
    refine hInv.2.2.2.2 e he t (le_trans htij ht) ?_
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl ⊢
    have hT := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hl.2
    exact ⟨hl.1, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
      ⟨(lock_entry_mem_T_of_exec M F) S A x R E w i e he, ancestorEq_trans hFF hT.2⟩⟩

end Steps

/-! ## A reader of the original vote clause -/

/-- **No block that conflicts with `B` is a fast block of an honest active validator's update of
a slot `s' ≥ s + 1`.** The proof; the audited statement is in
`Statements/Executions/PeriodCompatCopiesStatements.lean`.
`fast_blocks_compatible_of_votes_updater_ofCompat`, an honest active validator of `s'` being an
updater of `s'` (`honestActiveAt_subset_updaterAt`), and the votes' `VotesExtendAt` giving
`VotesCompatibleAt` (`votesCompatibleAt_of_votesExtendAt`).

 the copy is on this page, which
imports that one.
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot of the update; `u`: the validator.

Roots name blocks up to `u`'s own tick to `M.supportCutoff S.C (s' + 1)`: the block of the tree of `M.fg_to_ac` of the
state that tick starts from which a supporter's vote names is compared with the block the supporter held at its own tick
to the vote time, before `u`'s tick (`hSkew`).

Read aloud: no block off `B`'s chain ever passes the fast test at anyone. -/
theorem fast_blocks_compatible_of_votes (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    (P : AsyncHyps M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind tW) (s' : ℕ) (u : V)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep u (M.supportCutoff S.C (s' + 1)))))
    (hs' : s + 1 ≤ s') (hu : u ∈ honestActiveAt M S A x s')
    (hVotes : VotesExtendAt M S A x s B Δs b₀ b₁ s') :
    ∀ D ∈ (x.tickOutput u (M.supportCutoff S.C (s' + 1))).fastBlocks,
      D.compatible B = true := by
  exact
    (fast_blocks_compatible_of_votes_updater_ofCompat M F U R E)
      ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHyps.toUntil M F) P (M.supportCutoff S.C (s' + 1))) s' u
      le_rfl hRoots hs'
      ((honestActiveAt_subset_updaterAt M F) S A x R E s' hu) ((GoldilocksCorrectness.Record.Statements.Executions.votesCompatibleAt_of_votesExtendAt M) S A x hVotes)

end GoldilocksCorrectness.Record.Proofs.Executions

