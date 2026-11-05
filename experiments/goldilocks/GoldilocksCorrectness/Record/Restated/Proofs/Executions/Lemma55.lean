module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickWindowKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.WalkEndBridge
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas
public import GoldilocksCorrectness.Proofs.Routines.Lemma2
public import GoldilocksCorrectness.Proofs.Routines.NoRaise
public import GoldilocksCorrectness.Record.TickGoldilocks3
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.NodeTick

@[expose] public section

/-!
# Lemma55, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma55.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the node state a tick starts from has the
validator's sent record; what the attestation duty sends at the round's action time (the fields
`tick_supportCutoff_confirmation` of `F.tk2` and `tick_attestation_sent` of `F.tk3`); Lemma 55 and
its corollary, every honest validator with the honest proposal as its source attests for its height.
The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ supportCutoff_cast supportCutoff_eq
  supportCutoff_succ_times voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl tick_attest_input
  awake_since_record_awake)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

omit F in
/-- A block's depth is one more than its parent's.

The variables:
- `D`, `A`: the blocks.

Read aloud: a child is one level deeper than its parent. -/
theorem depth_of_parent? {D A : Block V} (h : D.parent? = some A) : D.depth = A.depth + 1 := by
  cases D with
  | genesis => exact absurd h (by simp [Block.parent?])
  | node p _ _ _ _ _ _ =>
    simp only [Block.parent?, Option.some.injEq] at h
    subst h
    rfl

omit F in
/-- **The walk ends somewhere.** In a finite tree, when the test `eligible` answers on every block
of `tree` and the score answers on every block of `tree` on which the test answers `true`, the walk
from any block `A`, at any tie-break, ends at some block.

Why: the walk steps only to a child, one level deeper, and the blocks of `tree` have a greatest
depth; from a block with an eligible child in `tree`, the set of the highest-scoring eligible
children is not empty (the scores answer), so the tie-break's pick is a walk step; from a block
with none, the test answers `false` on every child, and the walk ends there.

The variables:
- `tree`: the tree walked; `score`: the score; `eligible`: the test; `A`: the start.

Read aloud: the walk from any block ends. -/
theorem exists_walkEnd [GoldilocksCorrectness.Statements.Routines.TieBreak V] (tree : Finset (Block V))
    (score : Block V → DRE ℕ) (eligible : Block V → DRE Bool)
    -- the test answers on every block of the tree
    (he : ∀ D ∈ tree, ∃ b : Bool, eligible D = .ok b)
    -- the score answers on every block of the tree the test accepts
    (hs : ∀ D ∈ tree, eligible D = .ok true → ∃ k : ℕ, score D = .ok k) (A : Block V) :
    ∃ H : Block V, GoldilocksCorrectness.Statements.Routines.WalkEnd tree score eligible A H := by
  classical
  suffices h : ∀ m : ℕ, ∀ A : Block V, tree.sup Block.depth + 1 - A.depth ≤ m →
      ∃ H : Block V, GoldilocksCorrectness.Statements.Routines.WalkEnd tree score eligible A H from h _ A le_rfl
  intro m
  induction m with
  | zero =>
    intro A hA
    refine ⟨A, Relation.ReflTransGen.refl, fun D hD hp => ?_⟩
    have h1 : D.depth ≤ tree.sup Block.depth := Finset.le_sup (f := Block.depth) hD
    have h2 := depth_of_parent? hp
    omega
  | succ m ih =>
    intro A hA
    by_cases hex : ∃ D ∈ tree, D.parent? = some A ∧ eligible D = .ok true
    · obtain ⟨D₀, hD₀, hp₀, he₀⟩ := hex
      let cands := tree.filter fun D => D.parent? = some A ∧ eligible D = .ok true
      have hne : cands.Nonempty := ⟨D₀, Finset.mem_filter.2 ⟨hD₀, hp₀, he₀⟩⟩
      let f : Block V → ℕ := fun D => if h : ∃ k : ℕ, score D = .ok k then h.choose else 0
      have hf : ∀ D ∈ tree, eligible D = .ok true → score D = .ok (f D) := by
        intro D hD hDe
        have hk := hs D hD hDe
        simp only [f, dif_pos hk]
        exact hk.choose_spec
      obtain ⟨Dm, hDm, hmax⟩ := Finset.exists_max_image cands f hne
      obtain ⟨hDmt, hDmp, hDme⟩ := Finset.mem_filter.1 hDm
      have hHEC : (GoldilocksCorrectness.Statements.Routines.highestEligibleChildren tree score eligible A).Nonempty := by
        refine ⟨Dm, GoldilocksCorrectness.Proofs.Routines.mem_highestEligibleChildren_iff.2
          ⟨hDmt, hDmp, hDme, f Dm, hf Dm hDmt hDme, fun D' hD' hp' he' k' hk' => ?_⟩⟩
        have h1 := hmax D' (Finset.mem_filter.2 ⟨hD', hp', he'⟩)
        rw [hf D' hD' he'] at hk'
        cases hk'
        exact h1
      have hCmem := GoldilocksCorrectness.Statements.Routines.TieBreak.tieBreak_mem _ hHEC
      obtain ⟨hCt, hCp, hCe, -⟩ := GoldilocksCorrectness.Proofs.Routines.mem_highestEligibleChildren_iff.1 hCmem
      have hstep : GoldilocksCorrectness.Statements.Routines.WalkStep tree score eligible A
          (GoldilocksCorrectness.Statements.Routines.TieBreak.tieBreak (GoldilocksCorrectness.Statements.Routines.highestEligibleChildren tree score eligible A)) :=
        ⟨hCt, hCp, hCe, fun D hD _ => he D hD, fun D hD _ hDe => hs D hD hDe, rfl⟩
      have hd1 := depth_of_parent? hCp
      have hd2 : (GoldilocksCorrectness.Statements.Routines.TieBreak.tieBreak
          (GoldilocksCorrectness.Statements.Routines.highestEligibleChildren tree score eligible A)).depth ≤ tree.sup Block.depth :=
        Finset.le_sup (f := Block.depth) hCt
      obtain ⟨H, hH⟩ := ih (GoldilocksCorrectness.Statements.Routines.TieBreak.tieBreak
        (GoldilocksCorrectness.Statements.Routines.highestEligibleChildren tree score eligible A)) (by omega)
      exact ⟨H, Relation.ReflTransGen.head hstep hH.1, hH.2⟩
    · refine ⟨A, Relation.ReflTransGen.refl, fun D hD hp => ?_⟩
      obtain ⟨b, hb⟩ := he D hD
      cases b with
      | false => exact hb
      | true => exact absurd ⟨D, hD, hp, hb⟩ hex

omit F in
/-- **The walk of the attestation duty ends somewhere.** When no two blocks of the tree of
`M.fg_to_ac n` share a root, the walk counting `n`'s votes of slot `s'` from any block `A₀`, at the
model's tie-break, ends at some block `H` (`PoolHeadOf`): the Goldfish score and test answer on
every block (`goldfish_score_ok`, `goldfish_eligible_answers`).

The variables:
- `M`: the model;
- `C`: the configuration; `n`: the node state; `A₀`: the start; `t`: the time; `s'`: the slot.

Read aloud: the duty's walk from any block ends. -/
theorem exists_poolHeadOf (C : Config) (n : M.N)
    -- no two blocks of the tree of `M.fg_to_ac n` share a root
    (hRoots : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn (M.fg_to_ac n).tree)
    (A₀ : Block V) (t : Time) (s' : Slot) :
    ∃ H : Block V, GoldilocksCorrectness.Record.Statements.Routines.PoolHeadOf M C n A₀ t s' H := by
  classical
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  obtain ⟨H, hH⟩ := exists_walkEnd (M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree)
    (goldfish_score (M.fg_to_ac n) (M.votesHeldSet n s')
      ((M.votesHeldSet n s').filter fun vote => ∃ y : Stamp, GoldilocksCorrectness.Record.Statements.Routines.ResolvesAt M n vote y) s')
    (goldfish_eligible C (M.fg_to_ac n) t (M.votesHeldSet n s')
      ((M.votesHeldSet n s').filter fun vote => ∃ y : Stamp, GoldilocksCorrectness.Record.Statements.Routines.ResolvesAt M n vote y) s')
    (fun D _ => GoldilocksCorrectness.Proofs.Routines.goldfish_eligible_answers C hRoots t _ _ s' D)
    (fun D _ _ => GoldilocksCorrectness.Proofs.Routines.goldfish_score_ok hRoots _ _ s' D) A₀
  exact ⟨H, _, _, ⟨rfl, fun vote => Finset.mem_filter⟩, hH⟩

/-- The node state a tick starts from has the validator's anti-slashing record, read through its
four readers (the targets, the timeouts, the locks and the attestations sent), and its validator:
it is the state before `t` with `v`'s wake and deliveries at `t` applied (`tickInput_eq_fold`), and
neither writes them (`foldl_keeps_signingHistory`, `foldl_keeps_validator`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator.

Read aloud: the state a tick starts from has the validator's sent record and its validator. -/
theorem tickInputState_record {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) (ht : 1 ≤ t) (hv : v ∈ A.activeAtTime x t) :
    M.sentTarget (x.tickInput v t) = M.sentTarget (x.tickInput v t) ∧
      M.sentTimeout (x.tickInput v t) = M.sentTimeout (x.tickInput v t) ∧
      M.sentLock (x.tickInput v t) = M.sentLock (x.tickInput v t) ∧
      (x.tickInput v t).sentAttestations = (x.tickInput v t).sentAttestations ∧
      (x.tickInput v t).v = (x.tickInput v t).v := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Kit fact, what the duty sends.** Under Lemma 55's hypotheses other than the record's, some
justification height `h_j`, justified root `J` and finalization height `h_F`, with `J` the root of
`B`'s `T_h` when `h_j` is `B`'s height, are such that every attestation the validator client of
`v`'s state before the support cutoff of slot `s + 1` builds (`AttestationFrom`) from the height
and the root of `B`'s `T_h` and `(h_j, J, h_F)` is put on the wire by `v` at its tick at that
cutoff.

Over the record, the update is an outcome `(n', sent)` of the tick at the cutoff, from a state
awake for slot `s + 1`, that saves `B` as a fast block with every live lock entry on `B`'s chain.
The outcome the step took may be another one of the model's tick; it saves `B` too, holds it as a
fast block and has its live lock entries on `B`'s chain, since both outcomes update the
confirmation from the same state (`ConfirmationUpdated`) and the update's walk ends at one block.
The duty's head is the end of its walk from the anchor (`exists_poolHeadOf`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `n'`, `sent`: an outcome of `v`'s tick at the cutoff.

Read aloud: `v`'s tick at the round's action time sends what the client builds for `B`'s height
and `T_h` from the head the duty reads. -/
theorem attestation_duty_sends_at_source (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (r s : ℕ) (B : Block V) (v : V) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hs : s = r * S.C.R)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    (hSaved : M.savedConfirmation n' s = some B)
    (hFast : B ∈ M.fastBlocks n')
    (hLocks : ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hViable : B ∈ M.viable_tree (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree) :
    ∃ (h_j : Height) (J : BlockId) (h_F : Height),
      (h_j = (M.chainStateOf S.C B).h → J = (M.chainStateOf S.C B).T_h.root) ∧
      ∀ a : Attestation V,
        GoldilocksCorrectness.Record.Statements.Routines.AttestationFrom M (x.tickInput v (M.supportCutoff S.C (s + 1))) v (M.chainStateOf S.C B).h
          (M.chainStateOf S.C B).T_h.root h_j J h_F a →
        ∃ i : ℕ, x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
          (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  obtain ⟨hslotM, -, hActionM, hCutoffM⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_times M.toSlotLayout F.sched U) S r s hs
  -- the slot of the cutoff, read by the spec's `S.C.slot` (the tick's facts read it so)
  have hslot : S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast, ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact hslotM
  have hCutoff : ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = S.C.t_ (S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int)) + 2 * S.C.Δ := by
    rw [hslot]
    rw [hslotM] at hCutoffM
    exact hCutoffM
  have hAction : ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = S.C.a_ (S.C.round (S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int))) := by
    rw [hslot]
    rw [hslotM] at hActionM
    exact hActionM
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔpos := S.C.Δ_pos
  have hc1 : 1 ≤ M.supportCutoff S.C (s + 1) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U)]
    omega
  have hdw : M.dutyWindowStart S.C (s + 1) < M.supportCutoff S.C (s + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_lt_supportCutoff M.toSlotLayout F.sched) S s
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  -- `v`'s own tick to the cutoff, which ends its window
  obtain ⟨k', hl, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨τ, hτ, -⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
    ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout F.sched U)
      S (s + 1))
  -- the tick starts from `v`'s state before the cutoff: its input has a wake time, so no restart of
  -- `v` comes between
  have hti : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k' v := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hvk : v ∉ A.corrupted k' :=
    Activity.not_mem_corrupted_of_mem_active (E.tick_active k' v _ hl).1
  -- the outcome the tick step took
  obtain ⟨n'', sent'', hrun0, -, hsent0⟩ := R.tick k' v _ hl
  have hrun : .ok (n'', sent'') ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) := by
    rw [hti]
    exact hrun0
  have hwire : ∀ o ∈ sent'', (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k' + 1) - x.sent k' := by
    intro o ho
    rw [hsent0, add_tsub_cancel_left]
    exact Multiset.mem_map.2 ⟨o, Multiset.mem_coe.2 ho, rfl⟩
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) := by
    rw [hti]; exact ((lem11_node_invariant M F S A x R E k' v) hvk).1
  have hXv : (x.tickInput v (M.supportCutoff S.C (s + 1))).v = v := by
    rw [hti]; exact ((lem11_node_invariant M F S A x R E k' v) hvk).2.1
  have hAw : GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int)) := by
    rw [hslot]
    exact hAwake
  -- both outcomes update the confirmation of slot `s + 1` from that state
  have hcu' := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hUpdate hInv hCutoff hAw
  have hcu'' := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n'' sent'' hrun hInv hCutoff hAw
  rw [hslot] at hcu' hcu''
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hsub : s + 1 - 1 = s := Nat.add_sub_cancel s 1
  -- the hypotheses' outcome saves `B` as a fast block, and no live lock entry vetoes `B`
  have hS' : n'.savedConfirmation (s + 1 - 1) = some B := by
    rw [hsub]
    exact hSaved
  obtain ⟨hW, hel, hveto1, hveto0⟩ := GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_saved_some hs1 hcu' hS'
  have hnv : M.live_lock_vetoes (x.tickInput v (M.supportCutoff S.C (s + 1))) ((M.supportCutoff S.C (s + 1) : ℕ) : Int) B = false := by
    cases hvt : M.live_lock_vetoes (x.tickInput v (M.supportCutoff S.C (s + 1))) ((M.supportCutoff S.C (s + 1) : ℕ) : Int) B with
    | false => rfl
    | true =>
      have h0 : M.fastBlocks n' = ∅ := (hveto1 hvt).1
      rw [h0] at hFast
      exact absurd hFast (Finset.notMem_empty B)
  -- the step's outcome saves `B` too: the update's walk ends at one block
  obtain ⟨-, H, hWH, hSH, -, -, -⟩ := hcu''.resolve_left fun h0 => absurd h0.1 (Nat.succ_ne_zero s)
  have hHB : H = B := GoldilocksCorrectness.Proofs.Routines.walkEnd_eq_of_walkSteps hW.1 hW.2 hWH
  have hS'' : n''.savedConfirmation (s + 1 - 1) = some B := by
    rw [hSH, hHB, if_pos hel]
  obtain ⟨-, -, -, hveto0''⟩ := GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_saved_some hs1 hcu'' hS''
  have hFast'' : B ∈ n''.fastBlocks := ((hveto0'' hnv).2.1 B).2 (((hveto0 hnv).2.1 B).1 hFast)
  have hAnc := GoldilocksCorrectness.Record.Proofs.Routines.fast_blocks_ancestorEq_saved (Nat.succ_ne_zero s) hcu'' hS''
  obtain ⟨⟨e₀, he₀, he₀B, he₀d⟩, hBΦ⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.lock_entry_of_saved_fast (Nat.succ_ne_zero s) hcu'' hS'' hFast''
  -- the new lock's deadline is after the cutoff
  have hdl : ((M.supportCutoff S.C (s + 1) : ℕ) : Int) < S.C.t_ (s + 1 - 1 + S.C.k) + 5 * S.C.Δ := by
    rw [hsub, (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
    have h1 : S.C.t_ (s + 1) ≤ S.C.t_ (s + S.C.k) := by
      simp only [GoldilocksCorrectness.Proofs.Routines.t_eq_mul]
      have hk := S.C.k_ge_two
      exact Int.mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : s + 1 ≤ s + S.C.k))
        (Int.mul_nonneg (by decide) (le_of_lt S.C.Δ_pos))
    have key : ∀ a b d : Int, a ≤ b → 0 < d → a + 2 * d < b + 5 * d := by
      intro a b d h1 h2
      omega
    exact key _ _ _ h1 hΔpos
  -- the step's outcome's lock entries live at the cutoff are on `B`'s chain: an unexpired entry of
  -- the state is kept in `n'`, and the update's new lock is on a block lockable under `B`
  have hLocks'' : ∀ e ∈ n''.lockEntries, ((M.supportCutoff S.C (s + 1) : ℕ) : Int) < e.d →
      e.B ∈ (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree → e.B.AncestorEq B := by
    intro e he hd hT
    rcases GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_entries_cases hcu'' e he with ⟨heX, -⟩ |
        ⟨-, H', hSH', -, hLk, -⟩
    · refine hLocks e (GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_entries_keep hcu' e heX hd) ?_
      rw [F.rd.is_live_eq]
      simp [hd, hT]
    · rw [hS''] at hSH'
      obtain rfl := Option.some.inj hSH'
      exact hLk.2.2.1
  -- the source is `B`, the anchor is `B`, and every block the duty's walk reaches descends from `B`
  have hsrc := GoldilocksCorrectness.Record.Statements.Routines.lem48_attestation_source (x.tickInput v (M.supportCutoff S.C (s + 1))) n'' B hFast'' hAnc hViable
  obtain ⟨-, hdesc⟩ := GoldilocksCorrectness.Record.Statements.Routines.lem48b_anchor_is_locked_block (M := M)
    (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))) n''.lockEntries ((M.supportCutoff S.C (s + 1) : ℕ) : Int) B
    ⟨e₀, he₀, by rw [he₀d]; exact hdl, by rw [he₀B]; exact hBΦ,
      by rw [he₀B]; exact GoldilocksCorrectness.Proofs.Routines.ancestorEq_refl B⟩ hLocks'' hViable
  -- the duty's head: the end of its walk from the anchor
  obtain ⟨head, hhead⟩ := exists_poolHeadOf M S.C (x.tickInput v (M.supportCutoff S.C (s + 1)))
    ((GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E
      (x.tickStep v (M.supportCutoff S.C (s + 1))) v)
    (GoldilocksCorrectness.Record.Statements.Routines.AnchorAt M (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))) n''.lockEntries ((M.supportCutoff S.C (s + 1) : ℕ) : Int)) ((M.supportCutoff S.C (s + 1) : ℕ) : Int)
    (S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
  have hBh : B.AncestorEq head := by
    obtain ⟨vs, svs, -, hWE⟩ := hhead
    exact hdesc _ _ head hWE.1
  refine ⟨(M.chainStateOf S.C head).h_j, (M.chainStateOf S.C head).J.root,
    (M.chainStateOf S.C head).h_F, fun h => ?_, fun a ha => ?_⟩
  · rw [(GoldilocksCorrectness.Record.Statements.Executions.J_eq_T_h_of_same_height M F) S.C B head hBh h]
  · have hsent := F.tk3.tick_attestation_sent S.C S.P S.X _ _ n'' sent'' a B head hrun hInv
      hAction hAw hsrc hhead (by rw [hXv]; exact ha)
    exact ⟨_, hl, hwire _ hsent⟩

/-- **Lemma 55, every honest validator with the honest proposal as its source attests for its
height.** The proof; the audited statement is in
`Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `n'`, `sent`: an outcome of `v`'s tick at the support cutoff
  of slot `s + 1`.

Read aloud: an honest validator whose update saves the honest proposal as fast attests for its
height, or has already. -/
theorem lem55_honest_validator_attests_for_height (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (r s : ℕ) (B : Block V) (v : V) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hs : s = r * S.C.R)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    (hSaved : M.savedConfirmation n' s = some B)
    (hFast : B ∈ M.fastBlocks n')
    (hLocks : ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hViable : B ∈ M.viable_tree (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree)
    (hRecord : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      ((x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
          some (M.chainStateOf S.C B).T_h.root ∧
        ∀ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
          b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) :
    (∃ (i : ℕ) (a : Attestation V), x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = v ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root) ∨
    (∃ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
      b.h = (M.chainStateOf S.C B).h ∧ b.T = (M.chainStateOf S.C B).T_h.root) := by
  obtain ⟨h_j, J, h_F, hJ, hsend⟩ := (attestation_duty_sends_at_source M F U) S A x R r s B v E
    hs hv n' sent hUpdate hAwake hSaved hFast hLocks hViable
  rcases ((GoldilocksCorrectness.Record.Statements.Routines.lem50_attestation_sent_at_source F) _ v _ _ h_j J h_F hRecord hJ
      ((GoldilocksCorrectness.Record.Statements.Executions.target_sent_of_exec M F) S A x R E (x.tickStep v (M.supportCutoff S.C (s + 1))) v) ((GoldilocksCorrectness.Record.Statements.Executions.sent_target_recorded_of_exec M F) S A x R E (x.tickStep v (M.supportCutoff S.C (s + 1))) v)
      ((GoldilocksCorrectness.Record.Statements.Executions.timeout_recorded_of_exec M F) S A x R E (x.tickStep v (M.supportCutoff S.C (s + 1))) v)).1 with
    ⟨a, hbuilt, hav, hah, haT⟩ | ⟨-, b, hb, hbh, hbT⟩
  · obtain ⟨i, hl, hm⟩ := hsend a hbuilt
    exact Or.inl ⟨i, a, hl, hm, hav, hah, haT⟩
  · exact Or.inr ⟨b, hb, hbh, hbT⟩

/-- **Corollary of Lemma 55, a fresh height gets a target.** The proof; the audited statement is
in `Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `n'`, `sent`: an outcome of `v`'s tick at the support cutoff
  of slot `s + 1`.

Read aloud: at a height it has not attested at, that validator sends a target for the proposal's
height. -/
theorem lem55_target_of_fresh_height (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (r s : ℕ) (B : Block V) (v : V) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hs : s = r * S.C.R)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    (hSaved : M.savedConfirmation n' s = some B)
    (hFast : B ∈ M.fastBlocks n')
    (hLocks : ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hViable : B ∈ M.viable_tree (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree)
    (hRecord : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      ((x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
          some (M.chainStateOf S.C B).T_h.root ∧
        ∀ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
          b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root))
    (hFresh : ∀ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
      b.h ≠ (M.chainStateOf S.C B).h) :
    ∃ (i : ℕ) (a : Attestation V), x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = v ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root ∧
      a.τ = false := by
  obtain ⟨h_j, J, h_F, hJ, hsend⟩ := (attestation_duty_sends_at_source M F U) S A x R r s B v E
    hs hv n' sent hUpdate hAwake hSaved hFast hLocks hViable
  have htimeout : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentTimeout
      (M.chainStateOf S.C B).h = false := by
    cases h : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentTimeout (M.chainStateOf S.C B).h with
    | false => rfl
    | true =>
        obtain ⟨b, hb, hbh, -⟩ := (((GoldilocksCorrectness.Record.Statements.Executions.recordConsistent_of_exec M F) S A x R E
          (x.tickStep v (M.supportCutoff S.C (s + 1))) v).timeoutRec _).1 h
        exact absurd hbh (hFresh b hb)
  have htarget : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentTarget
      (M.chainStateOf S.C B).h = none := by
    cases h : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentTarget (M.chainStateOf S.C B).h with
    | none => rfl
    | some T =>
        obtain ⟨b, hb, hbh, -⟩ := (GoldilocksCorrectness.Record.Statements.Executions.target_sent_of_exec M F) S A x R E (x.tickStep v (M.supportCutoff S.C (s + 1))) v _ _ h
        exact absurd hbh (hFresh b hb)
  obtain ⟨a, hbuilt, hav, hah, haT, hτ⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem50_attestation_sent_at_source F) _ v _ _ h_j J h_F
      hRecord hJ ((GoldilocksCorrectness.Record.Statements.Executions.target_sent_of_exec M F) S A x R E (x.tickStep v (M.supportCutoff S.C (s + 1))) v)
      ((GoldilocksCorrectness.Record.Statements.Executions.sent_target_recorded_of_exec M F) S A x R E (x.tickStep v (M.supportCutoff S.C (s + 1))) v)
      ((GoldilocksCorrectness.Record.Statements.Executions.timeout_recorded_of_exec M F) S A x R E (x.tickStep v (M.supportCutoff S.C (s + 1))) v)).2 hFresh htimeout htarget
  obtain ⟨i, hl, hm⟩ := hsend a hbuilt
  exact ⟨i, a, hl, hm, hav, hah, haT, hτ⟩


end GoldilocksCorrectness.Record.Proofs.Executions

