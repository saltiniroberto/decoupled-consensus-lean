module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickWindowKit
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FrameStatementsFGState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Record
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Relay
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.FrameStatements
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeSends

@[expose] public section

/-!
# RoundKit, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/RoundKit.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the kit facts the proof of Lemma 80 reads.
The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt
  supportCutoff_slot viewFreeze_cast voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (initial_eq on_ac_message_eq wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (signingHistory_initial_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor FrameShape TreeClosed VoterTree
  LocksRevoked)

open GoldilocksCorrectness.Proofs.Routines (on_block_eq slot_lt_of_ancestorEq_of_treeClosed)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_genesis_iff ancestorEq_node_iff RecordFromSent tick_record_rel)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The times -/

/-! ## A Goldfish vote of a tick -/

/-- **Kit fact, the form of a tick's Goldfish vote.** A Goldfish vote a validator `u`'s tick puts
on the wire at the vote time of slot `s'` is `u`'s, of slot `s'` (Lemma 14, with Lemma 11 for the
validator field).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the validator;
  `vote`: the vote.

Read aloud: an honest tick's vote names its own validator and slot. -/
theorem honest_vote_form (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s' : ℕ) (u : V) (vote : GoldfishVote V)
    -- `u` put `vote` on the wire at its tick at the vote time of slot `s'`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    vote.val_index = u ∧ vote.slot = s' := by
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s' + 1) = M.slotStart S.C s' + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv : M.voteTime S.C s' = M.slotStart S.C s' + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
  have hslot : S.C.slot ((M.voteTime S.C s' : ℕ) : Int) = s' := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega)
      (by omega)
  obtain ⟨i, hl, hm⟩ := hSend
  obtain ⟨-, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F R E) hl hm
  -- the tick's input state is `u`'s state at the step `i` of its tick, which satisfies the node
  -- invariant and names `u` (Lemma 11)
  have hti : x.tickInput u (M.voteTime S.C s') = x.st i u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  rw [hti] at hrun
  have hInvT := (lem11_node_invariant M F S A x R E i u (E.not_mem_corrupted_of_tick hl)).1
  obtain ⟨-, hvi, hvs, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote
      hrun hInvT hvote
  rw [(lem11_node_invariant M F S A x R E i u (E.not_mem_corrupted_of_tick hl)).2.1] at hvi
  rw [hslot] at hvs
  exact ⟨hvi, hvs⟩

/-! ## The slots along a closed tree -/

/-- **Kit fact, an attestation a tick sends is well formed.** An attestation that `v`'s tick at `t`
puts on the wire is well formed: the validator client built it at the height of the chain state of
a source in `v`'s tree (Lemma 49), which is at least `1` (Lemma 47 (a), with Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `t`: the time;
  `v`: the validator; `a`: the attestation.

Read aloud: honest ticks send well-formed attestations. -/
theorem tick_attestation_well_formed (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i t : ℕ) (v : V) (a : Attestation V)
    -- the step `i` is the tick at `t`, and put `v`'s attestation `a` on the wire
    (hl : x.lbl i = Event.tick v t)
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    M.attestation_well_formed a = true := by
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  -- the tick's input state is `v`'s state at the step `i` of its tick, which satisfies the node
  -- invariant (Lemma 11)
  have hti : x.tickInput v t = x.st i v := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  rw [hti] at hrun
  have hInvT := (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  -- Lemma 49 over the record (T8, the field `tick_attestation` of `F.tk3`): the validator client
  -- built `a` from the height of the source's chain state (`AttestationFrom`)
  obtain ⟨-, -, source, head, -, -, ⟨τ, -, -, rfl⟩, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ha
  -- that height is at least `1` (Lemma 47 (a)), and the finality pair attached, if any, is at a
  -- smaller height
  have h1 : 1 ≤ (M.chainStateOf S.C source).h :=
    ((GoldilocksCorrectness.Record.Statements.Routines.lem47_chain_state_heights M F) S.C source
      source).1.1
  refine (F.rd.attestation_well_formed_iff _).2 ⟨h1, fun q hq => ?_⟩
  change (match M.finality_pair (x.st i v) (M.chainStateOf S.C head).h_j
      (M.chainStateOf S.C head).J.root (M.chainStateOf S.C head).h_F with
    | some q => if (M.chainStateOf S.C source).h ≤ q.hf then none else some q
    | none => none) = some q at hq
  change q.hf < (M.chainStateOf S.C source).h
  cases hfp : M.finality_pair (x.st i v) (M.chainStateOf S.C head).h_j
      (M.chainStateOf S.C head).J.root (M.chainStateOf S.C head).h_F with
  | none =>
    rw [hfp] at hq
    cases hq
  | some q' =>
    rw [hfp] at hq
    dsimp only at hq
    by_cases hle : (M.chainStateOf S.C source).h ≤ q'.hf
    · rw [if_pos hle] at hq
      cases hq
    · rw [if_neg hle] at hq
      cases hq
      exact Nat.lt_of_not_le hle

/-! ## The record's contents were sent -/

/-- Every content of a validator's record at the step `i` is the content of a well-formed
attestation of that validator that its tick at a step `j < i` put on the wire, active at that
step: by induction on the step, from the initial record, which holds none, through `step_cases`
(a delivery keeps the record, and a tick writes only what it sends, `tick_record_rel`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `i`: the step.

Read aloud: at every step, every content of a validator's record is the content of a well-formed
attestation of that validator that its tick put on the wire at an earlier step, awake and honest
then. -/
theorem record_content_sent_step (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) (i : ℕ) :
    ∀ b ∈ (x.st i v).sentAttestations, ∃ (j t' : ℕ) (a : Attestation V), j < i ∧
      x.lbl j = Event.tick v t' ∧
      v ∈ A.active j ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j ∧
      a.val_index = v ∧ a.content = b ∧ M.attestation_well_formed a = true := by
  induction i with
  | zero =>
      intro b hb
      rw [(getElem_zero_st M F) x R v, (F.init.initial_sent S.C v).2] at hb
      exact absurd hb (Finset.notMem_empty b)
  | succ i ih =>
      intro b hb
      have lift : (∃ (j t' : ℕ) (a : Attestation V), j < i ∧
          x.lbl j = Event.tick v t' ∧ v ∈ A.active j ∧
          (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j ∧
          a.val_index = v ∧ a.content = b ∧ M.attestation_well_formed a = true) →
          ∃ (j t' : ℕ) (a : Attestation V), j < i + 1 ∧
          x.lbl j = Event.tick v t' ∧ v ∈ A.active j ∧
          (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j ∧
          a.val_index = v ∧ a.content = b ∧ M.attestation_well_formed a = true := by
        rintro ⟨j, t', a, hj, h⟩
        exact ⟨j, t', a, by omega, h⟩
      rcases (step_cases M F) x R E i v with h | ⟨t, n', sent, hl, hact, hrun, h, hsent⟩ |
          ⟨sm, -, -, h⟩ | ⟨⟨tRw, keepw, hlw⟩, -, h⟩
      · rw [h] at hb
        exact lift (ih b hb)
      · -- the tick signs only what it sends, as the node's validator (the field `tick_record_rel`)
        rw [h] at hb
        have hin : x.tickInput v t = x.st i v := by
          unfold Trace.tickInput
          rw [(tickStep_eq_of_lbl M) x E hl]
        rw [hin] at hrun
        rcases F.tk.tick_record_rel S.C S.P S.X _ _ n' sent hrun b hb with hb' | ⟨a, ha, hab, hav⟩
        · exact lift (ih b hb')
        · have hs := hsent _ ha
          exact ⟨i, t, a, by omega, hl, hact, hs,
            by rw [hav, (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).2.1], hab,
            (tick_attestation_well_formed M F) S A x R E i t v a hl hs⟩
      · -- a delivery keeps what the node has signed (the field `receive_Λ`)
        rw [h, show (M.receive S.C S.P S.X (x.st i v) sm.msg).sentAttestations =
          (x.st i v).sentAttestations from (F.rcv.receive_Λ S.C S.P S.X (x.st i v) sm.msg).2.2.2] at hb
        exact lift (ih b hb)
      · -- a wake keeps what the node has signed (the field `wake_readers`)
        have hw : (M.wake (x.st i v) (tRw : Int)).sentAttestations = (x.st i v).sentAttestations :=
          (F.wk.wake_readers _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        rw [h tRw keepw hlw, hw] at hb
        exact lift (ih b hb)

/-- **Kit fact, a content of an honest record was sent by its own tick.** Every content of `v`'s
anti-slashing record before `t` is the content of an attestation of `v`, well formed, that `v` put
on the wire at its tick at a time `t' < t`, active at that tick's step.

Why: `record_content_sent_step` at the step `stepBefore M x t`, whose earlier steps end before `t`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `b`: the content.

Read aloud: every content of a validator's record is the content of a well-formed attestation of
that validator, put on the wire by its own tick, awake and honest then. -/
theorem record_content_sent (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t : ℕ) (v : V) (b : AttestationContent)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `b` is a content of `v`'s record before `t`
    (hb : b ∈ (x.tickInput v t).sentAttestations) :
    ∃ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick v t' ∧ t' < t ∧
      v ∈ A.active j ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j ∧
      a.val_index = v ∧ a.content = b ∧ M.attestation_well_formed a = true := by
  by_cases hex : ∃ k : ℕ, x.lbl k = Event.tick v t
  · -- the tick input is `v`'s state at its tick `k` to `t`; every content there was sent by an earlier tick of `v`,
    -- to a clock value at most `t` (`clock_mono`, `v` honest at `k`) and not `t` (`tick_unique`)
    have hk := x.lbl_tickStep hex
    have hv : v ∉ A.corrupted (x.tickStep v t) := E.not_mem_corrupted_of_tick hk
    unfold Trace.tickInput at hb
    obtain ⟨j, t', a, hj, hlj, hact, hs, hav, hab, hwf⟩ :=
      (record_content_sent_step M F) S A x R E v (x.tickStep v t) b hb
    have hle := E.clock_mono j (x.tickStep v t) v t' t hj hv (Or.inl hlj) (Or.inl hk)
    have hne : t' ≠ t := fun h => by
      rw [h] at hlj
      exact absurd (E.tick_unique j (x.tickStep v t) v t hlj hk) (by omega)
    exact ⟨j, t', a, hlj, by omega, hact, hs, hav, hab, hwf⟩
  · -- no tick of `v` to `t`: the tick input is the initial state, whose record is empty
    have h0 : x.tickStep v t = 0 := by unfold Trace.tickStep; rw [dif_neg hex]
    unfold Trace.tickInput at hb
    rw [h0, (getElem_zero_st M F) x R v, (F.init.initial_sent S.C v).2] at hb
    exact absurd hb (Finset.notMem_empty b)

/-! ## A block held early is in the voter tree and a viable head -/

/-- `proposal_viable_head_at_tick` at a step: the voter's state read at a step `j` at or after its tick
`k` to `c`, at which it is outside the adversary set, in place of its state before the vote time of slot `s'`. When `w`'s
clock value at `k` is less than `c`, `c` is at most the view freeze of slot `s' − 1`, `w` holds `B` in its tick input to
`c`, `w`'s frame at `j` has the root `ρ` and `head_height_floor` equal to `φ`, `ρ` is `B` or an ancestor of `B`, and
`B`'s chain-state height is at least `φ`, then `B` is in `w`'s voter tree of slot `s'` at `j` and is a viable head of its
frame there.

Why: `proposal_viable_head_at_tick`'s argument, read at `j`: `B`'s stamp in `w`'s tree is before the view freeze of
slot `s' − 1` and is kept to `j`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `c`: the clock value of `w`'s tick;
  `s'`: the slot of the vote; `w`: the voter; `B`: the block; `ρ`, `φ`: the root and `head_height_floor` of `w`'s
  frame at `j`; `k`: the step of `w`'s tick to `c`; `j`: the step read.

Read aloud: a block a voter held when its clock reached a value at most the view freeze, on its root's chain at a later
step and at its `head_height_floor` there, is in its voter tree and is a viable head at that step. -/
theorem proposal_viable_head_at_tick_st (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (c s' : ℕ) (w : V) (B ρ : Block V) (φ : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- step `k` is `w`'s tick to `c`, from a clock value less than `c`, at or before
    -- step `j`
    (k j : ℕ) (hk : x.lbl k = Event.tick w c) (hlt : x.clockValue k w < c)
    (hkv : k ≤ j)
    -- `w` is outside the adversary set at `j`
    (hwv : w ∉ A.corrupted j)
    -- `w` holds `B` in its tick input to `c`
    (hBin : B ∈ (x.tickInput w c).tree)
    -- `c` is at most the view freeze of slot `s' − 1`
    (hc₀ : c ≤ M.viewFreeze S.C (s' - 1))
    -- `w`'s frame at `j` has the root `ρ` and `head_height_floor` equal to `φ`
    (hShape : FrameShape M (x.st j w) ρ φ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRoot : ρ.AncestorEq B)
    -- `B`'s chain-state height is at least `head_height_floor`
    (hφ : φ ≤ (M.chainStateOf S.C B).h) :
    B ∈ VoterTree M S.C (x.st j w) s' ∧
      B ∈ (M.fg_to_ac (x.st j w)).viable_heads := by
  have hks : x.tickStep w c = k := (tickStep_eq_of_lbl M) x E hk
  have hBk : B ∈ (x.st k w).tree := by
    have h := hBin
    rw [show x.tickInput w c = x.st k w by show x.st (x.tickStep w c) w = x.st k w; rw [hks]] at h
    exact h
  have hw : w ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
  have hle : (((c : ℕ) : Int) : Stamp) ≤ ((S.C.t_ (s' - 1) + 3 * S.C.Δ : Time) : Stamp) := by
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U)]
    exact WithBot.coe_le_coe.2 (by exact_mod_cast hc₀)
  -- `B`'s stamp in `w`'s tree at `k` is before `c`
  have hstamp : ∃ st : Stamp, (x.st k w).blockStamp B = some st ∧
      st < ((S.C.t_ (s' - 1) + 3 * S.C.Δ : Time) : Stamp) := by
    by_cases hg : B = Block.genesis
    · subst hg
      exact ⟨⊥, (genesis_stamp M F) x R E k w, lt_of_lt_of_le (WithBot.bot_lt_coe _) hle⟩
    obtain ⟨e, hek, -, -, hst⟩ := (blockStamp_entry_clock M F) R E hBk hg
    rw [(clock_eq_clockValue M F) x R (e + 1) w] at hst
    refine ⟨_, hst, lt_of_lt_of_le ?_ hle⟩
    have hm : x.clockValue (e + 1) w ≤ x.clockValue k w := E.clockValue_mono (by omega) hw
    exact WithBot.coe_lt_coe.2 (by exact_mod_cast (lt_of_le_of_lt hm hlt))
  obtain ⟨st, hst, hstlt⟩ := hstamp
  have hT : B ∈ (x.st j w).tree := (mem_T_mono M F) x R E w hkv hBk
  have hkept : (x.st j w).blockStamp B = (x.st k w).blockStamp B :=
    (blockStamp_kept M F) x R E w hkv hBk
  have hFρ : (x.st j w).finalized.AncestorEq ρ := by
    rw [← hShape.1]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E j w
  have hFB := ancestorEq_trans hFρ hRoot
  have hΦ : B ∈ (M.fg_to_ac (x.st j w)).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hT, hFB⟩
  have hInvW : M.nodeInv S.C S.P S.X (x.st j w) :=
    (lem11_node_invariant M F S A x R E j w hwv).1
  refine ⟨(GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ s' B).2
    ⟨hΦ, st, by rw [hkept]; exact hst, Or.inl hstlt⟩, ?_⟩
  exact (((GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F) S.C S.P S.X _
    hInvW _ _ hShape).2.2 B).2 ⟨hT, hFB, hRoot, hφ⟩

/-! ## A proposer's anchor is on its proposal's chain -/

/-- **Kit fact, a block held at a tick before the view freeze is in the voter tree and a viable head.**
`proposal_viable_head_at` with the block read at `w`'s tick input to a clock value `c` at most the view
freeze of slot `s' − 1`: when step `k` is `w`'s tick to `c`, `w`'s clock value there is less
than `c`, `k` is at most `w`'s last step before the vote time of slot `s'`, `w` is outside the adversary set at
that last step, `w` holds `B` in its tick input
to `c`, `w`'s frame before the vote time of slot `s'` has the root `ρ` and `head_height_floor` equal to `φ`,
`ρ` is `B` or an ancestor of `B`, and `B`'s chain-state height is at least `φ`, then `B` is in `w`'s voter
tree of slot `s'` and is a viable head of `w`'s frame then.

Why: `B` entered `w`'s tree at a step at or before `k`, stamped with `w`'s clock value after that step
(`blockStamp_entry_clock`, `clock_eq_clockValue`), at most `w`'s clock value at `k` (`clockValue_mono`,
`w` honest at its tick), less than `c`, so before the view freeze; the genesis block is stamped `⊥`
(`genesis_stamp`). `B` stays in `w`'s tree with its stamp up to the vote time (`mem_T_mono`,
`blockStamp_kept`); the finalized block is `ρ` or an ancestor of it (Lemma 46), so `B` is in the frame's
tree, and Lemma 56 makes it a viable head.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `c`: the clock value of
  `w`'s tick; `s'`: the slot of the vote; `w`: the voter; `B`: the block; `ρ`, `φ`: the root and
  `head_height_floor` of `w`'s frame; `k`: the step of `w`'s tick to `c`.

Read aloud: a block a voter held when its clock reached a value at most the view freeze, on its root's
chain and at its `head_height_floor`, is in its voter tree and is a viable head. -/
theorem proposal_viable_head_at_tick (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (c s' : ℕ) (w : V) (B ρ : Block V) (φ : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- step `k` is `w`'s tick to `c`, from a clock value less than `c`, at most `w`'s last step before the
    -- vote time of slot `s'`
    (k : ℕ) (hk : x.lbl k = Event.tick w c) (hlt : x.clockValue k w < c)
    (hkv : k ≤ x.stepBefore (M.voteTime S.C s'))
    -- `w` is outside the adversary set at its last step before that vote time
    (hwv : w ∉ A.corrupted (x.stepBefore (M.voteTime S.C s')))
    -- `w` holds `B` in its tick input to `c`
    (hBin : B ∈ (x.tickInput w c).tree)
    -- `c` is at most the view freeze of slot `s' − 1`
    (hc₀ : c ≤ M.viewFreeze S.C (s' - 1))
    -- `w`'s frame before the vote time of slot `s'` has the root `ρ` and `head_height_floor` equal to `φ`
    (hShape : FrameShape M (x.stateBefore (M.voteTime S.C s') w) ρ φ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRoot : ρ.AncestorEq B)
    -- `B`'s chain-state height is at least `head_height_floor`
    (hφ : φ ≤ (M.chainStateOf S.C B).h) :
    B ∈ VoterTree M S.C (x.stateBefore (M.voteTime S.C s') w) s' ∧
      B ∈ (M.fg_to_ac (x.stateBefore (M.voteTime S.C s') w)).viable_heads := by
  exact proposal_viable_head_at_tick_st M F U S A x R c s' w B ρ φ E k (x.stepBefore (M.voteTime S.C s')) hk hlt hkv hwv
    hBin hc₀ hShape hRoot hφ

/-- **Kit fact, the proposer's anchor is the parent of its proposal or an ancestor of it.** When
`q`'s tick at the start of slot `s''` is the step `i` and put `B'` on the wire, `q`'s anchor at that
start, read at its tick input, is `B'`'s parent or an ancestor of it.

Why: `B'`'s parent is the end of `q`'s Goldfish fork choice from its anchor (Lemma 19), a walk
(`ghost`) that ends at its start or at a descendant of it (`ghost_spec`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s''`: the slot; `i`: the step of
  `q`'s tick; `B'`: the block; `q`: the proposer.

Read aloud: the proposal's parent descends from the anchor its walk started from. -/
theorem get_anchor_ancestorEq_proposal_parent (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s'' i : ℕ) (B' : Block V) (q : V)
    -- `q`'s tick at the start of slot `s''` is the step `i`, and put `B'` on the wire
    (hl : x.lbl i = Event.tick q (M.slotStart S.C s''))
    (hsent : (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    (M.get_anchor (x.tickInput q (M.slotStart S.C s''))
      ((M.slotStart S.C s'' : ℕ) : Int)).AncestorEq B'.parent := by
  obtain ⟨hqact, n₁', sent₁, hrun₁, hB₁⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  -- Lemma 19 over the record (T7, the field `tick_proposal` of `F.tk3`), from the tick's input
  -- state, which is `q`'s state at the step `i` of its tick and satisfies the node invariant:
  -- `B'`'s parent is the end of the walk from `q`'s anchor (`PoolHeadOf`)
  have hti : x.tickInput q (M.slotStart S.C s'') = x.st i q := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvq : M.nodeInv S.C S.P S.X (x.tickInput q (M.slotStart S.C s'')) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x R E i q (E.not_mem_corrupted_of_tick hl)).1
  obtain ⟨-, -, -, -, H, votes, support, -, -, hWalk, hBdef⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₁' _ sent₁ B'
      hrun₁ hInvq hB₁
  have hpar : B'.parent = H := by rw [hBdef]; rfl
  rw [hpar]
  -- the walk ends at its start or at a descendant of it
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  obtain ⟨_, _, -, hW⟩ := hWalk
  exact GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hW.1

/-! ## The live lock entries an honest update leaves -/

omit [RootOrder] in
/-- **A strict ancestor of a held block has a smaller slot, on a node state.** In a node state
whose tree is closed under parents with every parent of an earlier slot (`TreeClosed`), a block
that is an ancestor of a block `D` of the tree, other than `D`, has a slot less than `D`'s.

Why: by induction on `D`, each parent having an earlier slot (the landed
`slot_lt_of_ancestorEq_of_treeClosed`, read on the record's tree).

The variables:
- `M`: the model; `F`: its facts;
- `P`, `X`: the values; `n`: the node state; `B`: the ancestor; `D`: the block of the tree.

Read aloud: going back along a chain of a node state's tree, the slots decrease. -/
theorem slot_lt_of_ancestorEq_of_treeClosed_node {P : Provisional V} {X : External V} {n : M.N}
    (hTC : TreeClosed M P X n) {B D : Block V}
    -- `D` is a block of the tree
    (hD : D ∈ n.tree)
    -- `B` is an ancestor of `D` other than `D`
    (hBD : B.AncestorEq D) (hne : B ≠ D) :
    B.slot < D.slot := by
  unfold TreeClosed at hTC
  induction D with
  | genesis =>
      exact absurd ((GoldilocksCorrectness.Proofs.Routines.ancestorEq_genesis_iff B).1 hBD) hne
  | node p s r votes support ats v ih =>
      rcases (GoldilocksCorrectness.Proofs.Routines.ancestorEq_node_iff B p s r votes support ats v).1
          hBD with h | h
      · exact absurd h hne
      · obtain ⟨hpT, -, -, hps⟩ := hTC.2 _ hD (fun h' => by cases h')
        have hps' : p.slot < s := hps
        by_cases hBp : B = p
        · rw [hBp]
          exact hps'
        · have := ih hpT h hBp
          exact lt_trans this hps'

/-- **Kit fact, `update_lock_entries_ancestorEq` with the liveness read at any node state.** As
`update_lock_entries_ancestorEq`, for a lock entry of the update's outcome live at the support cutoff of slot
`s + 1` in any node state `n₀`: the proof reads only the deadline half of the liveness (the entry's deadline is
after the cutoff), and the tree half from the revocation at the vote time.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment facts;
  `s`: the slot of the confirmation; `B`: the saved block; `v`: the validator; `n'`, `sent`: an outcome of `v`'s
  tick at the support cutoff of slot `s + 1`; `n₀`: the node state the liveness is read at.

Read aloud: right after an honest update that saves `B`, no lock of the updater whose deadline is after the cutoff
is past `B` or off `B`'s chain. -/
theorem update_lock_entries_ancestorEq_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (B : Block V) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to its
    -- support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    -- `(n', sent)` is an outcome of `v`'s tick at the support cutoff of slot `s + 1`, which runs
    -- the update of slot `s + 1`, from a state awake for slot `s + 1`
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    -- `n'` saves `B` as the confirmation of slot `s`
    (hSaved : M.savedConfirmation n' s = some B)
    -- `B` is a block of slot `s`
    (hBslot : B.slot = s)
    -- the live entries an outcome of `v`'s tick to the vote time of slot `s + 1` leaves, from the
    -- state that tick starts from, are compatible with `B`
    (hLocks : ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) :
    -- the liveness is read at any node state `n₀`: only its deadline half is used
    ∀ e ∈ M.lockEntries n', ∀ n₀ : M.N,
      M.is_live n₀ ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B := by
  intro e he n₀ hlive
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hv' : ∀ s : ℕ, M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc' : ∀ s : ℕ, M.supportCutoff S.C s = M.voteTime S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hss : ∀ s : ℕ, M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
      Nat.mul_one]
  -- an entry the update adds is on the saved confirmation's chain (Lemma 35)
  have hCU := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n' sent hUpdate hAwake
  rcases (GoldilocksCorrectness.Record.Statements.Routines.lem35_update_confirmation_lock_entries hCU).2
      e he with hold | ⟨-, -, -, ⟨C', hC', hBC⟩, -⟩
  swap
  · rw [Nat.add_sub_cancel] at hC'
    have hCB : C' = B := Option.some.inj (hC'.symm.trans hSaved)
    rw [← hCB]
    exact hBC
  -- an entry held in the state `v`'s tick `k'` to the support cutoff starts from
  have hlive' := hlive
  simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hlive'
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hts : x.tickStep v (M.supportCutoff S.C (s + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  -- `v`'s tick `k₃` to the vote time of slot `s + 1`, inside its window (`hSkew`), from a state awake
  -- for slot `s + 1`
  have hdR := duty_window_start_real S (s + 1)
  have hvR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s + 1 : ℕ) : ℝ) + (Δ S : ℝ) := by
    rw [hv' (s + 1), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    push_cast
    ring
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.voteTime S.C (s + 1) : ℕ) : ℝ) + (Δ S : ℝ) := by
    rw [hc' (s + 1)]
    push_cast
    ring
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hkR : (2 : ℝ) ≤ (S.C.k : ℝ) := by exact_mod_cast hk
  have hΔk : (Δ S : ℝ) ≤ 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by nlinarith
  have hw₃ := (mem_activeThroughoutToTick_of_inside M F) R E (c := M.voteTime S.C (s + 1)) hv
    (by have := hv' (s + 1); omega) (by rw [hdR, hvR]; linarith) (by rw [hcR]; linarith)
  obtain ⟨τ₃, hτ₃, hτ₃le⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hw₃ (by
    have h : ((Goldilocks.duty_window_start S.C (s + 1) : ℤ) : ℝ) <
        (((M.voteTime S.C (s + 1) : ℕ) : ℤ) : ℝ) := by
      push_cast
      rw [hdR, hvR]
      linarith
    exact_mod_cast h)
  obtain ⟨k₃, hl₃, -⟩ := Activity.mem_activeThroughoutToTick.1 hw₃
  have hts₃ : x.tickStep v (M.voteTime S.C (s + 1)) = k₃ := (tickStep_eq_of_lbl M) x E hl₃
  obtain ⟨n₃, sent₃, hok₃, hst₃, -⟩ := R.tick k₃ v _ hl₃
  have hrun₃ : .ok (n₃, sent₃) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
      ((M.voteTime S.C (s + 1) : ℕ) : Int) := by
    unfold Trace.tickInput
    rw [hts₃]
    exact hok₃
  have hAwake₃ : AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) := ⟨τ₃, hτ₃, hτ₃le⟩
  have hvtc : M.voteTime S.C (s + 1) < M.supportCutoff S.C (s + 1) := by
    have := hc' (s + 1)
    omega
  -- from the state the tick to the vote time leaves to the state the tick to the support cutoff starts
  -- from, the lock entries only shrink: no clock value strictly between is a vote time or a support
  -- cutoff of its slot (`lockEntries_tickInput_subset_tickOutput`)
  have hNoDuty : ∀ t'' : ℕ, M.voteTime S.C (s + 1) < t'' → t'' < M.supportCutoff S.C (s + 1) →
      (t'' : Int) ≠ S.C.t_ (S.C.slot t'') + S.C.Δ ∧
        (t'' : Int) ≠ S.C.t_ (S.C.slot t'') + 2 * S.C.Δ := by
    intro t'' h1 h2
    have hv1 := hv' (s + 1)
    have hc1 := hc' (s + 1)
    have hs1 := hss (s + 1)
    have hsl : S.C.slot ((t'' : ℕ) : Int) = s + 1 := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
        (by omega) (by omega)
    have hvc := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S (s + 1)
    have hcc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S
      (s + 1)
    rw [hsl]
    constructor <;> intro h <;> omega
  have hsub := (lockEntries_tickInput_subset_tickOutput M F) x R E v hvtc hl₃ hk' hNoDuty
  have he₃ : e ∈ M.lockEntries n₃ := by
    have h := hsub hold
    unfold Trace.tickOutput at h
    rw [hts₃, hst₃] at h
    exact h
  -- that tick ran the revocation of slot `s + 1`; the entry is one it left, live at the vote time
  have hRevoke := (locksRevoked_of_voteTime_outcome M F U) S A x R E (s + 1) v n₃ sent₃ hrun₃ hAwake₃
  have hlive₃ : M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
      ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true := by
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
    exact ⟨lt_trans (Int.ofNat_lt.2 hvtc) hlive'.1,
      GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_entry_mem_tree (Nat.le_add_left 1 s)
        hRevoke e he₃⟩
  rcases (compatible_iff _ _).1 (hLocks n₃ sent₃ hrun₃ hAwake₃ e he₃ hlive₃) with h | hBe
  · exact h
  -- `e`'s block is not a strict descendant of `B`: it was added at an earlier slot (Lemma 39 at `k'`)
  have he' : e ∈ (x.st k' v).lockEntries := by
    rw [← hts]
    exact hold
  obtain ⟨σ, -, hk₁, hl₁, ⟨τ, hτ, hτle⟩, h39⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem39_lock_entry_provenance M F U) S A x R k' v e
      E he'
  obtain ⟨n₁, sent₁, hrun₁, hAw₁, -⟩ := (update_state_of_tick M F U) S A x R σ v E hl₁ ⟨τ, hτ, hτle⟩
  obtain ⟨e₀, -, -, he₀T, -, -, -, hee₀, -⟩ := h39 n₁ sent₁ hrun₁ hAw₁
  have he₀T' : e₀.B ∈ (x.st (x.tickStep v (M.supportCutoff S.C (σ + 1))) v).tree :=
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 he₀T).1
  have hu₁ : v ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (σ + 1))) :=
    E.not_mem_corrupted_of_tick hl₁
  -- the slot of a block of `v`'s tree at its tick to the support cutoff of slot `σ + 1` is at most
  -- `σ + 1`: the clock value there is less than that cutoff
  have hslot₀ : e₀.B.slot ≤ σ + 1 := by
    have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout
      F.sched) S σ
    have h1 := (slot_le_clockValue_of_mem_tree M F) R E hu₁ he₀T'
    have h2 := (clockValue_lt_of_tick_awakeSince_some M F) R E hl₁ (by omega) hτ
    have h3 : S.C.slot ((x.clockValue (x.tickStep v (M.supportCutoff S.C (σ + 1))) v : ℕ) : Int) ≤
        S.C.slot ((M.supportCutoff S.C (σ + 1) : ℕ) : Int) :=
      GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast h2.le)
    have hc1 : S.C.slot ((M.supportCutoff S.C (σ + 1) : ℕ) : Int) = σ + 1 := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
        hcs.1]
    exact h1.trans (h3.trans hc1.le)
  -- the tick to the support cutoff of slot `σ + 1` comes before `k'` (`clock_mono`, `tick_unique`), so
  -- `σ + 1 ≤ s`
  have hle₁ := E.clock_mono _ _ v _ _ hk₁ (E.not_mem_corrupted_of_tick hk') (Or.inl hl₁) (Or.inl hk')
  have hne₁ : M.supportCutoff S.C (σ + 1) ≠ M.supportCutoff S.C (s + 1) := fun h => by
    have hl' : x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) =
        Event.tick v (M.supportCutoff S.C (s + 1)) := by
      rw [hl₁, h]
    have := E.tick_unique _ _ v _ hl' hk'
    omega
  have hσ : σ + 1 ≤ s := by
    by_contra h
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s + 1 ≤ σ + 1 by omega)
    have h1 := hc' (σ + 1)
    have h2 := hv' (σ + 1)
    have h3 := hc' (s + 1)
    have h4 := hv' (s + 1)
    omega
  have hBe₀ := ancestorEq_trans hBe hee₀
  by_cases hEq : B = e₀.B
  · rw [hEq]
    exact hee₀
  · -- the tree of `v`'s state is closed under parents with earlier slots (the node invariant)
    have hTC : TreeClosed M S.P S.X (x.st (x.tickStep v (M.supportCutoff S.C (σ + 1))) v) :=
      F.nd.nodeInv_treeClosed
        (lem11_node_invariant M F S A x R E (x.tickStep v (M.supportCutoff S.C (σ + 1))) v hu₁).1
    have hlt := (slot_lt_of_ancestorEq_of_treeClosed_node M F) hTC he₀T' hBe₀ hEq
    have h2 : B.slot < σ + 1 := lt_of_lt_of_le hlt hslot₀
    rw [hBslot] at h2
    exact absurd (show s < σ + 1 from h2) (by omega)

/-- **Kit fact, the live lock entries of an honest update are on its saved block's chain.** When
`v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to the support
cutoff `a` of slot `s + 1`, with the two clock bounds together less than one delay; an outcome
`(n', sent)` of `v`'s tick at `a`, from its state awake for slot `s + 1`, which runs the confirmation
update of slot `s + 1`, saves `B` as the confirmation of slot `s`; `B` is of slot `s`; and every lock
entry an outcome of `v`'s tick to the vote time of slot `s + 1` leaves, live at that vote time, is on
a block compatible with `B` — then every lock entry of `n'` live at `a` is on `B` or an ancestor of
`B`.

Why: an entry the update adds is on its saved confirmation or an ancestor of it (Lemma 35). Any
other entry is in the state `v`'s tick to `a` starts from; `v` ticks to the vote time of slot `s + 1`
before (inside its window, `hSkew`), and from the state that tick leaves to the state the tick to `a`
starts from the lock entries only shrink (`lockEntries_tickInput_subset_tickOutput`: no vote time and
no support cutoff strictly between the two clock values), so the entry is one the revocation at the
vote time left, live there, hence compatible with `B`; and it is not on a strict descendant of `B`:
it was added by an update of a slot `σ + 1` with `σ < s` on a block of `v`'s tree then (Lemma 39),
whose slot is at most `σ + 1 ≤ s` (the clock value at that tick is less than its support cutoff),
while a strict descendant of `B` has a slot greater than `B`'s.

The landed statement names the answer `A'` of the confirmation update; the twin names an outcome
of the tick at `a` from a state awake for slot `s + 1` (template A2), and reads the revocation's
clause on the outcomes of `v`'s tick to the vote time from the state it starts from (template A1,
rule R3).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of the confirmation;
- `B`: the saved block; `v`: the validator; `n'`, `sent`: an outcome of `v`'s tick at `a`.

Read aloud: right after an honest update that saves `B`, no live lock of the updater is past `B`
or off `B`'s chain. -/
theorem update_lock_entries_ancestorEq (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (B : Block V) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to its
    -- support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    -- `(n', sent)` is an outcome of `v`'s tick at the support cutoff of slot `s + 1`, which runs
    -- the update of slot `s + 1`, from a state awake for slot `s + 1`
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    -- `n'` saves `B` as the confirmation of slot `s`
    (hSaved : M.savedConfirmation n' s = some B)
    -- `B` is a block of slot `s`
    (hBslot : B.slot = s)
    -- the live entries an outcome of `v`'s tick to the vote time of slot `s + 1` leaves, from the
    -- state that tick starts from, are compatible with `B`
    (hLocks : ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) :
    ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B := by
  intro e he hlive
  exact (update_lock_entries_ancestorEq_at M F U) S A x R s B v E hSkew hv n' sent hUpdate hAwake hSaved hBslot
    hLocks e he _ hlive

end GoldilocksCorrectness.Record.Proofs.Executions

