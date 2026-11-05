module
public import GoldilocksCorrectness.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Statements.Executions.NoRaiseStatements
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-! A Goldilocks node reads time through its clock
`n.t`, which only its tick sets (`Goldilocks/Node.lean`, `tick`'s step 2), and stamps every block
it admits (`on_block` through `ac_on_block`) and every Goldfish vote it admits
(`on_goldfish_vote`) with its clock. In an execution `x` of `GoldilocksCorrectness.Wiring.protocol
S`, which ticks at every reading, the clock of an honest awake validator reads the execution's
time, and the stamp of an admitted object is the time of the step that
admitted it.

## The relation

- `StampsAt n n'`: every block of `n'`'s tree that is not in `n`'s, and every vote `n'` holds under
  a slot that `n` does not hold under it, is stamped `n'.t` in `n'`.

## What is proved

- per routine: `on_block_stamps`, `on_ac_message_stamps`, `on_attestation_stamps`,
  `receive_stamps`, `propose_block_step`, `attest_step`, `tick_step`;
- per step: `tickInputState_S`, `tickInputState_A`, `tickInputState_t`, `tick_step_outcome`,
  `step_cases`, `step_stamps`, `tick_step_clock`, `step_clock_of_not_tick`;
- along an execution: `clock_le_time`, `clock_keep`, `clock_current`,
  `slot_current_at_delivery`, `clock_eq_time_of_changed`;
- the stamps: `blockStamp_step`, `voteStamp_step`, `blockStamp_eq`, `voteStamp_eq` (the delivery
  form), `blockStamp_entry`, `voteStamp_entry`, `genesis_stamp`; on the node states before a time,
  `blockStamp_lt_iff`, `voteStamp_lt_iff`, `blockStamp_before`, `voteStamp_before`.

`clock_current` and the stamp equalities take no `TimeDiverges`; the theorems on the node states
before a time take it.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_keeps fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (ACGrows ACStampsAt ACStampsAt.refl SlotKeyed
  SlotKeyed.of_poolKeyed ac_on_block_grows ac_on_tick_grows on_goldfish_vote_grows)

open GoldilocksCorrectness.Proofs.Routines (StampsAt StampsAt.congr_left StampsAt.refl StepFrom
  on_ac_message_step on_attestation_step on_block_step tick_step)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq fgState_initial_eq initial_eq
  mem_pool_iff wake_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_step)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The relation -/

section Relation

end Relation

/-! ## The routines -/

section Routines

variable [RootOrder]

end Routines

/-! ## The steps -/

section Steps

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg TickAllAwakeWake
  tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react
  applyNodeStepResult_getElem receive_getElem nodeStep_iff_exists)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol step_tick_iff step_wake_iff step_recv_iff)

variable [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- The pool of every validator is filed by slot, at every step (Lemma 11).

The variables:
- `x`: the execution; `i`: the step; `v`: the validator. -/
theorem slotKeyed_of_exec (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    SlotKeyed (x[i][v].st).A :=
  SlotKeyed.of_poolKeyed
    (GoldilocksCorrectness.Statements.Executions.lem11_node_invariant S Sched x i v).1.1

/-- Every validator starts from Goldilocks's initial node state.

The variables:
- `x`: the execution; `v`: the validator. -/
theorem getElem_zero_st (x : AtomicExec (protocol S) Sched) (v : V) :
    x[0][v].st = initial S.C v := by
  obtain ⟨-, hn, -⟩ := x.init
  show (x.cfg 0)[v].st = _
  rw [hn v]
  rfl

/-- The node state a tick starts from has the validator's FG state and AC state, and a clock at
most the validator's framework clock: a wake writes `awakeSince` and sets the clock to the framework
clock, and a stored clock is at most the framework clock (Lemma 11).

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator. -/
theorem tickInputState_frame (x : AtomicExec (protocol S) Sched) (i t : ℕ) (v : V) :
    (tickInputState x i t v).S = (x[i][v].st).S ∧ (tickInputState x i t v).A = (x[i][v].st).A ∧
      (tickInputState x i t v).t ≤ (x[i][v].clock : Int) := by
  unfold tickInputState
  split
  · rw [wake_eq]
    exact ⟨rfl, rfl, le_rfl⟩
  · exact ⟨rfl, rfl,
      (GoldilocksCorrectness.Statements.Executions.lem11_node_invariant S Sched x i v).2.2⟩

/-- **At the tick of every awake validator at `t`, a validator awake and outside the adversary set
at `t` holds the answer of an `.ok` outcome of its tick**, from `tickInputState`.

Why: the atomic step gives the validator a tick step from `tickInputState`; by `step_tick_iff` it
is an answer of the tick, or the state kept when the tick has no answer, and the second is
excluded because the tick never fails (`ticksSucceed_of_exec`).

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator.

Read aloud: after its tick, the validator holds a node state its tick could answer. -/
theorem tick_step_outcome (x : AtomicExec (protocol S) Sched) {i t : ℕ} {v : V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    -- `v` is awake and outside the adversary set at `t`
    (hv : v ∈ Sched.awake (t : Int)) (hadv : v ∉ Sched.adv (t : Int)) :
    ∃ (n' : NodeState V) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ (tick S.C S.P S.X (tickInputState x i t v) (t : Int)).outcomes ∧
        x[i + 1][v].st = n' := by
  have hmem : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) := Finset.mem_sdiff.2 ⟨hv, hadv⟩
  have hs := x.step i
  rw [hl] at hs
  obtain ⟨-, w, tk, hw, htk, hc⟩ := hs
  have hwv : (w v).state = tickInputState x i t v := by
    have hw' := hw v
    unfold TickAllAwakeWake at hw'
    unfold tickInputState
    split at hw'
    · rename_i he
      rw [if_pos he, (step_wake_iff S v _ _ _ _).1 hw']
      rfl
    · rename_i he
      rw [if_neg he, hw']
      rfl
  have htk' := (step_tick_iff S v t _ _ _).1 (htk v hmem)
  rw [hwv] at htk'
  have hst : x[i + 1][v].st = (tk v).state := by
    show (x.cfg (i + 1))[v].st = _
    rw [hc]
    exact congrArg Framework.StsMultisetLog.Local.st (tickAllAwakeUpdate_getElem_react hmem)
  rcases htk' with ⟨n', sent, hok, hres⟩ | ⟨hno, -⟩
  · exact ⟨n', sent, hok, by rw [hst, hres]⟩
  · obtain ⟨q, hq⟩ :=
      (GoldilocksCorrectness.Statements.Executions.ticksSucceed_of_exec S Sched x i t v hl hv
        hadv).exists_ok
    exact absurd hq (hno q)

/-- What a step does to a validator's node state: it keeps it; or it is the tick of every awake
validator at a time `t` at which the validator is awake and outside the adversary set, and the
validator holds the answer of an `.ok` outcome of its tick; or it delivers a signed message to the
validator, awake and outside the adversary set at the step's time, and the validator holds what
`receive` leaves.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: only the validator's own tick and a delivery to it change its node state. -/
theorem step_cases (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    x[i + 1][v].st = x[i][v].st ∨
      (∃ (t : ℕ) (n' : NodeState V) (sent : List (NamedObject V)),
        x.lbl i = AtomicAction.tickAllAwake t ∧
        v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
        .ok (n', sent) ∈ (tick S.C S.P S.X (tickInputState x i t v) (t : Int)).outcomes ∧
        x[i + 1][v].st = n') ∨
      (∃ sm : SignedMsg V (NamedObject V), x.lbl i = AtomicAction.deliver v sm ∧
        v ∈ Sched.awake (x[i].time : Int) ∧ v ∉ Sched.adv (x[i].time : Int) ∧
        x[i + 1][v].st = Goldilocks.Sts.receive S.C S.P S.X x[i][v].st sm.msg) := by
  have hs := x.step i
  cases hl : x.lbl i with
  | tickAllAwake t =>
      by_cases hmem : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
      · obtain ⟨n', sent, hok, hst⟩ :=
          tick_step_outcome x hl (Finset.mem_sdiff.1 hmem).1 (Finset.mem_sdiff.1 hmem).2
        exact Or.inr (Or.inl ⟨t, n', sent, rfl, hmem, hok, hst⟩)
      · left
        rw [hl] at hs
        obtain ⟨-, w, tk, -, -, hc⟩ := hs
        show (x.cfg (i + 1))[v].st = _
        rw [hc, tickAllAwakeUpdate_getElem_st_of_not_react hmem]
        rfl
  | deliver p m =>
      rw [hl] at hs
      obtain ⟨he, hr⟩ := hs
      obtain ⟨res, hp, hc⟩ := (nodeStep_iff_exists _ p (.recv m) _ _).1 hr
      by_cases hpv : p = v
      · subst hpv
        refine Or.inr (Or.inr ⟨m, rfl, he.2.1, he.2.2, ?_⟩)
        show (x.cfg (i + 1))[p].st = _
        rw [hc, applyNodeStepResult_getElem, if_pos rfl]
        rw [(step_recv_iff S _ _ _ _ _ _).1 hp]
        show Goldilocks.Sts.receive S.C S.P S.X
          (Framework.StsMultisetLog.receive p m (x.cfg i))[p].st m.msg = _
        rw [receive_getElem, if_pos rfl]
        rfl
      · left
        show (x.cfg (i + 1))[v].st = _
        rw [hc, applyNodeStepResult_getElem, if_neg hpv, receive_getElem, if_neg hpv]
        rfl
  | custom p ev => exact ev.elim
  | adversarial p m =>
      left
      rw [hl] at hs
      obtain ⟨-, hc⟩ := hs
      show (x.cfg (i + 1))[v].st = _
      rw [hc]
      rfl
  | forward p m =>
      left
      rw [hl] at hs
      obtain ⟨-, hc⟩ := hs
      show (x.cfg (i + 1))[v].st = _
      rw [hc]
      rfl

/-- Across a step, every block and vote a validator adds is stamped with the clock the step leaves
it at.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator. -/
theorem step_stamps (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    StampsAt (x[i][v].st) (x[i + 1][v].st) := by
  have hk := slotKeyed_of_exec x i v
  rcases step_cases x i v with h | ⟨t, n', sent, -, -, hok, h⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]
    exact StampsAt.refl _
  · rw [h]
    obtain ⟨hS, hA, -⟩ := tickInputState_frame x i t v
    have hk' : SlotKeyed (tickInputState x i t v).A := by rw [hA]; exact hk
    exact StampsAt.congr_left hS hA
      (DREBPost.of_outcome (tick_step S.C S.P S.X _ (t : Int) hk') hok).2.2.1
  · rw [h]
    exact (receive_step S.C S.P S.X _ sm.msg hk).2.2.1

/-- The tick of every awake validator at `t` sets the clock of every validator awake and outside
the adversary set at `t` to `t`.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator. -/
theorem tick_step_clock {x : AtomicExec (protocol S) Sched} {i t : ℕ} {v : V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    -- `v` is awake and outside the adversary set at `t`
    (hv : v ∈ Sched.awake (t : Int)) (hadv : v ∉ Sched.adv (t : Int)) :
    (x[i + 1][v].st).t = (t : Int) := by
  obtain ⟨n', sent, hok, hst⟩ := tick_step_outcome x hl hv hadv
  have hk : SlotKeyed (tickInputState x i t v).A := by
    rw [(tickInputState_frame x i t v).2.1]
    exact slotKeyed_of_exec x i v
  rw [hst]
  exact (DREBPost.of_outcome (tick_step S.C S.P S.X _ (t : Int) hk) hok).2.2.2

/-- A step other than the tick of every awake validator keeps every validator's clock.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator. -/
theorem step_clock_of_not_tick (x : AtomicExec (protocol S) Sched) {i : ℕ}
    -- the step `i` is not the tick of every awake validator at any time
    (hl : ∀ t, x.lbl i ≠ AtomicAction.tickAllAwake t) (v : V) :
    (x[i + 1][v].st).t = (x[i][v].st).t := by
  rcases step_cases x i v with h | ⟨t, -, -, hl', -⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]
  · exact absurd hl' (hl t)
  · rw [h]
    exact (receive_step S.C S.P S.X _ sm.msg (slotKeyed_of_exec x i v)).2.2.2

end Steps

/-! ## The clock along an execution -/

section Clock

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg tickAllAwake_of_time
  atomic_clock_le_time)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- No validator's clock runs ahead of the execution's time: the node's clock is at most the
framework's clock for it (Lemma 11), which is at most the configuration's time.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: a node's clock never reads a time the execution has not reached. -/
theorem clock_le_time (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    ((x[i][v].st).t : Int) ≤ (x[i].time : Int) :=
  le_trans (GoldilocksCorrectness.Statements.Executions.lem11_node_invariant S Sched x i v).2.2
    (by exact_mod_cast atomic_clock_le_time x i v)

/-- From a step to a later one with no tick of every awake validator between them, a validator's
clock is kept.

The variables:
- `x`: the execution; `v`: the validator; `j ≤ i`: the two steps. -/
theorem clock_keep (x : AtomicExec (protocol S) Sched) (v : V) {j i : ℕ} (hji : j ≤ i)
    -- no step from `j` to `i` is a tick of every awake validator
    (hno : ∀ m : ℕ, j ≤ m → m < i → ∀ t : ℕ, x.lbl m ≠ AtomicAction.tickAllAwake t) :
    (x[i][v].st).t = (x[j][v].st).t := by
  induction i, hji using Nat.le_induction with
  | base => rfl
  | succ i hji ih =>
      rw [step_clock_of_not_tick x (hno i hji (by omega)) v]
      exact ih (fun m h1 h2 => hno m h1 (by omega))

/-- The clock is current: a validator awake and outside the adversary
set at a step's time has its clock at that time. At a time `t ≥ 1`, the tick at `t` set it, and no
later step before the next tick changes it; at the time `0`, no tick has run and the initial node
state's clock is `0`.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: an honest awake validator's clock reads the current time. -/
theorem clock_current {x : AtomicExec (protocol S) Sched}
    {i : ℕ} {v : V}
    -- `v` is awake at the step's time
    (hAwake : v ∈ Sched.awake (x[i].time : Int))
    -- `v` is outside the adversary set at the step's time
    (hHonest : v ∉ Sched.adv (x[i].time : Int)) :
    (x[i][v].st).t = (x[i].time : Int) := by
  rcases Nat.eq_zero_or_pos x[i].time with h0 | hpos
  · -- no tick has run: every tick moves the time to at least `1`
    have hno : ∀ m : ℕ, 0 ≤ m → m < i → ∀ t : ℕ, x.lbl m ≠ AtomicAction.tickAllAwake t := by
      intro m _ hm t hl
      have h1 := (time_of_lbl_tickAllAwake x hl).2
      have h2 := (time_of_lbl_tickAllAwake x hl).1
      have h3 := time_mono x (show m + 1 ≤ i by omega)
      omega
    rw [clock_keep x v (Nat.zero_le i) hno, getElem_zero_st, h0, initial_eq]
    rfl
  · obtain ⟨j, hj, hlj, hj1, -⟩ := tickAllAwake_of_time x i rfl (by omega)
    have htick := tick_step_clock hlj hAwake hHonest
    have hno : ∀ m : ℕ, j + 1 ≤ m → m < i → ∀ t : ℕ, x.lbl m ≠ AtomicAction.tickAllAwake t := by
      intro m hm1 hm2 t hl
      have h1 := (time_of_lbl_tickAllAwake x hl).1
      have h2 := (time_of_lbl_tickAllAwake x hl).2
      have h3 := time_mono x hm1
      have h4 := time_mono x (show m + 1 ≤ i by omega)
      omega
    rw [clock_keep x v (show j + 1 ≤ i by omega) hno]
    exact htick

/-- The receiver's clock is current at a delivery: a delivery is only
to a validator awake and outside the adversary set. So is its slot.

The variables:
- `x`: the execution; `j`: the step of the delivery; `v`: the receiver; `sm`: the signed message.

Read aloud: a validator receives every message with its clock at the current time, in the current
slot. -/
theorem slot_current_at_delivery {x : AtomicExec (protocol S) Sched}
    {j : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)}
    -- the step `j` delivers `sm` to `v`
    (hl : x.lbl j = AtomicAction.deliver v sm) :
    (x[j][v].st).t = (x[j].time : Int) ∧ S.C.slot (x[j][v].st).t = S.C.slot (x[j].time : Int) := by
  have hs := x.step j
  rw [hl] at hs
  obtain ⟨he, -⟩ := hs
  have h := clock_current (i := j) he.2.1 he.2.2
  exact ⟨h, by rw [h]⟩

/-- A step that changes a validator's node state leaves its clock at
the step's time: the change is the validator's own tick, or a delivery to it while it is awake and
outside the adversary set.

The variables:
- `x`: the execution; `k`: the step; `v`: the validator. -/
theorem clock_eq_time_of_changed {x : AtomicExec (protocol S) Sched}
    {k : ℕ} {v : V}
    -- the step changes `v`'s node state
    (hchg : x[k + 1][v].st ≠ x[k][v].st) :
    (x[k + 1][v].st).t = (x[k + 1].time : Int) := by
  rcases step_cases x k v with h | ⟨t, -, -, hl, hmem, -⟩ | ⟨sm, hl, hv, hadv, h⟩
  · exact absurd h hchg
  · rw [(time_of_lbl_tickAllAwake x hl).2]
    exact tick_step_clock hl (Finset.mem_sdiff.1 hmem).1 (Finset.mem_sdiff.1 hmem).2
  · have hnt : ∀ t, x.lbl k ≠ AtomicAction.tickAllAwake t := by
      intro t h'
      rw [hl] at h'
      cases h'
    rw [h, (receive_step S.C S.P S.X _ sm.msg (slotKeyed_of_exec x k v)).2.2.2,
      time_succ_of_not_tickAllAwake x hnt]
    exact clock_current hv hadv

end Clock

/-! ## The stamps along an execution -/

section Stamps

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- A block that enters a validator's tree at a step is stamped with the time that step ends at.

The variables:
- `x`: the execution; `k`: the step; `v`: the validator; `B`: the block.

Read aloud: a block is stamped with the time of the step that admitted it. -/
theorem blockStamp_step {x : AtomicExec (protocol S) Sched}
    {k : ℕ} {v : V} {B : Block V}
    -- `B` is not in `v`'s tree before the step
    (hnk : B ∉ (x[k][v].st).S.T)
    -- `B` is in `v`'s tree after the step
    (hk1 : B ∈ (x[k + 1][v].st).S.T) :
    (x[k + 1][v].st).A.timestamp_block B = some (((x[k + 1].time : ℕ) : Int) : Stamp) := by
  rw [(step_stamps x k v).1 B hk1 hnk,
    clock_eq_time_of_changed (fun h => hnk (h ▸ hk1))]

/-- A Goldfish vote that enters a validator's pool of a slot at a step is stamped with the time
that step ends at.

The variables:
- `x`: the execution; `k`: the step; `v`: the validator; `s`: the slot; `vote`: the vote.

Read aloud: a vote is stamped with the time of the step that admitted it. -/
theorem voteStamp_step {x : AtomicExec (protocol S) Sched}
    {k : ℕ} {v : V} {s : Slot} {vote : GoldfishVote V}
    -- `vote` is not in `v`'s pool of slot `s` before the step
    (hnk : vote ∉ (x[k][v].st).A.pool s)
    -- `vote` is in `v`'s pool of slot `s` after the step
    (hk1 : vote ∈ (x[k + 1][v].st).A.pool s) :
    (x[k + 1][v].st).A.timestamp_vote vote = some (((x[k + 1].time : ℕ) : Int) : Stamp) := by
  rw [(step_stamps x k v).2 s vote ((mem_pool_iff _ _ _).1 hk1)
      (fun h => hnk ((mem_pool_iff _ _ _).2 h)),
    clock_eq_time_of_changed (fun h => hnk (h ▸ hk1))]

/-- A block that a delivery to a validator admits into its tree is stamped with the time of the
delivery.

The variables:
- `x`: the execution; `d`: the step of the delivery; `v`: the receiver; `sm`: the signed message;
  `B`: the block.

Read aloud: a block a delivery admits is stamped with the delivery's time. -/
theorem blockStamp_eq {x : AtomicExec (protocol S) Sched}
    {d : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)}
    {B : Block V}
    -- the step `d` delivers `sm` to `v`
    (hl : x.lbl d = AtomicAction.deliver v sm)
    -- `B` is not in `v`'s tree before the delivery
    (hnd : B ∉ (x[d][v].st).S.T)
    -- `B` is in `v`'s tree after the delivery
    (hd1 : B ∈ (x[d + 1][v].st).S.T) :
    (x[d + 1][v].st).A.timestamp_block B = some (((x[d].time : ℕ) : Int) : Stamp) := by
  rw [blockStamp_step hnd hd1,
    time_succ_of_not_tickAllAwake x (fun t h => by rw [hl] at h; cases h)]

/-- A Goldfish vote that a delivery to a validator admits into its pool of a slot is stamped with
the time of the delivery.

The variables:
- `x`: the execution; `d`: the step of the delivery; `v`: the receiver; `sm`: the signed message;
  `s`: the slot; `vote`: the vote.

Read aloud: a vote a delivery admits is stamped with the delivery's time. -/
theorem voteStamp_eq {x : AtomicExec (protocol S) Sched}
    {d : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)}
    {s : Slot} {vote : GoldfishVote V}
    -- the step `d` delivers `sm` to `v`
    (hl : x.lbl d = AtomicAction.deliver v sm)
    -- `vote` is not in `v`'s pool of slot `s` before the delivery
    (hnd : vote ∉ (x[d][v].st).A.pool s)
    -- `vote` is in `v`'s pool of slot `s` after the delivery
    (hd1 : vote ∈ (x[d + 1][v].st).A.pool s) :
    (x[d + 1][v].st).A.timestamp_vote vote = some (((x[d].time : ℕ) : Int) : Stamp) := by
  rw [voteStamp_step hnd hd1,
    time_succ_of_not_tickAllAwake x (fun t h => by rw [hl] at h; cases h)]

/-- A block other than the genesis block that a validator's tree holds entered it at an earlier
step, and is stamped with the time that step ends at.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator; `B`: the block;
- `k`: the step at which `B` entered `v`'s tree. -/
theorem blockStamp_entry {x : AtomicExec (protocol S) Sched}
    {i : ℕ} {v : V} {B : Block V}
    -- `v`'s tree holds `B` at `i`
    (hB : B ∈ (x[i][v].st).S.T)
    -- `B` is not the genesis block
    (hg : B ≠ Block.genesis) :
    ∃ k < i, B ∉ (x[k][v].st).S.T ∧ B ∈ (x[k + 1][v].st).S.T ∧
      (x[i][v].st).A.timestamp_block B = some (((x[k + 1].time : ℕ) : Int) : Stamp) := by
  classical
  have hex : ∃ m : ℕ, B ∈ (x[m][v].st).S.T := ⟨i, hB⟩
  have h0 : B ∉ (x[0][v].st).S.T := by
    rw [getElem_zero_st, initial_eq, fgState_initial_eq]
    intro h
    exact hg (Finset.mem_singleton.1 h)
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ i := Nat.find_min' hex hB
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnk : B ∉ (x[k][v].st).S.T := Nat.find_min hex (by omega)
  have hk1 : B ∈ (x[k + 1][v].st).S.T := hk ▸ Nat.find_spec hex
  refine ⟨k, by omega, hnk, hk1, ?_⟩
  rw [blockStamp_kept x v (show k + 1 ≤ i by omega) hk1]
  exact blockStamp_step hnk hk1

/-- A Goldfish vote that a validator's pool of a slot holds entered it at an earlier step, and is
stamped with the time that step ends at.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator; `s`: the slot; `vote`: the vote;
- `k`: the step at which `vote` entered `v`'s pool of slot `s`. -/
theorem voteStamp_entry {x : AtomicExec (protocol S) Sched}
    {i : ℕ} {v : V} {s : Slot} {vote : GoldfishVote V}
    -- `v`'s pool of slot `s` holds `vote` at `i`
    (hv : vote ∈ (x[i][v].st).A.pool s) :
    ∃ k < i, vote ∉ (x[k][v].st).A.pool s ∧ vote ∈ (x[k + 1][v].st).A.pool s ∧
      (x[i][v].st).A.timestamp_vote vote = some (((x[k + 1].time : ℕ) : Int) : Stamp) := by
  classical
  have hex : ∃ m : ℕ, vote ∈ (x[m][v].st).A.pool s := ⟨i, hv⟩
  have h0 : vote ∉ (x[0][v].st).A.pool s := by
    rw [getElem_zero_st, initial_eq, acState_initial_eq]
    intro h
    exact absurd ((mem_pool_iff _ _ _).1 h) List.not_mem_nil
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ i := Nat.find_min' hex hv
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnk : vote ∉ (x[k][v].st).A.pool s := Nat.find_min hex (by omega)
  have hk1 : vote ∈ (x[k + 1][v].st).A.pool s := hk ▸ Nat.find_spec hex
  refine ⟨k, by omega, hnk, hk1, ?_⟩
  rw [voteStamp_kept x v (show k + 1 ≤ i by omega) hk1]
  exact voteStamp_step hnk hk1

/-- The genesis block is stamped `⊥`, earlier than every time, at every step.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator. -/
theorem genesis_stamp (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    (x[i][v].st).A.timestamp_block Block.genesis = some ⊥ := by
  have h0 : (Block.genesis : Block V) ∈ (x[0][v].st).S.T := by
    rw [getElem_zero_st, initial_eq, fgState_initial_eq]
    exact Finset.mem_singleton_self _
  rw [blockStamp_kept x v (Nat.zero_le i) h0, getElem_zero_st]
  simp [initial_eq, acState_initial_eq, genesisStamp]

end Stamps

/-! ## The stamps on the node states before a time -/

section Before

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- On the node states before two times, a block's stamp tells which of them holds it, when
every time is reached: a block of the tree before `τ` is stamped strictly
before `t₀` exactly when the tree before `t₀` holds it. The genesis block is stamped `⊥` and is
held by every tree; another block is stamped with the time of the step that admitted it
(`blockStamp_entry`), and that step comes before `stepBefore x t₀` exactly when its time is before
`t₀` (`lt_stepBefore_iff`).

The variables:
- `x`: the execution; `τ`: the time of the node state read; `t₀`: the cutoff; `v`: the
  validator; `B`: the block;
- `st`: `B`'s stamp in the node state before `τ`.

Read aloud: in `v`'s node state before `τ`, a block is stamped strictly before `t₀` exactly when
`v`'s node state before `t₀` already holds it. -/
theorem blockStamp_lt_iff {x : AtomicExec (protocol S) Sched}
    -- every time is reached
    (hdiv : TimeDiverges x.toTrace) {τ t₀ : ℕ} {v : V} {B : Block V}
    -- `v`'s tree before `τ` holds `B`
    (hB : B ∈ (stateBefore x τ v).S.T) :
    (∃ st : Stamp, (stateBefore x τ v).A.timestamp_block B = some st ∧
        st < (((t₀ : ℕ) : Int) : Stamp)) ↔
      B ∈ (stateBefore x t₀ v).S.T := by
  show (∃ st : Stamp, (x[stepBefore x τ][v].st).A.timestamp_block B = some st ∧ _) ↔
    B ∈ (x[stepBefore x t₀][v].st).S.T
  by_cases hg : B = Block.genesis
  · subst hg
    refine ⟨fun _ => GoldilocksCorrectness.Statements.Executions.genesis_mem_T_of_exec
      S Sched x _ v, fun _ => ⟨⊥, genesis_stamp x _ v, ?_⟩⟩
    exact WithBot.bot_lt_coe _
  · obtain ⟨k, -, hnk, hk1, hst⟩ := blockStamp_entry hB hg
    rw [hst]
    constructor
    · rintro ⟨st, hs, hlt⟩
      cases hs
      have ht : x[k + 1].time < t₀ := by exact_mod_cast WithBot.coe_lt_coe.1 hlt
      exact mem_T_mono x v ((lt_stepBefore_iff x hdiv).2 ht) hk1
    · intro hBa
      have hka : k < stepBefore x t₀ := by
        by_contra hle
        exact hnk (mem_T_mono x v (Nat.le_of_not_lt hle) hBa)
      refine ⟨_, rfl, WithBot.coe_lt_coe.2 ?_⟩
      exact_mod_cast (lt_stepBefore_iff x hdiv).1 hka

/-- On the node states before two times, a Goldfish vote's stamp tells which of them holds it,
when every time is reached: a vote of the pool of a slot before `τ` is
stamped strictly before `t₀` exactly when the pool of that slot before `t₀` holds it. The vote is
stamped with the time of the step that admitted it (`voteStamp_entry`), and that step comes before
`stepBefore x t₀` exactly when its time is before `t₀` (`lt_stepBefore_iff`).

The variables:
- `x`: the execution; `τ`: the time of the node state read; `t₀`: the cutoff; `v`: the
  validator; `s`: the slot; `vote`: the vote;
- `st`: the vote's stamp in the node state before `τ`.

Read aloud: in `v`'s node state before `τ`, a vote is stamped strictly before `t₀` exactly when
`v`'s node state before `t₀` already holds it. -/
theorem voteStamp_lt_iff {x : AtomicExec (protocol S) Sched}
    -- every time is reached
    (hdiv : TimeDiverges x.toTrace) {τ t₀ : ℕ} {v : V} {s : Slot} {vote : GoldfishVote V}
    -- `v`'s pool of slot `s` before `τ` holds `vote`
    (hv : vote ∈ (stateBefore x τ v).A.pool s) :
    (∃ st : Stamp, (stateBefore x τ v).A.timestamp_vote vote = some st ∧
        st < (((t₀ : ℕ) : Int) : Stamp)) ↔
      vote ∈ (stateBefore x t₀ v).A.pool s := by
  show (∃ st : Stamp, (x[stepBefore x τ][v].st).A.timestamp_vote vote = some st ∧ _) ↔
    vote ∈ (x[stepBefore x t₀][v].st).A.pool s
  obtain ⟨k, -, hnk, hk1, hst⟩ := voteStamp_entry hv
  rw [hst]
  constructor
  · rintro ⟨st, hs, hlt⟩
    cases hs
    have ht : x[k + 1].time < t₀ := by exact_mod_cast WithBot.coe_lt_coe.1 hlt
    exact pool_mono x v ((lt_stepBefore_iff x hdiv).2 ht) s hk1
  · intro hva
    have hka : k < stepBefore x t₀ := by
      by_contra hle
      exact hnk (pool_mono x v (Nat.le_of_not_lt hle) s hva)
    refine ⟨_, rfl, WithBot.coe_lt_coe.2 ?_⟩
    exact_mod_cast (lt_stepBefore_iff x hdiv).1 hka

/-- Every block of a validator's tree before a time is stamped strictly before that time: `⊥`
for the genesis block, and the time of its admission otherwise.

The variables:
- `x`: the execution; `t`: the time; `v`: the validator; `B`: the block;
- `st`: the block's stamp.

Read aloud: a block held before `t` was stamped before `t`. -/
theorem blockStamp_before {x : AtomicExec (protocol S) Sched}
    -- every time is reached
    (hdiv : TimeDiverges x.toTrace) {t : ℕ} {v : V} {B : Block V}
    -- `v`'s tree before `t` holds `B`
    (hB : B ∈ (stateBefore x t v).S.T) :
    ∃ st : Stamp, (stateBefore x t v).A.timestamp_block B = some st ∧
      st < (((t : ℕ) : Int) : Stamp) :=
  (blockStamp_lt_iff hdiv hB).2 hB

/-- Every Goldfish vote of a validator's pool of a slot before a time is stamped strictly before
that time, with the time of its admission.

The variables:
- `x`: the execution; `t`: the time; `v`: the validator; `s`: the slot; `vote`: the vote;
- `st`: the vote's stamp.

Read aloud: a vote held before `t` was stamped before `t`. -/
theorem voteStamp_before {x : AtomicExec (protocol S) Sched}
    -- every time is reached
    (hdiv : TimeDiverges x.toTrace) {t : ℕ} {v : V} {s : Slot} {vote : GoldfishVote V}
    -- `v`'s pool of slot `s` before `t` holds `vote`
    (hv : vote ∈ (stateBefore x t v).A.pool s) :
    ∃ st : Stamp, (stateBefore x t v).A.timestamp_vote vote = some st ∧
      st < (((t : ℕ) : Int) : Stamp) :=
  (voteStamp_lt_iff hdiv hv).2 hv

end Before

end GoldilocksCorrectness.Proofs.Executions
