module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma107
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma94
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FinalityPairStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma107
public import GoldilocksCorrectness.Statements.Routines.FinalityPairStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma94Pair, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma94Pair.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 94, the round's attesters after
healing with the finality pair, and its kit, namely two entry blocks at one chain-state height on
one chain, the justified block of a chain state as an entry block, and the attestation duty sending
at the source with the head it reads named. The page's routine-level theorems are the facts' fields
or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono one_le_Δ supportCutoff_cast
  supportCutoff_eq supportCutoff_mono supportCutoff_succ_times voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (AttestationFrom)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks
  lem92_attestation_carries_finality_pair)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  tick_attest_input awake_since_record_awake)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Entry blocks on one chain -/

omit [RootOrder] in
/-- Two entry blocks at one chain-state height, each `D` or an ancestor of `D`, are one block.

Why: they are compatible (`ancestorEq_compatible`); of two blocks of one chain at one height, the
`T_h` is one (Lemma 47 (e)), and each is its own `T_h`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `E`, `E'`: the two entries; `D`: the block they are on the chain of.

Read aloud: two entry blocks at one chain-state height, each `D` or an ancestor of `D`, are one
block. -/
theorem entry_eq_of_ancestorEq_common (C : Config) {E E' D : Block V} (hE : E.AncestorEq D)
    (hE' : E'.AncestorEq D) (hEe : IsEntry M C E) (hEe' : IsEntry M C E')
    (hh : (M.chainStateOf C E).h = (M.chainStateOf C E').h) : E = E' := by
  rcases ancestorEq_compatible hE hE' with h1 | h1
  · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) C E E').2.2.2.2 h1 hh
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this
  · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) C E' E).2.2.2.2 h1 hh.symm
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this.symm

omit [RootOrder] in
/-- A chain state's justified block, when the justification height is at least `1`, is `B` or an
ancestor of `B`, an entry block, at the justification height.

Why: it is the `T_h` of a block `Y` of `B`'s chain at that height (Lemma 47 (f)), and a `T_h` is an
entry block of its block's height, `Y` or an ancestor of `Y` (`isEntry_T_h`).

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block whose justification is read.

Read aloud: when the justification height of `B`'s chain state is at least 1, its justified block is
an entry block, `B` or an ancestor of `B`, at the justification height. -/
theorem justified_entry_facts (C : Config) (B : Block V) (h1 : 1 ≤ (M.chainStateOf C B).h_j) :
    (M.chainStateOf C B).J.AncestorEq B ∧ IsEntry M C (M.chainStateOf C B).J ∧
      (M.chainStateOf C (M.chainStateOf C B).J).h = (M.chainStateOf C B).h_j := by
  obtain ⟨Y, hYB, hYh, hYJ⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem47f_justified_is_entry M F) C B _ rfl h1
  obtain ⟨hE, hh, hanc⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) C Y
  rw [hYJ] at hE hh hanc
  exact ⟨ancestorEq_trans hanc hYB, hE, hh.trans hYh⟩

/-! ## The duty's head -/

/-- **Kit fact, what the duty sends, with its head.** Under the hypotheses of
`attestation_duty_sends_at_source` (`Lemma55.lean`), some block `D`, `B` or a descendant of `B`,
that `v` holds before the support cutoff of slot `s + 1`, is the head the duty reads: with `J(D)`
the root of `B`'s `T_h` when `h_j(D)` is `B`'s height, every attestation the validator client
builds from `v`'s record before that cutoff, the height and the root of `B`'s `T_h`, and
`(h_j(D), J(D), h_F(D))`, is put on the wire by `v` at its tick at that cutoff.

Why: the proof of `attestation_duty_sends_at_source`, which names the head `fi.head` of the duty's
input: it descends from the anchor `B` (Lemma 48b) and is in the tree (`ac_to_fg_head_mem`).

Over the record, the update is an outcome `(n', sent)` of the tick at the cutoff, as in
`attestation_duty_sends_at_source`'s twin, whose state is awake for slot `s + 1` by `hv`; the
attestation the client builds is `AttestationFrom`, and the duty's head is the end of its walk from
the anchor.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `n'`, `sent`: an outcome of `v`'s tick at the cutoff.

Read aloud: the attestation duty of an awake honest member sends an attestation at its source, built
from a head `D` the member holds before the action time, `B` or a descendant of `B`. -/
theorem attestation_duty_sends_at_source_head (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (r s : ℕ) (B : Block V) (v : V) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hs : s = r * S.C.R)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hSaved : M.savedConfirmation n' s = some B)
    (hFast : B ∈ M.fastBlocks n')
    (hLocks : ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hViable : B ∈ M.viable_tree (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree) :
    ∃ D : Block V, B.AncestorEq D ∧ D ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree ∧
      ((M.chainStateOf S.C D).h_j = (M.chainStateOf S.C B).h →
        (M.chainStateOf S.C D).J.root = (M.chainStateOf S.C B).T_h.root) ∧
      ∀ a : Attestation V,
        AttestationFrom M (x.tickInput v (M.supportCutoff S.C (s + 1))) v
          (M.chainStateOf S.C B).h (M.chainStateOf S.C B).T_h.root (M.chainStateOf S.C D).h_j
          (M.chainStateOf S.C D).J.root (M.chainStateOf S.C D).h_F a →
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
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
    F.sched U) S (s + 1)
  -- `v`'s own tick to the cutoff, which ends its window; its input is awake since the duty window's
  -- start of slot `s + 1` or earlier, so no restart of `v` comes between the state before the cutoff
  -- and the tick
  obtain ⟨k', hl, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨τ₀, hτ₀, hτ₀le⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv hdw
  have hAwake := ((cutoff_state_facts_of_tick M F U) x R E s v τ₀ hl hτ₀ hτ₀le).1
  -- the tick's input is `v`'s state at its tick step `k'`, where `v` is outside the adversary set
  have hTI : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k' v := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hvk : v ∉ A.corrupted k' := E.not_mem_corrupted_of_tick hl
  -- the outcome the tick step took
  obtain ⟨n'', sent'', hrun0, -, hsent0⟩ := R.tick k' v _ hl
  have hrun : .ok (n'', sent'') ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
    exact hrun0
  have hwire : ∀ o ∈ sent'', (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k' + 1) - x.sent k' := by
    intro o ho
    rw [hsent0, add_tsub_cancel_left]
    exact Multiset.mem_map.2 ⟨o, Multiset.mem_coe.2 ho, rfl⟩
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) := by
    rw [hTI]; exact (lem11_node_invariant M F S A x R E k' v hvk).1
  have hXv : (x.tickInput v (M.supportCutoff S.C (s + 1))).v = v := by
    rw [hTI]; exact (lem11_node_invariant M F S A x R E k' v hvk).2.1
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
    (by
      rw [hTI]
      exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F)
        S A x R E k' v)
    (GoldilocksCorrectness.Record.Statements.Routines.AnchorAt M (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))) n''.lockEntries ((M.supportCutoff S.C (s + 1) : ℕ) : Int)) ((M.supportCutoff S.C (s + 1) : ℕ) : Int)
    (S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
  have hBh : B.AncestorEq head := by
    obtain ⟨vs, svs, -, hWE⟩ := hhead
    exact hdesc _ _ head hWE.1
  -- the head is a block of `v`'s tree (the record form of `ac_to_fg_head_mem`)
  have hDT : head ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree := by
    obtain ⟨vs, svs, -, hWE⟩ := hhead
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.ac_to_fg_head_mem M F) S.C S.P S.X _ hInv _ _ _ _
      head hWE.1).1
  refine ⟨head, hBh, hDT, fun h => ?_, fun a ha => ?_⟩
  · rw [(GoldilocksCorrectness.Record.Statements.Executions.J_eq_T_h_of_same_height M F) S.C B head hBh h]
  · have hsent := F.tk3.tick_attestation_sent S.C S.P S.X _ _ n'' sent'' a B head hrun hInv
      hAction hAw hsrc hhead (by rw [hXv]; exact ha)
    exact ⟨_, hl, hwire _ hsent⟩

/-! ## A justification certificate at a member's tick to the round's action time -/

omit [RootOrder] in
/-- **Kit fact, an attestation is determined by its validator and its content.**

The variables:
- `a`, `a'`: two attestations.

Read aloud: two attestations of one validator with the same content are equal. -/
theorem attestation_eq_of_content {a a' : Attestation V} (h1 : a'.val_index = a.val_index)
    (h2 : a'.content = a.content) : a' = a := by
  cases a; cases a'
  simp only [Attestation.content, AttestationContent.mk.injEq] at h2
  simp only at h1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h2
  subst h1
  rfl

/-- **Kit theorem, a justification certificate held at a member's tick to the round's action time is
at most the bound of the old attestations**. Let `c` be the support cutoff of slot `s + 1`, `s = r * R`, the action time of round
`r`. When every attestation an honest validator put on the wire at a tick to a clock value less than
`c` has height at most `H` (`hOld`), no block `w` holds at its tick `k` to `c` includes an attestation
put on the wire at a tick to `c` (`hTI`), and fewer than a quorum of validators have been in the
adversary set up to a real time `tH` at least the time of step `k` and at least `c`: a justification
certificate on the chain of a block `w` holds at step `k` is at a height at most `H`.

Why: the certificate has an honest member, whose attestation on the chain was put on the wire by it at
a tick before `k` to a clock value `t'` at most the time of `k` plus `ΔClockAhead`
(`lem74_honest_attestations_recorded`, `record_content_sent_step`); that attestation is the one on
the chain (`attestation_eq_of_content`). When `t' < c`, `hOld` bounds its height. When `t' = c`, its
block is held by `w` at `k` (`ancestors_mem_T_of_exec`), against `hTI`. When `t' > c`, `t'` is less
than `c` plus one delay (the tick `k` is at most `ΔClockBehind` after `c`, and `ΔClockAhead +
ΔClockBehind < Δ`), but an honest tick sends an attestation only at an action time (Lemma 49), and the
next action time after `c` is `4ΔR` later.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the environment's
  facts; `r`: the round; `s`: its first slot; `H`: the bound; `k`: the step of `w`'s tick to `c`;
  `w`: the holder; `tH`: the time up to which the adversary is bounded; `D`: the held block; `h`: the
  certificate's height; `T`: the block it names.

Read aloud: when every honest attestation sent before the round's action time has height at most `H`,
and nothing a member holds at its action tick includes an attestation of that action time, a
justification certificate on the chain of a block the member holds at that tick is at a height at most
`H`. -/
theorem justification_cert_height_le_at_tick (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout) (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (r s H k : ℕ) (w : V) (tH : ℝ) (D T : Block V) (h : Height) (hs : s = r * S.C.R)
    (hk : x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)))
    (hkH : x.time k ≤ tH) (hcH : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ tH)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) tH)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s + 1)) (M.supportCutoff S.C (s + 1)) H)
    (hTI : ∀ Z ∈ (x.st k w).tree, ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w' : V),
      x.lbl j = Event.tick w' (M.supportCutoff S.C (s + 1)) →
      (⟨w', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    (hD : D ∈ (x.st k w).tree)
    (hJ : GoldilocksCorrectness.Record.Statements.Routines.JustificationCertOn M D h T) :
    h ≤ H := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨X₁, hX₁D, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  -- an honest member of the certificate
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x tH u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ tH ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A k u :=
    fun i'' hi'' => hhonM i'' (le_trans ((time_mono M) x R hi'') hkH)
  obtain ⟨a, hau, hah, -, -, hon⟩ := hQ u hu
  have honD : M.on_chain a D = true := (GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁D hon
  have hrec := (lem74_honest_attestations_recorded M F) S A x R E k w D a hD honD (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, hval, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u k _ hrec
  have haa : a' = a := (attestation_eq_of_content M F) (by rw [hval, hau]) hcont
  subst haa
  have huH : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) :=
    Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i (le_trans hi hcH)
  rcases lt_trichotomy t' (M.supportCutoff S.C (s + 1)) with hlt | heq | hgt
  · -- a tick before the action time: `hOld`
    have hle := hOld j' t' u a' hl (by exact_mod_cast hlt) huH hsent
    rw [hah] at hle
    exact hle
  · -- a tick to the action time: its block is held at `k`, against `hTI`
    subst heq
    obtain ⟨X, hX, haX⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_iff M F) a' D).1 honD
    have hXT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E k w D X hD hX
    exact absurd hsent (hTI X hXT a' haX j' u hl)
  · -- a tick after the action time, less than one delay after it: no action time there (Lemma 49)
    exfalso
    have hkt := (E.tick_active k w _ hk).2.2
    have htj : (t' : ℝ) ≤ x.time k + ΔClockAhead := by
      have h1 := ((time_of_lbl_tick M) x R E hl).1.1
      have h2 := (time_mono M) x R hj'.le
      linarith
    have hlt' : t' < M.supportCutoff S.C (s + 1) + Δ S := by
      have : (t' : ℝ) < ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
    have hti : x.tickInput u t' = x.st j' u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hti] at hrun
    have hInvT := (lem11_node_invariant M F S A x R E j' u (E.not_mem_corrupted_of_tick hl)).1
    obtain ⟨hat, -⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a'
        hrun hInvT ha
    obtain ⟨hslotM, hround, hActionM, -⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_times M.toSlotLayout F.sched U) S r s hs
    rw [hslotM, hround] at hActionM
    have hΔc : ((Δ S : ℕ) : Int) = S.C.Δ := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
    have hΔ1 := one_le_Δ S
    simp only [Config.a_, Config.T_, t_eq_mul] at hat hActionM
    have hc1 : ((M.supportCutoff S.C (s + 1) : ℕ) : Int) < (t' : Int) := by exact_mod_cast hgt
    have hc2 : (t' : Int) < ((M.supportCutoff S.C (s + 1) : ℕ) : Int) + ((Δ S : ℕ) : Int) := by
      exact_mod_cast hlt'
    rw [hΔc] at hc2
    rw [hActionM, hat] at hc1
    rw [hActionM, hat] at hc2
    have hΔpos : (0 : Int) < S.C.Δ := by rw [← hΔc]; exact_mod_cast (by omega : 0 < Δ S)
    -- `r * R < q * R` for the round `q` of `t'`, so `q * R ≥ r * R + 1`
    have hrq : r * S.C.R < S.C.round (S.C.slot ((t' : ℕ) : Int)) * S.C.R := by
      by_contra hn
      have hle : ((S.C.round (S.C.slot ((t' : ℕ) : Int)) * S.C.R : ℕ) : Int) ≤ ((r * S.C.R : ℕ) : Int) := by
        exact_mod_cast Nat.le_of_not_lt hn
      nlinarith
    have hrq' : ((r * S.C.R : ℕ) : Int) + 1 ≤ ((S.C.round (S.C.slot ((t' : ℕ) : Int)) * S.C.R : ℕ) : Int) := by
      exact_mod_cast hrq
    nlinarith

/-- **Kit theorem, the finality twin of `justification_cert_height_le_at_tick`**. Under its hypotheses, a finality certificate on the chain of a block `w` holds at step
`k` is at a height less than `H`.

Why: as `justification_cert_height_le_at_tick`; the honest member's attestation carries the finality pair at that
height and is well formed (`record_content_sent_step`), so its own height is greater than the pair's
(`attestation_well_formed_iff`); its height is at most `H` when it was put on the wire at a tick before `c`, and the
other two cases do not occur.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the environment's
  facts; `r`: the round; `s`: its first slot; `H`: the bound; `k`: the step of `w`'s tick to `c`;
  `w`: the holder; `tH`: the time up to which the adversary is bounded; `D`: the held block; `h`: the
  certificate's height; `T`: the block it names.

Read aloud: when every honest attestation sent before the round's action time has height at most `H`,
and nothing a member holds at its action tick includes an attestation of that action time, a
finality certificate on the chain of a block the member holds at that tick is at a height less than
`H`. -/
theorem finality_cert_height_lt_at_tick (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout) (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (r s H k : ℕ) (w : V) (tH : ℝ) (D T : Block V) (h : Height) (hs : s = r * S.C.R)
    (hk : x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)))
    (hkH : x.time k ≤ tH) (hcH : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ tH)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) tH)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s + 1)) (M.supportCutoff S.C (s + 1)) H)
    (hTI : ∀ Z ∈ (x.st k w).tree, ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w' : V),
      x.lbl j = Event.tick w' (M.supportCutoff S.C (s + 1)) →
      (⟨w', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    (hD : D ∈ (x.st k w).tree)
    (hF : GoldilocksCorrectness.Record.Statements.Routines.FinalityCertOn M D h T) :
    h < H := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨X₁, hX₁D, Q, hqA, hQ⟩ := hF
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  -- an honest member of the certificate
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x tH u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ tH ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A k u :=
    fun i'' hi'' => hhonM i'' (le_trans ((time_mono M) x R hi'') hkH)
  obtain ⟨a, hau, hP, hon⟩ := hQ u hu
  have honD : M.on_chain a D = true := (GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁D hon
  have hrec := (lem74_honest_attestations_recorded M F) S A x R E k w D a hD honD (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, hval, hcont, hwf⟩ :=
    (record_content_sent_step M F) S A x R E u k _ hrec
  have haa : a' = a := (attestation_eq_of_content M F) (by rw [hval, hau]) hcont
  subst haa
  have hpw := ((F.rd.attestation_well_formed_iff a').1 hwf).2 _ hP
  have huH : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) :=
    Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i (le_trans hi hcH)
  rcases lt_trichotomy t' (M.supportCutoff S.C (s + 1)) with hlt | heq | hgt
  · -- a tick before the action time: `hOld`
    have hle := hOld j' t' u a' hl (by exact_mod_cast hlt) huH hsent
    exact lt_of_lt_of_le hpw hle
  · -- a tick to the action time: its block is held at `k`, against `hTI`
    subst heq
    obtain ⟨X, hX, haX⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_iff M F) a' D).1 honD
    have hXT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E k w D X hD hX
    exact absurd hsent (hTI X hXT a' haX j' u hl)
  · -- a tick after the action time, less than one delay after it: no action time there (Lemma 49)
    exfalso
    have hkt := (E.tick_active k w _ hk).2.2
    have htj : (t' : ℝ) ≤ x.time k + ΔClockAhead := by
      have h1 := ((time_of_lbl_tick M) x R E hl).1.1
      have h2 := (time_mono M) x R hj'.le
      linarith
    have hlt' : t' < M.supportCutoff S.C (s + 1) + Δ S := by
      have : (t' : ℝ) < ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
    have hti : x.tickInput u t' = x.st j' u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hti] at hrun
    have hInvT := (lem11_node_invariant M F S A x R E j' u (E.not_mem_corrupted_of_tick hl)).1
    obtain ⟨hat, -⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a'
        hrun hInvT ha
    obtain ⟨hslotM, hround, hActionM, -⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_times M.toSlotLayout F.sched U) S r s hs
    rw [hslotM, hround] at hActionM
    have hΔc : ((Δ S : ℕ) : Int) = S.C.Δ := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
    have hΔ1 := one_le_Δ S
    simp only [Config.a_, Config.T_, t_eq_mul] at hat hActionM
    have hc1 : ((M.supportCutoff S.C (s + 1) : ℕ) : Int) < (t' : Int) := by exact_mod_cast hgt
    have hc2 : (t' : Int) < ((M.supportCutoff S.C (s + 1) : ℕ) : Int) + ((Δ S : ℕ) : Int) := by
      exact_mod_cast hlt'
    rw [hΔc] at hc2
    rw [hActionM, hat] at hc1
    rw [hActionM, hat] at hc2
    have hΔpos : (0 : Int) < S.C.Δ := by rw [← hΔc]; exact_mod_cast (by omega : 0 < Δ S)
    -- `r * R < q * R` for the round `q` of `t'`, so `q * R ≥ r * R + 1`
    have hrq : r * S.C.R < S.C.round (S.C.slot ((t' : ℕ) : Int)) * S.C.R := by
      by_contra hn
      have hle : ((S.C.round (S.C.slot ((t' : ℕ) : Int)) * S.C.R : ℕ) : Int) ≤ ((r * S.C.R : ℕ) : Int) := by
        exact_mod_cast Nat.le_of_not_lt hn
      nlinarith
    have hrq' : ((r * S.C.R : ℕ) : Int) + 1 ≤ ((S.C.round (S.C.slot ((t' : ℕ) : Int)) * S.C.R : ℕ) : Int) := by
      exact_mod_cast hrq
    nlinarith

/-! ## Lemma 55's hypotheses at a tick input, and an honest attestation's tick before an action time -/

/-- **Kit theorem, Lemma 55's viable-tree and record hypotheses at a tick input**. Under a frame shape
with root `ρ` and `head_height_floor` value `φ` at `v`'s state at its tick to `t`, with `ρ` equal to
or an ancestor of `B`, `φ` at most `B`'s chain-state height, `B` in that state's tree and the lock box
of Lemma 61: `B` is in that state's viable tree, and the state holds no lock at `B`'s height or holds
`T_h(B)`'s root there with every attestation it signed at that height naming it.

Why: as `lem61_honest_validator_attests_frame` reads it at the tick input: the finalized block is the
root or an ancestor of it (`F_ancestorEq_fc_root_of_exec`), and the record's invariants at the step
(`lock_none_of_h_j_lt_of_exec`, `lockNamesSent_of_exec`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts and the
  environment's facts; `t`: the clock value of the tick; `B`: the block; `v`: the validator; `ρ`:
  the root; `φ`: the value of `head_height_floor`.

Read aloud: at the state a validator's tick starts from, a block on the frame root's chain, high
enough and held, is viable, and the record's lock at its height is absent or on its `T_h`. -/
theorem lem61_frame_hypotheses_at_tick (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (B : Block V) (v : V) (ρ : Block V) (φ : Height)
    (hShape : GoldilocksCorrectness.Record.Statements.Routines.FrameShape M (x.tickInput v t) ρ φ)
    (hRootV : ρ.AncestorEq B)
    (hBHeight : φ ≤ (M.chainStateOf S.C B).h)
    (hBin : B ∈ (x.tickInput v t).tree)
    (hLockBox : (x.tickInput v t).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v t).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v t).sentLock (M.chainStateOf S.C B).h = some (M.chainStateOf S.C B).T_h.root) :
    B ∈ M.viable_tree (M.fg_to_ac (x.tickInput v t)) (M.fg_to_ac (x.tickInput v t)).tree ∧
      ((x.tickInput v t).sentLock (M.chainStateOf S.C B).h = none ∨
        ((x.tickInput v t).sentLock (M.chainStateOf S.C B).h = some (M.chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (x.tickInput v t).sentAttestations,
            b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) := by
  refine ⟨?_, ?_⟩
  · refine (GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_of_frameShape_of_core M F) S.C S.P S.X _
      (lem11_node_invariantCore_of_run M F S x R (x.tickStep v t) v).1 ρ φ B hShape ?_ hRootV hBin hBHeight
    rw [← hShape.1]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ v
  · rcases hLockBox with hlt | hnone | hlock
    · exact Or.inl ((GoldilocksCorrectness.Record.Statements.Executions.lock_none_of_h_j_lt_of_exec M F) S A x R E _ v _ hlt)
    · exact Or.inl hnone
    · exact Or.inr ⟨hlock, (GoldilocksCorrectness.Record.Statements.Executions.lockNamesSent_of_exec M F) S A x R E _ v _ _
        hlock⟩

/-- **Kit theorem, an honest attestation's tick to a clock value less than a round's action time is
more than `ΔClockAhead` before it in real time**. Let `c` be the support cutoff of slot
`s + 1`, `s = r * R`, the action time of round `r`. A tick of `u` to a clock value `t' < c` that put an
attestation of `u` on the wire is at a real time less than `c − ΔClockAhead`.

Why: an honest tick sends an attestation only at an action time (Lemma 49), so `t'` is the action time
of an earlier round, at least one delay before `c` (rounds are `4ΔR` apart); the tick's real time is at
most `t' + ΔClockBehind`, and `ΔClockAhead + ΔClockBehind < Δ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts and the
  environment's facts; `r`: the round; `s`: its first slot; `j`: the tick's step; `t'`: its clock
  value; `u`: the validator; `a`: the attestation.

Read aloud: an attestation sent at a tick to a clock value before a round's action time was sent more
than one clock bound before that action time in real time. -/
theorem attestation_tick_time_lt_cutoff (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (r s j t' : ℕ) (u : V) (a : Attestation V) (hs : s = r * S.C.R)
    (hl : x.lbl j = Event.tick u t') (ht' : t' < M.supportCutoff S.C (s + 1))
    (hsent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j) :
    x.time j + ΔClockAhead < M.supportCutoff S.C (s + 1) := by
  have htj : x.time j ≤ t' + ΔClockBehind := ((time_of_lbl_tick M) x R E hl).1.2
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  have hti : x.tickInput u t' = x.st j u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  rw [hti] at hrun
  have hInvT := (lem11_node_invariant M F S A x R E j u (E.not_mem_corrupted_of_tick hl)).1
  obtain ⟨hat, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ha
  obtain ⟨hslotM, hround, hActionM, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_times M.toSlotLayout F.sched U) S r s hs
  rw [hslotM, hround] at hActionM
  have hΔc : ((Δ S : ℕ) : Int) = S.C.Δ := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
  have hΔ1 := one_le_Δ S
  simp only [Config.a_, Config.T_, t_eq_mul] at hat hActionM
  have hc1 : (t' : Int) < ((M.supportCutoff S.C (s + 1) : ℕ) : Int) := by exact_mod_cast ht'
  have hΔpos : (0 : Int) < S.C.Δ := by rw [← hΔc]; exact_mod_cast (by omega : 0 < Δ S)
  have key : (t' : Int) + ((Δ S : ℕ) : Int) ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : Int) := by
    rw [hActionM, hat] at hc1
    rw [hActionM, hat, hΔc]
    -- the round `q` of `t'` has `q * R < r * R`, so `q * R + 1 ≤ r * R`
    have hqr : S.C.round (S.C.slot ((t' : ℕ) : Int)) * S.C.R < r * S.C.R := by
      by_contra hn
      have hle : ((r * S.C.R : ℕ) : Int) ≤ ((S.C.round (S.C.slot ((t' : ℕ) : Int)) * S.C.R : ℕ) : Int) := by
        exact_mod_cast Nat.le_of_not_lt hn
      nlinarith
    have hqr' : ((S.C.round (S.C.slot ((t' : ℕ) : Int)) * S.C.R : ℕ) : Int) + 1 ≤ ((r * S.C.R : ℕ) : Int) := by
      exact_mod_cast hqr
    nlinarith
  have keyR : (t' : ℝ) + (Δ S : ℝ) ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by exact_mod_cast key
  linarith

/-! ## Lemma 94 -/

/-- **Lemma 94, the round's attesters after healing carry the finality pair.** The proof; the
audited statement is in `Statements/Executions/FinalityLivenessStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal; `u`: the member.

Read aloud: when no honest validator has attested above `B`'s justification height before the
round's action time, and that height is greater than the threshold, every honest active validator of
the honest round opening slot attests for `B`'s height at the action time, vouching for `B`'s
justification when it is not yet finalized or already holding a block on `B`'s chain that finalizes it,
provided no member already holds, when it attests, a block including one of the round's own attestations
. -/
theorem lem94_round_attesters_after_healing (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V) (u : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C (s + 1)))
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s + 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ M.supportCutoff S.C (s + 1) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) → w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hs : s = r * S.C.R) (hAfter : x.time i₂ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x s)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hOldJ : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s + 1)) (M.supportCutoff S.C (s + 1))
        (M.chainStateOf S.C B).h_j)
    (hHJ : H < (M.chainStateOf S.C B).h_j)
    -- no block an honest active member of the round holds when it ticks to the round's action time includes an
    -- attestation put on the wire at a tick to that action time
    (hTickInputs : ∀ v ∈ honestActiveAt M S A x s, ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (s + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    (hu : u ∈ honestActiveAt M S A x s) :
    ∃ (i : ℕ) (a : Attestation V), x.lbl i = Event.tick u (M.supportCutoff S.C (s + 1)) ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root ∧
      a.τ = false ∧
      ((M.chainStateOf S.C B).h_F < (M.chainStateOf S.C B).h_j →
        a.finality_pair =
          some (FinalityPair.mk (M.chainStateOf S.C B).h_j (M.chainStateOf S.C B).J.root) ∨
        ∃ D ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).tree, B.AncestorEq D ∧
          (M.chainStateOf S.C B).h_j ≤ (M.chainStateOf S.C D).h_F) := by
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  have hChain' : ConfirmationsChainBefore M S A x s₀ s :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  obtain ⟨hChainB, hBslot, hUpdB, hHB, ⟨n', sent, hrun, hAw, hSv, hFb⟩, hRev, hρ, hφ, hBin, hBox⟩ :=
    (round_member_frame_after_healing M F U Fx) S A x R GST s₀ anchor i₂ H s B u E hNet hSkew hRedeliver Sy hΔs
      hRootsU hParent hAdvQU hSleepK hAnchor hGST ht₀ hChain' hInv hLocks hLocks₀ hOld hCachesU
      hAfter hOpener hPropose hNoCollision hHold hHoldP hu
  have hupd : u ∈ updaterAt M S A x s := (honestActiveAt_subset_updaterAt M F) S A x R E s hu
  have hv : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) :=
    hupd
  have hLk := (update_lock_entries_ancestorEq M F U) S A x R s B u E hSkew hv n' sent hrun hAw hSv hBslot hRev
  obtain ⟨hViable, hRecord⟩ := (lem61_frame_hypotheses_at_tick M F) S A x R E _ B u _ _ ⟨rfl, rfl⟩ hρ hφ hBin
    hBox
  have hBh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1
  -- `u`'s tick `k` to the action time; its input is `u`'s state at `k`
  obtain ⟨k, hl, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hTI : x.tickInput u (M.supportCutoff S.C (s + 1)) = x.st k u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have huc : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) :=
    fun h => (Finset.mem_sdiff.1 hu).2 (Finset.mem_union_left _ h)
  have hc01 : M.supportCutoff S.C (s₀ + 1) ≤ M.supportCutoff S.C (s + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  -- an attestation `u` signed before its tick `k` was sent at a tick more than `ΔClockAhead` before the
  -- action time in real time, so `u` is honest at that tick's time
  have hRecTick : ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
      ∃ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick u t' ∧ t' < M.supportCutoff S.C (s + 1) ∧
        (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j ∧
        a.content = b ∧ u ∉ A.corruptedAtTime x (x.time j) := by
    intro b hb
    obtain ⟨j, t', a, hl', ht', -, hsent, -, hac, -⟩ := (record_content_sent M F) S A x R _ u b E hb
    have htj := (attestation_tick_time_lt_cutoff M F U) S A x R E hSkew r s j t' u a hs hl' ht' hsent
    exact ⟨j, t', a, hl', ht', hsent, hac,
      (not_mem_corruptedAtTime_of_mem_activeThroughoutToTick M F) x R E hv htj⟩
  -- `u`'s record at its tick holds nothing at `h(B)` (`hOldJ`)
  have hFresh : ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
      b.h ≠ (M.chainStateOf S.C B).h := by
    intro b hb hbh
    obtain ⟨j, t', a, hl', ht', hsent, hac, -⟩ := hRecTick b hb
    have hle := hOldJ j t' u a hl' (by exact_mod_cast ht') huc hsent
    have hah : a.h = b.h := by rw [← hac]; rfl
    rw [hah, hbh] at hle
    omega_nat
  -- the duty's head `D`, and the attestation it builds and sends
  obtain ⟨D, hBD, hDT, hJD, hsend⟩ := (attestation_duty_sends_at_source_head M F U) S A x R r s B u
    E hs hv n' sent hrun hSv hFb hLk hViable
  have htimeout : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentTimeout
      (M.chainStateOf S.C B).h = false := by
    cases h : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentTimeout (M.chainStateOf S.C B).h with
    | false => rfl
    | true =>
        obtain ⟨b, hb, hbh, -⟩ := (((GoldilocksCorrectness.Record.Statements.Executions.recordConsistent_of_exec M F)
          S A x R E (x.tickStep u (M.supportCutoff S.C (s + 1))) u).timeoutRec _).1 h
        exact absurd hbh (hFresh b hb)
  have htarget : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentTarget
      (M.chainStateOf S.C B).h = none := by
    cases h : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentTarget (M.chainStateOf S.C B).h with
    | none => rfl
    | some T =>
        obtain ⟨b, hb, hbh, -⟩ := (GoldilocksCorrectness.Record.Statements.Executions.target_sent_of_exec M F)
          S A x R E (x.tickStep u (M.supportCutoff S.C (s + 1))) u _ _ h
        exact absurd hbh (hFresh b hb)
  obtain ⟨a, hbuilt, hav, hah, haT, hτ⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem50_attestation_sent_at_source F) _ u _ _ _ _ _
      hRecord hJD
      ((GoldilocksCorrectness.Record.Statements.Executions.target_sent_of_exec M F) S A x R E
        (x.tickStep u (M.supportCutoff S.C (s + 1))) u)
      ((GoldilocksCorrectness.Record.Statements.Executions.sent_target_recorded_of_exec M F) S A x R E
        (x.tickStep u (M.supportCutoff S.C (s + 1))) u)
      ((GoldilocksCorrectness.Record.Statements.Executions.timeout_recorded_of_exec M F) S A x R E
        (x.tickStep u (M.supportCutoff S.C (s + 1))) u)).2 hFresh htimeout htarget
  obtain ⟨i, hli, hm⟩ := hsend a hbuilt
  refine ⟨i, a, hli, hm, hav, hah, haT, hτ, fun hFj => ?_⟩
  -- the finality pair
  have hj1 : 1 ≤ (M.chainStateOf S.C B).h_j := by omega_nat
  have hjD := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_h_j_h_F_mono M F) S.C B D hBD
  have hDk : D ∈ (x.st k u).tree := by rw [← hTI]; exact hDT
  -- the adversary is bounded up to the later of `k`'s time and the action time
  have hAdvQmax : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time k) ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ)) := by
    rcases le_total (x.time k) ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) with h | h
    · rw [max_eq_right h]; exact hAdvQ
    · rw [max_eq_left h]
      have h' := hAdvQU u hupd
      rwa [(tickStep_eq_of_lbl M) x E hl] at h'
  -- `h_j(D) = h_j(B)`: a justification on `D`'s chain at a greater height has an honest member whose
  -- attestation `hOldJ` and `hTickInputs` exclude (`justification_cert_height_le_at_tick`)
  have hjeq : (M.chainStateOf S.C D).h_j = (M.chainStateOf S.C B).h_j := by
    by_contra hne
    have hgt : (M.chainStateOf S.C B).h_j < (M.chainStateOf S.C D).h_j :=
      lt_of_le_of_ne hjD.1 (Ne.symm hne)
    have hcert := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 (by omega_nat)).1
    have := (justification_cert_height_le_at_tick M F U Fx) S A x R E hSkew r s _ k u
      (max (x.time k) ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ)) D _ _ hs hl (le_max_left _ _) (le_max_right _ _)
      hAdvQmax hOldJ (by rw [← hTI]; exact hTickInputs u hu) hDk hcert
    omega_nat
  -- `h_F(D) ≥ h_j(B)`: the second case of the conclusion
  by_cases hge : (M.chainStateOf S.C B).h_j ≤ (M.chainStateOf S.C D).h_F
  · exact Or.inr ⟨D, hDT, hBD, hge⟩
  left
  have hFlt : (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C B).h_j := lt_of_not_ge hge
  -- `J(D) = J(B)`: both entries at `h_j(B)` on `D`'s chain
  obtain ⟨hJBB, hJBe, hJBh⟩ := (justified_entry_facts M F) S.C B hj1
  obtain ⟨hJDD, hJDe, hJDh⟩ := (justified_entry_facts M F) S.C D (by omega_nat)
  have hJeq : (M.chainStateOf S.C D).J = (M.chainStateOf S.C B).J :=
    (entry_eq_of_ancestorEq_common M F) S.C hJDD (ancestorEq_trans hJBB hBD) hJDe hJBe
      (by rw [hJDh, hJBh, hjeq])
  -- an entry on the honest chain at a slot at most `s`, at `h_j(B)`, is `J(B)`
  have hEntryJ : ∀ (s_a : ℕ) (Eb : Block V), s_a ≤ s → OnHonestChainAt M S A x s₀ s_a Eb →
      IsEntry M S.C Eb → (M.chainStateOf S.C Eb).h = (M.chainStateOf S.C B).h_j →
      Eb = (M.chainStateOf S.C B).J := by
    intro s_a Eb hsa hOn hEe hEh
    have hEB : Eb.AncestorEq B := by
      rcases Nat.lt_or_ge s_a s with hlt | hge'
      · exact hChainB Eb ⟨s_a, hlt, hOn⟩
      · obtain rfl : s_a = s := le_antisymm hsa hge'
        obtain ⟨-, w, hw, C, hC, hEC⟩ := hOn
        rw [hUpdB w hw] at hC
        obtain rfl := Option.some.inj hC
        exact hEC
    exact (entry_eq_of_ancestorEq_common M F) S.C hEB hJBB hEe hJBe (by rw [hEh, hJBh])
  -- every attestation of `u` at `h_j(B)` signed before its tick is a target for `J(B)`
  have hrecJ : ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
      b.h = (M.chainStateOf S.C B).h_j → b.τ = false ∧ b.T = (M.chainStateOf S.C B).J.root := by
    intro b hb hbh
    obtain ⟨j, t', a', hl', ht', hsent', hac, hutj⟩ := hRecTick b hb
    have ha'h : a'.h = (M.chainStateOf S.C B).h_j := by rw [← hbh, ← hac]; rfl
    rcases Nat.lt_or_ge t' (M.supportCutoff S.C (s₀ + 1)) with hlt | hge'
    · have huC : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) :=
        (not_mem_corruptedAtTime_of_le M) x R E hc01 huc
      have := hOld j t' u a' hl' (by exact_mod_cast hlt) huC hsent'
      rw [ha'h] at this
      omega_nat
    have hτ' := (no_honest_timeout_after_healing_before M F U) S A x R s₀ H (s + 1) j t' u a' E
      hChain hOld hl' hge' ht'.le ((not_mem_corruptedAtTime_of_le M) x R E ht'.le huc) hsent'
      (by rw [ha'h]; exact hHJ)
    obtain ⟨s_a, Eb, -, hts, hOn, hEe, hEh, hET⟩ :=
      (lem82_honest_attestations_on_chain M F U) S A x R s₀ E j t' u a' hl' hge' hutj hsent'
    have hsa : s_a < s := by
      by_contra hn
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s + 1 ≤ s_a + 1 by omega)
      omega
    have hEJ := hEntryJ s_a Eb hsa.le hOn hEe (by rw [hEh, ha'h])
    refine ⟨by rw [← hac]; exact hτ', ?_⟩
    rw [← hac]
    show a'.T = _
    rw [hET, hEJ]
  have hTo : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentTimeout
      (M.chainStateOf S.C B).h_j = false := by
    cases h : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentTimeout (M.chainStateOf S.C B).h_j with
    | false => rfl
    | true =>
        obtain ⟨b, hb, hbh, hbτ⟩ := (((GoldilocksCorrectness.Record.Statements.Executions.recordConsistent_of_exec M F)
          S A x R E (x.tickStep u (M.supportCutoff S.C (s + 1))) u).timeoutRec _).1 h
        have := (hrecJ b hb hbh).1
        rw [hbτ] at this
        cases this
  have hTg : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentTarget (M.chainStateOf S.C B).h_j = none ∨
      (x.tickInput u (M.supportCutoff S.C (s + 1))).sentTarget (M.chainStateOf S.C B).h_j =
        some (M.chainStateOf S.C B).J.root := by
    cases h : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentTarget (M.chainStateOf S.C B).h_j with
    | none => exact Or.inl rfl
    | some T' =>
        obtain ⟨b, hb, hbh, hbT⟩ := (GoldilocksCorrectness.Record.Statements.Executions.target_sent_of_exec M F)
          S A x R E (x.tickStep u (M.supportCutoff S.C (s + 1))) u _ _ h
        right
        rw [← hbT, (hrecJ b hb hbh).2]
  -- a lock at `h_j(B)` names the honest chain's entry there (Lemma 83 at the real time of `k`), which
  -- is `J(B)`
  have hLkJ : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h_j = none ∨
      (x.tickInput u (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h_j =
        some (M.chainStateOf S.C B).J.root := by
    cases hlk : (x.tickInput u (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h_j with
    | none => exact Or.inl rfl
    | some T' =>
        right
        rw [hTI] at hlk
        obtain ⟨j', hj', D', hD'T, h1', hD'j, hD'J⟩ := (lock_justified_of_exec M F) S A x R E k u _ T' hlk
        have hcert := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D').1 (hD'j ▸ h1')).1
        rw [hD'j] at hcert
        have hj'k : x.time j' ≤ x.time k := (time_mono M) x R (Nat.le_of_lt hj')
        obtain ⟨s_a, Eb, ⟨k'', w'', hk''j', hlk''⟩, hOn, hEe, hEh, hEr⟩ :=
          (one_justification_greater_than_threshold_at_real M F Fx) S A x R E s₀ (M.supportCutoff S.C (s₀ + 1)) H
            j' u D' _ _ (max (x.time k) ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ))
            (le_trans hj'k (le_max_left _ _)) hAdvQmax
            ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E)
            (fun i t v a hl hlt hH hsent => hOld i t v a hl hlt
              (Activity.not_mem_corruptedAtTime.2 fun i' hi' => Activity.not_mem_corruptedAtTime.1 hH i'
                (le_trans hi' (le_trans (by exact_mod_cast hc01) (le_max_right _ _)))) hsent) hD'T
            hcert hHJ
        -- the tick `k''` to the support cutoff of slot `s_a + 1` comes before `k`, so `s_a ≤ s`
        have hsa : s_a ≤ s := by
          by_contra hn
          have hcmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
            (show s + 2 ≤ s_a + 1 by omega)
          have h1 := ((time_of_lbl_tick M) x R E hlk'').1.1
          have h2 := ((time_of_lbl_tick M) x R E hl).1.2
          have h3 : x.time k'' ≤ x.time k := (time_mono M) x R (by omega)
          have h4 : ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) ≤ M.supportCutoff S.C (s_a + 1) := by
            exact_mod_cast hcmono
          have h5 : ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) = M.supportCutoff S.C (s + 1) + 4 * Δ S := by
            rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 2),
              (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1),
              (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 2),
              (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1),
              (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 2),
              (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)]
            push_cast; ring
          have hA0 := E.ahead_nonneg
          have hB0 := E.behind_nonneg
          have hΔ1 : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast one_le_Δ S
          linarith
        have hEJ := hEntryJ s_a Eb hsa hOn hEe hEh
        rw [← hD'J, hEr, hEJ]
  -- Lemma 92
  have hpair := F.tk3.attestation_carries_finality_pair _ u _ _ _ _ _ a hbuilt
    (by rw [hjeq]; exact hFlt) (by rw [hjeq]; exact hBh.2.1) (by rw [hjeq, hJeq]; exact hTg)
    (by rw [hjeq]; exact hTo) (by rw [hjeq, hJeq]; exact hLkJ)
  rw [hpair.2, hjeq, hJeq]

end GoldilocksCorrectness.Record.Proofs.Executions

