module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89Defs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseFrameStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Statements.Executions.Lemma89Defs
public import GoldilocksCorrectness.Statements.Executions.PhaseFrameStatements
public import GoldilocksCorrectness.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89FastLine, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89FastLine.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the first four steps of Lemma 89 on
the fast-confirmation route, an honest attestation at a round's action time is built from a fast
block, the held heights before the action time, the honest finalized blocks as ancestors of a held
block, and Lemma 36b read at an ancestor of the saved confirmation. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (supportCutoff_cast supportCutoff_succ_times)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_lt_supportCutoff)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked
  VoterTreeAt hMax)

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
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl tick_attest_awake
  awakeSince_of_record_awake create_attestation_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **A1, an honest attestation is built from a fast block of its sender's update.** The proof;
the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: Lemma 82's, stopped at the fast block. The tick's attestation is the duty's
(Lemma 49), built from the duty's source, whose chain-state height it carries; the tick passed the
duty test, so it ran the confirmation update of slot `r * R + 1` (Lemma 15) on the state the tick
starts from, which is `v`'s state before `a_r`; the source is a fast block of the node state the
tick leaves, which the update can leave (`ConfirmationUpdated`), and a block of `v`'s tree. The
landed conclusion names the update's answer; the twin names a node state the update can leave,
as Lemma 36b's twin takes it (`Lemma81.lean`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `v`: the attester;
  `a`: the attestation.

Read aloud: whoever attests at height `h` has just fast-confirmed a block of height `h`. -/
theorem fast_block_of_honest_attestation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (r : ℕ) (v : V) (a : Attestation V)
    (hSend : HonestAttestationAt M S A x (aR M S r) v a) :
    ∃ (n' : M.N) (L : Block V),
      ConfirmationUpdated M S.C S.P (x.tickInput v (aR M S r)) ((aR M S r : ℕ) : Int)
        (r * S.C.R + 1) n' ∧
      L ∈ n'.fastBlocks ∧ L ∈ (x.tickInput v (aR M S r)).tree ∧
      (M.chainStateOf S.C L).h = a.h := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = r * S.C.R := ⟨_, rfl⟩
  have haR : aR M S r = M.supportCutoff S.C (s + 1) := by rw [hs]; rfl
  rw [haR] at hSend ⊢
  rw [← hs]
  obtain ⟨i, hl, hSent⟩ := hSend
  -- the tick, and the attestation it built
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hSent
  have hTI_i : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st i v := by
    show x.st (x.tickStep v (M.supportCutoff S.C (s + 1))) v = x.st i v
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) := by
    rw [hTI_i]
    exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  -- Lemma 49 over the record: the tick ran from a state awake for the slot of the cutoff, and built
  -- `a` from the height of the source's chain state, the source being the deepest fast block of the
  -- outcome in the viable tree
  obtain ⟨-, hAw, source, head, hsrc, -, ⟨τ', -, -, rfl⟩, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ha
  -- the spec's slot of the cutoff is `s + 1` (`U`)
  have hsl1 : S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).1
  -- the confirmation update of slot `s + 1` ran in the tick, from the state awake for the slot
  have hCU := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hrun hInvT
    (by rw [hsl1]; exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S (s + 1))
    hAw
  rw [hsl1] at hCU
  -- the source is a fast block of the outcome, and a block of the viable tree of the input's tree,
  -- so a block of the input's tree (the readers `viable_tree` and `fg_to_ac` by their definitions)
  obtain ⟨hfast, hvt⟩ := Finset.mem_inter.1 (GoldilocksCorrectness.Proofs.Routines.deepest?_mem hsrc)
  have hsT : source ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree := by
    rw [F.rd.viable_tree_eq] at hvt
    have h1 := (Finset.mem_filter.1 hvt).1
    rw [F.rd.fg_to_ac_eq] at h1
    exact (Finset.mem_filter.1 h1).1
  exact ⟨n', source, hCU, hfast, hsT, rfl⟩

/-- **A2, before `a_r` every honest-held block has height at most `H₂ + 1`.** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: `attested_height_bound_before` at the step `i ≤ k₀`, whose time is at most that of `k₀`,
so at most `tAwakeEnd`; every tick at a step before `i` is at a step before `k₀`, so `hOld` bounds its
honest attestations.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end;
- `H₂`: the bound; `k₀`: a step before which every honest attestation has height at most `H₂`;
  `i`: the step read; `w`: the holder; `D`: the block.

Read aloud: nothing climbs past `H₂ + 1` up to step `k₀`. -/
theorem held_height_le_before_action (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (tAwakeEnd H₂ k₀ i : ℕ) (w : V) (D : Block V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hOld : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : x.time k₀ ≤ tAwakeEnd)
    (hi : i ≤ k₀) (hD : D ∈ (x.st i w).tree) :
    (M.chainStateOf S.C D).h ≤ H₂ + 1 :=
  (attested_height_bound_before M F Fx) S A x R E i H₂ w D tAwakeEnd
    (le_trans ((time_mono M) x R hi) hEnd) hThird
    (fun k t u a hk => hOld k t u a (lt_of_lt_of_le hk hi)) hD

/-- **A3, before `a_r` every honest finalized block is `L` or an ancestor of `L`.** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: `w`'s finalized block at step `i` is the finalized block of the chain state of a block
`D` `w` holds then (`finalizedFromChain_of_exec`); `h_F(D) ≤ h_j(D) < h(D) ≤ H₂ + 1` (Lemma 47 (a)
and A2 at `i`), so `h_F(D) < h(L)`, and Lemma 89a at the steps `i` and `k₀` gives `F ⪯ L`, `v` being
honest at its tick `k₀`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end;
- `r`: the round; `H₂`: the bound; `k₀`: the step of `v`'s tick to `aR M S r`; `i`: the step read;
  `v`: the holder of `L`; `w`: the validator whose finalized block is read; `L`: the block.

Roots name blocks until a time `tR` at least the time of step `k₀`: the proof compares (Lemma 89a)
the block `B` `w` holds at step `i` with `L`, which `v` holds at step `k₀`, and `i ≤ k₀`.

Read aloud: no honest validator has finalized anything the fast block does not extend. -/
theorem finalized_ancestor_of_fast_block (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tAwakeEnd r H₂ k₀ i : ℕ) (v w : V) (L : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR) (htR : x.time k₀ ≤ tR)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hk₀ : x.lbl k₀ = Event.tick v (aR M S r))
    (hOld : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : x.time k₀ ≤ tAwakeEnd)
    (hLv : L ∈ (x.tickInput v (aR M S r)).tree)
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hi : i ≤ k₀) (hw : w ∉ A.corrupted i) :
    (x.st i w).finalized.AncestorEq L := by
  obtain ⟨B, hB, hF⟩ := (finalizedFromChain_of_exec M F) S A x R E i w
  have hBh := (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ k₀ i w B hThird
    hOld hEnd hi hB
  obtain ⟨-, hj, hFj⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1
  have hlt : (M.chainStateOf S.C B).h_F < (M.chainStateOf S.C L).h := by
    rw [hL]
    exact lt_of_le_of_lt hFj (lt_of_lt_of_le hj hBh)
  have hik := (time_mono M) x R hi
  have hT : A.AdversaryFewerThanThirdUntil x (validator_count V) (max (x.time i) (x.time k₀)) :=
    hThird.mono (max_le (hik.trans hEnd) hEnd)
  have hv' : v ∉ A.corrupted k₀ := E.not_mem_corrupted_of_tick hk₀
  have hLv' : L ∈ (x.st k₀ v).tree := by
    have h : x.tickInput v (aR M S r) = x.st k₀ v := by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk₀]
    rw [← h]; exact hLv
  have hFL := (lem68_honest_past_finalized M F Fx) S A x R E hRoots i k₀ w v B L hT hw hv' hB hLv' hlt
    (max_le (hik.trans htR) htR)
  rw [hF]
  exact hFL

/-- **A4, a confirmed block's ancestor is extended by the next slot's honest votes, the held
form.** The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: Lemma 36b's proof (`lem36b_confirmed_block_extended_held`), with Lemma 36 at the
ancestor `L` of the saved confirmation `C'` in place of `C'` itself, then Lemma 21 in the held form
at `L`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose confirmation `v`'s update of slot `s + 1` saves;
- `C'`: the saved confirmation; `L`: `C'` or an ancestor of it; `v`: the validator whose update
  saves `C'`; `w`: the voter of slot `s + 1`; `n'`: a node state the update can leave (the landed
  update's answer, as Lemma 36b's twin reads it); `vote`: `w`'s Goldfish vote.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: the proof reads Lemma 21 in the held form at
slot `s`, whose bound, the latest real time of `w`'s tick to the view freeze of slot `s`, is at most that
time.

Read at the validators' own ticks (T-RC8-2): `v` from `tStart` up to its tick to the support cutoff of
slot `s + 1`, `w` from `tStartW` up to its tick to the view freeze of slot `s`, the holders `v` (`hv₀`)
and `w` (`hw₀`) for the sync delay after the sync fact's read times.

Read aloud: the next slot's honest votes extend every ancestor of a confirmation whose frame and
lock conditions hold at the voter. -/
theorem lem36c_fast_ancestor_extended_held (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (C' L : Block V) (v w : V) (n' : M.N)
    (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`'s window starts at `tStart`, more than both clock bounds before the support cutoff of slot `s + 1`
    -- less six delays or one sync delay, whichever is longer
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ))
    -- `v` is active from `tStart` up to its tick to the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeThroughoutToTick x tStart (M.supportCutoff S.C (s + 1)))
    -- `v` is active at every step whose real time is in the sync delay after the view freeze of slot `s`
    -- less one delay or one sync delay, whichever is longer (the holder's window,, T-RC8-2)
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- `w` is active for the sync delay after the support cutoff of slot `s + 1` less one delay or one sync
    -- delay, whichever is longer (the holder's window,: Lemma 21b reads `w` as a holder through
    -- Lemma 64)
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `v`'s update of slot `s + 1` runs at its tick to the support cutoff of slot `s + 1` (, T-RC8-2)
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    (hSaved : n'.savedConfirmation s = some C')
    (hLC : L.AncestorEq C')
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible L = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq L →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
        (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          L.AncestorEq W)
    (hLocks : ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible L = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ L.AncestorEq H_w := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hm6 : max (6 * Δ S) Δs ≥ 6 * Δ S := le_max_left _ _
  -- `v`'s tick `k_v` to the support cutoff of slot `s + 1`, active from that cutoff less `ΔClockAhead`
  have hslR : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s + 1) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  obtain ⟨k_v, hk_v, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C (s + 1) : ℝ) - ΔClockAhead) (by linarith)
  have hti_v : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  have hRootsΦv : RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti_v]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ v
  -- Lemma 36 at `L`, an ancestor of `C'` or `C'` itself, on `v`'s pool at its tick to the support cutoff of
  -- slot `s + 1`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem36_confirmed_ancestor_early_supporters F)
      C' L hs1 hRootsΦv
      (by
        rw [Nat.add_sub_cancel, hti_v]
        exact (pool_vote_late_of_tick M F U) S A x R s v E k_v hk_v hwinv)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hSaved) hLC
  simp only [Nat.add_sub_cancel] at hSup hElig
  -- the roots until the latest real time of `w`'s tick to the view freeze of slot `s`
  have hRoots' : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind) := by
    refine (RootsNameBlocksUntil.mono M) ?_ hRoots
    have : (M.supportCutoff S.C (s + 1) : ℝ) = (M.viewFreeze S.C s : ℝ) + 3 * Δ S := by
      have h : M.supportCutoff S.C (s + 1) = M.viewFreeze S.C s + 3 * Δ S := by omega
      rw [h]; push_cast; ring
    rw [this]
    linarith
  -- Lemma 21, the held form, at `L`
  exact (lem21b_goldfish_vote_extends_eligible_block_held M F U) S A x R GST s Sup L v w vote E hNet hSkew hRedeliver Sy hΔs
    hRoots' hParent hGST tStart htStart hv tStartW htStartW hw hv₀ hw₀ hSup hElig hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Record.Proofs.Executions

