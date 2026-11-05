module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastBase
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityB6
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Proofs.Executions.Lemma89ChangeJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89RisingJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HealedRound
public import GoldilocksCorrectness.Proofs.Executions.Lemma89WaitJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb5
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Handover
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HandoverVF
public import GoldilocksCorrectness.Statements.Routines.ChainStateOfStatements

@[expose] public section

/-!
# Lemma 89: the events of the phase

## Summary

The final statements, one form each:

- `lem89_phase`: Lemma 89 of record, on the span premise of record
  `OpeningsOutsideWaitsAndWindows` (nine honest round opening slots outside two spans of `δt`
  slots and five spans of `k + 2` slots), from the climb and the hand-over, with the voter frame
  at the last opening's slot in its conclusion.


`ForkChoiceChangeAt` counts a root change only through `get_fc_root`'s first case
;
- `spoiled_near_fork_choice_change_cutoff`, `quiet_top_gives_attestation_cutoff`: B10 and B11
  with `hNoCol` (no root collision) and no `ForkChoiceChangeAt` of an honest validator over the
  opening's window and round;
- `honest_proposer_proposesJ` and its helpers: the proposal kit of `Lemma90Inclusion.lean`, copied;
- `quiet_rising_next_proposal_late`, `quiet_rising_heights_differ_cutoff`,
  `quiet_rising_before_fast_round_le_two_cutoff`, `quiet_waiting_next_proposal`,
  `quiet_waiting_same_entry_cutoff`: the rising and waiting steps (B12 with `hNoCol` and no
  `ForkChoiceChangeAt` over the opening's window and round), with the threshold-time hypothesis
  `T₁ + Δ ≤ slotStart S (rs 0 * R − k − 1)`, needed when `R` divides `2k + 1`;

- C1 `round_base_after_fast_block_opening`: with `hsR : S.C.R ∣ s` (the slot a round's first slot);
- C3 `healed_round_base_of_prev_votes`: with `hNoCol` for the slot and `hPrev` (the votes of slot
  `s − 1` extend the proposer's anchor);
- C2 `quiet_round_after_fast_block_opening`: with `hsR` and `hNoCol`;
- `lem89r_quiet_round_targets`: Lemma 89r with the fresh-height premise replaced by "every member's
  attestation at `h(B)` up to the action time is a target";
- C4 `opening_rises_after_fast_block_opening`: with `hsR`;
- C6 `caches_at_handover_of_held`: with `hHeld` and `hF₃`;
- C9 `opening_proposal_exists_of_window`: for the slots from `2` on.

The audited statements, proved in `GoldilocksCorrectness/Proofs/Executions/Lemma89.lean`:

- `plainCountCeil_implies_waitsAndWindows`: the plain count with ceilings implies the span
  premise of the phase;
- `quietRound_cases`: a round that is not quiet relative to its own confirmations shows a failed
  clause at a member, written out;
- `frontWindowStable_fail_event`: a window that is not stable shows a failed clause at a member,
  written out.

And the first four steps of part A of Lemma 89's skeleton on the fast-confirmation route
, proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma89FastLine.lean`:

- A1 `fast_block_of_honest_attestation`: an honest attestation is built from a fast block of its
  sender's confirmation update;
- A2 `held_height_le_before_action`: before the action time of a round, every honest-held block
  has height at most one more than the bound on the honest attestations sent before it;
- A3 `finalized_ancestor_of_fast_block`: before that time, every honest finalized block is `L`
  or an ancestor of `L`, for an honest-held block `L` one height above that bound;
- A4 `lem36c_fast_ancestor_extended_held`: Lemma 36b with the frame and lock conditions read at an
  ancestor of the saved confirmation.

And A5 `fast_block_base`, proved in `GoldilocksCorrectness/Proofs/Executions/Lemma89FastBase.lean`:
the slot invariant restricted to the fast block at the slot after its round.

And B1 to B4 of part B, proved in `GoldilocksCorrectness/Proofs/Executions/Lemma89Climb.lean`:

- B1 `exists_old_height_attained`: the threshold `H₂` at a time `T₁` exists;
- B2 `honest_h_max_bounds`: from `T₁ + Δ` to the action time of round `r`, every honest `h_max`
  is `H₂` or `H₂ + 1`;
- B3 `first_attestation_above_bound`: the first honest attestation above `H₂` from `T₁` on is at
  a round's action time, and nothing honest above `H₂` was sent at a tick before it;
- B4 `fast_block_at_first_round`: its sender holds a fast block of height exactly `H₂ + 1`.


- A7a `frame_at_time_relative_to_fast_block`, A7b `stepFrame_relative_to_fast_block`: the frames
  relative to `L`;
- A8a `fast_line_invariant_L`: the slot invariant relative to `L` from slot `r * R + 1` on;
- A8d `fast_line_at_later_round`: the slot invariant relative to a later round's honest fast block;
- A8c `confirmations_chain_after_old_locks`: the members' confirmations form one chain from slot
  `r * R + k` on;
- A7c `frame_at_time_relative_to_late_family`, A7d `stepFrame_relative_to_late_family`: the frames
  relative to `FastFamilyFrom … (r * R + k)`;
- A8b `fast_line_invariant_late_family`: the chain and lock invariants for that family from slot
  `r * R + 2k − 1` on;
- `lem89L_one_line_from_fast_block`: part A's assembly.


- B6 `stability_fact3`: a window that is not stable shows a fork-choice change of an honest
  validator from the vote time of slot `s − k − 1` to before the support cutoff of slot `s`, without the skeleton's `hSaved`.

And C1 to C3 of part C on the revised skeleton, each on a copy with added hypotheses, proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma89HealedRound.lean`:

- C1 `round_base_after_fast_block_opening`: the round base at an honest round opening slot after the fast
  block, the slot a round's first slot;
- C3 `healed_round_base_of_prev_votes`: Lemma 89's base facts at a round whose base holds, with the
  previous slot's honest votes extending the proposer's anchor and no root collision;
- C2 `quiet_round_after_fast_block_opening`: every honest round opening slot after the fast block whose
  proposal's root is fresh is quiet relative to its own confirmations.

And the waiting openings' entry, proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma89WaitJ.lean`:

- `honest_proposal_above_h_j`, `change_of_h_j_reaches`, `h_j_lt_of_later_proposal`,
  `J_genesis_of_h_j_le_one`, `h_j_lt_or_genesis_before_cutoff`: before a later honest round opening slot's
  support cutoff, no honest validator holds a justification at that opening's proposal's height.

And part B's climb: the rising and waiting steps with a
later threshold time (`quiet_waiting_next_proposal`, `quiet_waiting_same_entry_cutoff`: two waiting
quiet openings at one height share the height's entry), proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma89ClimbLate.lean`; the count before the climb's end
`climb_count_before` and the climb `climb_to_fast_block` (five spans of `k + 2` slots, count 9),
proved
in `GoldilocksCorrectness/Proofs/Executions/Lemma89Climb5.lean`.

And part C's carrier and hand-over, proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma89Handover.lean`, two of them on copies:

- C4 `opening_rises_after_fast_block_opening`: consecutive honest round opening slots after the fast block
  rise, the next one carrying the justification (the slot a round's first slot);
- C5 `round_justified_of_spacing3`: the next opening within `δt` of the entry inherits the
  justification;
- C6 `caches_at_handover_of_held`: the caches at the hand-over step (the proposal held, the
  finalized blocks on it);
- C7 `frames_at_phase_slots`: Lemma 89's frame clauses;
- C8 `exists_handover_step`: some step is at the vote time of the last opening's slot;
- C9 `opening_proposal_exists_of_window`: an honest proposer awake through its proposal window
  proposes (slots from `2` on);
- `handover_after_fast_block`: the hand-over, part C's assembly;
- `lem89_phase`: Lemma 89, from the climb and the hand-over's copy with the voter frame (proved in
  `Lemma89HandoverVF.lean`).


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart proposalWindowStart anchorCW)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks ProgressCertOn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **The plain count with ceilings implies the span premise of the phase.** When the rounds
`r 0 < … < r m` increase and `9 + 2 ⌈δt / R⌉ + 5 ⌈(k + 2) / R⌉ ≤ m`, then for every choice
of two spans of `δt` slots and five spans of `k + 2` slots, at least 9 of the honest round opening
slots fall outside all of them (`OpeningsOutsideWaitsAndWindows`). In `ℕ`, `⌈x / R⌉` is written
`(x + R − 1) / R`.

Why: a span of `L` slots holds at most `⌈L / R⌉` honest round opening slots, these being at least
`R` slots apart; the `m + 1` honest round opening slots `r 0, …, r m` then leave at least
`m + 1 − 2 ⌈δt / R⌉ − 5 ⌈(k + 2) / R⌉ ≥ 9` outside the seven spans.

The variables:
- `S`: the setup; `r`: the rounds; `m`: the index of the last honest round opening slot.

Read aloud: if the rounds `r 0, …, r m` increase and `m` is at least
`9 + 2 ⌈δt / R⌉ + 5 ⌈(k + 2) / R⌉`, then however two spans of `δt` slots and five of `k + 2` slots
are placed, at least nine of the honest round opening slots fall outside all seven. -/
theorem plainCountCeil_implies_waitsAndWindows (S : Setup V) (r : ℕ → ℕ) (m : ℕ)
    -- the rounds increase
    (hMono : ∀ i : ℕ, i < m → r i < r (i + 1))
    -- the plain count, with the ceilings `(L + R − 1) / R`
    (hm : 9 + 2 * ((S.C.δt + S.C.R - 1) / S.C.R) + 5 * ((S.C.k + 2 + S.C.R - 1) / S.C.R) ≤ m) :
    OpeningsOutsideWaitsAndWindows S r m :=
  GoldilocksCorrectness.Proofs.Executions.plainCountCeil_implies_waitsAndWindows S r m hMono hm

/-- **A round that is not quiet relative to its own confirmations.** When
`QuietRoundOnConfirmations S Sched x Hon B s s''` fails: some member of `Hon s` has its root off
`B.parent`'s chain or its `head_height_floor` past `h(B.parent)` before the vote time of slot `s`,
or its root off `B`'s chain or its `head_height_floor` past `h(B)` before the action time; or at a
slot `s'` of the round some member of `Hon (s' + 1)` fails `StepFrameAt` relative to `B`; or
relative to a confirmation a member of `Hon σ` saved for a slot `σ` from `s − 1` to `s'`; or the
proposer of slot `s''`, before the start of slot `s''`, has for no confirmation of slot `s'' − 2`
saved by a member of `Hon (s'' − 2)` both its root on that confirmation's chain and a viable head
that is that confirmation or a descendant of it. The confirmations of a slot are those the members
of the slot's own set save, the updaters of the slot in the phase.

Why: it is the negation of `QuietRoundOnConfirmations`, its first two clauses split into the root
and the `head_height_floor`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon`: one member set per slot;
- `B`: the round's proposal; `s`: its first slot; `s''`: the next honest round opening slot.

Read aloud: a round that is not quiet shows a member's root off the chain or its
`head_height_floor` past the clause's height, a failed step condition, or the next proposer off
every last confirmation. -/
theorem quietRound_cases (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ)
    -- the round is not quiet relative to its own confirmations
    (hNotQuiet : ¬ QuietRoundOnConfirmations S Sched x Hon B s s'') :
    (∃ w ∈ Hon s,
      RootOffChainAt S Sched x w (voteTime S s) B.parent ∨
      HeadHeightFloorPastAt S Sched x w (voteTime S s) (chainStateOf S.C B.parent).h ∨
      RootOffChainAt S Sched x w (supportCutoff S (s + 1)) B ∨
      HeadHeightFloorPastAt S Sched x w (supportCutoff S (s + 1)) (chainStateOf S.C B).h) ∨
    (∃ s', s ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ w ∈ Hon (s' + 1), ¬ StepFrameAt S Sched x B s' w) ∨
    (∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ σ, s - 1 ≤ σ ∧ σ ≤ s' ∧ ∃ v ∈ Hon σ,
      ∃ C : Block V,
        (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C ∧
        ∃ w ∈ Hon (s' + 1), ¬ StepFrameAt S Sched x C s' w) ∨
    (∀ C : Block V,
      (∃ v ∈ Hon (s'' - 2),
        (stateBefore x (supportCutoff S (s'' - 1) + 1) v).A.saved_confirmation (s'' - 2) =
          some C) →
      ¬ ((fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).fc_root.AncestorEq C ∧
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).viable_heads ∧
          C.AncestorEq W)) :=
  GoldilocksCorrectness.Proofs.Executions.quietRound_cases S Sched x Hon B s s'' hNotQuiet

/-- **A failure of `FrontWindowStable`, written out.** Under the member sets shrinking from one slot
to the next and every member of the set of a slot honest at the support cutoff of the next slot:
when `FrontWindowStable S Sched x Hon s_w s'` fails, one of four things happens, each at a member
`w` of a set `Hon s₁` with `s_w + k − 1 ≤ s₁ ≤ s'`:

1. `w`, a member of `Hon (s₁ + 1)` with `s₁ < s'`, has its root before `voteTime S (s₁ + 1)` in
   conflict with a confirmation `X` a member saved for a slot from `s_w + k − 1` to `s₁`
   (`RootIncompatibleAt`);
2. or that root is `X` or an ancestor of such an `X`, `w` holds `X` then, and no block of `w`'s
   voter tree of slot `s₁ + 1` that is `X` or a descendant of `X` is a viable head;
3. or `w`'s finalized block before `supportCutoff S (s₁ + 2)` conflicts with such an `X`
   (`FinalizedIncompatibleAt`);
4. or, at `s₁ = s'`, `w`'s root before `voteTime S (s' + 1)` is `D` or an ancestor of `D` for no
   block `D` of a live lock entry of a member of `Hon s'` and no confirmation `D` of slot `s' − 1`
   of a member of `Hon s'` (`RootOffChainAt` at every such `D`).

Why: the two clauses of `FrontWindowStable` negated; the failure of the first is a failed
`StepFrameAt` (`stepFrameAt_fail_cases`), where `w` holds `X` in the second case by the delivery
of the saver's own copy.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase, in which every honest validator is
  awake; `s_w`: the slot the window is counted from; `s'`: its last slot; `Hon`: one member set
  per slot.

Roots name blocks until `supportCutoff S (s' - 1) + Δ S`: `stepFrameAt_fail_cases` at a slot `σ`
at most `s' − 1`.

Read aloud: a window breaks at a member whose root or finalized block conflicts with a window
confirmation, whose frame finds no viable head on a confirmation's chain, or whose root is on no
family block's chain at the window's last slot. -/
theorem frontWindowStable_fail_event (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' - 1) + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x)
    -- the network is synchronous from `tGAT` on; the window has at least `2k − 1` slots
    (hGST : GST ≤ tGAT) (hs' : s_w + 2 * S.C.k - 1 ≤ s')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁)
    -- every member of the set of slot `s₁` is honest at the support cutoff of slot `s₁ + 1`
    (hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
      v ∉ Sched.adv ((supportCutoff S (s₁ + 1) : ℕ) : Int))
    -- every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    -- the duty window of slot `s_w` starts at or after `tGAT`; the support cutoff of slot
    -- `s' + 1` is inside the phase
    (hsw : tGAT ≤ dutyWindowStart S s_w) (hEnd : supportCutoff S (s' + 1) ≤ tAwakeEnd)
    -- the window is not stable
    (hFail : ¬ FrontWindowStable S Sched x Hon s_w s') :
    ∃ (s₁ : ℕ) (w : V), s_w + S.C.k - 1 ≤ s₁ ∧ s₁ ≤ s' ∧ w ∈ Hon s₁ ∧
      ((∃ X : Block V, WindowConfirmation S Sched x Hon (s_w + S.C.k - 1) s₁ X ∧ s₁ < s' ∧
          w ∈ Hon (s₁ + 1) ∧
          (RootIncompatibleAt S Sched x w (voteTime S (s₁ + 1)) X ∨
            ((get_fc_root (stateBefore x (voteTime S (s₁ + 1)) w).S).AncestorEq X ∧
              X ∈ (stateBefore x (voteTime S (s₁ + 1)) w).S.T ∧
              ∀ tree : Finset (Block V),
                voter_block_tree S.C (stateBefore x (voteTime S (s₁ + 1)) w).A
                  (fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S) (s₁ + 1) = .ok tree →
                ¬ ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s₁ + 1)) w).S).viable_heads ∧
                  X.AncestorEq W) ∨
            FinalizedIncompatibleAt S Sched x w (supportCutoff S (s₁ + 2)) X)) ∨
        (s₁ = s' ∧ ∀ D : Block V,
          ((∃ u ∈ Hon s', ∃ e ∈ (stateBefore x (voteTime S (s' + 1)) u).A.lock_entries,
              is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
                ((voteTime S (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
            ∃ v ∈ Hon s',
              (stateBefore x (supportCutoff S s' + 1) v).A.saved_confirmation (s' - 1) = some D) →
          RootOffChainAt S Sched x w (voteTime S (s' + 1)) D)) :=
  GoldilocksCorrectness.Proofs.Executions.frontWindowStable_fail_event S Sched x GST tGAT tAwakeEnd
    s_w s' Hon hDiv hMono hSync hCatch hRoots hParent hGST hs' hHonMono hHon hAwake hsw hEnd
    hFail

/-- **A1, an honest attestation is built from a fast block of its sender's update.** When `v`,
awake and honest at the action time `aR S r` of round `r`, put the attestation `a` on the wire at
its tick then, the confirmation update of slot `r * R + 1`, on `v`'s state before `aR S r` with its
expired lock entries removed, answers some `A'`; and some fast block `L` of `A'`, held by `v`
before `aR S r`, has `a`'s height as its chain-state height.

Why: the tick's attestation is the duty's (Lemma 49); the duty's source is the deepest fast block
of the tick's final AC state in the viable tree (`ac_to_fg`), and that AC state's fast blocks are
the update's answer's (Lemma 15); `fg_attest` sets the height to the source's chain-state height;
the source is a block of the frame's tree, held before the tick.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `v`: the attester;
  `a`: the attestation.

Read aloud: whoever attests at height `h` has just fast-confirmed a block of height `h`.

 -/
theorem fast_block_of_honest_attestation (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (r : ℕ) (v : V) (a : Attestation V)
    -- `v`, awake and honest at the action time of round `r`, sent `a` at its tick then
    (hSend : HonestAttestationAt S Sched x (aR S r) v a) :
    ∃ (A' : ACState V) (L : Block V),
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A' ∧
      L ∈ A'.fast_blocks ∧ L ∈ (stateBefore x (aR S r) v).S.T ∧
      (chainStateOf S.C L).h = a.h :=
  GoldilocksCorrectness.Proofs.Executions.fast_block_of_honest_attestation S Sched x r v a hSend

/-- **A2, before `a_r` every honest-held block has height at most `H₂ + 1`.** Under
unforgeability, with fewer than a third of the validators in the adversary set up to `tAwakeEnd`:
when every honest attestation sent before `aR S r` has height at most `H₂` and `t ≤ aR S r ≤
tAwakeEnd`, every block `w` holds before `t` has chain-state height at most `H₂ + 1`.

Why: `attested_height_bound` at the step `stepBefore x t`, whose time is at most `t − 1` (or `0`,
with no tick before it, when `t = 0`), so the bound `hOld` covers every tick up to it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end;
- `r`: the round; `H₂`: the bound on the old attestations; `t`: the time; `w`: the holder;
  `D`: the block.

Read aloud: nothing climbs past `H₂ + 1` before the first attestation above `H₂`.

 -/
theorem held_height_le_before_action (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tAwakeEnd r H₂ t : ℕ) (w : V) (D : Block V)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (htr : t ≤ aR S r) (hEnd : aR S r ≤ tAwakeEnd)
    (hD : D ∈ (stateBefore x t w).S.T) :
    (chainStateOf S.C D).h ≤ H₂ + 1 :=
  GoldilocksCorrectness.Proofs.Executions.held_height_le_before_action S Sched x tAwakeEnd r H₂ t w
    D hU hThird hOld htr hEnd hD

/-- **A3, before `a_r` every honest finalized block is `L` or an ancestor of `L`.** Under
unforgeability, roots naming blocks, permanent corruption and fewer than a third of the validators
in the adversary set up to `tAwakeEnd`: when every honest attestation sent before `aR S r` has
height at most `H₂`; `v` is honest at `aR S r` and holds `L` before it, with `L`'s chain-state
height `H₂ + 1`; and `w` is honest at a time `t ≤ aR S r ≤ tAwakeEnd` — then `w`'s finalized block
before `t` is `L` or an ancestor of `L`.

Why: `w`'s finalized block is the finalized block of the chain state of a held block `D`
(`finalizedFromChain_of_exec`), at a height `h_F(D) ≤ h_j(D) < h(D) ≤ H₂ + 1` (Lemma 47 (a), A2),
so `h_F(D) < h(L)`, and Lemma 89a with `v` holding `L` gives `F ⪯ L`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end;
- `r`: the round; `H₂`: the bound on the old attestations; `t`: the time; `v`: the holder of `L`;
  `w`: the validator whose finalized block is read; `L`: the block.

Roots name blocks until `aR S r`: the proof compares (Lemma 89a) the block `B` `w` holds before
`t` with `L`, which `v` holds before `aR S r`, and `t ≤ aR S r`.

Read aloud: no honest validator has finalized anything the fast block does not extend.

 -/
theorem finalized_ancestor_of_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tAwakeEnd r H₂ t : ℕ) (v w : V) (L : Block V)
    (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int)) (hLv : L ∈ (stateBefore x (aR S r) v).S.T)
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (htr : t ≤ aR S r) (hw : w ∉ Sched.adv (t : Int)) :
    (stateBefore x t w).S.F.AncestorEq L :=
  GoldilocksCorrectness.Proofs.Executions.finalized_ancestor_of_fast_block S Sched x tAwakeEnd r H₂
    t v w L hMono hU hRoots hThird hOld hEnd hv hLv hL htr hw

/-- **A4, a confirmed block's ancestor is extended by the next slot's honest votes, the held
form.** Lemma 36b's hypotheses (`lem36b_confirmed_block_extended_held`), with the frame and lock
conditions at `w` read against a block `L` that is `C'` or an ancestor of `C'`, in place of `C'`
itself: then `w`'s vote at the vote time of slot `s + 1` is its slot-`(s + 1)` vote for a block
`H_w` it holds then, and `H_w` is `L` or a descendant of `L`.

Why: Lemma 36 at `L` (`C'` or an ancestor of the saved `C'`) gives the set `Sup` of early
supporters of `L` at `v` with `v`'s late voters fewer than twice `Sup`; then Lemma 21 in the held
form at `L`, as Lemma 36b's proof calls it at `C'`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose confirmation `v`'s update of slot `s + 1` saves;
- `C'`: the saved confirmation; `L`: `C'` or an ancestor of it; `v`: the validator whose update
  saves `C'`; `w`: the voter of slot `s + 1`; `A'`: the update's answer; `vote`: `w`'s Goldfish
  vote.

Roots name blocks until `supportCutoff S (s + 1)`: the proof reads Lemma 21 in the held form at
slot `s`, whose bound is that time.

Read aloud: the next slot's honest votes extend every ancestor of a confirmation whose frame and
lock conditions hold at the voter.

 -/
theorem lem36c_fast_ancestor_extended_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (C' L : Block V) (v w : V) (A' : ACState V)
    (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ supportCutoff S s)
    (hv : ∀ t : ℕ, voteTime S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    (hSaved : A'.saved_confirmation s = some C')
    -- `L` is `C'` or an ancestor of `C'`
    (hLC : L.AncestorEq C')
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible L = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq L →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          L.AncestorEq W)
    (hLocks : ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible L = true)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ L.AncestorEq H_w :=
  GoldilocksCorrectness.Proofs.Executions.lem36c_fast_ancestor_extended_held S Sched x GST s C' L v
    w A' vote hDiv hMono hSync hCatch hRoots hParent hGST hv hw hUpdate hSaved hLC hF2 hF3
    hLocks hSend

/-- **A5, the slot invariant restricted to `L` at slot `r * R + 1`.** Under the eight execution
assumptions and unforgeability, with `GST ≤ tGAT`, fewer than a third of the validators in the
adversary set up to `tAwakeEnd`, every honest validator awake from `tGAT` to `tAwakeEnd`, committee
sleepiness from `anchorCW S tGAT` and slot `r * R + 1` starting at or after it, and
`supportCutoff S (r * R + 2) ≤ tAwakeEnd`: when every honest attestation sent before `aR S r` has
height at most `H₂`; `v` is honest at `aR S r`; `v`'s update of slot `r * R + 1` at `aR S r`
answers `A'` with `L` among its fast blocks; and `L`'s chain-state height is `H₂ + 1` — then
`HonestChainExtends S Sched x (Hon S Sched (r * R + 1)) L (r * R + 1)`: every slot-`(r * R + 1)`
vote of a member of `Hon S Sched (r * R + 1)` is for a block it holds that is `L` or a descendant
of `L`, every lock entry a member's revocation of slot `r * R + 2` leaves live is compatible with
`L`, and every confirmation of slot `r * R + 1` a member saves is `L` or a descendant of `L`.

Why: `L` is an ancestor of `v`'s saved confirmation of slot `r * R`, so Lemma 36 gives its early
supporters at `v`. At every member: its finalized block before the vote time of slot `r * R + 1`
is an ancestor of `L` (A3); `L` reaches it before the view freeze of slot `r * R` with an early
supporter's vote (Lemma 63); its `h_max` is then `H₂ + 1` (A2), so its fork-choice root is an
ancestor of `L` (the contest rule) and `L` is a viable head of its voter tree; Lemma 42 makes its
locks compatible with `L`; A4 gives the vote. The live locks of slot `r * R + 1` come from older
entries (Lemma 42) or from the member's confirmation of slot `r * R`, compatible with `v`'s
(Lemma 31). The confirmations: Lemma 79c with the honest committee voters of slot `r * R + 1`,
every member's finalized block being compatible with `L` (Lemma 89a at heights at most `H₂`; above
`H₂` an entry of the honest chain at slot `r * R`, `cert_entry_at_slot` and Lemma 31).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the
  bound on the old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast
  block; `A'`: the update's answer.

Roots name blocks until `supportCutoff S (r * S.C.R + 2)`: `finalized_compatible_fast_block` at
the support cutoff of slot `r * R + 2`, for the confirmations of slot `r * R + 1`; the other
steps read up to the support cutoff of slot `r * R + 1`.

Read aloud: the slot after the fast block's round, every honest vote, live lock and confirmation
extends the fast block.

 -/
theorem fast_block_base (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (r * S.C.R + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hEnd : supportCutoff S (r * S.C.R + 2) ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1) :
    HonestChainExtends S Sched x (Hon S Sched (r * S.C.R + 1)) L (r * S.C.R + 1) :=
  GoldilocksCorrectness.Proofs.Executions.fast_block_base S Sched x GST tGAT tAwakeEnd r H₂ v L A'
    hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake hCommittees hAnchor
    hEnd hOld hv hUpdate hFast hL

/-- **B1, the threshold exists.** In an execution that reaches every time, for every time `T₁`
there is an `H₂` with `OldHeightAttained S Sched x T₁ H₂`: every attestation an honest awake
validator put on the wire at a tick before `T₁` has height at most `H₂`, and `H₂` is `0` or the
height of such an attestation.

Why: the attestations put on the wire at ticks before `T₁` are in the finite sent log of the
configuration `x[stepBefore x T₁]`; `H₂` is the least bound on the heights of the honest ones.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `T₁`: the time.

Read aloud: there is a greatest height the honest validators attested before `T₁`.

 -/
theorem exists_old_height_attained (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (T₁ : ℕ)
    (hDiv : TimeDiverges x.toTrace) :
    ∃ H₂ : ℕ, OldHeightAttained S Sched x T₁ H₂ :=
  GoldilocksCorrectness.Proofs.Executions.exists_old_height_attained S Sched x T₁ hDiv

/-- **B2, the honest `h_max` from `T₁ + Δ` to `a_r`.** Under the execution assumptions and
unforgeability, with `GST ≤ tGAT ≤ T₁`, fewer than a third of the validators in the adversary set
up to `tAwakeEnd`, and every honest validator awake through the phase: when `H₂` is the threshold
at `T₁` (`OldHeightAttained`), every honest attestation sent before `aR S r` has height at most
`H₂`, `aR S r ≤ tAwakeEnd`, and `w` is honest at a time `t` with `T₁ + Δ ≤ t ≤ aR S r` — then
`w`'s `h_max` before `t` is at least `H₂` and at most `H₂ + 1`.

Why: at least `H₂` by Lemma 89b at the honest attestation of height `H₂` sent before `T₁` (when
`H₂ ≠ 0`); at most `H₂ + 1` because `h_max` is the chain-state height of a block `w` holds, which
A2 bounds.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `T₁`: the time of the
  threshold; `r`: the round; `H₂`: the threshold; `t`: the time; `w`: the validator.

Roots name blocks until `t`: the proof reads `lem89b_at` at `b := t`, `w`'s reading time.

Read aloud: once the phase has settled, every honest validator knows the threshold's height and
nothing higher than one more than it, until the first attestation above it.

 -/
theorem honest_h_max_bounds (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ t : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t' : ℕ, tGAT ≤ t' → t' ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t' : Int) → u ∈ Sched.awake (t' : Int))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (ht₁ : T₁ + Δ S ≤ t) (htr : t ≤ aR S r) (hw : w ∉ Sched.adv (t : Int)) :
    H₂ ≤ (stateBefore x t w).S.h_max ∧ (stateBefore x t w).S.h_max ≤ H₂ + 1 :=
  GoldilocksCorrectness.Proofs.Executions.honest_h_max_bounds S Sched x GST tGAT tAwakeEnd T₁ r H₂ t
    w hDiv hMono hSync hCatch hRoots hParent hU hGST hT₁ hThird hAwake hH₂ hOld hEnd ht₁ htr
    hw

/-- **B3, the first honest attestation above `H₂`.** When `H₂` is the threshold at `T₁` and some
validator honest and awake at a tick time `t₀ ≥ T₁` put an attestation of height greater than
`H₂` on the wire at that tick, then there is a round `r` with `T₁ ≤ aR S r ≤ t₀`, an honest
attestation above `H₂` at `aR S r`, and every honest attestation sent at a tick before `aR S r` of
height at most `H₂`.

Why: an attestation is sent only at the action time of a round (Lemma 49); take the least time at
or after `T₁` with an honest attestation above `H₂`; before `T₁`, `OldHeightAttained` bounds the
heights; between `T₁` and that time, the minimality does.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `T₁`: the time of the threshold;
  `H₂`: the threshold; `t₀`: the time of the given attestation; `u`: its sender; `a₀`: the
  attestation.

Read aloud: the first time an honest validator attests above the threshold is a round's action
time, and before it nothing honest was above the threshold.

 -/
theorem first_attestation_above_bound (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (T₁ H₂ t₀ : ℕ) (u : V) (a₀ : Attestation V)
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (ht₀ : T₁ ≤ t₀) (hSend : HonestAttestationAt S Sched x t₀ u a₀) (ha₀ : H₂ < a₀.h) :
    ∃ r : ℕ, T₁ ≤ aR S r ∧ aR S r ≤ t₀ ∧ OldAttestationsAtMost S Sched x (aR S r) H₂ ∧
      ∃ (v : V) (a : Attestation V), HonestAttestationAt S Sched x (aR S r) v a ∧ H₂ < a.h :=
  GoldilocksCorrectness.Proofs.Executions.first_attestation_above_bound S Sched x T₁ H₂ t₀ u a₀ hH₂
    ht₀ hSend ha₀

/-- **B4, the fast block at the first round above the threshold.** Under unforgeability and fewer
than a third of the validators in the adversary set up to `tAwakeEnd`: when every honest
attestation sent before `aR S r` has height at most `H₂`, `aR S r ≤ tAwakeEnd`, and `v`, honest and
awake at `aR S r`, sent an attestation `a` of height greater than `H₂` at its tick then, then `v`'s
update of slot `r * R + 1` at `aR S r` answers some `A'`, and some fast block `L` of `A'`, held by
`v` before `aR S r`, has chain-state height exactly `H₂ + 1`.

Why: A1 gives the fast block `L` with `h(L) = a.h > H₂`; A2 at `t := aR S r` and `w := v` bounds
`h(L) ≤ H₂ + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end; `r`:
  the round; `H₂`: the bound on the old attestations; `v`: the attester; `a`: the attestation.

Read aloud: the first honest validator above the threshold has just fast-confirmed a block exactly
one height above it.

 -/
theorem fast_block_at_first_round (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tAwakeEnd r H₂ : ℕ) (v : V) (a : Attestation V)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂) (hEnd : aR S r ≤ tAwakeEnd)
    (hSend : HonestAttestationAt S Sched x (aR S r) v a) (ha : H₂ < a.h) :
    ∃ (A' : ACState V) (L : Block V),
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A' ∧
      L ∈ A'.fast_blocks ∧ L ∈ (stateBefore x (aR S r) v).S.T ∧
      (chainStateOf S.C L).h = H₂ + 1 :=
  GoldilocksCorrectness.Proofs.Executions.fast_block_at_first_round S Sched x tAwakeEnd r H₂ v a hU
    hThird hOld hEnd hSend ha


/-! ## Part A on the revised skeleton: A6 to A8d and the assembly -/

/-- **A6, a certificate at a height greater than `H₂` names an entry of the honest chain from slot
`r * R`.** Under unforgeability, permanent corruption and fewer than a third of the validators in
the adversary set up to `tAwakeEnd`: when every honest attestation sent before `aR S r` has height
at most `H₂`, the step `j` is at a time at most `tAwakeEnd`, `w` holds `B` after `j` steps, and
`B`'s chain carries a progress certificate at a height `h > H₂` naming `T`'s root, then `T`'s root
is the root of an entry block of the honest chain from slot `r * R` at the height `h`.

Why: Lemma 83 with `s₀ := r * R` and `t₀ := aR S r`; its `hAgree` is Lemma 82 at `s₀ := r * R`; its
`hAdvQ` from `hThird` through `fewerThanQuorum_of_fewerThanThird`; its `hOld` in the honest-at form
from the landed form.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end; `r`: the
  round; `H₂`: the bound on the old attestations; `j`: the step; `w`: the holder; `B`: the held
  block; `T`: the block the certificate names; `h`: its height.

Read aloud: once the fast block's round has acted, every certificate at a height greater than the
old evidence is honest and on the chain the fast block started.

 -/
theorem certificate_on_fast_line (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tAwakeEnd r H₂ j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hj : x[j].time ≤ tAwakeEnd)
    (hB : B ∈ (x[j][w].st).S.T) (hJ : ProgressCertOn B h T) (hH : H₂ < h) :
    ∃ E : Block V, OnHonestChain S Sched x (r * S.C.R) E ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = h ∧ T.root = E.root :=
  GoldilocksCorrectness.Proofs.Executions.certificate_on_fast_line S Sched x tAwakeEnd r H₂ j w B T
    h hDiv hMono hU hThird hOld hj hB hJ hH

/-- **A7a, the frame of an honest validator relative to the fast block.** A5's hypotheses (the
execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks, `h(L) = H₂ + 1`);
a slot `s ≥ r * R + 1`; a time `t` from the vote time of slot `s + 1` to the support cutoff of slot
`s + 2`, inside the phase; and `w` honest at `t` — then the root of `w`'s fork choice before `t` is
compatible with `L`; when that root is `L` or an ancestor of `L`, some viable head of `w`'s frame is
`L` or a descendant of `L`; and `w`'s finalized block before `t` is compatible with `L`.

The skeleton's hypothesis `hInvL` (the slot invariant relative to `L` at every slot from `r * R + 1`
to `s`) is not a hypothesis: the proof does not read it, A5's hypotheses giving the whole invariant.

Why: the line invariant of `Proofs/Executions/Lemma89FastFamily.lean` (`PartAHyps.lineInv_all`): at
every slot of the phase, every honest vote, live lock and confirmation extends every line source of
an earlier slot `μ` (an ancestor of, or equal to, a block of a member's confirmation of slot `μ`
that is: fast at the height `H₂ + 1` when `μ = r * R`; fast or passing the slow test when
`μ ≥ r * R + 1`; any block when `μ ≥ r * R + k`). At heights at most `H₂` the root and the finalized
block are ancestors of `L` (Lemma 89a, the contest rule); at greater heights they are the entry of a
fast block of an honest attester's update at the action time of a round `r' ≥ r` (A1, Lemma 66), a
line source; a viable head is `L`, or the entry at `h_max − 1`, the state not being contested.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `A'`: the
  update's answer;
- `s`: the slot; `t`: the reading time; `w`: the reader.

Roots name blocks until `supportCutoff S (s + 2)`: the bundle `PartAHyps` is built with its end
time `supportCutoff S (s + 2)`, the latest time its kit reads here.

Read aloud: after the fast block's round, every honest validator's finality gadget lets it follow
the fast block.

 -/
theorem frame_at_time_relative_to_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s t : ℕ) (v w : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t' : ℕ, tGAT ≤ t' → t' ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t' : Int) → u ∈ Sched.awake (t' : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    -- the reading time, from the vote time of slot `s + 1` to the update of slot `s + 1`
    (hs : r * S.C.R + 1 ≤ s) (hts : voteTime S (s + 1) ≤ t)
    (ht : t ≤ supportCutoff S (s + 2)) (hEnd : supportCutoff S (s + 2) ≤ tAwakeEnd)
    (hw : w ∉ Sched.adv (t : Int)) :
    (fg_to_ac (stateBefore x t w).S).fc_root.compatible L = true ∧
    ((fg_to_ac (stateBefore x t w).S).fc_root.AncestorEq L →
      ∃ W ∈ (fg_to_ac (stateBefore x t w).S).tree,
        W ∈ (fg_to_ac (stateBefore x t w).S).viable_heads ∧ L.AncestorEq W) ∧
    (stateBefore x t w).S.F.compatible L = true :=
  GoldilocksCorrectness.Proofs.Executions.frame_at_time_relative_to_fast_block S Sched x GST tGAT
    tAwakeEnd r H₂ s t v w L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird
    hAwake hCommittees hAnchor hOld hv hUpdate hFast hL hs hts ht hEnd hw

/-- **A7b, the chain step's frame conditions relative to the fast block.** A5's hypotheses (the
execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks, `h(L) = H₂ + 1`);
a slot `s ≥ r * R + 1` whose support cutoff of slot `s + 2` is at most `tAwakeEnd` — then every
member `w` of `Hon S Sched (s + 1)` satisfies `StepFrameAt S Sched x L s w`.

The skeleton's hypothesis `hInvL` is not a hypothesis: the proof does not read it.

Why: A7a's argument at the vote time of slot `s + 1` and at the support cutoff of slot `s + 2`; the
viable head is held before the view freeze of slot `s`, so it is in the voter tree of slot `s + 1`
(`proposal_viable_head_at`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `A'`: the
  update's answer;
- `s`: the slot of the step.

Roots name blocks until `supportCutoff S (s + 2)`: the bundle `PartAHyps` is built with its end
time `supportCutoff S (s + 2)`, the latest time its kit reads here.

Read aloud: every member's vote and update of the next slot can follow the fast block.

 -/
theorem stepFrame_relative_to_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t' : ℕ, tGAT ≤ t' → t' ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t' : Int) → u ∈ Sched.awake (t' : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hs : r * S.C.R + 1 ≤ s) (hEnd : supportCutoff S (s + 2) ≤ tAwakeEnd) :
    ∀ w ∈ Hon S Sched (s + 1), StepFrameAt S Sched x L s w :=
  GoldilocksCorrectness.Proofs.Executions.stepFrame_relative_to_fast_block S Sched x GST tGAT
    tAwakeEnd r H₂ s v L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird
    hAwake hCommittees hAnchor hOld hv hUpdate hFast hL hs hEnd

/-- **A8a, the slot invariant relative to `L` at every slot of the phase from `r * R + 1`.** A5's
hypotheses (the execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at
`a_r`, `v`'s update of slot `r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks,
`h(L) = H₂ + 1`) — then at every slot `s ≥ r * R + 1` whose support cutoff of slot `s + 2` is at
most `tAwakeEnd`, `HonestChainExtends S Sched x (Hon S Sched s) L s`.

Why: the line invariant of `Proofs/Executions/Lemma89FastFamily.lean` (`PartAHyps.lineInv_all`): at
every slot of the phase, every honest vote, live lock and confirmation extends every line source of
an earlier slot `μ` (an ancestor of, or equal to, a block of a member's confirmation of slot `μ`
that is: fast at the height `H₂ + 1` when `μ = r * R`; fast or passing the slow test when
`μ ≥ r * R + 1`; any block when `μ ≥ r * R + k`), at the line source `L`; its base at slot
`r * R + 1` is A5.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `A'`: the
  update's answer;
- `s`: the slot.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

Read aloud: from the slot after the fast block's round to the end of the phase, every honest vote,
live lock and confirmation extends the fast block.

 -/
theorem fast_line_invariant_L (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x tAwakeEnd)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1) :
    ∀ s : ℕ, r * S.C.R + 1 ≤ s → supportCutoff S (s + 2) ≤ tAwakeEnd →
      HonestChainExtends S Sched x (Hon S Sched s) L s :=
  GoldilocksCorrectness.Proofs.Executions.fast_line_invariant_L S Sched x GST tGAT tAwakeEnd r H₂ v
    L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake hCommittees
    hAnchor hOld hv hUpdate hFast hL

/-- **A8d, every later honest fast block is extended by everything after its round.** A5's
hypotheses (the execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at
`a_r`, `v`'s update of slot `r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks,
`h(L) = H₂ + 1`) for `r`, `v`, `L`, `A'`; a round `r' ≥ r`; a validator `u` honest at `aR S r'`
whose update of slot `r' * R + 1` at `aR S r'` answers `A_u` with `X` among its fast blocks — then
at every slot `σ ≥ r' * R + 1` whose support cutoff of slot `σ + 2` is at most `tAwakeEnd`,
`HonestChainExtends S Sched x (Hon S Sched σ) X σ`.

Why: `X` is a line source of slot `r' * R` (`source_later`: a fast block of slot `r' * R` for
`r' > r`; for `r' = r`, at the height `H₂ + 1`, or an ancestor of `L`, A2 bounding its height by
`H₂ + 1`), and the line invariant of `Proofs/Executions/Lemma89FastFamily.lean`
(`PartAHyps.lineInv_all`): at every slot of the phase, every honest vote, live lock and confirmation
extends every line source of an earlier slot `μ` (an ancestor of, or equal to, a block of a member's
confirmation of slot `μ` that is: fast at the height `H₂ + 1` when `μ = r * R`; fast or passing the
slow test when `μ ≥ r * R + 1`; any block when `μ ≥ r * R + k`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `A'`: the
  update's answer;
- `r'`: the later round; `u`: the validator whose update makes `X` fast; `X`: the fast block; `A_u`:
  that update's answer.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

Read aloud: once an honest validator fast-confirms a block at a round's action time after the fast
block's round, every later honest vote, live lock and confirmation of the phase extends it.

 -/
theorem fast_line_at_later_round (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ r' : ℕ) (v u : V) (L X : Block V)
    (A' A_u : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x tAwakeEnd)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    -- a later round's honest fast block
    (hr' : r ≤ r') (hu : u ∉ Sched.adv ((aR S r' : ℕ) : Int))
    (hUpdate_u : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r') u).A ((aR S r' : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r') u).S) ((aR S r' : ℕ) : Int) (r' * S.C.R + 1) = .ok A_u)
    (hFast_u : X ∈ A_u.fast_blocks) :
    ∀ σ : ℕ, r' * S.C.R + 1 ≤ σ → supportCutoff S (σ + 2) ≤ tAwakeEnd →
      HonestChainExtends S Sched x (Hon S Sched σ) X σ :=
  GoldilocksCorrectness.Proofs.Executions.fast_line_at_later_round S Sched x GST tGAT tAwakeEnd r H₂
    r' v u L X A' A_u hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hAnchor hOld hv hUpdate hFast hL hr' hu hUpdate_u hFast_u

/-- **A8c, the members' confirmations form one chain from slot `r * R + k` on.** A5's hypotheses
(the execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks, `h(L) = H₂ + 1`)
— then for every slot `s` whose support cutoff of slot `s + 2` is at most `tAwakeEnd`,
`ConfirmationsChainOn S Sched x (roundMembers S Sched) (r * R + k) s`: a confirmation a member saved
for a slot `σ` from `r * R + k` to `s` is an ancestor of, or equal to, one a member saved for a
later slot of that range, and compatible with one of the same slot.

Why: a member's confirmation of a slot `σ ≥ r * R + k` is a line source of slot `σ`, and the line
invariant of `Proofs/Executions/Lemma89FastFamily.lean` (`PartAHyps.lineInv_all`): at every slot of
the phase, every honest vote, live lock and confirmation extends every line source of an earlier
slot `μ` (an ancestor of, or equal to, a block of a member's confirmation of slot `μ` that is: fast
at the height `H₂ + 1` when `μ = r * R`; fast or passing the slow test when `μ ≥ r * R + 1`; any
block when `μ ≥ r * R + k`); two confirmations of one slot are compatible (Lemma 32). The line
source's base is where the old locks are read: a lock live at the vote time of slot `σ + 1` is of a
slot at least `σ + 1 − k` (Lemma 41), so at least `r * R + 1`, and a lock block of such a slot is
itself a line source, which the confirmation of slot `σ` extends.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `A'`: the
  update's answer;
- `s`: the last slot of the range.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

Read aloud: once every lock made before the fast block's round has expired, the honest chain does
not switch again.

 -/
theorem confirmations_chain_after_old_locks (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x tAwakeEnd)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1) :
    ∀ s : ℕ, supportCutoff S (s + 2) ≤ tAwakeEnd →
      ConfirmationsChainOn S Sched x (roundMembers S Sched) (r * S.C.R + S.C.k) s :=
  GoldilocksCorrectness.Proofs.Executions.confirmations_chain_after_old_locks S Sched x GST tGAT
    tAwakeEnd r H₂ v L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hAnchor hOld hv hUpdate hFast hL

/-- **A7c, the frame of an honest validator relative to the late family.** A5's hypotheses (the
execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks, `h(L) = H₂ + 1`);
a slot `s ≥ r * R + k`; a time `t` from the vote time of slot `s + 1` to the support cutoff of slot
`s + 2`, inside the phase; and `w` honest at `t` — then for every block `C` of
`FastFamilyFrom S Sched x (r * R + k) L (s + 1)` (`L`'s ancestors and the members' confirmations of
the slots `r * R + k` to `s`, with their ancestors): the root of `w`'s fork choice before `t` is
compatible with `C`; when that root is `C` or an ancestor of `C`, some viable head of `w`'s frame is
`C` or a descendant of `C`; and `w`'s finalized block before `t` is compatible with `C`.

The skeleton's hypotheses `hInvL` (the slot invariant relative to `L` up to slot `s`) and `hChainF`
(A8c's conclusion up to slot `s`) are not hypotheses: the proof does not read them.

Why: every block of the family is a line source of a slot at most `s` (`family_source`), and A7a's
argument holds at every line source (`frame_source_at`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `A'`: the
  update's answer;
- `s`: the slot; `t`: the reading time; `w`: the reader.

Roots name blocks until `supportCutoff S (s + 2)`: the bundle `PartAHyps` is built with its end
time `supportCutoff S (s + 2)`, the latest time its kit reads here.

Read aloud: once the old locks have expired, every honest validator's finality gadget lets it follow
every block the honest chain has confirmed since.

 -/
theorem frame_at_time_relative_to_late_family (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s t : ℕ) (v w : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t' : ℕ, tGAT ≤ t' → t' ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t' : Int) → u ∈ Sched.awake (t' : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hs : r * S.C.R + S.C.k ≤ s) (hts : voteTime S (s + 1) ≤ t)
    (ht : t ≤ supportCutoff S (s + 2)) (hEnd : supportCutoff S (s + 2) ≤ tAwakeEnd)
    (hw : w ∉ Sched.adv (t : Int)) :
    ∀ C : Block V, FastFamilyFrom S Sched x (r * S.C.R + S.C.k) L (s + 1) C →
      (fg_to_ac (stateBefore x t w).S).fc_root.compatible C = true ∧
      ((fg_to_ac (stateBefore x t w).S).fc_root.AncestorEq C →
        ∃ W ∈ (fg_to_ac (stateBefore x t w).S).tree,
          W ∈ (fg_to_ac (stateBefore x t w).S).viable_heads ∧ C.AncestorEq W) ∧
      (stateBefore x t w).S.F.compatible C = true :=
  GoldilocksCorrectness.Proofs.Executions.frame_at_time_relative_to_late_family S Sched x GST tGAT
    tAwakeEnd r H₂ s t v w L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird
    hAwake hCommittees hAnchor hOld hv hUpdate hFast hL hs hts ht hEnd hw

/-- **A7d, the chain step's frame conditions relative to the late family.** A5's hypotheses (the
execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks, `h(L) = H₂ + 1`);
a slot `s ≥ r * R + k` whose support cutoff of slot `s + 2` is at most `tAwakeEnd` — then every
member `w` of `Hon S Sched (s + 1)` satisfies `StepFrameAt S Sched x C s w` for every block `C` of
`FastFamilyFrom S Sched x (r * R + k) L (s + 1)`.

The skeleton's hypotheses `hInvL` and `hChainF` are not hypotheses: the proof does not read them.

Why: every block of the family is a line source of a slot at most `s` (`family_source`), and A7b's
argument holds at every line source (`stepFrame_source`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `A'`: the
  update's answer;
- `s`: the slot of the step.

Roots name blocks until `supportCutoff S (s + 2)`: the bundle `PartAHyps` is built with its end
time `supportCutoff S (s + 2)`, the latest time its kit reads here.

Read aloud: every member's vote and update of the next slot can follow every block the honest chain
has confirmed since the old locks expired.

 -/
theorem stepFrame_relative_to_late_family (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t' : ℕ, tGAT ≤ t' → t' ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t' : Int) → u ∈ Sched.awake (t' : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hs : r * S.C.R + S.C.k ≤ s) (hEnd : supportCutoff S (s + 2) ≤ tAwakeEnd) :
    ∀ w ∈ Hon S Sched (s + 1), ∀ C : Block V,
      FastFamilyFrom S Sched x (r * S.C.R + S.C.k) L (s + 1) C → StepFrameAt S Sched x C s w :=
  GoldilocksCorrectness.Proofs.Executions.stepFrame_relative_to_late_family S Sched x GST tGAT
    tAwakeEnd r H₂ s v L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird
    hAwake hCommittees hAnchor hOld hv hUpdate hFast hL hs hEnd

/-- **A8b, the chain and lock invariants for the late family.** A5's hypotheses (the execution
assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s update of slot
`r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks, `h(L) = H₂ + 1`) — then at every
slot `s ≥ r * R + 2k − 1` whose support cutoff of slot `s + 2` is at most `tAwakeEnd`,
`ChainInvFor S Sched x (Hon S Sched s) (FastFamilyFrom S Sched x (r * R + k) L s) s`, and every
member of `Hon S Sched s` satisfies `LiveLocksOnFamilyAt` for that family at `s`.

Why: every block of the family is a line source of a slot before `s` (`family_source`), and the line
invariant of `Proofs/Executions/Lemma89FastFamily.lean` (`PartAHyps.lineInv_all`): at every slot of
the phase, every honest vote, live lock and confirmation extends every line source of an earlier
slot `μ` (an ancestor of, or equal to, a block of a member's confirmation of slot `μ` that is: fast
at the height `H₂ + 1` when `μ = r * R`; fast or passing the slow test when `μ ≥ r * R + 1`; any
block when `μ ≥ r * R + k`); every lock a member holds live at the vote time of slot `s + 1` is of a
slot at least `s + 1 − k ≥ r * R + k` (Lemma 41), on its holder's confirmation of that slot (Lemma
39), a block of the family (`late_locks_on_family`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `A'`: the
  update's answer;
- `s`: the slot.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

Read aloud: once every lock older than the fast block's round has expired and every live lock is of
a slot after the last switch, the honest chain is one line, every honest vote, live lock and
confirmation on it.

 -/
theorem fast_line_invariant_late_family (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x tAwakeEnd)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1) :
    ∀ s : ℕ, r * S.C.R + 2 * S.C.k - 1 ≤ s → supportCutoff S (s + 2) ≤ tAwakeEnd →
      ChainInvFor S Sched x (Hon S Sched s)
        (FastFamilyFrom S Sched x (r * S.C.R + S.C.k) L s) s ∧
      ∀ u ∈ Hon S Sched s,
        LiveLocksOnFamilyAt S Sched x (FastFamilyFrom S Sched x (r * S.C.R + S.C.k) L s) s u :=
  GoldilocksCorrectness.Proofs.Executions.fast_line_invariant_late_family S Sched x GST tGAT
    tAwakeEnd r H₂ v L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hAnchor hOld hv hUpdate hFast hL

/-- **Part A, one line from the first honest fast block at the height after the old evidence.** A5's
hypotheses (the execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at
`a_r`, `v`'s update of slot `r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks,
`h(L) = H₂ + 1`); then: (1) at every slot `s ≥ r * R + 1` of the phase, every honest vote, live lock
and confirmation of the members of slot `s` extends `L` (A8a); (2) at every slot
`s ≥ r * R + 2k − 1` of the phase, the chain and lock invariants hold for the family of `L`'s
ancestors and the members' confirmations from slot `r * R + k` on (A8b); (3) every progress
certificate at a height greater than `H₂` on the chain of a block an honest validator holds at a
step of the phase names an entry of the honest chain from slot `r * R` (A6).

Why: A8a, A8b and A6.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `A'`: the
  update's answer.

Roots name blocks until `tAwakeEnd`: the bound of A8a and A8b, whose conclusions hold at every
slot whose support cutoff of the slot after next is at most `tAwakeEnd`.

Read aloud: once one honest validator has fast-confirmed a block one height after everything the
honest validators had attested, no honest validator ever votes, locks or confirms off that block's
chain, the honest chain is one line once the older locks have expired, and every later certificate
is on its line.

 -/
theorem lem89L_one_line_from_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x tAwakeEnd)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hL : (chainStateOf S.C L).h = H₂ + 1) :
    (∀ s : ℕ, r * S.C.R + 1 ≤ s → supportCutoff S (s + 2) ≤ tAwakeEnd →
      HonestChainExtends S Sched x (Hon S Sched s) L s) ∧
    (∀ s : ℕ, r * S.C.R + 2 * S.C.k - 1 ≤ s → supportCutoff S (s + 2) ≤ tAwakeEnd →
      ChainInvFor S Sched x (Hon S Sched s)
        (FastFamilyFrom S Sched x (r * S.C.R + S.C.k) L s) s ∧
      ∀ u ∈ Hon S Sched s,
        LiveLocksOnFamilyAt S Sched x (FastFamilyFrom S Sched x (r * S.C.R + S.C.k) L s) s u) ∧
    (∀ (j : ℕ) (w : V) (B T : Block V) (h : Height), x[j].time ≤ tAwakeEnd →
      B ∈ (x[j][w].st).S.T → ProgressCertOn B h T → H₂ < h →
      ∃ E : Block V, OnHonestChain S Sched x (r * S.C.R) E ∧ IsEntry S.C E ∧
        (chainStateOf S.C E).h = h ∧ T.root = E.root) :=
  GoldilocksCorrectness.Proofs.Executions.lem89L_one_line_from_fast_block S Sched x GST tGAT
    tAwakeEnd r H₂ v L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hAnchor hOld hv hUpdate hFast hL

/-! ## Part B on the recount: the windows -/

omit [RootOrder] in
/-- **Every opening's window starts at or after the committee premise's anchor.** With the sequence
premise `hSeq` (its first opening's slot starting at least `3k + 1` slots after `tGAT`) and a slot
`s` at or after the first opening's, `2k ≤ s` and `anchorCW S tGAT ≤ slotStart S (s − 2k + 1)`.

Why: `4Δ · s ≥ 4Δ · s_0 ≥ tGAT + 4Δ(3k + 1)`, and `4Δ(3k + 1) = 4Δ(k + 2) + 4Δ(2k − 1)`.

The variables:
- `S`, `Sched`: the setup, the schedule; `rs`: the rounds of the honest round opening slots; `m`: the index of the last
  honest round opening slot; `tGAT`, `tAwakeEnd`: the phase; `s`: the slot.

Read aloud: the front of `3k + 1` slots leaves `2k − 1` slots of window after the anchor's `k + 2`;
the first opening's span of the count is not needed.

Copied from `scratch/goldilocks_healed/probe_fewer_1.lean:81`. -/
theorem window_after_anchor (S : Setup V) (Sched : Schedule V) (rs : ℕ → ℕ)
    (m tGAT tAwakeEnd s : ℕ)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hs : rs 0 * S.C.R ≤ s) :
    2 * S.C.k ≤ s ∧ anchorCW S tGAT ≤ slotStart S (s - 2 * S.C.k + 1) :=
  GoldilocksCorrectness.Proofs.Executions.window_after_anchor S Sched rs m tGAT tAwakeEnd s hSeq hs

/-! ## Part B: B5 and B6 -/

/-- **B5 with no fork-choice change in the window: the window's last slot has a confirmation.**
Under the execution assumptions and unforgeability, with every honest validator awake in the phase
`[tGAT, tAwakeEnd]` and fewer than a third of the validators in the adversary set up to its end,
and committee sleepiness from `anchorCW S tGAT`: when the window of the opening at slot `s`
(`k + 1 ≤ s`) starts at or after `anchorCW S tGAT` (`anchorCW S tGAT ≤ slotStart S (s − k)`), the
support cutoff of slot `s` is at most `aR S r ≤ tAwakeEnd`, and no validator outside the adversary
set has a `ForkChoiceChangeAt` at a time from the vote time of slot `s − k − 1` to before the vote time of slot `s` — then some member
of `Hon S Sched (s − 2)` saved a confirmation of slot `s − 2`.

 Proved in
`Proofs/Executions/Lemma89StabilityJ.lean`.

B5 as the skeleton states it (`scratch/goldilocks_healed/skeleton_89b/SkeletonPartB.lean`,
`window_last_confirmation_exists`) is false: the honest votes of slot `s − 2` split between `J₁`'s
chain and a chain conflicting with it, and the members' finalized block moving to `J₁` between those
votes and the update of slot `s − 2` (a block justifying the next height and finalizing `J₁`,
released right after the votes), make every member save nothing; The move is a fork-choice change in the window, which
this form excludes. The skeleton's hypotheses
`hT₁`, `hH₂`, `hOld`, `hwin` and `hFrame` are not read by the proof and are left out, with the
parameters `T₁` and `H₂` they alone named.

Why: write `σ := s − 2`. Committee sleepiness at slot `σ + 1` makes the honest members of the
committee of slot `σ` more than half of it, all honest active at slot `σ`; take one, `v`, as the
updater. Every honest vote of slot `σ` extends `v`'s finalized block before the support cutoff of
slot `σ + 1` (`vote_extends_finalized_of_no_change`: the vote extends its voter's root, and with no
fork-choice change at the voter and at `v` from two delays into slot `σ − 1` on, either the root is
at or above `v`'s finalized block, or every viable head of the voter is higher than the height `v`'s
finalized block was finalized at; each other case is a fork-choice change, or a delivery against
the voter's caches). So every honest committee vote supports `v`'s finalized block, and the update
saves a confirmation (`confirmation_saved_of_votes`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `r`: the round of the action time the
  window ends before; `s`: the honest round opening slot.

Roots name blocks until `supportCutoff S (s - 1)`: `vote_extends_finalized_of_no_change` at slot
`s − 2`, and `confirmation_saved_of_votes` at slot `s − 2`.

Read aloud: when no honest validator's fork choice changes during the window, an honest member
confirms something at the window's second-to-last slot.

 -/
theorem window_last_confirmation_exists_of_no_change (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r s : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s - 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hEnd : aR S r ≤ tAwakeEnd)
    -- the window: `k + 1` slots before `s`, before `a_r`, inside the committee premise
    (hk : S.C.k + 1 ≤ s)
    (hBefore : supportCutoff S s ≤ aR S r)
    (hAnchor : anchorCW S tGAT ≤ slotStart S (s - S.C.k))
    -- no validator outside the adversary set has a fork-choice change in the window
    (hNoChange : ∀ (w : V) (t' : ℕ), voteTime S (s - S.C.k - 1) ≤ t' → t' < voteTime S s →
      w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t') :
    ∃ v ∈ Hon S Sched (s - 2), ∃ D : Block V,
      (stateBefore x (supportCutoff S (s - 1) + 1) v).A.saved_confirmation (s - 2) = some D :=
  GoldilocksCorrectness.Proofs.Executions.window_last_confirmation_exists_of_no_change S Sched x
    GST tGAT tAwakeEnd r s hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird
    hAwake hCommittees hEnd hk hBefore hAnchor hNoChange

/-- **B6, the stability fact: a window that is not stable shows a fork-choice change.** Under the
execution assumptions and unforgeability, with every honest validator awake in the phase
`[tGAT, tAwakeEnd]` and fewer than a third of the validators in the adversary set up to its end,
and committee sleepiness from `anchorCW S tGAT`: when the window of the opening at slot `s`
(`k + 1 ≤ s`) starts at or after `anchorCW S tGAT` (`anchorCW S tGAT ≤ slotStart S (s − k)`), the
support cutoff of slot `s` is at most `aR S r ≤ tAwakeEnd`, and `FrontWindowStable` fails for the
member sets `Hon S Sched` from slot `s − 2k` to slot `s − 1` — then some validator `w`, outside the
adversary set at a time `t'` from the vote time of slot `s − k − 1` to before the support cutoff of slot `s`, has a
`ForkChoiceChangeAt` at `t'`.

 Proved in
`Proofs/Executions/Lemma89StabilityJ.lean`.

 Changed from the
skeleton (`scratch/goldilocks_healed/skeleton_89b/SkeletonPartB.lean`, `stability_fact3`): the
hypothesis `hSaved` (some member saved a confirmation of slot `s − 2`) is gone, its content derived
in the proof (`B6Ctx.member_saves`, B5's argument); the interval starts at the vote time of slot
`s − k − 1`. The skeleton's hypotheses
`hT₁`, `hH₂`, `hOld`, `hwin` and `hChain` are not read by the proof and are left out, with the
parameters `T₁` and `H₂` they alone named.

Why, by contradiction, with no such change: a confirmation `X` of a window slot `σ` has an honest
committee supporter `u` (its eligibility count against the committee majority), whose vote is for
`X` or a descendant of `X`, itself `W` or an ancestor of a viable block `W` of `u` at the vote time.
`W` stays viable at `u` for two delays, reaches every honest `w` by the support cutoff of slot `σ`,
and from then on, with no change at `w`, `w`'s `head_height_floor` is at most `W`'s height and its
finalized block and root are compatible with `W` (`frame_compatible_of_viable`): clause 1. For
clause 2, every honest
vote of slot `s − 2` extends a member's root before the vote time of slot `s`
(`B6Ctx.vote_extends_root`), so the member's own confirmation of slot `s − 2` is that root or a
descendant of it (Lemma 78).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `r`: the round of the action time the
  window ends before; `s`: the honest round opening slot.

Roots name blocks until `supportCutoff S s`: every block the proof compares is held before the
support cutoff of slot `s`, the window's end (the bundle `B6Ctx` carries the premise at that
time).

Read aloud: before the fast block's round, a window breaks only when some honest validator's root
moves to its justified block, other than an ancestor of its old root, or its `head_height_floor`
rises, at a time from the vote time of the window's second slot to before the support cutoff of
slot `s`.

 -/
theorem stability_fact3 (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r s : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hEnd : aR S r ≤ tAwakeEnd)
    -- the window: `k + 1` slots before `s`, before `a_r`, inside the committee premise
    (hk : S.C.k + 1 ≤ s)
    (hBefore : supportCutoff S s ≤ aR S r)
    (hAnchor : anchorCW S tGAT ≤ slotStart S (s - S.C.k))
    -- the window is not stable
    (hFail : ¬ FrontWindowStable S Sched x (Hon S Sched) (s - 2 * S.C.k) (s - 1)) :
    ∃ (w : V) (t' : ℕ), voteTime S (s - S.C.k - 1) ≤ t' ∧ t' < supportCutoff S s ∧
      w ∉ Sched.adv (t' : Int) ∧ ForkChoiceChangeAt S Sched x w t' :=
  GoldilocksCorrectness.Proofs.Executions.stability_fact3 S Sched x GST tGAT tAwakeEnd r s hDiv
    hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake hCommittees hEnd hk
    hBefore hAnchor hFail

/-! ## Part B: the climb's count -/

/-- **The four kinds of fork-choice change.** Under the execution assumptions and unforgeability,
with every honest validator awake in the phase `[tGAT, tAwakeEnd]`, fewer than a third of the
validators in the adversary set up to its end, `GST ≤ tGAT ≤ T₁`, the threshold `H₂` the greatest
height of an honest attestation sent before `T₁` (`OldHeightAttained`), every honest attestation
sent before `aR S r ≤ tAwakeEnd` of height at most `H₂`: there are four times `τ 0, …, τ 3` such that
every `ForkChoiceChangeAt` of a validator outside the adversary set at a time `t` from `T₁ + Δ` to
before `aR S r` is at a time from `τ c` to `τ c + Δ` for one of them.

The four kinds, each the first crossing of a level of the FG state: the cache `h_j` reaching
`H₂ − 1` (the root moving to the justified block `J₁` at `H₂ − 1`); `head_height_floor` reaching
`H₂`; `h_j` reaching `H₂` (the root moving to `J₂`); `head_height_floor` reaching `H₂ + 1`. No
fifth kind exists: a finality move is no fork-choice change.

 the hypotheses `hOwner` and `hCommittees` are not read by
the proof and are left out.

Why: a fork-choice change at `w` at `t` makes one of the four levels fail before `t` and hold before
`t + 1` (with `h_max` at `H₂` or `H₂ + 1`, B2 and A2; a root moving to `J` with `h_max = h_j + 1`
needs `h_j` to rise, Lemma 76 and Lemma 89a). Each level, once some validator honest at a time
`τ ≥ T₁` has it, reaches every honest validator by `τ + 1 + Δ`: the block witnessing the cache, or
the contesting block and the justified block's witness, are delivered within one delay. And each
level, once reached, stays reached up to `aR S r` (`h_j` does not decrease; a contested state stays
contested while its `h_max` stays). So the crossings of a level lie within one delay after the
first time from `T₁` some honest validator has it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `T₁`: the time of the threshold; `r`: the
  round of the action time the climb ends at; `H₂`: the threshold.

Roots name blocks until `aR S r`: every change the conclusion classifies is at a time before
`aR S r`, and the levels are read before times at most `aR S r` (the bundle `ClimbCtx`).

Read aloud: before the fast block's round, the members' roots and `head_height_floor`s change in
at most four bursts, each within one delay.

 -/
theorem fork_choice_change_kinds (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd) :
    ∃ τ : Fin 4 → ℕ, ∀ (w : V) (t : ℕ), T₁ + Δ S ≤ t → t < aR S r →
      w ∉ Sched.adv (t : Int) → ForkChoiceChangeAt S Sched x w t →
      ∃ c : Fin 4, τ c ≤ t ∧ t ≤ τ c + Δ S :=
  GoldilocksCorrectness.Proofs.Executions.fork_choice_change_kinds S Sched x GST tGAT tAwakeEnd
    T₁ r H₂ hDiv hMono hSync hCatch hRoots hParent hU hGST hT₁ hThird hAwake hH₂ hOld hEnd

/-- **B10 restated, on a copy: a spoiled opening has a fork-choice change near it, with
its time.** Under the execution assumptions and unforgeability, with every honest validator awake in
the phase `[tGAT, tAwakeEnd]`, fewer than a third of the validators in the adversary set up to its
end, committee sleepiness from `anchorCW S tGAT`, the honest round opening slots of the rounds `rs 0 < … < rs m`
(`HonestOpeningSeq`), `aR S r ≤ tAwakeEnd`, an opening `i < m` whose next opening's first slot is
at most `r * R`, and no opening's proposal colliding with a block its proposer held: when opening
`i` is spoiled (`Spoiled`), some validator `w` outside the adversary set at a time `t'` from the
vote time of slot `rs i * R − k − 1` to before the support cutoff of slot `rs (i + 1) * R` has a
`ForkChoiceChangeAt` at `t'`.

 The count of the climb is
  unchanged: a change of a kind starting at `t_K` with `t_K ≤ t'` before that support cutoff has
  its slot at most `rs (i + 1) * R`;
- the hypothesis `hNoCol` (no opening's proposal collides with a block its proposer held): in a
  collision, the proposal may be held by no honest validator, and the round fails its third
  clause with no fork-choice change; the climb concludes the collision as a disjunct
 and supplies `hNoCol` after splitting on it, as for `quiet_rising_heights_differ`;
- `ForkChoiceChangeAt` with the conjunct `h_max = h_j + 1`;
- the probe's hypotheses `T₁`, `H₂`, `hT₁`, `hH₂`, `hOld` and `hT₁0` are not read by the proof and
  are left out.

Why: by contradiction, with no such change. The window before the opening is stable (B6), so every
member's root before the vote time of the opening's first slot is on the chain of a member's live
lock or confirmation of the slot before, which every honest committee vote of that slot extends, as
it extends the proposer's anchor (the front's chain step; `vote_extends_root`); those blocks have a
viable head of the proposer's frame on their chain (B6's `frame`), so they are ancestors of the
proposal's parent (`family_ancestorEq_proposal_parent`), itself a viable head of the proposer: the
first clause. With no change, a member's root stays an ancestor of the proposal's parent with its
`head_height_floor` at most the parent's height (`root_below_kept`): the second and third clauses;
a member's root stays compatible with a block on each member confirmation's chain that it holds
(`frame_compat_kept`): the fourth; the next proposer's root is an ancestor of its own confirmation
of slot `rs (i + 1) * R − 2`, which has a viable head of its frame on its chain: the fifth.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `r`: the round of the action time the
  climb ends at; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `supportCutoff S (rs (i + 1) * S.C.R)`: the end of the range the context
`QuietCtx` reads, the support cutoff of the next honest round opening slot's first slot.

Read aloud: a spoiled honest round opening slot before the fast block's round has a member's
fork-choice change in its window or in its round, up to the support cutoff of the next opening's
first slot.

 -/
theorem spoiled_near_fork_choice_change_cutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r m i : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (rs (i + 1) * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hir : rs (i + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hSp : Spoiled S Sched x rs i) :
    ∃ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' ∧
      t' < supportCutoff S (rs (i + 1) * S.C.R) ∧ w ∉ Sched.adv (t' : Int) ∧
      ForkChoiceChangeAt S Sched x w t' :=
  GoldilocksCorrectness.Proofs.Executions.spoiled_near_fork_choice_change_cutoff S Sched x GST tGAT
    tAwakeEnd r m i rs hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hEnd hSeq hi hir hNoCol hSp

/-- **B11 restated, on a copy: a quiet opening above the threshold attests above it.** Under the
execution assumptions and unforgeability, with every honest validator awake in the phase
`[tGAT, tAwakeEnd]`, fewer than a third of the validators in the adversary set up to its end,
committee sleepiness from `anchorCW S tGAT`, the honest round opening slots of the rounds `rs 0 < … < rs m`, `aR S r ≤
tAwakeEnd`, an honest round opening slot `i < m`, a slot `s''` at least one round after its
first slot and at most `r * R`, no proposal of an honest round opening slot colliding with a block
its proposer held, and no validator outside the adversary set with a `ForkChoiceChangeAt` from the
vote time of slot `rs i * R − k − 1` to before the support cutoff of slot `s''`: when the
proposal `B` of slot `rs i * R` has chain-state height greater than `H₂`, some validator honest
and awake at a tick time `t₀ ≤ aR S (rs i)` put on the wire then an attestation of height greater
than `H₂`. The climb's count takes `s'' := rs (i + 1) * R`; the honest round opening slot whose
round holds `r * R` takes `s'' := r * R`; the form with
`s'' := rs (i + 1) * R` is the instance.

 the skeleton's `hSyncF` and `hCatchF` are not read and
are left out. The climb applies it to the openings with no fork-choice change in that range, which
it counts with the same budget.

Why: the round's base (`round_base_steps`, through the window's family) makes every member's update
at the action time save `B` with `B` among its fast blocks and its live locks on `B`'s chain; a
member then attests at `B`'s height at its tick (Lemma 55, Lemma 61), or its record already sent an
attestation at that height at an earlier tick.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `r`: the round of the action time the
  climb ends at; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `H₂`: the threshold; `s''`: the
  end of the range read; `rs`: the rounds of the honest round opening slots; `B`: the proposal at the honest round opening slot.

Roots name blocks until `supportCutoff S s''`: the end of the range the context `QuietCtx` carries
(`quietCtx_of`).

Read aloud: an honest round opening slot with no fork-choice change in its window and in its round up
to slot `s''`, whose proposal is above the threshold, produces an honest attestation above the
threshold by its action time.

 -/
theorem quiet_top_gives_attestation_cutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r m i H₂ s'' : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s''))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hsR : rs i * S.C.R + S.C.R ≤ s'') (hir : s'' ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S s'' → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) (hBh : H₂ < (chainStateOf S.C B).h) :
    ∃ (t₀ : ℕ) (v : V) (a : Attestation V), t₀ ≤ aR S (rs i) ∧
      HonestAttestationAt S Sched x t₀ v a ∧ H₂ < a.h :=
  GoldilocksCorrectness.Proofs.Executions.quiet_top_gives_attestation_cutoff S Sched x GST tGAT
    tAwakeEnd r m i H₂ s'' rs B hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird
    hAwake hCommittees hEnd hSeq hi hsR hir hNoCol hNo hB hBh

/-- **C1, the round base at an opening after the fast block (a copy of the skeleton's
`round_base_after_fast_block` with `S.C.R ∣ s`).** A5's hypotheses (the execution assumptions,
unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s update of slot
`r * R + 1` at `a_r` answering `A'` with `L` among its fast blocks, `h(L) = H₂ + 1`); a slot `s`
that is a round's first slot (`hsR`), at least `k + 2` slots after `r * R`, with
`supportCutoff S (s + 2) ≤ tAwakeEnd`, whose proposer is honest at the support cutoff of slot `s`,
and `B` its proposal — then `RoundBaseAt S Sched x B s`.

The copy's change, against the skeleton (`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:99`):
the hypothesis `hsR : S.C.R ∣ s` is added. Without it the second clause (each member's root at the
support cutoff of slot `s + 1` is `B` or an ancestor of `B`) reads a justification the attestations
of the round whose first slot is `s − 1` can make before that cutoff, the entry of a block made
fast by slot `s − 1`'s update, which no landed lemma places on `B`'s chain. Every caller reads C1 at
an opening, the first slot `rs j * R` of a round. The skeleton's hypotheses `hLv`, `hInvL` and
`hInvF` are deleted: the proof reads part A's line invariant directly.

Why: the proposal's parent extends every line source of a slot at least two slots before `s`
(`parent_extends_sources`); every member's root before the vote time of slot `s`, and before the
support cutoff of slot `s + 1`, is such a source (the line source of the entry its certificate
names, a round's first slot); every member's `head_height_floor` is at most `h(L)` or the height of
such a source (the entry at `h_max − 1`, the state not being contested); every live lock is on a
member's confirmation of a slot from `r * R + k` on, a line source.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the fast block's round; `H₂`: the
  bound on the old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast
  block; `A'`: the update's answer;
- `s`: the honest round opening slot; `B`: its proposal.

Roots name blocks until `supportCutoff S (s + 2)`: the bundle `PartAHyps` is built with its end
time `supportCutoff S (s + 2)`, the latest time its kit reads here.

Read aloud: after the fast block's round every honest round opening slot finds the members' frames on its
parent's chain and no lock against it.

 -/
theorem round_base_after_fast_block_opening (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L B : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 2)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s)
    (hEnd : supportCutoff S (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hB : ProposalAt S Sched x s B) :
    RoundBaseAt S Sched x B s :=
  GoldilocksCorrectness.Proofs.Executions.round_base_after_fast_block_opening S Sched x GST tGAT
    tAwakeEnd r H₂ s v L B A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird
    hAwake hCommittees hAnchor hOld hv hL hUpdate hFast hs hsR hEnd hp hB

/-- **C3, Lemma 89's base facts at the healed round (a copy of the skeleton's `healed_round_base`
with the previous slot's votes and no root collision).** Under the execution assumptions and
unforgeability, with the phase's premises: when the round base holds at slot `s` for the proposal
`B` of the honest proposer `p` of slot `s` (honest at `supportCutoff S s`), `s ≥ 1`, slot `s + 1`
starts at or after `anchorCW S tGAT`, slot `s` starts at or after `anchorCW S tGAT` (`hA`),
`supportCutoff S (s + 2) ≤ tAwakeEnd`, no block `p` held before the start of slot `s` has
`B`'s root (`hNoCol`), and every slot-`(s − 1)` vote of a committee member of
`Hon S Sched (s − 1)` is for a block it held that is a descendant of, or equal to, `p`'s anchor at
the start of slot `s` (`hPrev`): then `HonestChainExtends S Sched x (honestActiveAt S Sched s) B s`;
every updater of slot `s` saved `B` as its confirmation of slot `s`; `B.slot = s`; and `B.parent`
is in the viable tree of `p`'s frame before the start of slot `s`.

The copy's change, against the skeleton (`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:211`):
the hypotheses `hNoCol` and `hPrev` are added. When `p` holds a block other than `B` with `B`'s
root, no honest validator holds `B` (roots name one block among what honest validators hold), and
no updater saves `B`. Without `hPrev`, nothing in the statement speaks of slot `s − 1`'s votes, which
decide the members' walks of slot `s` (Lemma 59 reads them). Both are supplied at an opening after
the fast block: `hPrev` by the line invariant (the anchor is a line source, `anchor_source`), and
`hNoCol` by the case split on `RootCollisionAtOpening` that Lemma 89's conclusion already carries.

Why: `round_base_steps` with the members `Hon S Sched s`, the previous slot's voters with the block
`p`'s anchor, `p`'s viable head on its anchor's chain (`anchor_has_viable_head`), the `head_height_floor` values (the least chain-state height a viable block may have) ordered
by delivery (`floor_le_of_delivery_unordered`), the round base's three clauses, the slot's only
block (`only_block_of_unforgeability`) and `hNoCol`; the honest active validators and the updaters
are members; the parent is in the viable tree or is the anchor, itself in the viable tree or the
root (`get_anchor_root_or_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase;
- `s`: the round's first slot; `B`: its proposal.

Roots name blocks until `supportCutoff S (s + 1)`: the members' update of slot `s`
(`round_base_steps`), the latest time the proof reads.

Read aloud: at a round whose base holds, whose proposal's root is fresh and whose previous slot's
honest votes extend the proposer's anchor, every honest vote is for the proposal, every honest
update confirms it, and the proposal is the slot's.

 The assumption `hA`, that the anchor `anchorCW S tGAT` of the
committee premise is at or before the start of slot `s`, is that of `hAnchor` one slot earlier; it
replaces `tGAT + 4Δ · healFrontSlots S ≤ slotStart S s`, which the proof read only for this fact
. -/
theorem healed_round_base_of_prev_votes (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s : ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hs1 : 1 ≤ s) (hAnchor : anchorCW S tGAT ≤ slotStart S (s + 1))
    (hA : anchorCW S tGAT ≤ slotStart S s)
    (hEnd : supportCutoff S (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hB : ProposalAt S Sched x s B)
    (hBase : RoundBaseAt S Sched x B s)
    (hNoCol : ¬ RootCollisionAtProposal S Sched x s B)
    (hPrev : ∀ u ∈ S.P.committee (s - 1) ∩ Hon S Sched (s - 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T,
        vote = GoldfishVote.mk u (s - 1) H_u.root ∧
        (get_anchor (stateBefore x (slotStart S s) (S.P.proposer s)).A
          (fg_to_ac (stateBefore x (slotStart S s) (S.P.proposer s)).S)
          ((slotStart S s : ℕ) : Int)).AncestorEq H_u) :
    HonestChainExtends S Sched x (honestActiveAt S Sched s) B s ∧
    (∀ u ∈ updaterAt S Sched s,
      (stateBefore x (supportCutoff S (s + 1) + 1) u).A.saved_confirmation s = some B) ∧
    B.slot = s ∧
    B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) (S.P.proposer s)).S)
      (fg_to_ac (stateBefore x (slotStart S s) (S.P.proposer s)).S).tree :=
  GoldilocksCorrectness.Proofs.Executions.healed_round_base_of_prev_votes S Sched x GST tGAT
    tAwakeEnd s B hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hs1 hAnchor hA hEnd hp hB hBase hNoCol hPrev

/-- **C2, every round after the fast block is quiet relative to its own confirmations (a copy of
the skeleton's `quiet_round_after_fast_block` with `S.C.R ∣ s` and no root collision).** C1's
hypotheses (A5's, and a round's first slot `s` at least `k + 2` slots after `r * R` whose proposer is
honest at the support cutoff of slot `s`, `B` its proposal), with the next honest round opening
slot `s'' ≥ s + R`, its proposer honest at its own support cutoff, `supportCutoff S s'' ≤ tAwakeEnd`,
and no block the proposer of slot `s` held before the start of slot `s` with `B`'s root (`hNoCol`):
then `QuietRoundOnConfirmations S Sched x (Hon S Sched) B s s''`.

The copy's change, against the skeleton (`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:151`):
the hypotheses `hsR : S.C.R ∣ s` (C1's) and `hNoCol` are added. When the proposer of slot `s`
holds a block other than `B` with `B`'s root, no honest validator holds `B`, and the third clause (a viable head on `B`'s chain at every member of the next
slot) fails. The skeleton's flag (a member's confirmation of slot `s'' − 2` must exist) is closed:
every member saves a confirmation at every slot after `r * R` (`member_saves_confirmation`). The
skeleton's hypotheses `hLv`, `hInvL` and `hInvF` are deleted: the proof reads part A's line
invariant directly.

Why: the first two clauses are C1's; the members save `B` (C3, the previous slot's votes extending
the proposer's anchor by the line invariant), so `B` and every member's confirmation of a slot from
`s − 1` on are line sources, and the line invariant gives the third and fourth clauses
(`stepFrame_source`); for the fifth, the next proposer's root is a line source of a slot at most
`s'' − 2`, on the chain of a member's confirmation of slot `s'' − 2` (its own source's, or any
member's by the line invariant), and its frame has a viable head on that confirmation's chain.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the fast block's round; `H₂`: the
  bound on the old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast
  block; `A'`: the update's answer;
- `s`: the honest round opening slot; `s''`: the next honest round opening slot; `B`: the proposal at the honest round opening slot.

Roots name blocks until `supportCutoff S s''`: the bundle `PartAHyps` is built with its end time
`supportCutoff S s''`, the latest time its kit reads here; C1 and C3 read up to
`supportCutoff S (s + 2)`.

Read aloud: after the fast block, every honest round whose proposal's root is fresh is quiet, with
no window needed.

 -/
theorem quiet_round_after_fast_block_opening (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s s'' : ℕ) (v : V) (L B : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s''))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s) (hs'' : s + S.C.R ≤ s'')
    (hEnd : supportCutoff S s'' ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hq : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int))
    (hB : ProposalAt S Sched x s B)
    (hNoCol : ¬ RootCollisionAtProposal S Sched x s B) :
    QuietRoundOnConfirmations S Sched x (Hon S Sched) B s s'' :=
  GoldilocksCorrectness.Proofs.Executions.quiet_round_after_fast_block_opening S Sched x GST tGAT
    tAwakeEnd r H₂ s s'' v L B A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST
    hThird hAwake hCommittees hAnchor hOld hv hL hUpdate hFast hs hsR hs'' hEnd hp hq hB hNoCol

/-! ## Part B: two waiting openings at one height share one entry -/

/-- **An honest proposal is higher than its proposer's justification.** When `p` put the block `B`
on the wire at its tick at the start of slot `s + 1`, `B`'s chain-state height is at least one more
than `p`'s cache `h_j` then.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`, landed from
`scratch/goldilocks_healed/probe_wait_1.lean`.

Why: the parent `P` of `B` is a viable head of `p`. If `P` has height at least `h_j + 1`, so has
`B`. Otherwise `head_height_floor ≤ h_j`, which forces `h_max = h_j + 1` and no contest, so `p`'s
root is its justified block `J`, an ancestor of `P` at `P`'s height; `P`'s entry is `J`, and `p`'s
pool holds `J`'s justification certificate, which `B` includes (Lemma 53): `B` rises to `h_j + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
  `B`: the proposal; `p`: its proposer.

Read aloud: an honest proposer never proposes at the height its own justification is at. -/
theorem honest_proposal_above_h_j (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (p : V)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    (stateBefore x (slotStart S (s + 1)) p).S.h_j + 1 ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.honest_proposal_above_h_j S Sched x s B p hPropose

/-- **Reaching a justification height `h` with `head_height_floor` at most `h` is a
fork-choice change.** When `w`'s cache `h_j` is less than `h` before the time `t` and at least `h`
before `t + 1`, `w`'s `head_height_floor` before `t + 1` is at most `h`, and `w`'s justified block
before `t + 1` is not the genesis block, `w` has a `ForkChoiceChangeAt` at `t`.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`.

Why: after `t`, `h_max = h_j + 1` with no contest, so the root is the new justified block, of
height at least `h`; the old root is the old justified block or the finalized block, an ancestor of
it, of height less than `h`: the new root is not an ancestor of the old one.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `w`: the validator; `t`: the time;
  `h`: the height.

Read aloud: a validator whose justification reaches the height of its least viable height moves its
root to the new justified block, which is a fork-choice change. -/
theorem change_of_h_j_reaches (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (w : V) (t h : ℕ)
    (hlo : (stateBefore x t w).S.h_j < h) (hhi : h ≤ (stateBefore x (t + 1) w).S.h_j)
    (hfl : head_height_floor (stateBefore x (t + 1) w).S ≤ h)
    (hJg : (stateBefore x (t + 1) w).S.J ≠ Block.genesis) :
    ForkChoiceChangeAt S Sched x w t :=
  GoldilocksCorrectness.Proofs.Executions.change_of_h_j_reaches S Sched x w t h hlo hhi hfl hJg

/-- **No honest validator reaches the height of a later honest proposal's justification one delay
before it.** Under the execution assumptions and unforgeability, with fewer than a third of the
validators in the adversary set up to `tEnd`: when `p` puts the block `B` on the wire at its tick at
the start of slot `s + 1` (at most `tEnd`), awake and honest from `t` to that start, and `u` is
honest at the time `t` from `GST` with `t + Δ` at most that start, `u`'s cache `h_j` before `t` is
less than `B`'s chain-state height.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`.

Why: the block witnessing `u`'s `h_j` reaches `p` within one delay (`held_spread_h_j`), `p`'s `h_j`
does not decrease up to the slot's start (`h_j_mono`), and `B` is higher than `p`'s `h_j`
(`honest_proposal_above_h_j`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tEnd`: the end of the adversary bound; `t`: the time; `s`: the slot before the
  proposal's; `u`: the honest validator; `p`: the proposer; `B`: the proposal.

Roots name blocks until `slotStart S (s + 1)`: the proposer's `h_j` is read before the start of
slot `s + 1` (`h_j_mono`), after `u`'s justification spreads to it by `t + Δ`.

Read aloud: one delay before an honest proposal, every honest justification is lower than it. -/
theorem h_j_lt_of_later_proposal (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tEnd t s : ℕ) (u p : V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hGST : GST ≤ t) (hle : t + Δ S ≤ slotStart S (s + 1)) (hEnd : slotStart S (s + 1) ≤ tEnd)
    (hu : u ∉ Sched.adv ((x[stepBefore x t].time : ℕ) : Int))
    (hp : ∀ t' : ℕ, t ≤ t' → t' ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t' : Int) ∧ p ∉ Sched.adv (t' : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    (stateBefore x t u).S.h_j < (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.h_j_lt_of_later_proposal S Sched x GST tEnd t s u p B
    hDiv hMono hSync hCatch hRoots hParent hU hThird hGST hle hEnd hu hp hPropose

omit [RootOrder] in
/-- **A chain state whose justification height is at most `1` has the genesis block as its
justified block.** For every block `D`, when `(chainStateOf C D).h_j ≤ 1`,
`(chainStateOf C D).J` is the genesis block.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`.

Why: at `0` by `chainStateOf_J_spec`; at `1` the justified block is an entry of height `1`, and the
genesis block, an ancestor of it at the same height, is its own entry.

The variables:
- `C`: the configuration; `D`: the block.

Read aloud: nothing but the genesis block is justified at height at most one. -/
theorem J_genesis_of_h_j_le_one (C : Config) (D : Block V) (h1 : (chainStateOf C D).h_j ≤ 1) :
    (chainStateOf C D).J = Block.genesis :=
  GoldilocksCorrectness.Proofs.Executions.J_genesis_of_h_j_le_one C D h1

/-- **Before the later opening's support cutoff, no honest validator holds a justification at the
waited height `h`, other than the genesis block.** Under the execution assumptions and
unforgeability, with fewer than a third of the validators in the adversary set up to `tEnd`: let
`t₀ + Δ` be the start of slot `s + 1` (at most `tEnd`), where the proposer `p`, awake and honest
from `tL` (at least `GST`, at most `t₀`) to that start, puts on the wire a block `B₂` of chain-state
height `h`; let every validator honest at a time from `t₀` to `tc` have `head_height_floor` at most
`h`, and no validator outside the adversary set have a `ForkChoiceChangeAt` at a time from `t₀` to
before `tc`. Then every validator `u` honest at a time `t` from `tL` to `tc` has `h_j < h` before
`t`, or the genesis block as its justified block.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`.

Why: up to `t₀`, by `h_j_lt_of_later_proposal`; after `t₀`, the first time `u`'s `h_j` reaches `h`
is a fork-choice change (`change_of_h_j_reaches`), which the hypothesis excludes.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tEnd`: the end of the adversary bound; `tL`: the time from which `p` is awake
  and honest; `t₀`: one delay before the proposal; `tc`: the cutoff; `s`: the slot before the
  proposal's; `h`: the proposal's height; `p`: the proposer; `B₂`: the proposal; `u`, `t`: the
  validator and the time read.

Roots name blocks until `slotStart S (s + 1)`: `h_j_lt_of_later_proposal` at the later opening's
slot `s + 1`, the only reading of the premise.

Read aloud: until the later opening's support cutoff, no honest validator has justified anything at
the waited height. -/
theorem h_j_lt_or_genesis_before_cutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tEnd tL t₀ tc s h : ℕ) (p : V) (B₂ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hGST : GST ≤ tL) (hL0 : tL ≤ t₀) (ht₀ : t₀ + Δ S = slotStart S (s + 1))
    (hs : slotStart S (s + 1) ≤ tEnd)
    (hp : ∀ t' : ℕ, tL ≤ t' → t' ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t' : Int) ∧ p ∉ Sched.adv (t' : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B₂⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hB₂ : (chainStateOf S.C B₂).h = h)
    (hF : ∀ (u : V) (t : ℕ), t₀ ≤ t → t ≤ tc → u ∉ Sched.adv (t : Int) →
      head_height_floor (stateBefore x t u).S ≤ h)
    (hNo : ∀ (w : V) (t' : ℕ), t₀ ≤ t' → t' < tc → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (u : V) (t : ℕ) (hGt : tL ≤ t) (htc' : t ≤ tc) (hu : u ∉ Sched.adv (t : Int)) :
    (stateBefore x t u).S.h_j < h ∨ (stateBefore x t u).S.J = Block.genesis :=
  GoldilocksCorrectness.Proofs.Executions.h_j_lt_or_genesis_before_cutoff S Sched x GST tEnd tL t₀
    tc s h p B₂ hDiv hMono hSync hCatch hRoots hParent hU hThird hGST hL0 ht₀ hs hp hPropose
    hB₂ hF hNo u t hGt htc' hu

/-! ## Part B: the climb, on the span premise of record -/

/-- **B12 restated, part 1, on a copy: two rising quiet openings are at different heights.** In
the climb's context (the threshold `H₂` attained at `T₁`, every honest attestation before `aR S r`
at most `H₂`), two openings `i < i' < m` and a slot `s''₂` with `rs i' * R + R ≤ s''₂ ≤ r * R`,
each with no fork-choice change (`ForkChoiceChangeAt`) from the vote time of slot
`rs i * R − k − 1` (resp. `rs i' * R − k − 1`) to before the support cutoff of slot
`rs (i + 1) * R` (resp. `s''₂`), the first rising, have proposals `B`, `B₂` of different
chain-state heights, when no opening's proposal collides with a block its proposer held. The later
honest round opening slot's range ends at `s''₂`: `rs (i' + 1) * R` for a rising or waiting one, `r *
R` for the one whose round holds `r * R`; the form with `s''₂ := rs (i' + 1) * R` is
the instance.

 `rs i' * R < r * R` becomes
`rs (i' + 1) * R ≤ r * R`, the end of the second opening's round; `hNoCol` is added (as for
`spoiled_near_fork_choice_change_cutoff`); the probe's `hSyncF`, `hCatchF` and the second
opening's rising hypothesis are not read and are left out.

Why: by contradiction with both heights `h`. The next proposal `B'` after `B` is higher than `h`
and at most `H₂ + 1` high, so `h` is `H₂ − 1` or `H₂`. No honest `head_height_floor` reaches
`h + 1` before the support cutoff of the later opening's first slot (it would reach a member of
the later opening and stay); so every honest validator holds `B'` one delay after its proposal,
with `h_max = h + 1`, no contest and its root on `B'`'s chain. The round's base at `B'`'s slot
makes the honest votes there extend `B'`, `lem79_step_sets` carries the chain invariant relative
to `B'` to the slot before the later opening, whose proposer's anchor is then comparable with
`B'`; so `B'` is an ancestor of `B₂`'s parent, and `B₂` is higher than `h`.

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, a weaker
hypothesis than `T₁ ≤ slotStart S (rs 0 * R − 2k)`: the climb takes `T₁` three delays into slot
`rs 0 * R − 2k`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i < i'`: the indices of the two honest round opening slots; `s''₂`: the end
  of the later one's range; `rs`: the rounds of the honest round opening slots; `B`, `B₂`: their proposals.

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Read aloud: two honest round opening slots with no fork-choice change in their windows and rounds,
the first rising, propose at different heights.

 -/
theorem quiet_rising_heights_differ_cutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i i' s''₂ : ℕ)
    (rs : ℕ → ℕ)
    (B B₂ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hsR' : rs i' * S.C.R + S.C.R ≤ s''₂)
    (hir' : s''₂ ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hNo' : ∀ (w : V) (t' : ℕ), voteTime S (rs i' * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S s''₂ → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hRise : RisingAt S Sched x rs i)
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) (hB₂ : ProposalAt S Sched x (rs i' * S.C.R) B₂) :
    (chainStateOf S.C B).h ≠ (chainStateOf S.C B₂).h :=
  GoldilocksCorrectness.Proofs.Executions.quiet_rising_heights_differ_cutoff S Sched x GST tGAT
    tAwakeEnd T₁ r H₂ m i i' s''₂ rs B B₂ hDiv hMono hSync hCatch hRoots hParent hOwner hU
    hGST hT₁ hThird hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 hii' hi' hsR' hir' hNoCol hNo hNo'
    hRise hB hB₂

/-- **The quiet honest round opening slot whose round holds `r * R` proposes at height `H₂ − 1` or
`H₂`.** In the climb's context (the execution assumptions and unforgeability, every honest
validator awake in `[tGAT, tAwakeEnd]`, fewer than a third of the validators in the adversary set
up to its end, committee sleepiness from `anchorCW S tGAT`, the threshold `H₂` attained at `T₁`
with `tGAT ≤ T₁` and `T₁ + Δ` at most the start of slot `rs 0 * R − k − 1`, every honest
attestation before `aR S r ≤ tAwakeEnd` at most `H₂`, the honest round opening slots
`rs 0 < … < rs m`, no proposal of one colliding with a block its proposer held): for an honest
round opening slot `i < m` with `rs i * R + R ≤ r * R` and no validator outside the adversary set
with a `ForkChoiceChangeAt` from the vote time of slot `rs i * R − k − 1` to before the support
cutoff of slot `r * R`, its proposal `B` has `H₂ ≤ h(B) + 1` and `h(B) ≤ H₂`.


when quiet through the support cutoff of slot `r * R`, it is one of the two heights.

Why: above `H₂`, `quiet_top_gives_attestation_cutoff` at `s'' := r * R` gives an honest
attestation above `H₂` before `aR S r`, against `hOld`; below `H₂ − 1`, an honest committee
member of slot `rs i * R` has `head_height_floor` at most `h(B)` at the support cutoff of the next
slot (the round's second clause) and `h_max` at least `H₂` there.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the last honest round opening slot's index; `i`: the honest round
  opening slot; `rs`: their rounds; `B`: its proposal.

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Read aloud: a quiet honest round opening slot before the fast block proposes at one of the two
heights the climb has not left. -/
theorem quiet_straddler_heights (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hi : i < m) (hir : rs i * S.C.R + S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (r * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) :
    H₂ ≤ (chainStateOf S.C B).h + 1 ∧ (chainStateOf S.C B).h ≤ H₂ :=
  GoldilocksCorrectness.Proofs.Executions.quiet_straddler_heights S Sched x GST tGAT tAwakeEnd T₁
    r H₂ m i rs B hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁ hThird hAwake
    hCommittees hH₂ hOld hEnd hSeq hT₁0 hi hir hNoCol hNo hB

open Classical in
/-- **B12 restated, part 2, on a copy: at most two rising quiet openings before the climb's end.**
In the climb's context, the honest round opening slots `i < m` with `rs i * R < r * R`, no
fork-choice change (`ForkChoiceChangeAt`) from the vote time of slot `rs i * R − k − 1`
to before the support cutoff of slot `min (rs (i + 1) * R) (r * R)`, and rising when
`rs (i + 1) * R ≤ r * R`, are at most two, when no opening's proposal collides with a block its
proposer held.

 `hNoCol` is added; the probe's `hSyncF` and `hCatchF` are not read and
are left out.

Why: each such opening's proposal has chain-state height `H₂ − 1` or `H₂` (for a rising one, its
next proposal is higher and at most `H₂ + 1`; for the one whose round holds `r * R`,
`quiet_straddler_heights`; an honest committee member's `head_height_floor` at the action time is
at most the proposal's height, and its `h_max` at least `H₂`), and two of them have different
heights (part 1, the earlier one rising since its next slot is at or before the later one's, the
later one's range ending at `min (rs (i' + 1) * R) (r * R)`).

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, a weaker
hypothesis than `T₁ ≤ slotStart S (rs 0 * R − 2k)`: the climb takes `T₁` three delays into slot
`rs 0 * R − 2k`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR S r`: `quiet_rising_next_proposal_late`, `quiet_straddler_heights` and
`quiet_rising_heights_differ_cutoff`, at the action time of round `r`.

Read aloud: before the climb's end, at most two honest round opening slots with no fork-choice change
in their windows and rounds climb, the one whose round holds the fast round's first slot
included.

 -/
theorem quiet_rising_before_fast_round_le_two_cutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m) :
    ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
        t' < supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) →
        w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t') ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt S Sched x rs i))).card ≤ 2 :=
  GoldilocksCorrectness.Proofs.Executions.quiet_rising_before_fast_round_le_two_cutoff S Sched x GST
    tGAT tAwakeEnd T₁ r H₂ m rs hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁
    hThird hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 hNoCol

/-- **The next proposal after a waiting quiet opening.** In the climb's context (the execution
assumptions and unforgeability, every honest validator awake in `[tGAT, tAwakeEnd]`, fewer than a
third of the validators in the adversary set up to its end, committee sleepiness from
`anchorCW S tGAT`, the threshold `H₂` attained at `T₁` with `tGAT ≤ T₁` and `T₁ + Δ` at most the start of slot `rs 0 * R − k − 1`,
every honest attestation before `aR S r ≤ tAwakeEnd` at most `H₂`, the honest round opening slots
`rs 0 < … < rs m`): for an opening `i < m` with `rs (i + 1) * R ≤ r * R`, no opening's proposal
colliding with a block its proposer held, no validator outside the adversary set with a
`ForkChoiceChangeAt` from the vote time of slot `rs i * R − k − 1` to before the support cutoff
of slot `rs (i + 1) * R`, every proposal of the next opening at most as high as the opening's
proposal `B`, and `B` at most `H₂` high: some proposal `B'` of the next opening has `B` as an
ancestor, `B`'s chain-state height, is held by its proposer one time unit after its slot's start,
and `H₂ ≤ h(B) + 1 ≤ H₂ + 1`.

A copy of `quiet_rising_next_proposal` (`Proofs/Executions/Lemma89RisingJ.lean`) with the rising
hypothesis replaced by the waiting one (`hWait`) and `hTop`; proved in
`Proofs/Executions/Lemma89ClimbLate.lean`.

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, a weaker
hypothesis than `T₁ ≤ slotStart S (rs 0 * R − 2k)`: the climb takes `T₁` three delays into slot
`rs 0 * R − 2k`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `rs`: the rounds of the
  honest round opening slots; `B`: the proposal at the honest round opening slot.

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Read aloud: a waiting quiet opening's next proposal extends it at the same height, `H₂ − 1` or
`H₂`. -/
theorem quiet_waiting_next_proposal (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hi : i < m) (hir : rs (i + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hWait : ∀ B' : Block V, ProposalAt S Sched x (rs (i + 1) * S.C.R) B' →
      (chainStateOf S.C B').h ≤ (chainStateOf S.C B).h)
    (hTop : (chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) :
    ∃ B' : Block V, ProposalAt S Sched x (rs (i + 1) * S.C.R) B' ∧
      B.AncestorEq B' ∧ (chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
      B' ∈ (stateBefore x (slotStart S (rs (i + 1) * S.C.R) + 1)
        (S.P.proposer (rs (i + 1) * S.C.R))).S.T ∧
      H₂ ≤ (chainStateOf S.C B).h + 1 ∧ (chainStateOf S.C B).h ≤ H₂ :=
  GoldilocksCorrectness.Proofs.Executions.quiet_waiting_next_proposal S Sched x GST tGAT tAwakeEnd
    T₁ r H₂ m i rs B hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁ hThird hAwake
    hCommittees hH₂ hOld hEnd hSeq hT₁0 hi hir hNoCol hNo hSyncF hCatchF hWait hTop hB

/-- **Two waiting quiet openings at one height share the height's entry.** In the climb's context
(as for `quiet_waiting_next_proposal`: the execution assumptions and unforgeability, every honest
validator awake in `[tGAT, tAwakeEnd]`, fewer than a third of the validators in the adversary set up
to its end, committee sleepiness from `anchorCW S tGAT`, the threshold `H₂` attained at `T₁` with
`tGAT ≤ T₁` and `T₁ + Δ` at most the start of slot `rs 0 * R − k − 1`, every honest attestation before `aR S r ≤ tAwakeEnd` at
most `H₂`, the honest round opening slots of the rounds `rs 0 < … < rs m`): take two openings `i < i' < m` with
`rs (i' + 1) * R ≤ r * R`, no opening's proposal colliding with a block its proposer held, no
validator outside the adversary set with a `ForkChoiceChangeAt` from the vote time of slot
`rs i * R − k − 1` to before the support cutoff of slot `rs (i + 1) * R`, nor from the vote time
of slot `rs i' * R − k − 1` to before the support cutoff of slot `rs (i' + 1) * R`, every proposal
of opening `i + 1` at most as high as opening `i`'s proposal `B`, and `B` at most `H₂` high. If
`B` and opening `i'`'s proposal `B₂` have the same chain-state height, they have the same entry
(`(chainStateOf S.C ·).T_h`).

Proved in `Proofs/Executions/Lemma89ClimbLate.lean`, a copy of
`quiet_rising_heights_differ_cutoff`'s route.

Why: the next proposal `B'` after `B` is on `B`'s chain at `B`'s height `h`; no honest validator has
`h_j ≥ h` before the later opening's support cutoff (`h_j_lt_or_genesis_before_cutoff`), so every
honest holder of `B'` has its root on `B'`'s chain and `B'` reaches every honest validator; the
honest votes carry the chain invariant relative to `B'` to the later opening, whose proposal then
extends `B'`: one entry (Lemma 47 (e)).

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, a weaker
hypothesis than `T₁ ≤ slotStart S (rs 0 * R − 2k)`: the climb takes `T₁` three delays into slot
`rs 0 * R − 2k`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i < i'`: the indices of the two honest round opening slots; `rs`: the
  openings' rounds; `B`, `B₂`: their proposals.

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Read aloud: two quiet openings waiting at one height wait on the same entry. -/
theorem quiet_waiting_same_entry_cutoff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i i' : ℕ) (rs : ℕ → ℕ)
    (B B₂ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hir' : rs (i' + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hNo' : ∀ (w : V) (t' : ℕ), voteTime S (rs i' * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i' + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hWait : ∀ B' : Block V, ProposalAt S Sched x (rs (i + 1) * S.C.R) B' →
      (chainStateOf S.C B').h ≤ (chainStateOf S.C B).h)
    (hTop : (chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) (hB₂ : ProposalAt S Sched x (rs i' * S.C.R) B₂) :
    (chainStateOf S.C B).h = (chainStateOf S.C B₂).h →
      (chainStateOf S.C B).T_h = (chainStateOf S.C B₂).T_h :=
  GoldilocksCorrectness.Proofs.Executions.quiet_waiting_same_entry_cutoff S Sched x GST tGAT
    tAwakeEnd T₁ r H₂ m i i' rs B B₂ hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST
    hT₁ hThird hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 hii' hi' hir' hNoCol hNo hNo' hSyncF
    hCatchF hWait hTop hB hB₂

open Classical in
/-- **At most six openings before the climb's end lie outside the spans the climb places.** Under
the execution assumptions and unforgeability, with every honest validator awake in the phase
`[tGAT, tAwakeEnd]`, fewer than a third of the validators in the adversary set up to its end,
committee sleepiness from `anchorCW S tGAT`, the honest round opening slots of the rounds `rs 0 < … < rs m`
(`HonestOpeningSeq`), the threshold `H₂` the greatest height of an honest attestation before `T₁`
(`OldHeightAttained`) with `tGAT ≤ T₁` and `T₁ + Δ` at most the start of slot `rs 0 * R − k − 1`,
every honest attestation sent before `aR S r ≤ tAwakeEnd` of height at most `H₂`, and no opening's
proposal colliding with a block its proposer held: there are two spans of `δt` slots (`waits`) and
four spans of `k + 2` slots (`w4`) such that at most six honest round opening slots `i < m` with
`rs i * R < r * R` have their first slot outside all of them; the one whose round holds `r * R`
among them.



Why: the four spans of `k + 2` slots start at the slots of the four times of
`fork_choice_change_kinds`, the two of `δt` slots at the slots of the entries of the waiting
openings at the heights `H₂ − 1` and `H₂`. An opening with a `ForkChoiceChangeAt` of a validator
outside the adversary set from the vote time of slot `rs i * R − k − 1` to before the support
cutoff of slot `min (rs (i + 1) * R) (r * R)` outside the span of the change's kind has the change
in its round, and two such openings of one kind would put the later one in that kind's span: at
most four. An opening with no such change whose next slot is at or before `r * R` is quiet with
its base, so it rises or waits (Lemma 89r); a waiting one lies in its height's wait span
(`quiet_waiting_same_entry_cutoff`); the rising ones and the one whose round holds `r * R` are at
most two (`quiet_rising_before_fast_round_le_two_cutoff`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR S r`: `fork_choice_change_kinds` and the climb's steps read up to the
action time of round `r`.

Read aloud: before the climb's end, two waits and four windows leave at most six honest round opening slots
outside them. -/
theorem climb_count_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m) :
    ∃ (waits : Fin 2 → ℕ) (w4 : Fin 4 → ℕ),
      ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
        OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i)).card ≤ 6 :=
  GoldilocksCorrectness.Proofs.Executions.climb_count_before S Sched x GST tGAT tAwakeEnd T₁ r H₂
    m rs hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hGST hT₁ hThird
    hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 hNoCol

/-- **Part B's assembly, the climb to the first honest fast block.** Under the execution assumptions (time diverges, monotone corruption, synchrony and
catch-up on wake for the AC objects with delay `Δ` and for the FG objects with delay `Δ_F` from
`GST`, roots name blocks, a block's parent is held at its delivery, votes are
cast by their owners) and unforgeability, with `GST ≤ tGAT`, fewer than a third of the validators
in the adversary set up to `tAwakeEnd`, every validator outside the adversary set awake from
`tGAT` to `tAwakeEnd`, committee sleepiness from `anchorCW S tGAT`, the honest round opening slots
`rs 0 < … < rs m` from `tGAT + 4Δ · healFrontSlots S` to `tAwakeEnd`, and nine honest round
opening slots outside every two spans of `δt` slots and five spans of `k + 2` slots
(`OpeningsOutsideWaitsAndWindows`): either some opening's proposal collides with a block
its proposer held (`RootCollisionAtOpening`), or there are a round `r`, a threshold `H₂`, a
validator `v`, a block `L` and an update answer `A'` with: slot `r * R + 1` starting at or after
`anchorCW S tGAT`; `aR S r ≤ tAwakeEnd`; every honest attestation sent before `aR S r` of height
at most `H₂`; `v` outside the adversary set at `aR S r`; `v`'s update of slot `r * R + 1` at
`aR S r` answering `A'` with `L` among its fast blocks; `L`'s chain-state height `H₂ + 1`; and an
honest round opening slot `j` with `j + 2 ≤ m`, the first whose first slot is at least `k + 2`
slots after `r * R`.

Proved in `Proofs/Executions/Lemma89Climb5.lean`.

The probe's `climb_to_fast_block5` (`scratch/goldilocks_healed/probe_recount_1.lean:362`, not
landed) with the count 11 in place of 10: with 10, the opening whose round straddles `r * R`
leaves only three openings after the fast block.

Why: split on the collision disjunct. Take `T₁` three delays into slot `rs 0 * R − 2k` and `H₂` the
greatest height of an honest attestation before `T₁` (B1). Some honest attestation above `H₂` is
sent from `T₁` to before `aR S (rs (m − 1))`, or `climb_count_before` at that round leaves seven
outside openings at most. B3 gives the first round `r` above `H₂`, B4 its fast block `L`; `T₁ ≤
aR S r` puts slot `r * R + 1` at or after the anchor. At `r`, at most six outside openings `i < m`
with `rs i * R < r * R`, and the last
one (`after_of_before`): three outside honest round opening slots are at or after `r * R`, hence
at least `k + 2` slots after it (the span of `k + 2` slots at `r * R`), so the first honest round
opening slot at least `k + 2` slots after `r * R` has two more after it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR S (rs (m - 1))`: the count at the round `rs (m − 1)`
(`climb_count_before`), and at the first round `r` above the threshold, whose action time is before
`aR S (rs (m - 1))`.

Read aloud: nine honest round opening slots outside two timeout waits and five spans of `k + 2`
slots give the first honest fast block one height above the threshold and three honest
round opening slots at least `k + 2` slots after its round. -/
theorem climb_to_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S (rs (m - 1))))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening S Sched x rs m ∨
    ∃ (r H₂ : ℕ) (v : V) (L : Block V) (A' : ACState V),
      anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1) ∧ aR S r ≤ tAwakeEnd ∧
      OldAttestationsAtMost S Sched x (aR S r) H₂ ∧
      v ∉ Sched.adv ((aR S r : ℕ) : Int) ∧
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A' ∧
      L ∈ A'.fast_blocks ∧ (chainStateOf S.C L).h = H₂ + 1 ∧
      ∃ j : ℕ, j + 2 ≤ m ∧ r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R ∧
        ∀ i : ℕ, i < j → rs i * S.C.R < r * S.C.R + S.C.k + 2 :=
  GoldilocksCorrectness.Proofs.Executions.climb_to_fast_block S Sched x GST tGAT tAwakeEnd m rs
    hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hSeq hm

open GoldilocksCorrectness.Statements.Routines (JustificationCertOn)

/-- **C4, consecutive openings after the fast block rise (a copy of the skeleton's
`opening_rises_after_fast_block` with the round's first slot).** Under the execution assumptions,
attestations delivered within `Δ_F` after `GST` and unforgeability, with the phase's premises and
part A's (the fast block `L` of `v`'s update at the action time of round `r`, of height `H₂ + 1`):
when the honest round opening slot `s` is a round's first slot at least `k + 2` slots after `r * R`
,
`B` is its proposal, and `B'` is the proposal of a later honest round opening slot `s'' ≥ s + R` with
`supportCutoff S s'' ≤ tAwakeEnd`: either a block the proposer of slot `s` held before the start of
slot `s` has `B`'s root, or `B` is `B'` or an ancestor of `B'`, `B'`'s chain-state height is at
least `B`'s plus one, when `B'`'s parent is at `B`'s height the justified block of `B'`'s chain
state is `B`'s entry `T_h`, and every member of `Hon S Sched s` saved `B` as its confirmation of
slot `s`.

The copy's change, against the skeleton (`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:266`):
the hypothesis `hsR : S.C.R ∣ s` is added, which C1 and C2 (their copies) read; every caller reads
C4 at an opening, the first slot `rs i * R` of a round. The skeleton's hypotheses `hLv`, `hInvL`
and `hInvF` are deleted: the proof reads part A's line invariant directly.

Why: with no root collision, Lemma 89r with the targets premise (`lem89r_quiet_round_targets`) at
the round of slot `s`, its family the line sources of the slots `μ` with `μ + 2 ≤ s`, its quiet
round C2; the targets premise holds because `B`'s height is greater than `H₂` and every honest
attestation at such a height from round `r`'s action time on is a target
(`PartAHyps.attestation_target`). The skeleton's flag on the fresh height is answered there: a
member that attested at `B`'s height in an earlier round did so for `B`'s entry, with a target.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `r`, `H₂`, `v`, `L`, `A'`: the fast block's round, the threshold, the validator, the fast block,
  the update's answer;
- `s`, `B`: the honest round opening slot and its proposal; `s''`, `B'`: the next honest round opening slot and
  its proposal.

Roots name blocks until `supportCutoff S s''`: the bundle `PartAHyps` is built with its end time
`supportCutoff S s''`, the latest time its kit reads here; C2 reads up to the same time, Lemma 89r
up to `supportCutoff S (s'' - 1)`.

Read aloud: after the fast block, every honest round opening slot's proposal is extended by the next one's,
one height higher, which carries its justification.

 -/
theorem opening_rises_after_fast_block_opening (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s s'' : ℕ) (v : V)
    (L B B' : Block V) (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s''))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s) (hs'' : s + S.C.R ≤ s'')
    (hEnd : supportCutoff S s'' ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hq : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int))
    (hB : ProposalAt S Sched x s B) (hB' : ProposalAt S Sched x s'' B') :
    RootCollisionAtProposal S Sched x s B ∨
    (B.AncestorEq B' ∧ (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
      ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
        (chainStateOf S.C B').J = (chainStateOf S.C B).T_h) ∧
      ∀ u ∈ Hon S Sched s,
        (stateBefore x (supportCutoff S (s + 1) + 1) u).A.saved_confirmation s = some B) :=
  GoldilocksCorrectness.Proofs.Executions.opening_rises_after_fast_block_opening S Sched x GST tGAT
    tAwakeEnd r H₂ s s'' v L B B' A' hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent
    hOwner hU hGST hThird hAwake hCommittees hAnchor hOld hv hL hUpdate hFast hs hsR hs'' hEnd hp hq
    hB hB'

/-- **C6, the caches at the hand-over step (a copy of the skeleton's `caches_at_handover` with the
proposal held and the finalized blocks on it).** Under the execution assumptions and
unforgeability, every honest validator awake from `tGAT` to `tAwakeEnd`, fewer than a third of the
validators in the adversary set up to `tAwakeEnd`: when `B₃`, held by the proposer of slot
`s₃ ≤ s_m` (honest at its support cutoff) right after the start of slot `s₃ ≥ tGAT`, has a chain
state whose justification height is greater than `H`, every validator honest at the vote time of
slot `s₃` has its finalized block before that time `B₃` or an ancestor of `B₃`, every justified
block an honest validator holds at the step `i₁` at a height greater than `H` is, by its root, an
entry of the honest chain from `s₀` at a slot `s_a` with `supportCutoff S (s_a + 1) ≤ x[i₁].time`,
`supportCutoff S s_m ≤ tAwakeEnd`, and the step `i₁` is at
the vote time of slot `s_m` — then every validator honest at `x[i₁].time` has
`CachesOnChain S Sched x s₀ H` at `i₁`.

The copy's change, against the skeleton (`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:354`):
the proposal `hB₃` is replaced by `hHeld` (its proposer holds it), and `hF₃` (the finalized blocks
before the vote time of slot `s₃` are on `B₃`) is added: without them `B₃` need not reach a
validator by the vote time of slot `s_m` when `s₃ = s_m` (its delivery is accepted only on the
receiver's finalized chain), and C6's own hypotheses say nothing of the receivers' finalized blocks.
`hCerts` is read at the step `i₁` only (a weaker hypothesis). `hs₀` and `hJchain` are deleted
(unused). The hand-over supplies `hHeld` from `opening_proposal_held` and `hF₃` from
`PartAHyps.F_before_vote_ancestor_proposal`. the hand-over supplies it from `cert_entry_at_slot`.

Why: `B₃` reaches every honest validator by the vote time of slot `s₃` (`mem_T_at_step_of_held`),
so the cache `h_j` is at least `h_j(B₃) > H` (`h_j_ge_of_held_exec`); the justified block is a held
block's chain state's, with its justification certificate (Lemma 66), so `hCerts` puts it on the
honest chain (roots name blocks); the finalized block is on the justified block's chain (Lemma 46).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
- `s₀`: the first slot of the honest chain; `H`: the threshold; `s₃`, `B₃`: the carrier's slot and
  block; `s_m`: the last honest round opening slot; `i₁`: the step; `s_a`: the slot of an entry `hCerts`
  names.

Roots name blocks until `x[i₁].time`: the justified block `u` holds at the step `i₁` against the
entry `hCerts` names, at a slot whose update ran by `x[i₁].time`; `B₃` reaches `u` by the vote time
of slot `s₃`, before it.

Read aloud: once the carrier has reached everyone, every honest finality gadget's caches are on the
honest chain above the threshold.

 -/
theorem caches_at_handover_of_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s₀ H s₃ s_m i₁ : ℕ) (B₃ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (x[i₁].time))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hs₃ : s₃ ≤ s_m) (htGAT : tGAT ≤ slotStart S s₃)
    (hEnd : supportCutoff S s_m ≤ tAwakeEnd)
    (hp : S.P.proposer s₃ ∉ Sched.adv ((supportCutoff S s₃ : ℕ) : Int))
    -- the proposer holds `B₃` right after its proposal
    (hHeld : B₃ ∈ (stateBefore x (slotStart S s₃ + 1) (S.P.proposer s₃)).S.T)
    -- every validator honest at the vote time of slot `s₃` has its finalized block before that
    -- time `B₃` or an ancestor of `B₃`
    (hF₃ : ∀ u : V, u ∉ Sched.adv ((voteTime S s₃ : ℕ) : Int) →
      (stateBefore x (voteTime S s₃) u).S.F.AncestorEq B₃)
    (hJ : H < (chainStateOf S.C B₃).h_j)
    -- every justified block an honest validator holds at the step `i₁` at a height greater than
    -- `H` is on the chain, at a slot whose update ran by `x[i₁].time`
    (hCerts : ∀ (w : V) (D T : Block V) (h : Height),
      D ∈ (x[i₁][w].st).S.T → JustificationCertOn D h T → H < h →
      ∃ (s_a : ℕ) (E : Block V), supportCutoff S (s_a + 1) ≤ x[i₁].time ∧
        OnHonestChainAt S Sched x s₀ s_a E ∧ IsEntry S.C E ∧
        (chainStateOf S.C E).h = h ∧ T.root = E.root)
    (hi₁ : x[i₁].time = voteTime S s_m) :
    ∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) → CachesOnChain S Sched x s₀ H (x[i₁][u].st) :=
  GoldilocksCorrectness.Proofs.Executions.caches_at_handover_of_held S Sched x GST tGAT tAwakeEnd s₀
    H s₃ s_m i₁ B₃ hDiv hMono hSync hCatch hRoots hParent hU hGST hThird hAwake hs₃ htGAT
    hEnd hp hHeld hF₃ hJ hCerts hi₁

/-- **C7, Lemma 89's frame clauses from the line invariant.** Under the execution assumptions and
unforgeability, with the phase's premises and part A's (the fast block `L` of `v`'s update at the
action time of round `r`, of height `H₂ + 1`): for `s₀ ≥ r * R + k + 2` and
`supportCutoff S s_m ≤ tAwakeEnd`, at every slot `s` with `s₀ < s < s_m`, every member of
`Hon S Sched s` satisfies `VoterFrameOnChainAt S Sched x s₀ s` and
`UpdaterFinalizedOnChainAt S Sched x s₀ s`.

The skeleton's hypotheses `hLv`, `hInvF` and `hInvL` are deleted: the proof reads part A's line
invariant directly.

Why: a block on the honest chain before `s` from `s₀` is on an updater's confirmation of a slot
`s' ≥ s₀`, a line source of slot `s'` (`source_conf`); `stepFrame_source` at slot `s − 1` gives
`StepFrameAt` relative to it, whose conjuncts are the two clauses.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `r`, `H₂`, `v`, `L`, `A'`: the fast block's round, the threshold, the validator, the fast block,
  the update's answer; `s₀`: the healed round's slot; `s_m`: the last honest round opening slot.

Roots name blocks until `supportCutoff S s_m`: the bundle `PartAHyps` is built with its end time
`supportCutoff S s_m`, the latest time its kit reads here.

Read aloud: after the healed round every member's frame follows the honest chain so far.

 -/
theorem frames_at_phase_slots (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s₀ s_m : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s_m))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hs₀ : r * S.C.R + S.C.k + 2 ≤ s₀) (hEnd : supportCutoff S s_m ≤ tAwakeEnd) :
    ∀ s : ℕ, s₀ < s → s < s_m → ∀ w ∈ Hon S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w :=
  GoldilocksCorrectness.Proofs.Executions.frames_at_phase_slots S Sched x GST tGAT tAwakeEnd r H₂ s₀
    s_m v L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hAnchor hOld hv hL hUpdate hFast hs₀ hEnd

/-- **C8, the hand-over step exists.** In an execution that reaches every time, some step is at the
vote time of slot `s_m`.

Why: the tick at that time (`exists_lbl_tickAllAwake`) ends at it (`time_of_lbl_tickAllAwake`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s_m`: the slot.

Read aloud: the vote time of every slot is the time of some step.

 -/
theorem exists_handover_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s_m : ℕ) (hDiv : TimeDiverges x.toTrace) :
    ∃ i₁ : ℕ, x[i₁].time = voteTime S s_m :=
  GoldilocksCorrectness.Proofs.Executions.exists_handover_step S Sched x s_m hDiv

/-- **The hand-over after the fast block (part C's assembly).** Lemma 89's hypotheses, the climb's
output:
then Lemma 89's
right disjunct at `j`, with the threshold `h(B₀)`, or a root collision at an honest round opening
slot.

The skeleton's hypotheses `hEnd`, `hfirst` and part A's three conclusions `hInvL`, `hInvF`,
`hCerts` are deleted: the proof reads part A's line invariant directly and does not use the others.

Why: with no root collision at an opening, every opening's proposal is of its slot and held by its
proposer; at `s₀ := s_j` the copies of C1 and C3 give the base, the saved `B₀ := B_j` and its slot,
and `old_attestations_at_opening` the old attestations, at most `h(B₀)`; C7 the frames; the copy
of C4 at `j` and `j + 1` the chain `B_j ⪯ B_{j+1} ⪯ B_{j+2}`, one height per honest round opening
slot, and the justification clause at `j + 1`; `HonestOpeningSeq.spacing` at `j` and the tree's
slot order give C5's hypotheses, so `h_j(B_{j+2}) ≥ h(B_{j+1}) ≥ h(B₀) + 1`; C8 the step `i₁`; the
copy of C6 the caches at the threshold `h(B₀)`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`, `rs`: the index of the last honest round opening slot and the rounds of the honest round opening slots; `r`, `H₂`, `v`, `L`, `A'`: the climb's output; `j`: the index of an honest round opening slot.

Roots name blocks until `supportCutoff S (rs m * S.C.R)`: the bundle `PartAHyps` is built with its
end time `supportCutoff S (rs m * S.C.R)`; C4 at the honest round opening slots `j` and `j + 1`, C1,
C3, C6 and C7 read up to that time.

Read aloud: the first honest round opening slot a `k + 2`-slot wait after the fast block is the
healed round, and the two honest round opening slots after it bring the justification above
`h(B₀)` to every honest validator by the vote time of the last honest round opening slot.

  -/
theorem handover_after_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m r H₂ : ℕ) (rs : ℕ → ℕ) (v : V)
    (L : Block V) (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (rs m * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- the climb's output
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks) (hL : (chainStateOf S.C L).h = H₂ + 1)
    (j : ℕ) (hj2 : j + 2 ≤ m) (hsj : r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R) :
    RootCollisionAtOpening S Sched x rs m ∨
    (∃ (j' s₀ i₁ : ℕ) (B₀ : Block V),
      j' < m ∧ s₀ = rs j' * S.C.R ∧ x[i₁].time = voteTime S (rs m * S.C.R) ∧
      HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt S Sched s₀,
        (stateBefore x (supportCutoff S (s₀ + 1) + 1) u).A.saved_confirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        ∀ w ∈ roundMembers S Sched (s + 1),
          VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w) ∧
      (∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) →
        CachesOnChain S Sched x s₀ (chainStateOf S.C B₀).h (x[i₁][u].st))) :=
  GoldilocksCorrectness.Proofs.Executions.handover_after_fast_block S Sched x GST tGAT tAwakeEnd m r
    H₂ rs v L A' hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hGST hThird
    hAwake hCommittees hSeq hAnchor hOld hv hUpdate hFast hL j hj2 hsj

/-- **C9, every honest round opening slot has a proposal (a copy of the skeleton's `opening_proposal_exists`
for the slots from `2` on).** In an execution that reaches every time, with permanent corruption:
when the proposer of slot `s ≥ 2` is honest at the support cutoff
of slot `s`, every honest validator is awake from `tGAT` to `tAwakeEnd`, the proposal window of
slot `s` starts at or after `tGAT` and slot `s` starts at or before `tAwakeEnd`, the proposer's
tick at the start of slot `s` puts some block on the wire.

The copy's change, against the skeleton (`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:446`):
`hs1 : 1 ≤ s` becomes `hs2 : 2 ≤ s`, the slots the landed proposal kit covers
(`honest_proposer_proposesJ`); slot `1` is not measured. The copy has its own name because the
landed `opening_proposal_exists` (`Proofs/Executions/Lemma89RisingJ.lean:915`, over the opening
sequence, the form the hand-over calls) has the skeleton's name in the same namespace.

Why: the proposer is awake and honest from the proposal window's start to the slot's start, so its
tick proposes (`honest_proposer_proposesJ`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tGAT`, `tAwakeEnd`: the times; `s`:
  the slot.

Read aloud: an honest proposer awake through its proposal window proposes.

 -/
theorem opening_proposal_exists_of_window (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tGAT tAwakeEnd s : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hs2 : 2 ≤ s) (hWindow : tGAT ≤ proposalWindowStart S s) (hEnd : slotStart S s ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int)) :
    ∃ B : Block V, ProposalAt S Sched x s B :=
  GoldilocksCorrectness.Proofs.Executions.opening_proposal_exists_of_window S Sched x tGAT tAwakeEnd
    s hDiv hMono hAwake hs2 hWindow hEnd hp

/-! ## Lemma 89

Proved in `Proofs/Executions/Lemma89HandoverVF.lean`. -/

/-- **Lemma 89 of record: the events of the phase.** Under the phase's
premises and nine honest round opening slots outside every two spans of `δt` slots and five spans
of `k + 2` slots (`OpeningsOutsideWaitsAndWindows`, `PhaseDefs.lean`): either some honest round opening slot's proposal has
the root of a block its proposer held, or some opening `j < m` is the healed round: its first slot
`s₀` and proposal `B₀`, of slot `s₀`; the slot invariant restricted to `B₀` at `s₀` over the
honest active validators of `s₀`; every updater of `s₀` saved `B₀`; every honest attestation sent
before the round's action time has height at most `h(B₀)`; at every slot `s` with
`s₀ < s < s_m`, every member of `roundMembers S Sched (s + 1)` has its frame on the honest chain
before `s`; at the step `i₁` at the vote time of slot `s_m`, every honest validator's caches are on
the honest chain with `h_j > h(B₀)`; and every validator `w` outside the adversary set at the
vote time of slot `s_m` has its frame before that vote time on the honest chain before `s_m`
. Here `s_m := rs m * R`, the
first slot of the last opening.

Why the clause: the phase still runs at the vote time of slot `s_m` (its support cutoff is at most
`tAwakeEnd`, `HonestOpeningSeq.last`), so the phase's line invariant gives the voter frame there
(`PartAHyps.voterFrame_at_last_opening`); nothing after the hand-over reaches that time, the
caches being known only from `i₁` on.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`, `rs`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Why: the climb `climb_to_fast_block` and the hand-over's copy with the voter frame
`handover_after_fast_block_vf` (part A's assembly is not needed: the hand-over reads the line
invariant directly).

Roots name blocks until `supportCutoff S (rs m * S.C.R)`: the hand-over's copy
(`handover_after_fast_block_vf`); the climb reads up to `aR S (rs (m - 1))`, before it.

Read aloud: the conclusion of Lemma 89, and the voter frame at the last opening's slot.

   -/
theorem lem89_phase (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (rs m * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening S Sched x rs m ∨
    (∃ (j s₀ i₁ : ℕ) (B₀ : Block V),
      j < m ∧ s₀ = rs j * S.C.R ∧ x[i₁].time = voteTime S (rs m * S.C.R) ∧
      HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt S Sched s₀,
        (stateBefore x (supportCutoff S (s₀ + 1) + 1) u).A.saved_confirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        ∀ w ∈ roundMembers S Sched (s + 1),
          VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w) ∧
      (∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) →
        CachesOnChain S Sched x s₀ (chainStateOf S.C B₀).h (x[i₁][u].st)) ∧
      (∀ w : V, w ∉ Sched.adv ((voteTime S (rs m * S.C.R) : ℕ) : Int) →
        VoterFrameOnChainAt S Sched x s₀ (rs m * S.C.R) w)) :=
  GoldilocksCorrectness.Proofs.Executions.lem89_phase S Sched x GST tGAT tAwakeEnd m rs hDiv
    hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hGST hThird hAwake hCommittees
    hSeq hm

end GoldilocksCorrectness.Statements.Executions
