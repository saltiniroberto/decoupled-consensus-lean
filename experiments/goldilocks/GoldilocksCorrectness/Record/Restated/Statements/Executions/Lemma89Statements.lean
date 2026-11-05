module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastBase
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89HealedRound
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89WaitJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89ClimbLate
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Climb5
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Handover
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89HandoverVF
public import GoldilocksCorrectness.Statements.Routines.ChainStateOfStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89Statements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/Lemma89Statements.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 89 of record
(`lem89_phase`), the events of the phase on the span premise `OpeningsOutsideWaitsAndWindows`, and
the steps it is proved from: part A on the fast-confirmation route (the fast block of an honest
attestation, the heights held before the action time, the finalized blocks, the fast block's base,
the line invariant and the frames relative to the fast block and to a late family), part B (the
threshold `H₂`, the window and its last confirmation, the kinds of fork-choice change, the quiet
honest round opening slots, the round base, the justified heights, the rising and waiting steps, the
climb to the first honest fast block), part C (the honest round opening slots rising after the fast
block, the caches at the hand-over, the frames at the phase's slots, the hand-over itself), and the
audited statements (the quiet round and `FrontWindowStable` written out); each is the theorem of the
same name of its proof page under `Record/Restated/Proofs/Executions/`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart proposalWindowStart anchorCW)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (healFrontSlots)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn)
open GoldilocksCorrectness.Statements.Executions (InSpan Vocab.goldilocks acObject)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked
  VoterTreeAt hMax)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated LocksRevoked)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated hMax)
open GoldilocksCorrectness.Record.Statements.Routines (FrameShape ProgressCertOn)
open GoldilocksCorrectness.Statements.Executions (InSpan healFrontSlots)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject
  healFrontSlots)
open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn ConfirmationUpdated)
open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)
open GoldilocksCorrectness.Record.Statements.Routines (TreeClosed)
open GoldilocksCorrectness.Statements.Executions (InSpan OpeningsOutsideWaitsAndWindows
  OutsideSpans Vocab.goldilocks acObject fgObject healFrontSlots)
open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn ProgressCertOn
  RecordConsistent TreeClosed)
open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn TreeClosed)
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows OutsideSpans
  Vocab.goldilocks acObject fgObject healFrontSlots)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **A round that is not quiet relative to its own confirmations.** When
`QuietRoundOnConfirmations M S Sched x (Hon M) B s s''` fails: some member of `Hon M s` has its root
off `B.parent`'s chain or its `head_height_floor` past `h(B.parent)` in the state its tick to the
vote time of slot `s` starts from, or its root off `B`'s chain or its `head_height_floor` past
`h(B)` in the state its tick to the action time starts from; or at a slot `s'` of the round some
member of `Hon M (s' + 1)` fails `StepFrameAt` relative to `B`; or relative to a confirmation a
member of `Hon M σ` saved for a slot `σ` from `s − 1` to `s'`; or the proposer of slot `s''`, in the
state its tick to the start of slot `s''` starts from, has for no confirmation of slot `s'' − 2`
saved by a member of `Hon M (s'' − 2)` both its root on that confirmation's chain and a viable head
that is that confirmation or a descendant of it. The confirmations of a slot are those the members
of the slot's own set save, the updaters of the slot in the phase.

Why: it is the negation of `QuietRoundOnConfirmations`, its first two clauses split into the root
and the `head_height_floor`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon`: one member set per slot;
- `B`: the round's proposal; `s`: its first slot; `s''`: the next honest round opening slot.

Read aloud: a round that is not quiet shows a member's root off the chain or its
`head_height_floor` past the clause's height, a failed step condition, or the next proposer off
every last confirmation. -/
theorem quietRound_cases (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ)
    -- the round is not quiet relative to its own confirmations
    (hNotQuiet : ¬ QuietRoundOnConfirmations M S A x Hon B s s'') :
    (∃ w ∈ Hon s,
      RootOffChainAtTick M S A x w (M.voteTime S.C s) B.parent ∨
      HeadHeightFloorPastAtTick M S A x w (M.voteTime S.C s) (M.chainStateOf S.C B.parent).h ∨
      RootOffChainAtTick M S A x w (M.supportCutoff S.C (s + 1)) B ∨
      HeadHeightFloorPastAtTick M S A x w (M.supportCutoff S.C (s + 1))
        (M.chainStateOf S.C B).h) ∨
    (∃ s', s ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ w ∈ Hon (s' + 1), ¬ StepFrameAt M S A x B s' w) ∨
    (∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ σ, s - 1 ≤ σ ∧ σ ≤ s' ∧ ∃ v ∈ Hon σ,
      ∃ C : Block V,
        (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C ∧
        ∃ w ∈ Hon (s' + 1), ¬ StepFrameAt M S A x C s' w) ∨
    (∀ C : Block V,
      (∃ v ∈ Hon (s'' - 2),
        (x.tickOutput v (M.supportCutoff S.C (s'' - 1))).savedConfirmation (s'' - 2) =
          some C) →
      ¬
        ((M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).fc_root.AncestorEq
            C ∧
        ∃ W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s'') (M.slotStart S.C s''))).viable_heads ∧
          C.AncestorEq W)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.quietRound_cases M F) S A x Hon B s s''
    hNotQuiet

/-- **A failure of `FrontWindowStable`, written out.** Under the member sets shrinking from one slot
to the next and every member of the set of a slot honest at the support cutoff of the next slot:
when `FrontWindowStable M S Sched x (Hon M) s_w s'` fails, one of four things happens, each at a
member `w` of a set `Hon M s₁` with `s_w + k − 1 ≤ s₁ ≤ s'`:

1. `w`, a member of `Hon M (s₁ + 1)` with `s₁ < s'`, has its root before `M.voteTime S.C (s₁ + 1)`
in conflict with a confirmation `X` a member saved for a slot from `s_w + k − 1` to `s₁`
   (`RootIncompatibleAt`);
2. or that root is `X` or an ancestor of such an `X`, `w` holds `X` then, and no block of `w`'s
   voter tree of slot `s₁ + 1` that is `X` or a descendant of `X` is a viable head;
3. or `w`'s finalized block before `M.supportCutoff S.C (s₁ + 2)` conflicts with such an `X`
   (`FinalizedIncompatibleAt`);
4. or, at `s₁ = s'`, `w`'s root before `M.voteTime S.C (s' + 1)` is `D` or an ancestor of `D` for no
   block `D` of a live lock entry of a member of `Hon M s'` and no confirmation `D` of slot `s' − 1`
   of a member of `Hon M s'` (`RootOffChainAt` at every such `D`).

Why: the two clauses of `FrontWindowStable` negated; the failure of the first is a failed
`StepFrameAt` (`stepFrameAt_fail_cases`), where `w` holds `X` in the second case by the delivery
of the saver's own copy.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase, in which every honest validator is
  awake; `s_w`: the slot the window is counted from; `s'`: its last slot; `Hon`: one member set
  per slot.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' - 1) + Δ S`
: `stepFrameAt_fail_cases` at a slot `σ` at most `s' − 1`, whose roots premise is that
form at the clock value `M.supportCutoff S.C σ + Δ S`.

Read aloud: a window breaks at a member whose root or finalized block conflicts with a window
confirmation, whose frame finds no viable head on a confirmation's chain, or whose root is on no
family block's chain at the window's last slot. -/
theorem frontWindowStable_fail_event (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most one delay after the
    -- support cutoff of slot `s' - 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c →
      c ≤ M.supportCutoff S.C (s' - 1) + Δ S → RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from `tGAT` on; the window has at least `2k − 1` slots
    (hGST : GST ≤ tGAT) (hs' : s_w + 2 * S.C.k - 1 ≤ s')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁)
    -- every member of the set of slot `s₁` is honest at the support cutoff of slot `s₁ + 1`
    (hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
      v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 1)))
    -- every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- the duty window of slot `s_w` starts at or after `tGAT`; the support cutoff of slot
    -- `s' + 1` is inside the phase
    (hsw : tGAT ≤ M.dutyWindowStart S.C s_w) (hEnd : M.supportCutoff S.C (s' + 1) ≤ tAwakeEnd)
    -- the window is not stable
    (hFail : ¬ FrontWindowStable M S A x Hon s_w s') :
    ∃ (s₁ : ℕ) (w : V), s_w + S.C.k - 1 ≤ s₁ ∧ s₁ ≤ s' ∧ w ∈ Hon s₁ ∧
      ((∃ X : Block V, WindowConfirmation M S A x Hon (s_w + S.C.k - 1) s₁ X ∧ s₁ < s' ∧
          w ∈ Hon (s₁ + 1) ∧
          (RootIncompatibleAtTick M S A x w (M.voteTime S.C (s₁ + 1)) X ∨
            ((M.get_fc_root (x.tickInput w (M.voteTime S.C (s₁ + 1)))).AncestorEq X ∧
              X ∈ (x.tickInput w (M.voteTime S.C (s₁ + 1))).tree ∧
              ¬ ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s₁ + 1)))
                  (S.C.t_ ((s₁ + 1) - 1) + 3 * S.C.Δ) (s₁ + 1) W ∧
                W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s₁ + 1)))).viable_heads ∧
                X.AncestorEq W) ∨
            FinalizedIncompatibleAtTick M S A x w (M.supportCutoff S.C (s₁ + 2)) X)) ∨
        (s₁ = s' ∧ ∀ D : Block V,
          ((∃ u ∈ Hon s', ∃ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
              M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
                ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
            ∃ v ∈ Hon s',
              (x.tickOutput v (M.supportCutoff S.C s')).savedConfirmation (s' - 1) = some D)
                  →
          RootOffChainAtTick M S A x w (M.voteTime S.C (s' + 1)) D)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.frontWindowStable_fail_event M F U) S A x R GST
    tGAT tAwakeEnd s_w s' Hon E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hs' hHonMono hHon hAwake
    hsw hEnd hFail

/-- **A1, an honest attestation is built from a fast block of its sender's update.** When `v`,
awake and honest at the action time `aR M S r` of round `r`, put the attestation `a` on the wire at
its tick then, the confirmation update of slot `r * R + 1`, on `v`'s tick input at `aR M S r` with
its expired lock entries removed, can leave some node state `n'` (`ConfirmationUpdated`); and some
fast block `L` of `n'`, held in that tick input, has `a`'s height as its chain-state height.

Why: the tick's attestation is the duty's (Lemma 49); the duty's source is the deepest fast block
of the tick's final AC state in the viable tree (`ac_to_fg`), and that AC state's fast blocks are
the update's answer's (Lemma 15); `fg_attest` sets the height to the source's chain-state height;
the source is a block of the frame's tree, held before the tick.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `v`: the attester;
  `a`: the attestation.

The landed statement names the answer of `v`'s update; the twin names a node state `n'` that update
can leave (`ConfirmationUpdated`), as Lemma 36b's twin reads it.

Read aloud: whoever attests at height `h` has just fast-confirmed a block of height `h`.

 -/
theorem fast_block_of_honest_attestation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (r : ℕ) (v : V) (a : Attestation V)
    -- `v`, awake and honest at the action time of round `r`, sent `a` at its tick then
    (hSend : HonestAttestationAt M S A x (aR M S r) v a) :
    ∃ (n' : M.N) (L : Block V),
      ConfirmationUpdated M S.C S.P (x.tickInput v (aR M S r)) ((aR M S r : ℕ) : Int)
        (r * S.C.R + 1) n' ∧
      L ∈ n'.fastBlocks ∧ L ∈ (x.tickInput v (aR M S r)).tree ∧
      (M.chainStateOf S.C L).h = a.h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fast_block_of_honest_attestation M F U) S A x R E
    r v a hSend

/-- **A2, before `a_r` every honest-held block has height at most `H₂ + 1`.** Under
unforgeability, with fewer than a third of the validators in the adversary set up to `tAwakeEnd`:
when step `k₀` is at a time at most `tAwakeEnd` and every attestation put
on the wire by a tick at a step before `k₀`, by a validator outside the adversary set at
`tAwakeEnd`, has height at most `H₂`, then every block `w` holds at a step `i ≤ k₀` has chain-state
height at most `H₂ + 1`.

Why: `attested_height_bound_before` at the step `i`, whose time is at most the time of `k₀`, so at
most `tAwakeEnd`; every tick at a step before `i` is at a step before `k₀`, so `hOld` bounds its
honest attestations.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end;
- `H₂`: the bound on the old attestations; `k₀`: a step before which every honest attestation has
  height at most `H₂`; `i`: the step read; `w`: the holder; `D`: the block.

Read aloud: nothing climbs past `H₂ + 1` up to step `k₀`.

 -/
theorem held_height_le_before_action (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (tAwakeEnd H₂ k₀ i : ℕ) (w : V) (D : Block V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    -- every attestation put on the wire by a tick at a step before `k₀`, by a validator outside the
    -- adversary set at `tAwakeEnd`, has height at most `H₂`
    (hOld : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : x.time k₀ ≤ tAwakeEnd)
    (hi : i ≤ k₀) (hD : D ∈ (x.st i w).tree) :
    (M.chainStateOf S.C D).h ≤ H₂ + 1 :=
  (GoldilocksCorrectness.Record.Proofs.Executions.held_height_le_before_action M F Fx) S A x R E
    tAwakeEnd H₂ k₀ i w D hThird hOld hEnd hi hD

/-- **A3, before `a_r` every honest finalized block is `L` or an ancestor of `L`.** Under
unforgeability, roots naming blocks, permanent corruption and fewer than a third of the validators
in the adversary set up to `tAwakeEnd`: when step `k₀` is `v`'s tick to `aR M S r`, at a time at
most `tAwakeEnd`; every attestation put on the wire by a tick at a step before `k₀`, by a validator
outside the adversary set at `tAwakeEnd`, has height at most `H₂`; `v` holds `L` in its tick input to
`aR M S r`, with `L`'s chain-state height `H₂ + 1`; and `w` is honest at a step `i ≤ k₀` — then `w`'s
finalized block at step `i` is `L` or an ancestor of `L`.

Why: `w`'s finalized block is the finalized block of the chain state of a held block `D`
(`finalizedFromChain_of_exec`), at a height `h_F(D) ≤ h_j(D) < h(D) ≤ H₂ + 1` (Lemma 47 (a), A2),
so `h_F(D) < h(L)`, and Lemma 89a with `v` holding `L` gives `F ⪯ L`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end;
- `r`: the round; `H₂`: the bound on the old attestations; `k₀`: the step of `v`'s tick to
  `aR M S r`; `i`: the step read; `v`: the holder of `L`; `w`: the validator whose finalized block
  is read; `L`: the block.

Roots name blocks until a time `tR` at least the time of step `k₀`: the proof compares (Lemma 89a)
the block `B` `w` holds at step `i` with `L`, which `v` holds at step `k₀`, and `i ≤ k₀`.

Read aloud: no honest validator has finalized anything the fast block does not extend.

 -/
theorem finalized_ancestor_of_fast_block (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tAwakeEnd r H₂ k₀ i : ℕ) (v w : V) (L : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR) (htR : x.time k₀ ≤ tR)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    -- step `k₀` is `v`'s tick to the action time of round `r`
    (hk₀ : x.lbl k₀ = Event.tick v (aR M S r))
    -- every attestation put on the wire by a tick at a step before `k₀`, by a validator outside the
    -- adversary set at `tAwakeEnd`, has height at most `H₂`
    (hOld : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : x.time k₀ ≤ tAwakeEnd)
    (hLv : L ∈ (x.tickInput v (aR M S r)).tree)
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hi : i ≤ k₀) (hw : w ∉ A.corrupted i) :
    (x.st i w).finalized.AncestorEq L :=
  (GoldilocksCorrectness.Record.Proofs.Executions.finalized_ancestor_of_fast_block M F Fx) S A x R
    tAwakeEnd r H₂ k₀ i v w L E hRoots htR hThird hk₀ hOld hEnd hLv hL hi hw

/-- **A4, a confirmed block's ancestor is extended by the next slot's honest votes, the held
form.** Lemma 36b's hypotheses (`lem36b_confirmed_block_extended_held`), with the frame and lock
conditions at `w` read against a block `L` that is `C'` or an ancestor of `C'`, in place of `C'`
itself: then `w`'s vote at the vote time of slot `s + 1` is its slot-`(s + 1)` vote for a block
`H_w` it holds then, and `H_w` is `L` or a descendant of `L`.

Why: Lemma 36 at `L` (`C'` or an ancestor of the saved `C'`) gives the set `Sup` of early
supporters of `L` at `v` with `v`'s late voters fewer than twice `Sup`; then Lemma 21 in the held
form at `L`, as Lemma 36b's proof calls it at `C'`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose confirmation `v`'s update of slot `s + 1` saves;
- `C'`: the saved confirmation; `L`: `C'` or an ancestor of it; `v`: the validator whose update
  saves `C'`; `w`: the voter of slot `s + 1`; `tStartW`: the start of `w`'s window; `n'`: a node state
  `v`'s update can leave (`ConfirmationUpdated`); `vote`: `w`'s Goldfish
  vote.

The holders `v` (`hv₀`) and `w` (`hw₀`) stay active for the sync delay after the sync fact's read
times; `hw₀` is the one Lemma 21b reads through Lemma 64 (T-RC8-2's application, as
Lemma 42 takes it).

Roots name blocks until `M.supportCutoff S.C (s + 1)`: the proof reads Lemma 21 in the held form at
slot `s`, whose bound is that time.

The landed statement names the answer of `v`'s update of slot `s + 1`; the twin names a node state
`n'` that update can leave (`ConfirmationUpdated`), as Lemma 36b's twin reads it.

Read aloud: the next slot's honest votes extend every ancestor of a confirmation whose frame and
lock conditions hold at the voter.

 -/
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
    -- `v`'s window starts at `tStart`, strictly before one delay or one sync delay, whichever is
    -- longer, before the support cutoff of slot `s + 1`, and by more than `ΔClockAhead + ΔClockBehind`
    --
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
    -- `L` is `C'` or an ancestor of `C'`
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
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ L.AncestorEq H_w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem36c_fast_ancestor_extended_held M F U) S A
    x R GST s C' L v w n' vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST tStart htStart hv hv₀
    tStartW htStartW hw hw₀ hUpdate hSaved hLC hF2 hF3 hLocks hSend

/-- **A5, the slot invariant restricted to `L` at slot `r * R + 1`.** Under the eight execution
assumptions and unforgeability, with `GST ≤ tGAT`, fewer than a third of the validators in the
adversary set up to `tAwakeEnd`, every honest validator awake from `tGAT` to `tAwakeEnd`, committee
sleepiness from `anchorCW S tGAT` and slot `r * R + 1` starting at or after it, and
`M.supportCutoff S.C (r * R + 2) ≤ tAwakeEnd`: when every honest attestation sent before `aR M S r`
has height at most `H₂`; `v` is honest at `aR M S r`; `v`'s update of slot `r * R + 1` at `aR M S r`
has an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'`; and `L`'s
chain-state height is `H₂ + 1` — then
`HonestChainExtends M S Sched x (Hon M S Sched (r * R + 1)) L (r * R + 1)`: every slot-`(r * R + 1)`
vote of a member of `Hon M S Sched (r * R + 1)` is for a block it holds that is `L` or a descendant
of `L`, every lock entry a member's revocation of slot `r * R + 2` leaves live is compatible with
`L`, and every confirmation of slot `r * R + 1` a member saves is `L` or a descendant of `L`.

Why: `L` is an ancestor of `v`'s saved confirmation of slot `r * R`, so Lemma 36 gives its early
supporters at `v`. At every member: its finalized block before the vote time of slot `r * R + 1`
is an ancestor of `L` (A3); `L` reaches it before the view freeze of slot `r * R` with an early
supporter's vote (Lemma 63); its greatest chain-state height is then `H₂ + 1` (A2), so its
fork-choice root is an ancestor of `L` (the contest rule) and `L` is a viable head of its voter
tree; Lemma 42 makes its locks compatible with `L`; A4 gives the vote. The live locks of slot
`r * R + 1` come from older entries (Lemma 42) or from the member's confirmation of slot `r * R`,
compatible with `v`'s (Lemma 31). The confirmations: Lemma 79c with the honest committee voters of
slot `r * R + 1`, every member's finalized block being compatible with `L` (Lemma 89a at heights at
most `H₂`; above `H₂` an entry of the honest chain at slot `r * R`, `cert_entry_at_slot` and Lemma
31).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the
  bound on the old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast
  block; `n'`, `sent`: an outcome of `v`'s tick at the action time of round `r`.

Roots name blocks until `M.supportCutoff S.C (r * S.C.R + 2)`: `finalized_compatible_fast_block` at
the support cutoff of slot `r * R + 2`, for the confirmations of slot `r * R + 1`; the other
steps read up to the support cutoff of slot `r * R + 1`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input) (template A2),
without A2's hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`:
`hAwake` and `hv` give it.

Read aloud: the slot after the fast block's round, every honest vote, live lock and confirmation
extends the fast block.

 -/
theorem fast_block_base (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (r * S.C.R + 2)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `r * R + 2`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hEnd : M.supportCutoff S.C (r * S.C.R + 2) ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `r * R + 2` is at a real time at most `tAwakeEnd`
    --
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (r * S.C.R + 2) →
      x.time k ≤ tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    HonestChainExtends M S A x (Hon M S A x (r * S.C.R + 1)) L (r * S.C.R + 1) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fast_block_base M F U Fx) S A x R GST tGAT
    tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive
    hCommittees hAnchor hEnd hEndTick hOld hv n' sent hUpdate hFast hL

/-- **B1, the threshold exists.** In an execution that reaches every time, for every time `T₁`
there is an `H₂` with `OldHeightAttained M S Sched x T₁ H₂`: every attestation an honest awake
validator put on the wire at a tick before `T₁` has height at most `H₂`, and `H₂` is `0` or the
height of such an attestation.

Why: the attestations put on the wire at ticks before `T₁` are in the finite sent log of the
configuration `x[stepBefore M x T₁]`; `H₂` is the least bound on the heights of the honest ones.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `T₁`: the time.

Read aloud: there is a greatest height the honest validators attested before `T₁`.

 -/
theorem exists_old_height_attained (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (T₁ : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) :
    ∃ H₂ : ℕ, OldHeightAttained M S A x T₁ H₂ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.exists_old_height_attained M F) S A x R T₁ E

/-- **B2, the honest greatest chain-state height from `T₁ + Δ` to `a_r`.** Under the execution
assumptions and unforgeability, with `GST ≤ tGAT`, `tGAT + Δs ≤ T₁`, fewer than a third of the validators in the
adversary set up to `tAwakeEnd`, and every honest validator awake through the phase: when `H₂` is
the threshold at `T₁` (`OldHeightAttained`), step `k₀` is `v`'s tick to `aR M S r` at a time at most
`tAwakeEnd`, every attestation put on the wire by a tick at a step before `k₀` by a validator outside
the adversary set at `tAwakeEnd` has height at most `H₂`, and `w` is honest at a clock value `t` with
`T₁ + Δ ≤ t` whose tick is at a step at most `k₀` — then `w`'s greatest chain-state height in its tick
input at `t` is at least `H₂` and at most `H₂ + 1`.

Why: at least `H₂` by Lemma 89b at the honest attestation of height `H₂` sent before `T₁` (when
`H₂ ≠ 0`); at most `H₂ + 1` because the greatest chain-state height is the chain-state height of a
block `w` holds, which A2 bounds.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `T₁`: the time of the
  threshold; `r`: the round; `H₂`: the threshold; `t`: the clock value; `k₀`: the step of `v`'s
  tick to `aR M S r`; `v`: the attester; `w`: the validator.

Roots name blocks until the real time of `w`'s tick `k` to `t`: the proof reads `lem89b_at` at `b := t`,
at that tick.

Read aloud: once the phase has settled, every honest validator knows the threshold's height and
nothing higher than one more than it, up to the step of the first attestation above it.

 -/
theorem honest_h_max_bounds (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ t k₀ : ℕ) (v w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    -- step `k₀` is `v`'s tick to the action time of round `r`
    (hk₀ : x.lbl k₀ = Event.tick v (aR M S r))
    -- every attestation put on the wire by a tick at a step before `k₀`, by a validator outside the
    -- adversary set at `tAwakeEnd`, has height at most `H₂`
    (hOld : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : x.time k₀ ≤ tAwakeEnd)
    (ht₁ : T₁ + Δ S ≤ t) (k : ℕ) (hk : x.lbl k = Event.tick w t)
    (hRoots : RootsNameBlocksUntil M A x (x.time k)) (htr : k ≤ k₀)
    (hw : w ∉ A.corrupted k)
    -- `w` ticked to the threshold time `T₁`
    (hwt : ∃ k' : ℕ, x.lbl k' = Event.tick w T₁) :
    H₂ ≤ hMax M S.C (x.tickInput w t) ∧ hMax M S.C (x.tickInput w t) ≤ H₂ + 1 :=
  (GoldilocksCorrectness.Record.Proofs.Executions.honest_h_max_bounds M F U Fx) S A x R GST tGAT
    tAwakeEnd T₁ r H₂ t k₀ v w E hNet hSkew hRedeliver Sy hΔs hParent hGST hT₁s hThird hAwake hH₂
    hk₀ hOld hEnd ht₁ k hk hRoots htr hw hwt

/-- **B3, the first honest attestation above `H₂`.** When `H₂` is the threshold at `T₁` and some
validator put an attestation of height greater than `H₂` on the wire at its tick to a time `t₀ ≥ T₁`
and is outside the adversary set after every step whose time is `t₀`, then there is a round `r`
with `T₁ ≤ aR M S r ≤ t₀`, an attestation above `H₂` that a validator put on the wire at its tick to
`aR M S r` and that validator outside the adversary set after every step whose time is `aR M S r`,
every honest attestation sent at a tick before `aR M S r` of height at most `H₂`, and a step `k₀`,
that validator's tick to `aR M S r` at which it put that attestation on the wire, such that every
attestation put on the wire by a tick at a step before `k₀`, by a validator outside the adversary set
at `tAwakeEnd ≥ t₀`, has height at most `H₂`.

Why: an attestation is sent only at the action time of a round (Lemma 49); take the least step
whose tick, to a clock value from `T₁` to `t₀`, puts an attestation above `H₂` on the wire by a
validator outside the adversary set at that clock value; before `T₁`, `OldHeightAttained` bounds the
heights; from `T₁` on, the minimality does: a tick to a later round's action time at a step before
`k₀`, or a tick to an earlier round's action time at a step after `k₀`, would put two ticks more
than both clock bounds apart in the wrong order (`hSkew`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `T₁`: the time of the threshold;
  `H₂`: the threshold; `t₀`: the time of the given attestation; `tAwakeEnd`: the honesty time of
  the step form; `u`: its sender; `a₀`: the attestation.

Read aloud: the first step at which a validator honest through its clock value attests above the
threshold is a tick to a round's action time, and before it nothing honest was above the threshold.

 -/
theorem first_attestation_above_bound (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (T₁ H₂ t₀ tAwakeEnd : ℕ) (u : V) (a₀ : Attestation V)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (ht₀ : T₁ ≤ t₀) (hEnd : t₀ ≤ tAwakeEnd)
    (hSend : HonestAttestationAt M S A x t₀ u a₀ ∧ u ∉ A.corruptedAtTime x t₀) (ha₀ : H₂ < a₀.h) :
    ∃ r : ℕ, T₁ ≤ aR M S r ∧ aR M S r ≤ t₀ ∧ OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂ ∧
      ∃ (v : V) (a : Attestation V), HonestAttestationAt M S A x (aR M S r) v a ∧
        v ∉ A.corruptedAtTime x (aR M S r) ∧ H₂ < a.h ∧
        ∃ k₀ : ℕ, x.lbl k₀ = Event.tick v (aR M S r) ∧
          (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k₀ + 1) - x.sent k₀ ∧
          ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
            u ∉ A.corruptedAtTime x tAwakeEnd →
            (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.first_attestation_above_bound M F U) S A x R E hSkew
    T₁ H₂ t₀ tAwakeEnd u a₀ hH₂ ht₀ hEnd hSend ha₀

/-- **B4, the fast block at the first round above the threshold.** Under unforgeability and fewer
than a third of the validators in the adversary set up to `tAwakeEnd`: when `v` put an attestation
`a` of height greater than `H₂` on the wire at its tick to `aR M S r`, the step `k₀`, at a time at most
`tAwakeEnd`, and every attestation put on the wire by a tick at a step before `k₀`, by a validator
outside the adversary set at `tAwakeEnd`, has height at most `H₂`, then `v`'s update of slot
`r * R + 1` at `aR M S r` can leave some node state `n'` (`ConfirmationUpdated`), and some fast block
`L` of `n'`, held in `v`'s tick input to `aR M S r`, has chain-state height exactly `H₂ + 1`.

Why: A1 gives the fast block `L` with `h(L) = a.h > H₂`; `attested_height_bound_before` at the step
`k₀` bounds `h(L) ≤ H₂ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end; `r`:
  the round; `H₂`: the bound on the old attestations; `k₀`: the step of `v`'s tick; `v`: the
  attester; `a`: the attestation.

The landed statement names the answer of `v`'s update; the twin names a node state `n'` that update
can leave (`ConfirmationUpdated`), as Lemma 36b's twin reads it.

Read aloud: the first honest validator above the threshold has just fast-confirmed a block exactly
one height above it.

 -/
theorem fast_block_at_first_round (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (tAwakeEnd r H₂ k₀ : ℕ) (v : V) (a : Attestation V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    -- step `k₀` is `v`'s tick to the action time of round `r`, which put `a` on the wire
    (hk₀ : x.lbl k₀ = Event.tick v (aR M S r))
    (hSend : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k₀ + 1) - x.sent k₀)
    -- every attestation put on the wire by a tick at a step before `k₀`, by a validator outside the
    -- adversary set at `tAwakeEnd`, has height at most `H₂`
    (hOld : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : x.time k₀ ≤ tAwakeEnd) (ha : H₂ < a.h) :
    ∃ (n' : M.N) (L : Block V),
      ConfirmationUpdated M S.C S.P (x.tickInput v (aR M S r)) ((aR M S r : ℕ) : Int)
        (r * S.C.R + 1) n' ∧
      L ∈ n'.fastBlocks ∧ L ∈ (x.tickInput v (aR M S r)).tree ∧
      (M.chainStateOf S.C L).h = H₂ + 1 :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fast_block_at_first_round M F U Fx) S A x R E
    tAwakeEnd r H₂ k₀ v a hThird hk₀ hSend hOld hEnd ha

/-! ## Part A on the revised skeleton: A6 to A8d and the assembly -/

/-- **A6, a certificate at a height greater than `H₂` names an entry of the honest chain from slot
`r * R`.** Under unforgeability, permanent corruption and fewer than a third of the validators in
the adversary set up to `tAwakeEnd`: when every honest attestation sent before `aR M S r` has height
at most `H₂`, the step `j` is at a time at most `tAwakeEnd`, `w` holds `B` after `j` steps, and
`B`'s chain carries a progress certificate at a height `h > H₂` naming `T`'s root, then `T`'s root
is the root of an entry block of the honest chain from slot `r * R` at the height `h`.

Why: Lemma 83 with `s₀ := r * R` and `t₀ := aR M S r`; its `hAgree` is Lemma 82 at `s₀ := r * R`;
its `hAdvQ` from `hThird` through `fewerThanQuorum_of_fewerThanThird`; its `hOld` in the honest-at
form from the landed form.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end; `r`: the
  round; `H₂`: the bound on the old attestations; `j`: the step; `w`: the holder; `B`: the held
  block; `T`: the block the certificate names; `h`: its height.

Read aloud: once the fast block's round has acted, every certificate at a height greater than the
old evidence is honest and on the chain the fast block started.

 -/
theorem certificate_on_fast_line (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tAwakeEnd r H₂ j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hj : x.time j ≤ tAwakeEnd)
    -- the round's action time is at most the phase's end
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hB : B ∈ (x.st j w).tree) (hJ : ProgressCertOn M B h T) (hH : H₂ < h) :
    ∃ E : Block V, OnHonestChain M S A x (r * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.certificate_on_fast_line M F U Fx) S A x R
    tAwakeEnd r H₂ j w B T h E hThird hOld hj hEnd hB hJ hH

/-- **A7a, the frame of an honest validator relative to the fast block.** A5's hypotheses (the
execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick there, with `L`
among the fast blocks of `n'`, `h(L) = H₂ + 1`); a slot `s ≥ r * R + 1`; a time `t` from the vote
time of slot `s + 1` to the support cutoff of slot `s + 2`, inside the phase; and `w` honest at `t`
— then the root of `w`'s fork choice before `t` is compatible with `L`; when that root is `L` or an
ancestor of `L`, some viable head of `w`'s frame is `L` or a descendant of `L`; and `w`'s finalized
block before `t` is compatible with `L`.

The skeleton's hypothesis `hInvL` (the slot invariant relative to `L` at every slot from `r * R + 1`
to `s`) is not a hypothesis: the proof does not read it, A5's hypotheses giving the whole invariant.

Why: the line invariant of `Proofs/Executions/Lemma89FastFamily.lean` (`PartAHyps.lineInv_all`): at
every slot of the phase, every honest vote, live lock and confirmation extends every line source of
an earlier slot `μ` (an ancestor of, or equal to, a block of a member's confirmation of slot `μ`
that is: fast at the height `H₂ + 1` when `μ = r * R`; fast or passing the slow test when
`μ ≥ r * R + 1`; any block when `μ ≥ r * R + k`). At heights at most `H₂` the root and the finalized
block are ancestors of `L` (Lemma 89a, the contest rule); at greater heights they are the entry of a
fast block of an honest attester's update at the action time of a round `r' ≥ r` (A1, Lemma 66), a
line source; a viable head is `L`, or the entry at the greatest chain-state height minus one, the
state not being contested.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`: the slot; `t`: the reading time; `w`: the reader.

Roots name blocks until `M.supportCutoff S.C (s + 2)`: the bundle `PartAHyps` is built with its end
time `M.supportCutoff S.C (s + 2)`, the latest time its kit reads here.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: after the fast block's round, every honest validator's finality gadget lets it follow
the fast block.

 -/
theorem frame_at_time_relative_to_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s t : ℕ) (v w : V)
      (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 2)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    -- the reading time, from the vote time of slot `s + 1` to the update of slot `s + 1`
    (hs : r * S.C.R + 1 ≤ s) (hts : M.voteTime S.C (s + 1) ≤ t)
    (ht : t ≤ M.supportCutoff S.C (s + 2)) (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hw : w ∉ A.corruptedAtTime x t) :
    (M.fg_to_ac (x.stateBefore t w)).fc_root.compatible L = true ∧
    ((M.fg_to_ac (x.stateBefore t w)).fc_root.AncestorEq L →
      ∃ W ∈ (M.fg_to_ac (x.stateBefore t w)).tree,
        W ∈ (M.fg_to_ac (x.stateBefore t w)).viable_heads ∧ L.AncestorEq W) ∧
    (x.stateBefore t w).finalized.compatible L = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.frame_at_time_relative_to_fast_block M F U Fx) S
    A x R GST tGAT tAwakeEnd r H₂ s t v w L E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST
    hThird hAwake hActive hCommittees hAnchor hOld hv n' sent hUpdate hFast hL hs hts ht hEnd hw

/-- **A7b, the chain step's frame conditions relative to the fast block.** A5's hypotheses (the
execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick there, with `L`
among the fast blocks of `n'`, `h(L) = H₂ + 1`); a slot `s ≥ r * R + 1` whose support cutoff of slot
`s + 2` is at most `tAwakeEnd` — then every member `w` of `Hon M S Sched (s + 1)` satisfies
`StepFrameAt M S Sched x L s w`.

The skeleton's hypothesis `hInvL` is not a hypothesis: the proof does not read it.

Why: A7a's argument at the vote time of slot `s + 1` and at the support cutoff of slot `s + 2`; the
viable head is held before the view freeze of slot `s`, so it is in the voter tree of slot `s + 1`
(`proposal_viable_head_at`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`: the slot of the step.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` is built with its end time `tAwakeEnd`; the
third conjunct of `StepFrameAt` is read at each member's tick to the support cutoff of slot `s + 2`,
which `hEndTick` places at a real time at most `tAwakeEnd`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: every member's vote and update of the next slot can follow the fast block.

 -/
theorem stepFrame_relative_to_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hs : r * S.C.R + 1 ≤ s) (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hEndTick : ∀ (w : V) (k : ℕ), x.lbl k = Event.tick w (M.supportCutoff S.C (s + 2)) →
      x.time k ≤ tAwakeEnd) :
    ∀ w ∈ Hon M S A x (s + 1), StepFrameAt M S A x L s w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.stepFrame_relative_to_fast_block M F U Fx) S A
    x R GST tGAT tAwakeEnd r H₂ s v L E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird
    hAwake hActive hCommittees hAnchor hOld hv n' sent hUpdate hFast hL hs hEnd hEndTick

/-- **A8a, the slot invariant relative to `L` at every slot of the phase from `r * R + 1`.** A5's
hypotheses (the execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at
`a_r`, `v`'s update of slot `r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick
there, with `L` among the fast blocks of `n'`, `h(L) = H₂ + 1`) — then at every slot `s ≥ r * R + 1`
whose support cutoff of slot `s + 2` is at most `tAwakeEnd`,
`HonestChainExtends M S Sched x (Hon M S Sched s) L s`.

Why: the line invariant of `Proofs/Executions/Lemma89FastFamily.lean` (`PartAHyps.lineInv_all`): at
every slot of the phase, every honest vote, live lock and confirmation extends every line source of
an earlier slot `μ` (an ancestor of, or equal to, a block of a member's confirmation of slot `μ`
that is: fast at the height `H₂ + 1` when `μ = r * R`; fast or passing the slow test when
`μ ≥ r * R + 1`; any block when `μ ≥ r * R + k`), at the line source `L`; its base at slot
`r * R + 1` is A5.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`: the slot.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: from the slot after the fast block's round to the end of the phase, every honest vote,
live lock and confirmation extends the fast block.

 -/
theorem fast_line_invariant_L (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    ∀ s : ℕ, r * S.C.R + 1 ≤ s → M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      HonestChainExtends M S A x (Hon M S A x s) L s :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fast_line_invariant_L M F U Fx) S A x R GST tGAT
    tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv n' sent hUpdate hFast hL

/-- **A8d, every later honest fast block is extended by everything after its round.** A5's
hypotheses (the execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at
`a_r`, `v`'s update of slot `r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick
there, with `L` among the fast blocks of `n'`, `h(L) = H₂ + 1`) for `r`, `v`, `L`, `n'`, `sent`; a
round `r' ≥ r`; a validator `u` honest at `aR M S r'` whose update of slot `r' * R + 1` at
`aR M S r'` is read as an outcome `(n_u, sent_u)` of `u`'s tick there, with `X` among the fast
blocks of `n_u` — then at every slot `σ ≥ r' * R + 1` whose support cutoff of slot `σ + 2` is at
most `tAwakeEnd`, `HonestChainExtends M S Sched x (Hon M S Sched σ) X σ`.

Why: `X` is a line source of slot `r' * R` (`source_later`: a fast block of slot `r' * R` for
`r' > r`; for `r' = r`, at the height `H₂ + 1`, or an ancestor of `L`, A2 bounding its height by
`H₂ + 1`), and the line invariant of `Proofs/Executions/Lemma89FastFamily.lean`
(`PartAHyps.lineInv_all`): at every slot of the phase, every honest vote, live lock and confirmation
extends every line source of an earlier slot `μ` (an ancestor of, or equal to, a block of a member's
confirmation of slot `μ` that is: fast at the height `H₂ + 1` when `μ = r * R`; fast or passing the
slow test when `μ ≥ r * R + 1`; any block when `μ ≥ r * R + k`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `r'`: the later round; `u`: the validator whose update makes `X` fast; `X`: the fast block; `n_u`,
  `sent_u`: an outcome of `u`'s tick at the action time of round `r'`.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`; the later round's update of `u` is read in the same way, as an outcome
`(n_u, sent_u)` of `u`'s tick at the action time of round `r'`.

Read aloud: once an honest validator fast-confirms a block at a round's action time after the fast
block's round, every later honest vote, live lock and confirmation of the phase extends it.

 -/
theorem fast_line_at_later_round (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ r' : ℕ) (v u : V)
      (L X : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    -- a later round's honest fast block
    (hr' : r ≤ r') (hu : u ∉ A.corruptedAtTime x (aR M S r'))
    (n_u : M.N) (sent_u : List (NamedObject V))
    (hUpdate_u : .ok (n_u, sent_u) ∈ M.tick S.C S.P S.X (x.tickInput u (aR M S r'))
        ((aR M S r' : ℕ) : Int))
    (hFast_u : X ∈ M.fastBlocks n_u) :
    ∀ σ : ℕ, r' * S.C.R + 1 ≤ σ → M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd →
      HonestChainExtends M S A x (Hon M S A x σ) X σ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fast_line_at_later_round M F U Fx) S A x R GST
    tGAT tAwakeEnd r H₂ r' v u L X E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird
    hAwake hActive hCommittees hAnchor hOld hv n' sent hUpdate hFast hL hr' hu n_u sent_u hUpdate_u hFast_u

/-- **A8c, the members' confirmations form one chain from slot `r * R + k` on.** A5's hypotheses
(the execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick there, with `L`
among the fast blocks of `n'`, `h(L) = H₂ + 1`) — then for every slot `s` whose support cutoff of
slot `s + 2` is at most `tAwakeEnd`,
`ConfirmationsChainOn M S Sched x (roundMembers M S Sched) (r * R + k) s`: a confirmation a member
saved for a slot `σ` from `r * R + k` to `s` is an ancestor of, or equal to, one a member saved for
a later slot of that range, and compatible with one of the same slot.

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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`: the last slot of the range.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: once every lock made before the fast block's round has expired, the honest chain does
not switch again.

 -/
theorem confirmations_chain_after_old_locks (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    ∀ s : ℕ, M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      ConfirmationsChainOn M S A x (roundMembers M S A x) (r * S.C.R + S.C.k) s :=
  (GoldilocksCorrectness.Record.Proofs.Executions.confirmations_chain_after_old_locks M F U Fx) S
    A x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird
    hAwake hActive hCommittees hAnchor hOld hv n' sent hUpdate hFast hL

/-- **A7c, the frame of an honest validator relative to the late family.** A5's hypotheses (the
execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick there, with `L`
among the fast blocks of `n'`, `h(L) = H₂ + 1`); a slot `s ≥ r * R + k`; a time `t` from the vote
time of slot `s + 1` to the support cutoff of slot `s + 2`, inside the phase; and `w` honest at `t`
— then for every block `C` of `FastFamilyFrom M S Sched x (r * R + k) L (s + 1)` (`L`'s ancestors
and the members' confirmations of the slots `r * R + k` to `s`, with their ancestors): the root of
`w`'s fork choice before `t` is compatible with `C`; when that root is `C` or an ancestor of `C`,
some viable head of `w`'s frame is `C` or a descendant of `C`; and `w`'s finalized block before `t`
is compatible with `C`.

The skeleton's hypotheses `hInvL` (the slot invariant relative to `L` up to slot `s`) and `hChainF`
(A8c's conclusion up to slot `s`) are not hypotheses: the proof does not read them.

Why: every block of the family is a line source of a slot at most `s` (`family_source`), and A7a's
argument holds at every line source (`frame_source_at`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`: the slot; `t`: the reading time; `w`: the reader.

Roots name blocks until `M.supportCutoff S.C (s + 2)`: the bundle `PartAHyps` is built with its end
time `M.supportCutoff S.C (s + 2)`, the latest time its kit reads here.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: once the old locks have expired, every honest validator's finality gadget lets it follow
every block the honest chain has confirmed since.

 -/
theorem frame_at_time_relative_to_late_family (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s t : ℕ) (v w : V)
      (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 2)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hs : r * S.C.R + S.C.k ≤ s) (hts : M.voteTime S.C (s + 1) ≤ t)
    (ht : t ≤ M.supportCutoff S.C (s + 2)) (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hw : w ∉ A.corruptedAtTime x t) :
    ∀ C : Block V, FastFamilyFrom M S A x (r * S.C.R + S.C.k) L (s + 1) C →
      (M.fg_to_ac (x.stateBefore t w)).fc_root.compatible C = true ∧
      ((M.fg_to_ac (x.stateBefore t w)).fc_root.AncestorEq C →
        ∃ W ∈ (M.fg_to_ac (x.stateBefore t w)).tree,
          W ∈ (M.fg_to_ac (x.stateBefore t w)).viable_heads ∧ C.AncestorEq W) ∧
      (x.stateBefore t w).finalized.compatible C = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.frame_at_time_relative_to_late_family M F U Fx) S
    A x R GST tGAT tAwakeEnd r H₂ s t v w L E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST
    hThird hAwake hActive hCommittees hAnchor hOld hv n' sent hUpdate hFast hL hs hts ht hEnd hw

/-- **A7d, the chain step's frame conditions relative to the late family.** A5's hypotheses (the
execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s
update of slot `r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick there, with `L`
among the fast blocks of `n'`, `h(L) = H₂ + 1`); a slot `s ≥ r * R + k` whose support cutoff of slot
`s + 2` is at most `tAwakeEnd` — then every member `w` of `Hon M S Sched (s + 1)` satisfies
`StepFrameAt M S Sched x C s w` for every block `C` of
`FastFamilyFrom M S Sched x (r * R + k) L (s + 1)`.

The skeleton's hypotheses `hInvL` and `hChainF` are not hypotheses: the proof does not read them.

Why: every block of the family is a line source of a slot at most `s` (`family_source`), and A7b's
argument holds at every line source (`stepFrame_source`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`: the slot of the step.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` is built with its end time `tAwakeEnd`; the
third conjunct of `StepFrameAt` is read at each member's tick to the support cutoff of slot `s + 2`,
which `hEndTick` places at a real time at most `tAwakeEnd`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: every member's vote and update of the next slot can follow every block the honest chain
has confirmed since the old locks expired.

 -/
theorem stepFrame_relative_to_late_family (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (hs : r * S.C.R + S.C.k ≤ s) (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hEndTick : ∀ (w : V) (k : ℕ), x.lbl k = Event.tick w (M.supportCutoff S.C (s + 2)) →
      x.time k ≤ tAwakeEnd) :
    ∀ w ∈ Hon M S A x (s + 1), ∀ C : Block V,
      FastFamilyFrom M S A x (r * S.C.R + S.C.k) L (s + 1) C →
        StepFrameAt M S A x C s w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.stepFrame_relative_to_late_family M F U Fx) S
    A x R GST tGAT tAwakeEnd r H₂ s v L E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST
    hThird hAwake hActive hCommittees hAnchor hOld hv n' sent hUpdate hFast hL hs hEnd hEndTick

/-- **A8b, the chain and lock invariants for the late family.** A5's hypotheses (the execution
assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s update of slot
`r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick there, with `L` among the fast
blocks of `n'`, `h(L) = H₂ + 1`) — then at every slot `s ≥ r * R + 2k − 1` whose support cutoff of
slot `s + 2` is at most `tAwakeEnd`,
`ChainInvFor M S Sched x (Hon M S Sched s) (FastFamilyFrom M S Sched x (r * R + k) L s) s`, and
every member of `Hon M S Sched s` satisfies `LiveLocksOnFamilyAt` for that family at `s`.

Why: every block of the family is a line source of a slot before `s` (`family_source`), and the line
invariant of `Proofs/Executions/Lemma89FastFamily.lean` (`PartAHyps.lineInv_all`): at every slot of
the phase, every honest vote, live lock and confirmation extends every line source of an earlier
slot `μ` (an ancestor of, or equal to, a block of a member's confirmation of slot `μ` that is: fast
at the height `H₂ + 1` when `μ = r * R`; fast or passing the slow test when `μ ≥ r * R + 1`; any
block when `μ ≥ r * R + k`); every lock a member holds live at the vote time of slot `s + 1` is of a
slot at least `s + 1 − k ≥ r * R + k` (Lemma 41), on its holder's confirmation of that slot (Lemma
39), a block of the family (`late_locks_on_family`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`: the slot.

Roots name blocks until `tAwakeEnd`: the bundle `PartAHyps` carries the premise at the phase's
end; the conclusion holds at every slot whose support cutoff of the slot after next is at most
`tAwakeEnd`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: once every lock older than the fast block's round has expired and every live lock is of
a slot after the last switch, the honest chain is one line, every honest vote, live lock and
confirmation on it.

 -/
theorem fast_line_invariant_late_family (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    ∀ s : ℕ, r * S.C.R + 2 * S.C.k - 1 ≤ s → M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      ChainInvFor M S A x (Hon M S A x s)
        (FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s) s ∧
      ∀ u ∈ Hon M S A x s,
        LiveLocksOnFamilyAt M S A x
          (FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s) s u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fast_line_invariant_late_family M F U Fx) S A
    x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird
    hAwake hActive hCommittees hAnchor hOld hv n' sent hUpdate hFast hL

/-- **Part A, one line from the first honest fast block at the height after the old evidence.** A5's
hypotheses (the execution assumptions, unforgeability, the phase's premises, `hOld`, `v` honest at
`a_r`, `v`'s update of slot `r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick
there, with `L` among the fast blocks of `n'`, `h(L) = H₂ + 1`); then: (1) at every slot
`s ≥ r * R + 1` of the phase, every honest vote, live lock and confirmation of the members of slot
`s` extends `L` (A8a); (2) at every slot `s ≥ r * R + 2k − 1` of the phase, the chain and lock
invariants hold for the family of `L`'s ancestors and the members' confirmations from slot
`r * R + k` on (A8b); (3) every progress certificate at a height greater than `H₂` on the chain of a
block an honest validator holds at a step of the phase names an entry of the honest chain from slot
`r * R` (A6).

Why: A8a, A8b and A6.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the round; `H₂`: the bound on the
  old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`.

Roots name blocks until `tAwakeEnd`: the bound of A8a and A8b, whose conclusions hold at every
slot whose support cutoff of the slot after next is at most `tAwakeEnd`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: once one honest validator has fast-confirmed a block one height after everything the
honest validators had attested, no honest validator ever votes, locks or confirms off that block's
chain, the honest chain is one line once the older locks have expired, and every later certificate
is on its line.

 -/
theorem lem89L_one_line_from_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ : ℕ) (v : V) (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hL : (M.chainStateOf S.C L).h = H₂ + 1) :
    (∀ s : ℕ, r * S.C.R + 1 ≤ s → M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      HonestChainExtends M S A x (Hon M S A x s) L s) ∧
    (∀ s : ℕ, r * S.C.R + 2 * S.C.k - 1 ≤ s → M.supportCutoff S.C (s + 2) ≤ tAwakeEnd →
      ChainInvFor M S A x (Hon M S A x s)
        (FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s) s ∧
      ∀ u ∈ Hon M S A x s,
        LiveLocksOnFamilyAt M S A x (FastFamilyFrom M S A x (r * S.C.R + S.C.k) L s) s u) ∧
    (∀ (j : ℕ) (w : V) (B T : Block V) (h : Height), x.time j ≤ tAwakeEnd →
      B ∈ (x.st j w).tree → ProgressCertOn M B h T → H₂ < h →
      ∃ E : Block V, OnHonestChain M S A x (r * S.C.R) E ∧ IsEntry M S.C E ∧
        (M.chainStateOf S.C E).h = h ∧ T.root = E.root) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89L_one_line_from_fast_block M F U Fx) S A
    x R GST tGAT tAwakeEnd r H₂ v L E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird
    hAwake hActive hCommittees hAnchor hOld hEnd hv n' sent hUpdate hFast hL

/-! ## Part B on the recount: the windows -/

omit [RootOrder] in
/-- **Every opening's window starts at or after the committee premise's anchor.** With the sequence
premise `hSeq` (its first opening's slot starting at least `3k + 1` slots after `tGAT`) and a slot
`s` at or after the first opening's, `2k ≤ s` and `anchorCW S tGAT ≤ M.slotStart S.C (s − 2k + 1)`.

Why: `4Δ · s ≥ 4Δ · s_0 ≥ tGAT + 4Δ(3k + 1)`, and `4Δ(3k + 1) = 4Δ(k + 2) + 4Δ(2k − 1)`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`: the setup, the schedule; `rs`: the rounds of the honest round opening slots; `m`: the index of the last
  honest round opening slot; `tGAT`, `tAwakeEnd`: the phase; `s`: the slot.

Read aloud: the front of `3k + 1` slots leaves `2k − 1` slots of window after the anchor's `k + 2`;
the first opening's span of the count is not needed.

Copied from `scratch/goldilocks_healed/probe_fewer_1.lean:81`. -/
theorem window_after_anchor (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (rs : ℕ → ℕ)
    (m tGAT tAwakeEnd s : ℕ)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hs : rs 0 * S.C.R ≤ s) :
    2 * S.C.k ≤ s ∧ anchorCW S tGAT ≤ M.slotStart S.C (s - 2 * S.C.k + 1) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.window_after_anchor M F U) S A x rs m tGAT
    tAwakeEnd s hSeq hs

/-! ## Part B: B5 and B6 -/

/-- **B5 with no fork-choice change in the window: the window's last slot has a confirmation.**
Under the execution assumptions and unforgeability, with every honest validator awake in the phase
`[tGAT, tAwakeEnd]` and fewer than a third of the validators in the adversary set up to its end,
and committee sleepiness from `anchorCW S tGAT`: when the window of the opening at slot `s`
(`k + 1 ≤ s`) starts at or after `anchorCW S tGAT` (`anchorCW S tGAT ≤ M.slotStart S.C (s − k)`),
the support cutoff of slot `s` is at most `aR M S r ≤ tAwakeEnd`, and no step `j` whose real time
is from the vote time of slot `s − k − 1` to before the vote time of slot `s` has a
`ForkChoiceChangeStep` at a validator outside the adversary set at `j` — then some member of `Hon M S Sched (s − 2)` saved a confirmation of slot
`s − 2`.

 Proved in `Proofs/Executions/Lemma89StabilityJ.lean`.

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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `r`: the round of the action time the
  window ends before; `s`: the honest round opening slot.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s - 1)`
: the updater is read at its own tick to that cutoff, at a real time up to `ΔClockBehind`
after it (`member_saves_of_no_change`, `confirmation_saved_of_votes` at slot `s − 2`).

Read aloud: when no honest validator's fork choice changes during the window, an honest member
confirms something at the window's second-to-last slot.

 -/
theorem window_last_confirmation_exists_of_no_change (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r s : ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s - 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hEnd : aR M S r ≤ tAwakeEnd)
    -- the window: `k + 1` slots before `s`, before `a_r`, inside the committee premise
    (hk : S.C.k + 1 ≤ s)
    (hBefore : M.supportCutoff S.C s ≤ aR M S r)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (s - S.C.k))
    -- no validator outside the adversary set has a fork-choice change in the window
    (hNoChange : ∀ (w : V) (j : ℕ), (M.voteTime S.C (s - S.C.k - 1) : ℝ) ≤ x.time j → x.time j < M.voteTime S.C s →
      w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j) :
    ∃ v ∈ Hon M S A x (s - 2), ∃ D : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s - 1))).savedConfirmation (s - 2) = some D :=
  (GoldilocksCorrectness.Record.Proofs.Executions.window_last_confirmation_exists_of_no_change M F U Fx)
    S A x R GST tGAT tAwakeEnd r s E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird
    hAwake hActive hCommittees hEnd hk hBefore hAnchor hNoChange

/-- **B6, the stability fact: a window that is not stable shows a fork-choice change.** Under the
execution assumptions and unforgeability, with every honest validator awake in the phase
`[tGAT, tAwakeEnd]` and fewer than a third of the validators in the adversary set up to its end,
and committee sleepiness from `anchorCW S tGAT`: when the window of the opening at slot `s`
(`k + 1 ≤ s`) starts at or after `anchorCW S tGAT` (`anchorCW S tGAT ≤ M.slotStart S.C (s − k)`),
the support cutoff of slot `s` is at most `aR M S r ≤ tAwakeEnd`, and `FrontWindowStable` fails for
the member sets `Hon M S Sched` from slot `s − 2k` to slot `s − 1` — then some validator `w` has a
`ForkChoiceChangeStep` at a step `j` at which it is outside the adversary set, at or after its own tick
to the vote time of slot `s − k − 1`, and before one of its own ticks to a clock value at most the
support cutoff of slot `s`.

 Proved in `Proofs/Executions/Lemma89StabilityJ.lean`.

 Changed from
the skeleton (`scratch/goldilocks_healed/skeleton_89b/SkeletonPartB.lean`, `stability_fact3`): the
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `r`: the round of the action time the
  window ends before; `s`: the honest round opening slot.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: clause 1 at slot `s − 2` reads a member's finalized block at its own tick to that cutoff, at a real
time up to `ΔClockBehind` after it, and the window's end, the phase's end and the roots all reach that tick (the
bundle `B6Ctx` carries the three in the same form).

Read aloud: before the fast block's round, a window breaks only when some honest validator's root
moves to its justified block, other than an ancestor of its old root, or its `head_height_floor`
rises, at a step from its own tick to the vote time of the window's second slot to before one of its own ticks to a
clock value at most the support cutoff of slot `s`.

 -/
theorem stability_fact3 (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r s : ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hEnd : aR M S r ≤ tAwakeEnd)
    -- the window: `k + 1` slots before `s`, before `a_r`, inside the committee premise
    (hk : S.C.k + 1 ≤ s)
    (hBefore : M.supportCutoff S.C s ≤ aR M S r)
    -- every validator's tick to a clock value at most the support cutoff of slot `s` is in the phase
    (hTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      x.time k ≤ (tAwakeEnd : ℝ))
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (s - S.C.k))
    -- the window is not stable
    (hFail : ¬ FrontWindowStable M S A x (Hon M S A x) (s - 2 * S.C.k) (s - 1)) :
    ∃ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (s - S.C.k - 1)) ∧ k ≤ j ∧
      x.lbl k' = Event.tick w c ∧ c ≤ M.supportCutoff S.C s ∧ j < k' ∧ w ∉ A.corrupted j ∧
      ForkChoiceChangeStep M S A x w j :=
  (GoldilocksCorrectness.Record.Proofs.Executions.stability_fact3 M F U Fx) S A x R GST tGAT
    tAwakeEnd r s E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive hCommittees
    hEnd hk hBefore hTick hAnchor hFail

/-! ## Part B: the climb's count -/

/-- **The four kinds of fork-choice change.** Under the execution assumptions and unforgeability,
with every honest validator awake in the phase `[tGAT, tAwakeEnd]`, fewer than a third of the
validators in the adversary set up to its end, `GST ≤ tGAT`, `tGAT + Δs ≤ T₁`, the threshold `H₂` the greatest
height of an honest attestation sent before `T₁` (`OldHeightAttained`), every honest attestation
sent before `aR M S r ≤ tAwakeEnd` of height at most `H₂`: there are four clock values `τ 0, …, τ 3`
such that every step `j` whose real time is after `T₁ + Δ` and before `aR M S r`, with a
`ForkChoiceChangeStep` at a validator `w` outside the adversary set at `j`, comes, for one `c`, before
`w`'s tick to `τ c + Δ`, with `τ c` at most every natural number that is at least both the step's time and
`w`'s clock value just after the step.

The four kinds, each the first crossing of a level of the FG state: the cache `h_j` reaching
`H₂ − 1` (the root moving to the justified block `J₁` at `H₂ − 1`); `head_height_floor` reaching
`H₂`; `h_j` reaching `H₂` (the root moving to `J₂`); `head_height_floor` reaching `H₂ + 1`. No
fifth kind exists: a finality move is no fork-choice change.

 the window's start strict and its end at `w`'s tick to `τ c + Δ`, because
the receiver of a spread is reached only from its tick to `τ c + Δ` on, and the holder is read at a
step whose time and whose clock value are at most `τ c`); the hypotheses `hOwner` and
`hCommittees` are not read by the proof and are left out.

Why: a fork-choice change at `w` at the step `j` makes one of the four levels fail at `x.st j w` and
hold at `x.st (j + 1) w` (the step is `w`'s own, so `w` stays outside the adversary set and the time
stays; with the greatest chain-state height at `H₂` or `H₂ + 1`, B2 and A2; a root moving to `J`
with greatest chain-state height `h_j + 1` needs `h_j` to rise, Lemma 76 and Lemma 89a). Each level,
once some validator honest at a step whose time is from `T₁` to `τ` and whose clock value is at most `τ`
has it, reaches every honest validator at every step from its tick to `τ + Δ` on:
the block witnessing the cache, or the contesting block and the justified block's witness, are
delivered within one delay. And each level, once reached, stays reached up to `aR M S r` (`h_j` does
not decrease; a contested state stays contested while its greatest chain-state height stays). So the
crossings of a level lie at or after the real time `τ c` of the first step after `T₁` at which some
honest validator has it, and before the crossing validator's tick to any clock value at least
`τ c + ΔClockAhead + Δ`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `T₁`: the time of the threshold; `r`: the
  round of the action time the climb ends at; `H₂`: the threshold.

Roots name blocks until `aR M S r`: every change the conclusion classifies is at a step whose time
is before `aR M S r`, and the levels are read at steps before that time (the bundle `ClimbCtx`). The
changes classified are those of a validator `w` at a step after `w`'s tick to `T₁ + Δ S`. The
real time `τ c` at which the kind of each change starts is greater than `T₁`.

Read aloud: before the fast block's round, the members' roots and `head_height_floor`s change in
at most four bursts, each within one delay.

 -/
theorem fork_choice_change_kinds (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ : ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (k₀ : ℕ)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    -- every attestation put on the wire by a tick at a step before `k₀`, by a validator outside the adversary set at
    -- `tAwakeEnd`, has height at most `H₂`
    (hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : aR M S r ≤ tAwakeEnd) :
    ∃ τ : Fin 4 → ℝ, ∀ (w : V) (j : ℕ), x.lbl (x.tickStep w (T₁ + Δ S)) = Event.tick w (T₁ + Δ S) →
      x.tickStep w (T₁ + Δ S) < j → x.time j < aR M S r →
      j + 1 ≤ k₀ → w ∉ A.corrupted j → ForkChoiceChangeStep M S A x w j →
      ∃ c : Fin 4, τ c ≤ x.time j ∧
        (∀ (k' c' : ℕ), x.lbl k' = Event.tick w c' → τ c + ΔClockAhead + Δ S ≤ c' → j < k') ∧ (T₁ : ℝ) < τ c :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fork_choice_change_kinds M F U Fx) S A x R GST
    tGAT tAwakeEnd T₁ r H₂ E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick hThird hAwake hH₂ k₀ hOld
    hOldStep hEnd

/-- **B10 restated, on a copy: a spoiled opening has a fork-choice change near it, with
its time.** Under the execution assumptions and unforgeability, with every honest validator awake in
the phase `[tGAT, tAwakeEnd]`, fewer than a third of the validators in the adversary set up to its
end, committee sleepiness from `anchorCW S tGAT`, the honest round opening slots of the rounds `rs 0 < … < rs m`
(`HonestOpeningSeq`), `aR M S r ≤ tAwakeEnd`, an opening `i < m` whose next opening's first slot is
at most `r * R`, and no opening's proposal colliding with a block its proposer held: when opening
`i` is spoiled (`Spoiled`), some validator `w` has a `ForkChoiceChangeStep` at a step `j` at which it
is outside the adversary set, at or after its own tick to the vote time of slot `rs i * R − k − 1`
, with `j` before one of `w`'s own ticks to a clock value at most the support cutoff of slot `rs (i + 1) * R`.

 The count of the climb is
  unchanged: a change of a kind starting at `t_K`, at a time at least `t_K` and before that support cutoff, has
  its slot at most `rs (i + 1) * R`;
- the hypothesis `hNoCol` (no opening's proposal collides with a block its proposer held): in a
  collision, the proposal may be held by no honest validator, and the round fails its third
  clause with no fork-choice change; the climb concludes the collision as a disjunct
 and supplies `hNoCol` after splitting on it, as for `quiet_rising_heights_differ`;

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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `r`: the round of the action time the
  climb ends at; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `ΔClockBehind` after `M.supportCutoff S.C (rs (i + 1) * S.C.R)`: the end of the range the context
`QuietCtx` reads, the support cutoff of the next honest round opening slot's first slot.

Read aloud: a spoiled honest round opening slot before the fast block's round has a member's
fork-choice change in its window or in its round, up to the support cutoff of the next opening's
first slot.

 -/
theorem spoiled_near_fork_choice_change_cutoff (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r m i : ℕ) (rs : ℕ → ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until `ΔClockBehind` after the support cutoff of slot `rs (i + 1) * R`, where the members' ticks to it end
    --
    (hRoots : RootsNameBlocksUntil M A x (((M.supportCutoff S.C (rs (i + 1) * S.C.R) : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hir : rs (i + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hSp : Spoiled M S A x rs i) :
    ∃ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) ∧ k ≤ j ∧
      x.lbl k' = Event.tick w c ∧ c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) ∧ j < k' ∧ w ∉ A.corrupted j ∧
      ForkChoiceChangeStep M S A x w j :=
  (GoldilocksCorrectness.Record.Proofs.Executions.spoiled_near_fork_choice_change_cutoff M F U Fx) S
    A x R GST tGAT tAwakeEnd r m i rs E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird
    hAwake hActive hCommittees hEnd hSeq hi hir hNoCol hSp

/-- **B11 restated, on a copy: a quiet opening above the threshold attests above it.** Under the
execution assumptions and unforgeability, with every honest validator awake in the phase
`[tGAT, tAwakeEnd]`, fewer than a third of the validators in the adversary set up to its end,
committee sleepiness from `anchorCW S tGAT`, the honest round opening slots of the rounds `rs 0 < … < rs m`, `aR S r ≤
tAwakeEnd`, an honest round opening slot `i < m`, a slot `s''` at least one round after its
first slot and at most `r * R`, no proposal of an honest round opening slot colliding with a block
its proposer held, and no step, at or after a validator's own tick to the vote time of slot
`rs i * R − k − 1` and before one of that validator's own ticks to a clock value at most the support cutoff of slot `s''`, with a
`ForkChoiceChangeStep` at that validator, outside the adversary set at that step: when the
proposal `B` of slot `rs i * R` has chain-state height greater than `H₂`, some validator honest
and awake at a tick time `t₀ ≤ aR M S (rs i)` put on the wire then an attestation of height greater
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `r`: the round of the action time the
  climb ends at; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `H₂`: the threshold; `s''`: the
  end of the range read; `rs`: the rounds of the honest round opening slots; `B`: the proposal at the honest round opening slot.

Roots name blocks until `ΔClockBehind` after `M.supportCutoff S.C s''`, where the members' ticks to it end: the end of the range the context `QuietCtx`
carries (`quietCtx_of`).

Read aloud: an honest round opening slot with no fork-choice change in its window and in its round up
to slot `s''`, whose proposal is above the threshold, produces an honest attestation above the
threshold by its action time.


-/
theorem quiet_top_gives_attestation_cutoff (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r m i H₂ s'' : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until `ΔClockBehind` after the support cutoff of slot `s''`, where the members' ticks to it end
    (hRoots : RootsNameBlocksUntil M A x (((M.supportCutoff S.C s'' : ℕ) : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hi : i < m) (hsR : rs i * S.C.R + S.C.R ≤ s'') (hir : s'' ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s'' → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hB : ProposalAt M S x (rs i * S.C.R) B) (hBh : H₂ < (M.chainStateOf S.C B).h) :
    ∃ (t₀ : ℕ) (v : V) (a : Attestation V), t₀ ≤ aR M S (rs i) ∧
      HonestAttestationAt M S A x t₀ v a ∧ H₂ < a.h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.quiet_top_gives_attestation_cutoff M F U Fx) S
    A x R GST tGAT tAwakeEnd r m i H₂ s'' rs B E hNet hSkew hRedeliver Sy hΔs hRoots hParent
    hGST hThird hAwake hActive hCommittees hEnd hSeq hi hsR hir hNoCol hNo hB hBh

/-- **`head_height_floor` ordered by delivery, read at both validators' ticks**. The holder `p` ticks to
`cp` at the step `kp`, at a real time at least `a`, and is active from `a` through the sync delay after it; the receiver
`w` ticks to `c`, at least `cp + Δ S`, at the step `kR`, is active at every step from the real time `a` up to that tick,
and ticked earlier to `c₂`, at least the start of the slot of every block `p` holds at its tick and one delay before
`c`; the delivery premises reach `tE`, at least `c`. Then `p`'s `head_height_floor` (the least chain-state height a
viable block may have) at its tick is at most `w`'s at its tick.

Why: every block `p` holds at its tick is delivered to `w` by `w`'s tick to `c₂` and is in `w`'s tree at its tick to
`c`; `p`'s finalized block at its tick is before its block of greatest chain-state height (Lemma 68 at `p` itself); when
`p` is contested, the block that makes it so reaches `w` as well.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from which the network
  is synchronous; `cp`, `kp`: the clock value and the step of `p`'s tick; `a`: the start of the activity windows; `c`,
  `kR`: the clock value and the step of `w`'s tick; `c₂`, `k₂`: those of its earlier tick; `p`, `w`: the holder and the
  receiver.

 the hypothesis
`hF` stays dropped. Roots name blocks until `tR`, at least the real time of `kR`.

Read aloud: a validator that ticks one delay after another's tick, active from one delay or one sync delay before, and
whose clock had already reached the start of every slot of the other's blocks one delay earlier, has a
`head_height_floor` at its tick at least the other's at its tick. -/
theorem floor_le_of_delivery (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST cp kp a c c₂ kR k₂ : ℕ) (p w : V)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a third of the validators have been in the adversary set up to the real time of `kR`
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time kR))
    -- from `a` on, one delay or one sync delay before `c`, the network is synchronous
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ c)
    -- the holder `p`'s tick to `cp`, at a real time at least `a`; `p` active from `a` through the sync delay after it
    (hkp : x.lbl kp = Event.tick p cp) (hak : (a : ℝ) ≤ x.time kp)
    (hv₀ : p ∈ A.activeThroughout x a (a + Δs))
    -- the receiver `w`'s tick to `c`, at least one delay after `cp`, and its window from `a`
    (hkR : x.lbl kR = Event.tick w c) (hcu : cp + Δ S ≤ c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    -- an earlier tick of `w` to `c₂`, one delay before `c`, at least the start of every slot of `p`'s blocks
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.st kp p).tree, M.slotStart S.C Y.slot ≤ c₂)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time kR ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : c ≤ tE) :
    M.head_height_floor (x.st kp p) ≤ M.head_height_floor (x.st kR w) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.floor_le_of_delivery_ticks M F U Fx) S A x R GST cp kp a c c₂ kR k₂ p w
    E hNet hSkew hRedeliver Sy hRoots hParent hAdv hGSTa ha hkp hak hv₀ hkR hcu hwin hk₂ hc₂ hslot htR htE

/-- **C1, the round base at an opening after the fast block (a copy of the skeleton's
`round_base_after_fast_block` with `S.C.R ∣ s`).** A5's hypotheses (the execution assumptions,
unforgeability, the phase's premises, `hOld`, `v` honest at `a_r`, `v`'s update of slot
`r * R + 1` at `a_r` read as an outcome `(n', sent)` of `v`'s tick there, with `L` among the fast
blocks of `n'`, `h(L) = H₂ + 1`); a slot `s` that is a round's first slot (`hsR`), at least `k + 2`
slots after `r * R`, with `M.supportCutoff S.C (s + 2) ≤ tAwakeEnd`, whose proposer is
honest at the support cutoff of slot `s`, and `B` its proposal — then `RoundBaseAt M S Sched x B s`.

The copy's change, against the skeleton
(`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:99`): the hypothesis `hsR : S.C.R ∣ s`
is added. Without it the second clause (each member's root at the support cutoff of slot `s + 1` is
`B` or an ancestor of `B`) reads a justification the attestations of the round whose first slot is
`s − 1` can make before that cutoff, the entry of a block made fast by slot `s − 1`'s update, which
no landed lemma places on `B`'s chain. Every caller reads C1 at an opening, the first slot
`rs j * R` of a round. The skeleton's hypotheses `hLv`, `hInvL` and `hInvF` are deleted: the proof
reads part A's line invariant directly.

Why: the proposal's parent extends every line source of a slot at least two slots before `s`
(`parent_extends_sources`); every member's root before the vote time of slot `s`, and before the
support cutoff of slot `s + 1`, is such a source (the line source of the entry its certificate
names, a round's first slot); every member's `head_height_floor` is at most `h(L)` or the height of
such a source (the entry at the greatest chain-state height minus one, the state not being
contested); every live lock is on a member's confirmation of a slot from `r * R + k` on, a line
source.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the fast block's round; `H₂`: the
  bound on the old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast
  block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`: the honest round opening slot; `B`: its proposal.

Roots name blocks until `M.supportCutoff S.C (s + 2)`: the bundle `PartAHyps` is built with its end
time `M.supportCutoff S.C (s + 2)`, the latest time its kit reads here.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

 Clause 2 is proved by induction on the step of each tick to that
cutoff, with the per-member step `updater_saves_of_finalized_on_proposal` (C3's argument). At both clock bounds `0` and
with `dev`'s reads before the cutoff, `hNoCol` is not needed.

Read aloud: after the fast block's round every honest round opening slot finds the members' frames on its
parent's chain and no lock against it.

 -/
theorem round_base_after_fast_block_opening (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 2)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s)
    (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s B) :
    RoundBaseAt M S A x B s :=
  (GoldilocksCorrectness.Record.Proofs.Executions.round_base_after_fast_block_opening M F U Fx) S
    A x R GST tGAT tAwakeEnd r H₂ s v L B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST
    hThird hAwake hActive hCommittees hAnchor hOld hv hL n' sent hUpdate hFast hs hsR hEnd hp hB hNoCol

/-- **C3, Lemma 89's base facts at the healed round (a copy of the skeleton's `healed_round_base`
with the previous slot's votes and no root collision).** Under the execution assumptions and
unforgeability, with the phase's premises: when the round base holds at slot `s` for the proposal
`B` of the honest proposer `p` of slot `s` (honest at `M.supportCutoff S.C s`), `s ≥ 1`, slot
`s + 1` starts at or after `anchorCW S tGAT`, slot `s` starts at or after `anchorCW S tGAT` (`hA`),
`M.supportCutoff S.C (s + 2) ≤ tAwakeEnd`, no block `p` held before the start of slot `s` has
`B`'s root (`hNoCol`), and every slot-`(s − 1)` vote of a committee member of
`Hon M S Sched (s − 1)` is for a block it held that is a descendant of, or equal to, `p`'s anchor at
the start of slot `s` (`hPrev`): then
`HonestChainExtends M S Sched x (honestActiveAt M S Sched s) B s`; every updater of slot `s` saved
`B` as its confirmation of slot `s`; `B.slot = s`; and `B.parent` is in the viable tree of `p`'s
frame on the state its tick to the start of slot `s` starts from.

The copy's change, against the skeleton
(`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:211`): the hypotheses `hNoCol` and
`hPrev` are added. When `p` holds a block other than `B` with `B`'s root, no honest validator holds
`B` (roots name one block among what honest validators hold), and no updater saves `B`. Without
`hPrev`, nothing in the statement speaks of slot `s − 1`'s votes, which decide the members' walks of
slot `s` (Lemma 59 reads them). Both are supplied at an opening after the fast block: `hPrev` by the
line invariant (the anchor is a line source, `anchor_source`), and `hNoCol` by the case split on
`RootCollisionAtOpening` that Lemma 89's conclusion already carries.

Why: `round_base_steps` with the members `Hon M S Sched s`, the previous slot's voters with the
block `p`'s anchor, `p`'s viable head on its anchor's chain (`anchor_has_viable_head`), the values
of `head_height_floor` ordered by delivery (`floor_le_of_delivery_unordered`), the round base's
three clauses, the slot's only block (`only_block_of_unforgeability`) and `hNoCol`; the honest
active validators and the updaters are members; the parent is in the viable tree or is the anchor,
itself in the viable tree or the root (`get_anchor_root_or_viable`).

 at both clock
bounds `0` it is `dev`'s state before the start of slot `s`.

 at both clock
bounds `0` it is `dev`'s state before the start of slot `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase;
- `s`: the round's first slot; `B`: its proposal.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: the members' update of slot `s`
(`round_base_steps`), the latest time the proof reads.

Read aloud: at a round whose base holds, whose proposal's root is fresh and whose previous slot's
honest votes extend the proposer's anchor, every honest vote is for the proposal, every honest
update confirms it, and the proposal is the slot's.

 The assumption `hA`, that the anchor `anchorCW S tGAT` of the
committee premise is at or before the start of slot `s`, is that of `hAnchor` one slot earlier; it
replaces `tGAT + 4Δ · healFrontSlots S ≤ M.slotStart S.C s`, which the proof read only for this fact
. -/
theorem healed_round_base_of_prev_votes (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s : ℕ) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hs1 : 1 ≤ s) (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (s + 1))
    (hA : anchorCW S tGAT ≤ M.slotStart S.C s)
    (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B)
    (hBase : RoundBaseAt M S A x B s)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s B)
    (hPrev : ∀ u ∈ S.P.committee (s - 1) ∩ Hon M S A x (s - 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree,
        vote = GoldfishVote.mk u (s - 1) H_u.root ∧
        (M.get_anchor (x.tickInput (S.P.proposer s) (M.slotStart S.C s))
          ((M.slotStart S.C s : ℕ) : Int)).AncestorEq H_u) :
    HonestChainExtends M S A x (honestActiveAt M S A x s) B s ∧
    (∀ u ∈ updaterAt M S A x s,
      (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) ∧
    B.slot = s ∧
    B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput (S.P.proposer s) (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput (S.P.proposer s) (M.slotStart S.C s))).tree :=
  (GoldilocksCorrectness.Record.Proofs.Executions.healed_round_base_of_prev_votes M F U Fx) S A
    x R GST tGAT tAwakeEnd s B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hActive
    hCommittees hs1 hAnchor hA hEnd hp hB hBase hNoCol hPrev

/-- **C2, every round after the fast block is quiet relative to its own confirmations (a copy of
the skeleton's `quiet_round_after_fast_block` with `S.C.R ∣ s` and no root collision).** C1's
hypotheses (A5's, and a round's first slot `s` at least `k + 2` slots after `r * R` whose proposer
is honest at the support cutoff of slot `s`, `B` its proposal), with the next honest round opening
slot `s'' ≥ s + R`, its proposer honest at its own support cutoff,
`M.supportCutoff S.C s'' ≤ tAwakeEnd`, and no block the proposer of slot `s` held before the start
of slot `s` with `B`'s root (`hNoCol`): then
`QuietRoundOnConfirmations M S Sched x (Hon M S Sched) B s s''`.

The copy's change, against the skeleton
(`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:151`): the hypotheses `hsR : S.C.R ∣ s`
(C1's) and `hNoCol` are added. When the proposer of slot `s` holds a block other than `B` with `B`'s
root, no honest validator holds `B`, and the third clause (a viable head on `B`'s chain at every
member of the next slot) fails. The skeleton's flag (a member's confirmation of slot `s'' − 2` must
exist) is closed: every member saves a confirmation at every slot after `r * R`
(`member_saves_confirmation`). The skeleton's hypotheses `hLv`, `hInvL` and `hInvF` are deleted: the
proof reads part A's line invariant directly.

Why: the first two clauses are C1's; the members save `B` (C3, the previous slot's votes extending
the proposer's anchor by the line invariant), so `B` and every member's confirmation of a slot from
`s − 1` on are line sources, and the line invariant gives the third and fourth clauses
(`stepFrame_source`); for the fifth, the next proposer's root is a line source of a slot at most
`s'' − 2`, on the chain of a member's confirmation of slot `s'' − 2` (its own source's, or any
member's by the line invariant), and its frame has a viable head on that confirmation's chain.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `r`: the fast block's round; `H₂`: the
  bound on the old attestations; `v`: the validator whose update makes `L` fast; `L`: the fast
  block; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`: the honest round opening slot; `s''`: the next honest round opening slot; `B`: the proposal at the honest round opening slot.

Roots name blocks until `M.supportCutoff S.C s''`: the bundle `PartAHyps` is built with its end time
`M.supportCutoff S.C s''`, the latest time its kit reads here; C1 and C3 read up to
`M.supportCutoff S.C (s + 2)`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: after the fast block, every honest round whose proposal's root is fresh is quiet, with
no window needed.

 -/
theorem quiet_round_after_fast_block_opening (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s s'' : ℕ) (v : V)
      (L B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C s''))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `s''` ('s row)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s'' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s) (hs'' : s + S.C.R ≤ s'')
    (hEnd : M.supportCutoff S.C s'' ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `s''` is at a real time at most `tAwakeEnd`
    -- ('s row)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s'' →
      x.time k ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hq : S.P.proposer s'' ∉ A.corruptedAtTime x (M.supportCutoff S.C s''))
    (hB : ProposalAt M S x s B)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s B) :
    QuietRoundOnConfirmations M S A x (Hon M S A x) B s s'' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.quiet_round_after_fast_block_opening M F U Fx) S
    A x R GST tGAT tAwakeEnd r H₂ s s'' v L B E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent
    hGST hThird hAwake hActive hCommittees hAnchor hOld hv hL n' sent hUpdate hFast hs hsR hs'' hEnd hEndTick hp hq
    hB hNoCol

/-! ## Part B: two waiting openings at one height share one entry -/

/-- **An honest proposal is higher than its proposer's justification.** When `p` put the block `B`
on the wire at its tick at the start of slot `s + 1`, `B`'s chain-state height is at least one more
than `p`'s cache `h_j` then.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`, landed from
`scratch/goldilocks_healed/probe_wait_1.lean`.

Why: the parent `P` of `B` is a viable head of `p`. If `P` has height at least `h_j + 1`, so has
`B`. Otherwise `head_height_floor ≤ h_j`, which forces greatest chain-state height `h_j + 1` and no
contest, so `p`'s root is its justified block `J`, an ancestor of `P` at `P`'s height; `P`'s entry
is `J`, and `p`'s pool holds `J`'s justification certificate, which `B` includes (Lemma 53): `B`
rises to `h_j + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
  `B`: the proposal; `p`: its proposer.

Read aloud: an honest proposer never proposes at the height its own justification is at. -/
theorem honest_proposal_above_h_j (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (p : V)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    (x.tickInput p (M.slotStart S.C (s + 1))).justifiedHeight + 1 ≤
      (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.honest_proposal_above_h_j M F U Fx) S A x R E s B
    p hPropose

/-- **Reaching a justification height `h` with `head_height_floor` at most `h` is a
fork-choice change.** When `w`'s cache `h_j` is less than `h` before the step `j` (`x.st j w`) and at
least `h` after it (`x.st (j + 1) w`), `w`'s `head_height_floor` after the step is at most `h`, and
`w`'s justified block after the step is not the genesis block, the step `j` has a
`ForkChoiceChangeStep` at `w`.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`.

Why: after the step, greatest chain-state height `h_j + 1` with no contest, so the root is the new
justified block, of height at least `h`; the old root is the old justified block or the finalized
block, an ancestor of it, of height less than `h`: the new root is not an ancestor of the old one.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `w`: the validator; `j`: the step;
  `h`: the height.

Read aloud: a validator whose justification reaches the height of its least viable height moves its
root to the new justified block, which is a fork-choice change. -/
theorem change_of_h_j_reaches (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (w : V) (j h : ℕ)
    (hlo : (x.st j w).justifiedHeight < h)
      (hhi : h ≤ (x.st (j + 1) w).justifiedHeight)
    (hfl : M.head_height_floor (x.st (j + 1) w) ≤ h)
    (hJg : (x.st (j + 1) w).justified ≠ Block.genesis) :
    ForkChoiceChangeStep M S A x w j :=
  (GoldilocksCorrectness.Record.Proofs.Executions.change_of_h_j_reaches M F) S A x R E w j h hlo hhi
    hfl hJg

/-- **No honest validator reaches the height of a later honest proposal's justification one delay
before it.** Under the execution assumptions and unforgeability, with fewer than a third of the
validators in the adversary set up to `tEnd`: when `p` puts the block `B` on the wire at its tick at
the start of slot `s + 1` (that tick's step at a time at most `tEnd`), active at every step from the real
time `max (Δ S) Δs` before `t + Δ` up to that tick and ticking to the view freeze of slot `s`, and `u` is active from that time through `t` and honest at its last step before `t`, with
`GST + max (Δ S) Δs ≤ t + Δ` and `t + Δ` at most that start, `u`'s cache `h_j` before `t` is less
than `B`'s chain-state height.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`.

Why: the block witnessing `u`'s `h_j` reaches `p` by its tick to the start of slot `s + 1`
(`held_spread_tick`, with `p`'s tick to the view freeze of slot `s`), `p`'s `h_j`
does not decrease up to the slot's start (`h_j_mono`), and `B` is higher than `p`'s `h_j`
(`honest_proposal_above_h_j`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tEnd`: the end of the adversary bound; `t`: the time; `s`: the slot before the
  proposal's; `u`: the honest validator; `p`: the proposer; `B`: the proposal.

Roots name blocks until the time of the proposer's tick to the start of slot `s + 1`: the proposer's `h_j`
is read at that tick's input (`h_j_mono`), after `u`'s justification spreads to it.

Read aloud: one delay before an honest proposal, every honest justification is lower than it. -/
theorem h_j_lt_of_later_proposal (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd t s : ℕ) (u p : V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hGST : GST + max (Δ S) Δs ≤ t + Δ S) (hle : t + Δ S ≤ M.slotStart S.C (s + 1))
      (hEnd : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- `u` is active from `max (Δ S) Δs` before `t + Δ S` through `t + Δ S`, and honest at its last step before `t`
    (hu₀ : u ∈ A.activeThroughout x ((t + Δ S) - (max (Δ S) Δs)) (t + Δ S))
    (hu : u ∉ A.corrupted (x.stepBefore t))
    -- `p` is active at every step from the real time `max (Δ S) Δs` before `t + Δ S` up to its tick to the start of
    -- slot `s + 1`
    (hp : ∀ i : ℕ, (((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ x.tickStep p (M.slotStart S.C (s + 1)) →
      p ∈ A.active i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    (x.stateBefore t u).justifiedHeight < (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.h_j_lt_of_later_proposal M F U Fx) S A x R GST
    tEnd t s u p B E hNet hSkew hRedeliver Sy hRoots hParent hThird hGST hle hEnd hu₀ hu hp hpv hPropose

omit [RootOrder] in
/-- **A chain state whose justification height is at most `1` has the genesis block as its
justified block.** For every block `D`, when `(M.chainStateOf C D).h_j ≤ 1`,
`(M.chainStateOf C D).J` is the genesis block.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`.

Why: at `0` by `chainStateOf_J_spec`; at `1` the justified block is an entry of height `1`, and the
genesis block, an ancestor of it at the same height, is its own entry.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the configuration; `D`: the block.

Read aloud: nothing but the genesis block is justified at height at most one. -/
theorem J_genesis_of_h_j_le_one (C : Config) (D : Block V) (h1 : (M.chainStateOf C D).h_j ≤ 1) :
    (M.chainStateOf C D).J = Block.genesis :=
  (GoldilocksCorrectness.Record.Proofs.Executions.J_genesis_of_h_j_le_one M F) C D h1

/-- **Before the later opening's support cutoff, no honest validator holds a justification at the
waited height `h`, other than the genesis block.** Under the execution assumptions and
unforgeability, with fewer than a third of the validators in the adversary set up to `tEnd`: let
`t₀ + Δ` be the start of slot `s + 1` (at most `tEnd`), with `tL` at most `t₀`, where the proposer `p`,
ticking to the view freeze of slot `s`, puts on the wire a block `B₂` of
chain-state
height `h`; let every validator honest at a time from `t₀` to `tc` have `head_height_floor` at most
`h`, and no step whose real time is from `t₀` to before `tc` have a `ForkChoiceChangeStep` at a
validator outside the adversary set at that step. Then every validator `u` honest at `t + Δ S`, for a time `t` from `tL` to `tc`, has `h_j < h`
before `t`, or the genesis block as its justified block.

Proved in `Proofs/Executions/Lemma89WaitJ.lean`.

Why: up to `t₀`, by `h_j_lt_of_later_proposal`; after `t₀`, the first time `u`'s `h_j` reaches `h`
is a fork-choice change (`change_of_h_j_reaches`), which the hypothesis excludes.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `tEnd`: the end of the adversary bound; `tL`: the time from which the
  validators are read; `t₀`: one delay before the proposal; `tc`: the cutoff; `s`: the slot before the
  proposal's; `h`: the proposal's height; `p`: the proposer; `B₂`: the proposal; `u`, `t`: the
  validator and the time read.

Roots name blocks until the real time of `p`'s tick to the start of slot `s + 1`, a time at most
`tEnd`: `h_j_lt_of_later_proposal` at the later opening's slot `s + 1`, the only reading of the premise.

Read aloud: until the later opening's support cutoff, no honest validator has justified anything at
the waited height. -/
theorem h_j_lt_or_genesis_before_cutoff (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd tL t₀ tc s h : ℕ) (p : V) (B₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hL0 : tL ≤ t₀) (ht₀ : t₀ + Δ S = M.slotStart S.C (s + 1))
    (hs : M.slotStart S.C (s + 1) ≤ tEnd)
    -- the proposer's tick to the start of slot `s + 1` is at a real time at most `tEnd`
    (hsT : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- from a time `a` after `GST`, at least one delay or one sync delay before `tL + Δ S` and before `tL`,
    -- through `tEnd`, every validator outside the adversary set in a configuration in force then is awake in it
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ tL + Δ S) (ha₁ : a + 1 ≤ tL)
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B₂⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hB₂ : (M.chainStateOf S.C B₂).h = h)
    (hF : ∀ (u : V) (t : ℕ), t₀ ≤ t → t ≤ tc → u ∉ A.corruptedAtTime x t →
      M.head_height_floor (x.stateBefore t u) ≤ h)
    (hNo : ∀ (w : V) (j : ℕ), (t₀ : ℝ) ≤ x.time j → x.time j < tc → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (u : V) (t : ℕ) (hGt : tL ≤ t) (htc' : t ≤ tc) (hu : u ∉ A.corruptedAtTime x (t + Δ S)) :
    (x.stateBefore t u).justifiedHeight < h ∨
      (x.stateBefore t u).justified = Block.genesis := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.h_j_lt_or_genesis_before_cutoff M F U Fx) S A
    x R GST tEnd tL t₀ tc s h p B₂ E hNet hSkew hRedeliver Sy hΔs hRoots hParent hThird hL0 ht₀ hs hsT a hGSTa ha ha₁ hAw hpv
    hPropose hB₂ hF hNo u t hGt htc' hu

/-! ## Part B: the climb, on the span premise of record -/

/-- **B12 restated, part 1, on a copy: two rising quiet openings are at different heights.** In
the climb's context (the threshold `H₂` attained at `T₁`, every honest attestation before `aR M S r`
at most `H₂`), two openings `i < i' < m` and a slot `s''₂` with `rs i' * R + R ≤ s''₂ ≤ r * R`,
each with no fork-choice change (`ForkChoiceChangeStep`, at a step of a validator outside the
adversary set there) at a step from that validator's own tick to the vote time of slot `rs i * R − k − 1`
 to before one of its own ticks to a clock value at most the support cutoff of slot `rs (i + 1) * R` (resp. `s''₂`), the first rising, have proposals `B`, `B₂` of different
chain-state heights, when no opening's proposal collides with a block its proposer held. The later
honest round opening slot's range ends at `s''₂`: `rs (i' + 1) * R` for a rising or waiting one,
`r * R` for the one whose round holds `r * R`; the form with `s''₂ := rs (i' + 1) * R`
is the instance.

 `rs i' * R < r * R` becomes
`rs (i' + 1) * R ≤ r * R`, the end of the second opening's round; `hNoCol` is added (as for
`spoiled_near_fork_choice_change_cutoff`); the probe's `hSyncF`, `hCatchF` and the second
opening's rising hypothesis are not read and are left out.

Why: by contradiction with both heights `h`. The next proposal `B'` after `B` is higher than `h`
and at most `H₂ + 1` high, so `h` is `H₂ − 1` or `H₂`. No honest `head_height_floor` reaches
`h + 1` before the support cutoff of the later opening's first slot (it would reach a member of
the later opening and stay); so every honest validator holds `B'` one delay after its proposal,
with greatest chain-state height `h + 1`, no contest and its root on `B'`'s chain. The round's base
at `B'`'s slot makes the honest votes there extend `B'`, `lem79_step_sets` carries the chain
invariant relative to `B'` to the slot before the later opening, whose proposer's anchor is then
comparable with `B'`; so `B'` is an ancestor of `B₂`'s parent, and `B₂` is higher than `h`.

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, a weaker
hypothesis than `T₁ ≤ M.slotStart S.C (rs 0 * R − 2k)`: the climb takes `T₁` three delays into slot
`rs 0 * R − 2k`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i < i'`: the indices of the two honest round opening slots; `s''₂`: the end
  of the later one's range; `rs`: the rounds of the honest round opening slots; `B`, `B₂`: their proposals.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Read aloud: two honest round opening slots with no fork-choice change in their windows and rounds,
the first rising, propose at different heights.

 -/
theorem quiet_rising_heights_differ_cutoff (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i i' s''₂ : ℕ)
    (rs : ℕ → ℕ)
    (B B₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hsR' : rs i' * S.C.R + S.C.R ≤ s''₂)
    (hir' : s''₂ ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hNo' : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i' * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s''₂ → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hRise : RisingAt M S A x rs i)
    (hB : ProposalAt M S x (rs i * S.C.R) B)
      (hB₂ : ProposalAt M S x (rs i' * S.C.R) B₂) :
    (M.chainStateOf S.C B).h ≠ (M.chainStateOf S.C B₂).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.quiet_rising_heights_differ_cutoff M F U Fx) S
    A x R GST tGAT tAwakeEnd T₁ r H₂ m i i' s''₂ rs B B₂ E hNet hSkew hRedeliver Sy hΔs hRoots hParent
     hGST hT₁s hTick hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hii' hi' hsR' hir' hNoCol
    hNo hNo' hRise hB hB₂

/-- **The quiet honest round opening slot whose round holds `r * R` proposes at height `H₂ − 1` or
`H₂`.** In the climb's context: for an honest
round opening slot `i < m` with `rs i * R + R ≤ r * R` and no step from a validator's own tick to the
vote time of slot `rs i * R − k − 1` to before one of its own ticks to a clock value at most the support cutoff of slot
`r * R` with a `ForkChoiceChangeStep` at that validator, outside the adversary set at that step, its proposal `B` has `H₂ ≤ h(B) + 1` and `h(B) ≤ H₂`.


when quiet through the support cutoff of slot `r * R`, it is one of the two heights.

Why: above `H₂`, `quiet_top_gives_attestation_cutoff` at `s'' := r * R` gives an honest
attestation above `H₂` before `aR M S r`, against `hOld`; below `H₂ − 1`, an honest committee
member of slot `rs i * R` has `head_height_floor` at most `h(B)` at the support cutoff of the next
slot (the round's second clause) and the greatest chain-state height at least `H₂` there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the last honest round opening slot's index; `i`: the honest round
  opening slot; `rs`: their rounds; `B`: its proposal.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Read aloud: a quiet honest round opening slot before the fast block proposes at one of the two
heights the climb has not left. -/
theorem quiet_straddler_heights (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hi : i < m) (hir : rs i * S.C.R + S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (r * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hB : ProposalAt M S x (rs i * S.C.R) B) :
    H₂ ≤ (M.chainStateOf S.C B).h + 1 ∧ (M.chainStateOf S.C B).h ≤ H₂ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.quiet_straddler_heights M F U Fx) S A x R GST
    tGAT tAwakeEnd T₁ r H₂ m i rs B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick hThird
    hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hi hir hNoCol hNo hB

open Classical in
/-- **B12 restated, part 2, on a copy: at most two rising quiet openings before the climb's end.**
In the climb's context, the honest round opening slots `i < m` with `rs i * R < r * R`, no
fork-choice change (`ForkChoiceChangeStep`, at a step of a validator outside the adversary set
there) at a step from that validator's own tick to the vote time of slot `rs i * R − k − 1`
 to before one of its own ticks to a clock value at most the support cutoff of slot `min (rs (i + 1) * R) (r * R)`, and rising when
`rs (i + 1) * R ≤ r * R`, are at most two, when no opening's proposal collides with a block its
proposer held.

 `hNoCol` is added;
the probe's `hSyncF` and `hCatchF` are not read and are left out.

Why: each such opening's proposal has chain-state height `H₂ − 1` or `H₂` (for a rising one, its
next proposal is higher and at most `H₂ + 1`; for the one whose round holds `r * R`,
`quiet_straddler_heights`; an honest committee member's `head_height_floor` at the action time is
at most the proposal's height, and its greatest chain-state height at least `H₂`), and two of them
have different heights (part 1, the earlier one rising since its next slot is at or before the later
one's, the later one's range ending at `min (rs (i' + 1) * R) (r * R)`).

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, a weaker
hypothesis than `T₁ ≤ M.slotStart S.C (rs 0 * R − 2k)`: the climb takes `T₁` three delays into slot
`rs 0 * R − 2k`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR M S r`: `quiet_rising_next_proposal_late`, `quiet_straddler_heights` and
`quiet_rising_heights_differ_cutoff`, at the action time of round `r`.

Read aloud: before the climb's end, at most two honest round opening slots with no fork-choice change
in their windows and rounds climb, the one whose round holds the fast round's first slot
included.

 -/
theorem quiet_rising_before_fast_round_le_two_cutoff (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m : ℕ) (rs : ℕ → ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m) :
    ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
        x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) → j < k' →
        w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j) ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt M S A x rs i))).card ≤ 2 :=
  (GoldilocksCorrectness.Record.Proofs.Executions.quiet_rising_before_fast_round_le_two_cutoff M F U Fx)
    S A x R GST tGAT tAwakeEnd T₁ r H₂ m rs E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST
    hT₁s hTick hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hNoCol

/-- **The next proposal after a waiting quiet opening.** In the climb's context: for an opening `i < m` with `rs (i + 1) * R ≤ r * R`,
no opening's proposal colliding with a block its proposer held, no step from a validator's own tick to
the vote time of slot `rs i * R − k − 1` to before one of its own ticks to a clock value at most the support cutoff of slot
`rs (i + 1) * R` with a `ForkChoiceChangeStep` at that validator, outside the adversary set at that step, every proposal of the next opening at most as high as the opening's
proposal `B`, and `B` at most `H₂` high: some proposal `B'` of the next opening has `B` as an
ancestor, `B`'s chain-state height, is in its proposer's tree right after its tick to its slot's start,
and `H₂ ≤ h(B) + 1 ≤ H₂ + 1`.

A copy of `quiet_rising_next_proposal` (`Proofs/Executions/Lemma89RisingJ.lean`) with the rising
hypothesis replaced by the waiting one (`hWait`) and `hTop`; proved in
`Proofs/Executions/Lemma89ClimbLate.lean`.

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, a weaker
hypothesis than `T₁ ≤ M.slotStart S.C (rs 0 * R − 2k)`: the climb takes `T₁` three delays into slot
`rs 0 * R − 2k`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `rs`: the rounds of the
  honest round opening slots; `B`: the proposal at the honest round opening slot.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Read aloud: a waiting quiet opening's next proposal extends it at the same height, `H₂ − 1` or
`H₂`. -/
theorem quiet_waiting_next_proposal (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) {Δs : ℕ} (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hi : i < m) (hir : rs (i + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- every validator outside the adversary set at the support cutoff of the slot after the opening's first slot is
    -- active through the attestations' sync delay after the later of that first slot's duty window's start and `GST`
    --
    (hHoldF : ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hWait : ∀ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' →
      (M.chainStateOf S.C B').h ≤ (M.chainStateOf S.C B).h)
    (hTop : (M.chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt M S x (rs i * S.C.R) B) :
    ∃ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' ∧
      B.AncestorEq B' ∧ (M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
      B' ∈ (x.tickOutput (S.P.proposer (rs (i + 1) * S.C.R)) (M.slotStart S.C (rs (i + 1) * S.C.R))).tree ∧
      H₂ ≤ (M.chainStateOf S.C B).h + 1 ∧ (M.chainStateOf S.C B).h ≤ H₂ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.quiet_waiting_next_proposal M F U Fx) S A x R
    GST tGAT tAwakeEnd T₁ r H₂ m i rs B E hNet hSkew hRedeliver hRoots hParent hGST hT₁s hTick
    hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hi hir hNoCol hNo E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hWait hTop hB

/-- **Two waiting quiet openings at one height share the height's entry.** In the climb's context
: take two
openings `i < i' < m` with `rs (i' + 1) * R ≤ r * R`, no opening's proposal colliding with a block
its proposer held, no step with a `ForkChoiceChangeStep` at a validator outside
the adversary set at that step, from its own tick to the vote time of slot `rs i * R − k − 1` to before one of its own ticks to a clock value at most the support cutoff of slot `rs (i + 1) * R`, nor from its own tick to the vote time of
slot `rs i' * R − k − 1` to before one of its own ticks to a clock value at most the support cutoff of slot `rs (i' + 1) * R`
, every
proposal of opening `i + 1` at most as high as opening `i`'s proposal `B`, and `B` at most `H₂`
high. If `B` and opening `i'`'s proposal `B₂` have the same chain-state height, they have the same
entry (`(M.chainStateOf S.C ·).T_h`).

Proved in `Proofs/Executions/Lemma89ClimbLate.lean`, a copy of
`quiet_rising_heights_differ_cutoff`'s route.

Why: the next proposal `B'` after `B` is on `B`'s chain at `B`'s height `h`; no honest validator has
`h_j ≥ h` before the later opening's support cutoff (`h_j_lt_or_genesis_before_cutoff`), so every
honest holder of `B'` has its root on `B'`'s chain and `B'` reaches every honest validator; the
honest votes carry the chain invariant relative to `B'` to the later opening, whose proposal then
extends `B'`: one entry (Lemma 47 (e)).

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, a weaker
hypothesis than `T₁ ≤ M.slotStart S.C (rs 0 * R − 2k)`: the climb takes `T₁` three delays into slot
`rs 0 * R − 2k`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i < i'`: the indices of the two honest round opening slots; `rs`: the
  openings' rounds; `B`, `B₂`: their proposals.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Read aloud: two quiet openings waiting at one height wait on the same entry. -/
theorem quiet_waiting_same_entry_cutoff (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i i' : ℕ) (rs : ℕ → ℕ)
    (B B₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) {Δs : ℕ} (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hir' : rs (i' + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hNo' : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i' * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i' + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- every validator outside the adversary set at the support cutoff of the slot after opening `i`'s first slot is
    -- active through the attestations' sync delay after the later of that first slot's duty window's start and `GST`
    -- (; the row `quiet_waiting_next_proposal` reads)
    (hHoldF : ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hWait : ∀ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' →
      (M.chainStateOf S.C B').h ≤ (M.chainStateOf S.C B).h)
    (hTop : (M.chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt M S x (rs i * S.C.R) B)
      (hB₂ : ProposalAt M S x (rs i' * S.C.R) B₂) :
    (M.chainStateOf S.C B).h = (M.chainStateOf S.C B₂).h →
      (M.chainStateOf S.C B).T_h = (M.chainStateOf S.C B₂).T_h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.quiet_waiting_same_entry_cutoff M F U Fx) S A
    x R GST tGAT tAwakeEnd T₁ r H₂ m i i' rs B B₂ E hNet hSkew hRedeliver hRoots hParent
    hGST hT₁s hTick hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hii' hi' hir' hNoCol hNo hNo' E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F
    hHoldF hWait hTop hB hB₂

open Classical in
/-- **At most six openings before the climb's end lie outside the spans the climb places.** Under
the execution assumptions and unforgeability, with every honest validator awake in the phase
`[tGAT, tAwakeEnd]`, fewer than a third of the validators in the adversary set up to its end,
committee sleepiness from `anchorCW S tGAT`, the honest round opening slots of the rounds `rs 0 < … < rs m`
(`HonestOpeningSeq`), the threshold `H₂` the greatest height of an honest attestation before `T₁`
(`OldHeightAttained`) with `tGAT + Δs ≤ T₁` and `T₁ + Δ` at most the start of slot `rs 0 * R − k − 1`,
every honest attestation sent before `aR M S r ≤ tAwakeEnd` of height at most `H₂`, and no opening's
proposal colliding with a block its proposer held: there are two spans of `δt` slots (`waits`) and
four spans of `k + 2` slots (`w4`) such that at most six honest round opening slots `i < m` with
`rs i * R < r * R` have their first slot outside all of them; the one whose round holds `r * R`
among them.



Why: the four spans of `k + 2` slots start at the slots of the four times of
`fork_choice_change_kinds`, the two of `δt` slots at the slots of the entries of the waiting
openings at the heights `H₂ − 1` and `H₂`. An opening with a step `j` with `ForkChoiceChangeStep` at
a validator outside the adversary set at `j`, at a real time from the vote time of slot
`rs i * R − k − 1` to before the support cutoff of slot `min (rs (i + 1) * R) (r * R)`, outside the
span of the change's kind has the change
in its round, and two such openings of one kind would put the later one in that kind's span: at
most four. An opening with no such change whose next slot is at or before `r * R` is quiet with
its base, so it rises or waits (Lemma 89r); a waiting one lies in its height's wait span
(`quiet_waiting_same_entry_cutoff`); the rising ones and the one whose round holds `r * R` are at
most two (`quiet_rising_before_fast_round_le_two_cutoff`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR M S r`: `fork_choice_change_kinds` and the climb's steps read up to the
action time of round `r`.

Read aloud: before the climb's end, two waits and four windows leave at most six honest round opening slots
outside them. -/
theorem climb_count_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m : ℕ) (rs : ℕ → ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m) :
    ∃ (waits : Fin 2 → ℕ) (w4 : Fin 4 → ℕ),
      ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
        OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i)).card ≤ 6 :=
  (GoldilocksCorrectness.Record.Proofs.Executions.climb_count_before M F U Fx) S A x R GST tGAT
    tAwakeEnd T₁ r H₂ m rs E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hRoots hParent hGST hT₁s hTick
    hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hNoCol

/-- **Part B's assembly, the climb to the first honest fast block.** Under the execution assumptions
(time diverges, monotone corruption, synchrony and catch-up on wake for the AC objects with delay
`Δ` and for the FG objects with delay `Δ_F` from `GST`, roots name blocks, a block's parent is held
at its delivery, votes are cast by their owners) and unforgeability, with `GST ≤ tGAT`, fewer than a
third of the validators in the adversary set up to `tAwakeEnd`, every validator outside the
adversary set awake from `tGAT` to `tAwakeEnd`, committee sleepiness from `anchorCW S tGAT`, the
honest round opening slots of the rounds `rs 0 < … < rs m` from `tGAT + 4Δ · healFrontSlots S` to `tAwakeEnd`, and nine
honest round opening slots outside every two spans of `δt` slots and five spans of `k + 2` slots
(`OpeningsOutsideWaitsAndWindows`): either some opening's proposal collides with a block
its proposer held (`RootCollisionAtOpening`), or there are a round `r`, a threshold `H₂`, a
validator `v`, a block `L` and a node state `n'` with: slot `r * R + 1` starting at or after
`anchorCW S tGAT`; `aR M S r ≤ tAwakeEnd`; every honest attestation sent before `aR M S r` of height
at most `H₂`; `v` outside the adversary set at `aR M S r`; `v`'s update of slot `r * R + 1` at
`aR M S r` able to leave `n'` (`ConfirmationUpdated`), with `L` among the fast blocks of `n'`; `L`'s
chain-state height `H₂ + 1`; and an honest round opening slot `j` with `j + 2 ≤ m`, the first whose
first slot is at least `k + 2` slots after `r * R`.

Proved in `Proofs/Executions/Lemma89Climb5.lean`.

The probe's `climb_to_fast_block5` (`scratch/goldilocks_healed/probe_recount_1.lean:362`, not
landed) with the count 11 in place of 10: with 10, the opening whose round straddles `r * R`
leaves only three openings after the fast block.

Why: split on the collision disjunct. Take `T₁` three delays into slot `rs 0 * R − 2k` and `H₂` the
greatest height of an honest attestation before `T₁` (B1). Some honest attestation above `H₂` is
sent from `T₁` to before `aR M S (rs (m − 1))`, or `climb_count_before` at that round leaves seven
outside openings at most. B3 gives the first round `r` above `H₂`, B4 its fast block `L`; `T₁ ≤
aR S r` puts slot `r * R + 1` at or after the anchor. At `r`, at most six outside openings `i < m`
with `rs i * R < r * R`, and the last
one (`after_of_before`): three outside honest round opening slots are at or after `r * R`, hence
at least `k + 2` slots after it (the span of `k + 2` slots at `r * R`), so the first honest round
opening slot at least `k + 2` slots after `r * R` has two more after it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR M S (rs (m - 1))`: the count at the round `rs (m − 1)`
(`climb_count_before`), and at the first round `r` above the threshold, whose action time is before
`aR M S (rs (m - 1))`.

The landed statement names the answer of `v`'s update; the twin names a node state `n'` that update
can leave (`ConfirmationUpdated`), as `fast_block_at_first_round`'s twin does.

Read aloud: nine honest round opening slots outside two timeout waits and five spans of `k + 2`
slots give the first honest fast block one height above the threshold and three honest
round opening slots at least `k + 2` slots after its round. -/
theorem climb_to_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (aR M S (rs (m - 1))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening M S A x rs m ∨
    ∃ (r H₂ : ℕ) (v : V) (L : Block V) (n' : M.N),
      anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1) ∧ aR M S r ≤ tAwakeEnd ∧
      OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂ ∧
      v ∉ A.corruptedAtTime x (aR M S r) ∧
      ConfirmationUpdated M S.C S.P (x.tickInput v (aR M S r)) ((aR M S r : ℕ) : Int)
        (r * S.C.R + 1) n' ∧
      L ∈ M.fastBlocks n' ∧ (M.chainStateOf S.C L).h = H₂ + 1 ∧
      x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd ∧
      x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) ∧
      (∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.tickStep v (aR M S r) → x.lbl k = Event.tick u t →
        u ∉ A.corruptedAtTime x tAwakeEnd →
        (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂) ∧
      ∃ j : ℕ, j + 2 ≤ m ∧ r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R ∧
        ∀ i : ℕ, i < j → rs i * S.C.R < r * S.C.R + S.C.k + 2 :=
  (GoldilocksCorrectness.Record.Proofs.Executions.climb_to_fast_block M F U Fx) S A x R GST tGAT
    tAwakeEnd m rs E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hRoots hParent hGST hThird
    hAwake hActive hCommittees hSeq hm

/-- **C4, consecutive openings after the fast block rise (a copy of the skeleton's
`opening_rises_after_fast_block` with the round's first slot).** Under the execution assumptions,
attestations delivered within `Δ_F` after `GST` and unforgeability, with the phase's premises and
part A's (the fast block `L` of `v`'s update at the action time of round `r`, of height `H₂ + 1`):
when the honest round opening slot `s` is a round's first slot at least `k + 2` slots after `r * R`
,
`B` is its proposal, and `B'` is the proposal of a later honest round opening slot `s'' ≥ s + R` with
`M.supportCutoff S.C s'' ≤ tAwakeEnd`: either a block the proposer of slot `s` held before the start
of slot `s` has `B`'s root, or `B` is `B'` or an ancestor of `B'`, `B'`'s chain-state height is at
least `B`'s plus one, when `B'`'s parent is at `B`'s height the justified block of `B'`'s chain
state is `B`'s entry `T_h`, and every member of `Hon M S Sched s` saved `B` as its confirmation of
slot `s`.

The copy's change, against the skeleton
(`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:266`): the hypothesis `hsR : S.C.R ∣ s`
is added, which C1 and C2 (their copies) read; every caller reads C4 at an opening, the first slot
`rs i * R` of a round. The skeleton's hypotheses `hLv`, `hInvL` and `hInvF` are deleted: the proof
reads part A's line invariant directly.

Why: with no root collision, Lemma 89r with the targets premise (`lem89r_quiet_round_targets`) at
the round of slot `s`, its family the line sources of the slots `μ` with `μ + 2 ≤ s`, its quiet
round C2; the targets premise holds because `B`'s height is greater than `H₂` and every honest
attestation at such a height from round `r`'s action time on is a target
(`PartAHyps.attestation_target`). The skeleton's flag on the fresh height is answered there: a
member that attested at `B`'s height in an earlier round did so for `B`'s entry, with a target.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `r`, `H₂`, `v`, `L`: the fast block's round, the threshold, the validator, the fast block;
  `n'`, `sent`: an outcome of `v`'s tick at the action time of round `r`;
- `s`, `B`: the honest round opening slot and its proposal; `s''`, `B'`: the next honest round opening slot and
  its proposal.

Roots name blocks until `M.supportCutoff S.C s''`: the bundle `PartAHyps` is built with its end time
`M.supportCutoff S.C s''`, the latest time its kit reads here; C2 reads up to the same time, Lemma
89r up to `M.supportCutoff S.C (s'' - 1)`.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake hActive`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: after the fast block, every honest round opening slot's proposal is extended by the next one's,
one height higher, which carries its justification.

 -/
theorem opening_rises_after_fast_block_opening (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s s'' : ℕ) (v : V)
    (L B B' : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- the members of slot `s`'s round are active through the attestations' sync delay after the later of the slot's
    -- duty window's start and `GST`, where Lemma 89r reads the attestations' sync fact
    (hHoldF : ∀ w ∈ Hon M S A x s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C s''))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `s''` (, stops_recheck_85)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s'' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s) (hs'' : s + S.C.R ≤ s'')
    (hEnd : M.supportCutoff S.C s'' ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `s''` is at a real time at most
    -- `tAwakeEnd` (, stops_recheck_85)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s'' →
      x.time k ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hq : S.P.proposer s'' ∉ A.corruptedAtTime x (M.supportCutoff S.C s''))
    (hB : ProposalAt M S x s B) (hB' : ProposalAt M S x s'' B') :
    RootCollisionAtProposal M S A x s B ∨
    (B.AncestorEq B' ∧ (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
      ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
        (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h) ∧
      ∀ u ∈ Hon M S A x s,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.opening_rises_after_fast_block_opening M F U Fx) S
    A x R GST tGAT tAwakeEnd r H₂ s s'' v L B B' E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hRoots
    hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hOld hv hL n' sent hUpdate hFast hs hsR
    hs'' hEnd hEndTick hp hq hB hB'

/-- **C6, the caches at the hand-over step (a copy of the skeleton's `caches_at_handover` with the
proposal held and the finalized blocks on it).** Under the execution assumptions and
unforgeability, every honest validator awake from `tGAT` to `tAwakeEnd`, fewer than a third of the
validators in the adversary set up to `tAwakeEnd`: when `B₃`, held by the proposer of slot
`s₃ ≤ s_m` (honest at its support cutoff) right after the start of slot `s₃ ≥ tGAT`, has a chain
state whose justification height is greater than `H`, every validator honest at the vote time of
slot `s₃` has its finalized block before that time `B₃` or an ancestor of `B₃`, every justified
block an honest validator holds at the step `i₁` at a height greater than `H` is, by its root, an
entry of the honest chain from `s₀` at a slot `s_a` with
`M.supportCutoff S.C (s_a + 1) ≤ x[i₁].time`, `M.supportCutoff S.C s_m ≤ tAwakeEnd`, and the step
`i₁` is `u`'s tick to the vote time of slot `s_m` — then `u`, if honest at `x[i₁].time`, has
`CachesOnChain M S Sched x s₀ H` in the state that tick reads.

The copy's change, against the skeleton
(`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:354`): the proposal `hB₃` is replaced by
`hHeld` (its proposer holds it), and `hF₃` (the finalized blocks before the vote time of slot `s₃`
are on `B₃`) is added: without them `B₃` need not reach a validator by the vote time of slot `s_m`
when `s₃ = s_m` (its delivery is accepted only on the receiver's finalized chain), and C6's own
hypotheses say nothing of the receivers' finalized blocks. `hCerts` is read at the step `i₁` only (a
weaker hypothesis). `hs₀` and `hJchain` are deleted (unused). The hand-over supplies `hHeld`, the
proposer's tree in the state its tick to the start of slot `s₃` leaves, from
the tick that proposes `B₃` (`opening_proposal_held_tickOutput`) and `hF₃` from
`PartAHyps.F_before_vote_ancestor_proposal`. the hand-over supplies it from `cert_entry_at_slot`.

Why: `B₃` reaches every honest validator by the vote time of slot `s₃` (`mem_T_at_step_of_held`),
so the cache `h_j` is at least `h_j(B₃) > H` (`h_j_ge_of_held_exec`); the justified block is a held
block's chain state's, with its justification certificate (Lemma 66), so `hCerts` puts it on the
honest chain (roots name blocks); the finalized block is on the justified block's chain (Lemma 46).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
- `s₀`: the first slot of the honest chain; `H`: the threshold; `s₃`, `B₃`: the carrier's slot and
  block; `s_m`: the last honest round opening slot; `i₁`: the step; `s_a`: the slot of an entry `hCerts`
  names.



Roots name blocks until `x[i₁].time`: the justified block `u` holds at the step `i₁` against the
entry `hCerts` names, at a slot whose update an honest attester ran at a tick before `i₁`, holding the entry; `B₃` reaches `u` by the vote time
of slot `s₃`, before it.

Read aloud: once the carrier has reached everyone, every honest finality gadget's caches are on the
honest chain above the threshold.

 -/
theorem caches_at_handover_of_held (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s₀ H s₃ s_m i₁ : ℕ) (B₃ : Block V) (u : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time i₁))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hs₃ : s₃ ≤ s_m) (htGAT : tGAT + max (Δ S) Δs ≤ M.voteTime S.C s₃)
    (hEnd : M.supportCutoff S.C s_m ≤ tAwakeEnd)
    (hp : S.P.proposer s₃ ∉ A.corruptedAtTime x (M.supportCutoff S.C s₃))
    -- the proposer holds `B₃` in the state its tick to the start of slot `s₃` leaves
    (hHeld : B₃ ∈ (x.tickOutput (S.P.proposer s₃) (M.slotStart S.C s₃)).tree)
    -- `u` is active after every step from the proposer's tick to the start of slot `s₃` up to its own tick to the vote
    -- time of slot `s₃`, and `u` ticks to the start of slot `s₃`
    (hAct₃ : ∀ j : ℕ, x.tickStep (S.P.proposer s₃) (M.slotStart S.C s₃) ≤ j → j ≤ x.tickStep u (M.voteTime S.C s₃) → u ∈ A.active j)
    (hTick₃ : x.lbl (x.tickStep u (M.slotStart S.C s₃)) = Event.tick u (M.slotStart S.C s₃))
    -- every validator that ticks to the vote time of slot `s₃`, honest at that tick, has in the state
    -- the tick reads its finalized block `B₃` or an ancestor of `B₃`
    (hF₃ : ∀ w : V, x.lbl (x.tickStep w (M.voteTime S.C s₃)) = Event.tick w (M.voteTime S.C s₃) →
      w ∉ A.corruptedAtTime x (x.time (x.tickStep w (M.voteTime S.C s₃))) →
      (x.tickInput w (M.voteTime S.C s₃)).finalized.AncestorEq B₃)
    (hJ : H < (M.chainStateOf S.C B₃).h_j)
    -- every justified block an honest validator holds at the step `i₁` at a height greater than
    -- `H` was certified by an honest attester `uₐ` that ran the update of the entry's slot `s_a` at
    -- its tick to the support cutoff of slot `s_a + 1`, a step before `i₁`, is honest up to the time
    -- of `i₁`, and held the entry when it ticked; the entry is on the honest chain at `s_a` (K1's
    -- shape,)
    (hCerts : ∀ (w : V) (D T : Block V) (h : Height),
      D ∈ (x.st i₁ w).tree → JustificationCertOn M D h T → H < h →
      ∃ (s_a : ℕ) (uₐ : V) (E : Block V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < i₁ ∧
        x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
        uₐ ∈ updaterAt M S A x s_a ∧ uₐ ∉ A.corruptedAtTime x (x.time i₁) ∧
        E ∈ (x.tickInput uₐ (M.supportCutoff S.C (s_a + 1))).tree ∧
        OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
        (M.chainStateOf S.C E).h = h ∧ T.root = E.root)
    -- the step `i₁` is `u`'s tick to the vote time of slot `s_m`
    (hu : x.lbl i₁ = Event.tick u (M.voteTime S.C s_m)) :
    u ∉ A.corruptedAtTime x (x.time i₁) → CachesOnChain M S A x s₀ H (x.st i₁ u) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.caches_at_handover_of_held M F U Fx) S A x R GST
    tGAT tAwakeEnd s₀ H s₃ s_m i₁ B₃ u E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake
    hs₃ htGAT hEnd hp hHeld hAct₃ hTick₃ hF₃ hJ hCerts hu

/-- **C7, Lemma 89's frame clauses from the line invariant.** Under the execution assumptions and
unforgeability, with the phase's premises and part A's (the fast block `L` of `v`'s update at the
action time of round `r`, of height `H₂ + 1`): for `s₀ ≥ r * R + k + 2` and
`M.supportCutoff S.C s_m ≤ tAwakeEnd`, at every slot `s` with `s₀ < s < s_m`, every member of
`Hon M S Sched s` satisfies `VoterFrameOnChainAt M S Sched x s₀ s`, and every validator of
`updaterAt M S Sched x s` satisfies `UpdaterFinalizedOnChainAt M S Sched x s₀ s`.

The skeleton's hypotheses `hLv`, `hInvF` and `hInvL` are deleted: the proof reads part A's line
invariant directly.

Why: a block on the honest chain before `s` from `s₀` is on an updater's confirmation of a slot
`s' ≥ s₀`, a line source of slot `s'` (`source_conf`); `stepFrame_source` at slot `s − 1` gives
`StepFrameAt` relative to it, whose conjuncts are the two clauses.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `r`, `H₂`, `v`, `L`: the fast block's round, the threshold, the validator, the fast block;
  `n'`, `sent`: an outcome of `v`'s tick at the action time of round `r`;
  `s₀`: the healed round's slot; `s_m`: the last honest round opening slot.

Roots name blocks until `M.supportCutoff S.C s_m`: the bundle `PartAHyps` is built with its end time
`M.supportCutoff S.C s_m`, the latest time its kit reads here.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: after the healed round every member's frame follows the honest chain so far.

 -/
theorem frames_at_phase_slots (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s₀ s_m : ℕ) (v : V)
      (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C s_m))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `s_m` ('s row)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s_m →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hs₀ : r * S.C.R + S.C.k + 2 ≤ s₀) (hEnd : M.supportCutoff S.C s_m ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `s_m` is at a real time at most `tAwakeEnd`
    -- ('s row)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s_m →
      x.time k ≤ tAwakeEnd) :
    ∀ s : ℕ, s₀ < s → s < s_m →
      (∀ w ∈ Hon M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.frames_at_phase_slots M F U Fx) S A x R GST tGAT
    tAwakeEnd r H₂ s₀ s_m v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv hL n' sent hUpdate hFast hs₀ hEnd hEndTick

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
slot order give C5's hypotheses, so `h_j(B_{j+2}) ≥ h(B_{j+1}) ≥ h(B₀) + 1`; the
copy of C6 the caches at the threshold `h(B₀)`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`, `rs`: the index of the last honest round opening slot and the rounds of the honest round opening slots; `r`, `H₂`, `v`, `L`: the climb's output; `n'`,
  `sent`: an outcome of `v`'s tick at the action time of round `r`; `j`: the index of an honest round opening slot.

Roots name blocks until `M.supportCutoff S.C (rs m * S.C.R)`: the bundle `PartAHyps` is built with
its end time `M.supportCutoff S.C (rs m * S.C.R)`; C4 at the honest round opening slots `j` and
`j + 1`, C1, C3, C6 and C7 read up to that time.

The landed statement reads the answer `A'` of `v`'s update; the twin reads an outcome `(n', sent)`
of `v`'s tick at the action time of round `r` from the node state that tick reads (its tick input), with `L` among
the fast blocks of `n'` (template A2), without A2's hypothesis that `v` has been awake since the
duty window's start of slot `r * R + 1`: `hAwake`, `hAnchor` and `hv` give it, as for
`fast_block_base`.

Read aloud: the first honest round opening slot a `k + 2`-slot wait after the fast block is the
healed round, and the two honest round opening slots after it bring the justification above
`h(B₀)` to every honest validator by the vote time of the last honest round opening slot.

  -/
theorem handover_after_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m r H₂ : ℕ) (rs : ℕ → ℕ) (v : V)
    (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot before the last, the members of its round are active through the
    -- attestations' sync delay after the later of its duty window's start and `GST`, C4's row at that slot
    --
    (hHoldF : ∀ i, i < m → ∀ w ∈ Hon M S A x (rs i * S.C.R),
      w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (rs m * S.C.R)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `rs m * R` (, stops_recheck_85)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `rs m * R` is at a real time at most
    -- `tAwakeEnd` (, stops_recheck_85)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      x.time k ≤ tAwakeEnd)
    -- the climb's output
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n') (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (j : ℕ) (hj2 : j + 2 ≤ m) (hsj : r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R) :
    RootCollisionAtOpening M S A x rs m ∨
    (∃ (j' s₀ : ℕ) (B₀ : Block V),
      j' < m ∧ s₀ = rs j' * S.C.R ∧
      HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt M S A x s₀,
        (x.tickOutput u (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
        (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v)) ∧
      (∀ u : V, x.lbl (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) = Event.tick u (M.voteTime S.C (rs m * S.C.R)) →
        u ∉ A.corruptedAtTime x (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) →
        CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.tickInput u (M.voteTime S.C (rs m * S.C.R))))) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.handover_after_fast_block M F U Fx) S A x R GST
    tGAT tAwakeEnd m r H₂ rs v L E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hRoots hRootsTick hParent
    hGST hThird hAwake hActive hCommittees hSeq hEndTick hAnchor hOld hv n' sent hUpdate hFast hL j hj2 hsj

/-- **C9, every honest round opening slot has a proposal (a copy of the skeleton's `opening_proposal_exists`
for the slots from `2` on).** In an execution that reaches every time, with permanent corruption:
when the proposer of slot `s ≥ 2` ticks to the start of slot `s`, active after
every step up to that tick from the trace's start or from its own tick to a clock value at most the
proposal window's start of slot `s`, the proposer's tick at the start of slot `s` puts some block on the wire.

The copy's change, against the skeleton
(`scratch/goldilocks_healed/skeleton_89b/SkeletonPartC.lean:446`): `hs1 : 1 ≤ s` becomes
`hs2 : 2 ≤ s`, the slots the landed proposal kit covers (`honest_proposer_proposesJ`); slot `1` is
not measured. The copy has its own name because the landed `opening_proposal_exists`
(`Proofs/Executions/Lemma89RisingJ.lean:915`, over the opening sequence, the form the hand-over
calls) has the skeleton's name in the same namespace.

Why: the proposer is active through its own window from the proposal window's start to its tick to
the slot's start, so that tick proposes (`honest_proposer_proposesJ`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tGAT`, `tAwakeEnd`: the times; `s`:
  the slot.

Read aloud: an honest proposer awake through its proposal window proposes.

 -/
theorem opening_proposal_exists_of_window (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tGAT tAwakeEnd s : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hs2 : 2 ≤ s)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (proposal_window_start S.C s) (M.slotStart S.C s)) :
    ∃ B : Block V, ProposalAt M S x s B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.opening_proposal_exists_of_window M F U) S A x R
    tGAT tAwakeEnd s E hs2 hp

/-! ## Lemma 89

Proved in `Proofs/Executions/Lemma89HandoverVF.lean`. -/

/-- **Lemma 89 of record: the events of the phase.** Under the phase's
premises and nine honest round opening slots outside every two spans of `δt` slots and five spans
of `k + 2` slots (`OpeningsOutsideWaitsAndWindows`, `PhaseDefs.lean`): either some honest round opening slot's
proposal has the root of a block its proposer held, or some opening `j < m` is the healed round: its
first slot `s₀` and proposal `B₀`, of slot `s₀`; the slot invariant restricted to `B₀` at `s₀` over
the honest active validators of `s₀`; every updater of `s₀` saved `B₀`; every honest attestation
sent before the round's action time has height at most `h(B₀)`; at every slot `s` with
`s₀ < s < s_m`, every member of `roundMembers M S Sched (s + 1)` has its frame on the honest chain
before `s`; every validator that ticks to the vote time of slot `s_m`, honest at that tick, has in the state
the tick reads its caches on
the honest chain with `h_j > h(B₀)`; and every validator `w` outside the adversary set at the
vote time of slot `s_m` has its frame before that vote time on the honest chain before `s_m`
. Here `s_m := rs m * R`, the
first slot of the last opening.

Why the clause: the phase still runs at the vote time of slot `s_m` (its support cutoff is at most
`tAwakeEnd`, `HonestOpeningSeq.last`), so the phase's line invariant gives the voter frame there
(`PartAHyps.voterFrame_at_last_opening`); nothing after the hand-over reaches that time, the
caches being known only from each validator's tick to that vote time on.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`, `rs`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Why: the climb `climb_to_fast_block` and the hand-over's copy with the voter frame
`handover_after_fast_block_vf` (part A's assembly is not needed: the hand-over reads the line
invariant directly).

Roots name blocks until `M.supportCutoff S.C (rs m * S.C.R)`: the hand-over's copy
(`handover_after_fast_block_vf`); the climb reads up to `aR M S (rs (m - 1))`, before it.

Read aloud: the conclusion of Lemma 89, and the voter frame at the last opening's slot.

   -/
theorem lem89_phase (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (rs m * S.C.R)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `rs m * R` (, stops_recheck_85)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `rs m * R` is at a real time at most
    -- `tAwakeEnd` (, stops_recheck_85)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      x.time k ≤ tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening M S A x rs m ∨
    (∃ (j s₀ : ℕ) (B₀ : Block V),
      j < m ∧ s₀ = rs j * S.C.R ∧
      HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt M S A x s₀,
        (x.tickOutput u (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
        (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v)) ∧
      (∀ u : V, x.lbl (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) = Event.tick u (M.voteTime S.C (rs m * S.C.R)) →
        u ∉ A.corruptedAtTime x (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) →
        CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.tickInput u (M.voteTime S.C (rs m * S.C.R)))) ∧
      (∀ w : V, w ∉ A.corruptedAtTime x (M.voteTime S.C (rs m * S.C.R)) →
        VoterFrameOnChainAt M S A x s₀ (rs m * S.C.R) w)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89_phase M F U Fx) S A x R GST tGAT tAwakeEnd
    m rs E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hRoots hRootsTick hParent hGST hThird hAwake hActive
    hCommittees hSeq hEndTick hm

end GoldilocksCorrectness.Record.Statements.Executions

