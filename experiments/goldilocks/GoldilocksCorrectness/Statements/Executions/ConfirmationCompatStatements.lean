module
public import GoldilocksCorrectness.Proofs.Executions.Lemma78Compat
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements

@[expose] public section

/-! New statements, the compatible variants of Lemma 77 and
Lemma 78 and its twin, stated on the brief's templates; the landed Lemmas 77 and 78 stay as they
are. Proved in `GoldilocksCorrectness/Proofs/Routines/Lemma77Compat.lean` and
`GoldilocksCorrectness/Proofs/Executions/Lemma78Compat.lean`.

- Lemma 77c, `lem77c_update_confirmation_compatible_of_majority`, routine form: Lemma 77's
  statement with "an early supporter of `B`'s chain" replaced by "one vote in the pool, stamped
  before the late cutoff, every block of the frame's tree named by its head compatible with
  `B`", without its conditions on `Φ.F` and on the slots of the pool's votes, concluding
  compatibility with `B`;
- Lemma 78c, `lem78c_update_confirmation_compatible_of_voter_majority`, and its twin
  `lem78c_update_confirmation_compatible_of_voter_majority_upTo`: Lemma 78 and its twin with the
  members' blocks compatible with `B` in place of on `B`'s chain, concluding compatibility with
  `B`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

end GoldilocksCorrectness.Statements.Routines

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 78c, an honest confirmation update over a majority whose votes are compatible with
`B`.** In an execution that reaches every time, with permanent corruption, blocks and Goldfish
votes delivered within `Δ S` from `GST ≤ voteTime S s`, blocks reaching a validator only after
their parents, nobody voting in an honest validator's name, and roots naming blocks among what
honest validators hold up to the support cutoff of slot `s`: take a set `Hs` of members of slot
`s`'s committee honest at `supportCutoff S (s + 1)`, each of whose slot-`s` vote for a block
`H u` it holds before the vote time of `s` is on the wire at its tick, `H u` compatible with `B`;
fewer than twice `Hs` validators with a slot-`s` vote in `v`'s pool before
`supportCutoff S (s + 1)`; `v` awake and honest from the duty window of slot `s + 1` to that
cutoff, its finalized block before it compatible with `B`. Then the confirmation `v`'s update at
that cutoff saves for slot `s`, when there is one, is compatible with `B`.

Why: when `v`'s finalized block is `B` or an ancestor of `B`, every member's vote reaches `v`'s
pool before the support cutoff of `s` as its voter's only vote of the slot, and its block reaches
`v`'s tree, so the frame's block named by the vote's head is `H u`; Lemma 77c. When `B` is an
ancestor of `v`'s finalized block, the saved block descends from that block.

 every hypothesis is read.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the voters; `H`: their blocks; `B`:
  the block; `v`: the validator whose update it is.

Read aloud: when more than half of the counted voters are honest validators whose votes do not
conflict with `B`, and `v`'s finality gadget has not left `B`'s side, no confirmation `v` saves
conflicts with `B`. -/
theorem lem78c_update_confirmation_compatible_of_voter_majority (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- a validator in the adversary set stays in it
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- roots name blocks among what honest validators hold up to the support cutoff of `s`
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    -- the network is synchronous by the vote time of `s`
    (hGST : GST ≤ voteTime S s)
    -- each member of `Hs` is a committee member of `s`, honest at the cutoff of `s + 1`, whose
    -- slot-`s` vote for `H u`, a block it holds, is on the wire, `H u` compatible with `B`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ (H u).compatible B = true)
    -- fewer than twice `Hs` validators have a slot-`s` vote in `v`'s pool
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    -- `v` is awake and honest from the duty window of `s + 1` to its support cutoff
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `v`'s finalized block before that cutoff is compatible with `B`
    (hF : (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true) :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      C'.compatible B = true :=
  GoldilocksCorrectness.Proofs.Executions.lem78c_update_confirmation_compatible_of_voter_majority
    S Sched x GST s Hs H B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hv hF

/-- **Lemma 78c with the delivery premises up to the support cutoff of `s`.** Lemma 78c with
`SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at the bound `supportCutoff S s`, the deadline of
the slot-`s` votes and blocks its proof reads.

Why: Lemma 78c's proof with the deliveries' twins before the bound.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the voters; `H`: their blocks; `B`:
  the block; `v`: the validator whose update it is.

Read aloud: Lemma 78c, with the network synchronous only for what is due by the support cutoff of
slot `s`. -/
theorem lem78c_update_confirmation_compatible_of_voter_majority_upTo (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- a validator in the adversary set stays in it
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes due by the support cutoff of `s` are delivered within `Δ S`
    -- after `GST`
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    -- roots name blocks among what honest validators hold up to the support cutoff of `s`
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    -- the network is synchronous by the vote time of `s`
    (hGST : GST ≤ voteTime S s)
    -- each member of `Hs` is a committee member of `s`, honest at the cutoff of `s + 1`, whose
    -- slot-`s` vote for `H u`, a block it holds, is on the wire, `H u` compatible with `B`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ (H u).compatible B = true)
    -- fewer than twice `Hs` validators have a slot-`s` vote in `v`'s pool
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    -- `v` is awake and honest from the duty window of `s + 1` to its support cutoff
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `v`'s finalized block before that cutoff is compatible with `B`
    (hF : (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true) :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      C'.compatible B = true :=
  GoldilocksCorrectness.Proofs.Executions.lem78c_update_confirmation_compatible_of_voter_majority_upTo
    S Sched x GST s Hs H B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hv hF

end GoldilocksCorrectness.Statements.Executions
