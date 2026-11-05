module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89r

@[expose] public section

/-!
# Lemma 89r: a quiet round of the phase

The audited statement, proved in `GoldilocksCorrectness/Proofs/Executions/Lemma89r.lean`:

- Lemma 89r, `lem89r_quiet_round`: in a round quiet relative to its own confirmations
  (`QuietRoundOnConfirmations`) whose proposer's frame reaches the family's chain, the next honest
  proposal is on the round's proposal's chain and raises the height or carries the progress
  quorum, every member saves the proposal, and the chain invariant and the lock invariant are
  carried to the slot before the next opening, for one family: the family of the round's first
  slot, the proposal, and every confirmation of a slot from `s − 1` to `s'' − 2` that a member of
  the slot's own set saved.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 89r, a quiet round of the phase.** Write `s = r · R` for the round's first slot, `B`
for the honest proposal `p` put on the wire at its start, `anchor_p` for `p`'s anchor then, and
`s''` for a slot whose start is at least `Δ_F` after the action time `supportCutoff S (s + 1)`
(`hs''`: an attestation sent then is delivered before slot `s''` starts) and whose proposer `q`
put `B'` on the wire at its start. In an
execution with the eight execution assumptions, attestations delivered within `Δ_F` after `GST`,
and unforgeability: if the round is quiet relative to its own confirmations
(`QuietRoundOnConfirmations`); the member sets `Hon s'` of the slots from `s − 1` to `s'' − 1`
shrink, each member of `Hon s'` awake and honest from the duty window's start of slot `s'` to the
support cutoff of slot `s' + 1`, with a committee majority in `Hon s'`; `q` is a member of
`Hon (s'' − 1)` and the proposer of slot `s''`; at slot `s − 1` the chain invariant and the lock
invariant hold at `Hon (s − 1)` for a family `𝓒` holding `anchor_p`; and before the start of slot
`s`, `p`'s frame has, for every block `C` of `𝓒`, a viable head that is `C` or a descendant of
`C` — then either `p` held, before the start of slot `s`, a block with `B`'s root, or `B'` is on
`B`'s chain and raises the height or carries the progress quorum within `δt` of `B`'s entry (the
height rising, and `B'`'s justified block `B`'s entry when its parent is at `B`'s height, when no
member sent anything at `B`'s height before the action time), every member of `Hon s` saves `B`
as its confirmation of slot `s`, and both invariants hold at slot `s'' − 1` at `Hon (s'' − 1)`
for `𝓒` extended by `B` and by every confirmation of a slot `s'` from `s − 1` to `s'' − 2` saved
by a member of `Hon s'`, the members of the slot's own set, the updaters of the slot in the phase
. The adversary premise is read up to the action time `supportCutoff S (s + 1)` of
slot `s` only: fewer than a third of the validators have been in the adversary set up to it, and
the member set `Hon s` has at least `quorum V` validators.

Why: `p`'s walk passes every block of `𝓒` it starts before (`proposal_parent_extends_majority_block`
with `p`'s viable heads), so every block of `𝓒` is `B`'s parent or an ancestor of it, which gives
the round theorem's lock condition; the `head_height_floor` of each member at the vote time is at
least `p`'s by delivery and Lemma 89a; the next proposer's frame on `B`'s chain comes from the last
clause of the quiet round and the chain invariant relative to `B`, which puts `B` on the chain of
every confirmation of slot `s'' − 2`. The two invariants are carried slot by slot from slot
`s − 1` by the chain step `lem89s_chain_step` with the updaters `Hon s'` of each slot `s'` and
the lock invariant's step at each member of `Hon (s' + 1)`, whose frame conditions relative to the
confirmations are the quiet round's clause relative to the confirmations: that clause, and not one
relative to `B` alone, is what the chain step reads, since a member's confirmation may descend from
`B` strictly and a frame relative to `B` says nothing relative to a strict descendant of `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `r`: the round; `s`: its first slot; `s''`: the slot of `q`'s proposal;
- `Hon s'`: the member set of slot `s'`; `𝓒`: the family; `B`, `B'`: the two proposals; `p`, `q`:
  their proposers.

Read aloud: in a quiet round of the phase relative to its own confirmations, with the proposer's
frame reaching the family's chain, the next honest proposal extends the round's proposal and makes
progress, every member saves the round's proposal, and both invariants hold at the slot before the
next opening for the family, the proposal and every confirmation the round saved.




Roots name blocks until `supportCutoff S (s'' - 1)`: the round theorem
`lem80wq_round_height_advances_steps` at slot `s''` reads blocks held up to it, and the chain
steps of the slots before `s'' − 1` up to their support cutoffs, at most it. -/
theorem lem89r_quiet_round (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST r s s'' : ℕ) (Hon : ℕ → Finset V)
    (𝓒 : Block V → Prop) (B B' : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- fewer than a third of the validators have been in the adversary set up to the action time
    -- of slot `s`
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) ((supportCutoff S (s + 1) : ℕ) : Int))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s - 1 ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s - 1 ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the member set of the first slot has at least a quorum of validators
    (hQuorum : quorum V ≤ (Hon s).card)
    -- the committee of every slot of the round has a majority in that slot's set
    (hCommittees : ∀ s', s - 1 ≤ s' → s' < s'' →
      (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon s').card)
    -- `p` is awake from the vote time of slot `s − 1` to the start of slot `s`, and honest up to
    -- the vote time of slot `s`
    (hpAwake : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s → p ∈ Sched.awake (t : Int))
    (hpHon : HonestThroughTime Sched ((voteTime S s : ℕ) : Int) p)
    -- `q` is a member of the last slot's set; `p` and `q` are the proposers of slots `s`, `s''`
    (hq : q ∈ Hon (s'' - 1)) (hps : S.P.proposer s = p) (hqProp : S.P.proposer s'' = q)
    -- `p` put `B` on the wire at its tick at the start of slot `s`, and `q` put `B'` at slot `s''`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hQuiet : QuietRoundOnConfirmations S Sched x Hon B s s'')
    (hChain : ChainInvFor S Sched x (Hon (s - 1)) 𝓒 (s - 1))
    (hFamLocks : ∀ w ∈ Hon (s - 1), LiveLocksOnFamilyAt S Sched x 𝓒 (s - 1) w)
    -- the family holds `anchor_p`
    (hAnchor : 𝓒 (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)))
    -- `p`'s frame before the start of slot `s` has, for every block `C` of the family, a viable
    -- head that is `C` or a descendant of `C`
    (hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s) p).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S s) p).S).viable_heads ∧ C.AncestorEq W) :
    (∃ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root = B.root) ∨
    (B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt ∧
        ∃ Q : Finset V, quorum V ≤ Q.card ∧ Q ⊆ (chainStateOf S.C B').progress)) ∧
    ((∀ u ∈ Hon s, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) ∧
    (∀ v ∈ Hon s,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B) ∧
    ChainInvFor S Sched x (Hon (s'' - 1)) (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C)
      (s'' - 1) ∧
    (∀ w ∈ Hon (s'' - 1), LiveLocksOnFamilyAt S Sched x (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C)
      (s'' - 1) w)) :=
  GoldilocksCorrectness.Proofs.Executions.lem89r_quiet_round S Sched x GST r s s'' Hon
    𝓒 B B' p q hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hs hs1 hs''
    hGST hThird hHonMono hHon hQuorum hCommittees hpAwake hpHon hq hps hqProp hPropose
    hPropose' hQuiet hChain hFamLocks hAnchor hFrameP

end GoldilocksCorrectness.Statements.Executions
