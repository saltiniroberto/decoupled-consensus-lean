module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89r
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rQuietRound
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89rStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/Lemma89rStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 89r, the theorem of
the same name of `Record/Restated/Proofs/Executions/Lemma89r.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (BoxOne BoxTwo ChainStatesComputed
  CountedVotes HeightCacheBounds)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts honestActiveAt)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

open Classical in
/-- **Lemma 89r, a quiet round of the phase.** Write `s = r · R` for the round's first slot, `B`
for the honest proposal `p` put on the wire at its start, `anchor_p` for `p`'s anchor then, and
`s''` for a slot whose start is at least `Δ_F` after the action time `M.supportCutoff S.C (s + 1)`
(`hs''`: an attestation sent then is delivered before slot `s''` starts) and whose proposer `q`
put `B'` on the wire at its start. In an
execution with the eight execution assumptions, attestations delivered within `Δ_F` after `GST`,
and unforgeability: if the round is quiet relative to its own confirmations
(`QuietRoundOnConfirmations`); the member sets `Hon M s'` of the slots from `s − 1` to `s'' − 1`
shrink, each member of `Hon M s'` awake and honest from the duty window's start of slot `s'` to the
support cutoff of slot `s' + 1`, with a committee majority in `Hon M s'`; `q` is a member of
`Hon M (s'' − 1)` and the proposer of slot `s''`; at slot `s − 1` the chain invariant and the lock
invariant hold at `Hon M (s − 1)` for a family `𝓒` holding `anchor_p`; and before the start of slot
`s`, `p`'s frame has, for every block `C` of `𝓒`, a viable head that is `C` or a descendant of
`C` — then either `p` held, before the start of slot `s`, a block with `B`'s root, or `B'` is on
`B`'s chain and raises the height or carries the progress quorum within `δt` of `B`'s entry (the
height rising, and `B'`'s justified block `B`'s entry when its parent is at `B`'s height, when no
member sent anything at `B`'s height before the action time), every member of `Hon M s` saves `B`
as its confirmation of slot `s`, and both invariants hold at slot `s'' − 1` at `Hon M (s'' − 1)`
for `𝓒` extended by `B` and by every confirmation of a slot `s'` from `s − 1` to `s'' − 2` saved
by a member of `Hon M s'`, the members of the slot's own set, the updaters of the slot in the phase
. The adversary premise is read up to the action time `M.supportCutoff S.C (s + 1)` of
slot `s` only: fewer than a third of the validators have been in the adversary set up to it, and
the member set `Hon M s` has at least `quorum V` validators.

Why: `p`'s walk passes every block of `𝓒` it starts before (`proposal_parent_extends_majority_block`
with `p`'s viable heads), so every block of `𝓒` is `B`'s parent or an ancestor of it, which gives
the round theorem's lock condition; the `head_height_floor` of each member at the vote time is at
least `p`'s by delivery and Lemma 89a; the next proposer's frame on `B`'s chain comes from the last
clause of the quiet round and the chain invariant relative to `B`, which puts `B` on the chain of
every confirmation of slot `s'' − 2`. The two invariants are carried slot by slot from slot
`s − 1` by the chain step `lem89s_chain_step` with the updaters `Hon M s'` of each slot `s'` and
the lock invariant's step at each member of `Hon M (s' + 1)`, whose frame conditions relative to the
confirmations are the quiet round's clause relative to the confirmations: that clause, and not one
relative to `B` alone, is what the chain step reads, since a member's confirmation may descend from
`B` strictly and a frame relative to `B` says nothing relative to a strict descendant of `B`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `r`: the round; `s`: its first slot; `s''`: the slot of `q`'s proposal;
- `Hon M s'`: the member set of slot `s'`; `𝓒`: the family; `B`, `B'`: the two proposals; `p`, `q`:
  their proposers.

Read aloud: in a quiet round of the phase relative to its own confirmations, with the proposer's
frame reaching the family's chain, the next honest proposal extends the round's proposal and makes
progress, every member saves the round's proposal, and both invariants hold at the slot before the
next opening for the family, the proposal and every confirmation the round saved.



Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: the round theorem
`lem80wq_round_height_advances_steps` at slot `s''` reads blocks held up to it, and the chain
steps of the slots before `s'' − 1` up to their support cutoffs, at most it. -/
theorem lem89r_quiet_round (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST r s s'' : ℕ) (Hon : ℕ → Finset V)
    (𝓒 : Block V → Prop) (B B' : Block V) (p q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of the support cutoff of slot `s'' − 1`, and up to the real time of every
    -- validator's tick to a clock value at most that cutoff
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s'' - 1)))
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- fewer than a third of the validators have been in the adversary set up to the real time of each member's own
    -- tick to the support cutoff of slot `s + 1` (rule R3;)
    (hThird : ∀ v ∈ Hon s, A.AdversaryFewerThanThirdUntil x (validator_count V)
        (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s - 1 ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` from `s − 1` to `s'' − 1`, the members of slot `s'` are honest active validators of slot
    -- `s'` (, amending on this statement;
    -- are its instances at `s − 1` and `s'' − 1`)
    (hHon : ∀ s', s - 1 ≤ s' → s' < s'' → Hon s' ⊆ honestActiveAt M S A x s')
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the member set of the first slot has at least a quorum of validators
    (hQuorum : quorum V ≤ (Hon s).card)
    -- the committee of every slot of the round has a majority in that slot's set
    (hCommittees : ∀ s', s - 1 ≤ s' → s' < s'' →
      (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon s').card)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer of slot `s` is outside the adversary set at each member's tick to the vote time of slot `s`
    --
    (hpHon : ∀ w ∈ Hon s, p ∉ A.corrupted (x.tickStep w (M.voteTime S.C s)))
    -- `q` is a member of the last slot's set; `p` and `q` are the proposers of slots `s`, `s''`
    (hq : q ∈ Hon (s'' - 1)) (hps : S.P.proposer s = p) (hqProp : S.P.proposer s'' = q)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `p` put `B` on the wire at its tick at the start of slot `s`, and `q` put `B'` at slot `s''`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hQuiet : QuietRoundOnConfirmations M S A x Hon B s s'')
    (hChain : ChainInvFor M S A x (Hon (s - 1)) 𝓒 (s - 1))
    (hFamLocks : ∀ w ∈ Hon (s - 1), LiveLocksOnFamilyAt M S A x 𝓒 (s - 1) w)
    -- the family holds `anchor_p`
    (hAnchor : 𝓒
        (M.get_anchor (x.tickInput p (M.slotStart S.C s)) ((M.slotStart S.C s : ℕ) : Int)))
    -- `p`'s frame before the start of slot `s` has, for every block `C` of the family, a viable
    -- head that is `C` or a descendant of `C`
    (hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree,
        W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).viable_heads ∧ C.AncestorEq W) :
    (∃ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root = B.root) ∨
    (B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt ∧
        ∃ Q : Finset V, quorum V ≤ Q.card ∧ Q ⊆ (M.chainStateOf S.C B').progress)) ∧
    ((∀ u ∈ Hon s, ∀ b ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) u).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) ∧
    (∀ v ∈ Hon s,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) ∧
    ChainInvFor M S A x (Hon (s'' - 1)) (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C)
      (s'' - 1) ∧
    (∀ w ∈ Hon (s'' - 1), LiveLocksOnFamilyAt M S A x (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C)
      (s'' - 1) w)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89r_quiet_round M F U Fx) S A x R GST r s s'' Hon 𝓒 B B'
    p q E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hRoots hRootsTick hParent hs hs1 hs'' hGST hGSTF hThird hHonMono hHon hHold42 hHoldV hHoldF hQuorum hCommittees
    tStart htStart hp hHoldP hpHon hq hps hqProp hqWin hPropose hPropose' hQuiet hChain hFamLocks hAnchor hFrameP

end GoldilocksCorrectness.Record.Statements.Executions

