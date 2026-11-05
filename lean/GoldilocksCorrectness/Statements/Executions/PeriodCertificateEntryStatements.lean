module
public import GoldilocksCorrectness.Proofs.Executions.PeriodCertificateEntry

@[expose] public section

/-! a kit statement, new, no landed statement changes. Proved in
`GoldilocksCorrectness/Proofs/Executions/PeriodCertificateEntry.lean`.

- `cert_entry_held_by_attester`: a progress certificate on a chain an honest validator holds has
  an honest attester, an updater of a slot `sₐ` whose tick at `supportCutoff S (sₐ + 1)` sent it;
  the certified block is an ancestor of that update's fast block, and the attester held it before
  that tick.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (ProgressCertOn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Kit fact K1: the certified entry is held by an honest attester at its tick.** Take a block
`Y` that `w`, outside the adversary set at the time after `j` steps, holds after `j` steps, and a
progress certificate on the chain of `Y` at the height `h` naming the block `T`, an ancestor of
`Y` or `Y`. When fewer than a quorum of validators have been in the adversary set up to that time,
and roots name blocks among the blocks honest validators hold by then: some validator `uₐ` is an
updater of some slot `sₐ`, outside the adversary set at `supportCutoff S (sₐ + 1)`, a time at most
the time after `j` steps; some fast block `F` of the state right after `uₐ`'s tick at that time
has `T` as an ancestor or is `T`; and `uₐ` held `T` in its FG tree before that tick.

Why: some member `u` of the certificate's quorum is honest up to the time after `j` steps; its
attestation is in its record (Lemma 74), so its tick sent an attestation with that content at an
earlier step (`record_content_sent_step`). That tick is at `supportCutoff S (sₐ + 1)` for an
updater `u` of `sₐ`, and the attestation names, by root, the entry `E` of the chain state of a
fast block `F` of that update, with `E` an ancestor of `F` and `F` held before the tick
(`attest_source_fast_block_updater_inTree`). `E` and `T` have one root and are held by honest
validators by the time after `j` steps, so `E = T`.

 every
hypothesis is read. The height `h` is not compared with a threshold here (`cert_entry_at_slot`'s
`hOld` is not taken).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `j`: the step; `w`: the holder;
  `Y`: the held block; `T`: the block the certificate names; `h`: its height.

Read aloud: a progress certificate on a chain an honest validator holds has an honest attester, an
updater of a slot `sₐ` whose tick at `supportCutoff S (sₐ + 1)`, at or before the time after `j`
steps, sent it; the certified block `T` is an ancestor of that update's fast block `F`, or `F`,
and the attester held `T` before that tick. -/
theorem cert_entry_held_by_attester (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (j : ℕ) (w : V) (Y T : Block V) (h : Height)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- a validator in the adversary set stays in it
    (hMono : Sched.MonotoneCorruption)
    -- what honest validators sign is never forged
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum have been in the adversary set up to the time after `j` steps
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    -- roots name blocks among the blocks honest validators hold by that time
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time)
    -- `w` is outside the adversary set at that time
    (hw : w ∉ Sched.adv (x[j].time : Int))
    -- `w` holds `Y` after `j` steps
    (hY : Y ∈ (x[j][w].st).S.T)
    -- `T` is an ancestor of `Y`, or `Y`
    (hTY : T.AncestorEq Y)
    -- the chain of `Y` carries a progress certificate at `h` naming `T`
    (hJ : ProgressCertOn Y h T) :
    ∃ (sₐ : ℕ) (uₐ : V) (F : Block V), supportCutoff S (sₐ + 1) ≤ x[j].time ∧
      uₐ ∈ updaterAt S Sched sₐ ∧ uₐ ∉ Sched.adv ((supportCutoff S (sₐ + 1) : ℕ) : Int) ∧
      F ∈ (stateBefore x (supportCutoff S (sₐ + 1) + 1) uₐ).A.fast_blocks ∧ T.AncestorEq F ∧
      T ∈ (stateBefore x (supportCutoff S (sₐ + 1)) uₐ).S.T :=
  GoldilocksCorrectness.Proofs.Executions.cert_entry_held_by_attester S Sched x j w Y T h hDiv
    hMono hU hAdvQ hRoots hw hY hTY hJ

end GoldilocksCorrectness.Statements.Executions
