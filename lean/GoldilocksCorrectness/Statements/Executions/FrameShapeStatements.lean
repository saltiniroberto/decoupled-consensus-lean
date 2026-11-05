module
public import GoldilocksCorrectness.Proofs.Executions.FrameShape

@[expose] public section

/-!
# The vote, the confirmation and the attestation over a frame shape

The audited statements of Lemmas 24, 29 and 55 with their finality-gadget hypotheses replaced by
the root and `head_height_floor` (the least chain-state height a viable block may have) of the frames they read (`FrameShape`), proved in
`GoldilocksCorrectness/Proofs/Executions/FrameShape.lean`:

- Lemma 59, `lem59_goldfish_vote_names_honest_proposal_frame`: the next slot's honest vote names
  the honest proposal;
- Lemma 60, `lem60_update_confirmation_fast_locks_frame`: the confirmation update makes a block a
  voter majority voted for fast and locks it;
- the kit theorem `lem61_frame_hypotheses` and Lemma 61, `lem61_honest_validator_attests_frame`:
  every honest validator with the honest proposal as its source attests for its height.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes FrameShape)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## Lemma 59 -/

/-- **Lemma 59, the next slot's honest vote names the honest proposal, over a frame shape.** Under
the hypotheses of Lemma 24 (`lem24_goldfish_vote_names_honest_proposal_composed`) other than those
on the two frames, and: `p`'s frame before the start `t₁` of slot `s + 1` has the root `ρ_p` and
`head_height_floor` equal to `φ`, and `w`'s frame before the vote time `t₃` of slot `s + 1` has the root `ρ_w` and the same
`head_height_floor` equal to `φ`; some block of `p`'s tree that is `X` or a descendant of `X`, and `ρ_p` or a descendant of
`ρ_p`, has a chain-state height at least `φ`; `ρ_w` is `B` or an ancestor of `B`; and `B`'s
chain-state height is at least `φ` — then `w`'s vote names `B`.

Why: each finalized block is its frame's root or an ancestor of it (Lemma 46); Lemma 56 makes the
block of `p`'s tree a viable head of `p`'s frame and `B` viable at `w`, whose tree holds `B`
(Lemmas 22a and 22), with the chain state `B`'s own (Lemma 11); the two `head_height_floor` values are `φ`. Lemma 24
concludes.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`: their common `head_height_floor`.

Read aloud: the two frames have roots `ρ_p`, `ρ_w` and one `head_height_floor` value `φ`; some accepted block of `p`
on `ρ_p`'s chain descending from `X` reaches `head_height_floor`; `w`'s root is on `B`'s chain; and `B`
reaches `head_height_floor` — then `w`'s vote names `B`.



Roots name blocks until `voteTime S (s + 1)`: Lemma 22 and Lemma 24, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`. -/
theorem lem59_goldfish_vote_names_honest_proposal_frame (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    -- `p`'s frame before `t₁` has the root `ρ_p` and `head_height_floor` equal to `φ`
    (hShapeP : FrameShape (stateBefore x (slotStart S (s + 1)) p).S ρ_p φ)
    -- `w`'s frame before `t₃` has the root `ρ_w` and the same `head_height_floor` value `φ`
    (hShapeW : FrameShape (stateBefore x (voteTime S (s + 1)) w).S ρ_w φ)
    -- some accepted block of `p` on `ρ_p`'s chain, `X` or a descendant of `X`, reaches `head_height_floor`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
      X.AncestorEq W ∧ ρ_p.AncestorEq W ∧ φ ≤ (chainStateOf S.C W).h)
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    -- `w`'s root is `B` or an ancestor of `B`
    (hRootW : ρ_w.AncestorEq B)
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B`'s chain-state height reaches `head_height_floor`
    (hBHeight : φ ≤ (chainStateOf S.C B).h) :
    vote.head = B.root :=
  GoldilocksCorrectness.Proofs.Executions.lem59_goldfish_vote_names_honest_proposal_frame S Sched
    x GST s Hs H X B p w vote ρ_p ρ_w φ hDiv hMono hSync hCatch hRoots hParent hOwner hGST
    hHs hVoters hp hw hPropose hSend hOnly hRootNew hShapeP hShapeW hHeadP hApX hRootW hLocksW
    hBHeight

/-! ## Lemma 60 -/

/-- **Lemma 60, the confirmation update makes a voter-majority block fast and locks it, over a
root.** Under the hypotheses of Lemma 29
(`lem29_update_confirmation_fast_locks_voter_majority_block`) with "`v`'s finalized block before
the support cutoff `t₂` of slot `s + 1` is `B` or an ancestor of `B`" replaced by "the root of
`v`'s fork choice before `t₂` is `B` or an ancestor of `B`", `v`'s node state before `t₂ + 1` has
`B` among its fast blocks and the lock entry on `B` with the deadline
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`.

Why: the finalized block is the root of the fork choice or an ancestor of it (Lemma 46); Lemma 29
concludes.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `B`: the block their votes are for;
- `v`: the validator running the confirmation update of slot `s`.

Read aloud: when the root of `v`'s fork choice is `B` or an ancestor of `B`, Lemma 29's conclusion
holds.



Roots name blocks until `supportCutoff S s`: Lemma 29, which the proof calls, takes blocks as
held up to the support cutoff of slot `s`. -/
theorem lem60_update_confirmation_fast_locks_frame (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    -- the slot-`s` committee is at most twice `Hs`
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the root of `v`'s fork choice before `t₂` is `B` or an ancestor of `B`
    (hRootV : (get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S).AncestorEq B) :
    B ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries :=
  GoldilocksCorrectness.Proofs.Executions.lem60_update_confirmation_fast_locks_frame S Sched x GST
    s Hs B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hHalf hBne hv
    hRootV

/-! ## Lemma 61 -/

/-- **Kit theorem of Lemma 61, Lemma 55's frame hypotheses from a frame shape.** When `v`'s frame
before the support cutoff `t₂` of slot `s + 1` has the root `ρ` and `head_height_floor` equal to `φ`, `ρ` is `B` or an
ancestor of `B`, `B`'s chain-state height `H` is at least `φ`, `B` is in `v`'s tree, and `v`'s cache
`h_j` is less than `H`, or `v`'s record holds no lock at `H`, or it locks the root `T` of `B`'s
`T_h` at `H`: then `B` is in `v`'s viable tree, and `v`'s record holds no lock at `H`, or the lock `T` with every attestation it
sent at `H` naming `T`.

Why: `B` is its own viable head (Lemma 56, with Lemma 46 and Lemma 11); a cache `h_j` less than
`H` leaves no lock at `H`, and a lock at `H` has every attestation sent at `H` name it (Lemma 57).


The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the update's;
- `B`: the block; `v`: the validator; `ρ`: the root of `v`'s fork choice; `φ`: its `head_height_floor`.

Read aloud: the frame at `v` has its root on `B`'s chain and its `head_height_floor` at most `B`'s height, and
`v` holds no lock at `B`'s height on another block — then Lemma 55's viable-tree and record
hypotheses hold.

 -/
theorem lem61_frame_hypotheses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (v : V) (ρ : Block V) (φ : Height)
    -- `v`'s frame before `t₂` has the root `ρ` and `head_height_floor` equal to `φ`
    (hShape : FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S ρ φ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRootV : ρ.AncestorEq B)
    -- `B`'s chain-state height is at least `head_height_floor`
    (hBHeight : φ ≤ (chainStateOf S.C B).h)
    -- `B` is in `v`'s tree before `t₂`
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T)
    -- `v`'s cache `h_j` is less than `B`'s height, or `v`'s record holds no lock at that height,
    -- or it locks `B`'s `T_h` at that height
    (hLockBox : (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root) :
    B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  GoldilocksCorrectness.Proofs.Executions.lem61_frame_hypotheses S Sched x s B v ρ φ hShape hRootV
    hBHeight hBin hLockBox

/-- **Lemma 61, every honest validator with the honest proposal as its source attests for its
height, over a frame shape.** Write `s` for the first slot of round `r`, `a_r` for its action time,
which is the support cutoff of slot `s + 1`, `H` for the height of `B`'s chain state and `T` for the
root of its `T_h`. Under the hypotheses of Lemma 55 (`lem55_honest_validator_attests_for_height`)
with its viable-tree and record hypotheses replaced by: `v`'s frame before `a_r` has the root `ρ`
and `head_height_floor` equal to `φ`; `ρ` is `B` or an ancestor of `B`; `H` is at least `φ`; `B` is in `v`'s tree
before `a_r`; and `v`'s cache `h_j` is less than `H`, or `v`'s record holds no lock at `H`, or it
locks `T` at `H` — then `v`
put at its tick at `a_r` an attestation of `v` at `H` naming `T` on the wire, or its record before
`a_r` already holds one sent at `H` naming `T`.

Why: the kit theorem `lem61_frame_hypotheses` gives Lemma 55's viable-tree and record hypotheses;
Lemma 55 concludes.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `A'`: the answer of `v`'s update of slot `s + 1`;
- `ρ`: the root of `v`'s fork choice; `φ`: its `head_height_floor`.

Read aloud: the frame at `v` has root `ρ`, on `B`'s chain, and `head_height_floor` at most `B`'s height; the
cache `h_j` is less than `B`'s height, or there is no lock at that height, or the lock there is
`B`'s `T_h` — then Lemma 55's
conclusion.

 -/
theorem lem61_honest_validator_attests_frame (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (r s : ℕ) (B : Block V) (v : V) (A' : ACState V) (ρ : Block V) (φ : Height)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `s` is the first slot of round `r`, so the action time of `r` is the support cutoff
    -- of slot `s + 1`
    (hs : s = r * S.C.R)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to `a_r`
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `v`'s update of slot `s + 1` at `a_r` answers `A'`
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    -- `A'` saves `B` as the confirmation of slot `s`
    (hSaved : A'.saved_confirmation s = some B)
    -- `B` is a fast block of `A'`
    (hFast : B ∈ A'.fast_blocks)
    -- every lock entry of `A'` live at `a_r` is on `B` or an ancestor of `B`
    (hLocks : ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `v`'s frame before `a_r` has the root `ρ` and `head_height_floor` equal to `φ`
    (hShape : FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S ρ φ)
    -- `ρ` is `B` or an ancestor of `B`
    (hRootV : ρ.AncestorEq B)
    -- `B`'s chain-state height is at least `head_height_floor`
    (hBHeight : φ ≤ (chainStateOf S.C B).h)
    -- `B` is in `v`'s tree before `a_r`
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T)
    -- `v`'s cache `h_j` is less than `H`, or `v`'s record holds no lock at `H`, or it locks `T`
    -- at `H`
    (hLockBox : (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root) :
    (∃ (i : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = v ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root) ∨
    (∃ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
      b.h = (chainStateOf S.C B).h ∧ b.T = (chainStateOf S.C B).T_h.root) :=
  GoldilocksCorrectness.Proofs.Executions.lem61_honest_validator_attests_frame S Sched x r s B v A'
    ρ φ hDiv hMono hs hv hUpdate hSaved hFast hLocks hShape hRootV hBHeight hBin hLockBox

end GoldilocksCorrectness.Statements.Executions
