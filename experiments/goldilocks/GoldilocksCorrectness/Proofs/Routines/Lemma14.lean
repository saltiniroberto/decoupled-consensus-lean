module
public import GoldilocksCorrectness.Proofs.Routines.Lemma13
public import GoldilocksCorrectness.Proofs.Routines.Node
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.State
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Lemma 14: the vote a tick sends is the end of the Goldfish fork choice

The proof of `lem14_tick_vote_walk`, stated in
`GoldilocksCorrectness/Statements/Routines/TickStatements.lean`.

The route: a Goldfish vote a tick sends was sent by its tick of the available chain (the proposal
and the attestation duty send none, `propose_block_sends`, `attest_sends`), in the `if` at the
vote time, so the duty test passed; there the revocation answered some `A'` and the Goldfish vote
duty ran on `A'`, and the vote it sent is, in the `if` on the committee, the vote for the root of
the block its fork choice reached (`goldfish_vote_walk`, `ac_on_tick_walk`, `tick_walk`). The
revocation keeps the pool and the stamps, so the counted sets and the voter's tree read on `A'`
are those read on `n.A` (`countedVotes_of_keepsVotes`, `voter_block_tree_of_keepsVotes`); the
lock entries are Lemma 13's route (`ac_on_tick_revokes`), and the revocation's answer is unique.

## The relation

- `GoldfishVoteWalk C P A Φ t v vote`: `vote` is the vote the Goldfish vote duty of `v` at `t` on
  `A` sends: `v` is a committee member of the slot of `t`, and `vote` names the root of the block
  the Goldfish fork choice reaches from the anchor of `A`, through the viable tree of the voter's
  tree, counting the sets `CountedVotes` describes.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (propose_block_sends attest_sends tick_sends
  record_awake_frame)
open GoldilocksCorrectness.Proofs.Routines (KeepsVotes revoke_locks_keepsVotes)
open GoldilocksCorrectness.Proofs.Routines (DREBPost DREPost DREBEmits NoVote noVote_nil
  noVote_block_append noVote_attest_append)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## A lifted step whose answer the continuation reads -/

/-! ## The relation -/

/-- `GoldfishVoteWalk C P A Φ t v vote`: `v` is a member of the committee of the slot of `t`, and
for some sets `votes`, `support_votes` counted on `A` and `Φ` (`CountedVotes`), some answer `vbt`
of the voter's tree and some answer `H` of the Goldfish fork choice from the anchor
`get_anchor A Φ t` through `viable_tree Φ vbt`, `vote` is `v`'s vote for the slot of `t` naming
`H.root`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state the duty runs on; `Φ`: the frame;
  `t`: the time; `v`: the voter; `vote`: the vote.

Read aloud: `vote` is the vote `v`'s Goldfish vote duty at `t` on `A` casts. -/
def GoldfishVoteWalk (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V) (t : Time)
    (v : V) (vote : GoldfishVote V) : Prop :=
  v ∈ P.committee (C.slot t) ∧
    ∃ (votes support_votes : Finset (GoldfishVote V)) (vbt : Finset (Block V)) (H : Block V),
      CountedVotes C A Φ (C.slot t) votes support_votes ∧
      voter_block_tree C A Φ (C.slot t) = .ok vbt ∧
      goldfish_fork_choice C Φ t (get_anchor A Φ t) (viable_tree Φ vbt) votes support_votes
        (C.slot t - 1) = .ok H ∧
      vote = GoldfishVote.mk (val_index := v) (slot := C.slot t) (head := H.root)

/-! ## The routines -/

/-- Every Goldfish vote the Goldfish vote duty sends is the vote its walk casts.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the voter.

Read aloud: the duty votes, as a committee member, for the root of its fork choice's answer. -/
theorem goldfish_vote_walk (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) :
    DREBEmits (fun l => ∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ l →
        GoldfishVoteWalk C P A Φ t v vote)
      (goldfish_vote C P A Φ t v) := by
  simp only [goldfish_vote]
  refine DREBEmits.liftM_bind (fun votes₀ h₀ => ?_)
  refine DREBEmits.liftM_bind (fun sv₀ h₁ => ?_)
  refine DREBEmits.liftM_bind (fun isv h₂ => ?_)
  refine DREBEmits.liftM_bind (fun vbt h₃ => ?_)
  refine DREBEmits.liftM_bind (fun H h₄ => ?_)
  refine DREBEmits.ite (fun hv => ?_)
    (fun _ => DREBEmits.pure (fun _ h => absurd h List.not_mem_nil))
  refine (DREBEmits.broadcast_then _ (fun _ => DREBEmits.pure rfl)).mono ?_
  rintro _ rfl vote hvote
  rw [List.mem_singleton] at hvote
  injection hvote with hvote
  refine ⟨hv, votes₀ ∪ included_votes Φ (C.slot t), sv₀ ∪ isv, vbt, H, ⟨fun vote' => ?_,
    fun vote' => ?_⟩, h₃, h₄, hvote⟩
  · rw [Finset.mem_union, mem_beforeCutoff_iff h₀]
  · rw [Finset.mem_union, mem_early_iff h₁, mem_beforeCutoff_iff h₀,
      mem_of_filterM_eq_ok_iff _ _ _ h₂, and_assoc]

/-- Every Goldfish vote the tick of the available chain sends was sent at the vote time of its
slot with its vote test passed, by the Goldfish vote duty run on the answer `A'` of the revocation
of that slot on `expireLocks A t`, and is the vote that duty's walk casts.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the two wake tests.

Read aloud: the tick of the available chain votes only after revoking, as its walk on the revoked
AC state says. -/
theorem ac_on_tick_walk (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) :
    DREBEmits (fun l => ∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ l →
        b = true ∧ ∃ A' : ACState V,
          revoke_locks P (expireLocks A t) Φ t (C.slot t) = .ok A' ∧
            GoldfishVoteWalk C P A' Φ t v vote)
      (ac_on_tick C P A Φ t v b b') := by
  simp only [ac_on_tick]
  refine DREBEmits.ite (fun hc => ?_) (fun _ => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine DREBEmits.liftM_bind (fun A' hA' => ?_)
    refine (DREBEmits.bind (L₂ := (· = [])) (goldfish_vote_walk C P A' Φ t v)
      (fun _ => ?_)).mono ?_
    · repeat' first
        | exact DREBEmits.pure rfl
        | refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
        | refine DREBEmits.bind_nil (DREBEmits.liftM _) (fun _ => ?_)
    · rintro _ ⟨l₁, l₂, rfl, h₁, rfl⟩ vote hvote
      rw [List.append_nil] at hvote
      exact ⟨hc.2, A', hA', h₁ vote hvote⟩
  · repeat' first
      | exact DREBEmits.pure (fun _ h => absurd h List.not_mem_nil)
      | refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      | refine DREBEmits.bind_nil (DREBEmits.liftM _) (fun _ => ?_)

/-- Every Goldfish vote the node's tick at `t` sends was sent by its tick of the available chain,
with the duty test `(record_awake n t).awake_since (duty_window_start C (C.slot t))` passed, by the
Goldfish vote duty run on the answer `A'` of the revocation of the slot of `t` on
`expireLocks n.A t`, over the frame `fg_to_ac n.S`, and is the vote that duty's walk casts.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time.

Read aloud: the tick votes only after revoking, as its walk on the revoked AC state says. -/
theorem tick_walk (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBEmits (fun l => ∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ l →
        (record_awake n t).awake_since (duty_window_start C (C.slot t)) = true ∧
          ∃ A' : ACState V,
            revoke_locks P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A' ∧
              GoldfishVoteWalk C P A' (fg_to_ac n.S) t n.v vote)
      (tick C P X n t) := by
  obtain ⟨hS, hA, hv, -⟩ := record_awake_frame n t
  simp only [tick]
  refine (DREBEmits.bind (L₂ := NoVote) (ac_on_tick_walk C P _ _ t _ _ _)
    (fun _ => ?_)).mono ?_
  · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
    · refine (DREBEmits.bind (L₂ := NoVote) (propose_block_sends C P X _)
        (fun _ => ?_)).mono (fun _ h => noVote_block_append h)
      refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · exact (DREBEmits.bind (L₂ := NoVote) (attest_sends C _)
          (fun _ => DREBEmits.pure noVote_nil)).mono (fun _ h => noVote_attest_append h)
      · exact DREBEmits.pure noVote_nil
    · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · exact (DREBEmits.bind (L₂ := NoVote) (attest_sends C _)
          (fun _ => DREBEmits.pure noVote_nil)).mono (fun _ h => noVote_attest_append h)
      · exact DREBEmits.pure noVote_nil
  · rintro _ ⟨l₁, l₂, rfl, h₁, h₂⟩ vote hvote
    rcases List.mem_append.mp hvote with hvote | hvote
    · obtain ⟨hb, A', hA', hw⟩ := h₁ vote hvote
      rw [hS, hA, hv] at *
      exact ⟨hb, A', hA', hw⟩
    · exact absurd (h₂ _ hvote) (by simp [GoldilocksCorrectness.Proofs.Routines.isGfVote])

/-! ## Lemma 14 -/

/-- **Lemma 14, the vote a tick sends is the end of the Goldfish fork choice.** The proof; the
audited statement is in `Statements/Routines/TickStatements.lean`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer, the node state and the objects sent; `vote`: the vote sent;
- `A'`: the answer of the revocation; `votes`, `support_votes`: the counted sets; `vbt`: the
  voter's tree; `H`: the block the fork choice reaches. -/
theorem lem14_tick_vote_walk (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (vote : GoldfishVote V)
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hVote : NamedObject.gfVote vote ∈ sent) :
    t = C.t_ (C.slot t) + C.Δ ∧ vote.val_index = n.v ∧ vote.slot = C.slot t ∧
      n.v ∈ P.committee (C.slot t) ∧
      ∃ (A' : ACState V) (votes support_votes : Finset (GoldfishVote V))
        (vbt : Finset (Block V)) (H : Block V),
        revoke_locks P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) = .ok A' ∧
        CountedVotes C n.A (fg_to_ac n.S) (C.slot t) votes support_votes ∧
        voter_block_tree C n.A (fg_to_ac n.S) (C.slot t) = .ok vbt ∧
        goldfish_fork_choice C (fg_to_ac n.S) t (get_anchor A' (fg_to_ac n.S) t)
          (viable_tree (fg_to_ac n.S) vbt) votes support_votes (C.slot t - 1) = .ok H ∧
        vote.head = H.root ∧ n'.A.lock_entries = A'.lock_entries := by
  obtain ⟨hv, hs, ht⟩ := (tick_sends C P X n t hRun).1 vote hVote
  have hL := (tick_walk C P X n t).of_outcome hRun
  obtain ⟨hb, A', hA', hcomm, votes, sv, vbt, H, hCV, hvbt, hfc, hvote⟩ := hL vote hVote
  -- the lock entries: Lemma 13's route, with the duty test the vote forced
  obtain ⟨A₁, out, out', hrun, hk⟩ := tick_ac_on_tick C P X n n' t _ hRun
  rw [hb] at hrun
  obtain ⟨A'₂, hA'₂, hA₁⟩ :=
    ac_on_tick_revokes C P n.A (fg_to_ac n.S) t n.v true ht out A₁ out' hrun
  have heq : A'₂ = A' := by
    rw [hA'] at hA'₂
    exact (Except.ok.inj hA'₂).symm
  rw [heq] at hA₁
  -- the revocation keeps the pool and the stamps
  have hkv : KeepsVotes n.A A' :=
    revoke_locks_keepsVotes P (expireLocks n.A t) (fg_to_ac n.S) t (C.slot t) A' hA'
  refine ⟨ht, hv, hs, hcomm, A', votes, sv, vbt, H, hA',
    (countedVotes_of_keepsVotes hkv C _ _ votes sv).1 hCV, ?_, hfc, ?_, hk.1.trans hA₁⟩
  · rw [← voter_block_tree_of_keepsVotes hkv]
    exact hvbt
  · rw [hvote]

end GoldilocksCorrectness.Proofs.Routines
