module
public import GoldilocksCorrectness.Proofs.Routines.Lemma14
public import GoldilocksCorrectness.Proofs.Routines.ProposalFrame
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.State
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Lemma 19: the block a tick sends is the node's proposal

The proof of `lem19_tick_proposes`, stated in
`GoldilocksCorrectness/Statements/Routines/ProposalStatements.lean`.

The route: a block a tick sends was sent by the proposal (the tick of the available chain sends
only Goldfish votes, `ac_on_tick_sends`, and the attestation duty only an attestation,
`attest_sends`), so the proposal's `if` was taken: the slot of `t` is positive, `t` is its start,
and the node's validator is its proposer. At the start of a slot the tick of the available chain
only deletes the expired lock entries (`ac_on_tick_expire`: neither duty time of the slot is the
start, `C.Δ` being positive), so the proposal reads `expireLocks n.A t`; the block it sends is the
block built from the answer of `ac_proposal` (`propose_block_block`), whose three parts are the
pool's list, its resolving votes and the head from the anchor (`ac_proposal_facts`); the expiry
keeps the pool and the stamps and does not move the anchor (`get_anchor_expireLocks`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (propose_block_sends attest_sends record_awake_frame)
open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)
open GoldilocksCorrectness.Proofs.Routines (DREBPost DREPost DREBEmits)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## A bind whose continuation reads a fact about the first routine's answer -/

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- A bind appends what its first routine appends, then what its continuation appends, when the
continuation's condition holds on every answer of the first routine that satisfies `P`, and every
answer of the first routine satisfies `P`.

The variables:
- `x`: the first routine; `f`: the continuation; `P`: the fact about `x`'s answers;
- `L₁`, `L₂`: the conditions on what each part appends. -/
theorem DREBEmits.bind_post {α β : Type} {x : DREB V α} {f : α → DREB V β} {P : α → Prop}
    {L₁ L₂ : List (NamedObject V) → Prop} (hx : DREBEmits L₁ x) (hP : DREBPost x P)
    (hf : ∀ a, P a → DREBEmits L₂ (f a)) :
    DREBEmits (fun l => ∃ l₁ l₂, l = l₁ ++ l₂ ∧ L₁ l₁ ∧ L₂ l₂) (x >>= f) := by
  intro out b out' hb
  have hb' : (x.run out >>= fun p => (f p.1).run p.2) = .ok (b, out') := hb
  cases hxa : x.run out with
  | error e => rw [hxa] at hb'; cases hb'
  | ok p =>
      rw [hxa] at hb'
      obtain ⟨l₁, hp, h₁⟩ := hx out p.1 p.2 hxa
      obtain ⟨l₂, h', h₂⟩ := hf p.1 (hP out p.1 p.2 hxa) p.2 b out' hb'
      exact ⟨l₁ ++ l₂, by rw [h', hp, List.append_assoc], l₁, l₂, rfl, h₁, h₂⟩

/-! ## The relation -/

/-- `ProposalBlock C X A Φ t v B`: `B` is the block the proposal built from the answer of the
available chain's proposal `ac_proposal C A Φ t`: its parent, votes and support votes are that
answer's, its slot the slot of `t`, its attestations `proposal_attestations S H` for the FG state
`S` given, its root the digest of its content, and its proposer `v`.

The variables:
- `C`, `X`: the parameters and the digest; `S`: the FG state; `A`: the AC state; `Φ`: the frame;
- `t`: the time; `v`: the proposer; `B`: the block.

Read aloud: `B` is the block the proposal of `v` at `t` builds on `A`. -/
def ProposalBlock (C : Config) (X : External V) (S : FGState V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (B : Block V) : Prop :=
  ∃ pr : Proposal V, ac_proposal C A Φ t = .ok pr ∧
    B = Block.node pr.H (C.slot t)
      (X.digest pr.H.root (C.slot t) (proposal_attestations S pr.H) pr.votes pr.support_votes)
      pr.votes pr.support_votes (proposal_attestations S pr.H) v

/-! ## The routines -/

/-- At neither duty time of the slot of `t`, the tick of the available chain answers
`expireLocks A t`: neither `if` is taken.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the two wake tests.

Read aloud: away from the vote time and the support cutoff, the tick of the available chain only
deletes the expired lock entries. -/
theorem ac_on_tick_expire (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) :
    DREBPost (ac_on_tick C P A Φ t v b b') (fun A₁ => t ≠ C.t_ (C.slot t) + C.Δ →
      t ≠ C.t_ (C.slot t) + 2 * C.Δ → A₁ = expireLocks A t) := by
  simp only [ac_on_tick]
  refine DREBPost.ite (fun hc => ?_) (fun _ => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact DREBPost.bind_any (fun _ => DREBPost.bind_any (fun _ => DREBPost.ite
      (fun _ => DREBPost.bind_any (fun _ => DREBPost.pure (fun h _ => absurd hc.1 h)))
      (fun _ => DREBPost.pure (fun h _ => absurd hc.1 h))))
  · refine DREBPost.ite (fun hc => ?_) (fun _ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact DREBPost.bind_any (fun _ => DREBPost.pure (fun _ h => absurd hc.1 h))
    · exact DREBPost.pure (fun _ _ => rfl)

/-- Every block the proposal sends is the block built from the answer of `ac_proposal` on the
node's AC state, over the frame of its FG state, at its clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: the proposal sends the block it built. -/
theorem propose_block_block (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) :
    DREBEmits (fun l => ∀ B : Block V, NamedObject.block B ∈ l →
        ProposalBlock C X n.S n.A (fg_to_ac n.S) n.t n.v B)
      (propose_block C P X n) := by
  simp only [propose_block]
  refine DREBEmits.liftM_bind (fun pr hpr => ?_)
  obtain ⟨H, votes, support⟩ := pr
  refine (DREBEmits.broadcast_then _ (fun _ => DREBEmits.pure rfl)).mono ?_
  rintro _ rfl B hB
  rw [List.mem_singleton] at hB
  injection hB with hB
  exact ⟨_, hpr, hB⟩

/-- `NoBlock l`: no object of the list `l` is a block.

Read aloud: `l` holds no block. -/
def NoBlock (l : List (NamedObject V)) : Prop :=
  ∀ B : Block V, NamedObject.block B ∉ l

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- What the attestation duty sends, followed by nothing, holds no block. -/
theorem noBlock_of_attest {l : List (NamedObject V)}
    (h : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (l₁ = [] ∨ ∃ a : Attestation V, l₁ = [NamedObject.attest a]) ∧
      l₂ = []) : NoBlock l := by
  obtain ⟨l₁, l₂, rfl, h₁ | ⟨a, rfl⟩, rfl⟩ := h
  · subst h₁
    exact fun _ hB => absurd hB List.not_mem_nil
  · intro B hB
    simp at hB

/-- Every block the node's tick at `t` sends was sent by its proposal, in the proposal's `if`: the
slot of `t` is positive, `t` is its start, the node's validator is its proposer, and the block is
the one the proposal builds on the node's AC state with its expired entries removed
(`expireLocks n.A t`), over the frame `fg_to_ac n.S`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time.

Read aloud: the tick sends a block only as the proposer of its slot, at the slot's start. -/
theorem tick_block (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBEmits (fun l => ∀ B : Block V, NamedObject.block B ∈ l →
        0 < C.slot t ∧ t = C.t_ (C.slot t) ∧ n.v = P.proposer (C.slot t) ∧
          ProposalBlock C X n.S (expireLocks n.A t) (fg_to_ac n.S) t n.v B)
      (tick C P X n t) := by
  obtain ⟨hS, hA, hv, -⟩ := record_awake_frame n t
  -- the arithmetic of the slot's start, over `Int`
  have hstart : ∀ a d : Int, 0 < d → a ≠ a + d ∧ a ≠ a + 2 * d := by
    intro a d hd
    omega
  simp only [tick]
  refine (DREBEmits.bind_post (L₂ := fun l => ∀ B : Block V, NamedObject.block B ∈ l →
      0 < C.slot t ∧ t = C.t_ (C.slot t) ∧ n.v = P.proposer (C.slot t) ∧
        ProposalBlock C X n.S (expireLocks n.A t) (fg_to_ac n.S) t n.v B)
    (ac_on_tick_sends C P _ _ t _ _ _) (ac_on_tick_expire C P _ _ t _ _ _)
    (fun A₁ hA₁ => ?_)).mono ?_
  · refine DREBEmits.ite (fun hc => ?_) (fun _ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hpos, ht⟩, hprop⟩, -⟩ := hc
      have hA₁' : A₁ = expireLocks n.A t := by
        rw [← hA]
        refine hA₁ ?_ ?_
        · exact fun h => (hstart (C.t_ (C.slot t)) C.Δ C.Δ_pos).1 (ht.symm.trans h)
        · exact fun h => (hstart (C.t_ (C.slot t)) C.Δ C.Δ_pos).2 (ht.symm.trans h)
      refine (DREBEmits.bind (L₂ := NoBlock) (propose_block_block C P X _)
        (fun n₄ => ?_)).mono ?_
      · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
        · exact (DREBEmits.bind (L₂ := (· = [])) (attest_sends C _)
            (fun _ => DREBEmits.pure rfl)).mono (fun _ h => noBlock_of_attest h)
        · exact DREBEmits.pure (fun _ h => absurd h List.not_mem_nil)
      · rintro _ ⟨l₁, l₂, rfl, h₁, h₂⟩ B hB
        rcases List.mem_append.mp hB with hB | hB
        · have hP := h₁ B hB
          rw [hA₁', hS, hv] at hP
          rw [hv] at hprop
          exact ⟨hpos, ht, hprop, hP⟩
        · exact absurd hB (h₂ B)
    · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · exact (DREBEmits.bind (L₂ := (· = [])) (attest_sends C _)
          (fun _ => DREBEmits.pure rfl)).mono (fun _ h B hB => absurd hB (noBlock_of_attest h B))
      · exact DREBEmits.pure (fun _ h => absurd h List.not_mem_nil)
  · rintro _ ⟨l₁, l₂, rfl, h₁, h₂⟩ B hB
    rcases List.mem_append.mp hB with hB | hB
    · obtain ⟨⟨_, heq⟩, -⟩ := h₁.2 _ hB
      cases heq
    · exact h₂ B hB

/-- What an answer of the available chain's proposal holds: its votes are `A`'s list of slot
`C.slot t − 1`; its support votes are exactly the votes of that list that resolve; and its parent
is the head (`get_head`) for that slot with those votes.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame; `t`: the time; `pr`: the answer.

Read aloud: the proposal counts the pool's list and its resolving votes, and builds on the head. -/
theorem ac_proposal_facts (C : Config) (A : ACState V) (Φ : Frame V) (t : Time) (pr : Proposal V)
    (h : ac_proposal C A Φ t = .ok pr) :
    pr.votes = A.gf_votes (C.slot t - 1) ∧
      (∀ vote : GoldfishVote V, vote ∈ pr.support_votes ↔
        vote ∈ pr.votes ∧ ∃ y : Stamp, A.tau Φ vote = .ok (some y)) ∧
      get_head C A Φ t pr.votes.toFinset pr.support_votes.toFinset (C.slot t - 1) = .ok pr.H := by
  simp only [ac_proposal] at h
  obtain ⟨sv, hsv, h1⟩ := dre_bind_eq_ok h
  obtain ⟨H, hH, h2⟩ := dre_bind_eq_ok h1
  cases h2
  refine ⟨rfl, fun vote => ?_, hH⟩
  rw [List.mem_filterM_ok_iff _ _ _ hsv vote]
  refine and_congr_right fun _ => ?_
  cases hτ : A.tau Φ vote with
  | error e => simp [bind, Except.bind]
  | ok y =>
    cases y with
    | none => simp [bind, Except.bind, pure, Except.pure]
    | some y => simp [bind, Except.bind, pure, Except.pure]

/-! ## Lemma 19 -/

/-- **Lemma 19, the block a tick sends is the node's proposal.** The proof; the audited statement
is in `Statements/Routines/ProposalStatements.lean`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer, the node state and the objects sent; `B`: the block sent;
- `H`: the parent; `votes`, `support_votes`: the lists the proposal counts. -/
theorem lem19_tick_proposes (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (B : Block V)
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hBlock : NamedObject.block B ∈ sent) :
    0 < C.slot t ∧ t = C.t_ (C.slot t) ∧ n.v = P.proposer (C.slot t) ∧
      ∃ (H : Block V) (votes support_votes : List (GoldfishVote V)),
        votes = n.A.gf_votes (C.slot t - 1) ∧
        (∀ vote : GoldfishVote V, vote ∈ support_votes ↔
          vote ∈ votes ∧ ∃ y : Stamp, n.A.tau (fg_to_ac n.S) vote = .ok (some y)) ∧
        goldfish_fork_choice C (fg_to_ac n.S) t (get_anchor n.A (fg_to_ac n.S) t)
          (viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree) votes.toFinset
          support_votes.toFinset (C.slot t - 1) = .ok H ∧
        B = Block.node H (C.slot t)
          (X.digest H.root (C.slot t) (proposal_attestations n.S H) votes support_votes)
          votes support_votes (proposal_attestations n.S H) n.v := by
  -- step 1: the block was sent by the proposal, in its `if`
  have hL := (tick_block C P X n t).of_outcome hRun
  obtain ⟨hpos, ht, hprop, pr, hpr, hB⟩ := hL B hBlock
  -- step 2: the proposal's answer, its lists and its head
  have hstep2 := ac_proposal_facts C (expireLocks n.A t) (fg_to_ac n.S) t pr hpr
  obtain ⟨hvotes, hsupport, hhead⟩ := hstep2
  -- step 3: the expiry keeps the pool and the stamps, and does not move the anchor
  have hstep3 : get_head C (expireLocks n.A t) (fg_to_ac n.S) t pr.votes.toFinset
      pr.support_votes.toFinset (C.slot t - 1) =
      goldfish_fork_choice C (fg_to_ac n.S) t (get_anchor n.A (fg_to_ac n.S) t)
        (viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree) pr.votes.toFinset
        pr.support_votes.toFinset (C.slot t - 1) := by
    show goldfish_fork_choice C (fg_to_ac n.S) t (get_anchor (expireLocks n.A t) (fg_to_ac n.S) t)
        (viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree) pr.votes.toFinset
        pr.support_votes.toFinset (C.slot t - 1) = _
    rw [get_anchor_expireLocks]
  exact ⟨hpos, ht, hprop, pr.H, pr.votes, pr.support_votes, hvotes, hsupport,
    hstep3 ▸ hhead, hB⟩

end GoldilocksCorrectness.Proofs.Routines
