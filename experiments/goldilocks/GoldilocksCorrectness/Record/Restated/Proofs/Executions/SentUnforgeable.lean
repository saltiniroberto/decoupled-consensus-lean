module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas

@[expose] public section

/-!
# The protocol's half of unforgeability

`sent_unforgeable`: on a trace of the model's node, a message on the wire whose object, or an object
it includes, is attributed to a validator honest up to the time is on the wire under that validator's
own signature by then. The environment promises this for the steps of the kind `other` only
(`EnvFacts.other_sent`); for a tick, a wake and a delivery it follows from what the model's reactions
send.

Two private helpers carry the proof, each over an environment at any delay, any `GST` and any class
of messages: `held_onWire`, every vote and attestation a validator holds is on the wire, alone or
inside a block; and `nodeInv_along`, Lemma 11's node invariant along the run. The kit's own versions
(`pool_vote_sent`, `held_attestation_sent`, `lem11_node_invariant`) take the environment at the delay
`Δ S` and the class `acObject` only, so they do not apply to the `E` of this statement.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (carries)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Goldilocks
open Goldilocks.Sts (Setup)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks author)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- Along a run, every Goldfish vote and every attestation a validator holds is on the wire, alone
or included in a block on the wire.

Why: by induction on the step. Nothing is held after `0` steps; a step keeps the sent log; and what
a step adds to the validator's held votes and attestations is, at its tick, an object the tick sent
or a vote or attestation of a block it sent (`F.tk.tick_prov`, `F.tk.tick_prov_attestations`), at a
delivery, the delivered object or a vote or attestation of the delivered block (`F.rcv.receive_new`,
`F.rcv.receive_new_attestations`); a wake keeps both (`F.wk.wake_readers`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `k`: the step; `v`: the validator.

Read aloud: whatever vote or attestation a validator holds after `k` steps is on the wire then, by
itself or inside a block. -/
private theorem held_onWire {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) (k : ℕ) (v : V) :
    (∀ (s : Slot) (vote : GoldfishVote V), vote ∈ (x.st k v).votesHeld s →
      ∃ sm ∈ x.sent k, NamedObject.gfVote vote = sm.msg ∨ carries sm.msg (NamedObject.gfVote vote)) ∧
    (∀ a ∈ (x.st k v).attestationsHeld,
      ∃ sm ∈ x.sent k, NamedObject.attest a = sm.msg ∨ carries sm.msg (NamedObject.attest a)) := by
  induction k with
  | zero =>
    rw [R.init v]
    refine ⟨fun s vote h => ?_, fun a h => ?_⟩
    · rw [F.init.initial_votesHeld] at h
      simp at h
    · rw [F.init.initial_attestationsHeld] at h
      simp at h
  | succ k ih =>
    obtain ⟨ihV, ihA⟩ := ih
    have lift : ∀ o : NamedObject V, (∃ sm ∈ x.sent k, o = sm.msg ∨ carries sm.msg o) →
        ∃ sm ∈ x.sent (k + 1), o = sm.msg ∨ carries sm.msg o := fun o ⟨sm, hsm, h⟩ =>
      ⟨sm, Multiset.mem_of_le (R.sent_mono k) hsm, h⟩
    by_cases hT : ∃ t : ℕ, x.lbl k = Event.tick v t
    · obtain ⟨t, hl⟩ := hT
      obtain ⟨n', sent, hok, hst, hsent⟩ := R.tick k v t hl
      have own : ∀ o ∈ sent, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) := by
        intro o ho
        rw [hsent]
        exact Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨o, by simpa using ho, rfl⟩))
      have hP := F.tk.tick_prov S.C S.P S.X (x.st k v) (t : Int) n' sent hok
      rw [hst]
      refine ⟨fun s vote hv => ?_, fun a ha => ?_⟩
      · by_cases hn : vote ∈ (x.st k v).votesHeld s
        · exact lift _ (ihV s vote hn)
        · obtain ⟨o, ho, hc⟩ := hP.1 s vote hv hn
          refine ⟨⟨v, o⟩, own o ho, ?_⟩
          rcases hc with rfl | ⟨B, rfl, hB⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨vote, hB, rfl⟩)
      · by_cases hn : a ∈ (x.st k v).attestationsHeld
        · exact lift _ (ihA a hn)
        · rcases F.tk.tick_prov_attestations S.C S.P S.X (x.st k v) (t : Int) n' sent hok a ha hn
            with h1 | ⟨B, hB, hB'⟩
          · exact ⟨⟨v, _⟩, own _ h1, Or.inl rfl⟩
          · exact ⟨⟨v, _⟩, own _ hB, Or.inr (Or.inr ⟨a, hB', rfl⟩)⟩
    by_cases hW : ∃ (tR : ℕ) (keep : Bool), x.lbl k = Event.restart v tR keep
    · obtain ⟨tR, keep, hl⟩ := hW
      obtain ⟨hst, -⟩ := R.restart k v tR keep hl
      have hw := F.wk.wake_readers (x.st k v) (tR : Int)
      rw [hst]
      refine ⟨fun s vote hv => lift _ (ihV s vote ?_), fun a ha => lift _ (ihA a ?_)⟩
      · change vote ∈ M.votesHeld (M.wake (x.st k v) (tR : Int)) s at hv
        rwa [hw.2.2.2.2.2.2.2.1] at hv
      · change a ∈ M.attestationsHeld (M.wake (x.st k v) (tR : Int)) at ha
        rwa [hw.2.2.2.2.2.2.1] at ha
    by_cases hD : ∃ sm : SignedMsg V (NamedObject V), x.lbl k = Event.deliver v sm
    · obtain ⟨sm, hl⟩ := hD
      obtain ⟨hsm, hst, -⟩ := R.deliver k v sm hl
      have hsm' := Multiset.mem_of_le (R.sent_mono k) hsm
      rw [hst]
      refine ⟨fun s vote hv => ?_, fun a ha => ?_⟩
      · by_cases hn : vote ∈ (x.st k v).votesHeld s
        · exact lift _ (ihV s vote hn)
        · refine ⟨sm, hsm', ?_⟩
          rcases (F.rcv.receive_new S.C S.P S.X _ sm.msg).1 s vote hv hn with h | ⟨B, h, hB⟩
          · exact Or.inl h.symm
          · rw [h]
            exact Or.inr (Or.inl ⟨vote, hB, rfl⟩)
      · by_cases hn : a ∈ (x.st k v).attestationsHeld
        · exact lift _ (ihA a hn)
        · refine ⟨sm, hsm', ?_⟩
          rcases F.rcv.receive_new_attestations S.C S.P S.X _ sm.msg a ha hn with h | ⟨B, h, hB⟩
          · exact Or.inl h.symm
          · rw [h]
            exact Or.inr (Or.inr ⟨a, hB, rfl⟩)
    · have hst := R.untouched k v (fun t h => hT ⟨t, h⟩)
        (fun tR keep h => hW ⟨tR, keep, h⟩) (fun sm h => hD ⟨sm, h⟩)
      rw [hst]
      exact ⟨fun s vote hv => lift _ (ihV s vote hv), fun a ha => lift _ (ihA a ha)⟩

/-- Lemma 11's node invariant along a run: after every step, every validator's node state satisfies
the model's node invariant, has the validator, and has a clock at most the time.

Why: by induction on the step, from `F.init.initial_clock` and `F.nd.initial_nodeInv` after `0`
steps; at a tick, `F.nd.tick_nodeInv`, whose clock condition comes from the condition on executions
`clock_mono` (`clockValue_le_of_set`); at a wake and a delivery, `F.nd.wake_nodeInv` and
`F.nd.receive_nodeInv`; at any other step the node state is unchanged and the time does not
decrease.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator.

Read aloud: every node state of a validator outside the adversary set along a run satisfies the
model's invariant and runs as its validator. -/
private theorem nodeInv_along {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {ok : NamedObject V → Prop} {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok Vocab.goldilocks) (i : ℕ) (v : V)
    -- `v` is outside the adversary set after `i` steps
    (hv : v ∉ A.corrupted i) :
    M.nodeInv S.C S.P S.X (x.st i v) ∧ (x.st i v).v = v := by
  have key : M.nodeInv S.C S.P S.X (x.st i v) ∧ (x.st i v).v = v ∧
      (x.st i v).t = (x.clockValue i v : Int) := by
    induction i with
    | zero =>
        rw [R.init v, x.clockValue_zero v]
        exact ⟨F.nd.initial_nodeInv S.C S.P S.X v, (F.init.initial_clock S.C v).2,
          by rw [(F.init.initial_clock S.C v).1]; rfl⟩
    | succ i ih =>
        have hvi : v ∉ A.corrupted i := fun h => hv (E.corrupted_mono i (i + 1) (Nat.le_succ i) h)
        obtain ⟨hinv, hvv, hclk⟩ := ih hvi
        by_cases ht : ∃ t, x.lbl i = Event.tick v t
        · obtain ⟨t, hl⟩ := ht
          obtain ⟨n', sent, hok, hst, -⟩ := R.tick i v t hl
          have hle : (x.st i v).t ≤ (t : Int) := by
            rw [hclk]; exact_mod_cast E.clockValue_le_of_set hvi (Or.inl hl)
          obtain ⟨h1, h2, h3⟩ := F.nd.tick_nodeInv S.C S.P S.X (x.st i v) (t : Int) hinv hle n' sent hok
          rw [hst, x.clockValue_succ_of_tick hl]
          exact ⟨h1, h2.trans hvv, h3⟩
        by_cases hr : ∃ (tR : ℕ) (keep : Bool), x.lbl i = Event.restart v tR keep
        · obtain ⟨tR, keep, hl⟩ := hr
          have hle : (x.st i v).t ≤ (tR : Int) := by
            rw [hclk]; exact_mod_cast E.clockValue_le_of_set hvi (Or.inr ⟨keep, hl⟩)
          obtain ⟨h1, h2, h3⟩ := F.nd.wake_nodeInv S.C S.P S.X (x.st i v) (tR : Int) hinv hle
          rw [(R.restart i v tR keep hl).1, x.clockValue_succ_of_restart hl]
          exact ⟨h1, h2.trans hvv, h3⟩
        have ht' : ∀ t, x.lbl i ≠ Event.tick v t := fun t h => ht ⟨t, h⟩
        have hr' : ∀ (tR : ℕ) (keep : Bool), x.lbl i ≠ Event.restart v tR keep :=
          fun tR keep h => hr ⟨tR, keep, h⟩
        rw [x.clockValue_succ_of_not ht' hr']
        by_cases hd : ∃ sm, x.lbl i = Event.deliver v sm
        · obtain ⟨sm, hl⟩ := hd
          obtain ⟨h1, h2, h3⟩ := F.nd.receive_nodeInv S.C S.P S.X (x.st i v) sm.msg hinv
          rw [(R.deliver i v sm hl).2.1]
          exact ⟨h1, h2.trans hvv, h3.trans hclk⟩
        · rw [R.untouched i v ht' hr' (fun sm h => hd ⟨sm, h⟩)]
          exact ⟨hinv, hvv, hclk⟩
  exact ⟨key.1, key.2.1⟩

/-- **The protocol's half of unforgeability.** A message on the wire after `i` steps whose object,
or an object it includes, is attributed to a validator honest up to the time after `i` steps, is on
the wire under that validator's own signature by then.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `sm`: the
  message on the wire; `o'`: its object or an object it includes; `u`: the validator `o'` is
  attributed to.

Read aloud: nobody puts on the wire an object of an honest validator that the validator has not
itself put on the wire. -/
theorem sent_unforgeable {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {ok : NamedObject V → Prop} {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok Vocab.goldilocks)
    (i : ℕ) (sm : SignedMsg V (NamedObject V)) (o' : NamedObject V) (u : V)
    (hmem : sm ∈ x.sent i) (ho' : o' = sm.msg ∨ carries sm.msg o') (hu : author o' = some u)
    (hH : A.HonestThroughStep i u) :
    (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent i := by
  induction i generalizing sm with
  | zero =>
    rw [R.sent_zero] at hmem
    simp at hmem
  | succ i ih =>
    have hH' : A.HonestThroughStep i u := Activity.HonestThroughStep.mono (Nat.le_succ i) hH
    have lift : (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent i →
        (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) :=
      fun h => Multiset.mem_of_le (R.sent_mono i) h
    -- a message on the wire after `i` steps that is `o'` or includes it gives the claim
    have ihW : ∀ sm' : SignedMsg V (NamedObject V), sm' ∈ x.sent i →
        (o' = sm'.msg ∨ carries sm'.msg o') →
        (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) :=
      fun sm' h1 h2 => lift (ih sm' h1 h2 hH')
    by_cases hold : sm ∈ x.sent i
    · exact ihW sm hold ho'
    have hmem0 := hmem
    rcases hl : x.lbl i with ⟨v, t⟩ | ⟨v, tR, keep⟩ | ⟨v, sm₀⟩ | _
    · -- a tick of `v`: `sm` is `v`'s own object, sent from `v`'s node state
      obtain ⟨n', sent, hok, -, hsent⟩ := R.tick i v t hl
      rw [hsent] at hmem
      rcases Multiset.mem_add.1 hmem with h | h
      · exact absurd h hold
      obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.1 h
      have ho : o ∈ sent := by simpa using ho
      obtain ⟨hI, hv⟩ := nodeInv_along M F R E i v (E.not_mem_corrupted_of_tick hl)
      obtain ⟨hV, hA⟩ := held_onWire M F R i v
      cases o with
      | gfVote vote =>
        obtain ⟨-, hvi, -⟩ :=
          F.tk3.tick_vote_head S.C S.P S.X (x.st i v) (t : Int) n' sent vote hok hI ho
        rcases ho' with rfl | hc
        · have hu' : vote.val_index = u := Option.some_injective _ hu
          rw [← hu', hvi, hv]
          exact hmem0
        · exact hc.elim
      | attest a =>
        obtain ⟨-, -, source, head, -, -, ⟨τ, -, -, ha⟩, -⟩ :=
          F.tk3.tick_attestation S.C S.P S.X (x.st i v) (t : Int) n' sent a hok hI ho
        rcases ho' with rfl | hc
        · have hu' : a.val_index = u := Option.some_injective _ hu
          have hai : a.val_index = (x.st i v).v := by rw [ha]
          rw [← hu', hai, hv]
          exact hmem0
        · exact hc.elim
      | block B =>
        obtain ⟨-, -, -, -, H, votes, support_votes, hvotes, -, hPH, hB⟩ :=
          F.tk3.tick_proposal S.C S.P S.X (x.st i v) (t : Int) n' sent B hok hI ho
        rcases ho' with rfl | hc
        · have hp : B.proposer? = some (x.st i v).v := by rw [hB]; rfl
          have hu' : (x.st i v).v = u := Option.some_injective _ (hp.symm.trans hu)
          rw [← hu', hv]
          exact hmem0
        · rcases hc with ⟨vote, hvote, rfl⟩ | ⟨a, ha, rfl⟩
          · -- a vote of the proposal: one of `v`'s held votes of the previous slot
            have hvote' : vote ∈ (x.st i v).votesHeld (S.C.slot (t : Int) - 1) := by
              rw [← hvotes]
              rw [hB] at hvote
              exact hvote
            obtain ⟨sm', hsm', hw⟩ := hV _ vote hvote'
            exact ihW sm' hsm' hw
          · -- an attestation of the proposal: one of `v`'s held attestations
            obtain ⟨vs, svs, -, hEnd⟩ := hPH
            have hHT : H ∈ (x.st i v).tree :=
              GoldilocksCorrectness.Record.Proofs.Routines.walk_end_mem_T M F S.C S.P S.X _ hI
                (t : Int) H
                ((@GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq V _ M.tieBreak _ _ _ _ _ hEnd).symm)
                (F.nd.nodeInv_finalized_mem_tree hI) (F.nd.nodeInv_justifiedInTree hI)
            have ha' : a ∈ (x.st i v).attestationsHeld := by
              rw [hB] at ha
              change a ∈ M.proposal_attestations (x.st i v) H at ha
              rw [F.ndAdded.proposal_attestations_eq hI hHT, List.mem_filter] at ha
              exact ha.1
            obtain ⟨sm', hsm', hw⟩ := hA a ha'
            exact ihW sm' hsm' hw
    · -- a wake sends nothing
      rw [(R.restart i v tR keep hl).2] at hmem
      exact absurd hmem hold
    · -- a delivery: `sm` is a relay of the delivered message `sm₀`, which is on the wire
      obtain ⟨hsm₀, -, hsent⟩ := R.deliver i v sm₀ hl
      rw [hsent] at hmem
      rcases Multiset.mem_add.1 hmem with h | h
      · exact absurd h hold
      obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.1 h
      rcases (F.rcv.mem_relayedObjects_iff _ _).1 ho with rfl | ⟨B, hB, hvo⟩
      · exact ihW sm₀ hsm₀ ho'
      · rcases hvo with ⟨vote, hvote, rfl⟩ | ⟨a, ha, rfl⟩
        · rcases ho' with rfl | hc
          · exact ihW sm₀ hsm₀ (Or.inr (by rw [hB]; exact Or.inl ⟨vote, hvote, rfl⟩))
          · exact hc.elim
        · rcases ho' with rfl | hc
          · exact ihW sm₀ hsm₀ (Or.inr (by rw [hB]; exact Or.inr ⟨a, ha, rfl⟩))
          · exact hc.elim
    · -- a step of another kind: the environment's half (`E.other_sent`)
      have hnew : sm ∈ x.sent (i + 1) - x.sent i := by
        rw [← Multiset.count_pos, Multiset.count_sub, Multiset.count_eq_zero.2 hold,
          Nat.sub_zero]
        exact Multiset.count_pos.2 hmem
      rcases E.other_sent i sm hl hnew with h | ⟨-, h⟩
      · exact absurd h hold
      · exact lift (h o' u ho' hu hH')

end GoldilocksCorrectness.Record.Proofs.Executions
