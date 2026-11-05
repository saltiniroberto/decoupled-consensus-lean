module
public import GoldilocksCorrectness.Proofs.Routines.Lemma19
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.Walk
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.Node
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The attestation duty at the routine level

The proofs of the statements of `GoldilocksCorrectness/Statements/Routines/AttestationStatements.lean`:
the source and the anchor of the attestation duty (Lemmas 48 and 48b), the attestation a tick
sends (Lemmas 49 and 49b), what the validator client sends at a height (Lemma 50), and two kit
facts (`h_max_le_of_viable`, `fast_blocks_ancestorEq_saved`).

The route of Lemmas 49 and 49b: `DREBRel R m` says that every answer of the duty `m`, with the
objects it appends, satisfies the relation `R`; it composes over binds and `if`s. The attestation
duty answers its record and sends its attestation exactly as `fg_attest` builds them
(`attest_rel`); in the tick it runs only at the action time of the round, where the proposal does
not run (`slotStart_ne_actionTime`), on the FG state, the record and the clock the tick started
from and on the AC state the tick of the available chain left, which it keeps (`tick_attest_rel`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (propose_block_sends record_awake_frame
  on_attestation_frame)
open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)
open GoldilocksCorrectness.Proofs.Routines (DREBEmits DREBPost)

/-! ## A relation between a duty's answer and what it sends -/

section Rel

variable {V : Type}

/-- `DREBRel R m`: for every list `sent₀` of objects sent before `m` runs and every answer
`(a, sent)` of `m.run sent₀`, the list `sent` is `sent₀ ++ l` for some list `l` with `R a l`.

Read aloud: every answer of `m` and what it appends satisfy `R`. -/
def DREBRel {α : Type} (R : α → List (NamedObject V) → Prop) (m : DREB V α) : Prop :=
  ∀ (sent₀ : List (NamedObject V)) (a : α) (sent : List (NamedObject V)),
    m.run sent₀ = .ok (a, sent) → ∃ l, sent = sent₀ ++ l ∧ R a l

/-- A weaker relation follows from a stronger one. -/
theorem DREBRel.mono {α : Type} {m : DREB V α} {R R' : α → List (NamedObject V) → Prop}
    (h : DREBRel R m) (hR : ∀ a l, R a l → R' a l) : DREBRel R' m := by
  intro sent₀ a sent ha
  obtain ⟨l, hl, hR'⟩ := h sent₀ a sent ha
  exact ⟨l, hl, hR a l hR'⟩

/-- If every answer of `m` is related by `R` to what `m` appends (`DREBRel R m`), then the answer
of every `.ok` outcome of `m` is related by `R` to the objects that outcome sent.

The variables:
- `R`: the relation; `m`: the duty; `a`, `sent`: the answer and the objects sent. -/
theorem DREBRel.of_outcome {α : Type} {R : α → List (NamedObject V) → Prop} {m : DREB V α}
    (h : DREBRel R m) {a : α} {sent : List (NamedObject V)} (hm : .ok (a, sent) ∈ m.outcomes) :
    R a sent := by
  obtain ⟨l, hl, hR⟩ := h [] a sent (DREB.run_eq_of_mem_outcomes hm)
  rw [List.nil_append] at hl
  subst hl
  exact hR

/-- A return answers its value and appends nothing. -/
theorem DREBRel.pure {α : Type} {R : α → List (NamedObject V) → Prop} {a : α} (h : R a []) :
    DREBRel R (Pure.pure a : DREB V α) := by
  intro sent₀ a' sent ha
  have ha' : (Except.ok (a, sent₀) : DRE (α × List (NamedObject V))) = .ok (a', sent) := ha
  cases ha'
  exact ⟨[], (List.append_nil _).symm, h⟩

/-- A bind: its first routine's answer and list satisfy `R₁`, and from any such pair the
continuation's answer, with the first list followed by its own, satisfies `R`. -/
theorem DREBRel.bind {α β : Type} {x : DREB V α} {f : α → DREB V β}
    {R₁ : α → List (NamedObject V) → Prop} {R : β → List (NamedObject V) → Prop}
    (hx : DREBRel R₁ x)
    (hf : ∀ a l₁, R₁ a l₁ → DREBRel (fun b l₂ => R b (l₁ ++ l₂)) (f a)) :
    DREBRel R (x >>= f) := by
  intro out b out' hb
  have hb' : (x.run out >>= fun p => (f p.1).run p.2) = .ok (b, out') := hb
  cases hxa : x.run out with
  | error e => rw [hxa] at hb'; cases hb'
  | ok p =>
      rw [hxa] at hb'
      obtain ⟨l₁, hp, h₁⟩ := hx out p.1 p.2 hxa
      obtain ⟨l₂, h', h₂⟩ := hf p.1 l₁ h₁ p.2 b out' hb'
      exact ⟨l₁ ++ l₂, by rw [h', hp, List.append_assoc], h₂⟩

/-- An `if` satisfies what both its branches satisfy. -/
theorem DREBRel.ite {α : Type} {c : Prop} [Decidable c] {A B : DREB V α}
    {R : α → List (NamedObject V) → Prop} (hA : c → DREBRel R A) (hB : ¬ c → DREBRel R B) :
    DREBRel R (if c then A else B) := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h

/-- A dependent `if` satisfies what both its branches satisfy. -/
theorem DREBRel.dite {α : Type} {c : Prop} [Decidable c] {A : c → DREB V α}
    {B : ¬c → DREB V α} {R : α → List (NamedObject V) → Prop} (hA : ∀ h, DREBRel R (A h))
    (hB : ∀ h, DREBRel R (B h)) : DREBRel R (if h : c then A h else B h) := by
  by_cases h : c
  · rw [dif_pos h]; exact hA h
  · rw [dif_neg h]; exact hB h

/-- A routine that may fail, run without sending, answers what it answers and appends
nothing. -/
theorem DREBRel.liftM {α : Type} (m : DRE α) :
    DREBRel (fun a l => m = .ok a ∧ l = []) (liftM m : DREB V α) := by
  intro out a out' ha
  cases hm : m with
  | error e => rw [hm] at ha; cases ha
  | ok a' => rw [hm] at ha; cases ha; exact ⟨[], (List.append_nil _).symm, rfl, rfl⟩

/-- `broadcast o` appends `o`. -/
theorem DREBRel.broadcast (o : NamedObject V) :
    DREBRel (fun _ l => l = [o]) (Goldilocks.broadcast o) := by
  intro sent₀ a sent ha
  have ha' : (Except.ok ((), sent₀ ++ [o]) : DRE (Unit × List (NamedObject V))) =
      .ok (a, sent) := ha
  cases ha'
  exact ⟨[o], rfl, rfl⟩

/-- What a routine appends, by `DREBEmits`, is a relation that reads the list alone. -/
theorem DREBRel.of_emits {α : Type} {m : DREB V α} {L : List (NamedObject V) → Prop}
    (h : DREBEmits L m) : DREBRel (fun _ l => L l) m :=
  fun out a out' ha => h out a out' ha

end Rel

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The frames of the steps the duty reads -/

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The extraction `Option.get` of an option known to be `some a` is `a`.

The variables:
- `x`: the option; `a`: its value; `h`: the proof that `x` is present. -/
theorem get_eq_of_eq_some {α : Type} {x : Option α} {a : α} (hx : x = some a)
    (h : x.isSome) : x.get h = a := by
  subst hx
  rfl

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The first step of a tick keeps the anti-slashing record. -/
theorem record_awake_Λ (n : NodeState V) (t : Time) : (record_awake n t).Λ = n.Λ := by
  simp only [record_awake, Id.run]
  split <;> rfl

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps the anti-slashing record. -/
theorem on_attestation_Λ (n : NodeState V) (a : Attestation V) :
    (on_attestation n a).Λ = n.Λ := by
  simp only [on_attestation, Id.run]
  split <;> rfl

/-! ## The attestation duty -/

/-- What the attestation duty answers and sends: it keeps the AC state; `ac_to_fg` answered some
`fi` on the node's AC state, over the frame of its FG state, at its clock; with no source it
sends nothing; with a source, the record becomes the one `fg_attest` returns, and the duty sends
exactly the attestation `fg_attest` builds, when it builds one.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_rel (C : Config) (n : NodeState V) :
    DREBRel (fun n' l => n'.A = n.A ∧ ∃ fi : FGInput V,
        ac_to_fg C n.A (fg_to_ac n.S) n.t = .ok fi ∧
        (fi.source = none → l = []) ∧
        ∀ source : Block V, fi.source = some source →
          n'.Λ = (fg_attest n.S n.Λ n.v source fi.head).1 ∧
          ∀ a : Attestation V, NamedObject.attest a ∈ l ↔
            (fg_attest n.S n.Λ n.v source fi.head).2 = some a)
      (attest C n) := by
  simp only [attest]
  refine DREBRel.bind (DREBRel.liftM _) (fun fi l₁ ⟨hfi, hl₁⟩ => ?_)
  subst hl₁
  obtain ⟨src?, head⟩ := fi
  cases src? with
  | none =>
      simp only [List.nil_append, ne_eq, not_true_eq_false, dite_false]
      exact DREBRel.pure ⟨rfl, _, hfi, fun _ => rfl, fun source h => by cases h⟩
  | some source =>
      simp only [List.nil_append, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
        Option.value, Option.get_some]
      split
      · rename_i ha
        obtain ⟨a₀, ha₀⟩ := Option.ne_none_iff_exists'.mp ha
        rw [get_eq_of_eq_some ha₀]
        refine DREBRel.bind (DREBRel.broadcast _) (fun u l₁ hl₁ => ?_)
        subst hl₁
        refine DREBRel.pure ⟨(on_attestation_frame _ _).2.1, _, hfi, (fun h => by cases h),
          fun source' h => ?_⟩
        cases h
        refine ⟨on_attestation_Λ _ _, fun a => ?_⟩
        simp only [List.append_nil, List.mem_singleton, NamedObject.attest.injEq, ha₀,
          Option.some.injEq]
        exact eq_comm
      · rename_i ha
        simp only [Decidable.not_not] at ha
        refine DREBRel.pure ⟨rfl, _, hfi, (fun h => by cases h), fun source' h => ?_⟩
        cases h
        exact ⟨rfl, fun a => by simp [ha]⟩

/-- `NoAttest l`: no object of the list `l` is an attestation.

Read aloud: `l` holds no attestation. -/
def NoAttest (l : List (NamedObject V)) : Prop :=
  ∀ a : Attestation V, NamedObject.attest a ∉ l

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The tick of the available chain sends no attestation. -/
theorem noAttest_of_ac_on_tick {C : Config} {v : V} {t : Time} {l : List (NamedObject V)}
    (h : l.length ≤ 1 ∧ ∀ o ∈ l, (∃ h : BlockId, o = NamedObject.gfVote (GoldfishVote.mk v
      (C.slot t) h)) ∧ t = C.t_ (C.slot t) + C.Δ) : NoAttest l := by
  intro a ha
  obtain ⟨⟨_, he⟩, -⟩ := h.2 _ ha
  cases he

/-- What the tick answers and sends, about attestations: every attestation it sends was sent at
the action time of the round of its slot, and is the one `fg_attest` builds from the node's FG
state and record and the source and head `ac_to_fg` answers on the tick's final AC state; the
tick's final record is the one `fg_attest` returns. And at the action time, when the node passes
the duty test, every attestation `fg_attest` builds there is sent.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_attest_rel (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBRel (fun n' l =>
        (∀ a : Attestation V, NamedObject.attest a ∈ l →
          t = C.a_ (C.round (C.slot t)) ∧ ∃ (fi : FGInput V) (source : Block V),
            ac_to_fg C n'.A (fg_to_ac n.S) t = .ok fi ∧ fi.source = some source ∧
            (fg_attest n.S n.Λ n.v source fi.head).2 = some a ∧
            n'.Λ = (fg_attest n.S n.Λ n.v source fi.head).1) ∧
        (t = C.a_ (C.round (C.slot t)) →
          (record_awake n t).awake_since (duty_window_start C (C.slot t)) = true →
          ∀ (fi : FGInput V) (source : Block V) (a : Attestation V),
            ac_to_fg C n'.A (fg_to_ac n.S) t = .ok fi → fi.source = some source →
            (fg_attest n.S n.Λ n.v source fi.head).2 = some a → NamedObject.attest a ∈ l))
      (tick C P X n t) := by
  obtain ⟨hS, -, hv, -⟩ := record_awake_frame n t
  have hΛ := record_awake_Λ n t
  simp only [tick]
  refine DREBRel.bind (DREBRel.of_emits (ac_on_tick_sends C P _ _ t _ _ _))
    (fun A₁ l₁ hl₁ => ?_)
  have hl₁' : NoAttest l₁ := noAttest_of_ac_on_tick hl₁
  refine DREBRel.ite (fun hc₁ => ?_) (fun hc₁ => ?_)
  · -- the proposal ran, at the start of the slot: the attestation duty does not run
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₁
    have hstart : t = C.t_ (C.slot t) := hc₁.1.1.2
    refine DREBRel.bind (DREBRel.of_emits (propose_block_sends C P X _)) (fun n₄ l₂ hl₂ => ?_)
    refine DREBRel.ite (fun hc₂ => ?_) (fun hc₂ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₂
      exact absurd (hstart.symm.trans hc₂.1) (slotStart_ne_actionTime C _)
    · refine DREBRel.pure ⟨fun a ha => ?_, fun ht _ => ?_⟩
      · obtain ⟨B, rfl⟩ := hl₂
        simp only [List.append_nil, List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | ha
        · exact absurd ha (hl₁' a)
        · cases ha
      · exact absurd (hstart.symm.trans ht) (slotStart_ne_actionTime C _)
  · refine DREBRel.ite (fun hc₂ => ?_) (fun hc₂ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₂
      refine DREBRel.bind (attest_rel C _) (fun n₅ l₂ hl₂ => ?_)
      refine DREBRel.pure ?_
      obtain ⟨hA, fi, hfi, hnone, hsrc⟩ := hl₂
      dsimp only at hA hfi hsrc
      rw [hS] at hfi hsrc
      rw [hΛ, hv] at hsrc
      rw [List.append_nil]
      refine ⟨fun a ha => ?_, fun _ _ fi' source a hfi' hsrc' hbuilt => ?_⟩
      · rcases List.mem_append.mp ha with ha | ha
        · exact absurd ha (hl₁' a)
        · refine ⟨hc₂.1, ?_⟩
          cases hs : fi.source with
          | none => rw [hnone hs] at ha; exact absurd ha List.not_mem_nil
          | some source =>
              obtain ⟨hΛ', hiff⟩ := hsrc source hs
              exact ⟨fi, source, by rw [hA]; exact hfi, hs, (hiff a).1 ha, hΛ'⟩
      · rw [hA, hfi] at hfi'
        injection hfi' with hfi'
        subst hfi'
        exact List.mem_append.mpr (Or.inr (((hsrc source hsrc').2 a).2 hbuilt))
    · refine DREBRel.pure ⟨fun a ha => ?_, fun ht hawake => ?_⟩
      · rw [List.append_nil] at ha
        exact absurd ha (hl₁' a)
      · exfalso
        apply hc₂
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨ht, hawake⟩

/-! ## Lemmas 49 and 49b -/

/-- **Lemma 49, the attestation a tick sends is the duty's.** The proof; the audited statement is
in `Statements/Routines/AttestationStatements.lean`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer; `a`: the attestation sent. -/
theorem lem49_tick_attests (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (a : Attestation V)
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hAtt : NamedObject.attest a ∈ sent) :
    t = C.a_ (C.round (C.slot t)) ∧
    ∃ (fi : FGInput V) (source : Block V),
      ac_to_fg C n'.A (fg_to_ac n.S) t = .ok fi ∧ fi.source = some source ∧
      (create_attestation n.Λ n.v (n.S.σ source).h (n.S.σ source).T_h.root
        (n.S.σ fi.head).h_j (n.S.σ fi.head).J.root (n.S.σ fi.head).h_F).2 = some a ∧
      n'.Λ = (create_attestation n.Λ n.v (n.S.σ source).h (n.S.σ source).T_h.root
        (n.S.σ fi.head).h_j (n.S.σ fi.head).J.root (n.S.σ fi.head).h_F).1 := by
  obtain ⟨h1, -⟩ := (tick_attest_rel C P X n t).of_outcome hRun
  exact h1 a hAtt

/-- **Lemma 49b, the duty runs.** The proof; the audited statement is in
`Statements/Routines/AttestationStatements.lean`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer; `a`: the attestation built;
- `fi`: the duty's answer of `ac_to_fg`; `source`: its source. -/
theorem lem49b_attestation_duty_runs (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (a : Attestation V)
    (fi : FGInput V) (source : Block V)
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hAction : t = C.a_ (C.round (C.slot t)))
    (hAwake : ∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ duty_window_start C (C.slot t))
    (hInput : ac_to_fg C n'.A (fg_to_ac n.S) t = .ok fi)
    (hSource : fi.source = some source)
    (hBuilt : (create_attestation n.Λ n.v (n.S.σ source).h (n.S.σ source).T_h.root
        (n.S.σ fi.head).h_j (n.S.σ fi.head).J.root (n.S.σ fi.head).h_F).2 = some a) :
    NamedObject.attest a ∈ sent := by
  obtain ⟨τ, hτ, hle⟩ := hAwake
  obtain ⟨-, h2⟩ := (tick_attest_rel C P X n t).of_outcome hRun
  exact h2 hAction (awake_since_record_awake hτ hle) fi source a hInput hSource hBuilt

/-! ## Lemmas 48 and 48b -/

/-- **Lemma 48, the source of the attestation duty.** The proof; the audited statement is in
`Statements/Routines/AttestationStatements.lean`.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame; `t`: the time; `B`: the fast block. -/
theorem lem48_attestation_source (C : Config) (A : ACState V) (Φ : Frame V) (t : Time)
    (B : Block V) (hFast : B ∈ A.fast_blocks)
    (hAnc : ∀ B' ∈ A.fast_blocks, B'.AncestorEq B)
    (hViable : B ∈ viable_tree Φ Φ.tree) :
    ∀ fi : FGInput V, ac_to_fg C A Φ t = .ok fi → fi.source = some B := by
  intro fi hfi
  simp only [ac_to_fg] at hfi
  obtain ⟨sv, -, h1⟩ := dre_bind_eq_ok hfi
  obtain ⟨head, -, h2⟩ := dre_bind_eq_ok h1
  simp only [pure, Except.pure, Except.ok.injEq] at h2
  subst h2
  refine deepest?_eq_some (Finset.mem_inter.mpr ⟨hFast, hViable⟩)
    (fun D hD => depth_le_of_ancestorEq (hAnc D (Finset.mem_inter.mp hD).1))
    (fun D hD hd => eq_of_ancestorEq_of_depth (hAnc D (Finset.mem_inter.mp hD).1) hd.ge)

/-- **Lemma 48b, the anchor is the locked block.** The proof; the audited statement is in
`Statements/Routines/AttestationStatements.lean`.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame; `t`: the time; `B`: the locked
  block. -/
theorem lem48b_anchor_is_locked_block (C : Config) (A : ACState V) (Φ : Frame V) (t : Time)
    (B : Block V) (hLocked : is_locked A Φ t B = true)
    (hLocks : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.AncestorEq B)
    (hViable : B ∈ viable_tree Φ Φ.tree) :
    get_anchor A Φ t = B ∧
      ∀ fi : FGInput V, ac_to_fg C A Φ t = .ok fi → B.AncestorEq fi.head := by
  -- every locked block is `B` or an ancestor of `B`
  have hanc : ∀ D : Block V, is_locked A Φ t D = true → D.AncestorEq B := by
    intro D hD
    simp only [is_locked, decide_eq_true_eq] at hD
    obtain ⟨e, he, hlive, hDe⟩ := hD
    exact ancestorEq_trans hDe (hLocks e he hlive)
  have hD : Block.deepest? {B' ∈ viable_tree Φ Φ.tree | is_locked A Φ t B'} = some B := by
    refine deepest?_eq_some (Finset.mem_filter.mpr ⟨hViable, hLocked⟩)
      (fun D hD' => depth_le_of_ancestorEq (hanc D (Finset.mem_filter.mp hD').2))
      (fun D hD' hd => eq_of_ancestorEq_of_depth (hanc D (Finset.mem_filter.mp hD').2) hd.ge)
  have hanchor : get_anchor A Φ t = B := by
    simp only [get_anchor, Id.run]
    generalize hD' : Block.deepest? {B' ∈ viable_tree Φ Φ.tree | is_locked A Φ t B'} = D
    rw [hD'] at hD
    subst hD
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    rfl
  refine ⟨hanchor, fun fi hfi => ?_⟩
  simp only [ac_to_fg] at hfi
  obtain ⟨sv, -, h1⟩ := dre_bind_eq_ok hfi
  obtain ⟨head, hhead, h2⟩ := dre_bind_eq_ok h1
  simp only [pure, Except.pure, Except.ok.injEq] at h2
  subst h2
  have hghost : ghost (get_anchor A Φ t) (viable_tree Φ Φ.tree) _ _ = .ok head := hhead
  rw [hanchor] at hghost
  rcases ghost_spec hghost with h | ⟨h, -⟩
  · rw [h]
    exact ancestorEq_refl B
  · exact h

/-! ## The kit facts -/

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- **Kit fact, a viable block's height is at least the cache minus one.** The proof; the
audited statement is in `Statements/Routines/AttestationStatements.lean`.

The variables:
- `S`: the FG state; `B`: the block. -/
theorem h_max_le_of_viable [DecidableEq V] (S : FGState V) (B : Block V)
    (hV : is_viable S B = true) : S.h_max ≤ (S.σ B).h + 1 := by
  simp only [is_viable, decide_eq_true_eq] at hV
  have hV' : head_height_floor S ≤ (S.σ B).h := hV
  have hfloor : S.h_max - 1 ≤ head_height_floor S := by
    simp only [head_height_floor, Id.run]
    split
    · exact Nat.sub_le _ _
    · exact le_refl _
  unfold Height at *
  omega

/-- **Kit fact, every fast block of the update's answer is the saved confirmation or an ancestor
of it.** The proof; the audited statement is in `Statements/Routines/AttestationStatements.lean`.

The variables:
- `C`: the parameters; `P`: the values; `A`, `A'`: the AC state before and after the update;
- `Φ`: the frame; `t`: the time; `s`: the slot of the update; `C'`: the saved confirmation. -/
theorem fast_blocks_ancestorEq_saved (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot) (C' : Block V) (hs : s ≠ 0)
    (hUpdate : update_confirmation C P A Φ t s = .ok A')
    (hSaved : A'.saved_confirmation (s - 1) = some C') :
    ∀ L ∈ A'.fast_blocks, L.AncestorEq C' := by
  simp only [update_confirmation] at hUpdate
  rw [if_neg hs] at hUpdate
  obtain ⟨early, -, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, -, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, -, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, -, h4⟩ := dre_bind_eq_ok h3
  cases b
  · -- no block is saved: no fast block
    rw [if_neg (by decide)] at h4
    split at h4
    case isTrue hne => exact absurd rfl hne
    case isFalse =>
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      intro L hL
      exact absurd hL (Finset.notMem_empty L)
  rw [if_pos rfl] at h4
  split at h4
  case isFalse hne => exact absurd (Option.some_ne_none H) hne
  split at h4
  case isFalse =>
    -- a live lock vetoes `H`: no fast block
    simp only [pure, Except.pure, Except.ok.injEq] at h4
    subst h4
    intro L hL
    exact absurd hL (Finset.notMem_empty L)
  obtain ⟨fb, hfb, h5⟩ := dre_bind_eq_ok h4
  obtain ⟨lk, -, h6⟩ := dre_bind_eq_ok h5
  -- the saved confirmation is `H`, and every fast block is on the path to `H`
  have hpath : ∀ L ∈ fb, L.AncestorEq H := by
    intro L hL
    obtain ⟨hp, -⟩ := (mem_of_filterM_eq_ok_iff _ _ _ hfb L).1 hL
    simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.2.2
  generalize hD : Block.deepest? lk = D at h6
  cases D with
  | none =>
    simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure, Except.ok.injEq] at h6
    subst h6
    simp only [Function.update_self, Option.some.injEq] at hSaved
    subst hSaved
    exact hpath
  | some D =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some,
      pure, Except.pure, Except.ok.injEq] at h6
    subst h6
    simp only [Function.update_self, Option.some.injEq] at hSaved
    subst hSaved
    exact hpath

/-! ## Lemma 50 -/

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The lock `height_pair` reads at `h_c`: the finality pair's block when the pair is at `h_c`,
and the record's lock at `h_c` otherwise.

The variables:
- `Λ`: the record; `h_c`: the height; `fp`: the finality pair. -/
theorem own_lock_eq_match (Λ : SigningHistory) (h_c : Height) (fp : Option FinalityPair) :
    own_lock Λ h_c fp = match fp with
      | some p => if p.hf = h_c then some p.Tf else Λ.lock h_c
      | none => Λ.lock h_c := by
  cases fp with
  | none => simp only [own_lock, Id.run, ne_eq, not_true_eq_false, dite_false]; rfl
  | some p =>
      simp only [own_lock, Id.run, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
        Option.value, Option.get_some]
      split <;> rfl

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The height pair of a source `(h_c, T_c)`, written as the cases of `height_pair`.

The variables:
- `Λ`: the record; `h_c`, `T_c`: the source's height and root; `fp`: the finality pair. -/
theorem height_pair_eq_cases (Λ : SigningHistory) (h_c : Height) (T_c : BlockId)
    (fp : Option FinalityPair) :
    height_pair Λ (some (h_c, T_c)) fp =
      if Λ.timeout h_c = true then .vote h_c T_c true
      else if own_lock Λ h_c fp ≠ none then
        (if own_lock Λ h_c fp = some T_c then .vote h_c T_c false else .empty)
      else if Λ.target h_c = none ∨ Λ.target h_c = some T_c then .vote h_c T_c false
      else .vote h_c T_c true := by
  simp only [height_pair, Id.run, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
    Option.value, Option.get_some, GoldilocksCorrectness.Proofs.Routines.fun_getElem]
  split_ifs <;> first | rfl | (exfalso; simp_all)

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- **Lemma 50, what the validator client sends at a height.** The proof; the audited statement is
in `Statements/Routines/AttestationStatements.lean`.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height. -/
theorem lem50_attestation_sent_at_source (Λ : SigningHistory) (v : V) (h_c : Height)
    (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height)
    (hLock : Λ.lock h_c = none ∨
      (Λ.lock h_c = some T_c ∧ ∀ b ∈ Λ.sent, b.h = h_c → b.T = T_c))
    (hJ : h_j = h_c → J = T_c)
    (hTargetSent : ∀ (h : Height) (T : BlockId), Λ.target h = some T →
      ∃ b ∈ Λ.sent, b.h = h ∧ b.T = T)
    (hSentTarget : ∀ b ∈ Λ.sent, b.τ = false → Λ.target b.h ≠ none)
    (hSentTimeout : ∀ b ∈ Λ.sent, b.τ = true → Λ.timeout b.h = true) :
    ((∃ a : Attestation V, (create_attestation Λ v h_c T_c h_j J h_F).2 = some a ∧
        a.val_index = v ∧ a.h = h_c ∧ a.T = T_c) ∨
      ((create_attestation (V := V) Λ v h_c T_c h_j J h_F).2 = none ∧
        ∃ b ∈ Λ.sent, b.h = h_c ∧ b.T = T_c)) ∧
    ((∀ b ∈ Λ.sent, b.h ≠ h_c) → Λ.timeout h_c = false → Λ.target h_c = none →
      ∃ a : Attestation V, (create_attestation Λ v h_c T_c h_j J h_F).2 = some a ∧
        a.val_index = v ∧ a.h = h_c ∧ a.T = T_c ∧ a.τ = false) := by
  -- a finality pair the record allows is `(h_j, J)`, with no timeout and the target `J` or none
  have hfps : ∀ p : FinalityPair, finality_pair Λ h_j J h_F = some p →
      p = ⟨h_j, J⟩ ∧ Λ.timeout h_j = false ∧
        (Λ.target h_j = none ∨ Λ.target h_j = some J) := by
    intro p hp
    obtain ⟨hpe, -, htgt, hto, -⟩ := finality_pair_some hp
    refine ⟨hpe, hto, ?_⟩
    cases hT : Λ.target h_j with
    | none => exact Or.inl rfl
    | some T => exact Or.inr (by rw [htgt T hT])
  -- an attestation at `h_c` with no timeout recorded there, and the target there `T_c` or none,
  -- gives an attestation at `h_c` naming `T_c`
  have htarget : Λ.timeout h_c = false → (Λ.target h_c = none ∨ Λ.target h_c = some T_c) →
      ∀ b ∈ Λ.sent, b.h = h_c → ∃ b' ∈ Λ.sent, b'.h = h_c ∧ b'.T = T_c := by
    intro hto ht b hb hbh
    cases hτ : b.τ
    · have hne := hSentTarget b hb hτ
      rw [hbh] at hne
      rcases ht with ht | ht
      · exact absurd ht hne
      · exact hTargetSent h_c T_c ht
    · have := hSentTimeout b hb hτ
      rw [hbh, hto] at this
      cases this
  -- the lock `height_pair` reads is `T_c` or absent; when it is `T_c` from the finality pair, the
  -- record has no timeout at `h_c` and its target there is `T_c` or none
  have hown : own_lock Λ h_c (finality_pair Λ h_j J h_F) = none ∨
      (own_lock Λ h_c (finality_pair Λ h_j J h_F) = some T_c ∧
        (Λ.lock h_c = some T_c ∨
          (Λ.timeout h_c = false ∧ (Λ.target h_c = none ∨ Λ.target h_c = some T_c)))) := by
    rw [own_lock_eq_match]
    cases hfp : finality_pair Λ h_j J h_F with
    | none =>
        rcases hLock with hl | ⟨hl, -⟩
        · exact Or.inl hl
        · exact Or.inr ⟨hl, Or.inl hl⟩
    | some p =>
        obtain ⟨rfl, hto, ht⟩ := hfps p hfp
        dsimp only
        split
        · rename_i hhf
          subst hhf
          rw [hJ rfl] at ht ⊢
          exact Or.inr ⟨rfl, Or.inr ⟨hto, ht⟩⟩
        · rcases hLock with hl | ⟨hl, -⟩
          · exact Or.inl hl
          · exact Or.inr ⟨hl, Or.inl hl⟩
  refine ⟨?_, fun hfresh hto ht => ?_⟩
  · simp only [create_attestation, Id.run]
    rw [height_pair_eq_cases]
    by_cases hto : Λ.timeout h_c = true
    · -- the timeout at `h_c`
      simp only [hto, if_true]
      split_ifs with hs
      · right
        refine ⟨rfl, ?_⟩
        simp only [already_sent, decide_eq_true_eq, Bool.not_true, Bool.false_eq_true,
          false_or] at hs
        exact hs
      all_goals exact Or.inl ⟨_, rfl, rfl, rfl, rfl⟩
    · simp only [Bool.not_eq_true] at hto
      simp only [hto, Bool.false_eq_true, if_false]
      rcases hown with hn | ⟨hs', hsrc⟩
      · -- no lock: case 4 or 5
        simp only [hn, ne_eq, not_true_eq_false, if_false]
        by_cases ht : Λ.target h_c = none ∨ Λ.target h_c = some T_c
        · simp only [ht, if_true]
          split_ifs with hs
          · right
            refine ⟨rfl, ?_⟩
            simp only [already_sent, decide_eq_true_eq] at hs
            obtain ⟨b, hb, hbh, -⟩ := hs
            exact htarget hto ht b hb hbh
          all_goals exact Or.inl ⟨_, rfl, rfl, rfl, rfl⟩
        · simp only [ht, if_false]
          split_ifs with hs
          · right
            refine ⟨rfl, ?_⟩
            simp only [already_sent, decide_eq_true_eq, Bool.not_true, Bool.false_eq_true,
              false_or] at hs
            exact hs
          all_goals exact Or.inl ⟨_, rfl, rfl, rfl, rfl⟩
      · -- the lock `T_c`: the target at `h_c`
        simp only [hs', ne_eq, reduceCtorEq, not_false_eq_true, if_true]
        split_ifs with hs
        · right
          refine ⟨rfl, ?_⟩
          simp only [already_sent, decide_eq_true_eq] at hs
          obtain ⟨b, hb, hbh, -⟩ := hs
          rcases hsrc with hl | ⟨hto', ht⟩
          · rcases hLock with hl' | ⟨-, hall⟩
            · rw [hl] at hl'
              cases hl'
            · exact ⟨b, hb, hbh, hall b hb hbh⟩
          · exact htarget hto' ht b hb hbh
        all_goals exact Or.inl ⟨_, rfl, rfl, rfl, rfl⟩
  · -- a fresh height: the target at `h_c`, which nothing the record sent forbids
    simp only [create_attestation, Id.run]
    rw [height_pair_eq_cases]
    simp only [hto, Bool.false_eq_true, if_false]
    rcases hown with hn | ⟨hs', -⟩
    · simp only [hn, ne_eq, not_true_eq_false, if_false, ht, true_or, if_true]
      split_ifs with hs
      · exfalso
        simp only [already_sent, decide_eq_true_eq] at hs
        obtain ⟨b, hb, hbh, -⟩ := hs
        exact hfresh b hb hbh
      all_goals exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [hs', ne_eq, reduceCtorEq, not_false_eq_true, if_true]
      split_ifs with hs
      · exfalso
        simp only [already_sent, decide_eq_true_eq] at hs
        obtain ⟨b, hb, hbh, -⟩ := hs
        exact hfresh b hb hbh
      all_goals exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

end GoldilocksCorrectness.Proofs.Routines
