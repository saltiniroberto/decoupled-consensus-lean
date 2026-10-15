import Proofs.Instance.Model
import Proofs.Instance.Facts.SubtypeEqualities
import Proofs.Instance.Facts.ConfirmationTree
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# The handlers facts at `Model.spec`

Proofs of fields of `HandlersFacts` and `HandlersRunFacts` at the model `Model.spec`, one
theorem `spec_<x>` per field `<x>`. Most are proved from a lemma `specBase_<x>` at
`Model.specBase`, using the steps a store takes under the handlers.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecRecord.StoreSteps

open Spec
open scoped DC
open scoped Spec

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A total map read with brackets is the map applied: `f[a] = f a`. -/
theorem getElem_fn {α β : Type} (f : α → β) (a : α) : f[a] = f a := rfl

/-! ## Frame forms -/

/-- The two outcomes of `Protocol.admit_attestation C st a`: the store `st` unchanged, or, when
    `a`'s confirmed block is new for its sender and round, the store with `a` appended to the
    attestations of its round and its SG vote stamped with `st.t`. -/
theorem admit_attestation_cases (C : Config) (st : Store V) (a : Attestation V) :
    Protocol.admit_attestation C st a = st ∨
      (a.confirmed ∉ Protocol.round_votes st a ∧
        Protocol.admit_attestation C st a =
          { st with attestations := Function.update st.attestations a.round (st.attestations a.round ++ [a]),
                    timestamp_sg_vote :=
                      Function.update st.timestamp_sg_vote (Protocol.sgVote a) (some (st.t : Stamp)) }) := by
  unfold Protocol.admit_attestation Protocol.attestation_admissible Protocol.add_attestation
  simp only [Id.run, pure, getElem_fn]
  split_ifs with h1 h2 <;> first
    | exact Or.inl rfl
    | exact h2.elim
    | exact Or.inr ⟨fun hc => h1 (by simp [hc]), rfl⟩

/-- `Protocol.admit_attestation` writes only the attestations and the stamps of SG votes. -/
theorem admit_attestation_writes (C : Config) (st : Store V) (a : Attestation V) :
    ∃ x y, Protocol.admit_attestation C st a = { st with attestations := x, timestamp_sg_vote := y } := by
  rcases admit_attestation_cases C st a with h | ⟨-, h⟩
  · exact ⟨st.attestations, st.timestamp_sg_vote, h⟩
  · exact ⟨_, _, h⟩

/-- `Protocol.admit_attestations C st rows` is the left fold of `Protocol.admit_attestation C` over
    `rows`, from `st`. -/
theorem admit_attestations_foldl (C : Config) (rows : List (Attestation V)) (st : Store V) :
    Protocol.admit_attestations C st rows = rows.foldl (Protocol.admit_attestation C) st := by
  simp only [Protocol.admit_attestations, Id.run, List.forIn_pure_yield_eq_foldl]
  rfl

/-- `Protocol.admit_attestations` writes only the attestations and the stamps of SG votes. -/
theorem admit_attestations_writes (C : Config) (rows : List (Attestation V)) (st : Store V) :
    ∃ x y, Protocol.admit_attestations C st rows =
      { st with attestations := x, timestamp_sg_vote := y } := by
  rw [admit_attestations_foldl]
  induction rows generalizing st with
  | nil => exact ⟨_, _, rfl⟩
  | cons r rs ih =>
    simp only [List.foldl_cons]
    obtain ⟨x, y, h⟩ := admit_attestation_writes C st r
    obtain ⟨x', y', h'⟩ := ih (Protocol.admit_attestation C st r)
    rw [h', h]
    exact ⟨_, _, rfl⟩

/-- `Protocol.on_goldfish_vote_checked` writes only the Goldfish votes and their stamps. -/
theorem on_goldfish_vote_checked_writes (P : Provisional V) (st : Store V) (u : GoldfishVote V) :
    ∃ x y, Protocol.on_goldfish_vote_checked P st u = { st with gf_votes := x, timestamp_vote := y } := by
  unfold Protocol.on_goldfish_vote_checked Protocol.on_goldfish_vote
  simp only [Id.run, pure]
  split_ifs <;> exact ⟨_, _, rfl⟩

/-- Admitting a list of Goldfish votes, in order, writes only the Goldfish votes and their stamps. -/
theorem foldl_checked_writes (P : Provisional V) (votes : List (GoldfishVote V)) (st : Store V) :
    ∃ x y, votes.foldl (Protocol.on_goldfish_vote_checked P) st =
      { st with gf_votes := x, timestamp_vote := y } := by
  induction votes generalizing st with
  | nil => exact ⟨_, _, rfl⟩
  | cons u us ih =>
    simp only [List.foldl_cons]
    obtain ⟨x, y, h⟩ := on_goldfish_vote_checked_writes P st u
    obtain ⟨x', y', h'⟩ := ih (Protocol.on_goldfish_vote_checked P st u)
    rw [h', h]
    exact ⟨_, _, rfl⟩

/-- `Handlers.updateFinalityWith` writes only `h_max`, `J`, `h_j` and `F`. -/
theorem updateFinalityWith_writes (st : Store V) (σ : Protocol.ChainState V) :
    ∃ a b c d, Handlers.updateFinalityWith st σ = { st with h_max := a, J := b, h_j := c, F := d } := by
  unfold Handlers.updateFinalityWith
  simp only [Id.run, pure]
  split_ifs <;> exact ⟨_, _, _, _, rfl⟩

/-- `Protocol.update_finality` writes only `h_max`, `J`, `h_j` and `F`. -/
theorem update_finality_writes (st : Store V) (B : Block V) :
    ∃ a b c d, Protocol.update_finality st B = { st with h_max := a, J := b, h_j := c, F := d } := by
  rw [Handlers.update_finality_eq]
  exact updateFinalityWith_writes st (st.σ B)

/-- If `(a, x) < (b, y)` lexicographically, then `a ≤ b`. -/
theorem lex_fst_le {a b : Height} {x y : BlockId} (h : toLex (a, x) < toLex (b, y)) : a ≤ b := by
  rcases Prod.Lex.lt_iff.1 h with h1 | ⟨h1, -⟩
  · exact le_of_lt h1
  · exact le_of_eq h1

/-- `Handlers.updateFinalityWith` never lowers the justified height `h_j`. -/
theorem updateFinalityWith_h_j_le (st : Store V) (σ : Protocol.ChainState V) :
    st.h_j ≤ (Handlers.updateFinalityWith st σ).h_j := by
  unfold Handlers.updateFinalityWith
  simp only [Id.run, pure]
  split_ifs with h1 h2 <;> first
    | exact le_refl _
    | exact lex_fst_le (of_decide_eq_true (Bool.and_eq_true_iff.1 h1).2)

/-- `Protocol.update_finality` never lowers the justified height `h_j`. -/
theorem update_finality_h_j_le (st : Store V) (B : Block V) :
    st.h_j ≤ (Protocol.update_finality st B).h_j := by
  rw [Handlers.update_finality_eq]
  exact updateFinalityWith_h_j_le st (st.σ B)

/-! ## The block step -/

/-- A block the store admits (`Protocol.block_admissible`) is not in its tree. -/
theorem not_mem_of_block_admissible (C : Config) (P : Provisional V) (st : Store V) (B : Block V)
    (h : Protocol.block_admissible C P st B = true) : B ∉ st.T := by
  intro hB
  unfold Protocol.block_admissible at h
  simp [Id.run, hB] at h

/-- The two outcomes of `Protocol.on_block C P st B`: the store `st`, or, when `B` is not in the
    tree, the store with `B` admitted, the Goldfish votes `B` includes admitted, the finality update
    applied, and the attestations `B` includes admitted. -/
theorem on_block_shape (C : Config) (P : Provisional V) (st : Store V) (B : Block V) :
    Protocol.on_block C P st B = st ∨
      (B ∉ st.T ∧ ∃ σ' : Protocol.ChainState V,
        Protocol.on_block C P st B =
          Protocol.admit_attestations C
            (Protocol.update_finality
              (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked P)
                { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                          timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) })
              B)
            B.attestations) := by
  rw [Handlers.on_block_eq]
  by_cases h : Protocol.block_admissible C P st B = true
  · refine Or.inr ⟨not_mem_of_block_admissible C P st B h,
      Protocol.state_transition C P (st.σ B.parent) B, ?_⟩
    simp only [h, if_true, Handlers.admitBlockCore, Handlers.blockCore, Id.run, getElem_fn,
      List.forIn_pure_yield_eq_foldl]
    rfl
  · simp only [h]
    exact Or.inl rfl

/-! ## Steps -/

/-- `StoreStep C P τ st st'`: the store `st'` is obtained from `st` by one of the six writes that
    `tick` and the receiving routines make to a store, the clock write setting the clock to `τ`. The
    confirmation write keeps the three confirmation records in the tree when `F`, `J`,
    `latest_confirmed` and `latest_stable` are in it. -/
inductive StoreStep (C : Config) (P : Provisional V) (τ : Time) : Store V → Store V → Prop
  | grades (st : Store V) (g : SavedGrades V) : StoreStep C P τ st { st with saved_grades := g }
  | clock (st : Store V) : StoreStep C P τ st { st with t := τ, s := C.slotOf τ }
  | block (st : Store V) (B : Block V) : StoreStep C P τ st (Protocol.on_block C P st B)
  | vote (st : Store V) (u : GoldfishVote V) :
      StoreStep C P τ st (Protocol.on_goldfish_vote_checked P st u)
  | confirm (st : Store V) (a b c : Block V)
      (hmem : st.F ∈ st.T → st.J ∈ st.T → st.latest_confirmed ∈ st.T → st.latest_stable ∈ st.T →
        a ∈ st.T ∧ c ∈ st.T ∧ b ∈ st.T) :
      StoreStep C P τ st { st with live_confirmed := a, latest_stable := b, latest_confirmed := c }
  | attest (st : Store V) (row : Attestation V) :
      StoreStep C P τ st (Protocol.admit_attestation C st row)

/-- `StoreReach C P τ st st'`: the store `st'` is reached from `st` by zero or more steps
    `StoreStep C P τ`. -/
abbrev StoreReach (C : Config) (P : Provisional V) (τ : Time) : Store V → Store V → Prop :=
  Relation.ReflTransGen (StoreStep C P τ)

/-- Every answer of `Protocol.update_grades` is one step from the store. -/
theorem update_grades_step (C : Config) (P : Provisional V) (τ : Time) (st st' : Store V) (t : Time)
    (h : Protocol.update_grades C P st t = .ok st') : StoreStep C P τ st st' := by
  simp only [Protocol.update_grades, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; exact StoreStep.grades _ _)

/-- Every answer of `Protocol.update_confirmation` is one step from the store. -/
theorem update_confirmation_step (C : Config) (P : Provisional V) (τ : Time) (st st' : Store V)
    (s : Slot) (h : Protocol.update_confirmation C st s = .ok st') : StoreStep C P τ st st' := by
  have hmem := fun hF hJ hlt hls =>
    SpecRecord.NodeFacts.update_confirmation_mem hF hJ hlt hls h
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c : Block V,
      st' = { st with live_confirmed := a, latest_stable := b, latest_confirmed := c } := by
    simp only [Protocol.update_confirmation, bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (injection h with h; subst h; exact ⟨_, _, _, rfl⟩)
  exact StoreStep.confirm _ _ _ _ hmem

/-- Every answer of `Protocol.goldfish_vote` is reached from the store by at most one step. -/
theorem goldfish_vote_step (C : Config) (P : Provisional V) (τ : Time) (v : V) (st st' : Store V)
    (l l' : List (NamedObject V)) (h : Protocol.goldfish_vote C P v st l = .ok (st', l')) :
    StoreReach C P τ st st' := by
  simp only [Protocol.goldfish_vote, bind, StateT.bind, pure, Except.bind,
    Except.pure, broadcast, modify, modifyGet, MonadStateOf.modifyGet,
    liftM, monadLift, MonadLift.monadLift, StateT.lift] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h; injection h with h; subst h
       first
        | exact Relation.ReflTransGen.refl
        | exact Relation.ReflTransGen.single (StoreStep.vote _ _))

/-- Every answer of `Protocol.propose_block` is one step from the store. -/
theorem propose_block_step (C : Config) (P : Provisional V) (X : External V) (τ : Time) (v : V)
    (st st' : Store V) (l l' : List (NamedObject V))
    (h : Protocol.propose_block C P X v st l = .ok (st', l')) : StoreStep C P τ st st' := by
  simp only [Protocol.propose_block, bind, StateT.bind, pure, Except.bind,
    Except.pure, broadcast, modify, modifyGet, MonadStateOf.modifyGet,
    liftM, monadLift, MonadLift.monadLift, StateT.lift] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h; injection h with h; subst h; exact StoreStep.block _ _)

/-- Every answer of `Protocol.attest` is one step from the store. -/
theorem attest_step (C : Config) (P : Provisional V) (τ : Time) (v : V) (st st' : Store V)
    (sh sh' : SigningHistory) (l l' : List (NamedObject V))
    (h : Protocol.attest C v st sh l = .ok ((st', sh'), l')) : StoreStep C P τ st st' := by
  simp only [Protocol.attest, bind, StateT.bind, pure, Except.bind,
    Except.pure, broadcast, modify, modifyGet, MonadStateOf.modifyGet,
    liftM, monadLift, MonadLift.monadLift, StateT.lift] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h; injection h with h; injection h with h; subst h; exact StoreStep.attest _ _)

/-- `make_grades_compatible_with_finalized` is one step. -/
theorem compat_step (C : Config) (P : Provisional V) (τ : Time) (st : Store V) :
    StoreStep C P τ st (make_grades_compatible_with_finalized st) := by
  simp only [make_grades_compatible_with_finalized, Id.run]
  exact StoreStep.grades _ _

/-- Setting the store's clock to `τ` and its slot to the slot of `τ` is one step. -/
theorem clock_step (C : Config) (P : Provisional V) (τ : Time) (st : Store V) :
    StoreStep C P τ st { st with t := τ, s := C.slotOf τ } :=
  StoreStep.clock st

/-- `record_awake` keeps the node's store. -/
theorem record_awake_st (n : NodeState V) (t : Time) : (record_awake n t).st = n.st := by
  simp only [record_awake, Id.run]
  split <;> rfl

/-- A lifted routine pairs its answer with the list of objects sent:
    `StateT.lift m = fun l => Except.map (fun v => (v, l)) m`. -/
theorem lift_eq_map {α : Type} (m : DC.DRE α) :
    (StateT.lift m : DREB V α) = fun l => Except.map (fun v => (v, l)) m := by
  funext l
  cases m <;> rfl

/-- When `Except.map (fun v => (v, l)) m` answers `w`, the routine `m` answers `w.1`. -/
theorem map_ok {α : Type} {m : DC.DRE α} {l : List (NamedObject V)} {w : α × List (NamedObject V)}
    (h : Except.map (fun v => (v, l)) m = Except.ok w) : m = Except.ok w.1 := by
  cases m with
  | error e => cases h
  | ok v => cases h; rfl

/-- A sequence of steps followed by `make_grades_compatible_with_finalized` is a sequence of steps. -/
theorem reach_compat {C : Config} {P : Provisional V} {τ : Time} {a X : Store V}
    (h : StoreReach C P τ a X) : StoreReach C P τ a (make_grades_compatible_with_finalized X) :=
  h.tail (compat_step C P τ X)

/-- A sequence of steps followed by the attestation duty is a sequence of steps. -/
theorem reach_attest {C : Config} {P : Provisional V} {τ : Time} {a st : Store V} {v : V}
    {sh : SigningHistory} {l : List (NamedObject V)}
    {x : (Store V × SigningHistory) × List (NamedObject V)}
    (hr : StoreReach C P τ a st) (h : Protocol.attest C v st sh l = .ok x) :
    StoreReach C P τ a x.1.1 :=
  hr.tail (attest_step C P τ v st x.1.1 sh x.1.2 l x.2 h)

/-- A sequence of steps followed by the confirmation duty is a sequence of steps. -/
theorem reach_confirm {C : Config} {P : Provisional V} {τ : Time} {a st : Store V} {s : Slot}
    {l : List (NamedObject V)} {w : Store V × List (NamedObject V)}
    (hr : StoreReach C P τ a st)
    (h : Except.map (fun v => (v, l)) (Protocol.update_confirmation C st s) = Except.ok w) :
    StoreReach C P τ a w.1 :=
  hr.tail (update_confirmation_step C P τ st w.1 s (map_ok h))

/-- A sequence of steps followed by the Goldfish vote duty is a sequence of steps. -/
theorem reach_vote {C : Config} {P : Provisional V} {τ : Time} {a st : Store V} {v : V}
    {l : List (NamedObject V)} {w : Store V × List (NamedObject V)}
    (hr : StoreReach C P τ a st) (h : Protocol.goldfish_vote C P v st l = .ok w) :
    StoreReach C P τ a w.1 :=
  hr.trans (goldfish_vote_step C P τ v st w.1 l w.2 h)

/-- A sequence of steps followed by the proposal duty is a sequence of steps. -/
theorem reach_propose {C : Config} {P : Provisional V} {X : External V} {τ : Time} {a st : Store V}
    {v : V} {l : List (NamedObject V)} {w : Store V × List (NamedObject V)}
    (hr : StoreReach C P τ a st) (h : Protocol.propose_block C P X v st l = .ok w) :
    StoreReach C P τ a w.1 :=
  hr.tail (propose_block_step C P X τ v st w.1 l w.2 h)

/-- A sequence of steps followed by setting the clock to `τ` is a sequence of steps. -/
theorem reach_clock {C : Config} {P : Provisional V} {τ : Time} {a st : Store V}
    (hr : StoreReach C P τ a st) : StoreReach C P τ a { st with t := τ, s := C.slotOf τ } :=
  hr.tail (clock_step C P τ st)

/-- A sequence of steps followed by the grade update is a sequence of steps. -/
theorem reach_grades {C : Config} {P : Provisional V} {τ t : Time} {a st : Store V}
    {l : List (NamedObject V)} {w : Store V × List (NamedObject V)}
    (hr : StoreReach C P τ a st)
    (h : Except.map (fun v => (v, l)) (Protocol.update_grades C P st t) = Except.ok w) :
    StoreReach C P τ a w.1 :=
  hr.tail (update_grades_step C P τ st w.1 t (map_ok h))

section TickReach

attribute [local irreducible] Protocol.attest Protocol.goldfish_vote Protocol.propose_block
  Protocol.update_confirmation Protocol.update_grades

/-- When `n`'s `tick` at `t` answers the node state `n'`, the store of `n'` is reached from the
    store of `n` by steps whose clock writes set the clock to `t`. -/
theorem tick_reach (C : Config) (P : Provisional V) (X : External V) (n n' : NodeState V)
    (t : Time) (l l' : List (NamedObject V))
    (h : tick C P X n t l = .ok (n', l')) : StoreReach C P t n.st n'.st := by
  simp only [tick, bind, StateT.bind, pure, Except.bind, Except.pure, liftM, monadLift,
    MonadLift.monadLift, lift_eq_map] at h
  repeat' split at h
  all_goals (try simp only [StateT.bind, lift_eq_map, StateT.pure, Except.bind, Except.pure, pure,
    bind] at h)
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; injection h with h; subst h)
  all_goals (refine reach_compat ?_)
  all_goals (try refine reach_attest ?_ (by assumption))
  all_goals (try refine reach_confirm ?_ (by assumption))
  all_goals (try refine reach_vote ?_ (by assumption))
  all_goals (try refine reach_propose ?_ (by assumption))
  all_goals (refine reach_clock ?_)
  all_goals (refine reach_grades ?_ (by assumption))
  all_goals (rw [record_awake_st])

end TickReach

/-- The store after `n` receives `o` is reached from `n`'s store by steps. -/
theorem receive_reach (C : Config) (P : Provisional V) (τ : Time) (n : NodeState V)
    (o : NamedObject V) : StoreReach C P τ n.st (Spec.Sts.receive C P n o).st := by
  cases o with
  | block B =>
    simp only [Spec.Sts.receive, receive_block, Id.run]
    exact reach_compat (Relation.ReflTransGen.single (StoreStep.block _ _))
  | gfVote u =>
    simp only [Spec.Sts.receive, receive_goldfish_vote, Id.run]
    exact reach_compat (Relation.ReflTransGen.single (StoreStep.vote _ _))
  | attest a =>
    simp only [Spec.Sts.receive, receive_attestation, Id.run]
    exact reach_compat (Relation.ReflTransGen.single (StoreStep.attest _ _))

/-! ## A property of stores kept by every step -/

/-- A property kept by every step holds of every store reached from a store that has it. -/
theorem reach_induction {C : Config} {P : Provisional V} {τ : Time} (Q : Store V → Prop)
    (hstep : ∀ st st', StoreStep C P τ st st' → Q st → Q st') {st st' : Store V}
    (h : StoreReach C P τ st st') (hq : Q st) : Q st' := by
  induction h with
  | refl => exact hq
  | tail _ hs ih => exact hstep _ _ hs ih

/-- If every step keeps `I`, and every step from a store with `I` is related by the reflexive,
    transitive relation `R`, then along every sequence of steps from a store with `I`, `I` holds at
    the end and `R` relates the two ends. -/
theorem reach_relation {C : Config} {P : Provisional V} {τ : Time} (I : Store V → Prop)
    (R : Store V → Store V → Prop) (hrefl : ∀ st, R st st)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hI : ∀ st st', StoreStep C P τ st st' → I st → I st')
    (hR : ∀ st st', StoreStep C P τ st st' → I st → R st st') {st st' : Store V}
    (h : StoreReach C P τ st st') (hi : I st) : I st' ∧ R st st' := by
  induction h with
  | refl => exact ⟨hi, hrefl _⟩
  | tail _ hs ih => exact ⟨hI _ _ hs ih.1, htrans _ _ _ ih.2 (hR _ _ hs ih.1)⟩

/-! ## The Goldfish votes of each slot are from that slot's committee -/

/-- `VotesInCommittee P st`: every Goldfish vote `st` holds for slot `k` is from a member of the
    committee of slot `k` that `P` gives. -/
def VotesInCommittee (P : Provisional V) (st : Store V) : Prop :=
  ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k → u.val_index ∈ P.committee k

/-- `Protocol.on_goldfish_vote_checked` keeps `VotesInCommittee`. -/
theorem votesInCommittee_checked (P : Provisional V) (st : Store V) (u : GoldfishVote V)
    (h : VotesInCommittee P st) : VotesInCommittee P (Protocol.on_goldfish_vote_checked P st u) := by
  unfold Protocol.on_goldfish_vote_checked Protocol.on_goldfish_vote
  simp only [Id.run, pure, getElem_fn]
  split_ifs with h1 h2 h3 <;> first
    | exact h
    | (intro k x hx
       by_cases hk : k = u.slot
       · subst hk
         simp only [Function.update_self, List.mem_append, List.mem_singleton] at hx
         rcases hx with hx | rfl
         · exact h _ _ hx
         · simpa using h1
       · simp only [ne_eq, hk, not_false_eq_true, Function.update_of_ne] at hx
         exact h _ _ hx)

/-- Admitting a list of Goldfish votes keeps `VotesInCommittee`. -/
theorem votesInCommittee_foldl (P : Provisional V) (votes : List (GoldfishVote V)) (st : Store V)
    (h : VotesInCommittee P st) :
    VotesInCommittee P (votes.foldl (Protocol.on_goldfish_vote_checked P) st) := by
  induction votes generalizing st with
  | nil => exact h
  | cons u us ih => exact ih _ (votesInCommittee_checked P st u h)

/-- Every step keeps `VotesInCommittee`. -/
theorem votesInCommittee_step (C : Config) (P : Provisional V) (τ : Time) (st st' : Store V)
    (hs : StoreStep C P τ st st') (h : VotesInCommittee P st) : VotesInCommittee P st' := by
  cases hs with
  | grades => exact h
  | clock => exact h
  | confirm => exact h
  | vote u => exact votesInCommittee_checked P st u h
  | attest row =>
    obtain ⟨x, y, e⟩ := admit_attestation_writes C st row
    rw [e]; exact h
  | block B =>
    rcases on_block_shape C P st B with e | ⟨-, σ', e⟩
    · rw [e]; exact h
    · rw [e]
      obtain ⟨x, y, e1⟩ := admit_attestations_writes C B.attestations
        (Protocol.update_finality (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked P)
          { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                    timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }) B)
      rw [e1]
      obtain ⟨a, b, c, d, e2⟩ := update_finality_writes (B.gf_votes.foldl
        (Protocol.on_goldfish_vote_checked P)
          { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                    timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }) B
      rw [e2]
      exact votesInCommittee_foldl P _ _ h

/-! ## Fields that the finality update and the Goldfish vote admission keep -/

/-- `Protocol.update_finality` keeps the clock, the tree, the block stamps, the attestations, the SG
    vote stamps and the Goldfish votes. -/
theorem update_finality_keeps (st : Store V) (B : Block V) :
    let Y := Protocol.update_finality st B
    Y.t = st.t ∧ Y.T = st.T ∧ Y.timestamp_block = st.timestamp_block ∧
      Y.attestations = st.attestations ∧ Y.timestamp_sg_vote = st.timestamp_sg_vote ∧
      Y.gf_votes = st.gf_votes := by
  obtain ⟨a, b, c, d, e⟩ := update_finality_writes st B
  simp only [e, and_self]

/-- Admitting a list of Goldfish votes keeps the clock, the tree, the block stamps, the
    attestations, the SG vote stamps and the chain states. -/
theorem foldl_checked_keeps (P : Provisional V) (votes : List (GoldfishVote V)) (st : Store V) :
    let Y := votes.foldl (Protocol.on_goldfish_vote_checked P) st
    Y.t = st.t ∧ Y.T = st.T ∧ Y.timestamp_block = st.timestamp_block ∧
      Y.attestations = st.attestations ∧ Y.timestamp_sg_vote = st.timestamp_sg_vote ∧
      Y.σ = st.σ := by
  obtain ⟨x, y, e⟩ := foldl_checked_writes P votes st
  simp only [e, and_self]

/-- The store `on_block` builds before admitting the attestations a block `B` includes: its clock,
    attestations and SG vote stamps are `st`'s, its tree is `st`'s with `B` added, and every block
    other than `B` keeps its stamp. -/
theorem block_core_keeps (P : Provisional V) (st : Store V) (B : Block V) (σ' : Protocol.ChainState V) :
    let Y := Protocol.update_finality (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked P)
          { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                    timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }) B
    Y.t = st.t ∧ Y.T = st.T ∪ {B} ∧ Y.timestamp_block = Function.update st.timestamp_block B (some (st.t : Stamp)) ∧
      Y.attestations = st.attestations ∧ Y.timestamp_sg_vote = st.timestamp_sg_vote := by
  intro Y
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := update_finality_keeps (B.gf_votes.foldl
    (Protocol.on_goldfish_vote_checked P)
      { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }) B
  obtain ⟨f1, f2, f3, f4, f5, -⟩ := foldl_checked_keeps P B.gf_votes
      { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }
  exact ⟨u1.trans f1, u2.trans f2, u3.trans f3, u4.trans f4, u5.trans f5⟩

/-! ## The justified height never decreases -/

/-- No step lowers the justified height. -/
theorem h_j_le_step (C : Config) (P : Provisional V) (τ : Time) (st st' : Store V)
    (hs : StoreStep C P τ st st') : st.h_j ≤ st'.h_j := by
  cases hs with
  | grades => exact le_refl _
  | clock => exact le_refl _
  | confirm => exact le_refl _
  | vote u =>
    obtain ⟨x, y, e⟩ := on_goldfish_vote_checked_writes P st u
    rw [e]
  | attest row =>
    obtain ⟨x, y, e⟩ := admit_attestation_writes C st row
    rw [e]
  | block B =>
    rcases on_block_shape C P st B with e | ⟨-, σ', e⟩
    · rw [e]
    · rw [e]
      obtain ⟨x, y, e1⟩ := admit_attestations_writes C B.attestations
        (Protocol.update_finality (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked P)
          { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                    timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }) B)
      rw [e1]
      refine le_trans ?_ (update_finality_h_j_le _ _)
      obtain ⟨x, y, e⟩ := foldl_checked_writes P B.gf_votes
        { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                  timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }
      rw [e]

/-! ## The attestations and the stamps of their SG votes -/

/-- `RowsErasuresHeld st`: every attestation that `st` holds for round `r` (`st.sg_pool r`) is of
    round `r`. -/
def RowsErasuresHeld (st : Store V) : Prop :=
  ∀ (r : Round) (b : Attestation V), b ∈ st.sg_pool r → b.round = r

/-- `KeepsRows st st'`: `st'` holds every attestation of `st`, in the same round, and stamps the SG
    vote of each as `st` does. -/
def KeepsRows (st st' : Store V) : Prop :=
  (∀ r, st.sg_pool r ⊆ st'.sg_pool r) ∧
    ∀ (r : Round) (b : Attestation V), b ∈ st.sg_pool r →
      st'.timestamp_sg_vote (Protocol.sgVote b) = st.timestamp_sg_vote (Protocol.sgVote b)

/-- `KeepsRows` is reflexive. -/
theorem keepsRows_refl (st : Store V) : KeepsRows st st :=
  ⟨fun _ => subset_refl _, fun _ _ _ => rfl⟩

/-- `KeepsRows` is transitive. -/
theorem keepsRows_trans (a b c : Store V) (h1 : KeepsRows a b) (h2 : KeepsRows b c) :
    KeepsRows a c :=
  ⟨fun r => subset_trans (h1.1 r) (h2.1 r),
    fun r x hx => (h2.2 r x (h1.1 r hx)).trans (h1.2 r x hx)⟩

/-- An attestation is in `st.sg_pool r` exactly when it is in the list `st.attestations r`. -/
theorem mem_sg_pool_iff (st : Store V) (r : Round) (b : Attestation V) :
    b ∈ st.sg_pool r ↔ b ∈ st.attestations r := by
  simp only [Store.sg_pool, getElem_fn, List.mem_toFinset]

/-- An attestation `b` of `a`'s round held by the store, with `a`'s sender, has its confirmed block
    among `Protocol.round_votes st a`. -/
theorem confirmed_mem_round_votes (st : Store V) (a b : Attestation V)
    (hb : b ∈ st.sg_pool a.round) (hv : b.val_index = a.val_index) :
    b.confirmed ∈ Protocol.round_votes st a := by
  unfold Protocol.round_votes
  exact Finset.mem_image.2 ⟨b, Finset.mem_filter.2 ⟨hb, hv⟩, rfl⟩

/-- `Protocol.admit_attestation` keeps `RowsErasuresHeld`, `KeepsRows` and the clock; an attestation
    it newly holds is the one admitted, and its SG vote is stamped with the clock. -/
theorem admit_attestation_rows (C : Config) (st : Store V) (a : Attestation V)
    (hI : RowsErasuresHeld st) :
    RowsErasuresHeld (Protocol.admit_attestation C st a) ∧
      KeepsRows st (Protocol.admit_attestation C st a) ∧
      (Protocol.admit_attestation C st a).t = st.t ∧
      (∀ (r : Round) (x : Attestation V), x ∈ (Protocol.admit_attestation C st a).sg_pool r →
        x ∈ st.sg_pool r ∨
          (x = a ∧ (Protocol.admit_attestation C st a).timestamp_sg_vote (Protocol.sgVote a) =
            some (st.t : Stamp))) := by
  rcases admit_attestation_cases C st a with e | ⟨hnot, e⟩
  · rw [e]; exact ⟨hI, keepsRows_refl _, rfl, fun r x hx => Or.inl hx⟩
  · rw [e]
    have hpool : ∀ r, st.sg_pool r ⊆
        ({ st with attestations := Function.update st.attestations a.round (st.attestations a.round ++ [a]),
                   timestamp_sg_vote :=
                     Function.update st.timestamp_sg_vote (Protocol.sgVote a) (some (st.t : Stamp)) } :
          Store V).sg_pool r := by
      intro r b hb
      rw [mem_sg_pool_iff] at hb ⊢
      by_cases hr : r = a.round
      · subst hr
        simp only [Function.update_self, List.mem_append]
        exact Or.inl hb
      · simp only [ne_eq, hr, not_false_eq_true, Function.update_of_ne]
        exact hb
    have hnew : ∀ (r : Round) (x : Attestation V), x ∈
        ({ st with attestations := Function.update st.attestations a.round (st.attestations a.round ++ [a]),
                   timestamp_sg_vote :=
                     Function.update st.timestamp_sg_vote (Protocol.sgVote a) (some (st.t : Stamp)) } :
          Store V).sg_pool r → x ∈ st.sg_pool r ∨ (x = a ∧ r = a.round) := by
      intro r x hx
      rw [mem_sg_pool_iff] at hx
      by_cases hr : r = a.round
      · subst hr
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inl ((mem_sg_pool_iff _ _ _).2 hx)
        · exact Or.inr ⟨rfl, rfl⟩
      · simp only [ne_eq, hr, not_false_eq_true, Function.update_of_ne] at hx
        exact Or.inl ((mem_sg_pool_iff _ _ _).2 hx)
    refine ⟨fun r b hb => ?_, ⟨hpool, fun r b hb => ?_⟩, rfl, fun r x hx => ?_⟩
    · rcases hnew r b hb with hb | ⟨rfl, hr⟩
      · exact hI r b hb
      · exact hr.symm
    · have hne : Protocol.sgVote b ≠ Protocol.sgVote a := by
        intro heq
        simp only [Protocol.sgVote, Protocol.SGVote.mk.injEq] at heq
        obtain ⟨h1, h2, h3⟩ := heq
        apply hnot
        have hround : b.round = r := hI r b hb
        have hb' : b ∈ st.sg_pool a.round := by rw [← h2, hround]; exact hb
        rw [← h3]
        exact confirmed_mem_round_votes st a b hb' h1
      simp only [ne_eq, hne, not_false_eq_true, Function.update_of_ne]
    · rcases hnew r x hx with hx | ⟨rfl, -⟩
      · exact Or.inl hx
      · exact Or.inr ⟨rfl, by simp only [Function.update_self]⟩

/-- `StampsBounded b st`: the clock of `st` is at most `b`, and the SG vote of every attestation
    `st` holds is stamped with a time at most `b`. -/
def StampsBounded (b : Time) (st : Store V) : Prop :=
  st.t ≤ b ∧ ∀ (k : Round) (a : Attestation V), a ∈ st.sg_pool k →
    ∃ s : Time, s ≤ b ∧ st.timestamp_sg_vote (Protocol.sgVote a) = some (s : Stamp)

/-- A store with the attestations and the SG vote stamps of `st` keeps `RowsErasuresHeld` and
    `KeepsRows`. -/
theorem rows_of_eq (st st' : Store V) (h1 : st'.attestations = st.attestations)
    (h2 : st'.timestamp_sg_vote = st.timestamp_sg_vote) :
    (RowsErasuresHeld st → RowsErasuresHeld st') ∧ KeepsRows st st' := by
  have hp : ∀ r, st'.sg_pool r = st.sg_pool r := fun r => by
    simp only [Store.sg_pool, getElem_fn, h1]
  exact ⟨fun hI r b hb => hI r b (hp r ▸ hb),
    ⟨fun r => (hp r).symm ▸ subset_refl _, fun r b _ => by rw [h2]⟩⟩

/-- A store with the attestations, the SG vote stamps and the clock of `st` keeps `StampsBounded b`. -/
theorem bounded_of_eq (b : Time) (st st' : Store V) (h1 : st'.attestations = st.attestations)
    (h2 : st'.timestamp_sg_vote = st.timestamp_sg_vote) (ht : st'.t = st.t)
    (hB : StampsBounded b st) : StampsBounded b st' := by
  have hp : ∀ r, st'.sg_pool r = st.sg_pool r := fun r => by
    simp only [Store.sg_pool, getElem_fn, h1]
  refine ⟨ht ▸ hB.1, fun k x hx => ?_⟩
  rw [hp] at hx
  rw [h2]
  exact hB.2 k x hx

/-- `Protocol.admit_attestation` keeps `StampsBounded b`. -/
theorem admit_attestation_bounded (b : Time) (C : Config) (st : Store V)
    (row : Attestation V) (hI : RowsErasuresHeld st) (hB : StampsBounded b st) :
    StampsBounded b (Protocol.admit_attestation C st row) := by
  obtain ⟨-, hK, ht, hnew⟩ := admit_attestation_rows C st row hI
  refine ⟨ht ▸ hB.1, fun k x hx => ?_⟩
  rcases hnew k x hx with hold | ⟨rfl, hst⟩
  · obtain ⟨s, hs, hst⟩ := hB.2 k x hold
    exact ⟨s, hs, (hK.2 k x hold).trans hst⟩
  · exact ⟨st.t, hB.1, hst⟩

/-- `Protocol.admit_attestations` keeps `RowsErasuresHeld`, `KeepsRows`, the clock and
    `StampsBounded b`. -/
theorem admit_attestations_rows (C : Config) (rows : List (Attestation V)) (st : Store V)
    (hI : RowsErasuresHeld st) :
    RowsErasuresHeld (Protocol.admit_attestations C st rows) ∧
      KeepsRows st (Protocol.admit_attestations C st rows) ∧
      (Protocol.admit_attestations C st rows).t = st.t ∧
      ∀ b, StampsBounded b st → StampsBounded b (Protocol.admit_attestations C st rows) := by
  rw [admit_attestations_foldl]
  induction rows generalizing st with
  | nil => exact ⟨hI, keepsRows_refl _, rfl, fun _ h => h⟩
  | cons r rs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hI1, hK1, ht1, -⟩ := admit_attestation_rows C st r hI
    obtain ⟨hI2, hK2, ht2, hB2⟩ := ih (Protocol.admit_attestation C st r) hI1
    exact ⟨hI2, keepsRows_trans _ _ _ hK1 hK2, ht2.trans ht1,
      fun b hB => hB2 b (admit_attestation_bounded b C st r hI hB)⟩

/-- Every step from a store with `RowsErasuresHeld` keeps it and `KeepsRows`, sets the clock to `τ`
    or keeps it, and keeps `StampsBounded b` when `τ ≤ b`. -/
theorem rows_step (C : Config) (P : Provisional V) (τ : Time) (st st' : Store V)
    (hs : StoreStep C P τ st st') (hI : RowsErasuresHeld st) :
    RowsErasuresHeld st' ∧ KeepsRows st st' ∧ (τ ≤ st'.t ∨ st'.t = st.t) ∧
      ∀ b, τ ≤ b → StampsBounded b st → StampsBounded b st' := by
  cases hs with
  | grades g =>
    obtain ⟨h1, h2⟩ := rows_of_eq st { st with saved_grades := g } rfl rfl
    exact ⟨h1 hI, h2, Or.inr rfl, fun b _ hB => hB⟩
  | clock =>
    obtain ⟨h1, h2⟩ := rows_of_eq st { st with t := τ, s := C.slotOf τ } rfl rfl
    exact ⟨h1 hI, h2, Or.inl (le_refl _), fun b hτ hB => ⟨hτ, hB.2⟩⟩
  | confirm a b' c =>
    obtain ⟨h1, h2⟩ := rows_of_eq st
      { st with live_confirmed := a, latest_stable := b', latest_confirmed := c } rfl rfl
    exact ⟨h1 hI, h2, Or.inr rfl, fun b _ hB => hB⟩
  | vote u =>
    obtain ⟨x, y, e⟩ := on_goldfish_vote_checked_writes P st u
    rw [e]
    obtain ⟨h1, h2⟩ := rows_of_eq st { st with gf_votes := x, timestamp_vote := y } rfl rfl
    exact ⟨h1 hI, h2, Or.inr rfl, fun b _ hB => hB⟩
  | attest row =>
    obtain ⟨hI', hK, ht, -⟩ := admit_attestation_rows C st row hI
    exact ⟨hI', hK, Or.inr ht, fun b _ hB => admit_attestation_bounded b C st row hI hB⟩
  | block B =>
    rcases on_block_shape C P st B with e | ⟨-, σ', e⟩
    · rw [e]; exact ⟨hI, keepsRows_refl _, Or.inr rfl, fun _ _ hB => hB⟩
    · rw [e]
      obtain ⟨k1, -, -, k4, k5⟩ := block_core_keeps P st B σ'
      obtain ⟨r1, r2⟩ := rows_of_eq st _ k4 k5
      obtain ⟨hI3, hK3, ht3, hB3⟩ := admit_attestations_rows C B.attestations _ (r1 hI)
      exact ⟨hI3, keepsRows_trans _ _ _ r2 hK3, Or.inr (ht3.trans k1),
        fun b _ hB => hB3 b (bounded_of_eq b st _ k4 k5 k1 hB)⟩

/-! ## The properties along a sequence of steps -/

/-- Along a sequence of steps the justified height does not decrease. -/
theorem reach_h_j_le {C : Config} {P : Provisional V} {τ : Time} {a b : Store V}
    (h : StoreReach C P τ a b) : a.h_j ≤ b.h_j :=
  (reach_relation (fun _ => True) (fun x y => x.h_j ≤ y.h_j) (fun _ => le_refl _)
    (fun _ _ _ h1 h2 => le_trans h1 h2) (fun _ _ _ _ => trivial)
    (fun x y hs _ => h_j_le_step C P τ x y hs) h trivial).2

/-- Along a sequence of steps from a store with `RowsErasuresHeld`, `RowsErasuresHeld` holds and
    `KeepsRows` relates the two ends. -/
theorem reach_rows {C : Config} {P : Provisional V} {τ : Time} {a b : Store V}
    (h : StoreReach C P τ a b) (hI : RowsErasuresHeld a) : RowsErasuresHeld b ∧ KeepsRows a b :=
  reach_relation RowsErasuresHeld KeepsRows keepsRows_refl keepsRows_trans
    (fun x y hs hx => (rows_step C P τ x y hs hx).1)
    (fun x y hs hx => (rows_step C P τ x y hs hx).2.1) h hI

/-- Along a sequence of steps whose clock time `τ` is at most `bound`, `RowsErasuresHeld` and
    `StampsBounded bound` are kept. -/
theorem reach_bounded {C : Config} {P : Provisional V} {τ : Time} {a b : Store V} (bound : Time)
    (hτ : τ ≤ bound) (h : StoreReach C P τ a b) (hI : RowsErasuresHeld a) (hB : StampsBounded bound a) :
    RowsErasuresHeld b ∧ StampsBounded bound b :=
  (reach_relation (fun x => RowsErasuresHeld x ∧ StampsBounded bound x) (fun _ _ => True)
    (fun _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun x y hs hx => ⟨(rows_step C P τ x y hs hx.1).1,
      (rows_step C P τ x y hs hx.1).2.2.2 bound hτ hx.2⟩)
    (fun _ _ _ _ => trivial) h ⟨hI, hB⟩).1

/-- The initial store holds no attestation. -/
theorem rowsErasuresHeld_init : RowsErasuresHeld (Store.init : Store V) := by
  intro r b hb
  simp only [Store.sg_pool, Store.init, getElem_fn, List.toFinset_nil,
    Finset.notMem_empty] at hb

/-- The initial store satisfies `StampsBounded bound` when `0 ≤ bound`. -/
theorem stampsBounded_init (bound : Time) (h : 0 ≤ bound) :
    StampsBounded bound (Store.init : Store V) := by
  refine ⟨h, fun k a ha => ?_⟩
  simp only [Store.sg_pool, Store.init, getElem_fn, List.toFinset_nil,
    Finset.notMem_empty] at ha

end SpecRecord.StoreSteps


namespace SpecRecord.HandlersRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (ChainState HeightConfig HealConfig HeightId)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## A tick and a delivery at `Model.spec`, as sequences of steps of the store -/

/-- After the member `tick` of `Model.specBase` at `t`, the node's store is reached from its
    store before by steps whose clock writes set the clock to `t`. -/
theorem specBase_tick_reach (S : Setup V) (v : V) (n : Spec.NodeState V) (t : Time)
    (out : Spec.NodeState V × List (NamedObject V))
    (h : (Model.specBase (V := V)).tick S v n t ⇢ out) :
    StoreSteps.StoreReach (Setup.toSpec S).C (Setup.toSpec S).P t n.st out.1.st := by
  change Member.tick S v n t ⇢ out at h
  unfold Member.tick at h
  rw [returns_successOutcomes] at h
  cases e : (Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P (Setup.toSpec S).X n t).run []
    with
  | error err => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    cases h
    exact StoreSteps.tick_reach _ _ _ n x.1 t [] x.2 e

/-- After the member `tick` of `Model.spec` at `t`, the node's store is reached from its store
    before by steps whose clock writes set the clock to `t`. -/
theorem spec_tick_reach (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (h : (Model.spec (V := V)).tick S v n t ⇢ out) :
    StoreSteps.StoreReach (Setup.toSpec S).C (Setup.toSpec S).P t n.val.st out.1.val.st :=
  specBase_tick_reach S v n.val t (out.1.val, out.2) h

/-- After the member `process` of `Model.specBase`, the node's store is reached from its store
    before by steps, for every clock time `τ`. -/
theorem specBase_process_reach (S : Setup V) (n n' : Spec.NodeState V)
    (o : NamedObject V) (h : (Model.specBase (V := V)).process S n o ⇢ n') (τ : Time) :
    StoreSteps.StoreReach (Setup.toSpec S).C (Setup.toSpec S).P τ n.st n'.st := by
  change Member.process S n o ⇢ n' at h
  unfold Member.process at h
  rw [returns_pure] at h
  subst h
  exact StoreSteps.receive_reach _ _ τ n _

/-- After the member `process` of `Model.spec`, the node's store is reached from its store
    before by steps, for every clock time `τ`. -/
theorem spec_process_reach (S : Setup V) (n n' : (Model.spec (V := V)).N)
    (o : NamedObject V) (h : (Model.spec (V := V)).process S n o ⇢ n') (τ : Time) :
    StoreSteps.StoreReach (Setup.toSpec S).C (Setup.toSpec S).P τ n.val.st n'.val.st :=
  specBase_process_reach S n.val n'.val o h τ

/-- The member `wake` of `Model.specBase` keeps the node's store. -/
theorem specBase_wake_st (n : Spec.NodeState V) :
    ((Model.specBase (V := V)).wake n).st = n.st := rfl

/-- The member `wake` of `Model.spec` keeps the node's store. -/
theorem spec_wake_st (n : (Model.spec (V := V)).N) :
    ((Model.spec (V := V)).wake n).val.st = n.val.st :=
  specBase_wake_st n.val

/-! ## Folding events at `Model.spec` -/

/-- Let `Q` be a property of stores kept by every tick and every receipt of `Model.specBase`,
    and `R` a reflexive, transitive relation that each of them satisfies. If `Q` holds of every
    store of `w₁`, then in every world the events lead to from `w₁` under
    `worldStepOf Model.spec S`, `Q` holds of every store and `R` relates each validator's store
    in `w₁` to its store there. -/
theorem fold_relation_ok (S : Setup V) (Q : Spec.Store V → Prop)
    (R : Spec.Store V → Spec.Store V → Prop)
    (hrefl : ∀ st, R st st) (htrans : ∀ a b c, R a b → R b c → R a c)
    (es : List (Record.Event V))
    (htick : ∀ v t, Record.Event.tick v t ∈ es → ∀ (n : Spec.NodeState V) out,
      (Model.specBase (V := V)).tick S v n t ⇢ out → Q n.st → Q out.1.st ∧ R n.st out.1.st)
    (hproc : ∀ (n : Spec.NodeState V) o n', (Model.specBase (V := V)).process S n o ⇢ n' →
      Q n.st → Q n'.st ∧ R n.st n'.st)
    (w₁ : V → (Model.spec (V := V)).N) (hI : ∀ v, Q (w₁ v).val.st) :
    ∀ w₂ ∈ es.foldlM (worldStepOf (Model.spec (V := V)) S) w₁,
      ∀ v, Q (w₂ v).val.st ∧ R (w₁ v).val.st (w₂ v).val.st := by
  induction es generalizing w₁ with
  | nil =>
    intro w₂ hw v
    have hw' : w₂ = w₁ := hw
    subst hw'
    exact ⟨hI v, hrefl _⟩
  | cons e es ih =>
    intro w₂ hw v
    rw [List.foldlM_cons, Set.bind_def] at hw
    obtain ⟨w', hw', hw₂⟩ := Set.mem_iUnion₂.mp hw
    have hstep : ∀ u, Q (w' u).val.st ∧ R (w₁ u).val.st (w' u).val.st := by
      cases e with
      | wake p t =>
        simp only [worldStepOf, Set.mem_singleton_iff] at hw'
        subst hw'
        intro u
        by_cases hu : u = p
        · subst hu
          simp only [Function.update_self, spec_wake_st]
          exact ⟨hI u, hrefl _⟩
        · simp only [ne_eq, hu, not_false_eq_true, Function.update_of_ne]
          exact ⟨hI u, hrefl _⟩
      | tick p t =>
        simp only [worldStepOf, Set.mem_setOf_eq] at hw'
        rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
        · intro u
          by_cases hu : u = p
          · subst hu
            simp only [Function.update_self]
            exact htick u t (List.mem_cons_self) (w₁ u).val (out.1.val, out.2) hout (hI u)
          · simp only [ne_eq, hu, not_false_eq_true, Function.update_of_ne]
            exact ⟨hI u, hrefl _⟩
        · exact fun u => ⟨hI u, hrefl _⟩
      | deliver p o t =>
        simp only [worldStepOf, Set.mem_setOf_eq] at hw'
        rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
        · intro u
          by_cases hu : u = p
          · subst hu
            simp only [Function.update_self]
            exact hproc (w₁ u).val o n'.val hn' (hI u)
          · simp only [ne_eq, hu, not_false_eq_true, Function.update_of_ne]
            exact ⟨hI u, hrefl _⟩
        · exact fun u => ⟨hI u, hrefl _⟩
    have := ih (fun v t hm => htick v t (List.mem_cons_of_mem _ hm)) w' (fun u => (hstep u).1) w₂ hw₂ v
    exact ⟨this.1, htrans _ _ _ (hstep v).2 this.2⟩

end SpecRecord.HandlersRunFacts

namespace SpecRecord.HandlersFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (ChainState HeightConfig HealConfig HeightId)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## Lemmas for the subtype -/

/-- The two cases of the block-admitting members of `Model.spec`: when a block of `st`'s tree
    other than `Block.toSpecNamed B` has that block's root, `on_block_with` and
    `ns_process_block_core` both return `st`; otherwise they are the members of
    `Model.specBase` at `st.val`. -/
theorem ok_block_cases (admission : Protocol.CarriedAdmission) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V) :
    (RootHeldByOther st.val.T (Spec.Block.toSpecNamed B) ∧
        (Model.spec (V := V)).on_block_with admission E hc cfg st B = st ∧
        (Model.spec (V := V)).ns_process_block_core E hc cfg st B = st) ∨
      (¬ RootHeldByOther st.val.T (Spec.Block.toSpecNamed B) ∧
        ((Model.spec (V := V)).on_block_with admission E hc cfg st B).val =
          (Model.specBase (V := V)).on_block_with admission E hc cfg st.val B ∧
        ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).val =
          (Model.specBase (V := V)).ns_process_block_core E hc cfg st.val B) := by
  by_cases h : RootHeldByOther st.val.T (Spec.Block.toSpecNamed B)
  · exact Or.inl ⟨h, OkMember.on_block_with_of_held h, OkMember.ns_process_block_core_of_held h⟩
  · exact Or.inr ⟨h, OkMember.on_block_with_val_of_not_held h,
      OkMember.ns_process_block_core_val_of_not_held h⟩

/-! ## The members at the images of their arguments -/

/-- `(Member.core X).toProof = X.toProofNamed.core`. -/
theorem image_core (X : Spec.Store V) : (Member.core X).toProof = X.toProofNamed.core :=
  rfl

/-- `(Member.on_sg_vote hc st a).toProof = Protocol.on_sg_vote hc st.toProof a`. -/
theorem image_on_sg_vote (hc : HealConfig) (st : Spec.Store V)
    (a : CombinedAttestation V) :
    (Member.on_sg_vote hc st a).toProof = Protocol.on_sg_vote hc st.toProof a := by
  rw [Member.on_sg_vote, ← toProof_on_sg_vote, Spec.Attestation.toProof_toSpec]

/-- `(Member.on_goldfish_vote_checked E st u).toProof = Protocol.on_goldfish_vote_checked E st.toProof u`. -/
theorem image_on_goldfish_vote_checked (E : Env V) (st : Spec.Store V)
    (u : GoldfishVote V) :
    (Member.on_goldfish_vote_checked E st u).toProof =
      Protocol.on_goldfish_vote_checked E st.toProof u := by
  rw [Member.on_goldfish_vote_checked, ← toProof_on_goldfish_vote_checked,
    Spec.GoldfishVote.toProof_toSpec]

/-- `(Member.on_goldfish_vote st u).toProof = Protocol.on_goldfish_vote st.toProof u`. -/
theorem image_on_goldfish_vote (st : Spec.Store V) (u : GoldfishVote V) :
    (Member.on_goldfish_vote st u).toProof = Protocol.on_goldfish_vote st.toProof u := by
  rw [Member.on_goldfish_vote, ← toProof_on_goldfish_vote,
    Spec.GoldfishVote.toProof_toSpec]

/-- `(Member.admit_row hc st a).toProofNamed = Protocol.NamedAdmission.admit_row hc st.toProofNamed a`. -/
theorem image_admit_row (hc : HealConfig) (st : Spec.Store V)
    (a : NamedAttestation V) :
    (Member.admit_row hc st a).toProofNamed =
      Protocol.NamedAdmission.admit_row hc st.toProofNamed a := by
  rw [Member.admit_row, ← toProof_admit_row, Spec.Attestation.toProofNamed_toSpecNamed]

/-- `(Member.admit_rows hc st rows).toProofNamed = Protocol.NamedAdmission.admit_rows hc st.toProofNamed rows`. -/
theorem image_admit_rows (hc : HealConfig) (st : Spec.Store V)
    (rows : List (NamedAttestation V)) :
    (Member.admit_rows hc st rows).toProofNamed =
      Protocol.NamedAdmission.admit_rows hc st.toProofNamed rows := by
  rw [Member.admit_rows, ← toProof_admit_rows, List.map_map,
    Spec.Attestation.toProofNamed_comp_toSpecNamed, List.map_id]

/-- `(Member.ns_setClock E st t).toProofNamed = Protocol.NamedStore.setClock E st.toProofNamed t`. -/
theorem image_ns_setClock (E : Env V) (st : Spec.Store V) (t : Time) :
    (Member.ns_setClock E st t).toProofNamed = Protocol.NamedStore.setClock E st.toProofNamed t := by
  unfold Member.ns_setClock Protocol.NamedStore.setClock DecoupledConsensusModel.Env.slotOf
    DecoupledConsensusModel.slotOfTime
  rfl

/-- `Member.ns_initial.toProofNamed = Protocol.NamedStore.initial`. -/
theorem image_ns_initial :
    (Member.ns_initial : Spec.Store V).toProofNamed = Protocol.NamedStore.initial :=
  toProof_ns_initial.symm

/-- `Member.store_pool st s = Protocol.Store.pool st.toProof s`. -/
theorem image_store_pool (st : Spec.Store V) (s : Slot) :
    Member.store_pool st s = Protocol.Store.pool st.toProof s :=
  (toProof_store_pool st s).symm

/-- `Member.store_sg_pool st r = Protocol.Store.sg_pool st.toProof r`. -/
theorem image_store_sg_pool (st : Spec.Store V) (r : Round) :
    Member.store_sg_pool st r = Protocol.Store.sg_pool st.toProof r :=
  (toProof_store_sg_pool st r).symm

/-- `Member.round_votes st a = Protocol.round_votes st.toProof a`. -/
theorem image_round_votes (st : Spec.Store V) (a : CombinedAttestation V) :
    Member.round_votes st a = Protocol.round_votes st.toProof a := by
  rw [Member.round_votes, ← toProof_round_votes, Spec.Attestation.toProof_toSpec]

/-- `Member.sgVote a = Protocol.sgVote a`. -/
theorem image_sgVote (a : CombinedAttestation V) : Member.sgVote a = Protocol.sgVote a := by
  rw [Member.sgVote, ← toProof_sgVote, Spec.Attestation.toProof_toSpec]

/-- `Block.toSpec` keeps ancestry:
    `(Block.toSpec B).ancestorEq (Block.toSpec C) = Block.preceq B C`. -/
theorem toSpec_ancestorEq (B C : Block V) :
    (Spec.Block.toSpec B).ancestorEq (Spec.Block.toSpec C) =
      Block.preceq B C := by
  induction C with
  | genesis =>
      have hg : Spec.Block.toSpec (Block.genesis : Block V) =
          Spec.Block.genesis := rfl
      have hgi : Spec.Block.toSpec B = Spec.Block.genesis ↔
          B = Block.genesis := by
        rw [← hg]; exact Spec.Block.toSpec_injective.eq_iff
      rw [hg, Block.preceq]
      simp only [Spec.Block.ancestorEq, hgi]
  | node p s r votes support ats proposer ih =>
      have hn : Spec.Block.toSpec (Block.node p s r votes support ats proposer) =
          .node (Spec.Block.toSpec p) s (Spec.BlockId.toSpec r)
            (votes.map Spec.GoldfishVote.toSpec)
            (support.map Spec.GoldfishVote.toSpec)
            (ats.map Spec.Attestation.toSpec) proposer := rfl
      have heq : Spec.Block.toSpec B =
            Spec.Block.toSpec (Block.node p s r votes support ats proposer) ↔
          B = Block.node p s r votes support ats proposer :=
        Spec.Block.toSpec_injective.eq_iff
      rw [Block.preceq]
      rw [hn] at heq ⊢
      simp only [Spec.Block.ancestorEq, heq, ih]

/-- The attestations of a block's named image are the block's attestations, each mapped by
    `Attestation.toProofNamed`. -/
theorem toProofNamed_attestations (B : Spec.Block V) :
    B.toProofNamed.attestations = B.attestations.map Spec.Attestation.toProofNamed := by
  cases B <;> simp [Spec.Block.toProofNamed, Spec.Block.attestations,
    NamedBlock.attestations]

/-- `Member.advance_confirmed old c = Protocol.advance_confirmed old c`. -/
theorem image_advance_confirmed (old c : Block V) :
    Member.advance_confirmed old c = Protocol.advance_confirmed old c := by
  unfold Member.advance_confirmed Spec.Protocol.advance_confirmed
    Protocol.advance_confirmed
  simp only [Id.run, pure, toSpec_ancestorEq]
  split_ifs <;> exact Spec.Block.toProof_toSpec _

/-- `Member.floor_on_stable stable c old = Protocol.floor_on_stable stable c old`. -/
theorem image_floor_on_stable (stable c old : Block V) :
    Member.floor_on_stable stable c old = Protocol.floor_on_stable stable c old := by
  unfold Member.floor_on_stable Spec.Protocol.floor_on_stable
    Protocol.floor_on_stable
  simp only [Id.run, pure, toSpec_ancestorEq]
  split_ifs <;> exact Spec.Block.toProof_toSpec _

/-- `Member.carried_attestations_admissible hc B = Protocol.carried_attestations_admissible hc B`. -/
theorem image_carried_attestations_admissible (hc : HealConfig) (B : Block V) :
    Member.carried_attestations_admissible hc B = Protocol.carried_attestations_admissible hc B := by
  rw [Member.carried_attestations_admissible, ← toProof_carried_attestations_admissible,
    Spec.Block.toProof_toSpec]

/-- `Member.round_of hc s = hc.round_of s`. -/
theorem image_round_of (hc : HealConfig) (s : Slot) : Member.round_of hc s = hc.round_of s := by
  unfold Member.round_of HealConfig.round_of
  rfl

/-- A block's named image is among the named blocks of `X.toProofNamed` exactly when the block is in
    `X`'s tree. -/
theorem block_mem_bodies (X : Spec.Store V) (B : Spec.Block V) :
    B.toProofNamed ∈ X.toProofNamed.bodies ↔ B ∈ X.T :=
  Finset.mem_map' Spec.Block.toProofNamedEmb

/-- Every named block is the named image of a block. -/
theorem exists_namedBlock (B : NamedBlock V) : ∃ B' : Spec.Block V, B = B'.toProofNamed :=
  ⟨_, (Spec.Block.toProofNamed_toSpecNamed B).symm⟩

/-- `(Member.admit_carried adm hc before after B).toProofNamed = Protocol.NamedAdmission.admit_carried adm hc before.toProofNamed after.toProofNamed B`. -/
theorem image_admit_carried (adm : Protocol.CarriedAdmission) (hc : HealConfig)
    (before after : Spec.Store V) (B : NamedBlock V) :
    (Member.admit_carried adm hc before after B).toProofNamed =
      Protocol.NamedAdmission.admit_carried adm hc before.toProofNamed after.toProofNamed B := by
  obtain ⟨B', rfl⟩ := exists_namedBlock B
  rw [Member.admit_carried, Spec.Block.toSpecNamed_toProofNamed]
  unfold Handlers.admitCarried Protocol.NamedAdmission.admit_carried
  simp only [block_mem_bodies]
  split_ifs
  · rw [toProofNamed_attestations,
      toProof_admit_rows (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig]
  · rfl

/-- `Member.equivocates votes v = Protocol.equivocates votes v`. -/
theorem image_equivocates (votes : Finset (GoldfishVote V)) (v : V) :
    Member.equivocates votes v = Protocol.equivocates votes v := by
  rw [Member.equivocates, ← toProof_equivocates, Finset.map_map]
  congr 1
  ext u
  simp [ChainStateToHandlers.goldfishVoteToSpecEmb]

/-- Unfolds `Model.spec`'s readers and members into reads of the images `toProof`,
    `toProofNamed`, and rewrites each member with its `image_` lemma, in the goal and in every
    hypothesis. -/
local macro "unfold_spec" : tactic => `(tactic| simp only [Model.spec, Model.specBase, Model.S.t,
  Model.S.s, Model.S.T, Model.S.timestamp_block, Model.S.timestamp_vote, Model.S.timestamp_sg_vote,
  Model.S.σ, Model.S.gf_votes, Model.S.sg_votes, Model.S.F, Model.S.J, Model.S.h_j, Model.S.h_max,
  Model.S.live_confirmed, Model.S.latest_confirmed, Model.S.latest_stable, Model.NS.core,
  Model.NS.bodies, Model.NS.sg_rows, Model.N.st, Model.S.toHealing, Model.S.pool, Model.S.sg_pool,
  Model.NS.setClock, Model.NS.process_block_core, Model.NS.commitBlock,
  ChainStateModel.CS.h, ChainStateModel.CS.J, ChainStateModel.CS.h_j, ChainStateModel.CS.F,
  ChainStateModel.CS.h_F,
  Member.store_t, Member.store_s, Member.store_T, Member.store_timestamp_block,
  Member.store_timestamp_vote, Member.store_timestamp_sg_vote, Member.store_gf_votes,
  Member.store_sg_votes, Member.store_F, Member.store_J, Member.store_h_j, Member.store_h_max,
  Member.store_live_confirmed, Member.store_latest_confirmed, Member.store_latest_stable,
  Member.bodies, Member.sg_rows, Member.h, Member.J, Member.h_j, Member.F, Member.h_F,
  image_core, image_on_sg_vote, image_on_goldfish_vote_checked, image_on_goldfish_vote,
  image_admit_row, image_admit_rows,
  image_ns_setClock, image_ns_initial, image_store_pool, image_store_sg_pool, image_round_votes,
  image_sgVote, image_advance_confirmed, image_floor_on_stable,
  image_carried_attestations_admissible, image_round_of,
  image_admit_carried, image_equivocates] at *)

/-! ## Goldfish votes and named attestations as images -/

/-- Every Goldfish vote is the image of a Goldfish vote of the spec. -/
theorem exists_vote (u : GoldfishVote V) : ∃ u' : Spec.GoldfishVote V, u = u'.toProof :=
  ⟨_, (Spec.GoldfishVote.toProof_toSpec u).symm⟩

/-- Every named attestation is the named image of an attestation of the spec. -/
theorem exists_namedAtt (a : NamedAttestation V) :
    ∃ a' : Spec.Attestation V, a = a'.toProofNamed :=
  ⟨_, (Spec.Attestation.toProofNamed_toSpecNamed a).symm⟩

/-! ## The block admission and the finality update, field by field -/

/-- The outcomes of `Handlers.updateFinalityWith st σ`: `h_max` becomes `max st.h_max σ.h`; the
    justified block and its height are `st`'s, or `σ`'s when `st.F` is an ancestor of `σ.J` and
    `(st.h_j, root of st.J)` is lexicographically less than `(σ.h_j, root of σ.J)`; the finalized
    block is `st.F`, or `σ.F` when `st.F` is a strict ancestor of it and it is an ancestor of the
    justified block just written. -/
theorem updateFinalityWith_cases (st : Spec.Store V)
    (σ : Spec.Protocol.ChainState V) :
    (Handlers.updateFinalityWith st σ).h_max = max st.h_max σ.h ∧
    (((Handlers.updateFinalityWith st σ).J = st.J ∧ (Handlers.updateFinalityWith st σ).h_j = st.h_j) ∨
      ((Handlers.updateFinalityWith st σ).J = σ.J ∧ (Handlers.updateFinalityWith st σ).h_j = σ.h_j ∧
        st.F.ancestorEq σ.J = true ∧ toLex (st.h_j, st.J.root) < toLex (σ.h_j, σ.J.root))) ∧
    ((Handlers.updateFinalityWith st σ).F = st.F ∨
      ((Handlers.updateFinalityWith st σ).F = σ.F ∧ st.F.ancestorStrict σ.F = true ∧
        σ.F.ancestorEq (Handlers.updateFinalityWith st σ).J = true)) := by
  unfold Handlers.updateFinalityWith
  simp only [Id.run, pure]
  split_ifs with h1 h2 h2
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    exact ⟨rfl, Or.inr ⟨rfl, rfl, h1.1, h1.2⟩, Or.inr ⟨rfl, h2.1.1, h2.1.2⟩⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨rfl, Or.inr ⟨rfl, rfl, h1.1, h1.2⟩, Or.inl rfl⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, h2.1.1, h2.1.2⟩⟩
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩

/-- A strict ancestor is an ancestor. -/
theorem ancestorEq_of_ancestorStrict {B C : Spec.Block V} (h : B.ancestorStrict C = true) :
    B.ancestorEq C = true := by
  simp only [Spec.Block.ancestorStrict, Bool.and_eq_true] at h
  exact h.2

/-- `ancestorEq` is reflexive. -/
theorem ancestorEq_refl (B : Spec.Block V) : B.ancestorEq B = true := by
  cases B <;> simp [Spec.Block.ancestorEq]

/-- The store's finalized block is an ancestor of, or equal to, the finalized block after
    `Handlers.updateFinalityWith`. -/
theorem updateFinalityWith_F (st : Spec.Store V) (σ : Spec.Protocol.ChainState V) :
    st.F.ancestorEq (Handlers.updateFinalityWith st σ).F = true := by
  rcases (updateFinalityWith_cases st σ).2.2 with h | ⟨h, h', -⟩
  · rw [h]; exact ancestorEq_refl _
  · rw [h]; exact ancestorEq_of_ancestorStrict h'

@[simp] theorem updateFinalityWith_t (st : Spec.Store V) (σ : Spec.Protocol.ChainState V) :
    (Handlers.updateFinalityWith st σ).t = st.t := by
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ; rw [e]

@[simp] theorem updateFinalityWith_s (st : Spec.Store V) (σ : Spec.Protocol.ChainState V) :
    (Handlers.updateFinalityWith st σ).s = st.s := by
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ; rw [e]

@[simp] theorem updateFinalityWith_T (st : Spec.Store V) (σ : Spec.Protocol.ChainState V) :
    (Handlers.updateFinalityWith st σ).T = st.T := by
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ; rw [e]

@[simp] theorem updateFinalityWith_attestations (st : Spec.Store V)
    (σ : Spec.Protocol.ChainState V) :
    (Handlers.updateFinalityWith st σ).attestations = st.attestations := by
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ; rw [e]

@[simp] theorem foldl_checked_t (P : Spec.Provisional V)
    (votes : List (Spec.GoldfishVote V)) (X : Spec.Store V) :
    (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) X).t = X.t := by
  obtain ⟨x, y, e⟩ := StoreSteps.foldl_checked_writes P votes X; rw [e]

@[simp] theorem foldl_checked_s (P : Spec.Provisional V)
    (votes : List (Spec.GoldfishVote V)) (X : Spec.Store V) :
    (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) X).s = X.s := by
  obtain ⟨x, y, e⟩ := StoreSteps.foldl_checked_writes P votes X; rw [e]

@[simp] theorem foldl_checked_T (P : Spec.Provisional V)
    (votes : List (Spec.GoldfishVote V)) (X : Spec.Store V) :
    (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) X).T = X.T := by
  obtain ⟨x, y, e⟩ := StoreSteps.foldl_checked_writes P votes X; rw [e]

@[simp] theorem foldl_checked_F (P : Spec.Provisional V)
    (votes : List (Spec.GoldfishVote V)) (X : Spec.Store V) :
    (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) X).F = X.F := by
  obtain ⟨x, y, e⟩ := StoreSteps.foldl_checked_writes P votes X; rw [e]

@[simp] theorem foldl_checked_attestations (P : Spec.Provisional V)
    (votes : List (Spec.GoldfishVote V)) (X : Spec.Store V) :
    (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) X).attestations =
      X.attestations := by
  obtain ⟨x, y, e⟩ := StoreSteps.foldl_checked_writes P votes X; rw [e]

/-- `Handlers.blockCore C P st B` is the finality update of the store with `B`'s chain state
    written, `B` added to the tree and stamped, and the Goldfish votes `B` includes admitted. -/
theorem blockCore_eq (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    Handlers.blockCore C P st B =
      Spec.Protocol.update_finality
        (B.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P)
        { st with σ := Function.update st.σ B (Spec.Protocol.state_transition C P (st.σ B.parent) B),
                  T := st.T ∪ {B},
                  timestamp_block := Function.update st.timestamp_block B (some (st.t : Spec.Stamp)) })
        B := by
  simp only [Handlers.blockCore, Id.run, List.forIn_pure_yield_eq_foldl]
  rfl

/-- `Handlers.blockCore` keeps the clock, the slot and the attestations, adds `B` to the tree, and
    keeps the finalized block or moves it to a descendant. -/
theorem blockCore_fields (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Handlers.blockCore C P st B).t = st.t ∧ (Handlers.blockCore C P st B).s = st.s ∧
      (Handlers.blockCore C P st B).attestations = st.attestations ∧
      (Handlers.blockCore C P st B).T = st.T ∪ {B} ∧
      st.F.ancestorEq (Handlers.blockCore C P st B).F = true := by
  rw [blockCore_eq, Handlers.update_finality_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [updateFinalityWith_t, foldl_checked_t]
  · simp only [updateFinalityWith_s, foldl_checked_s]
  · simp only [updateFinalityWith_attestations, foldl_checked_attestations]
  · simp only [updateFinalityWith_T, foldl_checked_T]
  · have := updateFinalityWith_F (B.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P)
        { st with σ := Function.update st.σ B (Spec.Protocol.state_transition C P (st.σ B.parent) B),
                  T := st.T ∪ {B},
                  timestamp_block := Function.update st.timestamp_block B (some (st.t : Spec.Stamp)) })
      (Spec.Store.σ (B.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P)
        { st with σ := Function.update st.σ B (Spec.Protocol.state_transition C P (st.σ B.parent) B),
                  T := st.T ∪ {B},
                  timestamp_block := Function.update st.timestamp_block B (some (st.t : Spec.Stamp)) }) B)
    rw [foldl_checked_F] at this
    exact this

/-- `Handlers.admitBlockCore` keeps the clock, the slot and the attestations, and keeps the
    finalized block or moves it to a descendant. -/
theorem admitBlockCore_fields (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Handlers.admitBlockCore C P st B).t = st.t ∧ (Handlers.admitBlockCore C P st B).s = st.s ∧
      (Handlers.admitBlockCore C P st B).attestations = st.attestations ∧
      st.F.ancestorEq (Handlers.admitBlockCore C P st B).F = true := by
  unfold Handlers.admitBlockCore
  split_ifs
  · obtain ⟨h1, h2, h3, -, h5⟩ := blockCore_fields C P st B
    exact ⟨h1, h2, h3, h5⟩
  · exact ⟨rfl, rfl, rfl, ancestorEq_refl _⟩

/-- `Protocol.on_block` is `Handlers.admitBlockCore`, followed by the admission of the attestations
    `B` includes or by nothing. -/
theorem on_block_eq_core (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    Spec.Protocol.on_block C P st B =
        Spec.Protocol.admit_attestations C (Handlers.admitBlockCore C P st B) B.attestations ∨
      Spec.Protocol.on_block C P st B = Handlers.admitBlockCore C P st B := by
  rw [Handlers.on_block_eq]
  split_ifs with h
  · exact Or.inl rfl
  · right
    unfold Handlers.admitBlockCore
    rw [if_neg h]

/-- `Protocol.on_block` has the tree, the clock, the slot and the finalized block of
    `Handlers.admitBlockCore`. -/
theorem on_block_fields (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Spec.Protocol.on_block C P st B).T = (Handlers.admitBlockCore C P st B).T ∧
      (Spec.Protocol.on_block C P st B).t = (Handlers.admitBlockCore C P st B).t ∧
      (Spec.Protocol.on_block C P st B).s = (Handlers.admitBlockCore C P st B).s ∧
      (Spec.Protocol.on_block C P st B).F = (Handlers.admitBlockCore C P st B).F := by
  rcases on_block_eq_core C P st B with e | e
  · rw [e]
    obtain ⟨x, y, e'⟩ := StoreSteps.admit_attestations_writes C B.attestations
      (Handlers.admitBlockCore C P st B)
    rw [e']
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [e]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- `Block.toSpecNamed` keeps the parent edge. -/
theorem toSpecNamed_parent (B : NamedBlock V) :
    (Spec.Block.toSpecNamed B).parent = Spec.Block.toSpecNamed B.parent := by
  cases B <;> simp [Spec.Block.toSpecNamed, NamedBlock.parent, Spec.Block.parent]

/-- `Block.toSpecNamed` maps the included attestations by `Attestation.toSpecNamed`. -/
theorem toSpecNamed_attestations (B : NamedBlock V) :
    (Spec.Block.toSpecNamed B).attestations =
      B.attestations.map Spec.Attestation.toSpecNamed := by
  cases B <;> simp [Spec.Block.toSpecNamed, NamedBlock.attestations,
    Spec.Block.attestations]

/-- A named block is among the named blocks of `X.toProofNamed` exactly when `Block.toSpecNamed B`
    is in `X`'s tree. -/
theorem mem_bodies_iff (X : Spec.Store V) (B : NamedBlock V) :
    B ∈ X.toProofNamed.bodies ↔ Spec.Block.toSpecNamed B ∈ X.T := by
  conv_lhs => rw [← Spec.Block.toProofNamed_toSpecNamed B]
  exact block_mem_bodies X _

/-- `Protocol.admit_attestations` at `Config.toSpec E hc cfg` does not depend on `E` and `cfg`. -/
theorem admit_attestations_config (E E' : Env V) (hc : HealConfig) (cfg cfg' : HeightConfig)
    (st : Spec.Store V) (rows : List (Spec.Attestation V)) :
    Spec.Protocol.admit_attestations (Spec.Config.toSpec E hc cfg) st rows =
      Spec.Protocol.admit_attestations (Spec.Config.toSpec E' hc cfg') st rows :=
  rfl

@[simp] theorem admitBlockCore_t (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Handlers.admitBlockCore C P st B).t = st.t := (admitBlockCore_fields C P st B).1

@[simp] theorem admitBlockCore_s (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Handlers.admitBlockCore C P st B).s = st.s := (admitBlockCore_fields C P st B).2.1

@[simp] theorem admitBlockCore_attestations (C : Spec.Config)
    (P : Spec.Provisional V) (st : Spec.Store V) (B : Spec.Block V) :
    (Handlers.admitBlockCore C P st B).attestations = st.attestations :=
  (admitBlockCore_fields C P st B).2.2.1

@[simp] theorem on_block_T (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Spec.Protocol.on_block C P st B).T = (Handlers.admitBlockCore C P st B).T :=
  (on_block_fields C P st B).1

@[simp] theorem on_block_t (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Spec.Protocol.on_block C P st B).t = (Handlers.admitBlockCore C P st B).t :=
  (on_block_fields C P st B).2.1

@[simp] theorem on_block_s (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Spec.Protocol.on_block C P st B).s = (Handlers.admitBlockCore C P st B).s :=
  (on_block_fields C P st B).2.2.1

@[simp] theorem on_block_F (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    (Spec.Protocol.on_block C P st B).F = (Handlers.admitBlockCore C P st B).F :=
  (on_block_fields C P st B).2.2.2

/-- Unfolds `Model.spec`'s store readers and block handlers into the spec's fields and
    routines, with the frame lemmas of `Protocol.on_block` and `Handlers.admitBlockCore`. -/
local macro "unfold_draft" : tactic => `(tactic| simp only [Model.spec, Model.specBase, Model.NS.core,
  Model.NS.bodies, Model.NS.sg_rows, Model.S.F, Model.S.t, Model.S.s, Model.S.sg_votes,
  Member.store_F, Member.store_t, Member.store_s, Member.store_sg_votes, Member.core, id,
  Member.bodies, Member.sg_rows, Member.on_block_with, Member.ns_process_block_core,
  Spec.Store.toProof_F, Spec.Store.toProof_t, Spec.Store.toProof_s,
  Spec.Store.toProof_sg_votes, Spec.Store.toProofNamed_sg_rows,
  Spec.Store.toProofNamed_core, on_block_T, on_block_F, on_block_t, on_block_s,
  admitBlockCore_t, admitBlockCore_s, admitBlockCore_attestations])

/-- `a'.toProofNamed` is among the named rows of round `r` of `st.toProofNamed` exactly when `a'` is
    in `st.sg_pool r`. -/
theorem mem_sg_rows_iff (st : Spec.Store V) (r : Round)
    (a' : Spec.Attestation V) :
    a'.toProofNamed ∈ st.toProofNamed.sg_rows r ↔ a' ∈ st.sg_pool r := by
  rw [StoreSteps.mem_sg_pool_iff, Spec.Store.toProofNamed_sg_rows, List.mem_map]
  constructor
  · rintro ⟨b, hb, he⟩
    rw [Spec.Attestation.toProofNamed_injective he] at hb
    exact hb
  · intro h
    exact ⟨a', h, rfl⟩

/-- `Protocol.admit_attestation C X a = X` exactly when `Protocol.attestation_admissible` refuses
    `a`. -/
theorem admit_attestation_eq_self_iff (C : Spec.Config) (X : Spec.Store V)
    (a : Spec.Attestation V) :
    Spec.Protocol.admit_attestation C X a = X ↔
      Spec.Protocol.attestation_admissible C X a = false := by
  unfold Spec.Protocol.admit_attestation Spec.Protocol.add_attestation
  simp only [Id.run, pure, StoreSteps.getElem_fn]
  split_ifs with h
  · simp only [h, Bool.true_eq_false, iff_false]
    intro e
    have h2 := congrArg (fun Y : Spec.Store V => (Y.attestations a.round).length) e
    simp only [Function.update_self, List.length_append, List.length_singleton] at h2
    omega
  · simp only [Bool.not_eq_true] at h
    simp only [h]

/-- The admission test reads, of the attestation, only its sender, its round and its confirmed
    block. -/
theorem attestation_admissible_congr (C : Spec.Config) (X : Spec.Store V)
    {x y : Spec.Attestation V} (hr : x.round = y.round) (hv : x.val_index = y.val_index)
    (hc : x.confirmed = y.confirmed) :
    Spec.Protocol.attestation_admissible C X x =
      Spec.Protocol.attestation_admissible C X y := by
  have hrv : Spec.Protocol.round_votes X x = Spec.Protocol.round_votes X y := by
    unfold Spec.Protocol.round_votes
    rw [hr, hv]
  unfold Spec.Protocol.attestation_admissible
  rw [hrv, hr, hc]

/-- `Protocol.admit_attestation C X a` keeps the slot, and an attestation it newly holds is `a`, of
    a round at most the round of the store's slot. -/
theorem admit_attestation_new_round (C : Spec.Config) (X : Spec.Store V)
    (a : Spec.Attestation V) :
    (Spec.Protocol.admit_attestation C X a).s = X.s ∧
      ∀ (r : Round) (x : Spec.Attestation V),
        x ∈ (Spec.Protocol.admit_attestation C X a).sg_pool r → x ∉ X.sg_pool r →
          x.round ≤ C.round_of X.s := by
  obtain ⟨x0, y0, e0⟩ := StoreSteps.admit_attestation_writes C X a
  refine ⟨by rw [e0], fun r x hx hnot => ?_⟩
  by_cases hadm : Spec.Protocol.attestation_admissible C X a = true
  · have hx' := hx
    rw [StoreSteps.mem_sg_pool_iff] at hx'
    unfold Spec.Protocol.admit_attestation Spec.Protocol.add_attestation at hx'
    simp only [Id.run, pure, StoreSteps.getElem_fn, hadm, if_true] at hx'
    by_cases hr : r = a.round
    · subst hr
      simp only [Function.update_self, List.mem_append, List.mem_singleton] at hx'
      rcases hx' with hx' | rfl
      · exact absurd ((StoreSteps.mem_sg_pool_iff _ _ _).2 hx') hnot
      · unfold Spec.Protocol.attestation_admissible at hadm
        simp only [Id.run, pure] at hadm
        split_ifs at hadm with hc <;> first
          | exact absurd hadm Bool.false_ne_true
          | (simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
             exact Nat.le_of_not_lt hc.1.1.2)
    · simp only [ne_eq, hr, not_false_eq_true, Function.update_of_ne] at hx'
      exact absurd ((StoreSteps.mem_sg_pool_iff _ _ _).2 hx') hnot
  · have e : Spec.Protocol.admit_attestation C X a = X :=
      (admit_attestation_eq_self_iff C X a).2 (by simpa using hadm)
    rw [e] at hx
    exact absurd hx hnot

/-- `Protocol.admit_attestations C X rows` keeps the slot, and every attestation it newly holds is
    of a round at most the round of the store's slot. -/
theorem admit_attestations_new_round (C : Spec.Config)
    (rows : List (Spec.Attestation V)) (X : Spec.Store V) :
    (Spec.Protocol.admit_attestations C X rows).s = X.s ∧
      ∀ (r : Round) (x : Spec.Attestation V),
        x ∈ (Spec.Protocol.admit_attestations C X rows).sg_pool r → x ∉ X.sg_pool r →
          x.round ≤ C.round_of X.s := by
  rw [StoreSteps.admit_attestations_foldl]
  induction rows generalizing X with
  | nil => exact ⟨rfl, fun r x hx hnot => absurd hx hnot⟩
  | cons a rs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hs1, h1⟩ := admit_attestation_new_round C X a
    obtain ⟨hs2, h2⟩ := ih (Spec.Protocol.admit_attestation C X a)
    refine ⟨hs2.trans hs1, fun r x hx hnot => ?_⟩
    by_cases hmid : x ∈ (Spec.Protocol.admit_attestation C X a).sg_pool r
    · exact h1 r x hmid hnot
    · have := h2 r x hx hmid
      rw [hs1] at this
      exact this

/-! ## The fields of `HandlersFacts` at `Model.spec` -/

/-- The field `rawRelay_block_new_round_floor` of `HandlersFacts` at `Model.specBase`: an
    attestation `a` newly among the rows of its round after the block handler on `st` and `B` has a
    round at most the round of `st`'s slot. -/
theorem specBase_rawRelay_block_new_round_floor :
    ∀ (S : Setup V) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V) (a : NamedAttestation V),
    a ∉ st.sg_rows a.round →
    a ∈ ((Model.specBase (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).sg_rows a.round →
    a.round ≤ (Model.specBase (V := V)).round_of S.hc st.core.s := by
  intro S (st : Spec.Store V) B a h1 h2
  obtain ⟨a', rfl⟩ := exists_namedAtt a
  have h1' : a' ∉ st.sg_pool a'.round := fun h => h1 ((mem_sg_rows_iff st _ a').2 h)
  have h2' : a' ∈ (Spec.Protocol.on_block (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E) st
      (Spec.Block.toSpecNamed B)).sg_pool a'.round := (mem_sg_rows_iff _ _ a').1 h2
  have hpool : (Handlers.admitBlockCore (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E) st (Spec.Block.toSpecNamed B)).sg_pool a'.round =
      st.sg_pool a'.round := by
    simp only [Spec.Store.sg_pool, StoreSteps.getElem_fn, admitBlockCore_attestations]
  show a'.round ≤ Member.round_of S.hc st.s
  rcases on_block_eq_core (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E) st (Spec.Block.toSpecNamed B) with e | e <;> rw [e] at h2'
  · have := (admit_attestations_new_round (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Block.toSpecNamed B).attestations
      (Handlers.admitBlockCore (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E) st (Spec.Block.toSpecNamed B))).2 _ a' h2'
      (by rw [hpool]; exact h1')
    rw [admitBlockCore_s] at this
    exact this
  · rw [hpool] at h2'
    exact absurd h2' h1'

/-- The field `rawRelay_block_new_round_floor` of `HandlersFacts` at `Model.spec`. -/
theorem spec_rawRelay_block_new_round_floor :
    ∀ (S : Setup V) (st : (Model.spec (V := V)).NS) (B : NamedBlock V) (a : NamedAttestation V),
    a ∉ st.sg_rows a.round →
    a ∈ ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).sg_rows a.round →
    a.round ≤ (Model.spec (V := V)).round_of S.hc st.core.s := by
  intro S st B a h1 h2
  rcases ok_block_cases .alsoCarried S.E S.hc S.cfg st B with ⟨-, e1, -⟩ | ⟨-, e1, -⟩
  · rw [e1] at h2
    exact absurd h2 h1
  · have key := specBase_rawRelay_block_new_round_floor S st.val B a h1
    rw [← e1] at key
    exact key h2

/-- The field `rawRelay_new_row_round_floor` of `HandlersFacts` at `Model.specBase`: an
    attestation `a` newly among the rows of its round after the row admission of `incoming` has a
    round at most the round of `st`'s slot. -/
theorem specBase_rawRelay_new_row_round_floor :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).NS) (incoming a : NamedAttestation V),
    a ∉ st.sg_rows a.round → a ∈ ((Model.specBase (V := V)).admit_row hc st incoming).sg_rows a.round →
    a.round ≤ (Model.specBase (V := V)).round_of hc st.core.s := by
  intro hc st incoming a h1 h2
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).rawRelay_new_row_round_floor hc st.toProofNamed incoming a h1 h2

/-- The field `rawRelay_new_row_round_floor` of `HandlersFacts` at `Model.spec`. -/
theorem spec_rawRelay_new_row_round_floor :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).NS) (incoming a : NamedAttestation V),
    a ∉ st.sg_rows a.round → a ∈ ((Model.spec (V := V)).admit_row hc st incoming).sg_rows a.round →
    a.round ≤ (Model.spec (V := V)).round_of hc st.core.s :=
  fun hc st incoming a => specBase_rawRelay_new_row_round_floor hc st.val incoming a

/-- The field `invariant_clock` of `HandlersFacts` at `Model.spec`: setting a named store's
    clock keeps the confirmation-membership invariant. -/
theorem spec_invariant_clock : ∀ (E : Env V) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS) (t : Time)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.spec (V := V)) E cfg st),
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.spec (V := V)) E cfg ((Model.spec (V := V)).ns_setClock E st t) := by
  intro E cfg st t h
  exact h

/-- The field `initial_core_justifier` of `HandlersFacts` at `Model.spec`: some block of the
    initial store's tree has a chain state whose justification and justification height are the
    store's own. -/
theorem spec_initial_core_justifier :
    ∃ D ∈ ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.T,
    (((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.σ D).J = ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.J ∧
    (((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.σ D).h_j = ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.h_j := by
  refine ⟨DecoupledConsensusModel.Block.genesis, ?_, rfl, rfl⟩
  show DecoupledConsensusModel.Block.genesis ∈
    (Spec.Store.init : Spec.Store V).T.image Spec.Block.toProof
  exact Finset.mem_image.2 ⟨Spec.Block.genesis, Finset.mem_singleton_self _, rfl⟩

/-- The field `full_new_core_guard` of `HandlersFacts` at `Model.specBase`: if `admit_row`
    newly adds the named attestation `a` to the rows of its round, then the erasure of `a` was not
    in the core store's attestation set of that round, and is in it after `on_sg_vote`. -/
theorem specBase_full_new_core_guard :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).NS) (a : NamedAttestation V)
    (hpre : a ∉ st.sg_rows a.round) (hpost : a ∈ ((Model.specBase (V := V)).admit_row hc st a).sg_rows a.round),
    a.erase ∉ (Model.specBase (V := V)).store_sg_pool st.core a.round ∧
      a.erase ∈ (Model.specBase (V := V)).store_sg_pool ((Model.specBase (V := V)).on_sg_vote hc st.core a.erase) a.round := by
  intro hc st a hpre hpost
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).full_new_core_guard hc st.toProofNamed a hpre hpost

/-- The field `full_new_core_guard` of `HandlersFacts` at `Model.spec`. -/
theorem spec_full_new_core_guard :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).NS) (a : NamedAttestation V)
    (hpre : a ∉ st.sg_rows a.round) (hpost : a ∈ ((Model.spec (V := V)).admit_row hc st a).sg_rows a.round),
    a.erase ∉ (Model.spec (V := V)).store_sg_pool st.core a.round ∧
      a.erase ∈ (Model.spec (V := V)).store_sg_pool ((Model.spec (V := V)).on_sg_vote hc st.core a.erase) a.round :=
  fun hc st a hpre hpost => specBase_full_new_core_guard hc st.val a hpre hpost

/-- The field `coreEq_on_goldfish_vote_checked` of `HandlersFacts` at `Model.spec`:
    `on_goldfish_vote_checked` keeps `σ`, `F`, `J` and `h_j`. -/
theorem spec_coreEq_on_goldfish_vote_checked : ∀ (E : Env V) (st : (Model.spec (V := V)).S) (u : GoldfishVote V),
    ((Model.spec (V := V)).on_goldfish_vote_checked E st u).σ = st.σ ∧ ((Model.spec (V := V)).on_goldfish_vote_checked E st u).F = st.F ∧
      ((Model.spec (V := V)).on_goldfish_vote_checked E st u).J = st.J ∧ ((Model.spec (V := V)).on_goldfish_vote_checked E st u).h_j = st.h_j := by
  intro E st u
  simp only [Model.spec, Member.on_goldfish_vote_checked]
  unfold Spec.Protocol.on_goldfish_vote_checked Spec.Protocol.on_goldfish_vote
  simp only [Id.run, pure]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The field `NamedAdmission_admitted_original_row` of `HandlersFacts` at `Model.specBase`: if
    `on_sg_vote` newly adds the erasure of `row` to the core store's attestation set of its round,
    then `row` is among the named rows of its round after `admit_row hc st row`. -/
theorem specBase_NamedAdmission_admitted_original_row :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).NS) (row : NamedAttestation V)
    (hpre : row.erase ∉ (Model.specBase (V := V)).store_sg_pool st.core row.round)
    (hpost : row.erase ∈ (Model.specBase (V := V)).store_sg_pool ((Model.specBase (V := V)).on_sg_vote hc st.core row.erase) row.round),
    row ∈ ((Model.specBase (V := V)).admit_row hc st row).sg_rows row.round := by
  intro hc st row hpre hpost
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).NamedAdmission_admitted_original_row hc st.toProofNamed row hpre hpost

/-- The field `NamedAdmission_admitted_original_row` of `HandlersFacts` at `Model.spec`. -/
theorem spec_NamedAdmission_admitted_original_row :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).NS) (row : NamedAttestation V)
    (hpre : row.erase ∉ (Model.spec (V := V)).store_sg_pool st.core row.round)
    (hpost : row.erase ∈ (Model.spec (V := V)).store_sg_pool ((Model.spec (V := V)).on_sg_vote hc st.core row.erase) row.round),
    row ∈ ((Model.spec (V := V)).admit_row hc st row).sg_rows row.round :=
  fun hc st row hpre hpost => specBase_NamedAdmission_admitted_original_row hc st.val row hpre hpost

/-- The field `mem_gf_votes_on_goldfish_vote_checked` of `HandlersFacts` at `Model.specBase`: a
    Goldfish vote of slot `k` after `on_goldfish_vote_checked E st u` was already one of `st`, or is
    `u`. -/
theorem specBase_mem_gf_votes_on_goldfish_vote_checked :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).S) (u : GoldfishVote V) (k : Slot)
    {y : GoldfishVote V} (h : y ∈ ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).gf_votes k),
    y ∈ st.gf_votes k ∨ y = u := by
  intro E st u k y h
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).mem_gf_votes_on_goldfish_vote_checked E st.toProof u k (y := y) h

/-- The field `mem_gf_votes_on_goldfish_vote_checked` of `HandlersFacts` at `Model.spec`. -/
theorem spec_mem_gf_votes_on_goldfish_vote_checked :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (u : GoldfishVote V) (k : Slot)
    {y : GoldfishVote V} (h : y ∈ ((Model.spec (V := V)).on_goldfish_vote_checked E st u).gf_votes k),
    y ∈ st.gf_votes k ∨ y = u :=
  fun E st u k {y} h => specBase_mem_gf_votes_on_goldfish_vote_checked E st.val u k (y := y) h

/-- The field `on_sg_vote_existing_row_stamp` of `HandlersFacts` at `Model.specBase`:
    `on_sg_vote` keeps the stamp of the SG vote of every attestation the store already holds. -/
theorem specBase_on_sg_vote_existing_row_stamp :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).S) (incoming b : CombinedAttestation V)
    (hb : b ∈ (Model.specBase (V := V)).store_sg_pool st b.round),
    ((Model.specBase (V := V)).on_sg_vote hc st incoming).timestamp_sg_vote ((Model.specBase (V := V)).sgVote b) = st.timestamp_sg_vote ((Model.specBase (V := V)).sgVote b) := by
  intro hc st incoming b hb
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_sg_vote_existing_row_stamp hc st.toProof incoming b hb

/-- The field `on_sg_vote_existing_row_stamp` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_existing_row_stamp :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (incoming b : CombinedAttestation V)
    (hb : b ∈ (Model.spec (V := V)).store_sg_pool st b.round),
    ((Model.spec (V := V)).on_sg_vote hc st incoming).timestamp_sg_vote ((Model.spec (V := V)).sgVote b) = st.timestamp_sg_vote ((Model.spec (V := V)).sgVote b) :=
  fun hc st incoming b hb => specBase_on_sg_vote_existing_row_stamp hc st.val incoming b hb

/-- The field `setClock_core_sg_votes` of `HandlersFacts` at `Model.spec`: setting a named
    store's clock keeps the SG vote lists of its core store. -/
theorem spec_setClock_core_sg_votes :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.sg_votes = st.core.sg_votes := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `poolStep_on_goldfish_vote_checked` of `HandlersFacts` at `Model.specBase`:
    `on_goldfish_vote_checked` keeps every Goldfish vote and stamp of `st`, and keeps four
    conditions on the votes and their stamps: each vote is in its own slot's list, every listed vote
    is stamped, every stamped vote is listed, and no stamp is later than `st.t`. -/
theorem specBase_poolStep_on_goldfish_vote_checked :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).S) (u : GoldfishVote V),
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → (st.timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (st.timestamp_vote x).isSome = true → x ∈ st.gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c → c ≤ (st.t : Stamp))) →
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x ∈ ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).gf_votes k) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c →
        ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).timestamp_vote x = some c)) ∧
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).gf_votes k →
        (((Model.specBase (V := V)).on_goldfish_vote_checked E st u).timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (((Model.specBase (V := V)).on_goldfish_vote_checked E st u).timestamp_vote x).isSome = true →
        x ∈ ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).timestamp_vote x = some c →
        c ≤ (((Model.specBase (V := V)).on_goldfish_vote_checked E st u).t : Stamp))) := by
  intro E st u h1
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).poolStep_on_goldfish_vote_checked E st.toProof u h1

/-- The field `poolStep_on_goldfish_vote_checked` of `HandlersFacts` at `Model.spec`. -/
theorem spec_poolStep_on_goldfish_vote_checked :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (u : GoldfishVote V),
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → (st.timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (st.timestamp_vote x).isSome = true → x ∈ st.gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c → c ≤ (st.t : Stamp))) →
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x ∈ ((Model.spec (V := V)).on_goldfish_vote_checked E st u).gf_votes k) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c →
        ((Model.spec (V := V)).on_goldfish_vote_checked E st u).timestamp_vote x = some c)) ∧
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ ((Model.spec (V := V)).on_goldfish_vote_checked E st u).gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ ((Model.spec (V := V)).on_goldfish_vote_checked E st u).gf_votes k →
        (((Model.spec (V := V)).on_goldfish_vote_checked E st u).timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (((Model.spec (V := V)).on_goldfish_vote_checked E st u).timestamp_vote x).isSome = true →
        x ∈ ((Model.spec (V := V)).on_goldfish_vote_checked E st u).gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), ((Model.spec (V := V)).on_goldfish_vote_checked E st u).timestamp_vote x = some c →
        c ≤ (((Model.spec (V := V)).on_goldfish_vote_checked E st u).t : Stamp))) :=
  fun E st u => specBase_poolStep_on_goldfish_vote_checked E st.val u

/-- The field `mem_and_stamp_of_process` of `HandlersFacts` at `Model.specBase`: under four
    conditions on `st`'s Goldfish votes and stamps, a vote `u` of slot `st.s - 1` or `st.s` whose
    validator has not voted twice in that slot is, after `on_goldfish_vote st u`, in the list of its
    slot with a stamp no later than `st.t`. -/
theorem specBase_mem_and_stamp_of_process :
    ∀ (st : (Model.specBase (V := V)).S) (u : GoldfishVote V),
    (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) →
    (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → (st.timestamp_vote x).isSome = true) →
    (∀ x : GoldfishVote V, (st.timestamp_vote x).isSome = true → x ∈ st.gf_votes x.slot) →
    (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c → c ≤ (st.t : Stamp)) →
    ¬ u.slot < st.s - 1 → ¬ st.s < u.slot → (Model.specBase (V := V)).equivocates (st.pool u.slot) u.val_index = false →
    u ∈ ((Model.specBase (V := V)).on_goldfish_vote st u).gf_votes u.slot ∧
      ∃ c : Stamp, ((Model.specBase (V := V)).on_goldfish_vote st u).timestamp_vote u = some c ∧ c ≤ (st.t : Stamp) := by
  intro st u h1 h2 h3 h4 h5 h6 h7
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).mem_and_stamp_of_process st.toProof u h1 h2 h3 h4 h5 h6 h7

/-- The field `mem_and_stamp_of_process` of `HandlersFacts` at `Model.spec`. -/
theorem spec_mem_and_stamp_of_process :
    ∀ (st : (Model.spec (V := V)).S) (u : GoldfishVote V),
    (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) →
    (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → (st.timestamp_vote x).isSome = true) →
    (∀ x : GoldfishVote V, (st.timestamp_vote x).isSome = true → x ∈ st.gf_votes x.slot) →
    (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c → c ≤ (st.t : Stamp)) →
    ¬ u.slot < st.s - 1 → ¬ st.s < u.slot → (Model.spec (V := V)).equivocates (st.pool u.slot) u.val_index = false →
    u ∈ ((Model.spec (V := V)).on_goldfish_vote st u).gf_votes u.slot ∧
      ∃ c : Stamp, ((Model.spec (V := V)).on_goldfish_vote st u).timestamp_vote u = some c ∧ c ≤ (st.t : Stamp) :=
  fun st u => specBase_mem_and_stamp_of_process st.val u

/-- The field `sg_pool_subset_on_sg_vote` of `HandlersFacts` at `Model.specBase`: `on_sg_vote`
    keeps every attestation of `store_sg_pool st r`. -/
theorem specBase_sg_pool_subset_on_sg_vote :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V) (r : Round),
    (Model.specBase (V := V)).store_sg_pool st r ⊆ (Model.specBase (V := V)).store_sg_pool ((Model.specBase (V := V)).on_sg_vote hc st a) r := by
  intro hc st a r
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).sg_pool_subset_on_sg_vote hc st.toProof a r

/-- The field `sg_pool_subset_on_sg_vote` of `HandlersFacts` at `Model.spec`. -/
theorem spec_sg_pool_subset_on_sg_vote :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V) (r : Round),
    (Model.spec (V := V)).store_sg_pool st r ⊆ (Model.spec (V := V)).store_sg_pool ((Model.spec (V := V)).on_sg_vote hc st a) r :=
  fun hc st a r => specBase_sg_pool_subset_on_sg_vote hc st.val a r

/-- The field `initial_core` of `HandlersFacts` at `Model.spec`: the store part of the initial
    named store is the initial store. -/
theorem spec_initial_core :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core = (Model.spec (V := V)).store_init := by
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `initial_core_σ` of `HandlersFacts` at `Model.spec`: the initial store's
    chain-state map sends every block to the initial chain state. -/
theorem spec_initial_core_σ :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.σ = fun _ => (Model.spec (V := V)).cs_initial := by
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `on_block_checked_using_eq_handle` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_block_checked_using_eq_handle : ∀ (handle : (Model.spec (V := V)).S → (Model.spec (V := V)).S) (hc : Protocol.HealConfig)
    (st : (Model.spec (V := V)).S) {B : Block V}, (Model.spec (V := V)).carried_attestations_admissible hc B = true →
    (Model.spec (V := V)).on_block_checked_using handle hc st B = handle st :=
  fun handle _ st {_} h => if_pos h

/-- The field `on_block_with_of_new` of `HandlersFacts` at `Model.specBase`: when `B` is newly
    among the named blocks after `ns_process_block_core`, the block handler returns the admission of
    the attestations `B` includes at that store. -/
theorem specBase_on_block_with_of_new : ∀ (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V),
    B ∉ st.bodies → B ∈ ((Model.specBase (V := V)).ns_process_block_core E hc cfg st B).bodies →
    (Model.specBase (V := V)).on_block_with admission E hc cfg st B =
      (Model.specBase (V := V)).admit_rows hc ((Model.specBase (V := V)).ns_process_block_core E hc cfg st B) B.attestations := by
  intro adm E hc cfg (st : Spec.Store V) B h1 h2
  have hadm : Spec.Protocol.block_admissible (Spec.Config.toSpec E hc cfg)
      (Spec.Provisional.toSpec E) st (Spec.Block.toSpecNamed B) = true := by
    by_contra hn
    apply h1
    have h2' : Spec.Block.toSpecNamed B ∈ (Handlers.admitBlockCore
        (Spec.Config.toSpec E hc cfg) (Spec.Provisional.toSpec E) st
        (Spec.Block.toSpecNamed B)).T := (mem_bodies_iff _ B).1 h2
    unfold Handlers.admitBlockCore at h2'
    rw [if_neg hn] at h2'
    exact (mem_bodies_iff st B).2 h2'
  show Spec.Protocol.on_block (Spec.Config.toSpec E hc cfg)
      (Spec.Provisional.toSpec E) st (Spec.Block.toSpecNamed B) =
    Spec.Protocol.admit_attestations
      (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig)
      (Handlers.admitBlockCore (Spec.Config.toSpec E hc cfg)
        (Spec.Provisional.toSpec E) st (Spec.Block.toSpecNamed B))
      (B.attestations.map Spec.Attestation.toSpecNamed)
  rw [Handlers.on_block_eq, if_pos hadm, toSpecNamed_attestations]
  exact admit_attestations_config E _ hc cfg _ _ _

/-- The field `on_block_with_of_new` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_block_with_of_new : ∀ (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V),
    B ∉ st.bodies → B ∈ ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).bodies →
    (Model.spec (V := V)).on_block_with admission E hc cfg st B =
      (Model.spec (V := V)).admit_rows hc ((Model.spec (V := V)).ns_process_block_core E hc cfg st B) B.attestations := by
  intro admission E hc cfg st B hnew hcore
  rcases ok_block_cases admission E hc cfg st B with ⟨-, -, e2⟩ | ⟨-, e1, e2⟩
  · rw [e2] at hcore
    exact absurd hcore hnew
  · apply Subtype.ext
    have key := specBase_on_block_with_of_new admission E hc cfg st.val B hnew
    rw [← e1, ← e2] at key
    exact key hcore

/-- The field `on_block_with_of_not_new` of `HandlersFacts` at `Model.specBase`: unless `B` is
    newly among the named blocks after `ns_process_block_core`, the block handler returns the store
    `ns_process_block_core` returns. -/
theorem specBase_on_block_with_of_not_new : ∀ (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V),
    ¬ (B ∉ st.bodies ∧ B ∈ ((Model.specBase (V := V)).ns_process_block_core E hc cfg st B).bodies) →
    (Model.specBase (V := V)).on_block_with admission E hc cfg st B = (Model.specBase (V := V)).ns_process_block_core E hc cfg st B := by
  intro adm E hc cfg (st : Spec.Store V) B h
  show Spec.Protocol.on_block (Spec.Config.toSpec E hc cfg)
      (Spec.Provisional.toSpec E) st (Spec.Block.toSpecNamed B) =
    Handlers.admitBlockCore (Spec.Config.toSpec E hc cfg)
      (Spec.Provisional.toSpec E) st (Spec.Block.toSpecNamed B)
  rw [Handlers.on_block_eq]
  split_ifs with hadm
  · exfalso
    apply h
    refine ⟨fun hB => StoreSteps.not_mem_of_block_admissible _ _ _ _ hadm ((mem_bodies_iff st B).1 hB), ?_⟩
    refine (mem_bodies_iff _ B).2 ?_
    show Spec.Block.toSpecNamed B ∈ (Handlers.admitBlockCore
      (Spec.Config.toSpec E hc cfg) (Spec.Provisional.toSpec E) st
      (Spec.Block.toSpecNamed B)).T
    unfold Handlers.admitBlockCore
    rw [if_pos hadm, (blockCore_fields _ _ _ _).2.2.2.1]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · unfold Handlers.admitBlockCore
    rw [if_neg hadm]

/-- The field `on_block_with_of_not_new` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_block_with_of_not_new : ∀ (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V),
    ¬ (B ∉ st.bodies ∧ B ∈ ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).bodies) →
    (Model.spec (V := V)).on_block_with admission E hc cfg st B = (Model.spec (V := V)).ns_process_block_core E hc cfg st B := by
  intro admission E hc cfg st B hn
  rcases ok_block_cases admission E hc cfg st B with ⟨-, e1, e2⟩ | ⟨-, e1, e2⟩
  · rw [e1, e2]
  · apply Subtype.ext
    have key := specBase_on_block_with_of_not_new admission E hc cfg st.val B
    rw [← e1, ← e2] at key
    exact key hn

/-- The field `on_sg_vote_of_rejected` of `HandlersFacts` at `Model.specBase`: when `a` is too
    old, of a round later than the store's, its confirmed block is already recorded for its sender
    and round, or its sender already has two recorded, `on_sg_vote` returns the store unchanged. -/
theorem specBase_on_sg_vote_of_rejected : ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V),
    a.round < (Model.specBase (V := V)).round_of hc st.s - hc.η_SG ∨ (Model.specBase (V := V)).round_of hc st.s < a.round ∨
      a.confirmed ∈ (Model.specBase (V := V)).round_votes st a ∨ ((Model.specBase (V := V)).round_votes st a).card = 2 →
    (Model.specBase (V := V)).on_sg_vote hc st a = st := by
  intro hc (st : Spec.Store V) a h
  have hconf : a.confirmed = (Function.Embedding.optionMap Spec.BlockId.toProofEmb)
      (Spec.Attestation.toSpec a).confirmed := by
    conv_lhs => rw [← Spec.Attestation.toProof_toSpec a]
    rfl
  simp only [Model.specBase, Model.S.s, Member.store_s, Member.round_votes, Finset.card_map, hconf,
    Finset.mem_map', Spec.Store.toProof_s] at h
  show Spec.Protocol.admit_attestation (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig) st (Spec.Attestation.toSpec a) = st
  rw [admit_attestation_eq_self_iff]
  unfold Spec.Protocol.attestation_admissible
  simp only [Id.run, pure]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc]
  exact h

/-- The field `on_sg_vote_of_rejected` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_of_rejected : ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V),
    a.round < (Model.spec (V := V)).round_of hc st.s - hc.η_SG ∨ (Model.spec (V := V)).round_of hc st.s < a.round ∨
      a.confirmed ∈ (Model.spec (V := V)).round_votes st a ∨ ((Model.spec (V := V)).round_votes st a).card = 2 →
    (Model.spec (V := V)).on_sg_vote hc st a = st :=
  fun hc st a h => Subtype.ext (specBase_on_sg_vote_of_rejected hc st.val a h)

/-- The field `on_goldfish_vote_checked_time` of `HandlersFacts` at `Model.specBase`:
    `on_goldfish_vote_checked` keeps the clock. -/
theorem specBase_on_goldfish_vote_checked_time :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).S) (u : GoldfishVote V), ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).t = st.t := by
  intro E st u
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_goldfish_vote_checked_time E st.toProof u

/-- The field `on_goldfish_vote_checked_time` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_goldfish_vote_checked_time :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (u : GoldfishVote V), ((Model.spec (V := V)).on_goldfish_vote_checked E st u).t = st.t :=
  fun E st u => specBase_on_goldfish_vote_checked_time E st.val u

/-- The field `on_sg_vote_time` of `HandlersFacts` at `Model.specBase`: `on_sg_vote` keeps the
    clock. -/
theorem specBase_on_sg_vote_time :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V), ((Model.specBase (V := V)).on_sg_vote hc st a).t = st.t := by
  intro hc st a
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_sg_vote_time hc st.toProof a

/-- The field `on_sg_vote_time` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_time :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V), ((Model.spec (V := V)).on_sg_vote hc st a).t = st.t :=
  fun hc st a => specBase_on_sg_vote_time hc st.val a

/-- The field `update_finality_time` of `HandlersFacts` at `Model.specBase`: `update_finality`
    keeps the clock. -/
theorem specBase_update_finality_time :
    ∀ (st : (Model.specBase (V := V)).S) (σ : (Model.specBase (V := V)).CS), ((Model.specBase (V := V)).update_finality st σ).t = st.t := by
  intro st σ
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ
  simp only [Model.specBase, Member.update_finality, e]
  rfl

/-- The field `update_finality_time` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_time :
    ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS), ((Model.spec (V := V)).update_finality st σ).t = st.t :=
  fun st σ => specBase_update_finality_time st.val σ

/-- The field `on_block_with_bodies_eq` of `HandlersFacts` at `Model.specBase`: the named
    blocks after `on_block_with` are those after `ns_process_block_core`. -/
theorem specBase_on_block_with_bodies_eq :
    ∀ (S : Setup V) (admission : Protocol.CarriedAdmission) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V), ((Model.specBase (V := V)).on_block_with admission S.E S.hc S.cfg st B).bodies =
    ((Model.specBase (V := V)).ns_process_block_core S.E S.hc S.cfg st B).bodies := by
  intro S admission st B
  unfold_draft

/-- The field `on_block_with_bodies_eq` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_block_with_bodies_eq :
    ∀ (S : Setup V) (admission : Protocol.CarriedAdmission) (st : (Model.spec (V := V)).NS) (B : NamedBlock V), ((Model.spec (V := V)).on_block_with admission S.E S.hc S.cfg st B).bodies =
    ((Model.spec (V := V)).ns_process_block_core S.E S.hc S.cfg st B).bodies := by
  intro S admission st B
  rcases ok_block_cases admission S.E S.hc S.cfg st B with ⟨-, e1, e2⟩ | ⟨-, e1, e2⟩
  · rw [e1, e2]
  · have key := specBase_on_block_with_bodies_eq S admission st.val B
    rw [← e1, ← e2] at key
    exact key

/-- The field `update_finality_h_max_eq` of `HandlersFacts` at `Model.specBase`: after
    `update_finality st sigma`, `h_max` is `max st.h_max sigma.h`. -/
theorem specBase_update_finality_h_max_eq :
    ∀ (st : (Model.specBase (V := V)).S) (sigma : (Model.specBase (V := V)).CS), ((Model.specBase (V := V)).update_finality st sigma).h_max = max st.h_max sigma.h := by
  intro (st : Spec.Store V) sigma
  show (Handlers.updateFinalityWith st sigma).h_max = max st.h_max sigma.toProof.h
  rw [(updateFinalityWith_cases st sigma).1]
  rfl

/-- The field `update_finality_h_max_eq` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_h_max_eq :
    ∀ (st : (Model.spec (V := V)).S) (sigma : (Model.spec (V := V)).CS), ((Model.spec (V := V)).update_finality st sigma).h_max = max st.h_max sigma.h :=
  fun st sigma => specBase_update_finality_h_max_eq st.val sigma

/-- The field `admit_carried_of_new` of `HandlersFacts` at `Model.specBase`: when `B` is not
    among the named blocks of `before` and is among those of `after`, the admission of the
    attestations `B` includes is their admission one by one, from `after`. -/
theorem specBase_admit_carried_of_new : ∀ (admission : Protocol.CarriedAdmission) (hc : Protocol.HealConfig) {before after : (Model.specBase (V := V)).NS} {B : NamedBlock V} (hnew : B ∉ before.bodies) (hheld : B ∈ after.bodies), (Model.specBase (V := V)).admit_carried admission hc before after B =
    (Model.specBase (V := V)).admit_rows hc after B.attestations := by
  intro adm hc (before : Spec.Store V) (after : Spec.Store V) B hnew hheld
  show Handlers.admitCarried
      (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig)
      before after (Spec.Block.toSpecNamed B) =
    Spec.Protocol.admit_attestations
      (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig)
      after (B.attestations.map Spec.Attestation.toSpecNamed)
  unfold Handlers.admitCarried
  rw [if_pos ⟨(mem_bodies_iff before B).not.1 hnew, (mem_bodies_iff after B).1 hheld⟩,
    toSpecNamed_attestations]

/-- The field `admit_carried_of_new` of `HandlersFacts` at `Model.spec`. -/
theorem spec_admit_carried_of_new : ∀ (admission : Protocol.CarriedAdmission) (hc : Protocol.HealConfig) {before after : (Model.spec (V := V)).NS} {B : NamedBlock V} (hnew : B ∉ before.bodies) (hheld : B ∈ after.bodies), (Model.spec (V := V)).admit_carried admission hc before after B =
    (Model.spec (V := V)).admit_rows hc after B.attestations :=
  fun admission hc {before} {after} {B} hnew hheld => Subtype.ext
    (specBase_admit_carried_of_new admission hc (before := before.val) (after := after.val)
      (B := B) hnew hheld)

/-- The field `carried_attestations_admissible_eq_true_iff` of `HandlersFacts` at `Model.spec`:
    `carried_attestations_admissible hc B` holds exactly when every attestation included in `B` is
    of a round at most the round of `B`'s slot. -/
theorem spec_carried_attestations_admissible_eq_true_iff :
    ∀ (hc : Protocol.HealConfig) (B : Block V), (Model.spec (V := V)).carried_attestations_admissible hc B = true ↔
    ∀ a ∈ B.attestations, a.round ≤ ((Model.spec (V := V)).round_of hc B.slot) := by
  intro hc B
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).carried_attestations_admissible_eq_true_iff hc B

/-- The field `initial_bodies` of `HandlersFacts` at `Model.spec`: the named blocks of the
    initial named store are the genesis block alone. -/
theorem spec_initial_bodies :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).bodies = {NamedBlock.genesis} := by
  show (Spec.Store.init : Spec.Store V).T.map Spec.Block.toProofNamedEmb =
    {NamedBlock.genesis}
  simp only [Spec.Store.init, Finset.map_singleton, Spec.Block.coe_toProofNamedEmb,
    Spec.Block.toProofNamed_genesis]

/-- The field `initial_core_F` of `HandlersFacts` at `Model.spec`: the initial store's
    finalized block is genesis. -/
theorem spec_initial_core_F :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.F = Block.genesis := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_F

/-- The field `initial_core_J` of `HandlersFacts` at `Model.spec`: the initial store's
    justified block is genesis. -/
theorem spec_initial_core_J :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.J = Block.genesis := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_J

/-- The field `initial_core_T` of `HandlersFacts` at `Model.spec`: the initial store's tree is
    the genesis block alone. -/
theorem spec_initial_core_T :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.T = {Block.genesis} := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_T

/-- The field `initial_core_h_j` of `HandlersFacts` at `Model.spec`: the initial store's
    justified height is `0`. -/
theorem spec_initial_core_h_j :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.h_j = 0 := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_h_j

/-- The field `initial_core_h_j_lt_h_max` of `HandlersFacts` at `Model.spec`: in the initial
    store, `h_j < h_max`. -/
theorem spec_initial_core_h_j_lt_h_max :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.h_j <
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.h_max := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_h_j_lt_h_max

/-- The field `initial_core_h_max` of `HandlersFacts` at `Model.spec`: the initial store's
    `h_max` is `1`. -/
theorem spec_initial_core_h_max :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.h_max = 1 := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_h_max

/-- The field `initial_core_not_mem_pool` of `HandlersFacts` at `Model.spec`: the initial store
    holds no Goldfish vote. -/
theorem spec_initial_core_not_mem_pool :
    ∀ (k : Slot) (u : GoldfishVote V), u ∉ ((Model.spec (V := V)).store_pool ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core k) := by
  intro k u
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_not_mem_pool k u

/-- The field `initial_core_not_mem_sg_pool` of `HandlersFacts` at `Model.spec`: the initial
    store holds no attestation. -/
theorem spec_initial_core_not_mem_sg_pool :
    ∀ (r : Round) (a : CombinedAttestation V), a ∉ ((Model.spec (V := V)).store_sg_pool ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core r) := by
  intro r a
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_not_mem_sg_pool r a

/-- The field `initial_core_s` of `HandlersFacts` at `Model.spec`: the initial store's slot is
    `0`. -/
theorem spec_initial_core_s :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.s = 0 := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_s

/-- The field `initial_core_t` of `HandlersFacts` at `Model.spec`: the initial store's clock is
    `0`. -/
theorem spec_initial_core_t :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.t = 0 := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_core_t

/-- The field `initial_core_σ_h_le_h_max` of `HandlersFacts` at `Model.spec`: in the initial
    store, every block's chain-state height is at most `h_max`. -/
theorem spec_initial_core_σ_h_le_h_max :
    ∀ (B : Block V), (((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.σ B).h ≤
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.h_max := by
  intro B
  show (Spec.Protocol.ChainState.initial : Spec.Protocol.ChainState V).toProof.h ≤ 1
  rw [← toProof_cs_initial]
  simp [DecoupledConsensusModel.Protocol.ChainState.initial]

/-- The field `initial_sg_rows` of `HandlersFacts` at `Model.spec`: the initial named store has
    no named attestation in any round. -/
theorem spec_initial_sg_rows :
    ∀ (r : Round), ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).sg_rows r = [] := by
  intro r
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).initial_sg_rows r

/-- The field `on_block_checked_using_of_admissible` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_block_checked_using_of_admissible : ∀ (handle : (Model.spec (V := V)).S → (Model.spec (V := V)).S) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) {B : Block V} (h : (Model.spec (V := V)).carried_attestations_admissible hc B = true), (Model.spec (V := V)).on_block_checked_using handle hc st B = handle st :=
  fun handle _ st {_} h => if_pos h

/-- The field `on_block_checked_using_of_not_admissible` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_block_checked_using_of_not_admissible : ∀ (handle : (Model.spec (V := V)).S → (Model.spec (V := V)).S) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) {B : Block V} (h : ¬ (Model.spec (V := V)).carried_attestations_admissible hc B = true), (Model.spec (V := V)).on_block_checked_using handle hc st B = st :=
  fun handle _ st {_} h => if_neg h

/-- The field `on_block_with_core_F` of `HandlersFacts` at `Model.specBase`: the finalized
    block after `on_block_with` is the one after `ns_process_block_core` on the same arguments. -/
theorem specBase_on_block_with_core_F :
    ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V), ((Model.specBase (V := V)).on_block_with admission E hc cfg st B).core.F =
    ((Model.specBase (V := V)).ns_process_block_core E hc cfg st B).core.F := by
  intro admission E hc cfg st B
  unfold_draft

/-- The field `on_block_with_core_F` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_block_with_core_F :
    ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V), ((Model.spec (V := V)).on_block_with admission E hc cfg st B).core.F =
    ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).core.F := by
  intro admission E hc cfg st B
  rcases ok_block_cases admission E hc cfg st B with ⟨-, e1, e2⟩ | ⟨-, e1, e2⟩
  · rw [e1, e2]
  · have key := specBase_on_block_with_core_F admission E hc cfg st.val B
    rw [← e1, ← e2] at key
    exact key

/-- The field `on_goldfish_vote_checked_of_mem_committee` of `HandlersFacts` at `Model.spec`:
    when `u`'s validator is in the committee of `u`'s slot,
    `on_goldfish_vote_checked E st u = on_goldfish_vote st u`. -/
theorem spec_on_goldfish_vote_checked_of_mem_committee : ∀ (E : Env V) (st : (Model.spec (V := V)).S) (u : GoldfishVote V) (h : u.val_index ∈ E.committee u.slot), (Model.spec (V := V)).on_goldfish_vote_checked E st u = (Model.spec (V := V)).on_goldfish_vote st u := by
  intro E st u h
  obtain ⟨u', rfl⟩ := exists_vote u
  simp only [Spec.GoldfishVote.toProof_val_index, Spec.GoldfishVote.toProof_slot] at h
  simp only [Model.spec, Member.on_goldfish_vote_checked, Member.on_goldfish_vote,
    Spec.GoldfishVote.toSpec_toProof]
  unfold Spec.Protocol.on_goldfish_vote_checked
  simp only [Id.run, pure]
  split_ifs with hh <;> first | rfl | exact absurd h (by simpa using hh)

/-- The field `process_block_core_of_parent_not_mem` of `HandlersFacts` at `Model.specBase`:
    when `B`'s parent is not among the named blocks of `st`, `ns_process_block_core` returns `st`. -/
theorem specBase_process_block_core_of_parent_not_mem : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) {st : (Model.specBase (V := V)).NS} {B : NamedBlock V} (h : B.parent ∉ st.bodies), (Model.specBase (V := V)).ns_process_block_core E hc cfg st B = st := by
  intro E hc cfg st B h
  show Handlers.admitBlockCore (Spec.Config.toSpec E hc cfg)
    (Spec.Provisional.toSpec E) st (Spec.Block.toSpecNamed B) = st
  unfold Handlers.admitBlockCore
  rw [if_neg]
  intro hadm
  apply h
  refine (mem_bodies_iff st B.parent).2 ?_
  rw [← toSpecNamed_parent]
  by_contra hp
  unfold Spec.Protocol.block_admissible at hadm
  simp [Id.run, hp] at hadm

/-- The field `process_block_core_of_parent_not_mem` of `HandlersFacts` at `Model.spec`. -/
theorem spec_process_block_core_of_parent_not_mem : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) {st : (Model.spec (V := V)).NS} {B : NamedBlock V} (h : B.parent ∉ st.bodies), (Model.spec (V := V)).ns_process_block_core E hc cfg st B = st := by
  intro E hc cfg st B h
  rcases ok_block_cases .alsoCarried E hc cfg st B with ⟨-, -, e2⟩ | ⟨-, -, e2⟩
  · exact e2
  · apply Subtype.ext
    rw [e2]
    exact specBase_process_block_core_of_parent_not_mem E hc cfg (st := st.val) (B := B) h

/-- The field `ModelProperties_setClock_bodies` of `HandlersFacts` at `Model.spec`: setting a
    named store's clock keeps its named blocks. -/
theorem spec_ModelProperties_setClock_bodies :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Time), ((Model.spec (V := V)).ns_setClock E st t).bodies = st.bodies := by
  intro E st t
  rfl

/-- The field `ModelProperties_setClock_core_T` of `HandlersFacts` at `Model.specBase`: setting
    a named store's clock keeps its tree. -/
theorem specBase_ModelProperties_setClock_core_T :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Time), ((Model.specBase (V := V)).ns_setClock E st t).core.T = st.core.T := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).ModelProperties_setClock_core_T E st.toProofNamed t

/-- The field `ModelProperties_setClock_core_T` of `HandlersFacts` at `Model.spec`. -/
theorem spec_ModelProperties_setClock_core_T :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Time), ((Model.spec (V := V)).ns_setClock E st t).core.T = st.core.T :=
  fun E st t => specBase_ModelProperties_setClock_core_T E st.val t

/-- The field `ModelProperties_setClock_core_pool` of `HandlersFacts` at `Model.spec`: setting
    a named store's clock keeps its Goldfish votes of every slot. -/
theorem spec_ModelProperties_setClock_core_pool :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Time), ((Model.spec (V := V)).store_pool ((Model.spec (V := V)).ns_setClock E st t).core) = ((Model.spec (V := V)).store_pool st.core) := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `ModelProperties_setClock_core_s` of `HandlersFacts` at `Model.specBase`: after
    setting the clock to `t`, the slot is `E.slotOf t`. -/
theorem specBase_ModelProperties_setClock_core_s :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Time), ((Model.specBase (V := V)).ns_setClock E st t).core.s = E.slotOf t := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).ModelProperties_setClock_core_s E st.toProofNamed t

/-- The field `ModelProperties_setClock_core_s` of `HandlersFacts` at `Model.spec`. -/
theorem spec_ModelProperties_setClock_core_s :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Time), ((Model.spec (V := V)).ns_setClock E st t).core.s = E.slotOf t :=
  fun E st t => specBase_ModelProperties_setClock_core_s E st.val t

/-- The field `ModelProperties_setClock_core_t` of `HandlersFacts` at `Model.specBase`: after
    setting the clock to `t`, the clock is `t`. -/
theorem specBase_ModelProperties_setClock_core_t :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Time), ((Model.specBase (V := V)).ns_setClock E st t).core.t = t := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).ModelProperties_setClock_core_t E st.toProofNamed t

/-- The field `ModelProperties_setClock_core_t` of `HandlersFacts` at `Model.spec`. -/
theorem spec_ModelProperties_setClock_core_t :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Time), ((Model.spec (V := V)).ns_setClock E st t).core.t = t :=
  fun E st t => specBase_ModelProperties_setClock_core_t E st.val t

/-- The field `ModelProperties_setClock_core_σ` of `HandlersFacts` at `Model.spec`: setting a
    named store's clock keeps its chain-state map. -/
theorem spec_ModelProperties_setClock_core_σ :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Time), ((Model.spec (V := V)).ns_setClock E st t).core.σ = st.core.σ := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `NamedAdmission_admit_row_bodies` of `HandlersFacts` at `Model.specBase`:
    `admit_row` keeps the named blocks. -/
theorem specBase_NamedAdmission_admit_row_bodies :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).NS) (row : NamedAttestation V), ((Model.specBase (V := V)).admit_row hc st row).bodies = st.bodies := by
  intro hc st row
  obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes
    (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig) st
    (Spec.Attestation.toSpecNamed row)
  simp only [Model.specBase, Member.admit_row, e]
  rfl

/-- The field `NamedAdmission_admit_row_bodies` of `HandlersFacts` at `Model.spec`. -/
theorem spec_NamedAdmission_admit_row_bodies :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).NS) (row : NamedAttestation V), ((Model.spec (V := V)).admit_row hc st row).bodies = st.bodies :=
  fun hc st row => specBase_NamedAdmission_admit_row_bodies hc st.val row

/-- The field `admit_row_of_core_noop` of `HandlersFacts` at `Model.specBase`: if `on_sg_vote`
    leaves the store part of `st` unchanged on the erasure of `row`, then
    `admit_row hc st row = st`. -/
theorem specBase_admit_row_of_core_noop : ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).NS) (row : NamedAttestation V) (h : (Model.specBase (V := V)).on_sg_vote hc st.core row.erase = st.core), (Model.specBase (V := V)).admit_row hc st row = st := by
  intro hc (st : Spec.Store V) row h
  have h' : Spec.Protocol.admit_attestation (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig) st
      (Spec.Attestation.toSpec row.erase) = st := h
  show Spec.Protocol.admit_attestation (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig) st (Spec.Attestation.toSpecNamed row) = st
  rw [admit_attestation_eq_self_iff] at h' ⊢
  rw [← h']
  apply attestation_admissible_congr
  all_goals (cases row; simp [Spec.Attestation.toSpecNamed, Spec.Attestation.toSpec,
    DecoupledConsensusModel.NamedAttestation.erase])

/-- The field `admit_row_of_core_noop` of `HandlersFacts` at `Model.spec`. -/
theorem spec_admit_row_of_core_noop : ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).NS) (row : NamedAttestation V) (h : (Model.spec (V := V)).on_sg_vote hc st.core row.erase = st.core), (Model.spec (V := V)).admit_row hc st row = st :=
  fun hc st row h => Subtype.ext
    (specBase_admit_row_of_core_noop hc st.val row (congrArg Subtype.val h))

/-- The field `carried_row_prefix` of `HandlersFacts` at `Model.spec`: if the attestations `B`
    includes are `earlierRows ++ row :: suffix`, and `B` is newly among the named blocks of `after`,
    then `admit_carried .alsoCarried hc before after B` is `after` with `earlierRows`, then `row`,
    then `suffix` admitted. -/
theorem spec_carried_row_prefix : ∀ (hc : Protocol.HealConfig) (before after : (Model.spec (V := V)).NS) (B : NamedBlock V) (earlierRows suffix : List (NamedAttestation V)) (row : NamedAttestation V) (hrows : B.attestations = earlierRows ++ row :: suffix) (hnew : B ∉ before.bodies) (hheld : B ∈ after.bodies), (Model.spec (V := V)).admit_carried .alsoCarried hc before after B =
    (Model.spec (V := V)).admit_rows hc ((Model.spec (V := V)).admit_row hc ((Model.spec (V := V)).admit_rows hc after earlierRows) row) suffix := by
  intro hc before after B earlierRows suffix row hrows hnew hheld
  rw [spec_admit_carried_of_new _ hc hnew hheld, hrows]
  simp only [Model.spec, Member.admit_rows, Member.admit_row, List.map_append, List.map_cons,
    StoreSteps.admit_attestations_foldl, List.foldl_append, List.foldl_cons]

/-- The field `on_block_clock` of `HandlersFacts` at `Model.specBase`: `on_block_with` keeps
    the clock and the slot. -/
theorem specBase_on_block_clock :
    ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V), ((Model.specBase (V := V)).on_block_with admission E hc cfg st B).core.t = st.core.t ∧
    ((Model.specBase (V := V)).on_block_with admission E hc cfg st B).core.s = st.core.s := by
  intro admission E hc cfg st B
  unfold_draft
  exact ⟨trivial, trivial⟩

/-- The field `on_block_clock` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_block_clock :
    ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V), ((Model.spec (V := V)).on_block_with admission E hc cfg st B).core.t = st.core.t ∧
    ((Model.spec (V := V)).on_block_with admission E hc cfg st B).core.s = st.core.s := by
  intro admission E hc cfg st B
  rcases ok_block_cases admission E hc cfg st B with ⟨-, e1, -⟩ | ⟨-, e1, -⟩
  · rw [e1]
    exact ⟨rfl, rfl⟩
  · have key := specBase_on_block_clock admission E hc cfg st.val B
    rw [← e1] at key
    exact key

/-- The field `process_block_clock` of `HandlersFacts` at `Model.specBase`:
    `ns_process_block_core` keeps the clock and the slot. -/
theorem specBase_process_block_clock :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V), ((Model.specBase (V := V)).ns_process_block_core E hc cfg st B).core.t = st.core.t ∧
    ((Model.specBase (V := V)).ns_process_block_core E hc cfg st B).core.s = st.core.s := by
  intro E hc cfg st B
  unfold_draft
  exact ⟨trivial, trivial⟩

/-- The field `process_block_clock` of `HandlersFacts` at `Model.spec`. -/
theorem spec_process_block_clock :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V), ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).core.t = st.core.t ∧
    ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).core.s = st.core.s := by
  intro E hc cfg st B
  rcases ok_block_cases .alsoCarried E hc cfg st B with ⟨-, -, e2⟩ | ⟨-, -, e2⟩
  · rw [e2]
    exact ⟨rfl, rfl⟩
  · have key := specBase_process_block_clock E hc cfg st.val B
    rw [← e2] at key
    exact key

/-- The field `process_block_core_F` of `HandlersFacts` at `Model.specBase`: the finalized
    block of `st` is an ancestor of, or equal to, the finalized block after `ns_process_block_core`. -/
theorem specBase_process_block_core_F :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V), Block.Preceq st.core.F
    ((Model.specBase (V := V)).ns_process_block_core E hc cfg st B).core.F := by
  intro E hc cfg (st : Spec.Store V) B
  unfold_draft
  unfold Block.Preceq
  exact Spec.Block.toProof_preceq_of_ancestorEq _ _
    (admitBlockCore_fields (Spec.Config.toSpec E hc cfg) (Spec.Provisional.toSpec E)
      st (Spec.Block.toSpecNamed B)).2.2.2

/-- The field `process_block_core_F` of `HandlersFacts` at `Model.spec`. -/
theorem spec_process_block_core_F :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V), Block.Preceq st.core.F
    ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).core.F := by
  intro E hc cfg st B
  rcases ok_block_cases .alsoCarried E hc cfg st B with ⟨-, -, e2⟩ | ⟨-, -, e2⟩
  · rw [e2]
    unfold DecoupledConsensusModel.Block.Preceq
    exact DecoupledConsensusModel.Block.preceq_self _
  · have key := specBase_process_block_core_F E hc cfg st.val B
    rw [← e2] at key
    exact key

/-- The field `admit_row_mem_cases` of `HandlersFacts` at `Model.specBase`: a named attestation
    of its round after `admit_row hc st incoming` was one of `st`, or is `incoming`. -/
theorem specBase_admit_row_mem_cases :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).NS) (incoming a : NamedAttestation V) (h : a ∈ ((Model.specBase (V := V)).admit_row hc st incoming).sg_rows a.round), a ∈ st.sg_rows a.round ∨ a = incoming := by
  intro hc st incoming a h
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).admit_row_mem_cases hc st.toProofNamed incoming a h

/-- The field `admit_row_mem_cases` of `HandlersFacts` at `Model.spec`. -/
theorem spec_admit_row_mem_cases :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).NS) (incoming a : NamedAttestation V) (h : a ∈ ((Model.spec (V := V)).admit_row hc st incoming).sg_rows a.round), a ∈ st.sg_rows a.round ∨ a = incoming :=
  fun hc st incoming a h => specBase_admit_row_mem_cases hc st.val incoming a h

/-- The field `admit_row_mem_mono` of `HandlersFacts` at `Model.specBase`: `admit_row` keeps
    every named attestation `st` holds. -/
theorem specBase_admit_row_mem_mono :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).NS) (incoming a : NamedAttestation V) (h : a ∈ st.sg_rows a.round), a ∈ ((Model.specBase (V := V)).admit_row hc st incoming).sg_rows a.round := by
  intro hc st incoming a h
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).admit_row_mem_mono hc st.toProofNamed incoming a h

/-- The field `admit_row_mem_mono` of `HandlersFacts` at `Model.spec`. -/
theorem spec_admit_row_mem_mono :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).NS) (incoming a : NamedAttestation V) (h : a ∈ st.sg_rows a.round), a ∈ ((Model.spec (V := V)).admit_row hc st incoming).sg_rows a.round :=
  fun hc st incoming a h => specBase_admit_row_mem_mono hc st.val incoming a h

/-- The field `admit_rows_mem_mono` of `HandlersFacts` at `Model.specBase`: `admit_rows` keeps
    every named attestation `st` holds. -/
theorem specBase_admit_rows_mem_mono :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).NS) (rows : List (NamedAttestation V)) (a : NamedAttestation V) (h : a ∈ st.sg_rows a.round), a ∈ ((Model.specBase (V := V)).admit_rows hc st rows).sg_rows a.round := by
  intro hc st rows a h
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).admit_rows_mem_mono hc st.toProofNamed rows a h

/-- The field `admit_rows_mem_mono` of `HandlersFacts` at `Model.spec`. -/
theorem spec_admit_rows_mem_mono :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).NS) (rows : List (NamedAttestation V)) (a : NamedAttestation V) (h : a ∈ st.sg_rows a.round), a ∈ ((Model.spec (V := V)).admit_rows hc st rows).sg_rows a.round :=
  fun hc st rows a h => specBase_admit_rows_mem_mono hc st.val rows a h

/-- The field `admit_rows_new_marker` of `HandlersFacts` at `Model.specBase`: if admitting
    `rows` newly adds `a`, then some position `j` of `rows` holds `a`, `a` is not held after the
    first `j` entries are admitted, and is held once `a` is admitted next. -/
theorem specBase_admit_rows_new_marker :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).NS) (rows : List (NamedAttestation V)) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round) (hpost : a ∈ ((Model.specBase (V := V)).admit_rows hc st rows).sg_rows a.round), ∃ j, j < rows.length ∧ rows[j]? = some a ∧
    a ∉ ((Model.specBase (V := V)).admit_rows hc st (rows.take j)).sg_rows a.round ∧
    a ∈ ((Model.specBase (V := V)).admit_row hc
    ((Model.specBase (V := V)).admit_rows hc st (rows.take j)) a).sg_rows a.round := by
  intro hc st rows a hpre hpost
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).admit_rows_new_marker hc st.toProofNamed rows a hpre hpost

/-- The field `admit_rows_new_marker` of `HandlersFacts` at `Model.spec`. -/
theorem spec_admit_rows_new_marker :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).NS) (rows : List (NamedAttestation V)) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round) (hpost : a ∈ ((Model.spec (V := V)).admit_rows hc st rows).sg_rows a.round), ∃ j, j < rows.length ∧ rows[j]? = some a ∧
    a ∉ ((Model.spec (V := V)).admit_rows hc st (rows.take j)).sg_rows a.round ∧
    a ∈ ((Model.spec (V := V)).admit_row hc
    ((Model.spec (V := V)).admit_rows hc st (rows.take j)) a).sg_rows a.round :=
  fun hc st rows a hpre hpost => specBase_admit_rows_new_marker hc st.val rows a hpre hpost

/-- The field `finalized_preceq_get_stable` of `HandlersFacts` at `Model.specBase`: `st.F` is
    an ancestor of, or equal to, `get_stable st`. -/
theorem specBase_finalized_preceq_get_stable :
    ∀ (st : (Model.specBase (V := V)).S), Block.Preceq st.F ((Model.specBase (V := V)).get_stable st) := by
  intro (st : Spec.Store V)
  show Block.Preceq st.F.toProof (Spec.Protocol.get_stable (Spec.Store.ofImage st)).toProof
  unfold Block.Preceq Spec.Protocol.get_stable
  simp only [Id.run, pure]
  split_ifs with h
  · have h' := Spec.Block.toProof_preceq_of_ancestorEq _ _ h
    simpa only [Spec.Store.ofImage_F, Spec.Store.ofImage_latest_stable,
      Spec.Store.toProof_blockOfImage] using h'
  · have h' := Spec.Block.toProof_preceq_of_ancestorEq _ _
      (ancestorEq_refl (Spec.Store.ofImage st).F)
    simpa only [Spec.Store.ofImage_F, Spec.Store.toProof_blockOfImage] using h'

/-- The field `finalized_preceq_get_stable` of `HandlersFacts` at `Model.spec`. -/
theorem spec_finalized_preceq_get_stable :
    ∀ (st : (Model.spec (V := V)).S), Block.Preceq st.F ((Model.spec (V := V)).get_stable st) :=
  fun st => specBase_finalized_preceq_get_stable st.val

/-- The field `on_goldfish_vote_checked_slot` of `HandlersFacts` at `Model.specBase`:
    `on_goldfish_vote_checked` keeps the slot. -/
theorem specBase_on_goldfish_vote_checked_slot :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).S) (u : GoldfishVote V), ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).s = st.s := by
  intro E st u
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_goldfish_vote_checked_slot E st.toProof u

/-- The field `on_goldfish_vote_checked_slot` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_goldfish_vote_checked_slot :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (u : GoldfishVote V), ((Model.spec (V := V)).on_goldfish_vote_checked E st u).s = st.s :=
  fun E st u => specBase_on_goldfish_vote_checked_slot E st.val u

/-- The field `on_sg_vote_slot` of `HandlersFacts` at `Model.specBase`: `on_sg_vote` keeps the
    slot. -/
theorem specBase_on_sg_vote_slot :
    ∀ (hc : HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V), ((Model.specBase (V := V)).on_sg_vote hc st a).s = st.s := by
  intro hc st a
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_sg_vote_slot hc st.toProof a

/-- The field `on_sg_vote_slot` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_slot :
    ∀ (hc : HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V), ((Model.spec (V := V)).on_sg_vote hc st a).s = st.s :=
  fun hc st a => specBase_on_sg_vote_slot hc st.val a

/-- The field `process_block_core_sg_votes` of `HandlersFacts` at `Model.specBase`:
    `ns_process_block_core` keeps the attestations of every round. -/
theorem specBase_process_block_core_sg_votes : ∀ (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V), ((Model.specBase (V := V)).ns_process_block_core E hc cfg st B).core.sg_votes =
    st.core.sg_votes := by
  intro E hc cfg st B
  unfold_draft
  funext r
  simp only [Member.store_sg_votes, Spec.Store.toProof_sg_votes, admitBlockCore_attestations]

/-- The field `process_block_core_sg_votes` of `HandlersFacts` at `Model.spec`. -/
theorem spec_process_block_core_sg_votes : ∀ (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V), ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).core.sg_votes =
    st.core.sg_votes := by
  intro E hc cfg st B
  rcases ok_block_cases .alsoCarried E hc cfg st B with ⟨-, -, e2⟩ | ⟨-, -, e2⟩
  · rw [e2]
  · have key := specBase_process_block_core_sg_votes E hc cfg st.val B
    rw [← e2] at key
    exact key

/-- The field `on_goldfish_vote_checked_F` of `HandlersFacts` at `Model.specBase`:
    `on_goldfish_vote_checked` keeps the finalized block. -/
theorem specBase_on_goldfish_vote_checked_F :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).S) (vote : GoldfishVote V), ((Model.specBase (V := V)).on_goldfish_vote_checked E st vote).F = st.F := by
  intro E st vote
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_goldfish_vote_checked_F E st.toProof vote

/-- The field `on_goldfish_vote_checked_F` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_goldfish_vote_checked_F :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (vote : GoldfishVote V), ((Model.spec (V := V)).on_goldfish_vote_checked E st vote).F = st.F :=
  fun E st vote => specBase_on_goldfish_vote_checked_F E st.val vote

/-- The field `on_goldfish_vote_checked_T` of `HandlersFacts` at `Model.specBase`:
    `on_goldfish_vote_checked` keeps the tree. -/
theorem specBase_on_goldfish_vote_checked_T :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).S) (vote : GoldfishVote V), ((Model.specBase (V := V)).on_goldfish_vote_checked E st vote).T = st.T := by
  intro E st vote
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_goldfish_vote_checked_T E st.toProof vote

/-- The field `on_goldfish_vote_checked_T` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_goldfish_vote_checked_T :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (vote : GoldfishVote V), ((Model.spec (V := V)).on_goldfish_vote_checked E st vote).T = st.T :=
  fun E st vote => specBase_on_goldfish_vote_checked_T E st.val vote

/-- The field `on_goldfish_vote_checked_h_max` of `HandlersFacts` at `Model.specBase`:
    `on_goldfish_vote_checked` keeps `h_max`. -/
theorem specBase_on_goldfish_vote_checked_h_max :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).S) (vote : GoldfishVote V), ((Model.specBase (V := V)).on_goldfish_vote_checked E st vote).h_max = st.h_max := by
  intro E st vote
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_goldfish_vote_checked_h_max E st.toProof vote

/-- The field `on_goldfish_vote_checked_h_max` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_goldfish_vote_checked_h_max :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (vote : GoldfishVote V), ((Model.spec (V := V)).on_goldfish_vote_checked E st vote).h_max = st.h_max :=
  fun E st vote => specBase_on_goldfish_vote_checked_h_max E st.val vote

/-- The field `on_sg_vote_F` of `HandlersFacts` at `Model.specBase`: `on_sg_vote` keeps the
    finalized block. -/
theorem specBase_on_sg_vote_F :
    ∀ (hc : HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V), ((Model.specBase (V := V)).on_sg_vote hc st a).F = st.F := by
  intro hc st a
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_sg_vote_F hc st.toProof a

/-- The field `on_sg_vote_F` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_F :
    ∀ (hc : HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V), ((Model.spec (V := V)).on_sg_vote hc st a).F = st.F :=
  fun hc st a => specBase_on_sg_vote_F hc st.val a

/-- The field `on_sg_vote_T` of `HandlersFacts` at `Model.specBase`: `on_sg_vote` keeps the
    tree. -/
theorem specBase_on_sg_vote_T :
    ∀ (hc : HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V), ((Model.specBase (V := V)).on_sg_vote hc st a).T = st.T := by
  intro hc st a
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_sg_vote_T hc st.toProof a

/-- The field `on_sg_vote_T` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_T :
    ∀ (hc : HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V), ((Model.spec (V := V)).on_sg_vote hc st a).T = st.T :=
  fun hc st a => specBase_on_sg_vote_T hc st.val a

/-- The field `on_sg_vote_h_max` of `HandlersFacts` at `Model.specBase`: `on_sg_vote` keeps
    `h_max`. -/
theorem specBase_on_sg_vote_h_max :
    ∀ (hc : HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V), ((Model.specBase (V := V)).on_sg_vote hc st a).h_max = st.h_max := by
  intro hc st a
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_sg_vote_h_max hc st.toProof a

/-- The field `on_sg_vote_h_max` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_h_max :
    ∀ (hc : HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V), ((Model.spec (V := V)).on_sg_vote hc st a).h_max = st.h_max :=
  fun hc st a => specBase_on_sg_vote_h_max hc st.val a

/-- The field `update_finality_F` of `HandlersFacts` at `Model.specBase`: `st.F` is an ancestor
    of, or equal to, the finalized block after `update_finality st σ`. -/
theorem specBase_update_finality_F :
    ∀ (st : (Model.specBase (V := V)).S) (σ : (Model.specBase (V := V)).CS), Block.preceq st.F ((Model.specBase (V := V)).update_finality st σ).F = true := by
  intro (st : Spec.Store V) σ
  show Block.preceq st.F.toProof (Handlers.updateFinalityWith st σ).F.toProof = true
  exact Spec.Block.toProof_preceq_of_ancestorEq _ _ (updateFinalityWith_F st σ)

/-- The field `update_finality_F` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_F :
    ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS), Block.preceq st.F ((Model.spec (V := V)).update_finality st σ).F = true :=
  fun st σ => specBase_update_finality_F st.val σ

/-- The field `update_finality_T` of `HandlersFacts` at `Model.specBase`: `update_finality`
    keeps the tree. -/
theorem specBase_update_finality_T :
    ∀ (st : (Model.specBase (V := V)).S) (σ : (Model.specBase (V := V)).CS), ((Model.specBase (V := V)).update_finality st σ).T = st.T := by
  intro st σ
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ
  simp only [Model.specBase, Member.update_finality, e]
  rfl

/-- The field `update_finality_T` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_T :
    ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS), ((Model.spec (V := V)).update_finality st σ).T = st.T :=
  fun st σ => specBase_update_finality_T st.val σ

/-- The field `update_finality_h_max_mono` of `HandlersFacts` at `Model.specBase`:
    `update_finality` does not lower `h_max`. -/
theorem specBase_update_finality_h_max_mono :
    ∀ (st : (Model.specBase (V := V)).S) (sigma : (Model.specBase (V := V)).CS), st.h_max ≤ ((Model.specBase (V := V)).update_finality st sigma).h_max := by
  intro (st : Spec.Store V) sigma
  show st.h_max ≤ (Handlers.updateFinalityWith st sigma).h_max
  rw [(updateFinalityWith_cases st sigma).1]
  exact le_max_left _ _

/-- The field `update_finality_h_max_mono` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_h_max_mono :
    ∀ (st : (Model.spec (V := V)).S) (sigma : (Model.spec (V := V)).CS), st.h_max ≤ ((Model.spec (V := V)).update_finality st sigma).h_max :=
  fun st sigma => specBase_update_finality_h_max_mono st.val sigma

/-- The field `update_finality_heightId` of `HandlersFacts` at `Model.specBase`:
    `update_finality` does not lower the pair of the justified height and the justified block's
    root, in the order of `HeightId`. -/
theorem specBase_update_finality_heightId :
    ∀ (st : (Model.specBase (V := V)).S) (σ : (Model.specBase (V := V)).CS), HeightId.mk st.h_j st.J.root ≤
    HeightId.mk ((Model.specBase (V := V)).update_finality st σ).h_j
    ((Model.specBase (V := V)).update_finality st σ).J.root := by
  intro (st : Spec.Store V) (σ : Spec.Protocol.ChainState V)
  show HeightId.mk st.h_j st.J.toProof.root ≤
    HeightId.mk (Handlers.updateFinalityWith st σ).h_j (Handlers.updateFinalityWith st σ).J.toProof.root
  rcases (updateFinalityWith_cases st σ).2.1 with ⟨hJ, hh⟩ | ⟨hJ, hh, -, hlt⟩
  · rw [hJ, hh]
  · rw [hJ, hh]
    show toLex (st.h_j, st.J.toProof.root) ≤ toLex (σ.h_j, σ.J.toProof.root)
    rw [Spec.Block.toProof_root, Spec.Block.toProof_root]
    rcases Prod.Lex.lt_iff.1 hlt with h1 | ⟨h1, h2⟩
    · exact le_of_lt (Prod.Lex.lt_iff.2 (Or.inl h1))
    · exact le_of_lt (Prod.Lex.lt_iff.2 (Or.inr ⟨h1, Spec.BlockId.toProof_lt.2 h2⟩))

/-- The field `update_finality_heightId` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_heightId :
    ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS), HeightId.mk st.h_j st.J.root ≤
    HeightId.mk ((Model.spec (V := V)).update_finality st σ).h_j
    ((Model.spec (V := V)).update_finality st σ).J.root :=
  fun st σ => specBase_update_finality_heightId st.val σ

/-- The field `update_finality_preceq` of `HandlersFacts` at `Model.specBase`: if `st.F` is an
    ancestor of, or equal to, `st.J`, the same holds after `update_finality st σ`. -/
theorem specBase_update_finality_preceq :
    ∀ (st : (Model.specBase (V := V)).S) (σ : (Model.specBase (V := V)).CS) (h : Block.preceq st.F st.J = true), Block.preceq ((Model.specBase (V := V)).update_finality st σ).F
    ((Model.specBase (V := V)).update_finality st σ).J = true := by
  intro (st : Spec.Store V) σ h
  show Block.preceq (Handlers.updateFinalityWith st σ).F.toProof
    (Handlers.updateFinalityWith st σ).J.toProof = true
  rcases (updateFinalityWith_cases st σ).2.2 with hF | ⟨hF, -, hσJ⟩
  · rw [hF]
    rcases (updateFinalityWith_cases st σ).2.1 with ⟨hJ, -⟩ | ⟨hJ, -, hFJ, -⟩
    · rw [hJ]; exact h
    · rw [hJ]; exact Spec.Block.toProof_preceq_of_ancestorEq _ _ hFJ
  · rw [hF]
    exact Spec.Block.toProof_preceq_of_ancestorEq _ _ hσJ

/-- The field `update_finality_preceq` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_preceq :
    ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS) (h : Block.preceq st.F st.J = true), Block.preceq ((Model.spec (V := V)).update_finality st σ).F
    ((Model.spec (V := V)).update_finality st σ).J = true :=
  fun st σ h => specBase_update_finality_preceq st.val σ h

/-- The field `update_finality_σ` of `HandlersFacts` at `Model.specBase`: `update_finality`
    keeps the chain-state map. -/
theorem specBase_update_finality_σ : ∀ (st : (Model.specBase (V := V)).S) (σ : (Model.specBase (V := V)).CS), ((Model.specBase (V := V)).update_finality st σ).σ = st.σ := by
  intro st σ
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ
  simp only [Model.specBase, Member.update_finality, e]
  rfl

/-- The field `update_finality_σ` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_σ : ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS), ((Model.spec (V := V)).update_finality st σ).σ = st.σ :=
  fun st σ => specBase_update_finality_σ st.val σ

/-- The field `Protocol_admit_row_bodies` of `HandlersFacts` at `Model.specBase`: `admit_row`
    keeps the named blocks. -/
theorem specBase_Protocol_admit_row_bodies :
    ∀ (hc : HealConfig) (st : (Model.specBase (V := V)).NS) (a : NamedAttestation V), ((Model.specBase (V := V)).admit_row hc st a).bodies = st.bodies := by
  intro hc st a
  obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes
    (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig) st
    (Spec.Attestation.toSpecNamed a)
  simp only [Model.specBase, Member.admit_row, e]
  rfl

/-- The field `Protocol_admit_row_bodies` of `HandlersFacts` at `Model.spec`. -/
theorem spec_Protocol_admit_row_bodies :
    ∀ (hc : HealConfig) (st : (Model.spec (V := V)).NS) (a : NamedAttestation V), ((Model.spec (V := V)).admit_row hc st a).bodies = st.bodies :=
  fun hc st a => specBase_Protocol_admit_row_bodies hc st.val a

/-- The field `admit_row_core_T` of `HandlersFacts` at `Model.specBase`: `admit_row` keeps the
    tree. -/
theorem specBase_admit_row_core_T :
    ∀ (hc : HealConfig) (st : (Model.specBase (V := V)).NS) (a : NamedAttestation V), ((Model.specBase (V := V)).admit_row hc st a).core.T = st.core.T := by
  intro hc st a
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).admit_row_core_T hc st.toProofNamed a

/-- The field `admit_row_core_T` of `HandlersFacts` at `Model.spec`. -/
theorem spec_admit_row_core_T :
    ∀ (hc : HealConfig) (st : (Model.spec (V := V)).NS) (a : NamedAttestation V), ((Model.spec (V := V)).admit_row hc st a).core.T = st.core.T :=
  fun hc st a => specBase_admit_row_core_T hc st.val a

/-- The field `admit_rows_bodies_and_core_T` of `HandlersFacts` at `Model.specBase`:
    `admit_rows` keeps the named blocks and the tree. -/
theorem specBase_admit_rows_bodies_and_core_T :
    ∀ (hc : HealConfig), ∀ (rows : List (NamedAttestation V)) (st : (Model.specBase (V := V)).NS),
    ((Model.specBase (V := V)).admit_rows hc st rows).bodies = st.bodies ∧
    ((Model.specBase (V := V)).admit_rows hc st rows).core.T = st.core.T := by
  intro hc rows st
  obtain ⟨x, y, e⟩ := StoreSteps.admit_attestations_writes
    (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig)
    (rows.map Spec.Attestation.toSpecNamed) st
  simp only [Model.specBase, Member.admit_rows, e]
  exact ⟨rfl, rfl⟩

/-- The field `admit_rows_bodies_and_core_T` of `HandlersFacts` at `Model.spec`. -/
theorem spec_admit_rows_bodies_and_core_T :
    ∀ (hc : HealConfig), ∀ (rows : List (NamedAttestation V)) (st : (Model.spec (V := V)).NS),
    ((Model.spec (V := V)).admit_rows hc st rows).bodies = st.bodies ∧
    ((Model.spec (V := V)).admit_rows hc st rows).core.T = st.core.T :=
  fun hc rows st => specBase_admit_rows_bodies_and_core_T hc rows st.val

/-- The field `on_block_with_F` of `HandlersFacts` at `Model.specBase`: the finalized block of
    `st` is an ancestor of, or equal to, the finalized block after `on_block_with`. -/
theorem specBase_on_block_with_F :
    ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V), Block.Preceq st.core.F
    ((Model.specBase (V := V)).on_block_with admission E hc cfg st B).core.F := by
  intro admission E hc cfg (st : Spec.Store V) B
  unfold_draft
  unfold Block.Preceq
  exact Spec.Block.toProof_preceq_of_ancestorEq _ _
    (admitBlockCore_fields (Spec.Config.toSpec E hc cfg) (Spec.Provisional.toSpec E)
      st (Spec.Block.toSpecNamed B)).2.2.2

/-- The field `on_block_with_F` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_block_with_F :
    ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V), Block.Preceq st.core.F
    ((Model.spec (V := V)).on_block_with admission E hc cfg st B).core.F := by
  intro admission E hc cfg st B
  rcases ok_block_cases admission E hc cfg st B with ⟨-, e1, -⟩ | ⟨-, e1, -⟩
  · rw [e1]
    unfold DecoupledConsensusModel.Block.Preceq
    exact DecoupledConsensusModel.Block.preceq_self _
  · have key := specBase_on_block_with_F admission E hc cfg st.val B
    rw [← e1] at key
    exact key

/-- The field `on_goldfish_vote_checked_timestamp_block` of `HandlersFacts` at
    `Model.specBase`: `on_goldfish_vote_checked` keeps the block stamps. -/
theorem specBase_on_goldfish_vote_checked_timestamp_block :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).S) (u : GoldfishVote V), ((Model.specBase (V := V)).on_goldfish_vote_checked E st u).timestamp_block =
    st.timestamp_block := by
  intro E st u
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_goldfish_vote_checked_timestamp_block E st.toProof u

/-- The field `on_goldfish_vote_checked_timestamp_block` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_goldfish_vote_checked_timestamp_block :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (u : GoldfishVote V), ((Model.spec (V := V)).on_goldfish_vote_checked E st u).timestamp_block =
    st.timestamp_block :=
  fun E st u => specBase_on_goldfish_vote_checked_timestamp_block E st.val u

/-- The field `on_sg_vote_gf_votes` of `HandlersFacts` at `Model.specBase`: `on_sg_vote` keeps
    the Goldfish votes. -/
theorem specBase_on_sg_vote_gf_votes : ∀ (hc : HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V), ((Model.specBase (V := V)).on_sg_vote hc st a).gf_votes = st.gf_votes := by
  intro hc st a
  funext s
  unfold_spec
  exact congrFun ((Model.vocabulary_facts_handlers (V := V)).on_sg_vote_gf_votes hc st.toProof a) s

/-- The field `on_sg_vote_gf_votes` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_gf_votes : ∀ (hc : HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V), ((Model.spec (V := V)).on_sg_vote hc st a).gf_votes = st.gf_votes :=
  fun hc st a => specBase_on_sg_vote_gf_votes hc st.val a

/-- The field `on_sg_vote_timestamp_block` of `HandlersFacts` at `Model.specBase`: `on_sg_vote`
    keeps the block stamps. -/
theorem specBase_on_sg_vote_timestamp_block :
    ∀ (hc : HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V), ((Model.specBase (V := V)).on_sg_vote hc st a).timestamp_block = st.timestamp_block := by
  intro hc st a
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_sg_vote_timestamp_block hc st.toProof a

/-- The field `on_sg_vote_timestamp_block` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_timestamp_block :
    ∀ (hc : HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V), ((Model.spec (V := V)).on_sg_vote hc st a).timestamp_block = st.timestamp_block :=
  fun hc st a => specBase_on_sg_vote_timestamp_block hc st.val a

/-- The field `on_sg_vote_timestamp_vote` of `HandlersFacts` at `Model.specBase`: `on_sg_vote`
    keeps the Goldfish vote stamps. -/
theorem specBase_on_sg_vote_timestamp_vote :
    ∀ (hc : HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V), ((Model.specBase (V := V)).on_sg_vote hc st a).timestamp_vote = st.timestamp_vote := by
  intro hc st a
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_sg_vote_timestamp_vote hc st.toProof a

/-- The field `on_sg_vote_timestamp_vote` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_timestamp_vote :
    ∀ (hc : HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V), ((Model.spec (V := V)).on_sg_vote hc st a).timestamp_vote = st.timestamp_vote :=
  fun hc st a => specBase_on_sg_vote_timestamp_vote hc st.val a

/-- The field `update_finality_gf_votes` of `HandlersFacts` at `Model.specBase`:
    `update_finality` keeps the Goldfish votes. -/
theorem specBase_update_finality_gf_votes : ∀ (st : (Model.specBase (V := V)).S) (σ : (Model.specBase (V := V)).CS), ((Model.specBase (V := V)).update_finality st σ).gf_votes = st.gf_votes := by
  intro st σ
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ
  simp only [Model.specBase, Member.update_finality, e]
  rfl

/-- The field `update_finality_gf_votes` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_gf_votes : ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS), ((Model.spec (V := V)).update_finality st σ).gf_votes = st.gf_votes :=
  fun st σ => specBase_update_finality_gf_votes st.val σ

/-- The field `update_finality_timestamp_block` of `HandlersFacts` at `Model.specBase`:
    `update_finality` keeps the block stamps. -/
theorem specBase_update_finality_timestamp_block :
    ∀ (st : (Model.specBase (V := V)).S) (σ : (Model.specBase (V := V)).CS), ((Model.specBase (V := V)).update_finality st σ).timestamp_block = st.timestamp_block := by
  intro st σ
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ
  simp only [Model.specBase, Member.update_finality, e]
  rfl

/-- The field `update_finality_timestamp_block` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_timestamp_block :
    ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS), ((Model.spec (V := V)).update_finality st σ).timestamp_block = st.timestamp_block :=
  fun st σ => specBase_update_finality_timestamp_block st.val σ

/-- The field `update_finality_timestamp_vote` of `HandlersFacts` at `Model.specBase`:
    `update_finality` keeps the Goldfish vote stamps. -/
theorem specBase_update_finality_timestamp_vote :
    ∀ (st : (Model.specBase (V := V)).S) (σ : (Model.specBase (V := V)).CS), ((Model.specBase (V := V)).update_finality st σ).timestamp_vote = st.timestamp_vote := by
  intro st σ
  obtain ⟨a, b, c, d, e⟩ := StoreSteps.updateFinalityWith_writes st σ
  simp only [Model.specBase, Member.update_finality, e]
  rfl

/-- The field `update_finality_timestamp_vote` of `HandlersFacts` at `Model.spec`. -/
theorem spec_update_finality_timestamp_vote :
    ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS), ((Model.spec (V := V)).update_finality st σ).timestamp_vote = st.timestamp_vote :=
  fun st σ => specBase_update_finality_timestamp_vote st.val σ

/-- The field `advance_confirmed_eq_or_not_preceq` of `HandlersFacts` at `Model.spec`:
    `advance_confirmed old c` is `old`, or is not an ancestor of `old`. -/
theorem spec_advance_confirmed_eq_or_not_preceq :
    ∀ (old c : Block V), (Model.spec (V := V)).advance_confirmed old c = old ∨
    ¬ Block.Preceq ((Model.spec (V := V)).advance_confirmed old c) old := by
  intro old c
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).advance_confirmed_eq_or_not_preceq old c

/-- The field `advance_confirmed_values` of `HandlersFacts` at `Model.spec`: either `c` is an
    ancestor of, or equal to, `old` and `advance_confirmed old c = old`, or
    `advance_confirmed old c = c`. -/
theorem spec_advance_confirmed_values :
    ∀ (old c : Block V), (Block.Preceq c old ∧ (Model.spec (V := V)).advance_confirmed old c = old) ∨
    (Model.spec (V := V)).advance_confirmed old c = c := by
  intro old c
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).advance_confirmed_values old c

/-- The field `floor_on_stable_cases` of `HandlersFacts` at `Model.spec`:
    `floor_on_stable stable cand old` is `cand`, or `old`, or a block that is not an ancestor of
    `old`. -/
theorem spec_floor_on_stable_cases :
    ∀ (stable cand old : Block V), (Model.spec (V := V)).floor_on_stable stable cand old = cand ∨
    (Model.spec (V := V)).floor_on_stable stable cand old = old ∨
    ¬ Block.Preceq ((Model.spec (V := V)).floor_on_stable stable cand old) old := by
  intro stable cand old
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).floor_on_stable_cases stable cand old

/-- The field `floor_on_stable_stable_preceq` of `HandlersFacts` at `Model.spec`:
    `floor_on_stable stable candidate old` is a descendant of `stable`, or `stable` itself. -/
theorem spec_floor_on_stable_stable_preceq :
    ∀ (stable candidate old : Block V), Block.Preceq stable ((Model.spec (V := V)).floor_on_stable stable candidate old) := by
  intro stable candidate old
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).floor_on_stable_stable_preceq stable candidate old

/-- The field `floor_on_stable_values` of `HandlersFacts` at `Model.spec`:
    `floor_on_stable stable cand old` is `cand` with `stable ⪯ cand`, or `old` with `stable ⪯ old`,
    or `stable`. -/
theorem spec_floor_on_stable_values :
    ∀ (stable cand old : Block V), (Block.Preceq stable cand ∧ (Model.spec (V := V)).floor_on_stable stable cand old = cand) ∨
    (Block.Preceq stable old ∧ (Model.spec (V := V)).floor_on_stable stable cand old = old) ∨
    (Model.spec (V := V)).floor_on_stable stable cand old = stable := by
  intro stable cand old
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).floor_on_stable_values stable cand old

/-- The field `get_confirmed_eq_or` of `HandlersFacts` at `Model.specBase`: `get_confirmed st`
    is `st.latest_confirmed` or `get_stable st`. -/
theorem specBase_get_confirmed_eq_or :
    ∀ (st : (Model.specBase (V := V)).S), (Model.specBase (V := V)).get_confirmed st = st.latest_confirmed ∨
    (Model.specBase (V := V)).get_confirmed st = (Model.specBase (V := V)).get_stable st := by
  intro (st : Spec.Store V)
  show (Spec.Protocol.get_confirmed (Spec.Store.ofImage st)).toProof = st.latest_confirmed.toProof ∨
    (Spec.Protocol.get_confirmed (Spec.Store.ofImage st)).toProof =
      (Spec.Protocol.get_stable (Spec.Store.ofImage st)).toProof
  unfold Spec.Protocol.get_confirmed
  simp only [Id.run, pure]
  split_ifs
  · exact Or.inl (Spec.Store.toProof_blockOfImage _ _)
  · exact Or.inr rfl

/-- The field `get_confirmed_eq_or` of `HandlersFacts` at `Model.spec`. -/
theorem spec_get_confirmed_eq_or :
    ∀ (st : (Model.spec (V := V)).S), (Model.spec (V := V)).get_confirmed st = st.latest_confirmed ∨
    (Model.spec (V := V)).get_confirmed st = (Model.spec (V := V)).get_stable st :=
  fun st => specBase_get_confirmed_eq_or st.val

/-- The field `get_confirmed_values` of `HandlersFacts` at `Model.specBase`: either
    `get_stable st` is an ancestor of, or equal to, `st.latest_confirmed` and
    `get_confirmed st = st.latest_confirmed`, or `get_confirmed st = get_stable st`. -/
theorem specBase_get_confirmed_values :
    ∀ (st : (Model.specBase (V := V)).S), (Block.Preceq ((Model.specBase (V := V)).get_stable st) st.latest_confirmed ∧
    (Model.specBase (V := V)).get_confirmed st = st.latest_confirmed) ∨
    (Model.specBase (V := V)).get_confirmed st = (Model.specBase (V := V)).get_stable st := by
  intro (st : Spec.Store V)
  show (Block.Preceq (Spec.Protocol.get_stable (Spec.Store.ofImage st)).toProof
        st.latest_confirmed.toProof ∧
      (Spec.Protocol.get_confirmed (Spec.Store.ofImage st)).toProof = st.latest_confirmed.toProof) ∨
    (Spec.Protocol.get_confirmed (Spec.Store.ofImage st)).toProof =
      (Spec.Protocol.get_stable (Spec.Store.ofImage st)).toProof
  unfold Block.Preceq Spec.Protocol.get_confirmed
  simp only [Id.run, pure]
  split_ifs with h
  · have h' := Spec.Block.toProof_preceq_of_ancestorEq _ _ h
    rw [Spec.Store.ofImage_latest_confirmed, Spec.Store.toProof_blockOfImage] at h'
    exact Or.inl ⟨h', Spec.Store.toProof_blockOfImage _ _⟩
  · exact Or.inr rfl

/-- The field `get_confirmed_values` of `HandlersFacts` at `Model.spec`. -/
theorem spec_get_confirmed_values :
    ∀ (st : (Model.spec (V := V)).S), (Block.Preceq ((Model.spec (V := V)).get_stable st) st.latest_confirmed ∧
    (Model.spec (V := V)).get_confirmed st = st.latest_confirmed) ∨
    (Model.spec (V := V)).get_confirmed st = (Model.spec (V := V)).get_stable st :=
  fun st => specBase_get_confirmed_values st.val

/-- The field `get_stable_eq_or` of `HandlersFacts` at `Model.specBase`: `get_stable st` is
    `st.latest_stable` or `st.F`. -/
theorem specBase_get_stable_eq_or :
    ∀ (st : (Model.specBase (V := V)).S), (Model.specBase (V := V)).get_stable st = st.latest_stable ∨ (Model.specBase (V := V)).get_stable st = st.F := by
  intro (st : Spec.Store V)
  show (Spec.Protocol.get_stable (Spec.Store.ofImage st)).toProof = st.latest_stable.toProof ∨
    (Spec.Protocol.get_stable (Spec.Store.ofImage st)).toProof = st.F.toProof
  unfold Spec.Protocol.get_stable
  simp only [Id.run, pure]
  split_ifs
  · exact Or.inl (Spec.Store.toProof_blockOfImage _ _)
  · exact Or.inr (Spec.Store.toProof_blockOfImage _ _)

/-- The field `get_stable_eq_or` of `HandlersFacts` at `Model.spec`. -/
theorem spec_get_stable_eq_or :
    ∀ (st : (Model.spec (V := V)).S), (Model.spec (V := V)).get_stable st = st.latest_stable ∨ (Model.spec (V := V)).get_stable st = st.F :=
  fun st => specBase_get_stable_eq_or st.val

/-- The field `mem_on_sg_vote_sg_pool_of_not` of `HandlersFacts` at `Model.specBase`: when
    `on_sg_vote` does not refuse `a` (its round is within `η_SG` of the store's round and not later,
    its confirmed block is new for its sender and round, and its sender has fewer than two
    recorded), `a` is in the store's attestation set of its round afterwards. -/
theorem specBase_mem_on_sg_vote_sg_pool_of_not :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V) (h : ¬ (a.round < ((Model.specBase (V := V)).round_of hc st.s) - hc.η_SG ∨ ((Model.specBase (V := V)).round_of hc st.s) < a.round ∨
    a.confirmed ∈ (Model.specBase (V := V)).round_votes st a ∨ ((Model.specBase (V := V)).round_votes st a).card = 2)), a ∈ ((Model.specBase (V := V)).store_sg_pool ((Model.specBase (V := V)).on_sg_vote hc st a) a.round) := by
  intro hc st a h
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).mem_on_sg_vote_sg_pool_of_not hc st.toProof a h

/-- The field `mem_on_sg_vote_sg_pool_of_not` of `HandlersFacts` at `Model.spec`. -/
theorem spec_mem_on_sg_vote_sg_pool_of_not :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V) (h : ¬ (a.round < ((Model.spec (V := V)).round_of hc st.s) - hc.η_SG ∨ ((Model.spec (V := V)).round_of hc st.s) < a.round ∨
    a.confirmed ∈ (Model.spec (V := V)).round_votes st a ∨ ((Model.spec (V := V)).round_votes st a).card = 2)), a ∈ ((Model.spec (V := V)).store_sg_pool ((Model.spec (V := V)).on_sg_vote hc st a) a.round) :=
  fun hc st a h => specBase_mem_on_sg_vote_sg_pool_of_not hc st.val a h

/-- The field `mem_round_votes_iff` of `HandlersFacts` at `Model.specBase`:
    `o ∈ round_votes st a` exactly when some attestation of `a`'s round held by `st` is from `a`'s
    sender and confirms `o`. -/
theorem specBase_mem_round_votes_iff :
    ∀ (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V) (o : Option BlockId), o ∈ (Model.specBase (V := V)).round_votes st a ↔
    ∃ b ∈ ((Model.specBase (V := V)).store_sg_pool st a.round), b.val_index = a.val_index ∧ b.confirmed = o := by
  intro st a o
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).mem_round_votes_iff st.toProof a o

/-- The field `mem_round_votes_iff` of `HandlersFacts` at `Model.spec`. -/
theorem spec_mem_round_votes_iff :
    ∀ (st : (Model.spec (V := V)).S) (a : CombinedAttestation V) (o : Option BlockId), o ∈ (Model.spec (V := V)).round_votes st a ↔
    ∃ b ∈ ((Model.spec (V := V)).store_sg_pool st a.round), b.val_index = a.val_index ∧ b.confirmed = o :=
  fun st a o => specBase_mem_round_votes_iff st.val a o

/-- The field `namedStore_initial_h_max` of `HandlersFacts` at `Model.spec`: the initial
    store's `h_max` is `1`. -/
theorem spec_namedStore_initial_h_max :
    ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.h_max = 1 := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).namedStore_initial_h_max

/-- The field `on_goldfish_vote_checked_of_mem` of `HandlersFacts` at `Model.spec`: a Goldfish
    vote the store already holds for its slot leaves the store unchanged. -/
theorem spec_on_goldfish_vote_checked_of_mem : ∀ (E : Env V) (st : (Model.spec (V := V)).S) (u : GoldfishVote V) (h : u ∈ st.gf_votes u.slot), (Model.spec (V := V)).on_goldfish_vote_checked E st u = st := by
  intro E st u h
  obtain ⟨u', rfl⟩ := exists_vote u
  simp only [Model.spec, Model.S.gf_votes, Member.store_gf_votes, Spec.Store.toProof_gf_votes,
    Spec.GoldfishVote.toProof_slot, List.mem_map,
    Spec.GoldfishVote.toProof_injective.eq_iff, exists_eq_right] at h
  simp only [Model.spec, Member.on_goldfish_vote_checked, Spec.GoldfishVote.toSpec_toProof]
  unfold Spec.Protocol.on_goldfish_vote_checked Spec.Protocol.on_goldfish_vote
  simp only [Id.run, pure]
  split_ifs <;> first | rfl | (exfalso; simp_all [StoreSteps.getElem_fn])

/-- The field `on_sg_vote_timestamp_of_admitted` of `HandlersFacts` at `Model.specBase`: when
    `on_sg_vote` does not refuse `a`, it stamps `a`'s SG vote with `st.t`. -/
theorem specBase_on_sg_vote_timestamp_of_admitted :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V) (h : ¬ (a.round < ((Model.specBase (V := V)).round_of hc st.s) - hc.η_SG ∨ ((Model.specBase (V := V)).round_of hc st.s) < a.round ∨
    a.confirmed ∈ (Model.specBase (V := V)).round_votes st a ∨ ((Model.specBase (V := V)).round_votes st a).card = 2)), ((Model.specBase (V := V)).on_sg_vote hc st a).timestamp_sg_vote ((Model.specBase (V := V)).sgVote a) =
    some (st.t : Stamp) := by
  intro hc st a h
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).on_sg_vote_timestamp_of_admitted hc st.toProof a h

/-- The field `on_sg_vote_timestamp_of_admitted` of `HandlersFacts` at `Model.spec`. -/
theorem spec_on_sg_vote_timestamp_of_admitted :
    ∀ (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (a : CombinedAttestation V) (h : ¬ (a.round < ((Model.spec (V := V)).round_of hc st.s) - hc.η_SG ∨ ((Model.spec (V := V)).round_of hc st.s) < a.round ∨
    a.confirmed ∈ (Model.spec (V := V)).round_votes st a ∨ ((Model.spec (V := V)).round_votes st a).card = 2)), ((Model.spec (V := V)).on_sg_vote hc st a).timestamp_sg_vote ((Model.spec (V := V)).sgVote a) =
    some (st.t : Stamp) :=
  fun hc st a h => specBase_on_sg_vote_timestamp_of_admitted hc st.val a h

/-- The field `preceq_advance_confirmed_candidate` of `HandlersFacts` at `Model.spec`: `c` is
    an ancestor of, or equal to, `advance_confirmed old c`. -/
theorem spec_preceq_advance_confirmed_candidate :
    ∀ (old c : Block V), Block.Preceq c ((Model.spec (V := V)).advance_confirmed old c) := by
  intro old c
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).preceq_advance_confirmed_candidate old c

/-- The field `preceq_floor_on_stable_of_compatible` of `HandlersFacts` at `Model.spec`: if
    `stable` and `cand` are compatible and `X` is an ancestor of, or equal to, `cand`, then `X` is
    an ancestor of, or equal to, `floor_on_stable stable cand old`. -/
theorem spec_preceq_floor_on_stable_of_compatible :
    ∀ {X stable cand : Block V} (old : Block V) (hc : Block.compatible stable cand = true) (hX : Block.Preceq X cand), Block.Preceq X ((Model.spec (V := V)).floor_on_stable stable cand old) := by
  intro X stable cand old hc hX
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).preceq_floor_on_stable_of_compatible (X := X) (stable := stable) (cand := cand) old hc hX

/-- The field `process_block_core_sg_rows_eq` of `HandlersFacts` at `Model.specBase`:
    `ns_process_block_core` keeps the named attestations of every round. -/
theorem specBase_process_block_core_sg_rows_eq : ∀ (S : Setup V) (st : (Model.specBase (V := V)).NS) (B : NamedBlock V), ((Model.specBase (V := V)).ns_process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  intro S st B
  unfold_draft
  funext r
  simp only [Member.sg_rows, Spec.Store.toProofNamed_sg_rows, admitBlockCore_attestations]

/-- The field `process_block_core_sg_rows_eq` of `HandlersFacts` at `Model.spec`. -/
theorem spec_process_block_core_sg_rows_eq : ∀ (S : Setup V) (st : (Model.spec (V := V)).NS) (B : NamedBlock V), ((Model.spec (V := V)).ns_process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  intro S st B
  rcases ok_block_cases .alsoCarried S.E S.hc S.cfg st B with ⟨-, -, e2⟩ | ⟨-, -, e2⟩
  · rw [e2]
  · have key := specBase_process_block_core_sg_rows_eq S st.val B
    rw [← e2] at key
    exact key

/-- The field `Sts_setClock_bodies` of `HandlersFacts` at `Model.spec`: setting a named store's
    clock keeps its named blocks. -/
theorem spec_Sts_setClock_bodies :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).bodies = st.bodies := by
  intro E st t
  rfl

/-- The field `setClock_core_F` of `HandlersFacts` at `Model.specBase`: setting a named store's
    clock keeps its finalized block. -/
theorem specBase_setClock_core_F :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.F = st.core.F := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).setClock_core_F E st.toProofNamed t

/-- The field `setClock_core_F` of `HandlersFacts` at `Model.spec`. -/
theorem spec_setClock_core_F :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.F = st.core.F :=
  fun E st t => specBase_setClock_core_F E st.val t

/-- The field `setClock_core_J` of `HandlersFacts` at `Model.specBase`: setting a named store's
    clock keeps its justified block. -/
theorem specBase_setClock_core_J :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.J = st.core.J := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).setClock_core_J E st.toProofNamed t

/-- The field `setClock_core_J` of `HandlersFacts` at `Model.spec`. -/
theorem spec_setClock_core_J :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.J = st.core.J :=
  fun E st t => specBase_setClock_core_J E st.val t

/-- The field `Sts_setClock_core_T` of `HandlersFacts` at `Model.specBase`: setting a named
    store's clock keeps its tree. -/
theorem specBase_Sts_setClock_core_T :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.T = st.core.T := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).Sts_setClock_core_T E st.toProofNamed t

/-- The field `Sts_setClock_core_T` of `HandlersFacts` at `Model.spec`. -/
theorem spec_Sts_setClock_core_T :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.T = st.core.T :=
  fun E st t => specBase_Sts_setClock_core_T E st.val t

/-- The field `setClock_core_gf_votes` of `HandlersFacts` at `Model.specBase`: setting a named
    store's clock keeps its Goldfish votes of every slot. -/
theorem specBase_setClock_core_gf_votes :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int) (s : Slot), ((Model.specBase (V := V)).ns_setClock E st t).core.gf_votes s = st.core.gf_votes s := by
  intro E st t s
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).setClock_core_gf_votes E st.toProofNamed t s

/-- The field `setClock_core_gf_votes` of `HandlersFacts` at `Model.spec`. -/
theorem spec_setClock_core_gf_votes :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int) (s : Slot), ((Model.spec (V := V)).ns_setClock E st t).core.gf_votes s = st.core.gf_votes s :=
  fun E st t s => specBase_setClock_core_gf_votes E st.val t s

/-- The field `setClock_core_h_max` of `HandlersFacts` at `Model.specBase`: setting a named
    store's clock keeps its `h_max`. -/
theorem specBase_setClock_core_h_max :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.h_max = st.core.h_max := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).setClock_core_h_max E st.toProofNamed t

/-- The field `setClock_core_h_max` of `HandlersFacts` at `Model.spec`. -/
theorem spec_setClock_core_h_max :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.h_max = st.core.h_max :=
  fun E st t => specBase_setClock_core_h_max E st.val t

/-- The field `setClock_core_latest_confirmed` of `HandlersFacts` at `Model.specBase`: setting
    a named store's clock keeps its `latest_confirmed`. -/
theorem specBase_setClock_core_latest_confirmed :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.latest_confirmed = st.core.latest_confirmed := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).setClock_core_latest_confirmed E st.toProofNamed t

/-- The field `setClock_core_latest_confirmed` of `HandlersFacts` at `Model.spec`. -/
theorem spec_setClock_core_latest_confirmed :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.latest_confirmed = st.core.latest_confirmed :=
  fun E st t => specBase_setClock_core_latest_confirmed E st.val t

/-- The field `setClock_core_latest_stable` of `HandlersFacts` at `Model.specBase`: setting a
    named store's clock keeps its `latest_stable`. -/
theorem specBase_setClock_core_latest_stable :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.latest_stable = st.core.latest_stable := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).setClock_core_latest_stable E st.toProofNamed t

/-- The field `setClock_core_latest_stable` of `HandlersFacts` at `Model.spec`. -/
theorem spec_setClock_core_latest_stable :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.latest_stable = st.core.latest_stable :=
  fun E st t => specBase_setClock_core_latest_stable E st.val t

/-- The field `Sts_setClock_core_pool` of `HandlersFacts` at `Model.specBase`: setting a named
    store's clock keeps its set of Goldfish votes of every slot. -/
theorem specBase_Sts_setClock_core_pool :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int) (s : Slot), ((Model.specBase (V := V)).store_pool ((Model.specBase (V := V)).ns_setClock E st t).core s) = ((Model.specBase (V := V)).store_pool st.core s) := by
  intro E st t s
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).Sts_setClock_core_pool E st.toProofNamed t s

/-- The field `Sts_setClock_core_pool` of `HandlersFacts` at `Model.spec`. -/
theorem spec_Sts_setClock_core_pool :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int) (s : Slot), ((Model.spec (V := V)).store_pool ((Model.spec (V := V)).ns_setClock E st t).core s) = ((Model.spec (V := V)).store_pool st.core s) :=
  fun E st t s => specBase_Sts_setClock_core_pool E st.val t s

/-- The field `Sts_setClock_core_s` of `HandlersFacts` at `Model.specBase`: after setting the
    clock to `t`, the slot is `E.slotOf t`. -/
theorem specBase_Sts_setClock_core_s :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.s = E.slotOf t := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).Sts_setClock_core_s E st.toProofNamed t

/-- The field `Sts_setClock_core_s` of `HandlersFacts` at `Model.spec`. -/
theorem spec_Sts_setClock_core_s :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.s = E.slotOf t :=
  fun E st t => specBase_Sts_setClock_core_s E st.val t

/-- The field `Sts_setClock_core_t` of `HandlersFacts` at `Model.specBase`: after setting the
    clock to `t`, the clock is `t`. -/
theorem specBase_Sts_setClock_core_t :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.t = t := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).Sts_setClock_core_t E st.toProofNamed t

/-- The field `Sts_setClock_core_t` of `HandlersFacts` at `Model.spec`. -/
theorem spec_Sts_setClock_core_t :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.t = t :=
  fun E st t => specBase_Sts_setClock_core_t E st.val t

/-- The field `setClock_core_timestamp_block` of `HandlersFacts` at `Model.specBase`: setting a
    named store's clock keeps its block stamps. -/
theorem specBase_setClock_core_timestamp_block :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.timestamp_block = st.core.timestamp_block := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).setClock_core_timestamp_block E st.toProofNamed t

/-- The field `setClock_core_timestamp_block` of `HandlersFacts` at `Model.spec`. -/
theorem spec_setClock_core_timestamp_block :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.timestamp_block = st.core.timestamp_block :=
  fun E st t => specBase_setClock_core_timestamp_block E st.val t

/-- The field `setClock_core_timestamp_vote` of `HandlersFacts` at `Model.specBase`: setting a
    named store's clock keeps its Goldfish vote stamps. -/
theorem specBase_setClock_core_timestamp_vote :
    ∀ (E : Env V) (st : (Model.specBase (V := V)).NS) (t : Int), ((Model.specBase (V := V)).ns_setClock E st t).core.timestamp_vote = st.core.timestamp_vote := by
  intro E st t
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).setClock_core_timestamp_vote E st.toProofNamed t

/-- The field `setClock_core_timestamp_vote` of `HandlersFacts` at `Model.spec`. -/
theorem spec_setClock_core_timestamp_vote :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.timestamp_vote = st.core.timestamp_vote :=
  fun E st t => specBase_setClock_core_timestamp_vote E st.val t

/-- The field `Sts_setClock_core_σ` of `HandlersFacts` at `Model.spec`: setting a named store's
    clock keeps its chain-state map. -/
theorem spec_Sts_setClock_core_σ :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).core.σ = st.core.σ := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `setClock_gradeView` of `HandlersFacts` at `Model.spec`: setting a named store's
    clock keeps the grade view of its healing view. -/
theorem spec_setClock_gradeView :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing ((Model.spec (V := V)).ns_setClock E st t).core))
    = ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing st.core)) := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `setClock_sg_rows` of `HandlersFacts` at `Model.spec`: setting a named store's
    clock keeps its named attestations of every round. -/
theorem spec_setClock_sg_rows :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).ns_setClock E st t).sg_rows = st.sg_rows := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `setClock_toHealing_F` of `HandlersFacts` at `Model.spec`: setting a named
    store's clock keeps the finalized block of its healing view. -/
theorem spec_setClock_toHealing_F :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).toHealing ((Model.spec (V := V)).ns_setClock E st t).core).toFG.F = st.core.F := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `setClock_toHealing_J` of `HandlersFacts` at `Model.spec`: setting a named
    store's clock keeps the justified block of its healing view. -/
theorem spec_setClock_toHealing_J :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).toHealing ((Model.spec (V := V)).ns_setClock E st t).core).toFG.J = st.core.J := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `setClock_toHealing_T` of `HandlersFacts` at `Model.spec`: setting a named
    store's clock keeps the tree of its healing view. -/
theorem spec_setClock_toHealing_T : ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).toHealing ((Model.spec (V := V)).ns_setClock E st t).core).toFG.toSG.toGoldfishStore.T = st.core.T := by
  intro E st t
  simp only [Model.spec, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, Model.GS.T,
    Model.NS.core, Model.S.T, Member.toHealing, Member.toFG, Member.toSG, Member.toGoldfishStore,
    Member.gs_T, Member.store_T, Member.core, Member.ns_setClock, id]
  first
    | exact rfl
    | simp [Spec.Store.toProof, DecoupledConsensusModel.Protocol.Store.toHealing]

/-- The field `setClock_toHealing_h_j` of `HandlersFacts` at `Model.spec`: setting a named
    store's clock keeps the `h_j` of its healing view. -/
theorem spec_setClock_toHealing_h_j :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).toHealing ((Model.spec (V := V)).ns_setClock E st t).core).toFG.h_j = st.core.h_j := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `setClock_toHealing_h_max` of `HandlersFacts` at `Model.spec`: setting a named
    store's clock keeps the `h_max` of its healing view. -/
theorem spec_setClock_toHealing_h_max :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).toHealing ((Model.spec (V := V)).ns_setClock E st t).core).toFG.h_max = st.core.h_max := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)

/-- The field `setClock_toHealing_σ` of `HandlersFacts` at `Model.spec`: setting a named
    store's clock keeps the chain-state map of its healing view. -/
theorem spec_setClock_toHealing_σ :
    ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Int), ((Model.spec (V := V)).toHealing ((Model.spec (V := V)).ns_setClock E st t).core).toFG.σ = st.core.σ := by
  intro E st t
  first
    | rfl
    | (simp only [Model.spec]; rfl)


/-- The field `committeePools_on_tick_emit` of `HandlersFacts` at `Model.specBase`: if every
    Goldfish vote of slot `k` in the store of `before` is from a member of `S.E.committee k`, for
    every `k`, then the same holds after `v`'s tick at `t`. -/
theorem specBase_committeePools_on_tick_emit : ∀ (S : Setup V) (v : V) (before : (Model.specBase (V := V)).N) (t : Time) (out : (Model.specBase (V := V)).N × List (NamedObject V)), (Model.specBase (V := V)).tick S v before t ⇢ out → (∀ (k : Slot) (u : GoldfishVote V), u ∈ before.st.core.gf_votes k → u.val_index ∈ S.E.committee k) → ∀ (k : Slot) (u : GoldfishVote V), u ∈ out.1.st.core.gf_votes k → u.val_index ∈ S.E.committee k := by
  intro S v before t out hout h k u hu
  have hr := HandlersRunFacts.specBase_tick_reach S v before t out hout
  have hvic : StoreSteps.VotesInCommittee (Setup.toSpec S).P (Spec.NodeState.st before) := by
    intro k' u' hu'
    have h' := h k' u'.toProof (by
      show u'.toProof ∈ ((Spec.NodeState.st before).gf_votes k').map
        Spec.GoldfishVote.toProof
      exact List.mem_map_of_mem hu')
    simpa [Setup.toSpec, Spec.Provisional.toSpec_committee] using h'
  have hout' := StoreSteps.reach_induction _
    (fun a b hs hq => StoreSteps.votesInCommittee_step _ _ _ a b hs hq) hr hvic
  obtain ⟨u', rfl⟩ := exists_vote u
  have hu' : u' ∈ (Spec.NodeState.st out.1).gf_votes k := by
    have h2 : u'.toProof ∈ ((Spec.NodeState.st out.1).gf_votes k).map
        Spec.GoldfishVote.toProof := hu
    simpa [List.mem_map, Spec.GoldfishVote.toProof_injective.eq_iff] using h2
  have h3 := hout' k u' hu'
  simpa [Setup.toSpec, Spec.Provisional.toSpec_committee] using h3

/-- The field `committeePools_on_tick_emit` of `HandlersFacts` at `Model.spec`. -/
theorem spec_committeePools_on_tick_emit : ∀ (S : Setup V) (v : V) (before : (Model.spec (V := V)).N) (t : Time) (out : (Model.spec (V := V)).N × List (NamedObject V)), (Model.spec (V := V)).tick S v before t ⇢ out → (∀ (k : Slot) (u : GoldfishVote V), u ∈ before.st.core.gf_votes k → u.val_index ∈ S.E.committee k) → ∀ (k : Slot) (u : GoldfishVote V), u ∈ out.1.st.core.gf_votes k → u.val_index ∈ S.E.committee k :=
  fun S v before t out => specBase_committeePools_on_tick_emit S v before.val t (out.1.val, out.2)

/-- The field `commitBlock_core` of `HandlersFacts` at `Model.spec`: the store part of
    `commitBlock before after B` is `after`. -/
theorem spec_commitBlock_core : ∀ (before : (Model.spec (V := V)).NS)
    (after : (Model.spec (V := V)).S) (B : NamedBlock V)
    (_hafter : ((Model.spec (V := V)).ns_with_core before after).core = after),
    ((Model.spec (V := V)).commitBlock before after B).core = after := by
  intro before after B _
  rfl

/-- The field `commit_core` of `HandlersFacts` at `Model.spec`: the store part of
    `commitBlock before after B` is `after`. -/
theorem spec_commit_core : ∀ (before : (Model.spec (V := V)).NS)
    (after : (Model.spec (V := V)).S) (B : NamedBlock V)
    (_hafter : ((Model.spec (V := V)).ns_with_core before after).core = after),
    ((Model.spec (V := V)).commitBlock before after B).core = after :=
  spec_commitBlock_core

/-! ## The readers of a store part, through `sameCore` -/

/-- The field `sameCore_t` of `HandlersFacts` at `Model.spec`: two stores with the same store
    part have the same clock. -/
theorem spec_sameCore_t : ∀ {a b : (Model.spec (V := V)).S},
    (Model.spec (V := V)).sameCore a b → a.t = b.t :=
  fun h => congrArg DecoupledConsensusModel.Protocol.Store.t h

/-- The field `sameCore_s` of `HandlersFacts` at `Model.spec`: two stores with the same store
    part have the same slot. -/
theorem spec_sameCore_s : ∀ {a b : (Model.spec (V := V)).S},
    (Model.spec (V := V)).sameCore a b → a.s = b.s :=
  fun h => congrArg DecoupledConsensusModel.Protocol.Store.s h

/-- The field `sameCore_T` of `HandlersFacts` at `Model.spec`: two stores with the same store
    part have the same tree. -/
theorem spec_sameCore_T : ∀ {a b : (Model.spec (V := V)).S},
    (Model.spec (V := V)).sameCore a b → a.T = b.T :=
  fun h => congrArg DecoupledConsensusModel.Protocol.Store.T h

/-- The field `sameCore_timestamp_block` of `HandlersFacts` at `Model.spec`: two stores with
    the same store part have the same block stamps. -/
theorem spec_sameCore_timestamp_block : ∀ {a b : (Model.spec (V := V)).S},
    (Model.spec (V := V)).sameCore a b → a.timestamp_block = b.timestamp_block :=
  fun h => congrArg DecoupledConsensusModel.Protocol.Store.timestamp_block h

/-- The field `sameCore_timestamp_vote` of `HandlersFacts` at `Model.spec`: two stores with the
    same store part have the same Goldfish vote stamps. -/
theorem spec_sameCore_timestamp_vote : ∀ {a b : (Model.spec (V := V)).S},
    (Model.spec (V := V)).sameCore a b → a.timestamp_vote = b.timestamp_vote :=
  fun h => congrArg DecoupledConsensusModel.Protocol.Store.timestamp_vote h

/-- The field `sameCore_timestamp_sg_vote` of `HandlersFacts` at `Model.spec`: two stores with
    the same store part have the same SG vote stamps. -/
theorem spec_sameCore_timestamp_sg_vote : ∀ {a b : (Model.spec (V := V)).S},
    (Model.spec (V := V)).sameCore a b → a.timestamp_sg_vote = b.timestamp_sg_vote :=
  fun h => congrArg DecoupledConsensusModel.Protocol.Store.timestamp_sg_vote h

/-- The field `sameCore_gf_votes` of `HandlersFacts` at `Model.spec`: two stores with the same
    store part hold the same Goldfish votes. -/
theorem spec_sameCore_gf_votes : ∀ {a b : (Model.spec (V := V)).S},
    (Model.spec (V := V)).sameCore a b → a.gf_votes = b.gf_votes :=
  fun h => congrArg DecoupledConsensusModel.Protocol.Store.gf_votes h

/-- The field `sameCore_F` of `HandlersFacts` at `Model.spec`: two stores with the same store
    part have the same finalized block. -/
theorem spec_sameCore_F : ∀ {a b : (Model.spec (V := V)).S},
    (Model.spec (V := V)).sameCore a b → a.F = b.F :=
  fun h => congrArg DecoupledConsensusModel.Protocol.Store.F h

/-- The field `sameCore_store_sg_pool` of `HandlersFacts` at `Model.spec`: two stores with the
    same store part hold the same attestations of every round. -/
theorem spec_sameCore_store_sg_pool : ∀ {a b : (Model.spec (V := V)).S},
    (Model.spec (V := V)).sameCore a b →
      (Model.spec (V := V)).store_sg_pool a = (Model.spec (V := V)).store_sg_pool b := by
  intro a b h
  funext r
  have e := congrArg (fun s => (DecoupledConsensusModel.Protocol.Store.sg_votes s r).toFinset) h
  simp only [Spec.Store.toProof_sg_votes] at e
  have hm : ∀ L : List (Spec.Attestation V),
      (L.map Spec.Attestation.toProof).toFinset =
        L.toFinset.image Spec.Attestation.toProof := fun L => by
    ext x; simp [List.mem_toFinset, List.mem_map, Finset.mem_image]
  rw [hm, hm] at e
  exact e

/-! ## The commit members after the Goldfish vote and block handlers -/

/-- The field `ns_with_core_sg_rows` of `HandlersFacts` at `Model.spec`: committing the store
    after a Goldfish vote keeps the named attestations. -/
theorem spec_ns_with_core_sg_rows : ∀ (E : Env V) (ns : (Model.spec (V := V)).NS)
    (u : GoldfishVote V) (st : (Model.spec (V := V)).S)
    (hafter : (Model.spec (V := V)).on_goldfish_vote_checked E ns.core u = st),
    ((Model.spec (V := V)).ns_with_core ns st).sg_rows = ns.sg_rows := by
  intro E ns u st hafter
  subst hafter
  show Member.sg_rows (Member.on_goldfish_vote_checked E ns.val u) = Member.sg_rows ns.val
  obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes
    (Spec.Provisional.toSpec E) ns.val (Spec.GoldfishVote.toSpec u)
  unfold Member.on_goldfish_vote_checked
  rw [e]
  rfl

/-- The field `ns_with_core_bodies` of `HandlersFacts` at `Model.spec`: committing the store
    after a Goldfish vote keeps the named blocks. -/
theorem spec_ns_with_core_bodies : ∀ (E : Env V) (st : (Model.spec (V := V)).NS)
    (u : GoldfishVote V) (c : (Model.spec (V := V)).S)
    (hafter : (Model.spec (V := V)).on_goldfish_vote_checked E st.core u = c),
    ((Model.spec (V := V)).ns_with_core st c).bodies = st.bodies := by
  intro E st u c hafter
  subst hafter
  show Member.bodies (Member.on_goldfish_vote_checked E st.val u) = Member.bodies st.val
  obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes
    (Spec.Provisional.toSpec E) st.val (Spec.GoldfishVote.toSpec u)
  unfold Member.on_goldfish_vote_checked
  rw [e]
  rfl

/-- The field `process_block_core_bodies_eq_commit` of `HandlersFacts` at `Model.spec`:
    committing the block handler's store part to the named store gives the handler's named store. -/
theorem spec_process_block_core_bodies_eq_commit : ∀ (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) {st : (Model.spec (V := V)).NS}
    {B : NamedBlock V}, B.parent ∈ st.bodies →
    ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).bodies =
      ((Model.spec (V := V)).commitBlock st
        ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).core B).bodies :=
  fun _ _ _ _ _ _ => rfl

/-- The tree after the core block handler at `Model.spec` is the tree before, or the tree
    before with `Block.toSpecNamed B` added. -/
theorem process_block_core_T_cases (E : Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : (Model.spec (V := V)).NS)
    (B : NamedBlock V) :
    ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).val.T = st.val.T ∨
      ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).val.T =
        st.val.T ∪ {Spec.Block.toSpecNamed B} := by
  rcases ok_block_cases .alsoCarried E hc cfg st B with ⟨-, -, e2⟩ | ⟨-, -, e2⟩
  · left; rw [e2]
  · rw [e2]
    show (Handlers.admitBlockCore _ _ st.val _).T = _ ∨ (Handlers.admitBlockCore _ _ st.val _).T = _
    unfold Handlers.admitBlockCore
    split
    · right; exact SubtypeEqualities.blockCore_T _ _ _ _
    · left; rfl

/-- A named block is among the named blocks of a store of `Model.spec` exactly when
    `Block.toSpecNamed D` is in its tree. -/
theorem mem_bodies_ok (st : (Model.spec (V := V)).NS) (D : NamedBlock V) :
    D ∈ st.bodies ↔ Spec.Block.toSpecNamed D ∈ st.val.T :=
  mem_bodies_iff st.val D

/-- The field `commit_rows` of `HandlersFacts` at `Model.spec`: committing the core block
    handler's store keeps the named attestations. -/
theorem spec_commit_rows : ∀ (E : Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (before : (Model.spec (V := V)).NS)
    (after : (Model.spec (V := V)).S) (B : NamedBlock V)
    (hafter : ((Model.spec (V := V)).ns_process_block_core E hc cfg before B).core = after),
    ((Model.spec (V := V)).commitBlock before after B).sg_rows = before.sg_rows := by
  intro E hc cfg before after B hafter
  subst hafter
  show Member.sg_rows ((Model.spec (V := V)).ns_process_block_core E hc cfg before B).val =
    Member.sg_rows before.val
  rcases ok_block_cases .alsoCarried E hc cfg before B with ⟨-, -, e2⟩ | ⟨-, -, e2⟩
  · rw [e2]
  · rw [e2]
    show Member.sg_rows (Handlers.admitBlockCore _ _ before.val _) = _
    funext r
    simp only [Member.sg_rows, Spec.Store.toProofNamed_sg_rows,
      admitBlockCore_attestations]

/-- The field `mem_commitBlock_bodies_of_mem` of `HandlersFacts` at `Model.spec`: a named block
    held before the core block handler is held after the commit. -/
theorem spec_mem_commitBlock_bodies_of_mem : ∀ (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) {before : (Model.spec (V := V)).NS}
    {after : (Model.spec (V := V)).S} {B D : NamedBlock V}
    (hafter : ((Model.spec (V := V)).ns_process_block_core E hc cfg before B).core = after),
    D ∈ before.bodies → D ∈ ((Model.spec (V := V)).commitBlock before after B).bodies := by
  intro E hc cfg before after B D hafter hD
  subst hafter
  show D ∈ ((Model.spec (V := V)).ns_process_block_core E hc cfg before B).bodies
  rw [mem_bodies_ok] at hD ⊢
  rcases process_block_core_T_cases E hc cfg before B with e | e <;> rw [e]
  · exact hD
  · exact Finset.mem_union_left _ hD

/-- The field `mem_commitBlock_bodies_of_fresh` of `HandlersFacts` at `Model.spec`: a block the
    core block handler newly holds is among the committed named blocks. -/
theorem spec_mem_commitBlock_bodies_of_fresh : ∀ (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) {before : (Model.spec (V := V)).NS}
    {after : (Model.spec (V := V)).S} {B : NamedBlock V}
    (hafter : ((Model.spec (V := V)).ns_process_block_core E hc cfg before B).core = after),
    B.erase ∉ before.core.T ∧ B.erase ∈ after.T →
      B ∈ ((Model.spec (V := V)).commitBlock before after B).bodies := by
  intro E hc cfg before after B hafter ⟨hnot, hin⟩
  subst hafter
  show B ∈ ((Model.spec (V := V)).ns_process_block_core E hc cfg before B).bodies
  rw [mem_bodies_ok]
  rcases process_block_core_T_cases E hc cfg before B with e | e
  · exact absurd (by
      show B.erase ∈ before.val.toProof.T
      have h2 : B.erase ∈
          ((Model.spec (V := V)).ns_process_block_core E hc cfg before B).val.toProof.T := hin
      rw [Spec.Store.toProof_T, e] at h2
      exact h2) hnot
  · rw [e]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- The field `mem_commitBlock_bodies` of `HandlersFacts` at `Model.spec`: a committed named
    block was held before, or is `B` newly held. -/
theorem spec_mem_commitBlock_bodies : ∀ (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) {before : (Model.spec (V := V)).NS}
    {after : (Model.spec (V := V)).S} {B D : NamedBlock V}
    (hafter : ((Model.spec (V := V)).ns_process_block_core E hc cfg before B).core = after)
    (hheld : B ∈ ((Model.spec (V := V)).commitBlock before after B).bodies →
      B.erase ∈ before.core.T → B ∈ before.bodies),
    D ∈ ((Model.spec (V := V)).commitBlock before after B).bodies →
      (B.erase ∉ before.core.T ∧ B.erase ∈ after.T) ∧ D = B ∨ D ∈ before.bodies := by
  intro E hc cfg before after B D hafter hheld hD
  subst hafter
  have hD' := hD
  change D ∈ ((Model.spec (V := V)).ns_process_block_core E hc cfg before B).bodies at hD'
  rw [mem_bodies_ok] at hD'
  rcases process_block_core_T_cases E hc cfg before B with e | e
  · right
    rw [e] at hD'
    exact (mem_bodies_ok before D).2 hD'
  · rw [e] at hD'
    rcases Finset.mem_union.1 hD' with h | h
    · exact Or.inr ((mem_bodies_ok before D).2 h)
    · have hDB : D = B := by
        have := congrArg Spec.Block.toProofNamed (Finset.mem_singleton.1 h)
        simpa only [Spec.Block.toProofNamed_toSpecNamed] using this
      subst hDB
      by_cases hold : D.erase ∈ before.core.T
      · exact Or.inr (hheld hD hold)
      · refine Or.inl ⟨⟨hold, ?_⟩, rfl⟩
        show D.erase ∈
          ((Model.spec (V := V)).ns_process_block_core E hc cfg before D).val.toProof.T
        have hX : D.erase = (Spec.Block.toSpecNamed D).toProof := by
          rw [← Spec.Block.toProofNamed_erase,
            Spec.Block.toProofNamed_toSpecNamed]
        rw [Spec.Store.toProof_T, e, hX]
        exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ h)

/-! ## The admission of an attestation, read through `Store.toProof` -/

/-- Two attestations with the same image under `Attestation.toProof` have the same sender, round and
    confirmed block. -/
theorem attestation_fields_of_toProof {a b : Spec.Attestation V}
    (h : a.toProof = b.toProof) :
    a.val_index = b.val_index ∧ a.round = b.round ∧ a.confirmed = b.confirmed := by
  obtain ⟨v1, r1, c1, hp1, f1⟩ := a
  obtain ⟨v2, r2, c2, hp2, f2⟩ := b
  simp only [Spec.Attestation.toProof,
    DecoupledConsensusModel.CombinedAttestation.mk.injEq] at h
  exact ⟨h.1, h.2.1, Option.map_injective Spec.BlockId.toProof_injective h.2.2.1⟩

/-- Admitting attestations with the same image into stores with the same image under `Store.toProof`
    gives stores with the same image. -/
theorem toProof_admit_attestation_congr (C : Spec.Config)
    {st1 st2 : Spec.Store V} {a1 a2 : Spec.Attestation V}
    (h : st1.toProof = st2.toProof) (ha : a1.toProof = a2.toProof) :
    (Spec.Protocol.admit_attestation C st1 a1).toProof =
      (Spec.Protocol.admit_attestation C st2 a2).toProof := by
  obtain ⟨hv, hr, hcf⟩ := attestation_fields_of_toProof ha
  have hL : ∀ r, (st1.attestations r).map Spec.Attestation.toProof =
      (st2.attestations r).map Spec.Attestation.toProof :=
    fun r => congrArg (fun s => DecoupledConsensusModel.Protocol.Store.sg_votes s r) h
  have hs : st1.s = st2.s := congrArg DecoupledConsensusModel.Protocol.Store.s h
  have ht : st1.t = st2.t := congrArg DecoupledConsensusModel.Protocol.Store.t h
  have htsv : ∀ u, st1.timestamp_sg_vote (Spec.Protocol.SGVote.toSpec u) =
      st2.timestamp_sg_vote (Spec.Protocol.SGVote.toSpec u) :=
    fun u => congrFun (congrArg DecoupledConsensusModel.Protocol.Store.timestamp_sg_vote h) u
  -- the senders and confirmed roots of a round's attestations agree
  have hmem : ∀ r x, (∃ b ∈ st1.attestations r, b.val_index = a1.val_index ∧ b.confirmed = x) ↔
      (∃ b ∈ st2.attestations r, b.val_index = a2.val_index ∧ b.confirmed = x) := by
    intro r x
    constructor
    · rintro ⟨b, hb, hbv, hbx⟩
      have : b.toProof ∈ (st2.attestations r).map Spec.Attestation.toProof :=
        hL r ▸ List.mem_map_of_mem hb
      obtain ⟨b', hb', e⟩ := List.mem_map.1 this
      obtain ⟨e1, -, e3⟩ := attestation_fields_of_toProof e
      exact ⟨b', hb', by rw [e1, hbv, hv], by rw [e3, hbx]⟩
    · rintro ⟨b, hb, hbv, hbx⟩
      have : b.toProof ∈ (st1.attestations r).map Spec.Attestation.toProof :=
        (hL r).symm ▸ List.mem_map_of_mem hb
      obtain ⟨b', hb', e⟩ := List.mem_map.1 this
      obtain ⟨e1, -, e3⟩ := attestation_fields_of_toProof e
      exact ⟨b', hb', by rw [e1, hbv, ← hv], by rw [e3, hbx]⟩
  have hrv : Spec.Protocol.round_votes st1 a1 =
      Spec.Protocol.round_votes st2 a2 := by
    ext x
    simp only [Spec.Protocol.round_votes, Spec.Store.sg_pool,
      StoreSteps.getElem_fn, Finset.map', Finset.mem_image, Finset.mem_filter, List.mem_toFinset,
      hr]
    have := hmem a2.round x
    simpa [and_assoc] using this
  have hsg : Spec.Protocol.sgVote a1 = Spec.Protocol.sgVote a2 := by
    simp only [Spec.Protocol.sgVote, hv, hr, hcf]
  have key : ∀ (st : Spec.Store V) (A : Round → List (Spec.Attestation V))
      (τ : Spec.TimestampMap (Spec.Protocol.SGVote V)),
      ({ st with attestations := A, timestamp_sg_vote := τ } : Spec.Store V).toProof =
        { st.toProof with
          sg_votes := fun r => (A r).map Spec.Attestation.toProof
          timestamp_sg_vote := fun u => τ (Spec.Protocol.SGVote.toSpec u) } :=
    fun _ _ _ => rfl
  have hadm : Spec.Protocol.attestation_admissible C st1 a1 =
      Spec.Protocol.attestation_admissible C st2 a2 := by
    unfold Spec.Protocol.attestation_admissible
    rw [hs, hrv, hr, hcf]
  unfold Spec.Protocol.admit_attestation Spec.Protocol.add_attestation
  simp only [Id.run, pure, StoreSteps.getElem_fn]
  rw [hadm]
  split
  · rw [key st1, key st2, h]
    dsimp only
    congr 1
    · funext u
      simp only [Function.update_apply, hsg, ht]
      split_ifs
      · rfl
      · exact htsv u
    · funext r
      simp only [Function.update_apply, hr]
      split_ifs
      · rw [List.map_append, List.map_append, hL, List.map_singleton, List.map_singleton, ha]
      · exact hL r
  · exact h

/-- Admitting, one by one, two lists of attestations with the same images into stores with the same
    image under `Store.toProof` gives stores with the same image. -/
theorem toProof_foldl_admit_attestation_congr (C : Spec.Config) {γ : Type}
    (f g : γ → Spec.Attestation V) (rows : List γ)
    (hfg : ∀ x, (f x).toProof = (g x).toProof) :
    ∀ {st1 st2 : Spec.Store V}, st1.toProof = st2.toProof →
      (rows.foldl (fun s a => Spec.Protocol.admit_attestation C s (f a)) st1).toProof =
        (rows.foldl (fun s a => Spec.Protocol.admit_attestation C s (g a)) st2).toProof := by
  induction rows with
  | nil => intro st1 st2 h; exact h
  | cons x xs ih =>
    intro st1 st2 h
    simp only [List.foldl_cons]
    exact ih (toProof_admit_attestation_congr C h (hfg x))

/-- `(Attestation.toSpecNamed a).toProof = (Attestation.toSpec a.erase).toProof`. -/
theorem toProof_toSpecNamed_attestation (a : NamedAttestation V) :
    (Spec.Attestation.toSpecNamed a).toProof =
      (Spec.Attestation.toSpec a.erase).toProof := by
  rw [Spec.Attestation.toProof_toSpec, ← Spec.Attestation.toProofNamed_erase,
    Spec.Attestation.toProofNamed_toSpecNamed]

/-- The field `Execution_admit_row_core` of `HandlersFacts` at `Model.spec`: admitting a named
    attestation gives the same store part as admitting its erasure. -/
theorem spec_Execution_admit_row_core : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : (Model.spec (V := V)).NS) (a : NamedAttestation V),
    (Model.spec (V := V)).sameCore ((Model.spec (V := V)).admit_row hc st a).core
      ((Model.spec (V := V)).on_sg_vote hc st.core a.erase) :=
  fun _ _ a => toProof_admit_attestation_congr _ rfl (toProof_toSpecNamed_attestation a)

/-- The field `NamedAdmission_admit_row_core` of `HandlersFacts` at `Model.spec`: admitting a
    named attestation gives the same store part as admitting its erasure. -/
theorem spec_NamedAdmission_admit_row_core :
    ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.spec (V := V)).NS)
      (row : NamedAttestation V),
    (Model.spec (V := V)).sameCore ((Model.spec (V := V)).admit_row hc st row).core
      ((Model.spec (V := V)).on_sg_vote hc st.core row.erase) :=
  fun _ _ row => toProof_admit_attestation_congr _ rfl (toProof_toSpecNamed_attestation row)

/-- The value of the fold of the member `on_sg_vote` at `Model.spec` is the fold of
    `Member.on_sg_vote` at the value. -/
theorem foldl_on_sg_vote_val (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (rows : List (CombinedAttestation V)) :
    ∀ st : (Model.spec (V := V)).S,
      (rows.foldl ((Model.spec (V := V)).on_sg_vote hc) st).val =
        rows.foldl (Member.on_sg_vote hc) st.val := by
  induction rows with
  | nil => intro st; rfl
  | cons x xs ih => intro st; exact ih _

/-- The field `admit_rows_core` of `HandlersFacts` at `Model.spec`: admitting a list of named
    attestations gives the same store part as admitting their erasures one by one. -/
theorem spec_admit_rows_core : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : (Model.spec (V := V)).NS) (rows : List (NamedAttestation V)),
    (Model.spec (V := V)).sameCore ((Model.spec (V := V)).admit_rows hc st rows).core
      ((rows.map NamedAttestation.erase).foldl ((Model.spec (V := V)).on_sg_vote hc)
        st.core) := by
  intro hc st rows
  show (Member.admit_rows hc st.val rows).toProof =
    ((rows.map NamedAttestation.erase).foldl ((Model.spec (V := V)).on_sg_vote hc)
      st.core).val.toProof
  rw [foldl_on_sg_vote_val]
  unfold Member.admit_rows Member.on_sg_vote
  rw [StoreSteps.admit_attestations_foldl, List.foldl_map, List.foldl_map]
  exact toProof_foldl_admit_attestation_congr _ Spec.Attestation.toSpecNamed
    (fun a => Spec.Attestation.toSpec a.erase) rows
    toProof_toSpecNamed_attestation rfl

/-! ## The block handler `on_block_using` admits a new block -/

/-- When no tree block has the image `B`, the parent of `st.blockOfImage B` is
    `st.blockOfImage B.parent`. -/
theorem blockOfImage_parent_of_new (st : Spec.Store V) {B : Block V}
    (hnew : B ∉ st.T.image Spec.Block.toProof) :
    (st.blockOfImage B).parent = st.blockOfImage B.parent := by
  cases B with
  | genesis =>
    simp only [Spec.Store.blockOfImage, Spec.Store.blockOfImageIn,
      DecoupledConsensusModel.Block.parent, Spec.Block.parent]
  | node p s r votes support ats proposer =>
    simp only [Spec.Store.blockOfImage, DecoupledConsensusModel.Block.parent]
    cases hpk : Spec.pickUnique? st.T
        (fun B' => decide (B'.toProof = Block.node p s r votes support ats proposer)) with
    | none =>
      simp only [Spec.Store.blockOfImageIn, hpk, Option.getD, Spec.Block.parent]
    | some B' =>
      obtain ⟨hB', himg⟩ := Spec.Store.blockWithImage?_eq_some st hpk
      exact absurd (himg ▸ Finset.mem_image_of_mem _ hB') hnew

/-- The field `mem_T_on_block_using` of `HandlersFacts` at `Model.spec`: a block `B` not in the
    tree, of a slot at most the store's, whose parent is in the tree, whose slot is greater than its
    parent's, of which the finalized block is an ancestor, proposed by its slot's proposer, and
    whose root no other tree block has, is in the tree after `on_block_using`. -/
theorem spec_mem_T_on_block_using : ∀ (E : Env V) (st : (Model.spec (V := V)).S)
    (B : Block V) (build : (Model.spec (V := V)).CS → (Model.spec (V := V)).CS)
    (hslot : B.slot ≤ st.s) (hnew : B ∉ st.T) (hpar : B.parent ∈ st.T)
    (hfin : Block.preceq st.F B = true) (hprop : B.proposer? = some (E.proposer B.slot))
    (hpslot : B.parent.slot < B.slot)
    -- no block of `st`'s tree has `B`'s root unless it is `B`
    (hroot : (Model.spec (V := V)).rootFresh st B),
    B ∈ ((Model.spec (V := V)).on_block_using E st B build).T := by
  intro E st B build hslot hnew hpar hfin hprop hpslot hroot
  have hroot : ∀ C ∈ st.T, C.root = B.root → C = B := hroot
  obtain ⟨⟨_, _, _⟩, hd, hpc, hF⟩ := st.property
  have hnew' : B ∉ st.val.T.image Spec.Block.toProof := hnew
  set X := st.val.blockOfImage B with hXdef
  have hXB : X.toProof = B := Spec.Store.toProof_blockOfImage _ _
  have hXT : X ∉ st.val.T := fun h => hnew' (hXB ▸ Finset.mem_image_of_mem _ h)
  obtain ⟨Y, hY, hYp⟩ := Finset.mem_image.1 (show B.parent ∈ st.val.T.image _ from hpar)
  have hXpar : X.parent = Y := by
    rw [hXdef, blockOfImage_parent_of_new st.val hnew', ← hYp,
      Spec.Store.blockOfImage_toProof_of_mem st.val hd hY]
  have hnh : ¬ RootHeldByOther st.val.T X := by
    rintro ⟨B', hB', hne, hr⟩
    have e := hroot B'.toProof (Finset.mem_image_of_mem _ hB') (by
      rw [Spec.Block.toProof_root, hr, ← Spec.Block.toProof_root, hXB])
    exact hnew' (e ▸ Finset.mem_image_of_mem _ hB')
  have hslotX : X.slot = B.slot := by rw [← hXB, SubtypeEqualities.toProof_slot]
  have hpslotX : X.parent.slot = B.parent.slot := by
    rw [hXpar, ← SubtypeEqualities.toProof_slot, hYp]
  have hpropX : X.proposer? = B.proposer? := by rw [← hXB, SubtypeEqualities.toProof_proposer?]
  have hancX : st.val.F.ancestorEq X = true := by
    have hpc' : ∀ Z ∈ st.val.T ∪ {X}, Z.parent ∈ st.val.T ∪ {X} := by
      intro Z hZ
      rcases Finset.mem_union.1 hZ with hZ | hZ
      · exact Finset.mem_union_left _ (hpc Z hZ)
      · rw [Finset.mem_singleton.1 hZ, hXpar]; exact Finset.mem_union_left _ hY
    rw [← Spec.Block.toProof_preceq_of_injOn (st.val.T ∪ {X}) (SubtypeEqualities.injOn_insert hd hnh)
      hpc' (Finset.mem_union_left _ hF) (Finset.mem_union_right _ (Finset.mem_singleton_self X)),
      hXB]
    exact hfin
  show B ∈ (OkMember.on_block_using E st B build).val.toProof.T
  rw [OkMember.on_block_using_val_of_not_held hnh]
  show B ∈ (Handlers.onBlockUsing (Spec.Provisional.toSpec E) st.val X build).toProof.T
  have h1' : ¬ st.val.s < X.slot := by rw [hslotX]; exact Nat.not_lt.2 hslot
  have hpar' : X.parent ∈ st.val.T := hXpar ▸ hY
  have hprop' : X.proposer? = (Spec.Provisional.toSpec E).proposer X.slot := by
    rw [hpropX, hprop, hslotX]
    rfl
  have hps' : X.parent.slot < X.slot := by rw [hpslotX, hslotX]; exact hpslot
  have hTkeep : ∀ S0 : Spec.Store V,
      (Spec.Protocol.update_finality (X.gf_votes.foldl
        (Spec.Protocol.on_goldfish_vote_checked (Spec.Provisional.toSpec E))
        S0) X).T = S0.T := by
    intro S0
    obtain ⟨x, y, e⟩ := SubtypeEqualities.foldl_checked_shape
      (Spec.Provisional.toSpec E) X.gf_votes S0
    rw [Handlers.update_finality_eq, e]
    obtain ⟨a, b, c, d, hW⟩ := OkStore.updateFinalityWith_shape
      ({ S0 with gf_votes := x, timestamp_vote := y } : Spec.Store V)
      ((({ S0 with gf_votes := x, timestamp_vote := y } : Spec.Store V)).σ X)
    rw [hW]
  unfold Handlers.onBlockUsing
  simp only [Id.run, h1', hXT, hpar', hancX, hprop', hps', decide_false,
    Bool.or_false, not_true_eq_false, if_false, ne_eq, Bool.false_eq_true, Bool.not_false,
    List.forIn_pure_yield_eq_foldl]
  rw [Spec.Store.toProof_T]
  simp only [pure_bind]
  rw [← hXB]
  refine Finset.mem_image_of_mem _ ?_
  show X ∈ (Spec.Protocol.update_finality (X.gf_votes.foldl
    (Spec.Protocol.on_goldfish_vote_checked (Spec.Provisional.toSpec E)) _) X).T
  rw [hTkeep]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self X)

end SpecRecord.HandlersFacts

namespace SpecRecord.HandlersRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (ChainState HeightConfig HealConfig HeightId)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- A tick among the first `i` events of `rho`, whose times are all at most `bound`, has time at
    most `bound`. -/
theorem tick_mem_take_time (rho : Record.Run V) (i : Nat) (bound : Time)
    (hbefore : ∀ j (e : Record.Event V), j < i → rho.events[j]? = some e → e.time ≤ bound) (v : V)
    (t : Time) (hm : Record.Event.tick v t ∈ rho.events.take i) : t ≤ bound := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm
  rw [List.getElem?_take] at hj
  split_ifs at hj with hji
  · exact hbefore j _ hji hj

/-- The SG vote `Model.specBase` reads off `a'.toProofNamed.erase` is the image of
    `Protocol.sgVote a'`. -/
theorem sgVote_toProofNamed_erase_base (a' : Spec.Attestation V) :
    (Model.specBase (V := V)).sgVote a'.toProofNamed.erase =
      (Spec.Protocol.sgVote a').toProof := by
  show (Spec.Protocol.sgVote
    (Spec.Attestation.toSpec a'.toProofNamed.erase)).toProof = _
  rw [Spec.Attestation.toProofNamed_erase]
  congr 1
  cases a' with
  | mk v r c hp fp => cases c <;> rfl

/-- The stamp `st` holds for the SG vote of `a'.toProofNamed.erase` is its stamp of `a'`'s SG vote. -/
theorem stamp_sgVote_toProofNamed_erase (st : (Model.specBase (V := V)).S)
    (a' : Spec.Attestation V) :
    st.timestamp_sg_vote ((Model.specBase (V := V)).sgVote a'.toProofNamed.erase) =
      Spec.Store.timestamp_sg_vote st (Spec.Protocol.sgVote a') := by
  rw [sgVote_toProofNamed_erase_base]
  show Spec.Store.timestamp_sg_vote st (Spec.Protocol.SGVote.toSpec
    (Spec.Protocol.sgVote a').toProof) = _
  rw [Spec.Protocol.SGVote.toSpec_toProof]

/-- `a'.toProofNamed` is among the named attestations of round `r` of `st` exactly when `a'` is in
    `st.sg_pool r`. -/
theorem mem_sg_rows_iff (st : (Model.specBase (V := V)).NS) (r : Round)
    (a' : Spec.Attestation V) :
    a'.toProofNamed ∈ st.sg_rows r ↔ a' ∈ Spec.Store.sg_pool st r := by
  rw [StoreSteps.mem_sg_pool_iff]
  show a'.toProofNamed ∈ (st.attestations r).map Spec.Attestation.toProofNamed ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, he⟩
    rw [Spec.Attestation.toProofNamed_injective he] at hb
    exact hb
  · intro h
    exact ⟨a', h, rfl⟩

/-- The field `genesis_mem_stateBefore_zero` of `HandlersRunFacts` at `Model.spec`: in every
    world before the first event of `rho`, validator `v` holds the genesis block. -/
theorem spec_genesis_mem_stateBefore_zero : ∀ (S : Setup V) (rho : Record.Run V) (v : V)
    (w : V → (Model.spec (V := V)).N)
    (hw : w ∈ stateBeforeOf (Model.spec (V := V)) S rho 0),
    (NamedBlock.genesis : NamedBlock V) ∈ (w v).st.bodies := by
  intro S rho v w hw
  simp only [stateBeforeOf, List.take_zero, List.foldlM_nil, Set.pure_def,
    Set.mem_singleton_iff] at hw
  subst hw
  show (NamedBlock.genesis : NamedBlock V) ∈
    (Spec.Store.init : Spec.Store V).T.map Spec.Block.toProofNamedEmb
  exact Finset.mem_map_of_mem _ (Finset.mem_singleton_self _)

/-- The field `stateBefore_h_j_mono` of `HandlersRunFacts` at `Model.spec`. -/
theorem spec_stateBefore_h_j_mono : ∀ (S : Setup V) (rho : Record.Run V) (v : V) {m n : Nat}
    (hmn : m ≤ n),
    ∀ w₁ ∈ stateBeforeOf (Model.spec (V := V)) S rho m,
    ∀ w₂ ∈ ((rho.events.drop m).take (n - m)).foldlM (worldStepOf (Model.spec (V := V)) S) w₁,
      (w₁ v).st.core.h_j ≤ (w₂ v).st.core.h_j := by
  intro S rho v m n _ w₁ _ w₂ hw₂
  exact (fold_relation_ok S (fun _ => True)
    (fun a b => a.h_j ≤ b.h_j)
    (fun _ => le_refl _) (fun _ _ _ h1 h2 => le_trans h1 h2) _
    (fun p t _ n out hout _ =>
      ⟨trivial, StoreSteps.reach_h_j_le (specBase_tick_reach S p n t out hout)⟩)
    (fun n o n' h _ => ⟨trivial, StoreSteps.reach_h_j_le (specBase_process_reach S n n' o h 0)⟩)
    w₁ (fun _ => trivial) w₂ hw₂ v).2

/-- The stamp a store of `Model.spec` holds for the SG vote of `a'.toProofNamed.erase` is the
    stamp its value holds for `a'`'s SG vote. -/
theorem stamp_sgVote_toProofNamed_erase_ok (st : (Model.spec (V := V)).S)
    (a' : Spec.Attestation V) :
    st.timestamp_sg_vote ((Model.spec (V := V)).sgVote a'.toProofNamed.erase) =
      Spec.Store.timestamp_sg_vote st.val (Spec.Protocol.sgVote a') :=
  stamp_sgVote_toProofNamed_erase st.val a'

/-- Every world the events `es` lead to from the initial world at `Model.spec` holds, at every
    validator, a store whose attestations of each round are of that round. -/
theorem rows_fold_ok (S : Setup V) (es : List (Record.Event V)) :
    ∀ w ∈ es.foldlM (worldStepOf (Model.spec (V := V)) S)
        (fun u => (Model.spec (V := V)).initial S u),
      ∀ u, StoreSteps.RowsErasuresHeld (Spec.NodeState.st (w u).val) := fun w hw u =>
  (fold_relation_ok S StoreSteps.RowsErasuresHeld (fun _ _ => True) (fun _ => trivial)
    (fun _ _ _ _ _ => trivial) es
    (fun p t _ n out hout hI =>
      ⟨(StoreSteps.reach_rows (specBase_tick_reach S p n t out hout) hI).1, trivial⟩)
    (fun n o n' h hI =>
      ⟨(StoreSteps.reach_rows (specBase_process_reach S n n' o h 0) hI).1, trivial⟩)
    (fun u => (Model.spec (V := V)).initial S u) (fun _ => StoreSteps.rowsErasuresHeld_init)
    w hw u).1

/-- The field `stateBefore_sg_row_stamp_mono` of `HandlersRunFacts` at `Model.spec`. -/
theorem spec_stateBefore_sg_row_stamp_mono : ∀ (S : Setup V) (rho : Record.Run V) (reader : V)
    {i j : Nat} (hij : i ≤ j) {a : NamedAttestation V},
    ∀ w₁ ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
    a ∈ (w₁ reader).st.sg_rows a.round →
    ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (worldStepOf (Model.spec (V := V)) S) w₁,
    a ∈ (w₂ reader).st.sg_rows a.round ∧
      (w₂ reader).st.core.timestamp_sg_vote ((Model.spec (V := V)).sgVote a.erase) =
        (w₁ reader).st.core.timestamp_sg_vote ((Model.spec (V := V)).sgVote a.erase) := by
  intro S rho reader i j _ a w₁ hw₁ ha w₂ hw₂
  have hI₁ := rows_fold_ok S (rho.events.take i) w₁ hw₁
  have hR := (fold_relation_ok S StoreSteps.RowsErasuresHeld StoreSteps.KeepsRows
    StoreSteps.keepsRows_refl StoreSteps.keepsRows_trans _
    (fun p t _ n out hout hI => StoreSteps.reach_rows (specBase_tick_reach S p n t out hout) hI)
    (fun n o n' h hI => StoreSteps.reach_rows (specBase_process_reach S n n' o h 0) hI)
    w₁ hI₁ w₂ hw₂ reader).2
  obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
  have ha' : a' ∈ (Spec.NodeState.st (w₁ reader).val).sg_pool a'.round :=
    (mem_sg_rows_iff (w₁ reader).val.st _ a').1 ha
  refine ⟨(mem_sg_rows_iff (w₂ reader).val.st _ a').2 (hR.1 _ ha'), ?_⟩
  rw [stamp_sgVote_toProofNamed_erase_ok, stamp_sgVote_toProofNamed_erase_ok]
  exact hR.2 _ _ ha'

/-- The field `sgArrival_prefix_data` of `HandlersRunFacts` at `Model.spec`. -/
theorem spec_sgArrival_prefix_data : ∀ (S : Setup V) (rho : Record.Run V) (bound : Time)
    (hzero : 0 ≤ bound) (i : Nat)
    (hbefore : ∀ j (e : Record.Event V), j < i → rho.events[j]? = some e → e.time ≤ bound)
    (reader : V),
    ∀ w ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
      (w reader).st.core.t ≤ bound ∧
        ∀ k (a : NamedAttestation V), a ∈ (w reader).st.sg_rows k →
          a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
            (w reader).st.core.timestamp_sg_vote ((Model.spec (V := V)).sgVote a.erase) =
              some (stamp : Stamp) := by
  intro S rho bound hzero i hbefore reader w hw
  have hI := (fold_relation_ok S
    (fun st => StoreSteps.RowsErasuresHeld st ∧ StoreSteps.StampsBounded bound st)
    (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ => trivial) (rho.events.take i)
    (fun p t hm n out hout hI =>
      ⟨StoreSteps.reach_bounded bound (tick_mem_take_time rho i bound hbefore p t hm)
        (specBase_tick_reach S p n t out hout) hI.1 hI.2, trivial⟩)
    (fun n o n' h hI =>
      ⟨StoreSteps.reach_bounded bound (le_refl bound) (specBase_process_reach S n n' o h bound)
        hI.1 hI.2, trivial⟩)
    (fun u => (Model.spec (V := V)).initial S u)
    (fun _ => ⟨StoreSteps.rowsErasuresHeld_init, StoreSteps.stampsBounded_init bound hzero⟩)
    w hw reader).1
  refine ⟨hI.2.1, fun k a ha => ?_⟩
  obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
  have ha' : a' ∈ (Spec.NodeState.st (w reader).val).sg_pool k :=
    (mem_sg_rows_iff (w reader).val.st _ a').1 ha
  refine ⟨hI.1 k a' ha', ?_⟩
  obtain ⟨s, hs, hst⟩ := hI.2.2 k a' ha'
  refine ⟨s, hs, ?_⟩
  rw [stamp_sgVote_toProofNamed_erase_ok]
  exact hst

end SpecRecord.HandlersRunFacts

/-! ## The chain-state invariants along a run -/

namespace SpecRecord.HandlersRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (ChainState HeightConfig HealConfig HeightId)
open SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ### The steps of a tick or a receipt -/

/-- `KeepsBlocks st st'`: every block of `st`'s tree is in `st'`'s tree with the same stamp. -/
def KeepsBlocks (st st' : Spec.Store V) : Prop :=
  ∀ X ∈ st.T, X ∈ st'.T ∧ st'.timestamp_block X = st.timestamp_block X

/-- Every step keeps the blocks of the tree and their stamps. -/
theorem keepsBlocks_step {C : Spec.Config} {P : Spec.Provisional V} {τ : Time}
    {a b : Spec.Store V} (hs : StoreSteps.StoreStep C P τ a b) : KeepsBlocks a b := by
  cases hs with
  | grades g => exact fun X hX => ⟨hX, rfl⟩
  | clock => exact fun X hX => ⟨hX, rfl⟩
  | confirm x y z => exact fun X hX => ⟨hX, rfl⟩
  | vote u =>
    obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes P a u
    rw [e]
    exact fun X hX => ⟨hX, rfl⟩
  | attest row =>
    obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes C a row
    rw [e]
    exact fun X hX => ⟨hX, rfl⟩
  | block B =>
    rw [Handlers.on_block_eq]
    split_ifs with hadm
    · obtain ⟨⟨hBT, -⟩, -⟩ := (SubtypeEqualities.block_admissible_iff C P a B).mp hadm
      have hcore : Handlers.admitBlockCore C P a B = Handlers.blockCore C P a B := if_pos hadm
      rw [hcore]
      obtain ⟨x, y, e⟩ :=
        SubtypeEqualities.admit_attestations_shape C (Handlers.blockCore C P a B) B.attestations
      rw [e]
      intro X hX
      have hXB : X ≠ B := fun h => hBT (h ▸ hX)
      refine ⟨?_, ?_⟩
      · show X ∈ (Handlers.blockCore C P a B).T
        rw [SubtypeEqualities.blockCore_T]
        exact Finset.mem_union_left _ hX
      · show (Handlers.blockCore C P a B).timestamp_block X = a.timestamp_block X
        rw [SubtypeEqualities.blockCore_timestamp_block]
        exact Function.update_of_ne hXB _ _
    · exact fun X hX => ⟨hX, rfl⟩

/-- `KeepsBlocks` is reflexive. -/
theorem keepsBlocks_refl (st : Spec.Store V) : KeepsBlocks st st :=
  fun _ hX => ⟨hX, rfl⟩

/-- `KeepsBlocks` is transitive. -/
theorem keepsBlocks_trans (a b c : Spec.Store V) (h1 : KeepsBlocks a b)
    (h2 : KeepsBlocks b c) : KeepsBlocks a c := fun X hX =>
  ⟨(h2 X (h1 X hX).1).1, (h2 X (h1 X hX).1).2.trans (h1 X hX).2⟩

/-- Distinct roots pass to a subset of the tree. -/
theorem distinctRoots_of_subset {T T' : Finset (Spec.Block V)} (h : DistinctRoots T')
    (hs : T ⊆ T') : DistinctRoots T :=
  fun B hB B' hB' e => h B (hs hB) B' (hs hB') e

/-- If every step into a store with distinct roots keeps `Q`, then `Q` holds along every sequence of
    steps ending at a store with distinct roots. -/
theorem reach_induction_ok {C : Spec.Config} {P : Spec.Provisional V}
    {τ : Time} (Q : Spec.Store V → Prop)
    (hstep : ∀ a b, StoreSteps.StoreStep C P τ a b → DistinctRoots b.T → Q a → Q b)
    {st st' : Spec.Store V} (h : StoreSteps.StoreReach C P τ st st')
    (hd : DistinctRoots st'.T) (hq : Q st) : Q st' := by
  induction h with
  | refl => exact hq
  | tail _ hs ih =>
      exact hstep _ _ hs hd
        (ih (distinctRoots_of_subset hd (fun X hX => (keepsBlocks_step hs X hX).1)))

/-- Every step into a store with distinct roots keeps `StoreOk` and `RunStoreInv`. -/
theorem base_step {C : Spec.Config} {P : Spec.Provisional V} {τ : Time}
    {a b : Spec.Store V} (hs : StoreSteps.StoreStep C P τ a b) (hd : DistinctRoots b.T)
    (h : StoreOk a ∧ SubtypeEqualities.RunStoreInv a) :
    StoreOk b ∧ SubtypeEqualities.RunStoreInv b := by
  cases hs with
  | grades g => exact h
  | clock => exact h
  | confirm x y z => exact h
  | vote u =>
    refine ⟨OkStore.on_goldfish_vote_checked P h.1 u, ?_⟩
    obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes P a u
    rw [e]
    exact h.2
  | attest row =>
    refine ⟨OkStore.admit_attestation C h.1 row, ?_⟩
    obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes C a row
    rw [e]
    exact h.2
  | block B =>
    rcases SubtypeEqualities.on_block_cases_of_ok C P hd with e | hroot
    · rw [e]
      exact h
    · exact ⟨OkStore.on_block C P h.1 hroot, SubtypeEqualities.runStoreInv_on_block C P h.2 B⟩

/-- At a store with `StoreOk` and `RunStoreInv`, receiving a block whose root no other tree block
    has, read through the named image, is the named block receipt at the named image. -/
theorem image_on_block_step (S : Setup V) {st : Spec.Store V} (hok : StoreOk st)
    (hinv : SubtypeEqualities.RunStoreInv st) (B : Spec.Block V)
    (hroot : ¬ RootHeldByOther st.T B) :
    (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st B).toProofNamed =
      Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st.toProofNamed
        B.toProofNamed := by
  have h := SubtypeEqualities.image_on_block_with_of_not_held .alsoCarried S.E S.hc S.cfg hok hinv
    B.toProofNamed (by rwa [Spec.Block.toSpecNamed_toProofNamed])
  rw [Member.on_block_with, Spec.Block.toSpecNamed_toProofNamed] at h
  exact h

/-! ### Folding events at the node subtype -/

/-- Let `Q` be a property of stores kept by every tick and every receipt of `Model.spec`, and
    `R` a reflexive, transitive relation that each of them satisfies. If `Q` holds of every store of
    `w₁`, then in every world the events lead to from `w₁`, `Q` holds of every store and `R` relates
    each validator's store in `w₁` to its store there. -/
theorem fold_relation_sub (S : Setup V) (Q : Spec.Store V → Prop)
    (R : Spec.Store V → Spec.Store V → Prop)
    (hrefl : ∀ st, R st st) (htrans : ∀ a b c, R a b → R b c → R a c)
    (es : List (Record.Event V))
    (htick : ∀ v t, Record.Event.tick v t ∈ es → ∀ (n : (Model.spec (V := V)).N)
      (out : (Model.spec (V := V)).N × List (NamedObject V)),
      (Model.spec (V := V)).tick S v n t ⇢ out → Q n.val.st →
        Q out.1.val.st ∧ R n.val.st out.1.val.st)
    (hproc : ∀ (n : (Model.spec (V := V)).N) o (n' : (Model.spec (V := V)).N),
      (Model.spec (V := V)).process S n o ⇢ n' → Q n.val.st → Q n'.val.st ∧ R n.val.st n'.val.st)
    (w₁ : V → (Model.spec (V := V)).N) (hI : ∀ v, Q (w₁ v).val.st) :
    ∀ w₂ ∈ es.foldlM (worldStepOf (Model.spec (V := V)) S) w₁,
      ∀ v, Q (w₂ v).val.st ∧ R (w₁ v).val.st (w₂ v).val.st := by
  induction es generalizing w₁ with
  | nil =>
    intro w₂ hw v
    have hw' : w₂ = w₁ := hw
    subst hw'
    exact ⟨hI v, hrefl _⟩
  | cons e es ih =>
    intro w₂ hw v
    rw [List.foldlM_cons, Set.bind_def] at hw
    obtain ⟨w', hw', hw₂⟩ := Set.mem_iUnion₂.mp hw
    have hstep : ∀ u, Q (w' u).val.st ∧ R (w₁ u).val.st (w' u).val.st := by
      cases e with
      | wake p t =>
        simp only [worldStepOf, Set.mem_singleton_iff] at hw'
        subst hw'
        intro u
        by_cases hu : u = p
        · subst hu
          simp only [Function.update_self, spec_wake_st]
          exact ⟨hI u, hrefl _⟩
        · simp only [ne_eq, hu, not_false_eq_true, Function.update_of_ne]
          exact ⟨hI u, hrefl _⟩
      | tick p t =>
        simp only [worldStepOf, Set.mem_setOf_eq] at hw'
        rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
        · intro u
          by_cases hu : u = p
          · subst hu
            simp only [Function.update_self]
            exact htick u t (List.mem_cons_self) (w₁ u) out hout (hI u)
          · simp only [ne_eq, hu, not_false_eq_true, Function.update_of_ne]
            exact ⟨hI u, hrefl _⟩
        · exact fun u => ⟨hI u, hrefl _⟩
      | deliver p o t =>
        simp only [worldStepOf, Set.mem_setOf_eq] at hw'
        rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
        · intro u
          by_cases hu : u = p
          · subst hu
            simp only [Function.update_self]
            exact hproc (w₁ u) o n' hn' (hI u)
          · simp only [ne_eq, hu, not_false_eq_true, Function.update_of_ne]
            exact ⟨hI u, hrefl _⟩
        · exact fun u => ⟨hI u, hrefl _⟩
    have := ih (fun v t hm => htick v t (List.mem_cons_of_mem _ hm)) w' (fun u => (hstep u).1) w₂ hw₂ v
    exact ⟨this.1, htrans _ _ _ (hstep v).2 this.2⟩

/-- A property `I` that every step into a store with distinct roots keeps, together with `StoreOk`
    and `RunStoreInv`, holds with them at every validator of every world the events lead to from the
    initial world at `Model.spec`. -/
theorem inv_fold (S : Setup V) (I : Spec.Store V → Prop)
    (hstep : ∀ τ (a b : Spec.Store V),
      StoreSteps.StoreStep (Setup.toSpec S).C (Setup.toSpec S).P τ a b → DistinctRoots b.T →
        StoreOk a ∧ SubtypeEqualities.RunStoreInv a ∧ I a →
          StoreOk b ∧ SubtypeEqualities.RunStoreInv b ∧ I b)
    (hinit : I (Spec.Store.init : Spec.Store V))
    (es : List (Record.Event V)) :
    ∀ w ∈ es.foldlM (worldStepOf (Model.spec (V := V)) S)
        (fun u => (Model.spec (V := V)).initial S u),
      ∀ v, I (w v).val.st := fun w hw v =>
  ((fold_relation_sub S (fun st => StoreOk st ∧ SubtypeEqualities.RunStoreInv st ∧ I st)
    (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ => trivial) es
    (fun p t _ n out hout hI =>
      ⟨reach_induction_ok _ (fun a b hs hd hq => hstep t a b hs hd hq)
        (spec_tick_reach S p n t out hout) out.1.property.2.1 hI, trivial⟩)
    (fun n o n' h hI =>
      ⟨reach_induction_ok _ (fun a b hs hd hq => hstep 0 a b hs hd hq)
        (spec_process_reach S n n' o h 0) n'.property.2.1 hI, trivial⟩)
    (fun u => (Model.spec (V := V)).initial S u)
    (fun _ => ⟨OkStore.init, SubtypeEqualities.runStoreInv_init, hinit⟩) w hw v).1).2.2

/-! ### The justification bound -/

/-- `JustInv st`: the chain states of `st.toProof` satisfy `ChainStatesOk`, and `h_j < h_max`. -/
def JustInv (st : Spec.Store V) : Prop :=
  DecoupledConsensusModel.Proofs.ChainStatesOk st.toProof.σ ∧ st.toProof.h_j < st.toProof.h_max

/-- Every step into a store with distinct roots keeps `JustInv`, given `StoreOk` and `RunStoreInv`. -/
theorem justInv_step (S : Setup V) (τ : Time) (a b : Spec.Store V)
    (hs : StoreSteps.StoreStep (Setup.toSpec S).C (Setup.toSpec S).P τ a b)
    (hd : DistinctRoots b.T) (h : StoreOk a ∧ SubtypeEqualities.RunStoreInv a ∧ JustInv a) :
    StoreOk b ∧ SubtypeEqualities.RunStoreInv b ∧ JustInv b := by
  obtain ⟨hb1, hb2⟩ := base_step hs hd ⟨h.1, h.2.1⟩
  refine ⟨hb1, hb2, ?_⟩
  have hj := h.2.2
  cases hs with
  | grades g => exact hj
  | clock => exact hj
  | confirm x y z => exact hj
  | vote u =>
    have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationBound
      DecoupledConsensusModel.Proofs.NamedJustificationBound.gf_just) S.E a.toProof u.toProof hj
    rw [toProof_on_goldfish_vote_checked] at h1
    exact h1
  | attest row =>
    have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationBound
      DecoupledConsensusModel.Proofs.NamedJustificationBound.row_just) S.hc a.toProofNamed
      row.toProofNamed hj
    rw [toProof_admit_row S.E S.hc S.cfg] at h1
    exact h1
  | block B =>
    rcases SubtypeEqualities.on_block_cases_of_ok _ _ hd with e | hroot
    · rw [e]
      exact hj
    · have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationBound
        DecoupledConsensusModel.Proofs.NamedJustificationBound.block_just) S a.toProofNamed
        B.toProofNamed hj
      rw [← image_on_block_step S h.1 h.2.1 B hroot] at h1
      exact h1

/-- The initial store has `JustInv`. -/
theorem justInv_init : JustInv (Spec.Store.init : Spec.Store V) := by
  refine ⟨?_, ?_⟩
  · have e : (Spec.Store.init : Spec.Store V).toProof.σ =
        fun _ => (DecoupledConsensusModel.Protocol.ChainState.initial : ChainState V) := by
      funext C
      exact toProof_cs_initial.symm
    rw [e]
    exact DecoupledConsensusModel.Proofs.chainStatesOk_const_initial
  · show (0 : Nat) < 1
    exact Nat.one_pos

/-- The field `justificationBelowMax_stateBefore` of `HandlersRunFacts` at `Model.spec`: in
    every world the run `rho` can reach before its `i`-th event, validator `v`'s store has
    `h_j < h_max`. -/
theorem spec_justificationBelowMax_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat)
    (v : V), ∀ w₁ ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
      (w₁ v).st.core.h_j < (w₁ v).st.core.h_max := by
  intro S rho i v w₁ hw₁
  exact (inv_fold S JustInv (justInv_step S) justInv_init (rho.events.take i) w₁ hw₁ v).2

/-- The field `justificationBelowMax_stateBeforeTime` of `HandlersRunFacts` at `Model.spec`: in
    every world the events of `rho` with time less than `t` can reach from the initial world,
    validator `v`'s store has `h_j < h_max`. -/
theorem spec_justificationBelowMax_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V)
    (t : Time) (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM
        (worldStepOf (Model.spec (V := V)) S) (fun u => (Model.spec (V := V)).initial S u),
      (w₁ v).st.core.h_j < (w₁ v).st.core.h_max := by
  intro S rho t v w₁ hw₁
  exact (inv_fold S JustInv (justInv_step S) justInv_init _ w₁ hw₁ v).2

/-! ### No held named block offers a higher justification -/

/-- `(Member.derive_named E cfg B).toProof = Protocol.derive_named E cfg B`. -/
theorem image_derive_named (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (Member.derive_named E cfg B).toProof = Protocol.derive_named E cfg B := by
  induction B with
  | genesis =>
    rw [Protocol.derive_named.eq_1, Member.derive_named.eq_1]
    exact SpecRecord.toProof_cs_initial.symm
  | node p s r gv gsv rows i ih =>
    rw [Proofs.BlockProcessingDefaults.derive_named_node, ← ih]
    have h := toProof_named_transition E SpecRecord.unreadHealConfig cfg
      (Member.derive_named E cfg p)
      (Spec.Block.toSpecNamed (NamedBlock.node p s r gv gsv rows i))
    rw [Spec.Block.toProofNamed_toSpecNamed] at h
    exact h.symm

/-- `RootsInv S st`: the named image of `st` satisfies `NamedStoreRoots.Invariant` (it is coherent,
    and `F` and `J` are in its tree). -/
def RootsInv (S : Setup V) (st : Spec.Store V) : Prop :=
  Proofs.NamedStoreRoots.Invariant S.E S.cfg st.toProofNamed

/-- `NoHighInv S st`: at the named image of `st`, `F ⪯ J`, `J` is carried by a held named block at
    height `h_j`, and no held named block derives a justified height greater than `h_j`; and
    `RootsInv S st`. -/
def NoHighInv (S : Setup V) (st : Spec.Store V) : Prop :=
  (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationBound
    DecoupledConsensusModel.Proofs.NamedJustificationBound.Bundle) S st.toProofNamed ∧ RootsInv S st

/-- Every step into a store with distinct roots keeps `NoHighInv`, given `StoreOk` and
    `RunStoreInv`. -/
theorem noHighInv_step (S : Setup V) (τ : Time) (a b : Spec.Store V)
    (hs : StoreSteps.StoreStep (Setup.toSpec S).C (Setup.toSpec S).P τ a b)
    (hd : DistinctRoots b.T) (h : StoreOk a ∧ SubtypeEqualities.RunStoreInv a ∧ NoHighInv S a) :
    StoreOk b ∧ SubtypeEqualities.RunStoreInv b ∧ NoHighInv S b := by
  obtain ⟨hb1, hb2⟩ := base_step hs hd ⟨h.1, h.2.1⟩
  refine ⟨hb1, hb2, ?_⟩
  have hj := h.2.2
  cases hs with
  | grades g => exact hj
  | clock => exact hj
  | confirm x y z => exact hj
  | vote u =>
    obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes (Setup.toSpec S).P a u
    rw [e]
    exact hj
  | attest row =>
    have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationBound
      DecoupledConsensusModel.Proofs.NamedJustificationBound.bundle_row) S a.toProofNamed
      row.toProofNamed hj.1
    have h2 := Proofs.NamedStoreRoots.invariant_admit_row S.E S.hc S.cfg a.toProofNamed
      row.toProofNamed hj.2
    rw [toProof_admit_row S.E S.hc S.cfg] at h1 h2
    exact ⟨h1, h2⟩
  | block B =>
    rcases SubtypeEqualities.on_block_cases_of_ok _ _ hd with e | hroot
    · rw [e]
      exact hj
    · have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationBound
        DecoupledConsensusModel.Proofs.NamedJustificationBound.bundle_block_with) S a.toProofNamed
        B.toProofNamed hj.2.1 hj.2.2.1 hj.1
      have h2 := Proofs.NamedStoreRoots.invariant_on_block_with .alsoCarried S.E S.hc S.cfg
        a.toProofNamed B.toProofNamed hj.2
      rw [← image_on_block_step S h.1 h.2.1 B hroot] at h1 h2
      exact ⟨h1, h2⟩

/-- The initial store has `NoHighInv`. -/
theorem noHighInv_init (S : Setup V) (v : V) :
    NoHighInv S (Spec.Store.init : Spec.Store V) := by
  have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationBound
    DecoupledConsensusModel.Proofs.NamedJustificationBound.initial_bundle) S v
  rw [show (NamedWorld.init v : NamedNodeState V).st = Protocol.NamedStore.initial from
    Proofs.ModelProperties.initial_st] at h1
  have h2 := Proofs.NamedStoreRoots.invariant_initial S.E S.cfg (V := V)
  unfold NoHighInv RootsInv
  rw [← toProof_ns_initial]
  exact ⟨h1, h2⟩

/-- From `NoHighInv`, no named block the node holds derives a justified height greater than its
    store's. -/
theorem noHigh_of_inv (S : Setup V) (n : (Model.spec (V := V)).N)
    (h : NoHighInv S n.val.st) :
    ∀ B ∈ n.st.bodies,
      ((Model.spec (V := V)).derive_named S.E S.cfg B).h_j ≤ n.st.core.h_j := by
  intro B hB
  have h3 := h.1.2.2 B hB
  show (Member.derive_named S.E S.cfg B).toProof.h_j ≤ _
  rw [image_derive_named]
  exact h3

/-- The field `noHighJustifications_stateBefore` of `HandlersRunFacts` at `Model.spec`: in
    every world the run `rho` can reach before its `i`-th event, no named block validator `v` holds
    derives a justified height greater than its store's. -/
theorem spec_noHighJustifications_stateBefore : ∀ (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V), ∀ w₁ ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
      ∀ B ∈ (w₁ v).st.bodies,
        ((Model.spec (V := V)).derive_named S.E S.cfg B).h_j ≤ (w₁ v).st.core.h_j := by
  intro S rho i v w₁ hw₁
  exact noHigh_of_inv S (w₁ v) (inv_fold S (NoHighInv S) (noHighInv_step S)
    (noHighInv_init S v) (rho.events.take i) w₁ hw₁ v)

/-- The field `noHighJustifications_stateBeforeTime` of `HandlersRunFacts` at `Model.spec`: in
    every world the events of `rho` with time less than `t` can reach from the initial world, no
    named block validator `v` holds derives a justified height greater than its store's. -/
theorem spec_noHighJustifications_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V)
    (t : Time) (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM
        (worldStepOf (Model.spec (V := V)) S) (fun u => (Model.spec (V := V)).initial S u),
      ∀ B ∈ (w₁ v).st.bodies,
        ((Model.spec (V := V)).derive_named S.E S.cfg B).h_j ≤ (w₁ v).st.core.h_j := by
  intro S rho t v w₁ hw₁
  exact noHigh_of_inv S (w₁ v) (inv_fold S (NoHighInv S) (noHighInv_step S)
    (noHighInv_init S v) _ w₁ hw₁ v)

/-! ### The height maximum and the finalized block are carried by held named blocks -/

/-- `CarrierInv S st`: in the image of `st`, some tree block has a chain state at height `h_max`,
    and some tree block has a chain state with the store's `F` and a finalized height less than
    `h_max`; and `RootsInv S st`. -/
def CarrierInv (S : Setup V) (st : Spec.Store V) : Prop :=
  (priv% Proofs.Vocabulary.Protocol.Handlers.MaximumCarrier
    DecoupledConsensusModel.Proofs.NamedMaximumCarrier.CoreMaximum) st.toProof ∧
  (priv% Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
    DecoupledConsensusModel.Proofs.NamedFinalizationBridge.CoreFinalizer) st.toProof ∧
  RootsInv S st

/-- Every step into a store with distinct roots keeps `CarrierInv`, given `StoreOk` and
    `RunStoreInv`. -/
theorem carrierInv_step (S : Setup V) (τ : Time) (a b : Spec.Store V)
    (hs : StoreSteps.StoreStep (Setup.toSpec S).C (Setup.toSpec S).P τ a b)
    (hd : DistinctRoots b.T) (h : StoreOk a ∧ SubtypeEqualities.RunStoreInv a ∧ CarrierInv S a) :
    StoreOk b ∧ SubtypeEqualities.RunStoreInv b ∧ CarrierInv S b := by
  obtain ⟨hb1, hb2⟩ := base_step hs hd ⟨h.1, h.2.1⟩
  refine ⟨hb1, hb2, ?_⟩
  have hj := h.2.2
  cases hs with
  | grades g => exact hj
  | clock => exact hj
  | confirm x y z => exact hj
  | vote u =>
    have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.MaximumCarrier
      DecoupledConsensusModel.Proofs.NamedMaximumCarrier.gf_maximum) S.E a.toProof u.toProof hj.1
    have h2 := (priv% Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
      DecoupledConsensusModel.Proofs.NamedFinalizationBridge.gf_finalizer) S.E a.toProof u.toProof
      hj.2.1
    rw [toProof_on_goldfish_vote_checked] at h1 h2
    obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes (Setup.toSpec S).P a u
    refine ⟨h1, h2, ?_⟩
    rw [e]
    exact hj.2.2
  | attest row =>
    have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.MaximumCarrier
      DecoupledConsensusModel.Proofs.NamedMaximumCarrier.row_maximum) S.hc a.toProofNamed
      row.toProofNamed hj.1
    have h2 := (priv% Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
      DecoupledConsensusModel.Proofs.NamedFinalizationBridge.row_finalizer) S.hc a.toProofNamed
      row.toProofNamed hj.2.1
    have h3 := Proofs.NamedStoreRoots.invariant_admit_row S.E S.hc S.cfg a.toProofNamed
      row.toProofNamed hj.2.2
    rw [toProof_admit_row S.E S.hc S.cfg] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  | block B =>
    rcases SubtypeEqualities.on_block_cases_of_ok _ _ hd with e | hroot
    · rw [e]
      exact hj
    · have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.MaximumCarrier
        DecoupledConsensusModel.Proofs.NamedMaximumCarrier.block_maximum) S a.toProofNamed
        B.toProofNamed hj.1
      have h2 := (priv% Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
        DecoupledConsensusModel.Proofs.NamedFinalizationBridge.block_finalizer) S a.toProofNamed
        B.toProofNamed hj.2.2.1 hj.2.1
      have h3 := Proofs.NamedStoreRoots.invariant_on_block_with .alsoCarried S.E S.hc S.cfg
        a.toProofNamed B.toProofNamed hj.2.2
      rw [← image_on_block_step S h.1 h.2.1 B hroot] at h1 h2 h3
      exact ⟨h1, h2, h3⟩

/-- The initial store has `CarrierInv`. -/
theorem carrierInv_init (S : Setup V) :
    CarrierInv S (Spec.Store.init : Spec.Store V) := by
  have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.MaximumCarrier
    DecoupledConsensusModel.Proofs.NamedMaximumCarrier.initial_core_maximum) (V := V)
  have h2 := (priv% Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
    DecoupledConsensusModel.Proofs.NamedFinalizationBridge.initial_core_finalizer) (V := V)
  have h3 := Proofs.NamedStoreRoots.invariant_initial S.E S.cfg (V := V)
  rw [toProof_ns_initial] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- From `CarrierInv`, some named block the node holds derives the store's finalized block, with a
    finalized height less than `h_max`. -/
theorem finalization_of_inv (S : Setup V) (n : (Model.spec (V := V)).N)
    (h : CarrierInv S n.val.st) :
    ∃ D : NamedBlock V, D ∈ n.st.bodies ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).F = n.st.core.F ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h_F < n.st.core.h_max := by
  obtain ⟨D, hD, hF, hh⟩ := (priv% Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
    DecoupledConsensusModel.Proofs.NamedFinalizationBridge.named_finalizer) S
    n.val.st.toProofNamed h.2.2.1 h.2.1
  refine ⟨D, hD, ?_, ?_⟩
  · show (Member.derive_named S.E S.cfg D).toProof.F = _
    rw [image_derive_named]
    exact hF
  · show (Member.derive_named S.E S.cfg D).toProof.h_F < _
    rw [image_derive_named]
    exact hh

/-- From `CarrierInv`, some named block the node holds derives a chain state at the store's `h_max`. -/
theorem maximum_of_inv (S : Setup V) (n : (Model.spec (V := V)).N)
    (h : CarrierInv S n.val.st) :
    ∃ D : NamedBlock V, D ∈ n.st.bodies ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h = n.st.core.h_max := by
  obtain ⟨D, hD, hh⟩ := (priv% Proofs.Vocabulary.Protocol.Handlers.MaximumCarrier
    DecoupledConsensusModel.Proofs.NamedMaximumCarrier.named_maximum) S
    n.val.st.toProofNamed h.2.2.1 h.1
  refine ⟨D, hD, ?_⟩
  show (Member.derive_named S.E S.cfg D).toProof.h = _
  rw [image_derive_named]
  exact hh

/-- The field `finalization_carrier_stateBefore` of `HandlersRunFacts` at `Model.spec`: in
    every world the run `rho` can reach before its `i`-th event, some named block validator `v`
    holds derives `v`'s finalized block, with a finalized height less than `v`'s `h_max`. -/
theorem spec_finalization_carrier_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat)
    (v : V) (w : V → (Model.spec (V := V)).N)
    (hw : w ∈ stateBeforeOf (Model.spec (V := V)) S rho i),
    ∃ D : NamedBlock V, D ∈ (w v).st.bodies ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).F = (w v).st.core.F ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h_F < (w v).st.core.h_max := by
  intro S rho i v w hw
  exact finalization_of_inv S (w v) (inv_fold S (CarrierInv S) (carrierInv_step S)
    (carrierInv_init S) (rho.events.take i) w hw v)

/-- The field `finalization_carrier_stateBeforeTime` of `HandlersRunFacts` at `Model.spec`: in
    every world the events of `rho` with time less than `t` can reach from the initial world, some
    named block validator `v` holds derives `v`'s finalized block, with a finalized height less than
    `v`'s `h_max`. -/
theorem spec_finalization_carrier_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V)
    (t : Time) (v : V) (w : V → (Model.spec (V := V)).N)
    (hw : w ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM
      (worldStepOf (Model.spec (V := V)) S) (fun u => (Model.spec (V := V)).initial S u)),
    ∃ D : NamedBlock V, D ∈ (w v).st.bodies ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).F = (w v).st.core.F ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h_F < (w v).st.core.h_max := by
  intro S rho t v w hw
  exact finalization_of_inv S (w v) (inv_fold S (CarrierInv S) (carrierInv_step S)
    (carrierInv_init S) _ w hw v)

/-- The field `maximum_carrier_stateBeforeTime` of `HandlersRunFacts` at `Model.spec`: in every
    world the events of `rho` with time less than `t` can reach from the initial world, some named
    block validator `v` holds derives a chain state at `v`'s `h_max`. -/
theorem spec_maximum_carrier_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time)
    (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM
        (worldStepOf (Model.spec (V := V)) S) (fun u => (Model.spec (V := V)).initial S u),
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h = (w₁ v).st.core.h_max := by
  intro S rho t v w₁ hw₁
  exact maximum_of_inv S (w₁ v) (inv_fold S (CarrierInv S) (carrierInv_step S)
    (carrierInv_init S) _ w₁ hw₁ v)

/-- The field `maximum_carrier_stateBefore` of `HandlersRunFacts` at `Model.spec`: in every
    world the run `rho` can reach before its `i`-th event, some named block validator `v` holds
    derives a chain state at `v`'s `h_max`. -/
theorem spec_maximum_carrier_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat)
    (v : V), ∀ w₁ ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h = (w₁ v).st.core.h_max := by
  intro S rho i v w₁ hw₁
  exact maximum_of_inv S (w₁ v) (inv_fold S (CarrierInv S) (carrierInv_step S)
    (carrierInv_init S) (rho.events.take i) w₁ hw₁ v)

/-! ### A held named block keeps its stamp -/

/-- The field `stateBefore_body_stamp_mono` of `HandlersRunFacts` at `Model.spec`: for `i ≤ j`,
    if `reader` holds the named block `B` in a world before the `i`-th event of `rho`, then in every
    world the events `i` to `j - 1` lead to, `reader` still holds `B` with the same block stamp. -/
theorem spec_stateBefore_body_stamp_mono : ∀ (S : Setup V) (rho : Record.Run V) (reader : V)
    {i j : Nat} (hij : i ≤ j) {B : NamedBlock V},
    ∀ w₁ ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
    B ∈ (w₁ reader).st.bodies →
    ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (worldStepOf (Model.spec (V := V)) S) w₁,
    B ∈ (w₂ reader).st.bodies ∧
      (w₂ reader).st.core.timestamp_block B.erase =
        (w₁ reader).st.core.timestamp_block B.erase := by
  intro S rho reader i j _ B w₁ _ hB w₂ hw₂
  have hR := (fold_relation_ok S (fun _ => True) KeepsBlocks keepsBlocks_refl keepsBlocks_trans _
    (fun p t _ n out hout _ => ⟨trivial, (StoreSteps.reach_relation (fun _ => True) KeepsBlocks
      keepsBlocks_refl keepsBlocks_trans (fun _ _ _ _ => trivial)
      (fun _ _ hs _ => keepsBlocks_step hs) (specBase_tick_reach S p n t out hout)
      trivial).2⟩)
    (fun n o n' h _ => ⟨trivial, (StoreSteps.reach_relation (fun _ => True) KeepsBlocks
      keepsBlocks_refl keepsBlocks_trans (fun _ _ _ _ => trivial)
      (fun _ _ hs _ => keepsBlocks_step hs) (specBase_process_reach S n n' o h 0)
      trivial).2⟩)
    w₁ (fun _ => trivial) w₂ hw₂ reader).2
  have hB' : B ∈ (w₁ reader).val.st.T.map Spec.Block.toProofNamedEmb := hB
  obtain ⟨X, hX, rfl⟩ := Finset.mem_map.mp hB'
  have hX₂ := (hR X hX).1
  refine ⟨Finset.mem_map_of_mem _ hX₂, ?_⟩
  show (w₂ reader).val.st.toProof.timestamp_block (Spec.Block.toProofNamedEmb X).erase =
    (w₁ reader).val.st.toProof.timestamp_block (Spec.Block.toProofNamedEmb X).erase
  rw [Spec.Block.coe_toProofNamedEmb, Spec.Block.toProofNamed_erase,
    Spec.Store.toProof_timestamp_block_of_mem _
      (SubtypeEqualities.injOn_of_distinctRoots (w₂ reader).property.2.1) hX₂,
    Spec.Store.toProof_timestamp_block_of_mem _
      (SubtypeEqualities.injOn_of_distinctRoots (w₁ reader).property.2.1) hX]
  exact (hR X hX).2

end SpecRecord.HandlersRunFacts
