module
public import Model.Vocabulary.Protocol.Duties.Proposals

@[expose] public section

/-!
# Height-pair cases

The branches of `Protocol.height_pair`, and their lift to the height pair of the named round action.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The branches of `height_pair` -/

omit [DecidableEq V] [Fintype V] in
/-- A recorded timeout at `H` makes `height_pair` emit a timeout at `H`. -/
theorem height_pair_eq_timeout_of_timeout
    (Lambda : Record) {H : Height} {T : BlockId} {nu : Bool}
    (fp : Option FinalityPair) (htimeout : Lambda.timeout H = true) :
    height_pair Lambda (some (H, T, nu)) fp = HeightPair.timeout H := by
  simp [height_pair, htimeout]

omit [DecidableEq V] [Fintype V] in
/-- With a clear timeout bit and `own_lock` equal to the selected target, `height_pair` emits that
    target. -/
theorem height_pair_eq_target_of_aligned_lock
    (Lambda : Record) {H : Height} {T : BlockId} {nu : Bool}
    (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false)
    (hlock : own_lock Lambda H fp = some T) :
    height_pair Lambda (some (H, T, nu)) fp = HeightPair.target H T := by
  simp [height_pair, htimeout, hlock]

omit [DecidableEq V] [Fintype V] in
/-- With a clear timeout bit, no `own_lock`, and a recorded target equal to the selected target,
    `height_pair` emits that target. -/
theorem height_pair_eq_target_of_no_lock_recorded_target
    (Lambda : Record) {H : Height} {T : BlockId} {nu : Bool}
    (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false)
    (hlock : own_lock Lambda H fp = none)
    (htarget : Lambda.target H = some T) :
    height_pair Lambda (some (H, T, nu)) fp = HeightPair.target H T := by
  simp [height_pair, htimeout, hlock, htarget]

omit [DecidableEq V] [Fintype V] in
/-- With a clear timeout bit, no `own_lock`, and a recorded target different from the selected
    target, `height_pair` emits a timeout. -/
theorem height_pair_eq_timeout_of_no_lock_off_target_record
    (Lambda : Record) {H : Height} {T recorded : BlockId} {nu : Bool}
    (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false)
    (hlock : own_lock Lambda H fp = none)
    (htarget : Lambda.target H = some recorded) (hne : recorded ≠ T) :
    height_pair Lambda (some (H, T, nu)) fp = HeightPair.timeout H := by
  simp [height_pair, htimeout, hlock, htarget, hne]

omit [DecidableEq V] [Fintype V] in
/-- With a clear timeout bit, no `own_lock`, no recorded target and a false `nj` bit, `height_pair`
    emits the selected target. -/
theorem height_pair_eq_target_of_no_lock_no_target_justifiable
    (Lambda : Record) {H : Height} {T : BlockId}
    (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false)
    (hlock : own_lock Lambda H fp = none)
    (htarget : Lambda.target H = none) :
    height_pair Lambda (some (H, T, false)) fp = HeightPair.target H T := by
  simp [height_pair, htimeout, hlock, htarget]

omit [DecidableEq V] [Fintype V] in
/-- With a clear timeout bit, no `own_lock`, no recorded target and a true `nj` bit, `height_pair`
    emits a timeout. -/
theorem height_pair_eq_timeout_of_no_lock_no_target_nonjustifiable
    (Lambda : Record) {H : Height} {T : BlockId}
    (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false)
    (hlock : own_lock Lambda H fp = none)
    (htarget : Lambda.target H = none) :
    height_pair Lambda (some (H, T, true)) fp = HeightPair.timeout H := by
  simp [height_pair, htimeout, hlock, htarget]

omit [DecidableEq V] [Fintype V] in
/-- With height fields `(H, T, nu)` and `own_lock` at `H` empty or `T`, `height_pair` emits
    `target H T` or `timeout H`. -/
theorem height_pair_target_or_timeout_of_fields_some_and_lock_none_or_aligned
    (Lambda : Record) (H : Height) (T : BlockId) (nu : Bool)
    (fp : Option FinalityPair)
    (hlock : own_lock Lambda H fp = none ∨ own_lock Lambda H fp = some T) :
    height_pair Lambda (some (H, T, nu)) fp = HeightPair.target H T ∨
      height_pair Lambda (some (H, T, nu)) fp = HeightPair.timeout H := by
  by_cases htimeout : Lambda.timeout H = true
  · exact Or.inr (height_pair_eq_timeout_of_timeout Lambda fp htimeout)
  · have htimeoutFalse : Lambda.timeout H = false :=
      Bool.eq_false_of_not_eq_true htimeout
    rcases hlock with hnone | haligned
    · cases htarget : Lambda.target H with
      | none =>
          cases nu with
          | false =>
              exact Or.inl
                (height_pair_eq_target_of_no_lock_no_target_justifiable
                  Lambda fp htimeoutFalse hnone htarget)
          | true =>
              exact Or.inr
                (height_pair_eq_timeout_of_no_lock_no_target_nonjustifiable
                  Lambda fp htimeoutFalse hnone htarget)
      | some recorded =>
          by_cases heq : recorded = T
          · subst recorded
            exact Or.inl
              (height_pair_eq_target_of_no_lock_recorded_target
                Lambda fp htimeoutFalse hnone htarget)
          · exact Or.inr
              (height_pair_eq_timeout_of_no_lock_off_target_record
                Lambda fp htimeoutFalse hnone htarget heq)
    · exact Or.inl
        (height_pair_eq_target_of_aligned_lock
          Lambda fp htimeoutFalse haligned)


/-! ## The named round action's height pair -/


/-- Without fields there is no named row to emit. -/
theorem encodeHeight_none (p : HeightPair) :
    Protocol.NamedRecord.encodeHeight none p = NamedHeightPair.empty := by
  cases p <;> rfl

omit [DecidableEq V] [Fintype V] in
/-- With height fields `(H, T, nu)`, a target pair is encoded as a vote for `T` at `H` with the
    timeout bit false. -/
theorem encodeHeight_of_target
    {H : Height} {T : BlockId} {nu : Bool} {g : Height} {X : BlockId} :
    Protocol.NamedRecord.encodeHeight (some (H, T, nu))
      (HeightPair.target g X) = NamedHeightPair.vote H T false := rfl

omit [DecidableEq V] [Fintype V] in
/-- With height fields `(H, T, nu)`, a timeout pair is encoded as a vote for `T` at `H` with the
    timeout bit true. -/
theorem encodeHeight_of_timeout
    {H : Height} {T : BlockId} {nu : Bool} {g : Height} :
    Protocol.NamedRecord.encodeHeight (some (H, T, nu))
      (HeightPair.timeout g) = NamedHeightPair.vote H T true := rfl

/-- The action's selected source under a grade contract. -/
def actionSource (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) : Option (Block V) :=
  Protocol.fg_source_with contract E hc st (hc.round_of st.s)
    (Protocol.grade2_block_with contract E hc st (hc.round_of st.s))

/-- The named round action's height pair is `encodeHeight` of the record's `height_pair`, with the
    height fields read from the action's source. -/
theorem named_round_action_height_pair (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.height_pair =
      Protocol.NamedRecord.encodeHeight
        ((actionSource contract E hc st).map
          (fun Q => ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj)))
        (height_pair record.legacy
          ((actionSource contract E hc st).map
            (fun Q => ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj)))
          (Protocol.NamedActions.round_action_with
            contract E hc nd st record).2.finality_pair) := rfl


/-- The named round action's height pair is in one of four cases: no selected source, an `own_lock`
    different from the selected target, the selected target, or a timeout at the selected height. -/
theorem round_action_height_pair_cases
    (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord) :
    (actionSource contract E hc st = none ∧
      (Protocol.NamedActions.round_action_with contract E hc nd st record).2.height_pair =
        NamedHeightPair.empty) ∨
      ∃ Q,
        actionSource contract E hc st = some Q ∧
        ((∃ locked,
            record.legacy.timeout (st.σ Q).h = false ∧
            own_lock record.legacy (st.σ Q).h
                (Protocol.NamedActions.round_action_with
                  contract E hc nd st record).2.finality_pair =
              some locked ∧
            locked ≠ (st.σ Q).T_h.root ∧
            (Protocol.NamedActions.round_action_with
              contract E hc nd st record).2.height_pair = NamedHeightPair.empty) ∨
          (Protocol.NamedActions.round_action_with
              contract E hc nd st record).2.height_pair =
              NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root false ∨
          (Protocol.NamedActions.round_action_with
              contract E hc nd st record).2.height_pair =
              NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root true) := by
  set fp := (Protocol.NamedActions.round_action_with
    contract E hc nd st record).2.finality_pair with hfp
  cases hsource : actionSource contract E hc st with
  | none =>
      left
      refine ⟨rfl, ?_⟩
      rw [named_round_action_height_pair, hsource, Option.map_none]
      exact encodeHeight_none _
  | some Q =>
      right
      refine ⟨Q, rfl, ?_⟩
      by_cases htimeout : record.legacy.timeout (st.σ Q).h = true
      · right
        right
        rw [named_round_action_height_pair, hsource, Option.map_some,
          height_pair_eq_timeout_of_timeout record.legacy fp htimeout]
        exact encodeHeight_of_timeout
      · have htimeoutFalse : record.legacy.timeout (st.σ Q).h = false :=
          Bool.eq_false_of_not_eq_true htimeout
        cases hlock : own_lock record.legacy (st.σ Q).h fp with
        | none =>
            rcases
                height_pair_target_or_timeout_of_fields_some_and_lock_none_or_aligned
                  record.legacy (st.σ Q).h (st.σ Q).T_h.root (st.σ Q).nj fp
                  (Or.inl hlock) with htarget | htimeoutPair
            · refine Or.inr (Or.inl ?_)
              rw [named_round_action_height_pair, hsource, Option.map_some, htarget]
              exact encodeHeight_of_target
            · refine Or.inr (Or.inr ?_)
              rw [named_round_action_height_pair, hsource, Option.map_some,
                htimeoutPair]
              exact encodeHeight_of_timeout
        | some locked =>
            by_cases heq : locked = (st.σ Q).T_h.root
            · subst locked
              refine Or.inr (Or.inl ?_)
              rw [named_round_action_height_pair, hsource, Option.map_some,
                height_pair_eq_target_of_aligned_lock
                  record.legacy fp htimeoutFalse hlock]
              exact encodeHeight_of_target
            · left
              refine ⟨locked, htimeoutFalse, rfl, heq, ?_⟩
              rw [named_round_action_height_pair, hsource, Option.map_some]
              rw [show height_pair record.legacy
                  (some ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj)) fp =
                  HeightPair.empty by
                simp [height_pair, htimeoutFalse, hlock, heq]]
              rfl


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
