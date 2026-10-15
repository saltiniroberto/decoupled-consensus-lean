import Model.Record.Wiring
import Model.Record.ModelSpellings
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Records
import Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
import Proofs.Vocabulary.Protocol.Duties.Inputs.ActionSources
import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions
import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
import Proofs.Vocabulary.Execution.BodyRetention
import Proofs.Vocabulary.Protocol.Store.RawSource
import Proofs.Vocabulary.Protocol.Grades.Interpolation
import Proofs.Vocabulary.Protocol.Handlers.HMaxMonotone
import Proofs.Vocabulary.Protocol.Handlers.NumericStore
import Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
import Proofs.Vocabulary.Protocol.Schedule.ReceiptCallsF1

/-!
# Facts of the validator-client routines

`ValidatorClientFacts` holds the facts a model `M` provides about its signing-record routines
(`M.own_lock`, `M.height_pair`, `M.create_attestation`, `M.finality_pair`, `M.encodeHeight`) on an
arbitrary input. `ValidatorClientRunFacts`, for facts about runs, has no field.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The facts about the validator-client routines of a model `M`. -/
structure ValidatorClientFacts (M : Model V) : Prop where
  /-- If the record `Λ` is lock-compatible and the attestation `M.create_attestation` returns from
      `Λ` has the height pair target `(h, T)`, the record that call returns holds the target `T` at
      height `h`. -/
  create_attestation_saves : ∀ (Λ : M.R)
    (hla : Restated.Vocabulary.Proofs.Records.LockCompatible M Λ) (val_index : V)
    (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) {h : Height} {T : BlockId}
    (hhp : (M.create_attestation Λ val_index r confirmed fields h_j J h_F).2.height_pair =
      HeightPair.target h T),
    (M.create_attestation Λ val_index r confirmed fields h_j J h_F).1.target h = some T
  /-- If the record `Lambda` has no target, no timeout and no lock at height `H`, and the finality
      pair `fp` is at no height `H`, the height pair for the entry `(H, T, true)` and `fp` is the
      timeout at `H`. -/
  height_pair_timeout_of_fresh_of_finality_avoids : ∀ {Lambda : M.R} {H : Height} {T : BlockId}
    (hfresh : Lambda.target H = none ∧ Lambda.timeout H = false ∧ Lambda.lock H = none)
    (fp : Option FinalityPair) (havoid : ∀ p : FinalityPair, fp = some p → p.height ≠ H),
    M.height_pair Lambda (some (H, T, true)) fp = HeightPair.timeout H
  /-- For every outcome of the round action, with `src` the source it selects: either `src` is
      `none` and the height pair is empty, or `src` is a block `Q` and the height pair is empty
      because the record's own lock at `Q`'s height differs from the target root without a timeout
      there, or it is a vote at `Q`'s height for that root, with or without timeout. -/
  round_action_height_pair_cases : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS) (record : M.NR)
    (g : Option (Block V)) (hg : M.grade2_block_with contract E hc st (M.round_of hc st.s) ⇢ g)
    (src : Option (Block V)) (hsrc : M.fg_source_with contract E hc st (M.round_of hc st.s) g ⇢ src)
    (out : M.NR × NamedAttestation V) (hout : M.round_action_with contract E hc nd st record ⇢ out),
    (src = none ∧ out.2.height_pair = NamedHeightPair.empty) ∨
    ∃ Q, src = some Q ∧
      ((∃ locked, record.legacy.timeout (st.σ Q).h = false ∧
          M.own_lock record.legacy (st.σ Q).h out.2.finality_pair = some locked ∧
          locked ≠ (st.σ Q).T_h.root ∧ out.2.height_pair = NamedHeightPair.empty) ∨
        out.2.height_pair = NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root false ∨
        out.2.height_pair = NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root true)
  /-- The lock at height `g` of `M.record_attestation Λ a` is `M.own_lock Λ g` at `a`'s finality
      pair. -/
  record_attestation_lock_eq_own_lock : ∀ (Λ : M.R) (a : CombinedAttestation V) (g : Height),
    (M.record_attestation Λ a).lock g = M.own_lock Λ g a.finality_pair
  /-- The record `M.create_attestation` returns is `Λ` with the returned attestation recorded by
      `M.record_attestation`. -/
  create_attestation_fst : ∀ (Λ : M.R) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height)
    (J : BlockId) (h_F : Height),
    (M.create_attestation Λ val_index r confirmed fields h_j J h_F).1 =
      M.record_attestation Λ (M.create_attestation Λ val_index r confirmed fields h_j J h_F).2
  /-- The height pair `M.height_pair Λ fields fp` is empty, or `fields` is `some (h, T, ν)` and the
      height pair is the timeout at `h` or the target `(h, T)`. -/
  height_pair_cases : ∀ {Λ : M.R} (fields : Option (Height × BlockId × Bool)) (fp : Option FinalityPair), M.height_pair Λ fields fp = .empty ∨
    ∃ (h : Height) (T : BlockId) (ν : Bool), fields = some (h, T, ν) ∧
    (M.height_pair Λ fields fp = .timeout h ∨
    M.height_pair Λ fields fp = .target h T)
  /-- If the record `Λ` holds the lock `T` at height `h`, so does the record `M.create_attestation`
      returns from `Λ`. -/
  create_attestation_lock_mono : ∀ {Λ : M.R} {h : Height} {T : BlockId} (hlock : Λ.lock h = some T) (val_index : V) (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height) (J : BlockId) (h_F : Height), (M.create_attestation Λ val_index r confirmed fields h_j J h_F).1.lock h =
    some T
  /-- If the attestation `M.create_attestation` returns has the height pair target `(h, T)` and the
      finality pair `(h, T')`, then `T = T'`. -/
  create_attestation_no_self_E1 : ∀ (Λ : M.R) (val_index : V) (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height) (J : BlockId) (h_F : Height) {h : Height} {T T' : BlockId} (hhp : (M.create_attestation Λ val_index r confirmed fields h_j J h_F).2.height_pair =
    HeightPair.target h T) (hfp : (M.create_attestation Λ val_index r confirmed fields h_j J h_F).2.finality_pair =
    some ⟨h, T'⟩), T = T'
  /-- `M.encodeHeight` with no fields returns the empty named height pair. -/
  encodeHeight_none : ∀ (p : HeightPair), M.encodeHeight none p = NamedHeightPair.empty
  /-- `M.encodeHeight` at the fields `(H, T, nu)` and a target height pair returns the height vote
      for `H` and `T` with timeout bit `false`. -/
  encodeHeight_of_target : ∀ {H : Height} {T : BlockId} {nu : Bool} {g : Height} {X : BlockId}, M.encodeHeight (some (H, T, nu))
    (HeightPair.target g X) = NamedHeightPair.vote H T false
  /-- `M.encodeHeight` at the fields `(H, T, nu)` and a timeout height pair returns the height vote
      for `H` and `T` with timeout bit `true`. -/
  encodeHeight_of_timeout : ∀ {H : Height} {T : BlockId} {nu : Bool} {g : Height}, M.encodeHeight (some (H, T, nu))
    (HeightPair.timeout g) = NamedHeightPair.vote H T true
  /-- If `Lambda` has no timeout at height `H` and its own lock at `H` with the finality pair `fp`
      is `T`, the height pair at the fields `(H, T, nu)` and `fp` is the target `(H, T)`. -/
  height_pair_eq_target_of_aligned_lock : ∀ (Lambda : M.R) {H : Height} {T : BlockId} {nu : Bool} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : M.own_lock Lambda H fp = some T), M.height_pair Lambda (some (H, T, nu)) fp = HeightPair.target H T
  /-- If `Lambda` has no timeout, no own lock with the finality pair `fp`, and no target at height
      `H`, the height pair at the fields `(H, T, false)` and `fp` is the target `(H, T)`. -/
  height_pair_eq_target_of_no_lock_no_target_justifiable : ∀ (Lambda : M.R) {H : Height} {T : BlockId} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : M.own_lock Lambda H fp = none) (htarget : Lambda.target H = none), M.height_pair Lambda (some (H, T, false)) fp = HeightPair.target H T
  /-- If `Lambda` has no timeout and no own lock with the finality pair `fp` at height `H`, and
      holds the target `T` there, the height pair at the fields `(H, T, nu)` and `fp` is the target
      `(H, T)`. -/
  height_pair_eq_target_of_no_lock_recorded_target : ∀ (Lambda : M.R) {H : Height} {T : BlockId} {nu : Bool} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : M.own_lock Lambda H fp = none) (htarget : Lambda.target H = some T), M.height_pair Lambda (some (H, T, nu)) fp = HeightPair.target H T
  /-- If `Lambda` has no timeout, no own lock with the finality pair `fp`, and no target at height
      `H`, the height pair at the fields `(H, T, true)` and `fp` is the timeout at `H`. -/
  height_pair_eq_timeout_of_no_lock_no_target_nonjustifiable : ∀ (Lambda : M.R) {H : Height} {T : BlockId} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : M.own_lock Lambda H fp = none) (htarget : Lambda.target H = none), M.height_pair Lambda (some (H, T, true)) fp = HeightPair.timeout H
  /-- If `Lambda` has no timeout and no own lock with the finality pair `fp` at height `H`, and
      holds there a target `recorded` other than `T`, the height pair at the fields `(H, T, nu)` and
      `fp` is the timeout at `H`. -/
  height_pair_eq_timeout_of_no_lock_off_target_record : ∀ (Lambda : M.R) {H : Height} {T recorded : BlockId} {nu : Bool} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : M.own_lock Lambda H fp = none) (htarget : Lambda.target H = some recorded) (hne : recorded ≠ T), M.height_pair Lambda (some (H, T, nu)) fp = HeightPair.timeout H
  /-- If `Lambda` has a timeout at height `H`, the height pair at the fields `(H, T, nu)` and any
      finality pair is the timeout at `H`. -/
  height_pair_eq_timeout_of_timeout : ∀ (Lambda : M.R) {H : Height} {T : BlockId} {nu : Bool} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = true), M.height_pair Lambda (some (H, T, nu)) fp = HeightPair.timeout H
  /-- The finality pair of the attestation `M.create_attestation` returns is
      `M.finality_pair Λ h_j J h_F`. -/
  create_attestation_snd_finality_pair : ∀ (Λ : M.R) (val_index : V) (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height) (J : BlockId) (h_F : Height), (M.create_attestation Λ val_index r confirmed fields h_j J h_F).2.finality_pair =
    M.finality_pair Λ h_j J h_F
  /-- With a finality pair at height `h` and target `J`, the own lock at height `h` is `J`. -/
  own_lock_some_self : ∀ (Λ : M.R) (h : Height) (J : BlockId), M.own_lock Λ h (some ⟨h, J⟩) = some J
  /-- If `M.finality_pair Λ h_j J h_F` is `(h, T)`, then `h = h_j`. -/
  finality_pair_height : ∀ {Λ : M.R} {h_j : Height} {J : BlockId} {h_F h : Height} {T : BlockId} (hp : M.finality_pair Λ h_j J h_F = some ⟨h, T⟩), h_j = h
  /-- If `M.finality_pair Λ h_j J h_F` is `(h, T)`, then `T = J`. -/
  finality_pair_target : ∀ {Λ : M.R} {h_j : Height} {J : BlockId} {h_F h : Height} {T : BlockId} (hp : M.finality_pair Λ h_j J h_F = some ⟨h, T⟩), J = T
  /-- `M.encodeHeight` writes the empty height pair as the empty named height pair, whatever the
      fields. -/
  encodeHeight_empty : ∀ (fields : Option (Height × BlockId × Bool)), M.encodeHeight fields HeightPair.empty = NamedHeightPair.empty
  /-- If `M.encodeHeight` at the fields `(h, e, ν)` gives a vote at `(H, e')`, then `h = H` and
      `e = e'`. -/
  encodeHeight_vote_inv_l85c : ∀ {h H : Height} {e e' : BlockId} {ν b : Bool} {p : HeightPair} (hp : M.encodeHeight (some (h, e, ν)) p = .vote H e' b), h = H ∧ e = e'
  /-- If `M.encodeHeight fields pair` is the height vote for `h₀` and `entry`, then `fields` is
      `some (h₀, entry, b)` for some Boolean `b`. -/
  fields_of_encodeHeight_vote : ∀ (fields : Option (Height × BlockId × Bool)) (pair : HeightPair) {h₀ : Height} {entry : BlockId} {tmo : Bool} (h : M.encodeHeight fields pair = NamedHeightPair.vote h₀ entry tmo), ∃ b : Bool, fields = some (h₀, entry, b)
  /-- At the fields `(H, e, ν)`, the height pair is the target `(H, e)`; or the timeout at `H`, and
      then the record times `H` out, holds a target at `H` other than `e`, or `ν` is set; or empty,
      and then the own lock at `H` names a block other than `e`. -/
  height_pair_cases_l85c : ∀ (Λ : M.R) (H : Height) (e : BlockId) (ν : Bool) (fp : Option FinalityPair), M.height_pair Λ (some (H, e, ν)) fp = .target H e ∨
    (M.height_pair Λ (some (H, e, ν)) fp = .timeout H ∧
    (Λ.timeout H = true ∨ (∃ rec, Λ.target H = some rec ∧ rec ≠ e) ∨ ν = true)) ∨
    (M.height_pair Λ (some (H, e, ν)) fp = .empty ∧
    ∃ locked, M.own_lock Λ H fp = some locked ∧ locked ≠ e)
  /-- With no finality pair, the own lock at height `h` is the record's lock at `h`. -/
  own_lock_none : ∀ (Λ : M.R) (h : Height), M.own_lock Λ h none = Λ.lock h
  /-- With a finality pair `p` at a height other than `h`, the own lock at height `h` is the
      record's lock at `h`. -/
  own_lock_some_of_ne : ∀ (Λ : M.R) (h : Height) {p : FinalityPair} (hp : p.height ≠ h), M.own_lock Λ h (some p) = Λ.lock h
  /-- With a finality pair `p` at a height other than `h`, the own lock at height `h` is the
      record's lock at `h`. -/
  own_lock_some_of_ne_explicit : ∀ (Λ : M.R) (h : Height) (p : FinalityPair) (hne : ¬ p.height = h), M.own_lock Λ h (some p) = Λ.lock h
  /-- With a finality pair at a height `h'` other than `h`, the own lock at height `h` is the
      record's lock at `h`. -/
  own_lock_some_pair_of_ne : ∀ (Λ : M.R) {h h' : Height} (J : BlockId) (hne : h' ≠ h), M.own_lock Λ h (some ⟨h', J⟩) = Λ.lock h

/-- The facts about runs of the validator-client routines of a model `M`; it has no field. -/
structure ValidatorClientRunFacts (M : Model V) : Prop where


end DecoupledConsensusModel.Sts.Record
