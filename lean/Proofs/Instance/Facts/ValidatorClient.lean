import Proofs.Instance.Model
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Instance.Facts.Duties

/-!
# The validator-client facts at `Model.spec`

The fields of `ValidatorClientFacts` proved at `Model.spec`, one theorem `spec_<field>`
per field, and the bundle `Model.spec_runFacts_validatorClient` of `ValidatorClientRunFacts`,
which has no field.
-/

set_option autoImplicit false

namespace SpecRecord.ValidatorClientFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecRecord.ChainStateToHandlers (fieldsToSpec)

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The members the fields name -/

/-- Mapping an optional triple of a height, a root and a flag to the spec's form and back gives it. -/
private theorem fields_round_trip (fields : Option (Height × BlockId × Bool)) :
    (fieldsToSpec fields).map (fun f => (f.1, f.2.1.toProof, f.2.2)) = fields := by
  rcases fields with _ | ⟨h, e, ν⟩ <;> rfl

/-- Mapping an optional finality pair to the spec's form and back gives it. -/
private theorem finality_pair_round_trip (fp : Option FinalityPair) :
    (fp.map Spec.FinalityPair.toSpec).map Spec.FinalityPair.toProof = fp := by
  rcases fp with _ | p <;> rfl

/-- The member `own_lock` of `Model.spec` at `sh` is the member `own_lock` of `Model.vocabulary`
    at `sh.toProof.legacy`. -/
private theorem own_lock_spec (sh : Spec.SigningHistory) (h : Height)
    (fp : Option FinalityPair) :
    (Model.spec (V := V)).own_lock sh h fp =
      (Model.vocabulary (V := V)).own_lock sh.toProof.legacy h fp := by
  show (Spec.Protocol.own_lock sh h (fp.map Spec.FinalityPair.toSpec)).map
    Spec.BlockId.toProof = Protocol.own_lock sh.toProof.legacy h fp
  rw [← toProof_own_lock, finality_pair_round_trip]

/-- The member `height_pair` of `Model.spec` at `sh` is the member `height_pair` of
    `Model.vocabulary` at `sh.toProof.legacy`. -/
private theorem height_pair_spec (sh : Spec.SigningHistory)
    (fields : Option (Height × BlockId × Bool)) (fp : Option FinalityPair) :
    (Model.spec (V := V)).height_pair sh fields fp =
      (Model.vocabulary (V := V)).height_pair sh.toProof.legacy fields fp := by
  show (Spec.Protocol.height_pair sh (fieldsToSpec fields)
    (fp.map Spec.FinalityPair.toSpec)).toProof =
      Protocol.height_pair sh.toProof.legacy fields fp
  rw [← toProof_height_pair, fields_round_trip, finality_pair_round_trip]

/-- The member `finality_pair` of `Model.spec` at `sh` is the member `finality_pair` of
    `Model.vocabulary` at `sh.toProof.legacy`. -/
private theorem finality_pair_spec (sh : Spec.SigningHistory) (h_j : Height)
    (J : BlockId) (h_F : Height) :
    (Model.spec (V := V)).finality_pair sh h_j J h_F =
      (Model.vocabulary (V := V)).finality_pair sh.toProof.legacy h_j J h_F := by
  show (Spec.Protocol.finality_pair sh h_j (Spec.BlockId.toSpec J) h_F).map
    Spec.FinalityPair.toProof = Protocol.finality_pair sh.toProof.legacy h_j J h_F
  rw [← toProof_finality_pair, Spec.BlockId.toProof_toSpec]

/-- The member `encodeHeight` of `Model.spec` is the member `encodeHeight` of `Model.vocabulary`. -/
private theorem encodeHeight_spec (fields : Option (Height × BlockId × Bool))
    (pair : HeightPair) :
    (Model.spec (V := V)).encodeHeight fields pair =
      (Model.vocabulary (V := V)).encodeHeight fields pair := rfl

/-- The image of the signing history the member `record_attestation` of `Model.spec` returns
    from `sh` and `a` is the member `record_attestation` of `Model.vocabulary` at `sh.toProof.legacy`
    and `a`. -/
private theorem record_attestation_spec (sh : Spec.SigningHistory)
    (a : CombinedAttestation V) :
    (Spec.SigningHistory.toProof
        ((Model.spec (V := V)).record_attestation sh a)).legacy =
      (Model.vocabulary (V := V)).record_attestation sh.toProof.legacy a := by
  show (Spec.Protocol.record_attestation sh
    (Spec.Attestation.toSpec a)).toProof.legacy =
      Protocol.record_attestation sh.toProof.legacy a
  rw [← toProof_record_attestation, Spec.Attestation.toProof_toSpec]

/-- The member `create_attestation` of `Model.spec` at `sh`, its signing history mapped to its
    image, is the member `create_attestation` of `Model.vocabulary` at `sh.toProof.legacy`. -/
private theorem create_attestation_spec (sh : Spec.SigningHistory) (v : V)
    (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    Prod.map (fun x : Spec.SigningHistory => x.toProof.legacy) id
        ((Model.spec (V := V)).create_attestation sh v r confirmed fields h_j J h_F) =
      (Model.vocabulary (V := V)).create_attestation sh.toProof.legacy v r confirmed fields h_j J
        h_F := by
  show Prod.map (fun x : Spec.SigningHistory => x.toProof.legacy) id
      (Prod.map id Spec.Attestation.toProof
        (Spec.Protocol.create_attestation sh v r
          (confirmed.map Spec.BlockId.toSpec) (fieldsToSpec fields) h_j
          (Spec.BlockId.toSpec J) h_F)) =
    Protocol.create_attestation sh.toProof.legacy v r confirmed fields h_j J h_F
  have hc : (confirmed.map Spec.BlockId.toSpec).map Spec.BlockId.toProof =
      confirmed := by rcases confirmed with _ | c <;> rfl
  conv_rhs => rw [← hc, ← fields_round_trip fields, ← Spec.BlockId.toProof_toSpec J,
    toProof_create_attestation]
  rfl

/-- `Protocol.record_attestation sh` gives the same signing history on `a` and on
    `Attestation.toSpec a.toProof`. -/
theorem record_attestation_toSpec_toProof (sh : Spec.SigningHistory)
    (a : Spec.Attestation V) :
    Spec.Protocol.record_attestation sh (Spec.Attestation.toSpec a.toProof) =
      Spec.Protocol.record_attestation sh a := by
  obtain ⟨v, r, c, hp, fp⟩ := a
  rcases hp with _ | ⟨h, T, _ | _⟩ <;> cases fp <;> rfl

/-- The image of the signing history the member `create_attestation` of `Model.spec` returns
    from `sh` is the signing record the member `create_attestation` of `Model.vocabulary` returns from
    `sh.toProof.legacy`. -/
private theorem create_attestation_fst_spec (sh : Spec.SigningHistory) (v : V)
    (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    (Spec.SigningHistory.toProof
        ((Model.spec (V := V)).create_attestation sh v r confirmed fields h_j J h_F).1).legacy =
      ((Model.vocabulary (V := V)).create_attestation sh.toProof.legacy v r confirmed fields h_j J
        h_F).1 :=
  congrArg Prod.fst (create_attestation_spec sh v r confirmed fields h_j J h_F)

/-- The attestation the member `create_attestation` of `Model.spec` returns from `sh` is the
    one the member `create_attestation` of `Model.vocabulary` returns from `sh.toProof.legacy`. -/
private theorem create_attestation_snd_spec (sh : Spec.SigningHistory) (v : V)
    (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    ((Model.spec (V := V)).create_attestation sh v r confirmed fields h_j J h_F).2 =
      ((Model.vocabulary (V := V)).create_attestation sh.toProof.legacy v r confirmed fields h_j J
        h_F).2 :=
  congrArg Prod.snd (create_attestation_spec sh v r confirmed fields h_j J h_F)

/-! ## The fields -/

/-- The field `create_attestation_saves` of `ValidatorClientFacts` at `Model.spec`: if the
    record `Λ` is lock-compatible and the attestation `create_attestation` returns from `Λ` has the
    height pair target `(h, T)`, then the record that call returns holds the target `T` at height
    `h`. -/
theorem spec_create_attestation_saves : ∀ (Λ : (Model.spec (V := V)).R)
    (hla : Restated.Vocabulary.Proofs.Records.LockCompatible (Model.spec (V := V)) Λ) (val_index : V)
    (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) {h : Height} {T : BlockId}
    (hhp : ((Model.spec (V := V)).create_attestation Λ val_index r confirmed fields h_j J h_F).2.height_pair =
    HeightPair.target h T),
    ((Model.spec (V := V)).create_attestation Λ val_index r confirmed fields h_j J h_F).1.target h = some T := by
  intro Λ hla v r c f h_j J h_F h T hhp
  rw [create_attestation_snd_spec] at hhp
  have hup := (Model.vocabulary_facts_validatorClient (V := V)).create_attestation_saves
    (Spec.SigningHistory.toProof Λ).legacy hla v r c f h_j J h_F hhp
  rw [← create_attestation_fst_spec] at hup
  exact hup

/-- The field `height_pair_timeout_of_fresh_of_finality_avoids` of `ValidatorClientFacts` at
    `Model.spec`: if the record `Lambda` has no target, no timeout and no lock at height `H`,
    and the finality pair `fp`, if any, is at a height other than `H`, then the height pair for the
    fields `(H, T, true)` and `fp` is the timeout at `H`. -/
theorem spec_height_pair_timeout_of_fresh_of_finality_avoids : ∀ {Lambda : (Model.spec (V := V)).R} {H : Height} {T : BlockId}
    (hfresh : Lambda.target H = none ∧ Lambda.timeout H = false ∧ Lambda.lock H = none)
    (fp : Option FinalityPair) (havoid : ∀ p : FinalityPair, fp = some p → p.height ≠ H),
    (Model.spec (V := V)).height_pair Lambda (some (H, T, true)) fp = HeightPair.timeout H := by
  intro Λ H T hfresh fp havoid
  rw [height_pair_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).height_pair_timeout_of_fresh_of_finality_avoids
    (Lambda := (Spec.SigningHistory.toProof Λ).legacy) hfresh fp havoid

/-- The field `record_attestation_lock_eq_own_lock` of `ValidatorClientFacts` at `Model.spec`:
    the lock at height `g` of `record_attestation Λ a` is `own_lock Λ g a.finality_pair`. -/
theorem spec_record_attestation_lock_eq_own_lock : ∀ (Λ : (Model.spec (V := V)).R) (a : CombinedAttestation V) (g : Height),
    ((Model.spec (V := V)).record_attestation Λ a).lock g = (Model.spec (V := V)).own_lock Λ g a.finality_pair := by
  intro Λ a g
  show (Spec.SigningHistory.toProof
    ((Model.spec (V := V)).record_attestation Λ a)).legacy.lock g = _
  rw [record_attestation_spec, own_lock_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).record_attestation_lock_eq_own_lock
    (Spec.SigningHistory.toProof Λ).legacy a g

/-- The field `create_attestation_fst` of `ValidatorClientFacts` at `Model.spec`: the record
    `create_attestation` returns from `Λ` is `Λ` with the attestation it returns recorded by
    `record_attestation`. -/
theorem spec_create_attestation_fst : ∀ (Λ : (Model.spec (V := V)).R) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height)
    (J : BlockId) (h_F : Height),
    ((Model.spec (V := V)).create_attestation Λ val_index r confirmed fields h_j J h_F).1 =
    (Model.spec (V := V)).record_attestation Λ ((Model.spec (V := V)).create_attestation Λ val_index r confirmed fields h_j J h_F).2 := by
  intro Λ v r c f h_j J h_F
  show (Spec.Protocol.create_attestation Λ v r (c.map Spec.BlockId.toSpec)
      (fieldsToSpec f) h_j (Spec.BlockId.toSpec J) h_F).1 =
    Spec.Protocol.record_attestation Λ (Spec.Attestation.toSpec
      (Spec.Attestation.toProof (Spec.Protocol.create_attestation Λ v r
        (c.map Spec.BlockId.toSpec) (fieldsToSpec f) h_j
        (Spec.BlockId.toSpec J) h_F).2))
  rw [record_attestation_toSpec_toProof]
  rfl

/-- The field `height_pair_cases` of `ValidatorClientFacts` at `Model.spec`: the height pair
    `height_pair Λ fields fp` is empty, or `fields` is `some (h, T, ν)` and the height pair is the
    timeout at `h` or the target `(h, T)`. -/
theorem spec_height_pair_cases : ∀ {Λ : (Model.spec (V := V)).R} (fields : Option (Height × BlockId × Bool)) (fp : Option FinalityPair), (Model.spec (V := V)).height_pair Λ fields fp = .empty ∨
    ∃ (h : Height) (T : BlockId) (ν : Bool), fields = some (h, T, ν) ∧
    ((Model.spec (V := V)).height_pair Λ fields fp = .timeout h ∨
    (Model.spec (V := V)).height_pair Λ fields fp = .target h T) := by
  intro Λ fields fp
  rw [height_pair_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).height_pair_cases
    (Λ := (Spec.SigningHistory.toProof Λ).legacy) fields fp

/-- The field `create_attestation_lock_mono` of `ValidatorClientFacts` at `Model.spec`: if the
    record `Λ` holds the lock `T` at height `h`, the record `create_attestation` returns from `Λ`
    still holds the lock `T` at `h`. -/
theorem spec_create_attestation_lock_mono : ∀ {Λ : (Model.spec (V := V)).R} {h : Height} {T : BlockId} (hlock : Λ.lock h = some T) (val_index : V) (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height) (J : BlockId) (h_F : Height), ((Model.spec (V := V)).create_attestation Λ val_index r confirmed fields h_j J h_F).1.lock h =
    some T := by
  intro Λ h T hlock v r c f h_j J h_F
  show (Spec.SigningHistory.toProof
    ((Model.spec (V := V)).create_attestation Λ v r c f h_j J h_F).1).legacy.lock h = some T
  rw [create_attestation_fst_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).create_attestation_lock_mono
    (Λ := (Spec.SigningHistory.toProof Λ).legacy) hlock v r c f h_j J h_F

/-- The field `create_attestation_no_self_E1` of `ValidatorClientFacts` at `Model.spec`: if the
    attestation `create_attestation` returns has the height pair target `(h, T)` and the finality
    pair `(h, T')`, then `T = T'`. -/
theorem spec_create_attestation_no_self_E1 : ∀ (Λ : (Model.spec (V := V)).R) (val_index : V) (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height) (J : BlockId) (h_F : Height) {h : Height} {T T' : BlockId} (hhp : ((Model.spec (V := V)).create_attestation Λ val_index r confirmed fields h_j J h_F).2.height_pair =
    HeightPair.target h T) (hfp : ((Model.spec (V := V)).create_attestation Λ val_index r confirmed fields h_j J h_F).2.finality_pair =
    some ⟨h, T'⟩), T = T' := by
  intro Λ v r c f h_j J h_F h T T' hhp hfp
  rw [create_attestation_snd_spec] at hhp hfp
  exact (Model.vocabulary_facts_validatorClient (V := V)).create_attestation_no_self_E1
    (Spec.SigningHistory.toProof Λ).legacy v r c f h_j J h_F hhp hfp

/-- The field `encodeHeight_none` of `ValidatorClientFacts` at `Model.spec`: with no fields,
    `encodeHeight` returns the empty named height pair. -/
theorem spec_encodeHeight_none : ∀ (p : HeightPair), (Model.spec (V := V)).encodeHeight none p = NamedHeightPair.empty := by
  intro p
  rw [encodeHeight_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).encodeHeight_none p

/-- The field `encodeHeight_of_target` of `ValidatorClientFacts` at `Model.spec`:
    `encodeHeight` at the fields `(H, T, nu)` and a target height pair returns the height vote for
    `H` and `T` with timeout bit `false`. -/
theorem spec_encodeHeight_of_target : ∀ {H : Height} {T : BlockId} {nu : Bool} {g : Height} {X : BlockId}, (Model.spec (V := V)).encodeHeight (some (H, T, nu))
    (HeightPair.target g X) = NamedHeightPair.vote H T false := by
  intro H T nu g X
  rw [encodeHeight_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).encodeHeight_of_target

/-- The field `encodeHeight_of_timeout` of `ValidatorClientFacts` at `Model.spec`:
    `encodeHeight` at the fields `(H, T, nu)` and a timeout height pair returns the height vote for
    `H` and `T` with timeout bit `true`. -/
theorem spec_encodeHeight_of_timeout : ∀ {H : Height} {T : BlockId} {nu : Bool} {g : Height}, (Model.spec (V := V)).encodeHeight (some (H, T, nu))
    (HeightPair.timeout g) = NamedHeightPair.vote H T true := by
  intro H T nu g
  rw [encodeHeight_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).encodeHeight_of_timeout

/-- The field `height_pair_eq_target_of_aligned_lock` of `ValidatorClientFacts` at
    `Model.spec`: if the record `Lambda` has no timeout at height `H` and its own lock at `H`
    with `fp` is `T`, the height pair for the fields `(H, T, nu)` is the target `(H, T)`. -/
theorem spec_height_pair_eq_target_of_aligned_lock : ∀ (Lambda : (Model.spec (V := V)).R) {H : Height} {T : BlockId} {nu : Bool} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : (Model.spec (V := V)).own_lock Lambda H fp = some T), (Model.spec (V := V)).height_pair Lambda (some (H, T, nu)) fp = HeightPair.target H T := by
  intro Λ H T nu fp htimeout hlock
  rw [own_lock_spec] at hlock
  rw [height_pair_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).height_pair_eq_target_of_aligned_lock
    (Spec.SigningHistory.toProof Λ).legacy fp htimeout hlock

/-- The field `height_pair_eq_target_of_no_lock_no_target_justifiable` of `ValidatorClientFacts` at
    `Model.spec`: if the record `Lambda` has no timeout, no own lock with `fp` and no target at
    height `H`, the height pair for the fields `(H, T, false)` is the target `(H, T)`. -/
theorem spec_height_pair_eq_target_of_no_lock_no_target_justifiable : ∀ (Lambda : (Model.spec (V := V)).R) {H : Height} {T : BlockId} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : (Model.spec (V := V)).own_lock Lambda H fp = none) (htarget : Lambda.target H = none), (Model.spec (V := V)).height_pair Lambda (some (H, T, false)) fp = HeightPair.target H T := by
  intro Λ H T fp htimeout hlock htarget
  rw [own_lock_spec] at hlock
  rw [height_pair_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).height_pair_eq_target_of_no_lock_no_target_justifiable
    (Spec.SigningHistory.toProof Λ).legacy fp htimeout hlock htarget

/-- The field `height_pair_eq_target_of_no_lock_recorded_target` of `ValidatorClientFacts` at
    `Model.spec`: if the record `Lambda` has no timeout and no own lock with `fp` at height
    `H`, and the target `T` at `H`, the height pair for the fields `(H, T, nu)` is the target
    `(H, T)`. -/
theorem spec_height_pair_eq_target_of_no_lock_recorded_target : ∀ (Lambda : (Model.spec (V := V)).R) {H : Height} {T : BlockId} {nu : Bool} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : (Model.spec (V := V)).own_lock Lambda H fp = none) (htarget : Lambda.target H = some T), (Model.spec (V := V)).height_pair Lambda (some (H, T, nu)) fp = HeightPair.target H T := by
  intro Λ H T nu fp htimeout hlock htarget
  rw [own_lock_spec] at hlock
  rw [height_pair_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).height_pair_eq_target_of_no_lock_recorded_target
    (Spec.SigningHistory.toProof Λ).legacy fp htimeout hlock htarget

/-- The field `height_pair_eq_timeout_of_no_lock_no_target_nonjustifiable` of `ValidatorClientFacts`
    at `Model.spec`: if the record `Lambda` has no timeout, no own lock with `fp` and no target
    at height `H`, the height pair for the fields `(H, T, true)` is the timeout at `H`. -/
theorem spec_height_pair_eq_timeout_of_no_lock_no_target_nonjustifiable : ∀ (Lambda : (Model.spec (V := V)).R) {H : Height} {T : BlockId} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : (Model.spec (V := V)).own_lock Lambda H fp = none) (htarget : Lambda.target H = none), (Model.spec (V := V)).height_pair Lambda (some (H, T, true)) fp = HeightPair.timeout H := by
  intro Λ H T fp htimeout hlock htarget
  rw [own_lock_spec] at hlock
  rw [height_pair_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).height_pair_eq_timeout_of_no_lock_no_target_nonjustifiable
    (Spec.SigningHistory.toProof Λ).legacy fp htimeout hlock htarget

/-- The field `height_pair_eq_timeout_of_no_lock_off_target_record` of `ValidatorClientFacts` at
    `Model.spec`: if the record `Lambda` has no timeout and no own lock with `fp` at height
    `H`, and a target `recorded` other than `T` at `H`, the height pair for the fields `(H, T, nu)`
    is the timeout at `H`. -/
theorem spec_height_pair_eq_timeout_of_no_lock_off_target_record : ∀ (Lambda : (Model.spec (V := V)).R) {H : Height} {T recorded : BlockId} {nu : Bool} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = false) (hlock : (Model.spec (V := V)).own_lock Lambda H fp = none) (htarget : Lambda.target H = some recorded) (hne : recorded ≠ T), (Model.spec (V := V)).height_pair Lambda (some (H, T, nu)) fp = HeightPair.timeout H := by
  intro Λ H T recorded nu fp htimeout hlock htarget hne
  rw [own_lock_spec] at hlock
  rw [height_pair_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).height_pair_eq_timeout_of_no_lock_off_target_record
    (Spec.SigningHistory.toProof Λ).legacy fp htimeout hlock htarget hne

/-- The field `height_pair_eq_timeout_of_timeout` of `ValidatorClientFacts` at `Model.spec`: if
    the record `Lambda` has a timeout at height `H`, the height pair for the fields `(H, T, nu)` and
    `fp` is the timeout at `H`. -/
theorem spec_height_pair_eq_timeout_of_timeout : ∀ (Lambda : (Model.spec (V := V)).R) {H : Height} {T : BlockId} {nu : Bool} (fp : Option FinalityPair) (htimeout : Lambda.timeout H = true), (Model.spec (V := V)).height_pair Lambda (some (H, T, nu)) fp = HeightPair.timeout H := by
  intro Λ H T nu fp htimeout
  rw [height_pair_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).height_pair_eq_timeout_of_timeout
    (Spec.SigningHistory.toProof Λ).legacy fp htimeout

/-- The field `create_attestation_snd_finality_pair` of `ValidatorClientFacts` at `Model.spec`:
    the finality pair of the attestation `create_attestation` returns is
    `finality_pair Λ h_j J h_F`. -/
theorem spec_create_attestation_snd_finality_pair : ∀ (Λ : (Model.spec (V := V)).R) (val_index : V) (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height) (J : BlockId) (h_F : Height), ((Model.spec (V := V)).create_attestation Λ val_index r confirmed fields h_j J h_F).2.finality_pair =
    (Model.spec (V := V)).finality_pair Λ h_j J h_F := by
  intro Λ v r c f h_j J h_F
  rw [create_attestation_snd_spec, finality_pair_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).create_attestation_snd_finality_pair
    (Spec.SigningHistory.toProof Λ).legacy v r c f h_j J h_F

/-- The field `own_lock_some_self` of `ValidatorClientFacts` at `Model.spec`: with the finality
    pair `(h, J)`, the own lock at height `h` is `J`. -/
theorem spec_own_lock_some_self : ∀ (Λ : (Model.spec (V := V)).R) (h : Height) (J : BlockId), (Model.spec (V := V)).own_lock Λ h (some ⟨h, J⟩) = some J := by
  intro Λ h J
  rw [own_lock_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).own_lock_some_self
    (Spec.SigningHistory.toProof Λ).legacy h J

/-- The field `finality_pair_height` of `ValidatorClientFacts` at `Model.spec`: if
    `finality_pair Λ h_j J h_F` is `(h, T)`, then `h_j = h`. -/
theorem spec_finality_pair_height : ∀ {Λ : (Model.spec (V := V)).R} {h_j : Height} {J : BlockId} {h_F h : Height} {T : BlockId} (hp : (Model.spec (V := V)).finality_pair Λ h_j J h_F = some ⟨h, T⟩), h_j = h := by
  intro Λ h_j J h_F h T hp
  rw [finality_pair_spec] at hp
  exact (Model.vocabulary_facts_validatorClient (V := V)).finality_pair_height hp

/-- The field `finality_pair_target` of `ValidatorClientFacts` at `Model.spec`: if
    `finality_pair Λ h_j J h_F` is `(h, T)`, then `J = T`. -/
theorem spec_finality_pair_target : ∀ {Λ : (Model.spec (V := V)).R} {h_j : Height} {J : BlockId} {h_F h : Height} {T : BlockId} (hp : (Model.spec (V := V)).finality_pair Λ h_j J h_F = some ⟨h, T⟩), J = T := by
  intro Λ h_j J h_F h T hp
  rw [finality_pair_spec] at hp
  exact (Model.vocabulary_facts_validatorClient (V := V)).finality_pair_target hp

/-- The field `encodeHeight_empty` of `ValidatorClientFacts` at `Model.spec`: `encodeHeight`
    writes the empty height pair as the empty named height pair, whatever the fields. -/
theorem spec_encodeHeight_empty : ∀ (fields : Option (Height × BlockId × Bool)), (Model.spec (V := V)).encodeHeight fields HeightPair.empty = NamedHeightPair.empty := by
  intro fields
  rw [encodeHeight_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).encodeHeight_empty fields

/-- The field `encodeHeight_vote_inv_l85c` of `ValidatorClientFacts` at `Model.spec`:
    `encodeHeight` at the fields `(h, e, ν)` gives a vote at `(H, e')` only when `h = H` and
    `e = e'`. -/
theorem spec_encodeHeight_vote_inv_l85c : ∀ {h H : Height} {e e' : BlockId} {ν b : Bool} {p : HeightPair} (hp : (Model.spec (V := V)).encodeHeight (some (h, e, ν)) p = .vote H e' b), h = H ∧ e = e' := by
  intro h H e e' ν b p hp
  rw [encodeHeight_spec] at hp
  exact (Model.vocabulary_facts_validatorClient (V := V)).encodeHeight_vote_inv_l85c hp

/-- The field `fields_of_encodeHeight_vote` of `ValidatorClientFacts` at `Model.spec`: if
    `encodeHeight` returns a height vote for `h₀` and `entry`, the fields were `some (h₀, entry, b)`
    for some `b`. -/
theorem spec_fields_of_encodeHeight_vote : ∀ (fields : Option (Height × BlockId × Bool)) (pair : HeightPair) {h₀ : Height} {entry : BlockId} {tmo : Bool} (h : (Model.spec (V := V)).encodeHeight fields pair = NamedHeightPair.vote h₀ entry tmo), ∃ b : Bool, fields = some (h₀, entry, b) := by
  intro fields pair h₀ entry tmo h
  rw [encodeHeight_spec] at h
  exact (Model.vocabulary_facts_validatorClient (V := V)).fields_of_encodeHeight_vote fields pair h

/-- The field `height_pair_cases_l85c` of `ValidatorClientFacts` at `Model.spec`: at the fields
    `(H, e, ν)` the height pair is the target `(H, e)`; or the timeout at `H`, and then the record
    times `H` out, records a target other than `e` at `H`, or `ν` is set; or empty, and then the own
    lock at `H` names a block other than `e`. -/
theorem spec_height_pair_cases_l85c : ∀ (Λ : (Model.spec (V := V)).R) (H : Height) (e : BlockId) (ν : Bool) (fp : Option FinalityPair), (Model.spec (V := V)).height_pair Λ (some (H, e, ν)) fp = .target H e ∨
    ((Model.spec (V := V)).height_pair Λ (some (H, e, ν)) fp = .timeout H ∧
    (Λ.timeout H = true ∨ (∃ rec, Λ.target H = some rec ∧ rec ≠ e) ∨ ν = true)) ∨
    ((Model.spec (V := V)).height_pair Λ (some (H, e, ν)) fp = .empty ∧
    ∃ locked, (Model.spec (V := V)).own_lock Λ H fp = some locked ∧ locked ≠ e) := by
  intro Λ H e ν fp
  rw [height_pair_spec, own_lock_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).height_pair_cases_l85c
    (Spec.SigningHistory.toProof Λ).legacy H e ν fp

/-- The field `own_lock_none` of `ValidatorClientFacts` at `Model.spec`: with no finality pair,
    the own lock at height `h` is `Λ.lock h`. -/
theorem spec_own_lock_none : ∀ (Λ : (Model.spec (V := V)).R) (h : Height), (Model.spec (V := V)).own_lock Λ h none = Λ.lock h := by
  intro Λ h
  rw [own_lock_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).own_lock_none
    (Spec.SigningHistory.toProof Λ).legacy h

/-- The field `own_lock_some_of_ne` of `ValidatorClientFacts` at `Model.spec`: with a finality
    pair `p` at a height other than `h`, the own lock at height `h` is `Λ.lock h`. -/
theorem spec_own_lock_some_of_ne : ∀ (Λ : (Model.spec (V := V)).R) (h : Height) {p : FinalityPair} (hp : p.height ≠ h), (Model.spec (V := V)).own_lock Λ h (some p) = Λ.lock h := by
  intro Λ h p hp
  rw [own_lock_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).own_lock_some_of_ne
    (Spec.SigningHistory.toProof Λ).legacy h hp

/-- The field `own_lock_some_of_ne_explicit` of `ValidatorClientFacts` at `Model.spec`: with a
    finality pair `p` at a height other than `h`, the own lock at height `h` is `Λ.lock h`. -/
theorem spec_own_lock_some_of_ne_explicit : ∀ (Λ : (Model.spec (V := V)).R) (h : Height) (p : FinalityPair) (hne : ¬ p.height = h), (Model.spec (V := V)).own_lock Λ h (some p) = Λ.lock h := by
  intro Λ h p hne
  rw [own_lock_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).own_lock_some_of_ne_explicit
    (Spec.SigningHistory.toProof Λ).legacy h p hne

/-- The field `own_lock_some_pair_of_ne` of `ValidatorClientFacts` at `Model.spec`: with the
    finality pair `(h', J)` and `h' ≠ h`, the own lock at height `h` is `Λ.lock h`. -/
theorem spec_own_lock_some_pair_of_ne : ∀ (Λ : (Model.spec (V := V)).R) {h h' : Height} (J : BlockId) (hne : h' ≠ h), (Model.spec (V := V)).own_lock Λ h (some ⟨h', J⟩) = Λ.lock h := by
  intro Λ h h' J hne
  rw [own_lock_spec]
  exact (Model.vocabulary_facts_validatorClient (V := V)).own_lock_some_pair_of_ne
    (Spec.SigningHistory.toProof Λ).legacy J hne

/-! ### The field about the round action -/

/-- The field `round_action_height_pair_cases` of `ValidatorClientFacts` at `Model.spec`: the
    round action's height pair is empty when there is no source; otherwise it is empty because the
    record's lock at the source's height names another root, or it is a vote, a target or a timeout
    at the source's height for the root of the block that entered that height. -/
theorem spec_round_action_height_pair_cases : ∀ (contract : (Model.spec (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.spec (V := V)).HS) (record : (Model.spec (V := V)).NR)
    (g : Option (Block V)) (hg : (Model.spec (V := V)).grade2_block_with contract E hc st ((Model.spec (V := V)).round_of hc st.s) ⇢ g)
    (src : Option (Block V)) (hsrc : (Model.spec (V := V)).fg_source_with contract E hc st ((Model.spec (V := V)).round_of hc st.s) g ⇢ src)
    (out : (Model.spec (V := V)).NR × NamedAttestation V) (hout : (Model.spec (V := V)).round_action_with contract E hc nd st record ⇢ out),
    (src = none ∧ out.2.height_pair = NamedHeightPair.empty) ∨
    ∃ Q, src = some Q ∧
      ((∃ locked, record.legacy.timeout (st.σ Q).h = false ∧
          (Model.spec (V := V)).own_lock record.legacy (st.σ Q).h out.2.finality_pair = some locked ∧
          locked ≠ (st.σ Q).T_h.root ∧ out.2.height_pair = NamedHeightPair.empty) ∨
        out.2.height_pair = NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root false ∨
        out.2.height_pair = NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root true) := by
  intro contract E hc nd st record g hg src hsrc out hout
  have hhp := DutiesFacts.spec_named_round_action_height_pair contract E hc nd st record out
    hout g hg src hsrc
  rw [height_pair_spec] at hhp
  cases hs : src with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    rw [hhp, hs, Option.map_none]
    exact DecoupledConsensusModel.Proofs.HealingSurface.encodeHeight_none _
  | some Q =>
    right
    refine ⟨Q, rfl, ?_⟩
    rw [hs, Option.map_some] at hhp
    rw [own_lock_spec]
    simp only [Model.vocabulary] at hhp ⊢
    by_cases htimeout : record.legacy.timeout (st.σ Q).h = true
    · right
      right
      rw [hhp, DecoupledConsensusModel.Proofs.HealingSurface.height_pair_eq_timeout_of_timeout
        (Spec.SigningHistory.toProof record.legacy).legacy out.2.finality_pair htimeout]
      exact DecoupledConsensusModel.Proofs.HealingSurface.encodeHeight_of_timeout
    · have htf : record.legacy.timeout (st.σ Q).h = false := Bool.eq_false_of_not_eq_true htimeout
      cases hlock : DecoupledConsensusModel.Protocol.own_lock
          (Spec.SigningHistory.toProof record.legacy).legacy (st.σ Q).h
          out.2.finality_pair with
      | none =>
        rcases DecoupledConsensusModel.Proofs.HealingSurface.height_pair_target_or_timeout_of_fields_some_and_lock_none_or_aligned
            (Spec.SigningHistory.toProof record.legacy).legacy (st.σ Q).h
            (st.σ Q).T_h.root (st.σ Q).nj out.2.finality_pair (Or.inl hlock) with ht | ht
        · refine Or.inr (Or.inl ?_)
          rw [hhp, ht]
          exact DecoupledConsensusModel.Proofs.HealingSurface.encodeHeight_of_target
        · refine Or.inr (Or.inr ?_)
          rw [hhp, ht]
          exact DecoupledConsensusModel.Proofs.HealingSurface.encodeHeight_of_timeout
      | some locked =>
        by_cases heq : locked = (st.σ Q).T_h.root
        · subst locked
          refine Or.inr (Or.inl ?_)
          rw [hhp, DecoupledConsensusModel.Proofs.HealingSurface.height_pair_eq_target_of_aligned_lock
            (Spec.SigningHistory.toProof record.legacy).legacy out.2.finality_pair htf hlock]
          exact DecoupledConsensusModel.Proofs.HealingSurface.encodeHeight_of_target
        · left
          refine ⟨locked, htf, rfl, heq, ?_⟩
          rw [hhp]
          rw [show DecoupledConsensusModel.Protocol.height_pair
              (Spec.SigningHistory.toProof record.legacy).legacy
              (some ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj)) out.2.finality_pair =
              HeightPair.empty by
            simp [DecoupledConsensusModel.Protocol.height_pair, hlock, heq]
            exact htf]
          exact spec_encodeHeight_empty _

end SpecRecord.ValidatorClientFacts

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `Model.spec` satisfies `ValidatorClientRunFacts`, which has no field. -/
theorem Model.spec_runFacts_validatorClient :
    ValidatorClientRunFacts (Model.spec (V := V)) where

end DecoupledConsensusModel.Sts.Record
