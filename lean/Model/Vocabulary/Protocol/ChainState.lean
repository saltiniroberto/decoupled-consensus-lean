module
public import Model.Vocabulary.Objects.Time
public import Model.Vocabulary.Objects.Identifiers
public import Model.Vocabulary.Objects.Parameters
public import Model.Vocabulary.Objects.Blocks
public import Model.Vocabulary.Objects.Weights
public import Model.Vocabulary.Objects.NamedBlocks

@[expose] public section

/-!
# Chain state

The chain state `σ` with its quorum reads, the transition that folds a block's attestations
(`process_attestation`, `process_height_events`, `advance_height`), and the slashing conditions E1
and E2 on attestations.
-/

section
/-! ## Slashing conditions and equivocation -/

namespace DecoupledConsensusModel

namespace Protocol

/-- A height pair `(h,T')` conflicts with a nonempty finality pair `(h,T)` when the heights agree
    and `T' ≠ T`, `T' = ⊥` included; the empty height pair conflicts with nothing. -/
def conflictsWithFinality : HeightPair → FinalityPair → Bool
  | .empty, _ => false
  | .timeout height, pair => decide (height = pair.height)
  | .target height target, pair =>
      decide (height = pair.height) && !decide (target = pair.target)

variable {V : Type} [DecidableEq V]

/-- Two attestations come from the same validator. -/
def sameValidator (left right : CombinedAttestation V) : Bool :=
  decide (left.val_index = right.val_index)

/-- Two attestations are for the same round. -/
def sameRound (left right : CombinedAttestation V) : Bool :=
  decide (left.round = right.round)

/-- E1's field conflict: one attestation's finality pair conflicts with the other's height pair, in
    either direction; `left = right` is allowed. -/
def e1Fields (left right : CombinedAttestation V) : Bool :=
  left.finality_pair.elim false (conflictsWithFinality right.height_pair) ||
    right.finality_pair.elim false (conflictsWithFinality left.height_pair)

/-- E2's field conflict: two target height pairs `(h,T)` and `(h,T')` with `T ≠ T'`; a timeout or
    empty pair on either side is not a conflict. -/
def e2Fields (left right : CombinedAttestation V) : Bool :=
  match left.height_pair, right.height_pair with
  | .target leftHeight leftTarget, .target rightHeight rightTarget =>
      decide (leftHeight = rightHeight) && !decide (leftTarget = rightTarget)
  | _, _ => false

/-- E1: two attestations of one validator where one finality pair is `(h,T)` and one height pair is
    `(h,T')` with `T' ≠ T`, `T' = ⊥` included. -/
def e1Slashable (left right : CombinedAttestation V) : Bool :=
  sameValidator left right && e1Fields left right

/-- E2: two attestations of one validator whose height pairs are `(h,T)` and `(h,T')` with
    `T,T' ≠ ⊥` and `T ≠ T'`. -/
def e2Slashable (left right : CombinedAttestation V) : Bool :=
  sameValidator left right && e2Fields left right

/-- Two attestations are slashable under E1 or E2. -/
def slashable (left right : CombinedAttestation V) : Bool :=
  e1Slashable left right || e2Slashable left right

/-- A single attestation is slashable on its own. -/
def selfSlashable (a : CombinedAttestation V) : Bool :=
  slashable a a

/-- Two attestations of one validator in one round with different SG votes. -/
def sgHeadEquivocation (left right : CombinedAttestation V) : Bool :=
  sameValidator left right && sameRound left right &&
    !decide (left.confirmed = right.confirmed)

/-- `e1Slashable` as a proposition. -/
def E1Slashable (left right : CombinedAttestation V) : Prop :=
  e1Slashable left right = true

/-- `e2Slashable` as a proposition. -/
def E2Slashable (left right : CombinedAttestation V) : Prop :=
  e2Slashable left right = true

/-- `slashable` as a proposition. -/
def Slashable (left right : CombinedAttestation V) : Prop :=
  slashable left right = true

/-- `sgHeadEquivocation` as a proposition. -/
def SGHeadEquivocation (left right : CombinedAttestation V) : Prop :=
  sgHeadEquivocation left right = true

instance (left right : CombinedAttestation V) : Decidable (Slashable left right) :=
  inferInstanceAs (Decidable (slashable left right = true))

instance (left right : CombinedAttestation V) :
    Decidable (E1Slashable left right) :=
  inferInstanceAs (Decidable (e1Slashable left right = true))

instance (left right : CombinedAttestation V) :
    Decidable (E2Slashable left right) :=
  inferInstanceAs (Decidable (e2Slashable left right = true))

instance (left right : CombinedAttestation V) :
    Decidable (SGHeadEquivocation left right) :=
  inferInstanceAs (Decidable (sgHeadEquivocation left right = true))

/-- At most one member of `xs` per key. -/
def atMostOnePer {α β : Type} [DecidableEq β] (key : α → β) (xs : List α) : Prop :=
  ∀ k : β, (xs.filter (fun x => decide (key x = k))).length ≤ 1

/-- The honest emission budget over one validator's emissions: at most one proposal per slot, one
    Goldfish vote per slot, and one combined attestation per round. -/
def HonestEmissionBudget (blocks : List (Block V))
    (gf_votes : List (GoldfishVote V))
    (attestations : List (CombinedAttestation V)) : Prop :=
  atMostOnePer Block.slot blocks ∧
    atMostOnePer GoldfishVote.slot gf_votes ∧
      atMostOnePer CombinedAttestation.round attestations

end Protocol

end DecoupledConsensusModel
end

section
/-! ## Chain state -/

namespace DecoupledConsensusModel

namespace Protocol

/-- The height parameters `K ≥ 4`, `D ≥ 2`, and the timeout delay `δ_t` in slots. -/
structure HeightConfig where
  /-- `K`: the nonjustifiable period. -/
  K : Nat
  /-- `D`: the finality-debt bound. -/
  D : Nat
  /-- `δ_t`: the delay, in slots, before a progress quorum that can contain timeout rows is
      consumed. -/
  timeoutDelay : Nat
  /-- `K ≥ 4`. -/
  K_ge_four : 4 ≤ K
  /-- `D ≥ 2`. -/
  D_ge_two : 2 ≤ D

namespace HeightConfig

end HeightConfig

/-- A chain state
    `σ = (L, s, h, T_h, nj, target_participation, progress, finalize, J, h_j, F, h_F)`. -/
structure ChainState (V : Type) where
  /-- `L`: the latest block. -/
  L : Block V
  /-- `s = L.slot`, the slot of the latest block. -/
  s : Slot
  /-- `h`: the current height. -/
  h : Height
  /-- `T_h`: the block that carried the transition into height `h`. -/
  T_h : Block V
  /-- `nj`: the nonjustifiable flag, computed when the chain enters `h` and fixed until the height
      changes. -/
  nj : Bool
  /-- The target participation, as a set of validators. -/
  target_participation : Finset V
  /-- The progress participation, as a set of validators. -/
  progress : Finset V
  /-- The finality participation, as a set of validators. -/
  finalize : Finset V
  /-- `J`: the latest justified block on the chain. -/
  J : Block V
  /-- `h_j`: the height of `J`. -/
  h_j : Height
  /-- `F`: the latest finalized block on the chain. -/
  F : Block V
  /-- `h_F`: the height of `F`. -/
  h_F : Height
deriving DecidableEq

namespace ChainState

variable {V : Type}

/-- The initial chain state: `L`, `T_h`, `J` and `F` are the genesis block, `s = 0`, `h = 1`,
    `h_j = h_F = 0`, `nj = false`, and the participation sets are empty. -/
def initial : ChainState V :=
  { L := .genesis
    s := 0
    h := 1
    T_h := .genesis
    nj := false
    target_participation := ∅
    progress := ∅
    finalize := ∅
    J := .genesis
    h_j := 0
    F := .genesis
    h_F := 0 }

/-- `Q_target(σ)`, the target participation set. -/
def Q_target (σ : ChainState V) : Finset V :=
  σ.target_participation

/-- `Q_prog(σ)`, the progress participation set. -/
def Q_prog (σ : ChainState V) : Finset V :=
  σ.progress

/-- `Q_finality(σ)`, the finality participation set. -/
def Q_finality (σ : ChainState V) : Finset V :=
  σ.finalize

variable [DecidableEq V] [Fintype V]

/-- `w(Q_target(σ)) ≥ q`. -/
def targetQuorum (E : Env V) (σ : ChainState V) : Bool :=
  E.electorate.quorumCheck σ.Q_target

/-- `w(Q_prog(σ)) ≥ q`. -/
def progQuorum (E : Env V) (σ : ChainState V) : Bool :=
  E.electorate.quorumCheck σ.Q_prog

/-- `w(Q_finality(σ)) ≥ q`. -/
def finalityQuorum (E : Env V) (σ : ChainState V) : Bool :=
  E.electorate.quorumCheck σ.Q_finality

end ChainState

end Protocol

end DecoupledConsensusModel
end

section
/-! ## The state transition -/

namespace DecoupledConsensusModel

namespace Protocol

/-- The nonjustifiability rule `nj ← (K | h) ∧ (h − h_F > D)`, with truncated subtraction. -/
def nonjustifiable (cfg : HeightConfig) (h h_F : Height) : Bool :=
  decide (cfg.K ∣ h) && decide (cfg.D < h - h_F)

section Attestations

variable {V : Type} [DecidableEq V]

/-- `process_attestation(σ, a)`: adds `a`'s validator to the finality set when `h_F < h_j` and `a`'s
    finality pair is `(h_j, J)`; adds it to the target and progress sets when `a`'s height pair is
    the target vote `(h, T_h)`, and to the progress set alone when it is the timeout vote `(h, ⊥)`. -/
def process_attestation (σ : ChainState V) (a : CombinedAttestation V) :
    ChainState V :=
  let i := a.val_index
  let afterFinality :=
    if decide (σ.h_F < σ.h_j) &&
        decide (a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) then
      { σ with finalize := insert i σ.finalize }
    else σ
  if a.height_pair = .target σ.h σ.T_h.root then
    { afterFinality with
      target_participation := insert i afterFinality.target_participation
      progress := insert i afterFinality.progress }
  else if a.height_pair = .timeout σ.h then
    { afterFinality with progress := insert i afterFinality.progress }
  else afterFinality

end Attestations

section Transition

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The finality condition of `process_height_events`: `h_F < h_j` and `Q_finality` is a quorum. -/
def finalityReady (E : Env V) (σ : ChainState V) : Bool :=
  decide (σ.h_F < σ.h_j) && σ.finalityQuorum E

/-- The justification condition: `nj` is false and `Q_target` is a quorum. -/
def targetReady (E : Env V) (σ : ChainState V) : Bool :=
  !σ.nj && σ.targetQuorum E

/-- The progress condition: `Q_target` is a quorum, or `Q_prog` is a quorum and
    `T_h.slot + δ_t ≤ s`. -/
def progReady (E : Env V) (cfg : HeightConfig) (σ : ChainState V) : Bool :=
  σ.targetQuorum E ||
    (decide (σ.T_h.slot + cfg.timeoutDelay ≤ σ.s) && σ.progQuorum E)

/-- `advance_height(σ)`: increments the height, sets `T_h ← L`, recomputes `nj` from the new height
    and `h_F`, and clears the target and progress sets; the finality set is kept. -/
def advance_height (cfg : HeightConfig) (σ : ChainState V) : ChainState V :=
  let next := σ.h + 1
  { σ with
    h := next
    T_h := σ.L
    nj := nonjustifiable cfg next σ.h_F
    target_participation := ∅
    progress := ∅ }

/-- `process_height_events(σ)`: finalize `J` when the finality condition holds; then justify `T_h`
    at height `h` and advance when the justification condition holds, or else advance when the
    progress condition holds. -/
def process_height_events (E : Env V) (cfg : HeightConfig) (σ : ChainState V) :
    ChainState V :=
  let afterFinality :=
    if finalityReady E σ then { σ with F := σ.J, h_F := σ.h_j } else σ
  if targetReady E afterFinality then
    advance_height cfg
      { afterFinality with
        J := afterFinality.T_h
        h_j := afterFinality.h
        finalize := ∅ }
  else if progReady E cfg afterFinality then
    advance_height cfg afterFinality
  else afterFinality

end Transition

end Protocol

end DecoupledConsensusModel
end

section
/-! ## Interpreting height pairs -/
namespace DecoupledConsensusModel.Protocol

/-- A reading of an arbitrary row type as attestations: a base attestation, and a height pair read
    against the chain state. -/
structure TimeoutBinding (V Row : Type) where
  base : Row → CombinedAttestation V
  heightPair : ChainState V → Row → HeightPair

namespace TimeoutBinding
variable {V Row : Type}

/-- The attestation a row is read as: its base attestation with the height pair the binding reads
    from `st`. -/
def view (binding : TimeoutBinding V Row) (st : ChainState V) (row : Row) :
    CombinedAttestation V :=
  { binding.base row with height_pair := binding.heightPair st row }

end TimeoutBinding

/-- `process_attestation` applied to the attestation the binding reads from `row`. -/
def process_attestation_with {V Row : Type} [DecidableEq V]
    (binding : TimeoutBinding V Row) (st : ChainState V) (row : Row) : ChainState V :=
  process_attestation st (binding.view st row)

end DecoupledConsensusModel.Protocol
end

section
namespace DecoupledConsensusModel.Protocol

namespace TimeoutBinding

/-- The height pair of a named attestation read against `st`: its erased height pair when it is a
    vote at `st.h` naming `st.T_h.root`, the empty pair otherwise. -/
def targetedHeightPair {V : Type} (st : ChainState V) (row : NamedAttestation V) : HeightPair :=
  if row.height_pair.matchesEntry st.h st.T_h.root then row.height_pair.erase else .empty

def targeted (V : Type) : TimeoutBinding V (NamedAttestation V) where
  base := NamedAttestation.erase
  heightPair := targetedHeightPair

end TimeoutBinding
end DecoupledConsensusModel.Protocol
end

section
namespace DecoupledConsensusModel.Protocol
variable {V Row : Type} [DecidableEq V] [Fintype V]

def fold_rows (binding : TimeoutBinding V Row) (st : ChainState V)
    (geometry : Block V) (rows : List Row) : ChainState V :=
  { rows.foldl (process_attestation_with binding) { st with s := geometry.slot }
      with L := geometry }

def transition_rows (binding : TimeoutBinding V Row) (E : Env V) (cfg : HeightConfig)
    (st : ChainState V) (geometry : Block V) (rows : List Row) : ChainState V :=
  process_height_events E cfg (fold_rows binding st geometry rows)

/-- The chain-state transition of a named block, reading its own attestations through the targeted
    height-pair binding. -/
def named_transition (E : Env V) (cfg : HeightConfig) (st : ChainState V)
    (B : NamedBlock V) : ChainState V :=
  transition_rows (TimeoutBinding.targeted V) E cfg st B.erase B.attestations

/-- The chain state of a named block, obtained by applying `named_transition` along its chain from
    genesis. -/
def derive_named (E : Env V) (cfg : HeightConfig) : NamedBlock V → ChainState V
  | .genesis => .initial
  | B@(.node p _ _ _ _ _ _) => named_transition E cfg (derive_named E cfg p) B

end DecoupledConsensusModel.Protocol
end

end
