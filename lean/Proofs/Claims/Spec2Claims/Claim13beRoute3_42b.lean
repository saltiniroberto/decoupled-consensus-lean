import Proofs.Claims.Spec2Claims.Claim13beRoute3_42
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Definitions over a family of validator sets

The `On` forms of the definitions that read a run's honest set. Each takes a family
`Hs : Int → Finset V`, read at the instant of each use, or a plain set `X` or `Xb` where the use has
no instant.
-/

set_option autoImplicit false

/-- Closes an `Iff` between two structures whose fields agree definitionally once the listed
    equations have rewritten the nested structures. -/
syntax "twin_iff" ("[" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| twin_iff) =>
    `(tactic| (constructor <;> intro h <;> cases h <;> constructor <;> assumption))
  | `(tactic| twin_iff [$ls,*]) =>
    `(tactic| (constructor <;> intro h <;> cases h <;> constructor <;>
        (try simp only [$ls,*] at *) <;> assumption))

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Collisions, run blocks, slashing, attestations in play and certificates -/

/-- The run blocks of `rho` read through `Xb` have no two distinct blocks with one root on their
    chains, and a proposer's root for its slot is new. -/
structure RootCollisionFreeOn (S : Setup V) (rho : NamedRun V) (Xb : Finset V) : Prop where
  root_injective : ∀ B C : NamedBlock V,
    blockInRunOn S rho Xb B → blockInRunOn S rho Xb C →
    ∀ A D : NamedBlock V,
      (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
      (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D
  /-- When the run has the tick of slot `s`'s proposer at `s`'s proposal instant, no body the
      proposer holds just before that tick has the root its node gives slot `s`. -/
  honest_roots_new : ∀ (s : Slot) (j : Nat),
    rho.events[j]? = some (.tick (S.E.proposer s) (proposal_time S.E s)) →
    ∀ B ∈ (NamedRun.stateBefore S rho j (S.E.proposer s)).st.bodies,
      B.root ≠ (S.node (S.E.proposer s)).new_root s

/-- Some run block of `rho`, read through `Xb`, erases to `B`. -/
def RunBlockOfOn (S : Setup V) (rho : Run V) (Xb : Finset V) (B : Block V) : Prop :=
  ∃ D : NamedBlock V, D.erase = B ∧ RunBlockOn S rho Xb D

/-- `HasSlashableWeightBetween` holds between the chain attestations of no two run blocks of `ρ`
    read through `Xb`. -/
def SlashableBoundOn (S : Setup V) (ρ : Run V) (Xb : Finset V) : Prop :=
  ∀ B₁ B₂ : NamedBlock V, RunBlockOn S ρ Xb B₁ → RunBlockOn S ρ Xb B₂ →
    ¬HasSlashableWeightBetween S.E (chain_attestations B₁.erase) (chain_attestations B₂.erase)

/-- `a` is delivered in `ρ`, or is on the chain of some run block of `ρ` read through `Xb`. -/
def RunAttestationOn (S : Setup V) (ρ : Run V) (Xb : Finset V) (a : NamedAttestation V) :
    Prop :=
  Object.attest a ∈ NamedRun.objects ρ ∨
    ∃ B : NamedBlock V, RunBlockOn S ρ Xb B ∧ a ∈ named_chain_attestations B

/-- Some set `Q` of weight at least `q` has, for each member, an attestation in play in `ρ` (read
    through `Xb`) by that member voting for target `T` at height `h`. -/
def CertificateOn (S : Setup V) (ρ : Run V) (Xb : Finset V) (h : Height) (T : BlockId) :
    Prop :=
  ∃ Q : Finset V, S.E.q ≤ S.E.electorate.weightOf Q ∧
    ∀ v ∈ Q, ∃ a : NamedAttestation V, RunAttestationOn S ρ Xb a ∧
      a.val_index = v ∧ a.height_pair = NamedHeightPair.vote h T false

/-- Some subset `Q` of `X`, whose weight plus the weight outside `X` reaches `q`, has for each
    member an emitted attestation with target `T` at height `h`. -/
def CompletableOn (S : Setup V) (ρ : Run V) (X : Finset V) (h : Height) (T : BlockId) :
    Prop :=
  ∃ Q ⊆ X,
    S.E.q ≤ S.E.electorate.weightOf Q + S.E.electorate.weightOf (Finset.univ \ X) ∧
      ∀ v ∈ Q, ∃ (a : NamedAttestation V) (t : Time),
        Run.emits S ρ v (Object.attest a) t ∧ T ∈ targetsAt a.erase h

/-- At each height, at most one target is `CompletableOn` for `X`. -/
def PerHeightCompletabilityOn (S : Setup V) (ρ : Run V) (X : Finset V) : Prop :=
  ∀ (h : Height) (T T' : BlockId), CompletableOn S ρ X h T → CompletableOn S ρ X h T' → T = T'

/-- No member of `X` emits two attestations with different targets at one height. -/
def HonestNoDoubleTargetOn (S : Setup V) (ρ : Run V) (X : Finset V) : Prop :=
  ∀ v ∈ X, ∀ (a a' : NamedAttestation V) (t t' : Time),
    Run.emits S ρ v (Object.attest a) t → Run.emits S ρ v (Object.attest a') t' →
      ∀ (h : Height) (T T' : BlockId), T ∈ targetsAt a.erase h → T' ∈ targetsAt a'.erase h →
        T = T'

/-! ## Heights read over a set -/

/-- The largest `h_max` of the stores at `t` of the members of `Hs t`; `0` when `Hs t` is empty. -/
noncomputable def honestHMaxAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (t : Time) : Height :=
  (Hs t).sup fun v => (Run.storeAt S rho v t).core.h_max

/-- The largest `h_max` of the stores of the members of `X` after the first `n` events. -/
noncomputable def honestHMaxBeforeIndexOn (S : Setup V) (rho : Run V) (X : Finset V)
    (n : Nat) : Height :=
  X.sup fun v => (Run.stateBefore S rho n v).st.h_max

/-- The largest finalized height of any body held by a member of `X` after the first `n` events. -/
noncomputable def recoveryPrefixFinalityHeightOn (S : Setup V) (rho : Run V) (X : Finset V)
    (n : Nat) : Height :=
  X.sup fun v =>
    (Run.stateBefore S rho n v).st.bodies.sup fun B => (derive_named S.E S.cfg B).h_F

/-- Every body held by a member of `X` after the first `n` events has finalized height at most
    `hF0`. -/
def HonestPrefixFinalityCapOn (S : Setup V) (rho : Run V) (X : Finset V) (n : Nat)
    (hF0 : Height) : Prop :=
  ∀ v ∈ X, ∀ B ∈ (Run.stateBefore S rho n v).st.bodies, (derive_named S.E S.cfg B).h_F ≤ hF0

/-- Every body held by a member of `X` after the first `n` events has the `nj` bit at height
    `blocked` and no justification at `blocked`. -/
def HonestPrefixNJUniverseOn (S : Setup V) (rho : Run V) (X : Finset V) (n : Nat)
    (blocked : Height) : Prop :=
  ∀ v ∈ X, ∀ B ∈ (Run.stateBefore S rho n v).st.bodies,
    ((derive_named S.E S.cfg B).h = blocked → (derive_named S.E S.cfg B).nj = true) ∧
      (derive_named S.E S.cfg B).h_j ≠ blocked

/-- No member of `Hs t` whose tick at `t` is among the first `n` events emits there an attestation
    with a height pair at `blocked`. -/
def NoLocalHeightPairBeforeOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (n : Nat)
    (blocked : Height) : Prop :=
  ∀ {i : Nat} {v : V} {t : Time} {a : NamedAttestation V},
    i < n → v ∈ Hs t → rho.events[i]? = some (Event.tick v t) →
      Object.attest a ∈ NamedRun.emittedAt S rho i v t → a.height_pair.erase.height? ≠ some blocked

/-- `lag` is positive, and from round `r0` on, every round whose `lag` following rounds end within
    the horizon sees `honestHMaxAtOn` rise by the end of those rounds. -/
def EventualHeightProgressFromOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (r0 lag : Round) : Prop :=
  0 < lag ∧ ∀ r : Round, r0 ≤ r → S.a (r + lag) ≤ rho.horizon →
    honestHMaxAtOn S rho Hs (S.a r) < honestHMaxAtOn S rho Hs (S.a (r + lag))

/-- Every member of `Hs (vote_time s)` has, after every prefix of the events before slot `s`'s vote
    instant, a finalized block that is an ancestor of `B`. -/
def ProposalFinalizedBelowAtDeliveriesOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (s : Slot) (B : NamedBlock V) : Prop :=
  ∀ v ∈ Hs (vote_time S.E s),
    ∀ i ≤ (List.filter (fun (e : Event V) => decide (e.time < vote_time S.E s)) rho.events).length,
      (Run.stateBefore S rho i v).st.core.F ⪯ B.erase

/-- `first` is positive, and before every index less than `first` the largest `h_max` over `X` is at
    most `H`. -/
structure HeightWindowAtOn (S : Setup V) (rho : Run V) (X : Finset V) (H : Height)
    (first : Nat) : Prop where
  positive : 0 < first
  before : ∀ i < first, honestHMaxBeforeIndexOn S rho X i ≤ H

/-- `first` is positive, the largest `h_max` over `X` before index `first` is `H + 1`, and before
    every earlier index it is at most `H`. -/
structure FirstHeightProgressAtOn (S : Setup V) (rho : Run V) (X : Finset V) (H : Height)
    (first : Nat) : Prop where
  positive : 0 < first
  frontier : honestHMaxBeforeIndexOn S rho X first = H + 1
  before : ∀ i < first, honestHMaxBeforeIndexOn S rho X i ≤ H

/-- Some member of `X` holds, after the first `n` events, a run block (read through `Xb`) at height
    `blocked + 2` with an ancestor run block at height `blocked`, both held. -/
def PrefixHeightCrossingWitnessOn (S : Setup V) (rho : Run V) (X Xb : Finset V) (n : Nat)
    (blocked : Height) : Prop :=
  ∃ v ∈ X, ∃ (carrier : NamedBlock V) (anchor : NamedBlock V),
    carrier ∈ (Run.stateBefore S rho n v).st.bodies ∧
      anchor ∈ (Run.stateBefore S rho n v).st.bodies ∧
        RunBlockOn S rho Xb carrier ∧ RunBlockOn S rho Xb anchor ∧
          anchor.Preceq carrier ∧
            (derive_named S.E S.cfg anchor).h = blocked ∧
              (derive_named S.E S.cfg carrier).h = blocked + 2

/-! ## Round voters -/

/-- The members of `Hs (S.a k)` that emitted in round `k`. -/
def honestRoundVotersOn (S : Setup V) (rho : NamedRun V) (Hs : Int → Finset V) (k : Round) :
    Finset V :=
  (Hs (S.a k)).filter (fun v => NamedOutageEntry.emittedInRound S rho v k)

/-- The union, over the rounds `k` from `r − η_SG` to `r − 2`, of the round-`k` voters in
    `Hs (S.a k)`. -/
def historicalHonestVotersOn (S : Setup V) (rho : NamedRun V) (Hs : Int → Finset V)
    (r : Round) : Finset V :=
  ((Finset.range r).filter (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r)).biUnion
    (fun k => honestRoundVotersOn S rho Hs k)

/-- The voters of `historicalHonestVotersOn` for `r` that did not vote in round `r − 1`. -/
def staleHistoricalVotersOn (S : Setup V) (rho : NamedRun V) (Hs : Int → Finset V)
    (r : Round) : Finset V :=
  historicalHonestVotersOn S rho Hs r \ honestRoundVotersOn S rho Hs (r - 1)

/-- The weight outside `X` together with the stale historical voters of `r` is less than the weight
    of the round-`(r − 1)` voters inside `X`. -/
def GradeFormingMajorityOn (S : Setup V) (rho : NamedRun V) (Hs : Int → Finset V)
    (X : Finset V) (r : Round) : Prop :=
  S.E.electorate.weightOf (Finset.univ \ X ∪ staleHistoricalVotersOn S rho Hs r) <
    S.E.electorate.weightOf (honestRoundVotersOn S rho Hs (r - 1) ∩ X)

/-- Every member `w` of `Hs` at round `r + 1`'s phase-`p` domain instant has, in its interpreted
    inputs and its tree, the round-`r` action carrier of every round-`r` voter still in `Hs` at
    round `r + 1`'s early phase-`p` cutoff. -/
def RelativeCarrierWindowAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round)
    (p : Phase) : Prop :=
  ∀ w ∈ Hs (domain S.E S.hc (r + 1) p),
    ∀ u ∈ honestRoundVotersOn S rho Hs r, u ∈ Hs (early S.E S.hc (r + 1) p) →
      ∃ y ∈ interpretedInputs (relativePhaseRead S rho r p w).st.core.toHealing.gradeView
            (relativePhaseRead S rho r p w).st.core.F S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p) u,
        y.round = r ∧
          y.confirmed = some (actionSGBlockAt S rho u r).root ∧
            Block.find? (relativePhaseRead S rho r p w).st.core.T (actionSGBlockAt S rho u r).root =
              some (actionSGBlockAt S rho u r)

/-! ## Votes and heads -/

/-- Every member of slot `s`'s committee in `Hs (vote_time s)` emitted, at slot `s`'s vote instant,
    a vote whose head is a run block (read through `Xb`) satisfying `tgt`. -/
def NamedHonestVotesConeOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (s : Slot) (tgt : Block V → Prop) : Prop :=
  ∀ x ∈ Hs (vote_time S.E s), x ∈ S.E.committee s →
    ∃ X : NamedBlock V, tgt X.erase ∧ blockInRunOn S rho Xb X ∧
      NamedRun.emits S rho x (NamedObject.gfVote { val_index := x, slot := s, head := X.erase.root })
        (vote_time S.E s)

/-- Every member of slot `s`'s committee in `Hs (vote_time s)` emitted, at slot `s`'s vote instant,
    the vote naming `B`. -/
def NamedHonestVotesNameOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (s : Slot)
    (B : Block V) : Prop :=
  ∀ v ∈ Hs (vote_time S.E s), v ∈ S.E.committee s →
    NamedRun.emits S rho v (NamedObject.gfVote { val_index := v, slot := s, head := B.root })
      (vote_time S.E s)

/-- Some member of slot `s`'s committee in `Hs (confirmation_time s)` emitted, at slot `s`'s vote
    instant, the vote whose head is `head`, a run block read through `Xb`. -/
def NamedHonestHeadOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (s : Slot) (head : NamedBlock V) : Prop :=
  ∃ x ∈ Hs (confirmation_time S.E s), x ∈ S.E.committee s ∧ RunBlockOn S rho Xb head ∧
    Run.emits S rho x (Object.gfVote { val_index := x, slot := s, head := head.erase.root })
      (vote_time S.E s)

/-- Some member of slot `s`'s committee in `Hs (confirmation_time s)` voted, at slot `s`'s vote
    instant, for `X`, the erasure of a run block read through `Xb`. -/
def HonestHeadOn (S : Setup V) (ρ : Run V) (Hs : Int → Finset V) (Xb : Finset V) (s : Slot)
    (X : Block V) : Prop :=
  ∃ x ∈ Hs (confirmation_time S.E s), x ∈ S.E.committee s ∧
    (∃ C : NamedBlock V, C.erase = X ∧ RunBlockOn S ρ Xb C) ∧
      Run.emits S ρ x (Object.gfVote { val_index := x, slot := s, head := X.root })
        (vote_time S.E s)

/-- Some head of `NamedHonestHeadOn` for slot `s` is a descendant of `C` with height at least
    `M − 1`. -/
def ThinHonestHeadAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (M : Height) (s : Slot) (C : Block V) : Prop :=
  ∃ head : NamedBlock V, NamedHonestHeadOn S rho Hs Xb s head ∧ C ⪯ head.erase ∧
    M - 1 ≤ (derive_named S.E S.cfg head).h

/-- Every head of `HonestHeadOn` for slot `s` is found by its root in `T` and stamped in `tb` before
    slot `s`'s support cutoff. -/
def HeadsResolveInOn (S : Setup V) (ρ : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (s : Slot) (T : Finset (Block V)) (tb : TimestampMap (Block V)) : Prop :=
  ∀ X : Block V, HonestHeadOn S ρ Hs Xb s X →
    Block.find? T X.root = some X ∧ stampedBefore tb (support_cutoff S.E s) X = true

/-- Every head of `HonestHeadOn` for slot `s` is genesis or admitted by `v` before `Gamma`. -/
def HonestHeadsAvailableBeforeOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (s : Slot) (v : V) (Gamma : Time) : Prop :=
  ∀ X : Block V, HonestHeadOn S rho Hs Xb s X → X = Block.genesis ∨ AdmittedBefore S rho v X Gamma

/-- Every member of slot `s`'s committee in `Hs (vote_time s)` has a vote store whose walk extends
    to the proposal `B`. -/
def VoteStoresExtendOn (S : Setup V) (ρ : Run V) (Hs : Int → Finset V) (s : Slot)
    (B : NamedBlock V) : Prop :=
  ∀ v ∈ Hs (vote_time S.E s), v ∈ S.E.committee s →
    ∃ (tree₀ : Finset (Block V)) (H : Block V), NamedVoteStoreExtends S ρ v s tree₀ H B

/-- Every member of slot `s`'s committee in `Hs (vote_time s)` has a vote store at slot `s`
    extending to `B`, and emits at slot `s`'s vote instant the vote its duty computes. -/
def VoteTickExtendsOn (S : Setup V) (ρ : Run V) (Hs : Int → Finset V) (s : Slot)
    (B : NamedBlock V) : Prop :=
  ∀ v ∈ Hs (vote_time S.E s), v ∈ S.E.committee s →
    ∃ (tree₀ : Finset (Block V)) (H : Block V) (u : GoldfishVote V),
      let n := NamedRecoveryRead.voteDutyRead S ρ v s
      n.st.core.s = s ∧
        NamedVoteStoreExtends S ρ v s tree₀ H B ∧
          (NamedDuties.goldfish_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc
            (S.node v) n.st).2 = some u ∧
            NamedRun.emits S ρ v (NamedObject.gfVote u) (vote_time S.E s)

/-- For every member `v` of `Hs (S.a r)`, every committee member of slot `s` in `Hs` at its vote
    instant votes for a descendant of `v`'s round-`r` action carrier. -/
def NamedSGTargetConeCanonicalityOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (r : Round) (s : Slot) : Prop :=
  ∀ v ∈ Hs (S.a r), NamedHonestVotesConeOn S rho Hs Xb s fun X => actionSGBlockAt S rho v r ⪯ X

/-- For every member `v` of `Hs (S.a r)`, every committee member of slot `s` in `Hs` at its vote
    instant votes for a descendant of `v`'s round-`r` action carrier; the same body as
    `NamedSGTargetConeCanonicalityOn`. -/
def SGTargetConeCanonicalityOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (r : Round) (s : Slot) : Prop :=
  ∀ v ∈ Hs (S.a r), NamedHonestVotesConeOn S rho Hs Xb s fun X => actionSGBlockAt S rho v r ⪯ X

/-- `SGTargetConeCanonicalityOn` holds, and every run block of height at least `K` that slot `s`'s
    committee votes into has as an ancestor the finality root of every member of
    `Hs (vote_time (s + 1))` at slot `s + 1`'s vote duty. -/
structure SGTargetOpeningConeRootLockOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (K : Height) (r : Round) (s : Slot) : Prop where
  canonical : SGTargetConeCanonicalityOn S rho Hs Xb r s
  coneRootLock : ∀ {B : NamedBlock V}, RunBlockOn S rho Xb B →
    K ≤ (derive_named S.E S.cfg B).h →
    (NamedHonestVotesConeOn S rho Hs Xb s fun X => B.erase ⪯ X) →
    ∀ v ∈ Hs (vote_time S.E (s + 1)),
      get_fg_root (NamedRecoveryRead.voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG ⪯
        B.erase

/-- Every grade-1 block of a member of `Hs` at round `r + 1`'s grade-1 domain instant is voted into
    by slot `s`'s committee, and any two such blocks are compatible. -/
structure NamedG1ConcentrationOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (r : Round) (s : Slot) : Prop where
  supported : ∀ {w : V} {B : Block V}, w ∈ Hs (domain S.E S.hc (r + 1) Phase.g1) →
    namedG1At S rho w (r + 1) B → NamedHonestVotesConeOn S rho Hs Xb s fun X => B ⪯ X
  compatible : ∀ {w₁ w₂ : V} {B₁ B₂ : Block V},
    w₁ ∈ Hs (domain S.E S.hc (r + 1) Phase.g1) → w₂ ∈ Hs (domain S.E S.hc (r + 1) Phase.g1) →
      namedG1At S rho w₁ (r + 1) B₁ → namedG1At S rho w₂ (r + 1) B₂ → B₁.compatible B₂ = true

/-- Conditions on `w`'s store read at slot `s + 1`'s vote instant that relate its voter views, its
    SG root and its head to `B` and to the votes `source` counts at slot `s`; the head is a run
    block read through `Xb`, and `w` emits the vote its duty computes. -/
structure NamedNextVoteAdoptionOn (S : Setup V) (rho : Run V) (Xb : Finset V)
    (source : Store V) (s : Slot) (B : Block V) (w : V) : Prop where
  transport :
    let read :=
      NamedActionReads.confirmationReadFrom S (Run.stateBeforeTime S rho (vote_time S.E (s + 1)) w)
        (vote_time S.E (s + 1))
    AdoptionTransport source.T read.st.core.T (confVotes S.E source s) (confLate S.E source s)
      (voter_view S.E read.st.core.toHealing.toGoldfishStore read.st.core.s)
      (voter_support_view S.E read.st.core.toHealing.toGoldfishStore read.st.core.s) B
  support_subset :
    let read :=
      NamedActionReads.confirmationReadFrom S (Run.stateBeforeTime S rho (vote_time S.E (s + 1)) w)
        (vote_time S.E (s + 1))
    voter_support_view S.E read.st.core.toHealing.toGoldfishStore read.st.core.s ⊆
      voter_view S.E read.st.core.toHealing.toGoldfishStore read.st.core.s
  anchor :
    let read :=
      NamedActionReads.confirmationReadFrom S (Run.stateBeforeTime S rho (vote_time S.E (s + 1)) w)
        (vote_time S.E (s + 1))
    (get_sg_root_with (NamedProfile.gradeContract read.cache) S.E S.hc read.st.core.toHealing
      (S.hc.round_of read.st.core.s)).compatible B = true
  path :
    let read :=
      NamedActionReads.confirmationReadFrom S (Run.stateBeforeTime S rho (vote_time S.E (s + 1)) w)
        (vote_time S.E (s + 1))
    get_sg_root_with (NamedProfile.gradeContract read.cache) S.E S.hc read.st.core.toHealing
        (S.hc.round_of read.st.core.s) ⪯ B →
      ∀ C : Block V,
        get_sg_root_with (NamedProfile.gradeContract read.cache) S.E S.hc read.st.core.toHealing
            (S.hc.round_of read.st.core.s) ⪯ C →
          C ≠ get_sg_root_with (NamedProfile.gradeContract read.cache) S.E S.hc
              read.st.core.toHealing (S.hc.round_of read.st.core.s) →
            C ⪯ B → C ∈ voter_filtered_block_tree S.E read.st.core read.st.core.s
  run :
    let read :=
      NamedActionReads.confirmationReadFrom S (Run.stateBeforeTime S rho (vote_time S.E (s + 1)) w)
        (vote_time S.E (s + 1))
    ∃ C : NamedBlock V,
      C.erase =
          get_head_in_tree_with_layer (NamedProfile.gradeContract read.cache) S.E S.hc
            read.st.core.toHealing (voter_filtered_block_tree S.E read.st.core read.st.core.s)
            (voter_view S.E read.st.core.toHealing.toGoldfishStore read.st.core.s)
            (voter_support_view S.E read.st.core.toHealing.toGoldfishStore read.st.core.s)
            (read.st.core.s - 1) ∧
        RunBlockOn S rho Xb C
  emit : ∀ u : GoldfishVote V,
    let read :=
      NamedActionReads.confirmationReadFrom S (Run.stateBeforeTime S rho (vote_time S.E (s + 1)) w)
        (vote_time S.E (s + 1))
    (NamedDuties.goldfish_vote_with (NamedProfile.gradeContract read.cache) S.E S.hc (S.node w)
        read.st).2 = some u →
      Run.emits S rho w (Object.gfVote u) (vote_time S.E (s + 1))

/-! ## Action carriers, grades and deliveries -/

/-- Every member of `Hs (domain r .g2)` has `C` active and graded 2 in its read at that instant. -/
def NamedGradeFormsAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round)
    (C : Block V) : Prop :=
  ∀ v ∈ Hs (domain S.E S.hc r Phase.g2),
    C ∈ PhaseGrades.filteredTree (PhaseGrades.readAt S rho (domain S.E S.hc r Phase.g2) v) ∧
      PhaseGrades.storeGrade S.E S.hc (PhaseGrades.readAt S rho (domain S.E S.hc r Phase.g2) v).st
        r Phase.g2 C = true

/-- `P` is an ancestor of the round-`r` action carrier of every member of `Hs (S.a r)`. -/
def ActionCarriersCoverOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round)
    (P : Block V) : Prop :=
  ∀ v ∈ Hs (S.a r), P ⪯ actionSGBlockAt S rho v r

/-- The round-`r` action carriers of any two members of `Hs (S.a r)` are compatible. -/
def HonestActionCarriersOneChainAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (r : Round) : Prop :=
  ∀ u ∈ Hs (S.a r), ∀ v ∈ Hs (S.a r),
    (actionSGBlockAt S rho u r).compatible (actionSGBlockAt S rho v r) = true

/-- Every block a member of `Hs (S.a r)` selects at grade 2 is, at the round-`r` action read of
    every member of `Hs (S.a r)`, an ancestor of its finality root or in its filtered tree. -/
def SelectedG2SettledAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) :
    Prop :=
  ∀ u ∈ Hs (S.a r), ∀ Q : Block V, PhaseGrades.nodeQ2 S (actionReadAt S rho u r) r = some Q →
    ∀ w ∈ Hs (S.a r), FinalityFilterNoninterferenceAtRead S rho w (S.a r) Q

/-- Every grade-1 block of a member of `Hs (domain r .g1)` is, at the round-`r` action read of every
    member of `Hs (S.a r)`, an ancestor of its finality root or in its filtered tree. -/
def NamedLiveG1SettledAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) :
    Prop :=
  ∀ u ∈ Hs (domain S.E S.hc r Phase.g1), ∀ B : Block V, namedG1At S rho u r B →
    ∀ w ∈ Hs (S.a r), FinalityFilterNoninterferenceAtRead S rho w (S.a r) B

/-- The round-`(r − 1)` action carrier of every member of `Hs (S.a (r − 1))` does not interfere at
    the round-`r` action read of any member of `Hs (S.a r)`. -/
def PreviousActionCarriersQuietAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (r : Round) : Prop :=
  ∀ u ∈ Hs (S.a (r - 1)), ∀ w ∈ Hs (S.a r),
    FinalityFilterNoninterferenceAtRead S rho w (S.a r) (actionSGBlockAt S rho u (r - 1))

/-- Every member of `Hs (S.a r)` that emits its round-`r` attestation has an action carrier
    compatible with `B`. -/
def HonestSGEmissionsCompatibleAtRoundOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (r : Round) (B : Block V) : Prop :=
  ∀ v ∈ Hs (S.a r), Run.emits S rho v (Object.attest (actionAttestationAt S rho v r)) (S.a r) →
    (actionSGBlockAt S rho v r).compatible B = true

/-- The round-`r` attestation of every member of `X` is covered by the chain of `B`'s parent or
    included in `B`, and votes for target `T` at height `H`. -/
def NamedTargetedHonestActionProposalCoverageAtOn (S : Setup V) (rho : Run V)
    (X : Finset V) (r : Round) (B : NamedBlock V) (H : Height) (T : BlockId) : Prop :=
  let sigma := derive_named S.E S.cfg B.parent
  ∀ v ∈ X,
    (actionAttestationAt S rho v r ∈ named_chain_attestations B.parent ∧
          v ∈ sigma.progress ∧
            ((actionAttestationAt S rho v r).height_pair = NamedHeightPair.vote H T false →
              v ∈ sigma.target_participation) ∨
        actionAttestationAt S rho v r ∈ B.attestations) ∧
      ((actionAttestationAt S rho v r).height_pair = NamedHeightPair.vote H T false ∨
        (actionAttestationAt S rho v r).height_pair = NamedHeightPair.vote H T true)

/-- A clean action read of `P` at round `r`: after `t_GST`, with the cutoff `Γ_neg1 (r + 1)` in the
    horizon, `P` is active at every reader of round `r + 1`, and every reader has resolved before
    that cutoff the round-`r` action vote of every author in `Hs (S.a r + S.E.Δ)`, whose head covers
    `P`; each reader is in `Hs` at the instant of its read. -/
structure CleanActionReadForOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round)
    (P : Block V) : Prop where
  post_gst : S.E.t_GST ≤ S.a r
  cutoff_in_horizon : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon
  active : ∀ w ∈ Hs (S.a (r + 1)), P ∈ get_filtered_block_tree (healStoreAt S rho w (r + 1)).toFG
  active_domain : ∀ w ∈ Hs (domain S.E S.hc (r + 1) Phase.g2),
    P ∈ PhaseGrades.filteredTree (relativeG2Read S rho (r + 1) w)
  resolved_support : ∀ w ∈ Hs (S.a (r + 1)), ∀ v ∈ Hs (S.a r + S.E.Δ),
    occurrenceBefore
          (sg_resolution_time (gradeViewAt S rho w (r + 1)).T
            (gradeViewAt S rho w (r + 1)).timestamp_block
            (gradeViewAt S rho w (r + 1)).timestamp_sg_vote (actionSGVoteAt S rho v r))
          (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true ∧
      head_covers (gradeViewAt S rho w (r + 1)).T P (actionSGVoteAt S rho v r).confirmed = true

/-- `C` is active at every member of `Hs (domain r .g2)`, every such reader counts every member of
    `X` as positive for `C`, and every validator such a reader counts as opposing is outside `X`. -/
structure RelativeG2SupportOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (X : Finset V)
    (r : Round) (C : Block V) : Prop where
  active : ∀ v ∈ Hs (domain S.E S.hc r Phase.g2),
    C ∈ PhaseGrades.filteredTree (relativeG2Read S rho r v)
  positive : ∀ w ∈ Hs (domain S.E S.hc r Phase.g2), ∀ v ∈ X, relativePositiveAt S rho r w v C = true
  opposing_not_honest : ∀ w ∈ Hs (domain S.E S.hc r Phase.g2), ∀ v : V,
    relativeOpposingAt S rho r w v C = true → v ∉ X

/-! ## Frames -/

/-- At every instant `read` from `S.a lo` to `S.a hi`, every member of `Hs read` has, in its store
    just before `read`, `h_j + 2 ≤ M` and `h_max = M`. -/
def GateOffFrameAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height)
    (lo hi : Round) : Prop :=
  ∀ read : Time, S.a lo ≤ read → read ≤ S.a hi → ∀ w ∈ Hs read,
    (Run.storeBeforeTime S rho w read).core.h_j + 2 ≤ M ∧
      (Run.storeBeforeTime S rho w read).core.h_max = M

/-- The same body as `GateOffFrameAtOn`. -/
def NamedGateOffFrameAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height)
    (lo hi : Round) : Prop :=
  ∀ read : Time, S.a lo ≤ read → read ≤ S.a hi → ∀ w ∈ Hs read,
    (Run.storeBeforeTime S rho w read).core.h_j + 2 ≤ M ∧
      (Run.storeBeforeTime S rho w read).core.h_max = M

/-- The body of `GateOffFrameAtOn`, with the store read without `.core`. -/
def SeedGateOffFrameAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height)
    (lo hi : Round) : Prop :=
  ∀ read : Time, S.a lo ≤ read → read ≤ S.a hi → ∀ w ∈ Hs read,
    (Run.storeBeforeTime S rho w read).h_j + 2 ≤ M ∧ (Run.storeBeforeTime S rho w read).h_max = M

/-- Every member of `Hs (vote_time d)` has, at slot `d`'s vote duty, `h_max = M`, `h_j + 2 ≤ M`, and
    a finality root comparable with `C`. -/
def VoteDutyFrameAtOn' (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height)
    (d : Slot) (C : Block V) : Prop :=
  ∀ w ∈ Hs (vote_time S.E d),
    (voteDutyStore S rho w d).h_max = M ∧
      (voteDutyStore S rho w d).h_j + 2 ≤ M ∧
        (get_fg_root (voteDutyStore S rho w d).toHealing.toFG ⪯ C ∨
          C ⪯ get_fg_root (voteDutyStore S rho w d).toHealing.toFG)

/-- At every vote duty from slot `lo` to `hi + 1` and every confirmation from `lo` to `hi`, every
    member of `Hs` at that instant has `h_max = M` and `h_j + 2 ≤ M`. -/
structure GateOffSeedConeWindowAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (M : Height) (lo hi : Slot) : Prop where
  voteFrontier : ∀ d : Slot, lo ≤ d → d ≤ hi + 1 → ∀ w ∈ Hs (vote_time S.E d),
    (voteDutyStore S rho w d).h_max = M
  voteGateOff : ∀ d : Slot, lo ≤ d → d ≤ hi + 1 → ∀ w ∈ Hs (vote_time S.E d),
    (voteDutyStore S rho w d).h_j + 2 ≤ M
  confirmationFrontier : ∀ s : Slot, lo ≤ s → s ≤ hi → ∀ w ∈ Hs (confirmation_time S.E s),
    (confStore S rho w s).h_max = M
  confirmationGateOff : ∀ s : Slot, lo ≤ s → s ≤ hi → ∀ w ∈ Hs (confirmation_time S.E s),
    (confStore S rho w s).h_j + 2 ≤ M

/-- Every member of `X`, after every prefix of at most `stop` events, has a finalized block that is
    an ancestor of every run block (read through `Xb`) of height at least `blocked` descending from
    `Tprev`. -/
def FinalityFloorAtOn (S : Setup V) (rho : Run V) (X Xb : Finset V) (blocked : Height)
    (stop : Nat) (Tprev : Block V) : Prop :=
  ∀ v ∈ X, ∀ n ≤ stop, ∀ B : NamedBlock V, RunBlockOn S rho Xb B →
    blocked ≤ (derive_named S.E S.cfg B).h → Tprev ⪯ B.erase →
      (Run.stateBefore S rho n v).st.F ⪯ B.erase

/-- `FinalityFloorAtOn` with a named `Tprev`. -/
def NamedFinalityFloorAtOn (S : Setup V) (rho : Run V) (X Xb : Finset V) (blocked : Height)
    (stop : Nat) (Tprev : NamedBlock V) : Prop :=
  ∀ v ∈ X, ∀ n ≤ stop, ∀ B : NamedBlock V, RunBlockOn S rho Xb B →
    blocked ≤ (derive_named S.E S.cfg B).h → Tprev.Preceq B →
      (Run.stateBefore S rho n v).st.core.F ⪯ B.erase

/-- The height-regime frame up to event index `stop`: `FinalityFloorAtOn` for `X`, `Tprev` of height
    at most `blocked`, and conditions tying the height-`(blocked + 1)` blocks of the stores and
    action sources of `X`'s members to `Tprev`. -/
structure HeightRegimeFrameOn (S : Setup V) (rho : Run V) (X Xb : Finset V) (blocked : Height)
    (stop : Nat) (Tprev : Block V) (c0 : Round) : Prop where
  floor : FinalityFloorAtOn S rho X Xb blocked stop Tprev
  prevHeight : (derived_state S.E S.cfg Tprev).h ≤ blocked
  rootBelow : ∀ v ∈ X, ∀ n ≤ stop, ∀ Q ∈ (Run.stateBefore S rho n v).st.T,
    ((Run.stateBefore S rho n v).st.σ Q).h = blocked + 1 → Tprev ⪯ Q →
      get_fg_root (Run.stateBefore S rho n v).st.toHealing.toFG ⪯ Q
  sourceAbove : ∀ p ∈ X, ∀ r : Round, strictEventIndex rho (S.a r) ≤ stop →
    S.a r ≤ rho.horizon → ∀ B : Block V,
      fg_source S.E S.hc (actionStoreAt S rho p r).toHealing r
          (grade2_block S.E S.hc (actionStoreAt S rho p r).toHealing r) = some B →
        (derived_state S.E S.cfg B).h = blocked + 1 → Tprev ⪯ B
  namedSourceAbove : ∀ p ∈ X, ∀ r : Round, strictEventIndex rho (S.a r) ≤ stop →
    S.a r ≤ rho.horizon → ∀ B ∈ (actionStoreAt S rho p r).st.bodies,
      actionFGSource S (actionStoreAt S rho p r) = some B.erase →
        (derive_named S.E S.cfg B).h = blocked + 1 → Tprev ⪯ B.erase

/-- The named form of `HeightRegimeFrameOn`, with `Tprev` a run block read through `Xb` and the
    owner of each round-`r` action store read in `Hs (S.a r)`. -/
structure NamedHeightRegimeFrameOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (X Xb : Finset V) (blocked : Height) (stop : Nat) (Tprev : NamedBlock V) (c0 : Round) :
    Prop where
  floor : NamedFinalityFloorAtOn S rho X Xb blocked stop Tprev
  prevRun : RunBlockOn S rho Xb Tprev
  prevHeight : (derive_named S.E S.cfg Tprev).h ≤ blocked
  rootBelow : ∀ v ∈ X, ∀ n ≤ stop, ∀ Q ∈ (Run.stateBefore S rho n v).st.bodies,
    (derive_named S.E S.cfg Q).h = blocked + 1 → Tprev.Preceq Q →
      get_fg_root (Run.stateBefore S rho n v).st.core.toHealing.toFG ⪯ Q.erase
  sourceAbove : ∀ (p : V) (r : Round), p ∈ Hs (S.a r) → strictEventIndex rho (S.a r) ≤ stop →
    S.a r ≤ rho.horizon → ∀ B ∈ (actionStoreAt S rho p r).st.bodies,
      actionFGSource S (actionStoreAt S rho p r) = some B.erase →
        (derive_named S.E S.cfg B).h = blocked + 1 → Tprev.Preceq B

/-- For every attestation emitted by a member of `Hs (S.a a.round)` before index `first`, targeting
    at height `blocked` a run block `R` that its action store's confirmation witness names: whenever
    the finality-gadget root of a member of `X` whose `h_max` exceeds `blocked` is `R.erase`, `R` is
    an ancestor of `T`. -/
def NamedOldTargetRootBelowRunOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (X Xb : Finset V) (first : Nat) (blocked : Height) (T : NamedBlock V) : Prop :=
  ∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs (S.a a.round) →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
      strictEventIndex rho (S.a a.round) < first →
        ∀ R : NamedBlock V, RunBlockOn S rho Xb R →
          (derive_named S.E S.cfg R).h = blocked →
            a.height_pair.erase = HeightPair.target blocked R.erase.root →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R.erase →
                ∀ w ∈ X, ∀ time : Time,
                  blocked < (Run.storeBeforeTime S rho w time).h_max →
                    get_fg_root (Run.storeBeforeTime S rho w time).core.toHealing.toFG = R.erase →
                      R.Preceq T

/-- An attestation emitted at event `index`, from `start` to `stop`, by a member of `Hs actionTime`
    at its action instant, whose action finality-gadget source `selectedBlock` has height
    `blocked + 1` and checkpoint `checkpoint`, and which the committee of the round's first or
    second slot votes into. -/
structure PrefixFGSelectorConeAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (start stop : Nat) (blocked : Height) (index : Nat)
    (attestation : NamedAttestation V) (actionTime : Time) (selectedBlock : NamedBlock V)
    (checkpoint : Block V) : Prop where
  startLeIndex : start ≤ index
  indexLtStop : index < stop
  signerHonest : attestation.val_index ∈ Hs actionTime
  exactTick : rho.events[index]? = some (Event.tick attestation.val_index actionTime)
  tickOutput : Object.attest attestation ∈
    NamedRun.emittedAt S rho index attestation.val_index actionTime
  emitted : NamedRun.emits S rho attestation.val_index (Object.attest attestation) actionTime
  actionTime_eq : actionTime = S.a attestation.round
  exactAction : attestation = actionAttestationAt S rho attestation.val_index attestation.round
  exactFGSource : actionFGSource S (actionStoreAt S rho attestation.val_index attestation.round) =
    some selectedBlock.erase
  sourceMem : selectedBlock ∈
    (actionStoreAt S rho attestation.val_index attestation.round).st.bodies
  sourceStoredHeight :
    ((actionStoreAt S rho attestation.val_index attestation.round).st.core.σ
      selectedBlock.erase).h = blocked + 1
  sourceDerivedHeight : (derive_named S.E S.cfg selectedBlock).h = blocked + 1
  checkpointStored : checkpoint =
    ((actionStoreAt S rho attestation.val_index attestation.round).st.core.σ
      selectedBlock.erase).T_h
  checkpointDerived : checkpoint = (derive_named S.E S.cfg selectedBlock).T_h
  targetOrTimeout : attestation.height_pair.erase = HeightPair.target (blocked + 1) checkpoint.root ∨
    attestation.height_pair.erase = HeightPair.timeout (blocked + 1)
  cone : (NamedHonestVotesConeOn S rho Hs Xb (S.hc.opening_slot attestation.round)
      fun X => selectedBlock.erase ⪯ X) ∨
    NamedHonestVotesConeOn S rho Hs Xb (S.hc.opening_slot attestation.round + 1)
      fun X => selectedBlock.erase ⪯ X

/-- The base of the height regime from round `r0`: `X`'s largest `h_max` first reaches `blocked + 1`
    at index `first` after being less than `blocked` at `r0`'s action instant,
    `NamedHeightRegimeFrameOn` holds from the first round of a height-`(blocked + 1)` vote, and
    conditions on the roots that old targets at height `blocked` leave. -/
structure NamedHeightRegimeBaseOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (X Xb : Finset V) (r0 : Round) (blocked : Height) (first : Nat) (Tprev : NamedBlock V) :
    Prop where
  crossing : FirstHeightProgressAtOn S rho X (blocked + 1) first
  start : honestHMaxBeforeIndexOn S rho X (inclusiveEventIndex rho (S.a r0)) < blocked
  positive : 1 ≤ blocked
  frame : ∀ c : Round,
    (∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs ta →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
        a.height_pair.erase.height? = some (blocked + 1) → c ≤ a.round) →
      NamedHeightRegimeFrameOn S rho Hs X Xb blocked (first - 1) Tprev c
  oldRoot : ∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs (S.a a.round) →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
      strictEventIndex rho (S.a a.round) < first →
        ∀ R : NamedBlock V, (derive_named S.E S.cfg R).h = blocked →
          a.height_pair.erase = HeightPair.target blocked R.erase.root →
            fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R.erase →
              ∀ w ∈ X, ∀ time : Time,
                blocked < (Run.storeBeforeTime S rho w time).h_max →
                  get_fg_root (Run.storeBeforeTime S rho w time).core.toHealing.toFG = R.erase →
                    ∀ Y : NamedBlock V, RunBlockOn S rho Xb Y →
                      (derive_named S.E S.cfg Y).h = blocked + 1 → Tprev.Preceq Y → R.Preceq Y

/-- `NamedHeightRegimeBaseOn` with each old target root itself a run block read through `Xb`. -/
structure NamedHeightRegimeBaseRunOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (X Xb : Finset V) (r0 : Round) (blocked : Height) (first : Nat) (Tprev : NamedBlock V) :
    Prop where
  crossing : FirstHeightProgressAtOn S rho X (blocked + 1) first
  start : honestHMaxBeforeIndexOn S rho X (inclusiveEventIndex rho (S.a r0)) < blocked
  positive : 1 ≤ blocked
  frame : ∀ c : Round,
    (∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs ta →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
        a.height_pair.erase.height? = some (blocked + 1) → c ≤ a.round) →
      NamedHeightRegimeFrameOn S rho Hs X Xb blocked (first - 1) Tprev c
  oldRoot : ∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs (S.a a.round) →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
      strictEventIndex rho (S.a a.round) < first →
        ∀ R : NamedBlock V, RunBlockOn S rho Xb R → (derive_named S.E S.cfg R).h = blocked →
          a.height_pair.erase = HeightPair.target blocked R.erase.root →
            fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R.erase →
              ∀ w ∈ X, ∀ time : Time,
                blocked < (Run.storeBeforeTime S rho w time).h_max →
                  get_fg_root (Run.storeBeforeTime S rho w time).core.toHealing.toFG = R.erase →
                    ∀ Y : NamedBlock V, RunBlockOn S rho Xb Y →
                      (derive_named S.E S.cfg Y).h = blocked + 1 → Tprev.Preceq Y → R.Preceq Y

/-- The height regime at attestation `a`: `PrefixFGSelectorConeAtOn` for `a`, the frame and the
    height window, a grade-1 block for every member of `Hs` at the round's grade-1 domain instant,
    `NamedOldTargetRootBelowRunOn`, and `a.round` minimal among the rounds of height-`(blocked + 1)`
    votes. -/
structure NamedHeightRegimeRunOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (X Xb : Finset V) (r0 : Round) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
    (ta : Time) (Cfg T Tprev : NamedBlock V) (c0 : Round) : Prop where
  seed : PrefixFGSelectorConeAtOn S rho Hs Xb (inclusiveEventIndex rho (S.a r0)) first blocked i a
    ta Cfg T.erase
  checkpointPreceq : T.Preceq Cfg
  checkpointErase : T.erase = (derive_named S.E S.cfg Cfg).T_h
  crossing : HeightWindowAtOn S rho X (blocked + 1) first
  frame : NamedHeightRegimeFrameOn S rho Hs X Xb blocked (first - 1) Tprev c0
  c0le : c0 ≤ a.round
  ready : GradeRoundReady S rho a.round
  postPrev : S.E.t_GST ≤ S.a (a.round - 1)
  g1 : ∀ w ∈ Hs (domain S.E S.hc a.round Phase.g1), ∃ Q : Block V, namedG1At S rho w a.round Q
  pred : NamedOldTargetRootBelowRunOn S rho Hs X Xb first blocked T
  minimal : ∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ Hs tb →
    NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) → a.round ≤ b.round

end DecoupledConsensusModel.Sts
