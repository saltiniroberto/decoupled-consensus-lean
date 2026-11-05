module
public import GoldilocksCorrectness.Record.Model

@[expose] public section

/-!
# The dot spellings of the record's readers

Over a model `M`, a reader of a chain state, a pending pair, a lock entry or a node state is a
member applied to the value: `M.cs_h σ`, `M.le_B e`, `M.tree n`. Each abbreviation here spells
that read as a field of the value: over the record `σ.h` is `M.cs_h σ`, `e.B` is `M.le_B e`,
`n.v` is `M.validator n`, `n.tree` is `M.tree n`, and `n.votesHeld s` is `M.votesHeld n s`.
Each is reducible: a statement written with the spelling and one written with the member are the
same term up to unfolding an abbreviation.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open DC (DRE)
open Goldilocks (Block Attestation AttestationContent GoldfishVote Frame BlockId Height Slot Time
  Stamp Occurrence)

variable {V : Type} [DecidableEq V] [Fintype V]

-- BEGIN GENERATED spellings
/-- `n.v` is `M.validator n`: the validator the node runs as.
    Read aloud: the validator of `n`. -/
abbrev GoldilocksModel.N.v {M : GoldilocksModel V} (n : M.N) :
    V :=
  M.validator n

/-- `n.t` is `M.clock n`: the node's clock.
    Read aloud: the clock of `n`. -/
abbrev GoldilocksModel.N.t {M : GoldilocksModel V} (n : M.N) :
    Time :=
  M.clock n

/-- `n.awakeSince` is `M.awakeSince n`: the time since which the node has been awake without
    interruption, or none between a wake and the first tick after it.
    Read aloud: the time `n` has been awake since. -/
abbrev GoldilocksModel.N.awakeSince {M : GoldilocksModel V} (n : M.N) :
    Option Time :=
  M.awakeSince n

/-- `n.tree` is `M.tree n`: the blocks the node has accepted.
    Read aloud: the accepted blocks of `n`. -/
abbrev GoldilocksModel.N.tree {M : GoldilocksModel V} (n : M.N) :
    Finset (Block V) :=
  M.tree n

/-- `n.finalized` is `M.finalized n`: the block the node has finalized.
    Read aloud: the finalized block of `n`. -/
abbrev GoldilocksModel.N.finalized {M : GoldilocksModel V} (n : M.N) :
    Block V :=
  M.finalized n

/-- `n.justified` is `M.justified n`: the justified block the node holds.
    Read aloud: the justified block of `n`. -/
abbrev GoldilocksModel.N.justified {M : GoldilocksModel V} (n : M.N) :
    Block V :=
  M.justified n

/-- `n.justifiedHeight` is `M.justifiedHeight n`: the height at which `justified n` was justified.
    Read aloud: the justification height of `n`. -/
abbrev GoldilocksModel.N.justifiedHeight {M : GoldilocksModel V} (n : M.N) :
    Height :=
  M.justifiedHeight n

/-- `n.attestationsHeld` is `M.attestationsHeld n`: every attestation the node has received, one
    copy of each, in the order of first acceptance.
    Read aloud: the attestations `n` has received. -/
abbrev GoldilocksModel.N.attestationsHeld {M : GoldilocksModel V} (n : M.N) :
    List (Attestation V) :=
  M.attestationsHeld n

/-- `n.votesHeld` is `M.votesHeld n`: the Goldfish votes of slot `s` the node has admitted, in the
    order of admission.
    Read aloud: `n`'s votes of slot `s`. -/
abbrev GoldilocksModel.N.votesHeld {M : GoldilocksModel V} (n : M.N) (s : Slot) :
    List (GoldfishVote V) :=
  M.votesHeld n s

/-- `n.voteStamp` is `M.voteStamp n`: the time the node admitted the Goldfish vote `vote`, or none.
    Read aloud: the time `n` admitted `vote`. -/
abbrev GoldilocksModel.N.voteStamp {M : GoldilocksModel V} (n : M.N) (vote : GoldfishVote V) :
    Option Stamp :=
  M.voteStamp n vote

/-- `n.blockStamp` is `M.blockStamp n`: the time the node admitted the block `B`, or none.
    Read aloud: the time `n` admitted `B`. -/
abbrev GoldilocksModel.N.blockStamp {M : GoldilocksModel V} (n : M.N) (B : Block V) :
    Option Stamp :=
  M.blockStamp n B

/-- `n.savedConfirmation` is `M.savedConfirmation n`: the confirmation the node's update of slot `s`
    computed, or none.
    Read aloud: `n`'s saved confirmation of slot `s`. -/
abbrev GoldilocksModel.N.savedConfirmation {M : GoldilocksModel V} (n : M.N) (s : Slot) :
    Option (Block V) :=
  M.savedConfirmation n s

/-- `n.lockEntries` is `M.lockEntries n`: the lock entries the node holds.
    Read aloud: the lock entries of `n`. -/
abbrev GoldilocksModel.N.lockEntries {M : GoldilocksModel V} (n : M.N) :
    Finset M.LE :=
  M.lockEntries n

/-- `n.fastBlocks` is `M.fastBlocks n`: the blocks the node's latest confirmation update locked by
    its fast test.
    Read aloud: the fast blocks of `n`. -/
abbrev GoldilocksModel.N.fastBlocks {M : GoldilocksModel V} (n : M.N) :
    Finset (Block V) :=
  M.fastBlocks n

/-- `n.latestConfirmed` is `M.latestConfirmed n`: the node's record of the confirmed tip.
    Read aloud: the record of `n`'s confirmed tip. -/
abbrev GoldilocksModel.N.latestConfirmed {M : GoldilocksModel V} (n : M.N) :
    Block V :=
  M.latestConfirmed n

/-- `n.sentTarget` is `M.sentTarget n`: the first target the node sent at the height `h`, or none.
    Read aloud: `n`'s target at `h`. -/
abbrev GoldilocksModel.N.sentTarget {M : GoldilocksModel V} (n : M.N) (h : Height) :
    Option BlockId :=
  M.sentTarget n h

/-- `n.sentTimeout` is `M.sentTimeout n`: whether the node sent a timeout at the height `h`.
    Read aloud: `n` sent a timeout at `h`. -/
abbrev GoldilocksModel.N.sentTimeout {M : GoldilocksModel V} (n : M.N) (h : Height) :
    Bool :=
  M.sentTimeout n h

/-- `n.sentLock` is `M.sentLock n`: the target of the node's first finality pair at the height `h`,
    or none.
    Read aloud: `n`'s lock at `h`. -/
abbrev GoldilocksModel.N.sentLock {M : GoldilocksModel V} (n : M.N) (h : Height) :
    Option BlockId :=
  M.sentLock n h

/-- `n.sentAttestations` is `M.sentAttestations n`: the contents of the attestations the node has
    sent.
    Read aloud: the attestations `n` has sent. -/
abbrev GoldilocksModel.N.sentAttestations {M : GoldilocksModel V} (n : M.N) :
    Finset AttestationContent :=
  M.sentAttestations n

/-- `σ.L` is `M.cs_L σ`: the latest block of the chain state `σ`.
    Read aloud: the latest block of `σ`. -/
abbrev GoldilocksModel.CS.L {M : GoldilocksModel V} (σ : M.CS) :
    Block V :=
  M.cs_L σ

/-- `σ.s` is `M.cs_s σ`: the slot of the latest block of `σ`.
    Read aloud: the slot of `σ`. -/
abbrev GoldilocksModel.CS.s {M : GoldilocksModel V} (σ : M.CS) :
    Slot :=
  M.cs_s σ

/-- `σ.h` is `M.cs_h σ`: the current height of `σ`.
    Read aloud: the height of `σ`. -/
abbrev GoldilocksModel.CS.h {M : GoldilocksModel V} (σ : M.CS) :
    Height :=
  M.cs_h σ

/-- `σ.T_h` is `M.cs_T_h σ`: the block that took the chain into the height `cs_h σ`.
    Read aloud: the block that took `σ` into its height. -/
abbrev GoldilocksModel.CS.T_h {M : GoldilocksModel V} (σ : M.CS) :
    Block V :=
  M.cs_T_h σ

/-- `σ.target_participation` is `M.cs_target_participation σ`: the validators whose target vote at
    the current height for `cs_T_h σ` has been counted.
    Read aloud: the validators counted for the target at `σ`'s height. -/
abbrev GoldilocksModel.CS.target_participation {M : GoldilocksModel V} (σ : M.CS) :
    Finset V :=
  M.cs_target_participation σ

/-- `σ.progress` is `M.cs_progress σ`: the validators whose target vote or timeout at the current
    height for `cs_T_h σ` has been counted.
    Read aloud: the validators counted for a target or a timeout at `σ`'s height. -/
abbrev GoldilocksModel.CS.progress {M : GoldilocksModel V} (σ : M.CS) :
    Finset V :=
  M.cs_progress σ

/-- `σ.pending_finality` is `M.cs_pending_finality σ`: the justifications of `σ` not yet finalized,
    in increasing order of height.
    Read aloud: the pending justifications of `σ`. -/
abbrev GoldilocksModel.CS.pending_finality {M : GoldilocksModel V} (σ : M.CS) :
    List M.PP :=
  M.cs_pending_finality σ

/-- `σ.finality_participation` is `M.cs_finality_participation σ`: the validators counted for the
    pending justification of height `j`.
    Read aloud: the validators counted for finalizing the justification of height `j`. -/
abbrev GoldilocksModel.CS.finality_participation {M : GoldilocksModel V} (σ : M.CS) (j : Height) :
    Finset V :=
  M.cs_finality_participation σ j

/-- `σ.J` is `M.cs_J σ`: the latest justified block of `σ`.
    Read aloud: the justified block of `σ`. -/
abbrev GoldilocksModel.CS.J {M : GoldilocksModel V} (σ : M.CS) :
    Block V :=
  M.cs_J σ

/-- `σ.h_j` is `M.cs_h_j σ`: the height at which `cs_J σ` was justified.
    Read aloud: the justification height of `σ`. -/
abbrev GoldilocksModel.CS.h_j {M : GoldilocksModel V} (σ : M.CS) :
    Height :=
  M.cs_h_j σ

/-- `σ.F` is `M.cs_F σ`: the latest finalized block of `σ`.
    Read aloud: the finalized block of `σ`. -/
abbrev GoldilocksModel.CS.F {M : GoldilocksModel V} (σ : M.CS) :
    Block V :=
  M.cs_F σ

/-- `σ.h_F` is `M.cs_h_F σ`: the height at which `cs_F σ` was justified.
    Read aloud: the finalization height of `σ`. -/
abbrev GoldilocksModel.CS.h_F {M : GoldilocksModel V} (σ : M.CS) :
    Height :=
  M.cs_h_F σ

/-- `e.j` is `M.pp_j e`: the height at which the chain justified the block of `e`.
    Read aloud: the height of the pending pair `e`. -/
abbrev GoldilocksModel.PP.j {M : GoldilocksModel V} (e : M.PP) :
    Height :=
  M.pp_j e

/-- `e.T` is `M.pp_T e`: the justified block of `e`.
    Read aloud: the block of the pending pair `e`. -/
abbrev GoldilocksModel.PP.T {M : GoldilocksModel V} (e : M.PP) :
    Block V :=
  M.pp_T e

/-- `e.B` is `M.le_B e`: the locked block of the lock entry `e`.
    Read aloud: the block of `e`. -/
abbrev GoldilocksModel.LE.B {M : GoldilocksModel V} (e : M.LE) :
    Block V :=
  M.le_B e

/-- `e.d` is `M.le_d e`: the deadline of `e`: the entry is live strictly before it.
    Read aloud: the deadline of `e`. -/
abbrev GoldilocksModel.LE.d {M : GoldilocksModel V} (e : M.LE) :
    Time :=
  M.le_d e
-- END GENERATED spellings

end GoldilocksCorrectness.Record
