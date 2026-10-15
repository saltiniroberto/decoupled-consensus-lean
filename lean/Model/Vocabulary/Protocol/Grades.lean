module
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish
public import Model.Vocabulary.Protocol.ValidatorClient

@[expose] public section

/-!
# Grades and the round schedule

The round schedule, the grade view over the store, the grade tests, the grade contract a duty reads,
and the cache of grades saved at each phase of a round.
-/

section
/-! ## Round schedule -/

namespace DecoupledConsensusModel
namespace Protocol

/-- The round schedule: the round length `R ≥ 3` and the SG lookback `η_SG`. -/
structure HealConfig where
/-- `R`: round `r` is the slots `rR … rR+R−1`. -/
  R : Nat
  /-- `R ≥ 3`. -/
  R_ge_three : 3 ≤ R
  /-- `η_SG`: the SG lookback window, in rounds. -/
  η_SG : Round
  /-- `η_SG ≥ 1`. -/
  η_SG_ge_one : 1 ≤ η_SG

namespace HealConfig

variable (hc : HealConfig)

/-- `round(s) = ⌊s/R⌋`. -/
def round_of (s : Slot) : Round :=
  s / hc.R

/-- The opening slot `rR` of round `r`. -/
def opening_slot (r : Round) : Slot :=
  r * hc.R

/-- `a_r = t_{rR} + 6Δ`, the action time of round `r`. -/
def a (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r) + 6 * Δ

end HealConfig

section Alignment

variable {V : Type} [DecidableEq V] [Fintype V]

end Alignment

end Protocol
end DecoupledConsensusModel
end

section
/-! ## Grade view -/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (SGVote)

structure GradeView (V : Type) where
  /-- The processed block tree, used to resolve roots. -/
  T : Finset (Block V)
  /-- Receipt times for blocks in the processed tree. -/
  timestamp_block : TimestampMap (Block V)
  /-- The currently filtered block tree. -/
  tree : Finset (Block V)
  /-- The SG votes of each round. -/
  sg_votes : Round → Finset (SGVote V)
  /-- Receipt times of the SG votes. -/
  timestamp_sg_vote : TimestampMap (SGVote V)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Resolved-head coverage -/

/-- Whether the root `H` resolves in `T` to a descendant of, or equal to, `B`. -/
def head_covers (T : Finset (Block V)) (B : Block V) (H : Option BlockId) : Bool :=
  match H with
  | none => false
  | some root =>
    match Block.find? T root with
    | some head => Block.preceq B head
    | none => false

end Protocol
end DecoupledConsensusModel
end

section
/-! ## The healing store -/

namespace DecoupledConsensusModel
namespace Protocol

/-! ## The store -/

structure HealingStore (V : Type) extends toFG : Protocol.FGStore V

namespace HealingStore

variable {V : Type} [DecidableEq V]

/-- The store's grade view. -/
def gradeView (st : HealingStore V) : GradeView V where
  T := st.T
  timestamp_block := st.timestamp_block
  tree := Protocol.get_filtered_block_tree st.toFG
  sg_votes := st.sg_votes
  timestamp_sg_vote := st.timestamp_sg_vote

end HealingStore

end Protocol
end DecoupledConsensusModel
end

section
/-! ## Grade contracts -/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The chain from `B` towards genesis, `B` first, following at most the given number of parents. -/
def chain_up : Nat → Block V → List (Block V)
  | 0, B => [B]
  | n + 1, B =>
    B :: (match B.parent? with
      | none => []
      | some p => chain_up n p)

/-- The chain from `B` to genesis, `B` first. -/
def chain_of (B : Block V) : List (Block V) :=
  chain_up B.depth B

/-- The deepest block passing `test` among `C` and its ancestors that are descendants of, or equal
    to, `floor` when it is given. -/
def deepest_clear (floor : Option (Block V)) (C : Block V)
    (test : Block V → Bool) : Option (Block V) :=
  Block.deepest? ((chain_of C).toFinset.filter (fun B =>
    floor.elim true (fun anchor => Block.preceq anchor B) = true ∧ test B = true))

/-- One grade read: the anchor, the grade-2 candidate `Q2`, the clear test, and the raw grade-2
    condition with its decidability. -/
structure GradeRead (V : Type) where
  anchor : Block V
  Q2 : Option (Block V)
  clear : Block V → Bool
  rawG2 : Prop
  rawG2_decidable : Decidable rawG2

/-- An optional SG candidate for the confirmation update. -/
inductive ConfirmationSGCandidate (V : Type) [DecidableEq V] [Fintype V] where
  | optional (select : Env V → HealConfig → HealingStore V → Slot → Option (Block V))

/-- The parts of the grade runtime a protocol supplies: the grade read, the SG vote choice, the
    confirmation SG candidate and the stable root. -/
structure GradeContract (V : Type) [DecidableEq V] [Fintype V] where
  read : Env V → HealConfig → HealingStore V → Round → GradeRead V
  sgVote : HealingStore V → GradeRead V → Block V
  confirmationSG : ConfirmationSGCandidate V
  /-- The round's stable-record root. -/
  stableRoot : Env V → HealConfig → HealingStore V → Round → Option (Block V)

/-- The SG vote from a grade read: the deepest clear block from the anchor to `live_confirmed`; else
    `Q2`; else `get_fg_root` when the raw grade-2 condition holds; else the anchor. -/
def currentSGVote (st : HealingStore V) (grades : GradeRead V) : Block V :=
  letI := grades.rawG2_decidable
  match deepest_clear (some grades.anchor) st.live_confirmed grades.clear with
  | some B => B
  | none =>
    match grades.Q2 with
    | some q => q
    | none =>
      if grades.rawG2 then Protocol.get_fg_root st.toFG else grades.anchor

end Protocol
end DecoupledConsensusModel
end

section

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V]

def clipGrade (g F : Block V) : Block V :=
  match g with
  | .genesis => .genesis
  | .node p s root gv gsv ats v =>
      if Block.compatible (.node p s root gv gsv ats v) F then
        .node p s root gv gsv ats v
      else clipGrade p F

end DecoupledConsensusModel.Protocol
end

section

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

def rawInputs (gv : Protocol.GradeView V) (eta r : Round) (cutoff : Time) (sender : V) :
    Finset (Protocol.SGVote V) :=
  ((Protocol.latest_window eta r).toFinset.biUnion gv.sg_votes).filter fun u =>
    u.val_index = sender ∧ occurrenceBefore (gv.timestamp_sg_vote u) cutoff = true

/-- Whether an SG vote's block is ready at `cutoff`: an empty vote is; otherwise its root must
    resolve in the grade view's tree to a block stamped before `cutoff` and compatible with `F`. -/
def bodyReady (gv : Protocol.GradeView V) (F : Block V) (cutoff : Time)
    (u : Protocol.SGVote V) : Bool :=
  match u.confirmed with
  | none => true
  | some root => match Block.find? gv.T root with
    | none => false
    | some H => stampedBefore gv.timestamp_block cutoff H && Block.compatible H F

def interpretedInputs (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) (cutoff : Time) (sender : V) : Finset (Protocol.SGVote V) :=
  (rawInputs gv eta r cutoff sender).filter fun u => bodyReady gv F cutoff u = true

end DecoupledConsensusModel.Protocol
end

section
/-! ## Support and opposition -/

namespace DecoupledConsensusModel.Protocol

structure Token (Key : Type*) where
  round : Nat
  key : Key
deriving DecidableEq

variable {Key : Type*} {Block : Type*}

def CleanFrom (raw : Finset (Token Key)) (k : Nat) : Prop :=
  ∀ x ∈ raw, ∀ y ∈ raw, k ≤ x.round → x.round = y.round → x.key = y.key

/-- `B` is supported: a latest-round token `u` of `early` covers `B`, `raw` holds no two different
    keys in one round from `u`'s round on, and every token of `late` of a later round covers `B`. -/
def Supports (covers : Key → Block → Prop)
    (early late raw : Finset (Token Key)) (B : Block) : Prop :=
  ∃ u ∈ early,
    (∀ x ∈ early, x.round ≤ u.round) ∧
    covers u.key B ∧
    CleanFrom raw u.round ∧
    ∀ x ∈ late, u.round < x.round → covers x.key B
def Opposes (covers : Key → Block → Prop)
    (early late raw : Finset (Token Key)) (B : Block) : Prop :=
  (∃ x ∈ late, (∀ u ∈ early, u.round ≤ x.round) ∧ ¬ covers x.key B) ∨
  ∃ x ∈ raw, ∃ y ∈ raw, (∀ u ∈ early, u.round ≤ x.round) ∧
    x.round = y.round ∧ x.key ≠ y.key

end DecoupledConsensusModel.Protocol

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Protocol (Token)

def token (u : Protocol.SGVote V) : Token (Option BlockId) := ⟨u.round, u.confirmed⟩

end DecoupledConsensusModel.Protocol
end

section

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token)

section DecidableGrades
variable {Key B : Type*} [DecidableEq Key]

instance supportsDecidable (covers : Key → B → Bool)
    (early late raw : Finset (Token Key)) (b : B) :
    Decidable (DecoupledConsensusModel.Protocol.Supports (fun k x => covers k x = true) early late raw b) := by
  unfold DecoupledConsensusModel.Protocol.Supports DecoupledConsensusModel.Protocol.CleanFrom
  infer_instance

instance opposesDecidable (covers : Key → B → Bool)
    (early late raw : Finset (Token Key)) (b : B) :
    Decidable (DecoupledConsensusModel.Protocol.Opposes (fun k x => covers k x = true) early late raw b) := by
  unfold DecoupledConsensusModel.Protocol.Opposes
  infer_instance

end DecidableGrades

def rawView (gv : Protocol.GradeView V) (eta r : Round) (cutoff : Time) (v : V) :=
  (rawInputs gv eta r cutoff v).image token

def readyView (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) (cutoff : Time) (v : V) :=
  (interpretedInputs gv F eta r cutoff v).image token

def localCovers (gv : Protocol.GradeView V) (key : Option BlockId) (B : Block V) : Bool :=
  Protocol.head_covers gv.T B key

def positive (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V) (B : Block V) : Bool :=
  decide (DecoupledConsensusModel.Protocol.Supports (fun k b => localCovers gv k b = true)
    (readyView gv F eta r early v) (readyView gv F eta r late v) (rawView gv eta r late v) B)

def opposing (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V) (B : Block V) : Bool :=
  decide (DecoupledConsensusModel.Protocol.Opposes (fun k b => localCovers gv k b = true)
    (readyView gv F eta r early v) (readyView gv F eta r late v) (rawView gv eta r late v) B)

/-- The local grade test for `B`: the weight of the validators positive for `B` exceeds the weight
    of those opposing it. -/
def gradeBool (E : Env V) (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (B : Block V) : Bool :=
  decide (E.electorate.weightOf
    (Finset.univ.filter fun v => opposing gv F eta r early late v B = true) <
    E.electorate.weightOf
      (Finset.univ.filter fun v => positive gv F eta r early late v B = true))

/-- The deepest block of the grade view's tree that passes `gradeBool`. -/
def freezeRoot (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) (early late : Time) : Option (Block V) :=
  Block.deepest? (gv.T.filter fun B => gradeBool E gv F eta r early late B = true)

/-- The deepest block of `tree` that is an ancestor of, or equal to, `root`. -/
def activePrefix (tree : Finset (Block V)) (root : Block V) : Option (Block V) :=
  Block.deepest? (tree.filter fun B => Block.preceq B root = true)

/-- The SG anchor: when grade 1 completed with a root, the deepest block of the filtered block tree
    that is an ancestor of, or equal to, that root, falling back to `get_fg_root`; otherwise
    `get_fg_root`. -/
def anchor (_E : Env V) (_hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (_r : Round)
    (g1 : Option (Option (Block V))) : Block V :=
  match g1 with
  | some (some root) =>
    (activePrefix (Protocol.get_filtered_block_tree st.toFG) root).getD
      (Protocol.get_fg_root st.toFG)
  | _ => Protocol.get_fg_root st.toFG

/-- The grade results of a round's three phases G0, G1 and G2: `none` while pending, `some none`
    when completed empty. -/
structure Frame (V : Type) where
  g0 : Option (Option (Block V))
  g1 : Option (Option (Block V))
  g2 : Option (Option (Block V))

def allClosed (frame : Frame V) : Bool :=
  frame.g0.isSome && frame.g1.isSome && frame.g2.isSome

def grade2Block (st : Protocol.HealingStore V) (frame : Frame V) : Option (Block V) :=
  if allClosed frame then
    (frame.g2.bind id).bind (activePrefix (Protocol.get_filtered_block_tree st.toFG))
  else none

def clear (frame : Frame V) (B : Block V) : Bool :=
  match frame.g0 with
  | some (some root) => Block.compatible B root
  | _ => true

end DecoupledConsensusModel.Protocol
end

section
/-! ## The phase cache -/

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

inductive Phase where
  | g0 | g1 | g2
  deriving DecidableEq

def Phase.earlyOffset : Phase → Int
  | .g0 => -3 | .g1 => -4 | .g2 => -5

def Phase.lateOffset : Phase → Int
  | .g0 => -3 | .g1 => -2 | .g2 => -1

def Phase.domainOffset : Phase → Int
  | .g0 => 1 | .g1 => 0 | .g2 => -1

def opening (E : Env V) (hc : Protocol.HealConfig) (r : Round) : Time :=
  Protocol.proposal_time E (hc.opening_slot r)

def early (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase) : Time :=
  opening E hc r + p.earlyOffset * E.Δ

def late (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase) : Time :=
  opening E hc r + p.lateOffset * E.Δ

def domain (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase) : Time :=
  opening E hc r + p.domainOffset * E.Δ

def pendingFrame : Frame V := ⟨none, none, none⟩
def emptyFrame : Frame V := ⟨some none, some none, some none⟩

def phaseResult (f : Frame V) : Phase → Option (Option (Block V))
  | .g0 => f.g0 | .g1 => f.g1 | .g2 => f.g2

def putPhase (f : Frame V) (p : Phase) (result : Option (Block V)) : Frame V :=
  match p with
  | .g0 => { f with g0 := some result }
  | .g1 => { f with g1 := some result }
  | .g2 => { f with g2 := some result }

/-- Completes phase `p` of round `r` at time `t`: a pending result is computed with `freezeRoot`
    when `t` is the phase's domain time; a completed result is kept. -/
def completeOne (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (t : Time) (p : Phase) (f : Frame V) : Frame V :=
  match phaseResult f p with
  | some _ => f
  | none =>
    if t = domain E hc r p then
      putPhase f p (freezeRoot E st.gradeView st.F hc.η_SG r (early E hc r p) (late E hc r p))
    else f

def completeFrame (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (t : Time) (f : Frame V) : Frame V :=
  completeOne E hc st r t .g0
    (completeOne E hc st r t .g1 (completeOne E hc st r t .g2 f))

def clipResult (F : Block V) (result : Option (Option (Block V))) :
    Option (Option (Block V)) :=
  result.map (fun root => root.map (fun B => DecoupledConsensusModel.Protocol.clipGrade B F))

def clipFrame (F : Block V) (f : Frame V) : Frame V :=
  ⟨clipResult F f.g0, clipResult F f.g1, clipResult F f.g2⟩

/-- The phase cache: the current round, its frame, and the next round's frame. -/
structure Cache (V : Type) where
  round : Round
  current : Frame V
  next : Frame V

def initialCache : Cache V := ⟨0, emptyFrame, pendingFrame⟩

/-- The cache moved to round `r`: unchanged at its own round; at the following round the next frame
    becomes current; otherwise both frames start pending. -/
def alignRound (c : Cache V) (r : Round) : Cache V :=
  if r = c.round then c
  else if r = c.round + 1 then ⟨r, c.next, pendingFrame⟩
  else ⟨r, pendingFrame, pendingFrame⟩

def cacheAtRound (c : Cache V) (r : Round) : Frame V :=
  if r = c.round then c.current
  else if r = c.round + 1 then c.next
  else pendingFrame

def clipCache (F : Block V) (c : Cache V) : Cache V :=
  ⟨c.round, clipFrame F c.current, clipFrame F c.next⟩

/-- The cache after a tick at time `t`: aligned to `t`'s round, both frames completed at `t`, and
    clipped to the store's finalized block. -/
def onPhaseTick (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (t : Time) (c : Cache V) : Cache V :=
  let c := alignRound c (hc.round_of (E.slotOf t))
  clipCache st.F ⟨c.round, completeFrame E hc st c.round t c.current,
    completeFrame E hc st (c.round + 1) t c.next⟩

end DecoupledConsensusModel.Protocol
end

section
/-! ## The frame grade contract -/

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

def readFrame (c : Cache V) (st : Protocol.HealingStore V) (r : Round) : Frame V :=
  clipFrame st.F (cacheAtRound c r)

def frameGradeRead (c : Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) : Protocol.GradeRead V where
  anchor := DecoupledConsensusModel.Protocol.anchor E hc st r (readFrame c st r).g1
  Q2 := grade2Block st (readFrame c st r)
  clear := DecoupledConsensusModel.Protocol.clear (readFrame c st r)
  rawG2 := ((readFrame c st r).g2.bind id).isSome = true
  rawG2_decidable := inferInstance

def frameSGCandidate (c : Cache V) (_E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (_slot : Slot) : Option (Block V) :=
  ((readFrame c st (hc.round_of st.s)).g2.bind id).bind
    (activePrefix (Protocol.get_filtered_block_tree st.toFG))

/-- The stable root of round `r`: the deepest block of the filtered block tree that is an ancestor
    of, or equal to, the saved grade-2 root, or `get_fg_root` when there is none. -/
def frameStableRoot (c : Cache V) (_E : Env V) (_hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) : Option (Block V) :=
  match ((readFrame c st r).g2.bind id).bind
      (activePrefix (Protocol.get_filtered_block_tree st.toFG)) with
  | some G => some G
  | none => some (Protocol.get_fg_root st.toFG)

/-- The grade contract read from the cache `c`: the frame grade read, `currentSGVote`, the frame SG
    candidate and `frameStableRoot`. -/
def frameContract (c : Cache V) : Protocol.GradeContract V where
  read := frameGradeRead c
  sgVote := Protocol.currentSGVote
  confirmationSG := .optional (frameSGCandidate c)
  stableRoot := frameStableRoot c

end DecoupledConsensusModel.Protocol
end

end
