import Decoupled.Spec.Pseudocode

/-!
# Figure 2 (`alg:attestation-processing`) — direct attestation and height-event processing

`height_filter_healing.tex`, Figure 2 (`alg:attestation-processing`), lines 759–810: the
four routines `process_block`, `process_attestation`, `process_height_events` and
`advance_height`. Figure 1 (`alg:state-replay`) is the caller; nothing here calls back into
it, so the import between the two files is one-way.

All notation comes from `Decoupled/Spec/Pseudocode.lean`; read that first. Each routine
takes `σ` and returns it, as the figure writes it, and its body is a `do` block over a local
mutable `σ`.

## Three things to know while reading

**`σ` on a right-hand side is the state at that statement.** That is what makes
`advance_height`'s new `nj` read the *already-incremented* `h`: the two lines are in the
paper's order and mean what the paper means.

**Prestate classification.** Definition 16 (`def:block-attestation-processing`) says every
attestation is classified against the block's prestate, while the figure folds them one
after another. The two agree here because the fields `process_attestation` *reads* — `h`,
`T_h`, `h_j`, `h_F`, `F`, `J` — are disjoint from the ones it *writes*, which are `P` and
the two participation arrays. That is an observation about this rendering, not a proved
lemma.

**`σ.` is written out.** The figure elides it inside a routine — `T_h ← L`, `P ← P ∪ {i}` —
and writes it only where a second state is in play. Recovering that would need the
assignment macro to know which bare identifiers are fields of the state record, which it
cannot without elaboration, so every field write here is `σ.field ← …`.

## The one routine that can fail

`process_block` returns `invalid`, which is Definition 24 (`def:total-raw-replay`)'s "either
a state or `invalid`". The other three are total `σ → σ`, the shape the figure shows.
-/

set_option autoImplicit false

namespace Decoupled

open Framework.StsMultisetLog

variable {Node Root : Type}

section
variable [DecidableEq Node] [Electorate Node] [Params]

/-- `process_attestation(σ, a, A)` (Figure 2, `alg:attestation-processing`, lines 772–786).
    Definition 16 (`def:block-attestation-processing`)'s three tests, in the figure's order.
    `A` is the including block's parent, against which the broader progress rule evaluates
    ancestry; Definition 10 (`def:vote-contribution`) is where that bound comes from, and
    it is what stops a block proving its own progress.

    The two height tests are independent, so an exact target vote sets both bits. -/
noncomputable def processAttestation (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) : ChainState Node Root := Id.run do
  let mut σ := σ
  let i := a.validator                                        -- line 773
  if σ.h_j > σ.h_F ∧ σ.F ⪯ σ.J ∧
      a.finalityPair = .commit σ.h_j σ.J then                 -- lines 774–775
    σ.P ← insert i σ.P                                        -- line 776
  -- `if a's height pair = (h, T_h ≠ ⊥)` (line 778)
  match a.heightPair, σ.T_h with
  | .target hh T, some Th =>
      if hh = σ.h ∧ T = Th then
        σ.targetParticipation[i] ← true                       -- line 779
  | _, _ => pure ()
  -- `if a's height pair = (h, ⊥), or = (h, T ≠ ⊥) with T ⪯ A` (lines 781–782)
  match a.heightPair with
  | .timeout hh => if hh = σ.h then σ.progress[i] ← true       -- line 783
  | .target hh T => if hh = σ.h ∧ T ⪯ A then σ.progress[i] ← true
  | .empty => pure ()
  return σ                                                    -- line 785

/-- The attestation loop of `process_block` (Figure 2, `alg:attestation-processing`,
    lines 766–768), as a declaration of its own so that its equation can later be proved by
    induction on the list. -/
noncomputable def processAttestations (σ : ChainState Node Root)
    (as : List (Attestation Node Root)) (A : Blk Node Root) : ChainState Node Root :=
  Id.run do
  let mut σ := σ
  for a in as do
    σ ← processAttestation σ a A
  return σ

/-- `process_block(σ, B)` (Figure 2, `alg:attestation-processing`, lines 759–770). Fails
    when the block does not extend the cursor's chain at the cursor's slot, or when one of
    its attestations fails Definition 9 (`def:valid-attestation-inclusion`).

    **`A` is `σ.L`, where the figure writes `A ← B.parent`.** The two are the same block
    here: the preceding check has already returned `invalid` unless `B.parent = σ.L`, and
    `σ.L` is a block where `B.parent` is an `Option`. -/
noncomputable def processBlock (σ : ChainState Node Root) (B : Blk Node Root)
    : TransitionResult Node Root := Id.run do
  let mut σ := σ
  if B.parent ≠ some σ.L ∨ B.slot ≠ σ.s ∨
      ¬ (B.attestations).all ValidInclusion then              -- lines 760–762
    return invalid                                            -- line 763
  let A := σ.L                                                -- line 765: `A ← B.parent`
  σ.L ← B                                                     -- line 765: `L ← B`
  σ ← processAttestations σ B.attestations A                  -- lines 766–768
  return σ                                                    -- line 769

/-- `advance_height(σ, justify, start)` (Figure 2, `alg:attestation-processing`,
    lines 802–810). A nonempty `justify` installs the new justification and clears the
    finality tally; either way the height increments, the new height starts empty at
    `start`, and Definition 14 (`def:nonjustifiable`) fixes its flag from the *new* height
    against the current finalized height. -/
def advanceHeight (σ : ChainState Node Root)
    (justify : Option (Blk Node Root)) (start : Time) : ChainState Node Root := Id.run do
  let mut σ := σ
  if let some T := justify then                               -- line 803
    σ.J ← T                                                   -- line 804
    σ.h_j ← σ.h
    σ.P ← ∅
  σ.h ← σ.h + 1                                               -- line 806
  σ.s_h ← start
  σ.T_h ← ⊥
  σ.nj ← nonjustifiable σ.h σ.h_F                             -- line 807
  σ.targetParticipation, σ.progress ← fun _ => false          -- line 808: `false^V`
  return σ                                                    -- line 809

/-- `process_height_events(σ, start)` (Figure 2, `alg:attestation-processing`,
    lines 788–800) — Definition 18 (`def:height-outcome`)'s three cases, in order:
    finalize the old latest justification, then prefer the exact current target, and
    otherwise advance by progress. Justification therefore wins whenever both height
    thresholds are present. -/
noncomputable def processHeightEvents (σ : ChainState Node Root) (start : Time)
    : ChainState Node Root := Id.run do
  let mut σ := σ
  if σ.h_j > σ.h_F ∧ σ.F ⪯ σ.J ∧ w(σ.P)≥q then                -- line 789
    σ.F ← σ.J                                                 -- line 790
    σ.h_F ← σ.h_j
  if ¬ σ.nj ∧ σ.T_h ≠ ⊥ ∧ w(σ.Qtarget)≥q then                 -- lines 792–793
    return advanceHeight σ σ.T_h start                        -- line 794
  if w(σ.Qprog)≥q then                                        -- line 796
    return advanceHeight σ ⊥ start                            -- line 797
  return σ                                                    -- line 799

end

end Decoupled
