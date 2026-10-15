import Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Cross-reader conditions on the grade views

Conditions relating what `source` reads at one grade phase of round `r` (g2, or g1) to what `target`
reads at the next one (g1, or g0), stated over a model `M : Record.Model V`. Each takes the two node
states it reads as arguments `ns nt : M.N` after `target`, and every grade-view reader it names is
read for every outcome.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)

/-- At `source`'s node state `ns` (its g2 phase of round `r`) and `target`'s node state `nt` (its g1
    phase): a row `u` in an outcome of `ns`'s interpreted inputs at the early g2 cutoff, whose head
    an outcome of `ns`'s local cover test finds covering `B`, passes every outcome of `nt`'s body
    test at the early g1 cutoff (`forward`); and a row `u` in an outcome of `nt`'s interpreted
    inputs at the late g1 cutoff passes every outcome of `ns`'s body test at the late g2 cutoff
    (`backward`). -/
structure Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (r : Round)
    (source target : V) (ns nt : M.N) (B : Block V) : Prop where
  forward : ∀sender u,
    ∀ I, M.interpretedInputs
      (M.gradeView (M.toHealing ns.st.core))
      ns.st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) sender ⇢ I → u ∈ I →
    ∀ c, M.localCovers
      (M.gradeView (M.toHealing ns.st.core))
      u.confirmed B ⇢ c → c = true →
    ∀ b, M.bodyReady
      (M.gradeView (M.toHealing nt.st.core))
      nt.st.core.F
      (M.early S.E S.hc r .g1) u ⇢ b → b = true
  backward : ∀sender u,
    ∀ I, M.interpretedInputs
      (M.gradeView (M.toHealing nt.st.core))
      nt.st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender ⇢ I → u ∈ I →
    ∀ b, M.bodyReady
      (M.gradeView (M.toHealing ns.st.core))
      ns.st.core.F
      (M.late S.E S.hc r .g2) u ⇢ b → b = true

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)

/-- At `source`'s node state `ns` (its g2 phase of round `r`) and `target`'s node state `nt` (its g1
    phase): if a row `u` of `ns`'s interpreted inputs at the early g2 cutoff is covered for `B` and
    its head `root` names `H` in `ns`'s grade view, then `nt`'s finalized block is an ancestor of or
    equal to `H` (`forward`); and if a row `u` of `nt`'s interpreted inputs at the late g1 cutoff
    has head `root` naming `H` in `nt`'s grade view, then `H` is compatible with `ns`'s finalized
    block (`backward`). -/
structure Vocabulary.Proofs.HealingSurface.CrossReaderFinalizedBelow (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (r : Round)
    (source target : V) (ns nt : M.N) (B : Block V) : Prop where
  forward : ∀sender u root H,
    ∀ I, M.interpretedInputs
      (M.gradeView (M.toHealing ns.st.core))
      ns.st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) sender ⇢ I → u ∈ I →
    ∀ c, M.localCovers
      (M.gradeView (M.toHealing ns.st.core))
      u.confirmed B ⇢ c → c = true →
    u.confirmed = some root →
    Block.find?
      (M.gradeView (M.toHealing ns.st.core)).T root =
        some H →
    Block.Preceq nt.st.core.F H
  backward : ∀sender u root H,
    ∀ I, M.interpretedInputs
      (M.gradeView (M.toHealing nt.st.core))
      nt.st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender ⇢ I → u ∈ I →
    u.confirmed = some root →
    Block.find?
      (M.gradeView (M.toHealing nt.st.core)).T root =
        some H →
    Block.compatible H ns.st.core.F = true

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)

/-- At `source`'s node state `ns` (its g2 phase of round `r`) and `target`'s node state `nt` (its g1
    phase), a token `x` moves between the two ready views: from `ns`'s ready view at the early g2
    cutoff, when covered for `B`, into `nt`'s ready view at the early g1 cutoff (`forward`); from
    `nt`'s ready view at the late g1 cutoff into `ns`'s ready view at the late g2 cutoff
    (`lateBack`); and from `nt`'s raw view at the late g1 cutoff into `ns`'s raw view at the late g2
    cutoff (`rawBack`); in each case unless the receiving raw view shows an equivocation at `x`'s
    round. -/
structure Vocabulary.Proofs.HealingSurface.CrossReaderTokenTransport (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (r : Round)
    (source target : V) (ns nt : M.N) (B : Block V) : Prop where
  forward : ∀sender x,
    ∀ X, M.readyView
      (M.gradeView (M.toHealing ns.st.core))
      ns.st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g2) sender ⇢ X → x ∈ X →
    ∀ c, M.localCovers
      (M.gradeView (M.toHealing ns.st.core))
      x.key B ⇢ c → c = true →
    ∀ Y, M.readyView
        (M.gradeView (M.toHealing nt.st.core))
        nt.st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g1) sender ⇢ Y →
    ∀ R, M.rawView
          (M.gradeView (M.toHealing nt.st.core))
          S.hc.η_SG r (M.late S.E S.hc r .g1) sender ⇢ R →
    x ∈ Y ∨ EquivocationAt R x.round
  lateBack : ∀sender x,
    ∀ X, M.readyView
      (M.gradeView (M.toHealing nt.st.core))
      nt.st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender ⇢ X → x ∈ X →
    ∀ Y, M.readyView
        (M.gradeView (M.toHealing ns.st.core))
        ns.st.core.F
        S.hc.η_SG r (M.late S.E S.hc r .g2) sender ⇢ Y →
    ∀ R, M.rawView
          (M.gradeView (M.toHealing ns.st.core))
          S.hc.η_SG r (M.late S.E S.hc r .g2) sender ⇢ R →
    x ∈ Y ∨ EquivocationAt R x.round
  rawBack : ∀sender x,
    ∀ X, M.rawView
      (M.gradeView (M.toHealing nt.st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g1) sender ⇢ X → x ∈ X →
    ∀ Y, M.rawView
        (M.gradeView (M.toHealing ns.st.core))
        S.hc.η_SG r (M.late S.E S.hc r .g2) sender ⇢ Y →
    x ∈ Y ∨ EquivocationAt Y x.round

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)

/-- `CrossReaderBodyReadyGuard` one phase earlier: at `source`'s node state `ns` (its g1 phase of
    round `r`) and `target`'s node state `nt` (its g0 phase), a row `u` of `ns`'s interpreted inputs
    at the early g1 cutoff whose head is covered for `B` passes every outcome of `nt`'s body test at
    the early g0 cutoff (`forward`), and a row `u` of `nt`'s interpreted inputs at the late g0
    cutoff passes every outcome of `ns`'s body test at the late g1 cutoff (`backward`). -/
structure Vocabulary.Proofs.HealingSurface.G1G0CrossReaderBodyReadyGuard (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (r : Round)
    (source target : V) (ns nt : M.N) (B : Block V) : Prop where
  forward : ∀sender u,
    ∀ I, M.interpretedInputs
      (M.gradeView (M.toHealing ns.st.core))
      ns.st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g1) sender ⇢ I → u ∈ I →
    ∀ c, M.localCovers
      (M.gradeView (M.toHealing ns.st.core))
      u.confirmed B ⇢ c → c = true →
    ∀ b, M.bodyReady
      (M.gradeView (M.toHealing nt.st.core))
      nt.st.core.F
      (M.early S.E S.hc r .g0) u ⇢ b → b = true
  backward : ∀sender u,
    ∀ I, M.interpretedInputs
      (M.gradeView (M.toHealing nt.st.core))
      nt.st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g0) sender ⇢ I → u ∈ I →
    ∀ b, M.bodyReady
      (M.gradeView (M.toHealing ns.st.core))
      ns.st.core.F
      (M.late S.E S.hc r .g1) u ⇢ b → b = true

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)

/-- `CrossReaderFinalizedBelow` one phase earlier, at `source`'s node state `ns` for its g1 phase of
    round `r` and `target`'s node state `nt` for its g0 phase. -/
structure Vocabulary.Proofs.HealingSurface.G1G0CrossReaderFinalizedBelow (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (r : Round)
    (source target : V) (ns nt : M.N) (B : Block V) : Prop where
  forward : ∀sender u root H,
    ∀ I, M.interpretedInputs
      (M.gradeView (M.toHealing ns.st.core))
      ns.st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g1) sender ⇢ I → u ∈ I →
    ∀ c, M.localCovers
      (M.gradeView (M.toHealing ns.st.core))
      u.confirmed B ⇢ c → c = true →
    u.confirmed = some root →
    Block.find?
      (M.gradeView (M.toHealing ns.st.core)).T root =
        some H →
    Block.Preceq nt.st.core.F H
  backward : ∀sender u root H,
    ∀ I, M.interpretedInputs
      (M.gradeView (M.toHealing nt.st.core))
      nt.st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g0) sender ⇢ I → u ∈ I →
    u.confirmed = some root →
    Block.find?
      (M.gradeView (M.toHealing nt.st.core)).T root =
        some H →
    Block.compatible H ns.st.core.F = true

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)

/-- `CrossReaderTokenTransport` one phase earlier, at `source`'s node state `ns` for its g1 phase of
    round `r` and `target`'s node state `nt` for its g0 phase. -/
structure Vocabulary.Proofs.HealingSurface.G1G0CrossReaderTokenTransport (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (r : Round)
    (source target : V) (ns nt : M.N) (B : Block V) : Prop where
  forward : ∀sender x,
    ∀ X, M.readyView
      (M.gradeView (M.toHealing ns.st.core))
      ns.st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g1) sender ⇢ X → x ∈ X →
    ∀ c, M.localCovers
      (M.gradeView (M.toHealing ns.st.core))
      x.key B ⇢ c → c = true →
    ∀ Y, M.readyView
        (M.gradeView (M.toHealing nt.st.core))
        nt.st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g0) sender ⇢ Y →
    ∀ R, M.rawView
          (M.gradeView (M.toHealing nt.st.core))
          S.hc.η_SG r (M.late S.E S.hc r .g0) sender ⇢ R →
    x ∈ Y ∨ EquivocationAt R x.round
  lateBack : ∀sender x,
    ∀ X, M.readyView
      (M.gradeView (M.toHealing nt.st.core))
      nt.st.core.F
      S.hc.η_SG r (M.late S.E S.hc r .g0) sender ⇢ X → x ∈ X →
    ∀ Y, M.readyView
        (M.gradeView (M.toHealing ns.st.core))
        ns.st.core.F
        S.hc.η_SG r (M.late S.E S.hc r .g1) sender ⇢ Y →
    ∀ R, M.rawView
          (M.gradeView (M.toHealing ns.st.core))
          S.hc.η_SG r (M.late S.E S.hc r .g1) sender ⇢ R →
    x ∈ Y ∨ EquivocationAt R x.round
  rawBack : ∀sender x,
    ∀ X, M.rawView
      (M.gradeView (M.toHealing nt.st.core))
      S.hc.η_SG r (M.late S.E S.hc r .g0) sender ⇢ X → x ∈ X →
    ∀ Y, M.rawView
        (M.gradeView (M.toHealing ns.st.core))
        S.hc.η_SG r (M.late S.E S.hc r .g1) sender ⇢ Y →
    x ∈ Y ∨ EquivocationAt Y x.round

end

end DecoupledConsensusModel.Sts.Restated
