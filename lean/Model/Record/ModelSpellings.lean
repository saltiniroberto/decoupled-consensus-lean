import Model.Record.Model

/-!
# Inherited readers of the record's store types

A healing store reads the fields of the FG, SG and Goldfish stores it extends. Each definition here
spells such a read over the record through the projections `toFG`, `toSG` and `toGoldfishStore`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

open DecoupledConsensusModel.Protocol (HeightConfig HealConfig SGVote Token GradeRead Phase
  CarriedAdmission ProposalRowSource)
open DecoupledConsensusModel.Execution (NamedObject Setup)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `fg.T`: the blocks `fg` has processed, the reader `T` of the Goldfish store `fg` projects to. -/
def Model.FGS.T {M : Model V} (fg : M.FGS) : Finset (Block V) :=
  fg.toSG.toGoldfishStore.T

/-- `hs.σ`: the chain state `hs` holds for each block, the reader `σ` of the FG store `hs` projects
    to. -/
def Model.HS.σ {M : Model V} (hs : M.HS) : Block V → M.CS :=
  hs.toFG.σ

/-- `hs.F`: the finalized block of `hs`, the reader `F` of the FG store `hs` projects to. -/
def Model.HS.F {M : Model V} (hs : M.HS) : Block V :=
  hs.toFG.F

/-- `hs.J`: the justified block of `hs`, the reader `J` of the FG store `hs` projects to. -/
def Model.HS.J {M : Model V} (hs : M.HS) : Block V :=
  hs.toFG.J

/-- `hs.h_j`: the justified height of `hs`, the reader `h_j` of the FG store `hs` projects to. -/
def Model.HS.h_j {M : Model V} (hs : M.HS) : Height :=
  hs.toFG.h_j

/-- `hs.h_max`: the largest height `hs` has seen, the reader `h_max` of the FG store `hs` projects
    to. -/
def Model.HS.h_max {M : Model V} (hs : M.HS) : Height :=
  hs.toFG.h_max

/-- `hs.sg_votes`: the SG votes of each round that `hs` has processed, the reader `sg_votes` of the
    SG store `hs` projects to. -/
def Model.HS.sg_votes {M : Model V} (hs : M.HS) : Round → Finset (SGVote V) :=
  hs.toFG.toSG.sg_votes

/-- `hs.s`: the current slot of `hs`, the reader `s` of the Goldfish store `hs` projects to. -/
def Model.HS.s {M : Model V} (hs : M.HS) : Slot :=
  hs.toFG.toSG.toGoldfishStore.s

/-- `hs.T`: the blocks `hs` has processed, the reader `T` of the Goldfish store `hs` projects to. -/
def Model.HS.T {M : Model V} (hs : M.HS) : Finset (Block V) :=
  hs.toFG.toSG.toGoldfishStore.T

/-- `hs.live_confirmed`: the block `hs` last confirmed, the reader `live_confirmed` of the Goldfish
    store `hs` projects to. -/
def Model.HS.live_confirmed {M : Model V} (hs : M.HS) : Block V :=
  hs.toFG.toSG.toGoldfishStore.live_confirmed

end DecoupledConsensusModel.Sts.Record
