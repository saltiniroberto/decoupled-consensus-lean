import Proofs.Instance.Objects
import Proofs.Instance.ObjectConstants
import Proofs.Instance.Equalities.Fill
import Proofs.Instance.Equalities.ForkChoiceImages
import Proofs.Instance.Equalities.GradesImages
import Proofs.Instance.Equalities.ContractImages
import Proofs.Instance.Wiring
import Proofs.Instance.Model
import Proofs.Instance.ModelWiring
import Proofs.Instance.Facts.ChainState
import Proofs.Instance.Facts.ChainStateAdded
import Proofs.Instance.Facts.ChainStateOwnRuns
import Proofs.Instance.Facts.Schedule
import Proofs.Instance.Facts.Store
import Proofs.Instance.Facts.ForkChoice
import Proofs.Instance.Facts.ValidatorClient
import Proofs.Instance.Facts.Grades
import Proofs.Instance.Facts.SubtypeEqualities
import Proofs.Instance.Facts.ConfirmationTree
import Proofs.Instance.Facts.Handlers
import Proofs.Instance.Facts.Duties
import Proofs.Instance.Facts.Node
import Proofs.Instance.Facts.Node2
import Proofs.Instance.Facts.Evidence
import Proofs.Instance.Facts.NoRaise
import Proofs.Instance.Facts.NonEmpty
import Proofs.Instance.Facts.StoreRun
import Proofs.Instance.Facts.HandlersRun
import Proofs.Instance.Facts.HandlersStore
import Proofs.Instance.Facts.GradesRun
import Proofs.Instance.Facts.Remaining
import Proofs.Instance.Facts.Reached
import Proofs.Instance.Facts.NodeReached
import Proofs.Instance.Facts.GradesReached
import Proofs.Instance.Facts.TickReached
import Proofs.Instance.Facts.DutiesReached
import Proofs.Instance.Facts.StoreWithCache
import Proofs.Instance.Facts.ReachedReads
import Proofs.Instance.Facts.Assembly

/-!
# The spec's instance of the record

The maps between the spec's types and the record's, the equalities of the spec's routines with the
record's members, the instance `Model.spec` of the record `Model V`, and the proofs of the
record's facts at it, gathered in the bundle `Model.spec_facts`.
-/
