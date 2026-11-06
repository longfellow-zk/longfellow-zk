import LfzkV2.Current.ApplicationStatement
import LfzkV2.Current.ApplicationOracle
import LfzkV2.Current.SelectionPath

/-! The selected joint boundary belongs to zk-v2.  Applications supply public
cell layouts and compiled frontend data; this boundary owns early selection
and the mandatory appended fingerprint equations.  Witness selection remains
a sibling protocol underneath it, with its existing algebra and FS proofs.
The current application theorem specializes this generic typed pair. -/
noncomputable section
namespace LfzkV2.Current.ZkJoint
open RecursivePolygero NonrecursiveFS Counting WitnessSelection ApplicationOracle Application
open scoped Classical

variable {k s n t : ℕ} {IB IN Key : Type}

/-- The zk-v2 frontend exposes a full-cell projection of one typed backend
participant.  Two dedicated masks are included in each projected candidate. -/
structure SelectedField (P : Joint.Participant k s n t) (Index Key : Type) where
  view : Key → (tupleCounts P.backend).Index → WitnessSelection.Candidate P.Carrier Index
  cutoff : ℕ

/-- Public selection metadata for the typed joint pair. No proof response or
oracle answer is retained in these parameters. -/
structure JointParam (P R : Joint.Participant k s n t) (IB IN Key : Type) where
  first : SelectedField P IB Key
  second : SelectedField R IN Key

namespace JointParam
variable [Fintype IB] [Fintype IN]
variable {roles : List Role} {Block Link Body C : Type}
variable {P R : Joint.Participant k s n t} (param : JointParam P R IB IN Key)

/-- All field coefficients share one answer, and all responses are read from
the already-bound rank-one prefix. The same cut oracle is later authenticated
by joint Polygero; applications never run a separate selection exchange. -/
def source
    (coins : C → Coins P.Carrier IB × Coins R.Carrier IN)
    (responses : Input roles Key Block Link Body →
      (P.Carrier × P.Carrier) × (R.Carrier × R.Carrier))
    (fallback : (P.Carrier × P.Carrier) × (R.Carrier × R.Carrier))
    (cutOracle : (Input roles Key Block Link Body → Link × C) → Key → JointResponse.Oracle P R)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context) :
    SelectionSource roles Key Block Link Body C (JointResponse.Oracle P R)
      P.Carrier R.Carrier IB IN where
  lists key W := ((committedCandidates P.backend W.1 param.first.cutoff).image (param.first.view key),
    (committedCandidates R.backend W.2 param.second.cutoff).image (param.second.view key))
  coins := coins
  responses := Selection.responsesAt responses fallback
  oracle := cutOracle
  oracle_off := cutOff

end JointParam

variable {B I J SlotB PadB Other PadN CB CN : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
  [Fintype I] [DecidableEq I] [Fintype J] [Fintype Other]
  [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN]
variable {p shared maskBits M K : ℕ} [Fact p.Prime]
variable {A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K}
  {P : FieldBackend B k s n t} {R : FieldBackend (ZMod p) k s n t}

/-- Final authentication consumes the stored selection data together with
the frontend rows. Its statement constructor always appends both fingerprint
equations in both fields, so callers cannot drop them at the backend handoff. -/
def authenticate (data : StatementData A P R)
    (oracle : JointResponse.Oracle P.participant R.participant)
    (coin : JointResponse.Coin P.participant R.participant)
    (response : JointResponse.Response P.participant R.participant) (cutoff : ℕ × ℕ) :
    Application.Authentication A P R where
  prefixData := data
  oracle := oracle
  coin := coin
  response := response
  cutoff := cutoff

theorem authenticate_statement (data : StatementData A P R)
    (oracle : JointResponse.Oracle P.participant R.participant)
    (coin : JointResponse.Coin P.participant R.participant)
    (response : JointResponse.Response P.participant R.participant) (cutoff : ℕ × ℕ) :
    (authenticate data oracle coin response cutoff).statement = data.statement := rfl

end LfzkV2.Current.ZkJoint
