import LfzkV2.Current.ApplicationStatement

/-! End-to-end algebraic extraction cover.  The canonical-field backend
wrapper makes the prime carrier definitionally `ZMod p`: no field conversion
or correspondence between independently chosen field instances is assumed.
The authenticated statement is the exact compiler/handoff row list followed
by the two dedicated fingerprint rows in each participant. -/
noncomputable section
namespace LfzkV2.Current.Application
open RecursivePolygero NonrecursiveFS Counting SumcheckV2 WitnessSelection

variable {B I J SlotB PadB Other PadN IB IN CB CN : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
  [Fintype I] [DecidableEq I] [Fintype J] [Fintype Other]
  [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN]
variable {p shared maskBits M K k s n t : ℕ} [Fact p.Prime]

/-- The prefix fixes its affine statement data. Late authentication adds
only the recovered oracle and backend exchange. Replay establishes their
consistency and query causality; this record assumes no soundness result. -/
structure Authentication
    (A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K)
    (P : FieldBackend B k s n t) (R : FieldBackend (ZMod p) k s n t)
    extends prefixData : StatementData A P R where
  oracle : JointResponse.Oracle P.participant R.participant
  coin : JointResponse.Coin P.participant R.participant
  response : JointResponse.Response P.participant R.participant
  cutoff : ℕ × ℕ

namespace Authentication
variable {A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K}
  {P : FieldBackend B k s n t} {R : FieldBackend (ZMod p) k s n t}
variable (a : Authentication A P R)

def statement : JointResponse.Statement P.participant R.participant :=
  a.prefixData.statement

theorem statement_prefixData : a.prefixData.statement = a.statement := rfl

theorem compile_prefixData : StatementData.compile ⟨A,a.prefixData⟩ = a.statement := rfl

/-- A concrete codec identity suffices to identify the backend statement.
The reader has no oracle or final-proof argument: only the supplied prefix
type, normally a batching preimage paired with its strict prior answers. -/
theorem statement_of_prefix {Prefix : Type}
    (read : Prefix → Σ A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K,
      StatementData A P R) (boundPrefix : Prefix)
    (hread : read boundPrefix = ⟨A,a.prefixData⟩) :
    StatementData.compile (read boundPrefix) = a.statement := by
  rw [hread]
  rfl


def context : Selection.Context B (ZMod p) IB IN where
  binaryList := (committedCandidates P.backend a.oracle.1 a.cutoff.1).image
    (FingerprintRows.view P.backend a.primaryB
      (fun i => A.binaryLayout (.inl i)) (fun j => A.binaryLayout (.inr j)))
  primeList := (committedCandidates R.backend a.oracle.2 a.cutoff.2).image
    (FingerprintRows.view R.backend a.primaryN
      (fun i => A.primeLayout (.inl i)) (fun j => A.primeLayout (.inr j)))
  binaryCoins := a.coinsB
  primeCoins := a.coinsN
  binaryResponse := a.targetB
  primeResponse := a.targetN

def BackendBad : Prop :=
  JointResponse.failure P.participant R.participant a.statement a.oracle a.coin a.response ∨
    decodedOutsideList P.backend a.statement.1 a.oracle.1 a.coin.1 a.response.1 a.cutoff.1 ∨
    decodedOutsideList R.backend a.statement.2 a.oracle.2 a.coin.2 a.response.2 a.cutoff.2 ∨
    a.context.Collision

/-- Actual recovery of the two appended affine statements identifies the
selected pair and authenticates the rows consumed by the frontend reduction.
Backend lifts with identical selected cells introduce no new candidate. -/
theorem rows_or_backend :
    (∃ w, a.context.extract = some w ∧
      RowsHold A.binary.rows (A.binaryRead w) ∧ RowsHold A.primeRows (A.primeRead w)) ∨
      a.BackendBad := by
  exact BackendSelection.extraction_reduction P.participant R.participant
    A.binary.rows A.primeRows a.primaryB a.primaryN A.binaryLayout A.primeLayout
    a.coinsB a.coinsN a.targetB a.targetN a.equationsB a.equationsN
    a.oracle a.coin a.response a.cutoff

/-- The selected pair is a satisfying application witness, or recovery,
list membership, fingerprint selection, or an explicitly located frontend
algebraic event fails.  Both compiler reductions and the prime handoff are
proved by composition; there is no assumed application failure cover. -/
theorem extraction_reduction :
    (∃ w, a.context.extract = some w ∧ A.True w) ∨ a.BackendBad ∨
      (∃ w, a.context.extract = some w ∧ A.Bad w) := by
  rcases a.rows_or_backend with ⟨w,hs,hb,hn⟩ | hbackend
  · rcases A.rows_reduction w hb hn with htrue | hbad
    · exact Or.inl ⟨w,hs,htrue⟩
    · exact Or.inr (Or.inr ⟨w,hs,hbad⟩)
  · exact Or.inr (Or.inl hbackend)

/-- Specialization to extractor failure, retaining the exact selected pair
for the later query-local causal cover. -/
theorem extraction_failure_cover
    (hfailure : ¬ ∃ w, a.context.extract = some w ∧ A.True w) :
    a.BackendBad ∨ (∃ w, a.context.extract = some w ∧ A.Bad w) := by
  exact a.extraction_reduction.resolve_left hfailure

/-- A fixed earlier extractor output can be substituted once replay has
identified its selection context with the late authenticated context. -/
theorem selected_failure_cover (selected : Option A.Pair)
    (hagrees : selected = a.context.extract)
    (hfailure : ¬ ∃ w, selected = some w ∧ A.True w) :
    a.BackendBad ∨ (∃ w, selected = some w ∧ A.Bad w) := by
  rw [hagrees] at hfailure ⊢
  exact a.extraction_failure_cover hfailure

end Authentication
end LfzkV2.Current.Application
