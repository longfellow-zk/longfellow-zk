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

/-- Transcript-assisted extraction, as in Polygero (`scanRecoverAt`): in each
field the backend coin and response identify the good columns of the
committed rows, each row is uniquely decoded on them, and the recovered
tableau is projected to its selected cells. It forms no candidate list and
reads no list-decoding cutoff. -/
def StatementData.recover {A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K}
    {P : FieldBackend B k s n t} {R : FieldBackend (ZMod p) k s n t} (d : StatementData A P R)
    (oracle : JointResponse.Oracle P.participant R.participant)
    (coin : JointResponse.Coin P.participant R.participant)
    (response : JointResponse.Response P.participant R.participant) :
    Option (Selection.Pair B (ZMod p) IB IN) :=
  (scanRecoverAt P.backend d.statement.1 oracle.1 coin.1 response.1).bind fun gB =>
    (scanRecoverAt R.backend d.statement.2 oracle.2 coin.2 response.2).map fun gN =>
      (FingerprintRows.view P.backend d.primaryB
        (fun i => A.binaryLayout (.inl i)) (fun j => A.binaryLayout (.inr j)) gB,
       FingerprintRows.view R.backend d.primaryN
        (fun i => A.primeLayout (.inl i)) (fun j => A.primeLayout (.inr j)) gN)

namespace Authentication
variable {A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K}
  {P : FieldBackend B k s n t} {R : FieldBackend (ZMod p) k s n t}
variable (a : Authentication A P R)

def statement : JointResponse.Statement P.participant R.participant :=
  a.prefixData.statement

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

/-- Transcript-assisted extraction at the authenticated data. -/
def recover : Option (Selection.Pair B (ZMod p) IB IN) :=
  a.prefixData.recover a.oracle a.coin a.response

/-- Recovery fails exactly on the backend's own failure event. -/
theorem recover_isSome (hrecovered : ¬ JointResponse.failure P.participant R.participant
    a.statement a.oracle a.coin a.response) : a.recover.isSome := by
  obtain ⟨gB,hB⟩ : ∃ gB, scanRecoverAt P.backend a.prefixData.statement.1 a.oracle.1 a.coin.1 a.response.1 = some gB :=
    Option.ne_none_iff_exists'.mp fun h => hrecovered (Or.inl h)
  obtain ⟨gN,hN⟩ : ∃ gN, scanRecoverAt R.backend a.prefixData.statement.2 a.oracle.2 a.coin.2 a.response.2 = some gN :=
    Option.ne_none_iff_exists'.mp fun h => hrecovered (Or.inr h)
  simp only [recover,StatementData.recover,hB,hN,Option.bind_some]
  rfl

/-- Every recovered pair satisfies the frontend rows of both fields. The
proof reads only the uniquely decoded tableaux and the appended affine
statements (`scanRecoverAt_valid`); it uses no candidate list. -/
theorem recover_rows (w : Selection.Pair B (ZMod p) IB IN) (hw : a.recover = some w) :
    RowsHold A.binary.rows (A.binaryRead w) ∧ RowsHold A.primeRows (A.primeRead w) := by
  simp only [recover,StatementData.recover,Option.bind_eq_some_iff,Option.map_eq_some_iff] at hw
  obtain ⟨gB,hB,gN,hN,rfl⟩ := hw
  have hb := FingerprintRows.decoded_view P.backend A.binary.rows a.primaryB _ _ a.coinsB a.targetB
    a.equationsB a.oracle.1 a.coin.1 a.response.1 gB hB
  have hn := FingerprintRows.decoded_view R.backend A.primeRows a.primaryN _ _ a.coinsN a.targetN
    a.equationsN a.oracle.2 a.coin.2 a.response.2 gN hN
  exact ⟨(FingerprintRows.rows_realized A.binaryLayout A.binary.rows _).mpr hb.1,
    (FingerprintRows.rows_realized A.primeLayout A.primeRows _).mpr hn.1⟩

/-- Outside the backend events, the recovered pair is the pair that early
fingerprint selection picks from the commitment-only lists. This
identification is used only to charge the frontend's algebraic event to a
witness fixed before the frontend challenges. -/
theorem recover_eq_extract (hgood : ¬ a.BackendBad) : a.recover = a.context.extract := by
  obtain ⟨gB,gN,hB,hN,hs,_,_⟩ := BackendSelection.recovered_selected P.participant R.participant
    A.binary.rows A.primeRows a.primaryB a.primaryN (fun i => A.binaryLayout (.inl i))
    (fun i => A.primeLayout (.inl i)) (fun j => A.binaryLayout (.inr j)) (fun j => A.primeLayout (.inr j))
    a.coinsB a.coinsN a.targetB a.targetN a.equationsB a.equationsN a.oracle a.coin a.response a.cutoff
    (fun h => hgood (Or.inl h)) (fun h => hgood (Or.inr (Or.inl h)))
    (fun h => hgood (Or.inr (Or.inr (Or.inl h)))) (fun h => hgood (Or.inr (Or.inr (Or.inr h))))
  have hB' : scanRecoverAt P.backend a.prefixData.statement.1 a.oracle.1 a.coin.1 a.response.1 = some gB := hB
  have hN' : scanRecoverAt R.backend a.prefixData.statement.2 a.oracle.2 a.coin.2 a.response.2 = some gN := hN
  rw [show a.context.extract = _ from hs]
  simp only [recover,StatementData.recover,hB',hN']
  rfl

/-- The recovered pair is a satisfying application witness, or the backend
events hold, or the frontend's algebraic event holds for the early-selected
pair. Both compiler reductions and the prime handoff are proved by
composition; there is no assumed application failure cover. -/
theorem extraction_reduction :
    (∃ w, a.recover = some w ∧ A.True w) ∨ a.BackendBad ∨
      (∃ w, a.context.extract = some w ∧ A.Bad w) := by
  by_cases hbad : a.BackendBad
  · exact Or.inr (Or.inl hbad)
  obtain ⟨w,hw⟩ := Option.isSome_iff_exists.mp (a.recover_isSome fun h => hbad (Or.inl h))
  obtain ⟨hb,hn⟩ := a.recover_rows w hw
  rcases A.rows_reduction w hb hn with htrue | hfront
  · exact Or.inl ⟨w,hw,htrue⟩
  · exact Or.inr (Or.inr ⟨w,(a.recover_eq_extract hbad) ▸ hw,hfront⟩)

/-- Specialization to failure of transcript-assisted extraction, retaining
the early-selected pair for the later query-local causal cover. -/
theorem extraction_failure_cover
    (hfailure : ¬ ∃ w, a.recover = some w ∧ A.True w) :
    a.BackendBad ∨ (∃ w, a.context.extract = some w ∧ A.Bad w) :=
  a.extraction_reduction.resolve_left hfailure

end Authentication
end LfzkV2.Current.Application
