import LfzkV2.Current.Application

/-! The canonical late affine statement compiler consumes only frontend
data and already-bound fingerprint messages.  Backend answers, opened rows
and authentication are deliberately absent from this input type. -/
noncomputable section
namespace LfzkV2.Current.Application
open RecursivePolygero SumcheckV2 WitnessSelection

variable {k s n t : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A participant whose carrier is a specified field.  This is only the
geometry certificate required by the existing joint backend, with the field
kept as a parameter so frontend expressions need no transports. -/
structure FieldBackend (F : Type) [Field F] (k s n t : ℕ) where
  backend : Instance F
  dimension : backend.r + backend.w = k
  batching : backend.s = s
  columns : backend.n = n
  openings : backend.t = t
  linearOnly : backend.nq = 0

def FieldBackend.participant (P : FieldBackend F k s n t) : Joint.Participant k s n t where
  Carrier := F
  field := inferInstance
  finite := inferInstance
  eq := inferInstance
  backend := P.backend
  dimension := P.dimension
  batching := P.batching
  columns := P.columns
  openings := P.openings
  linearOnly := P.linearOnly

variable {B I J SlotB PadB Other PadN IB IN CB CN : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
  [Fintype I] [DecidableEq I] [Fintype J] [Fintype Other]
  [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN]
variable {p shared maskBits M K k s n t : ℕ} [Fact p.Prime]

/-- This is exactly the data needed to construct both appended affine
statements.  The frontend `System` is reconstructed from the strict batching
prefix; the public address maps and equation isomorphisms complete its layout. -/
structure StatementData
    (A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K)
    (P : FieldBackend B k s n t) (R : FieldBackend (ZMod p) k s n t) where
  primaryB : SlotB → Fin P.backend.nw × Fin P.backend.q
  primaryN : Other ⊕ Unit → Fin R.backend.nw × Fin R.backend.q
  coinsB : Coins B IB
  coinsN : Coins (ZMod p) IN
  targetB : B × B
  targetN : ZMod p × ZMod p
  equationsB : P.backend.Equations ≃ Fin
    (A.binary.rows ++ FingerprintRows.rows (fun i => A.binaryLayout (.inl i))
      (fun j => A.binaryLayout (.inr j)) coinsB targetB).length
  equationsN : R.backend.Equations ≃ Fin
    (A.primeRows ++ FingerprintRows.rows (fun i => A.primeLayout (.inl i))
      (fun j => A.primeLayout (.inr j)) coinsN targetN).length

namespace StatementData
variable {A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K}
  {P : FieldBackend B k s n t} {R : FieldBackend (ZMod p) k s n t}

def statement (d : StatementData A P R) : JointResponse.Statement P.participant R.participant :=
  (FingerprintRows.statement P.backend A.binary.rows d.primaryB
    (fun i => A.binaryLayout (.inl i)) (fun j => A.binaryLayout (.inr j))
    d.coinsB d.targetB d.equationsB,
   FingerprintRows.statement R.backend A.primeRows d.primaryN
    (fun i => A.primeLayout (.inl i)) (fun j => A.primeLayout (.inr j))
    d.coinsN d.targetN d.equationsN)

/-- A prefix reader may reconstruct the challenge-dependent generated
circuit together with this data.  The resulting statement is still one fixed
function of that prefix, rather than a caller-supplied late statement. -/
def compile (d : Σ A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K,
    StatementData A P R) : JointResponse.Statement P.participant R.participant :=
  d.2.statement

end StatementData
end LfzkV2.Current.Application
