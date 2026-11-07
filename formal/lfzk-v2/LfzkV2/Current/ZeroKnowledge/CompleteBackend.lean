import LfzkV2.Current.ZeroKnowledge.BackendProfile
import LfzkV2.Current.ZeroKnowledge.CompleteOpening

/-! The zero-cell backend simulation passes the actual current two-field
compiler. This is completeness of the explicit public correction at Q,
without any satisfying-witness or verifier-acceptance premise. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteBackend

set_option maxHeartbeats 800000

open Merkle Merkle.MH LigeroFamily RecursivePolygero RecursivePolygero.Local
open scoped Classical

variable {B N : Type} [Field B] [Field N] [Fintype B] [Fintype N]
variable [DecidableEq B] [DecidableEq N]
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
variable (binaryCells primeCells countB countN : ℕ)

def first := (ConcreteSetup.backend binaryNodes binaryCells).indexed countB
def second := (ConcreteSetup.backend primeNodes primeCells).indexed countN

abbrev Masks := Backend.ProfileTape binaryNodes binaryCells × Backend.ProfileTape primeNodes primeCells

def oracle (tape : Masks binaryNodes primeNodes binaryCells primeCells) :
    JointResponse.Oracle (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant :=
  (PolygeroZk.oracle (Backend.profileGeometry binaryNodes) 0 tape.1,
    PolygeroZk.oracle (Backend.profileGeometry primeNodes) 0 tape.2)

def responses (Q : QuerySet 2443 84)
    (statement : JointResponse.Statement (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant)
    (coin : JointResponse.Coin (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant)
    (tape : Masks binaryNodes primeNodes binaryCells primeCells) :
    JointResponse.Response (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant :=
  ((Backend.jointSimulate (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
      Q 0 statement coin tape).1.2,
    (Backend.jointSimulate (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
      Q 0 statement coin tape).2.2)

def familyOracle (tape : Masks binaryNodes primeNodes binaryCells primeCells) :
    (Joint.Pair.family (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant).Oracle :=
  (Joint.Pair.oracleEquiv _ _).symm (oracle binaryNodes primeNodes binaryCells primeCells countB countN tape)

theorem verifies (Q : QuerySet 2443 84)
    (statement : JointResponse.Statement (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant)
    (coin : JointResponse.Coin (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant)
    (tape : Masks binaryNodes primeNodes binaryCells primeCells) :
    (Joint.Pair.family (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant).Verify
      ((Joint.Pair.statementEquiv _ _).symm statement)
      (familyOracle binaryNodes primeNodes binaryCells primeCells countB countN tape)
      ((Joint.Pair.coinEquiv _ _).symm coin)
      ((Joint.Pair.responseEquiv _ _).symm
        (responses binaryNodes primeNodes binaryCells primeCells countB countN Q statement coin tape)) Q := by
  apply (Joint.Pair.verify_iff _ _ _ _ _ _ _).mpr
  rw [familyOracle,Equiv.apply_symm_apply]
  exact Backend.jointSimulate_verifies (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
    (by decide : 84+265+12 ≤ 2443) Q 0 statement coin tape

variable {Enc : Type}
variable [Inhabited (Joint.Pair.family (first binaryNodes binaryCells countB).participant
  (second primeNodes primeCells countN).participant).Leaf]
variable (scheme : Scheme (Fin 2443 × Digest)
  (Joint.Pair.family (first binaryNodes binaryCells countB).participant
    (second primeNodes primeCells countN).participant).Leaf Digest Enc)

theorem compiled_verifies (indices : Fin 84 ↪ Fin 2443)
    (statement : JointResponse.Statement (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant)
    (coin : JointResponse.Coin (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant)
    (tape : Masks binaryNodes primeNodes binaryCells primeCells) (nonces : Fin 2443 → Digest) :
    let family := Joint.Pair.family (first binaryNodes binaryCells countB).participant
      (second primeNodes primeCells countN).participant
    let W := familyOracle binaryNodes primeNodes binaryCells primeCells countB countN tape
    let columns := family.columnsEquiv W
    let Q := OrderedOpening.query indices
    (family.compiler (by decide)).Accepts scheme
      ((Joint.Pair.statementEquiv _ _).symm statement)
      (root scheme 2443 (fun i => (i,nonces i)) columns)
      ((Joint.Pair.coinEquiv _ _).symm coin)
      ((Joint.Pair.responseEquiv _ _).symm
        (responses binaryNodes primeNodes binaryCells primeCells countB countN Q statement coin tape))
      Q (CompleteOpening.claim scheme (fun i nonce => (i,nonce)) indices nonces columns) := by
  intro family W columns Q
  refine ⟨rfl,CompleteOpening.claim_accepts scheme _ indices (by decide) nonces columns,?_⟩
  have values : ∀ i ∈ Q.coordinates,
      family.columnsEquiv W i = (CompleteOpening.claim scheme (fun i nonce => (i,nonce)) indices nonces columns).a i := by
    intro i inside
    exact (CompleteOpening.claim_value scheme (fun i nonce => (i,nonce)) indices nonces columns i inside).symm
  have opened : (family.compiler (by decide : 0<84)).protocol.openOracle W Q =
      (family.compiler (by decide : 0<84)).protocol.openOracle
        ((family.compiler (by decide : 0<84)).oracleOfClaim
          (CompleteOpening.claim scheme (fun i nonce => (i,nonce)) indices nonces columns).a) Q :=
    (family.compiler (by decide : 0<84)).open_congr W
    ((family.compiler (by decide : 0<84)).oracleOfClaim
      (CompleteOpening.claim scheme (fun i nonce => (i,nonce)) indices nonces columns).a) Q
    (fun i inside => by
      rw [Bcs.Compiler.columns_oracleOfClaim]
      exact values i inside)
  rw [← opened]
  exact (family.compiler_verify (by decide) _ _ _ _ _).mpr
    (verifies binaryNodes primeNodes binaryCells primeCells countB countN Q statement coin tape)

end LfzkV2.Current.ZeroKnowledge.CompleteBackend
