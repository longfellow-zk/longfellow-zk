import polygero.Protocol.ResponseSemantics
import Mathlib.LinearAlgebra.Lagrange

/-!
# Shared-column polynomial relations

This file supplies the bounded response pair and generic bookkeeping for
pointwise polynomial and direct-product relations on one common set of columns.
The concrete paper verifier is defined in `Protocol/Verifier.lean`.
-/

namespace RecursivePolygero.Local

open Finset Polynomial
open Codes

variable {F : Type*} [Field F] [DecidableEq F]
variable {n m k s kappa A t : Nat}

/-- The paper's bounded primary and arithmetic response polynomials. -/
structure LigeroPayload (F : Type*) [Field F] (k s : Nat) where
  primary : DegreeLT F (k + s)
  arithmetic : DegreeLT F (2 * k)

/-- A polynomial response over a finite field is finite coefficient data. -/
noncomputable instance ligeroPayloadFintype [Fintype F] :
    Fintype (LigeroPayload F k s) :=
  Fintype.ofEquiv (DegreeLT F (k + s) × DegreeLT F (2 * k))
    { toFun := fun payload =>
        { primary := payload.1, arithmetic := payload.2 }
      invFun := fun payload => (payload.primary, payload.arithmetic)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Evaluation-space verifier data.  `extra` is deliberately part of the
local relation; it is where direct-product or other protocol-specific column
checks live. -/
structure SharedColumnVerifier
    (C : RSCode F n (k + s)) (m k s : Nat) where
  semantics : ResponseSemantics C m k s (2 * k)
  extra : Fin n → (Fin m → F) → Bool

namespace SharedColumnVerifier

variable {C : RSCode F n (k + s)}

/-- The paper's direct product checks, expressed in evaluation space. -/
def directProductExtra (left right output : Fin t → Fin m)
    (_z : Fin n) (values : Fin m → F) : Bool :=
  decide (∀ row, values (left row) * values (right row) = values (output row))

@[simp] theorem directProductExtra_eq_true_iff
    (left right output : Fin t → Fin m) (z : Fin n) (values : Fin m → F) :
    directProductExtra left right output z values = true ↔
      ∀ row, values (left row) * values (right row) = values (output row) := by
  simp [directProductExtra]

/-- Combine arithmetic-response semantics with the three product-row embeddings. -/
def directProduct
    (semantics : ResponseSemantics C m k s (2 * k))
    (left right output : Fin t → Fin m) : SharedColumnVerifier C m k s where
  semantics := semantics
  extra := directProductExtra left right output

/-- All columns on which the complete verifier-local relation is true. -/
noncomputable def goodColumns
    (V : SharedColumnVerifier C m k s)
    (W : Fin m → Word F n) (B : Challenge F m s)
    (payload : LigeroPayload F k s) : Finset (Fin n) :=
  Finset.univ.filter fun z =>
    (payload.primary : F[X]).eval (C.node z) = response C W B z ∧
    (payload.arithmetic : F[X]).eval (C.node z) =
      V.semantics.pointwise B z (fun i => W i z) ∧
    V.extra z (fun i => W i z) = true

@[simp] theorem mem_goodColumns
    (V : SharedColumnVerifier C m k s)
    (W : Fin m → Word F n) (B : Challenge F m s)
    (payload : LigeroPayload F k s) (z : Fin n) :
    z ∈ V.goodColumns W B payload ↔
      (payload.primary : F[X]).eval (C.node z) = response C W B z ∧
      (payload.arithmetic : F[X]).eval (C.node z) =
        V.semantics.pointwise B z (fun i => W i z) ∧
      V.extra z (fun i => W i z) = true := by
  simp [goodColumns]


end SharedColumnVerifier
end RecursivePolygero.Local
