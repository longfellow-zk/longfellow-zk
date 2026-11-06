import LfzkV2.Current.ApplicationStatement
import LfzkV2.Current.BackendPositions
import LfzkV2.Current.JointResponse
import LfzkV2.Current.Replay
import Mathlib.LinearAlgebra.Lagrange

/-! Pure v2 backend body decoding and opening-boundary framing. H/Z are
evaluations at the first oracle nodes, decoded by interpolation. The finite
coefficient representation belongs to the algebraic backend only. This module
contains no execution, charging or accepted-failure assumptions. -/
noncomputable section
namespace LfzkV2.Current

namespace Replay.Encoding
variable {g : Geometry} {fields : Fields} {Advice Auth Key Block C Response : Type}

/-- The opening boundary writes the complete response pair. Earlier block
encoders are preserved; this is an immutable definition of the complete
encoder, not a change to transcript state during verification. -/
def withOpening (earlier : Encoding g fields Advice Auth Key Block C)
    (responses : Output g fields Advice Auth → Response) (encode : Response → Block) :
    Encoding g fields Advice Auth Key Block C where
  context := earlier.context
  block proof i past := if i = g.openingIndex then encode (responses proof) else earlier.block proof i past

@[simp] theorem withOpening_context (earlier : Encoding g fields Advice Auth Key Block C)
    (responses : Output g fields Advice Auth → Response) (encode : Response → Block)
    (proof : Output g fields Advice Auth) :
    (earlier.withOpening responses encode).context proof = earlier.context proof := rfl

@[simp] theorem withOpening_block (earlier : Encoding g fields Advice Auth Key Block C)
    (responses : Output g fields Advice Auth → Response) (encode : Response → Block)
    (proof : Output g fields Advice Auth) (past : Fin g.openingIndex.val → C) :
    (earlier.withOpening responses encode).block proof g.openingIndex past = encode (responses proof) := by
  simp only [withOpening, ↓reduceIte]

theorem withOpening_block_earlier (earlier : Encoding g fields Advice Auth Key Block C)
    (responses : Output g fields Advice Auth → Response) (encode : Response → Block)
    (proof : Output g fields Advice Auth) (i : Fin g.roles.length) (past : Fin i.val → C)
    (hi : i ≠ g.openingIndex) :
    (earlier.withOpening responses encode).block proof i past = earlier.block proof i past := by
  simp only [withOpening, if_neg hi]

end Replay.Encoding

namespace Response
variable {g : Geometry} {F G : Type}

/-- Coefficient decoding preserves every field cell and has a genuine
inverse. The wire representation need not itself carry field operations. -/
def mapEquiv (field : F ≃ G) : Response g F ≃ Response g G where
  toFun response := ⟨field ∘ response.h,field ∘ response.z⟩
  invFun response := ⟨field.symm ∘ response.h,field.symm ∘ response.z⟩
  left_inv response := by
    cases response
    simp only [Function.comp_def, Equiv.symm_apply_apply]
  right_inv response := by
    cases response
    simp only [Function.comp_def, Equiv.apply_symm_apply]

/-- Evaluation at distinct nodes is invertible by Lagrange interpolation.
Wire samples must never be confused with monomial coefficients. -/
def evaluationEquiv (F : Type) [Field F] [DecidableEq F] {d : ℕ}
    (nodes : Fin d → F) (hinj : Function.Injective nodes) :
    Polynomial.degreeLT F d ≃ (Fin d → F) where
  toFun p i := (p : Polynomial F).eval (nodes i)
  invFun values := ⟨Lagrange.interpolate Finset.univ nodes values, by
    rw [Polynomial.mem_degreeLT]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) values hinj.injOn⟩
  left_inv p := by
    apply Subtype.ext
    exact (Lagrange.eq_interpolate hinj.injOn
      (by simpa only [Finset.card_univ, Fintype.card_fin] using
        Polynomial.mem_degreeLT.mp p.property)).symm
  right_inv values := by
    funext i
    exact Lagrange.eval_interpolate_at_node values hinj.injOn (Finset.mem_univ i)

theorem evaluationEquiv_eval (F : Type) [Field F] [DecidableEq F] {d : ℕ}
    (nodes : Fin d → F) (hinj : Function.Injective nodes) (values : Fin d → F) (i : Fin d) :
    (((evaluationEquiv F nodes hinj).symm values : Polynomial.degreeLT F d) : Polynomial F).eval
      (nodes i) = values i :=
  congrFun ((evaluationEquiv F nodes hinj).apply_symm_apply values) i

/-- The transmitted H/Z arrays are samples on the oracle prefix. Decode
them by evaluation-domain interpolation, as `interpolate_range(k, ...)` does
in the runtime verifier. -/
def polynomialEquiv (g : Geometry) (F : Type) [Field F] [DecidableEq F]
    (hNodes : Fin (g.rowDimension+g.maskingDegree) → F) (hInjective : Function.Injective hNodes)
    (zNodes : Fin (2*g.rowDimension) → F) (zInjective : Function.Injective zNodes) :
    Response g F ≃ RecursivePolygero.Local.LigeroPayload F g.rowDimension g.maskingDegree where
  toFun response := {
    primary := (evaluationEquiv F hNodes hInjective).symm response.h
    arithmetic := (evaluationEquiv F zNodes zInjective).symm response.z }
  invFun response := {
    h := evaluationEquiv F hNodes hInjective response.primary
    z := evaluationEquiv F zNodes zInjective response.arithmetic }
  left_inv response := by cases response; simp only [Equiv.apply_symm_apply]
  right_inv response := by cases response; simp only [Equiv.symm_apply_apply]

end Response

namespace BackendVerifier
open Application RecursivePolygero

variable {g : Geometry} {fields : Fields} {Advice Auth Key Block C : Type}
variable {B I J SlotB PadB Other PadN IB IN : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
  [Fintype I] [DecidableEq I] [Fintype J] [Fintype Other]
  [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN] [Fintype C]
variable {p shared maskBits M K k s n t : ℕ} [Fact p.Prime]
variable (P : FieldBackend B k s n t) (R : FieldBackend (ZMod p) k s n t)

section Coefficients
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Public shared geometry reindexes coefficient lengths, without changing
any decoded field value. -/
def payloadEquiv (participant : FieldBackend F k s n t)
    (hrow : g.rowDimension = k) (hmask : g.maskingDegree = s) (hproduct : 2*k ≤ n) :
    Response g F ≃ participant.participant.Response :=
  let hlength : g.rowDimension+g.maskingDegree ≤ participant.backend.n := by
    simpa only [hrow,hmask,participant.dimension,participant.batching] using participant.backend.primary_le
  let zlength : 2*g.rowDimension ≤ participant.backend.n := by
    simpa only [hrow,participant.columns] using hproduct
  let nodes := fun (d : ℕ) (hd : d ≤ participant.backend.n) (i : Fin d) =>
    participant.backend.domain.point (LigeroFamily.codePosition ⟨i.val,lt_of_lt_of_le i.isLt hd⟩)
  let injective := fun (d : ℕ) (hd : d ≤ participant.backend.n) =>
    show Function.Injective (nodes d hd) from by
      intro i j h
      have he := participant.backend.domain.injective h
      exact Fin.ext (congrArg (fun z : LigeroFamily.Position participant.backend.r participant.backend.w
        participant.backend.n => match z with | .inl _ => 0 | .inr i => i.val) he)
  (Response.polynomialEquiv g F (nodes _ hlength) (injective _ hlength)
    (nodes _ zlength) (injective _ zlength)).trans (Equiv.cast (by
    change RecursivePolygero.Local.LigeroPayload F g.rowDimension g.maskingDegree =
      RecursivePolygero.Local.LigeroPayload F (participant.backend.r+participant.backend.w)
        participant.backend.s
    rw [hrow,hmask,participant.dimension,participant.batching]))

end Coefficients

/-- Both full payloads are decoded from the proof body in their fixed field
order. The equivalences also give the canonical inverse used at the opening
boundary; a projection onto one participant would have no such inverse. -/
def responsesEquiv (binary : fields .binary ≃ B) (prime : fields .prime ≃ ZMod p)
    (hrow : g.rowDimension = k) (hmask : g.maskingDegree = s) (hproduct : 2*k ≤ n) :
    (Response g (fields .binary) × Response g (fields .prime)) ≃
      JointResponse.Response P.participant R.participant :=
  Equiv.prodCongr ((Response.mapEquiv binary).trans (payloadEquiv P hrow hmask hproduct))
    ((Response.mapEquiv prime).trans (payloadEquiv R hrow hmask hproduct))

def responses (binary : fields .binary ≃ B) (prime : fields .prime ≃ ZMod p)
    (hrow : g.rowDimension = k) (hmask : g.maskingDegree = s) (hproduct : 2*k ≤ n)
    (proof : Replay.Output g fields Advice Auth) : JointResponse.Response P.participant R.participant :=
  responsesEquiv P R binary prime hrow hmask hproduct
    (proof.body.binaryBackend.response,proof.body.primeBackend.response)

def encodeResponses (binary : fields .binary ≃ B) (prime : fields .prime ≃ ZMod p)
    (hrow : g.rowDimension = k) (hmask : g.maskingDegree = s) (hproduct : 2*k ≤ n)
    (wire : Response g (fields .binary) × Response g (fields .prime) → Block)
    (response : JointResponse.Response P.participant R.participant) : Block :=
  wire ((responsesEquiv P R binary prime hrow hmask hproduct).symm response)

omit [Algebra (ZMod 2) B] in
theorem encodeResponses_injective (binary : fields .binary ≃ B) (prime : fields .prime ≃ ZMod p)
    (hrow : g.rowDimension = k) (hmask : g.maskingDegree = s) (hproduct : 2*k ≤ n)
    (wire : Response g (fields .binary) × Response g (fields .prime) → Block)
    (hwire : Function.Injective wire) :
    Function.Injective (encodeResponses P R binary prime hrow hmask hproduct wire) :=
  hwire.comp (responsesEquiv P R binary prime hrow hmask hproduct).symm.injective

omit [Algebra (ZMod 2) B] in
theorem encodeResponses_body (binary : fields .binary ≃ B) (prime : fields .prime ≃ ZMod p)
    (hrow : g.rowDimension = k) (hmask : g.maskingDegree = s) (hproduct : 2*k ≤ n)
    (wire : Response g (fields .binary) × Response g (fields .prime) → Block)
    (proof : Replay.Output g fields Advice Auth) :
    encodeResponses P R binary prime hrow hmask hproduct wire (responses P R binary prime hrow hmask hproduct proof) =
      wire (proof.body.binaryBackend.response,proof.body.primeBackend.response) :=
  congrArg wire ((responsesEquiv P R binary prime hrow hmask hproduct).symm_apply_apply _)


end BackendVerifier
end LfzkV2.Current
