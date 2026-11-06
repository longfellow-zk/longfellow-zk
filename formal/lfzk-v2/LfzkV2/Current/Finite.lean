import LfzkV2.Current.Prefix

/-! Finite logical message and oracle-input spaces. The oracle alphabet is a
finite ideal sample space; canonical byte encoding and ideal-XOF sampling are
separate correspondence obligations. These instances add no equality test or
alternative runtime representation. -/
noncomputable section
namespace LfzkV2.Current

namespace Input

/-- An ordinary boundary contains its indexed history and fresh block; the
final seal contains the completed history and the complete proof body. -/
def finiteEquiv (roles : List Role) (Context Block Link Body : Type) :
    Input roles Context Block Link Body ≃
      ((i : Fin roles.length) × (History Context Block Link i.val × Block)) ⊕
        (History Context Block Link roles.length × Body) where
  toFun
    | .round i history block => .inl ⟨i,history,block⟩
    | .finalSeal history body => .inr (history,body)
  invFun
    | .inl ⟨i,history,block⟩ => .round i history block
    | .inr (history,body) => .finalSeal history body
  left_inv point := by cases point <;> rfl
  right_inv point := by rcases point with ⟨i,history,block⟩ | ⟨history,body⟩ <;> rfl

instance fintype (roles : List Role) (Context Block Link Body : Type)
    [Fintype Context] [Fintype Block] [Fintype Link] [Fintype Body] :
    Fintype (Input roles Context Block Link Body) :=
  Fintype.ofEquiv
    (((i : Fin roles.length) × (History Context Block Link i.val × Block)) ⊕
      (History Context Block Link roles.length × Body))
    (finiteEquiv roles Context Block Link Body).symm

theorem card (roles : List Role) (Context Block Link Body : Type)
    [Fintype Context] [Fintype Block] [Fintype Link] [Fintype Body] :
    Fintype.card (Input roles Context Block Link Body) =
      (∑ i : Fin roles.length, Fintype.card (History Context Block Link i.val) * Fintype.card Block) +
        Fintype.card (History Context Block Link roles.length) * Fintype.card Body := by
  rw [Fintype.card_congr (finiteEquiv roles Context Block Link Body)]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod]

end Input

instance batchSamplesFintype (g : Geometry) (F : Fields) (side : Side)
    [Fintype (F side)] : Fintype (BatchSamples g F side) := by
  apply Fintype.ofInjective (fun samples => (samples.affine,samples.polynomials))
  intro first second h
  cases first
  cases second
  cases h
  rfl

instance layerPayloadFintype (F : Type) (rounds : ℕ) [Fintype F] :
    Fintype (LayerPayload F rounds) := by
  apply Fintype.ofInjective (fun payload => (payload.coefficients,payload.cross,payload.claims))
  intro first second h
  cases first
  cases second
  cases h
  rfl

instance packingPayloadFintype (F : Type) (degree : ℕ) [Fintype F] :
    Fintype (PackingPayload F degree) := by
  unfold PackingPayload
  split_ifs <;> infer_instance

instance responseFintype (g : Geometry) (F : Type) [Fintype F] : Fintype (Response g F) := by
  apply Fintype.ofInjective (fun response => (response.h,response.z))
  intro first second h
  cases first
  cases second
  cases h
  rfl

instance fieldBodyFintype (g : Geometry) (F : Fields) (side : Side)
    [Fintype (F side)] : Fintype (FieldBody g F side) := by
  apply Fintype.ofInjective (fun body => (body.response,body.rows))
  intro first second h
  cases first
  cases second
  cases h
  rfl

instance bodyFintype (g : Geometry) (F : Fields) (Advice Authentication : Type)
    [∀ side, Fintype (F side)] [Fintype Advice] [Fintype Authentication] :
    Fintype (Body g F Advice Authentication) := by
  apply Fintype.ofInjective (fun body =>
    (body.commitment,body.fingerprints,body.mu,body.advice,body.binary,body.prime,
      body.packing,body.binaryBackend,body.primeBackend,body.authentication))
  intro first second h
  cases first
  cases second
  cases h
  rfl

instance proofFintype (g : Geometry) (F : Fields) (Advice Authentication : Type)
    [∀ side, Fintype (F side)] [Fintype Advice] [Fintype Authentication] :
    Fintype (Proof g F Advice Authentication) := by
  apply Fintype.ofInjective (fun proof => (proof.body,proof.finalSeal))
  intro first second h
  cases first
  cases second
  cases h
  rfl

instance samplesFintype (g : Geometry) (F : Fields) [∀ side, Zero (F side)]
    [∀ side, Fintype (F side)] (role : Role) : Fintype (Samples g F role) := by
  classical
  cases role <;> dsimp only [Samples] <;> infer_instance

instance roundPayloadFintype (g : Geometry) (F : Fields) [∀ side, Fintype (F side)]
    (role : Role) : Fintype (RoundPayload g F role) := by
  cases role <;> dsimp only [RoundPayload] <;> infer_instance

end LfzkV2.Current
