import LigeroFamily.Code.ReedSolomon
import LfzkV1.LigeroZk.CoreTranslation

/-!
# Core-padding translation over the v7 binary subfield

A core row sampled over the small field can be moved between two witness
blocks in that same field while keeping its opened values. This follows
from the commuting evaluations on the two Reed–Solomon domains. It is a
rowwise support statement for the existing adaptive tape translation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.V7SubfieldPadding

open LigeroFamily LigeroFamily.ReedSolomon Polynomial

variable {K F : Type} [Field K] [Field F] {r w n : ℕ}
variable (emb : K →+* F) (small : Domain K r w n) (large : Domain F r w n)
variable (domainMap : ∀ i, large.point i = emb (small.point i))
variable (hk : r + w ≤ n)
variable (C : MultiplicativeCode F r w n)
variable (baseEq : C.base = evaluationSpace large (r + w))

include domainMap baseEq in
/-- A complete base-row encoding commutes with the field embedding. -/
theorem encode_map (pads : Fin r → K) (witness : Fin w → K) :
    C.encode (emb ∘ pads) (emb ∘ witness) =
      emb ∘ (multiplicativeCode small hk).encode pads witness := by
  let smallCode := multiplicativeCode small hk
  let row := smallCode.encode pads witness
  have hm : row ∈ evaluationSpace small (r + w) := smallCode.encode_mem pads witness
  obtain ⟨p, hp, heval⟩ := (mem_evaluationSpace small).mp hm
  have hmap : emb ∘ row ∈ C.base := by
    rw [baseEq]
    refine (mem_evaluationSpace large).mpr ⟨p.map emb, ?_, ?_⟩
    · exact Polynomial.mem_degreeLT.mpr (Polynomial.degree_map_le.trans_lt (Polynomial.mem_degreeLT.mp hp))
    · intro j
      change emb (row j) = (p.map emb).eval (large.point j)
      rw [heval j, domainMap j, Polynomial.eval_map_apply]
  apply C.base_unique (C.encode_mem _ _) hmap (messagePositions r w n) (by simp [C.k_eq])
  intro j hj
  rcases Finset.mem_image.mp hj with ⟨x, _, rfl⟩
  cases x with
  | inl x =>
    change C.encode _ _ (randomPosition x) = emb (smallCode.encode pads witness (randomPosition x))
    simp
  | inr x =>
    change C.encode _ _ (witnessPosition x) = emb (smallCode.encode pads witness (witnessPosition x))
    simp

include domainMap baseEq in
/-- Keeping the opened columns while replacing the witness block can be
calculated entirely over the subfield when its inputs lie there. -/
theorem translateCorePadding_map (query : QuerySet n r)
    (fromWitness toWitness : Fin w → K) (pads : Fin r → K) :
    translateCorePadding C query (emb ∘ fromWitness) (emb ∘ toWitness) (emb ∘ pads) =
      emb ∘ translateCorePadding (multiplicativeCode small hk) query fromWitness toWitness pads := by
  apply (openedRowEquiv C query (emb ∘ toWitness)).injective
  change openedRow C query.coordinates _ (translateCorePadding C query _ _ _) = openedRow C query.coordinates _ _
  rw [translateCorePadding_opening]
  funext j
  simp only [openedRow, encode_map emb small large domainMap hk C baseEq]
  have h := congrFun (translateCorePadding_opening (multiplicativeCode small hk) query fromWitness toWitness pads) j
  exact (congrArg emb h).symm

include domainMap baseEq in
/-- Rowwise support closure for either direction of the padding translation. -/
theorem translateCorePadding_mem_range (query : QuerySet n r)
    (fromWitness toWitness : Fin w → F) (pads : Fin r → F)
    (hfrom : ∀ j, fromWitness j ∈ Set.range emb)
    (hto : ∀ j, toWitness j ∈ Set.range emb) (hpads : ∀ j, pads j ∈ Set.range emb) :
    ∀ j, translateCorePadding C query fromWitness toWitness pads j ∈ Set.range emb := by
  classical
  have hk : r + w ≤ n := C.k_eq ▸ C.k_le_n
  choose smallFrom hfrom using hfrom
  choose smallTo hto using hto
  choose smallPads hpads using hpads
  rw [show fromWitness = emb ∘ smallFrom from funext fun j => (hfrom j).symm,
    show toWitness = emb ∘ smallTo from funext fun j => (hto j).symm,
    show pads = emb ∘ smallPads from funext fun j => (hpads j).symm,
    translateCorePadding_map emb small large domainMap hk C baseEq]
  intro j
  exact ⟨_, rfl⟩

end LfzkV1.V7SubfieldPadding
