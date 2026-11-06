import LfzkV2.Current.Opening
import LfzkV2.Current.IdealProjections
import Mathlib.Data.Fintype.CardEmbedding

/-! Uniform ordered openings and their unordered query sets. The sampled
order remains available as a permutation; forgetting it has exactly `t!`
preimages per set. This is finite ideal-sampler algebra, not a statement
that a bounded byte seed samples an arbitrary finite set exactly. -/
noncomputable section
namespace LfzkV2.Current.OpeningSampling
open LigeroFamily Finset
open scoped Classical

variable {n t : ℕ}

/-- Numeric order gives one distinguished enumeration of every query set.
It is used only to record the otherwise retained sampling permutation. -/
def canonicalOrder (query : QuerySet n t) : Fin t ≃ ↥query.coordinates :=
  (query.coordinates.orderIsoOfFin (QuerySet.card_coordinates query)).toEquiv

def fromOrder (query : QuerySet n t) (order : Fin t ≃ ↥query.coordinates) : Fin t ↪ Fin n where
  toFun i := (order i).val
  inj' _ _ h := order.injective (Subtype.ext h)

theorem fromOrder_query (query : QuerySet n t) (order : Fin t ≃ ↥query.coordinates) :
    OrderedOpening.query (fromOrder query order) = query := by
  apply Subtype.ext
  apply Finset.ext
  intro j
  change j ∈ univ.image (fromOrder query order) ↔ j ∈ query.coordinates
  constructor
  · intro hj
    obtain ⟨i,_,hi⟩ := mem_image.mp hj
    exact hi ▸ (order i).property
  · intro hj
    refine mem_image.mpr ⟨order.symm ⟨j,hj⟩,mem_univ _,?_⟩
    exact congrArg Subtype.val (order.apply_symm_apply ⟨j,hj⟩)

private theorem cast_order_val {first second : QuerySet n t} (h : first = second)
    (order : Fin t ≃ ↥first.coordinates) (i : Fin t) :
    ((h ▸ order) i).val = (order i).val := by cases h; rfl

/-- An ordered sample with a fixed underlying set is exactly an enumeration
of that set. The equality transport changes no column values. -/
def fiberOrder (query : QuerySet n t) :
    {indices : Fin t ↪ Fin n // OrderedOpening.query indices = query} ≃
      (Fin t ≃ ↥query.coordinates) where
  toFun indices := indices.property ▸ OrderedOpening.order indices.val
  invFun order := ⟨fromOrder query order,fromOrder_query query order⟩
  left_inv := by
    rintro ⟨indices,hindices⟩
    apply Subtype.ext
    subst query
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv order := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact cast_order_val (fromOrder_query query order) (OrderedOpening.order (fromOrder query order)) i

/-- Each set's enumerations differ from numeric order by one permutation. -/
def orderPermutation (query : QuerySet n t) :
    (Fin t ≃ ↥query.coordinates) ≃ Equiv.Perm (Fin t) where
  toFun order := order.trans (canonicalOrder query).symm
  invFun perm := perm.trans (canonicalOrder query)
  left_inv order := by ext i; simp
  right_inv perm := by ext i; simp

def fiberPermutation (query : QuerySet n t) :
    {indices : Fin t ↪ Fin n // OrderedOpening.query indices = query} ≃ Equiv.Perm (Fin t) :=
  (fiberOrder query).trans (orderPermutation query)

/-- A uniform ordered injection factors into its query set and its retained
order, with no balancing or sampler-law premise. -/
def orderedEquiv : (Fin t ↪ Fin n) ≃ QuerySet n t × Equiv.Perm (Fin t) :=
  (Equiv.sigmaFiberEquiv (OrderedOpening.query (n := n) (t := t))).symm.trans
    ((Equiv.sigmaCongrRight fiberPermutation).trans (Equiv.sigmaEquivProd _ _))

@[simp] theorem orderedEquiv_query (indices : Fin t ↪ Fin n) :
    (orderedEquiv indices).1 = OrderedOpening.query indices := rfl

theorem query_fiber_card (query : QuerySet n t) :
    (univ.filter fun indices : Fin t ↪ Fin n => OrderedOpening.query indices = query).card = t.factorial := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (fiberPermutation query)).trans (by rw [Fintype.card_perm,Fintype.card_fin])

/-- Exact uniform unordered opening sampler, derived from the explicit
set/permutation bijection. -/
def orderedDecoder : BalancedDecoder (Fin t ↪ Fin n) (QuerySet n t) :=
  IdealProjections.decoder orderedEquiv

@[simp] theorem orderedDecoder_decode (indices : Fin t ↪ Fin n) :
    orderedDecoder.decode indices = OrderedOpening.query indices := rfl

@[simp] theorem orderedDecoder_fiber : (orderedDecoder (n := n) (t := t)).fiber = t.factorial := by
  change Fintype.card (Equiv.Perm (Fin t)) = t.factorial
  rw [Fintype.card_perm,Fintype.card_fin]

section Factor
variable {Raw Unused : Type} [Fintype Raw] [Fintype Unused]

/-- A larger ideal answer may retain every other coordinate. The opening
set is still an exactly balanced projection of that same answer. -/
def decoder (factor : Raw ≃ (Fin t ↪ Fin n) × Unused) : BalancedDecoder Raw (QuerySet n t) :=
  IdealProjections.decoder (factor.trans
    ((Equiv.prodCongr orderedEquiv (Equiv.refl Unused)).trans (Equiv.prodAssoc _ _ _)))

@[simp] theorem decoder_decode (factor : Raw ≃ (Fin t ↪ Fin n) × Unused) (raw : Raw) :
    (decoder factor).decode raw = OrderedOpening.query (factor raw).1 := rfl

@[simp] theorem decoder_fiber (factor : Raw ≃ (Fin t ↪ Fin n) × Unused) :
    (decoder factor).fiber = t.factorial*Fintype.card Unused := by
  change Fintype.card (Equiv.Perm (Fin t) × Unused) = _
  rw [Fintype.card_prod,Fintype.card_perm,Fintype.card_fin]

end Factor
end LfzkV2.Current.OpeningSampling
