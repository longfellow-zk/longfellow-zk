import polygero.Reduction.ChildInstance
import polygero.Protocol.Wire
import Mathlib.FieldTheory.Finite.GaloisField

/-! Inhabitation of the concrete two-level grinding geometry. Both layers
use the rate-1/16 domain; the entire 1600-coefficient parent payload fits
exactly into four child rows of 400 logical slots. -/

namespace RecursivePolygero.Benchmarks.FSGrindingInstance

open Polynomial Finset Codes LigeroFamily Local Local.Polygero
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The coefficient packing is a bijection, with no unused coefficient
slots and no assumption about a particular coefficient ordering. -/
noncomputable def packing : Packing 512 64 4 400 :=
  (Fintype.equivOfCardEq (by
    simp only [CoefficientIndex, Slots, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_prod]) : CoefficientIndex 512 64 ≃ Slots 4 400).toEmbedding

theorem packing_surjective : Function.Surjective packing :=
  (Fintype.equivOfCardEq (by
    simp only [CoefficientIndex, Slots, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_prod]) : CoefficientIndex 512 64 ≃ Slots 4 400).surjective

noncomputable def parent (D : ReedSolomon.Domain F 0 512 8192) : Instance F where
  q := 1
  r := 0
  w := 512
  n := 8192
  nw := 1
  nq := 0
  s := 64
  t := 70
  Equations := Bool
  equationsFinite := inferInstance
  equationsDecidable := inferInstance
  domain := D
  layout := ConstraintLayout.logicalPrefix 1 511
  primary_le := by decide
  query_le := by decide

noncomputable def child (D : ReedSolomon.Domain F 0 512 8192) : Child (parent D) where
  r := 0
  w := 512
  n := 8192
  d := 4
  slots := 400
  s := 64
  t := 70
  domain := D
  layout := ConstraintLayout.logicalPrefix 400 112
  primary_le := by decide
  query_le := by decide
  packing := packing

omit [Fintype F] [DecidableEq F] in
theorem parent_geometry (D : ReedSolomon.Domain F 0 512 8192) :
    (parent D).r = 0 ∧ (parent D).w = 512 ∧ (parent D).n = 8192 ∧
      (parent D).nw = 1 ∧ (parent D).nq = 0 ∧ (parent D).q = 1 ∧
      (parent D).s = 64 ∧ (parent D).t = 70 := by
  repeat' constructor

omit [Fintype F] [DecidableEq F] in
theorem child_geometry (D : ReedSolomon.Domain F 0 512 8192) :
    (child D).instance.r = 0 ∧ (child D).instance.w = 512 ∧ (child D).instance.n = 8192 ∧
      (child D).instance.nw = 4 ∧ (child D).instance.nq = 0 ∧ (child D).instance.q = 400 ∧
      (child D).instance.s = 64 ∧ (child D).instance.t = 70 := by
  repeat' constructor

/-- The child has an actual transmitted row on which the entry-variation
family can be formed. -/
def variedRow (D : ReedSolomon.Domain F 0 512 8192) : (child D).instance.WireRow false := by
  change CoreRow 4 0
  refine ⟨.linear, ?_⟩
  change Fin 4
  exact 0

def variedColumn (D : ReedSolomon.Domain F 0 512 8192) : Fin (child D).instance.n := by
  change Fin 8192
  exact 8191

/-- The full disjoint Longfellow domain needs 512 message points and 8192
code points. The 128-bit field easily provides their actual embedding. -/
noncomputable def domain (hF : Fintype.card F = 2 ^ 128) : ReedSolomon.Domain F 0 512 8192 :=
  ReedSolomon.Domain.ofCardLE (by rw [hF]; decide)

omit [DecidableEq F] in
theorem exists_parent_child (hF : Fintype.card F = 2 ^ 128) :
    ∃ I : Instance F, ∃ C : Child I,
      I.r = 0 ∧ I.w = 512 ∧ I.n = 8192 ∧ I.nw = 1 ∧ I.nq = 0 ∧
      I.q = 1 ∧ I.s = 64 ∧ I.t = 70 ∧
      C.instance.r = 0 ∧ C.instance.w = 512 ∧ C.instance.n = 8192 ∧
      C.instance.nw = 4 ∧ C.instance.nq = 0 ∧ C.instance.q = 400 ∧
      C.instance.s = 64 ∧ C.instance.t = 70 := by
  exact ⟨parent (domain hF), child (domain hF), by repeat' constructor⟩

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- An inhabited concrete field removes even the ambient finite-field
cardinality premise from the existence check. -/
abbrev Field128 := GaloisField 2 128

noncomputable instance : Fintype Field128 := Fintype.ofFinite _
noncomputable instance : DecidableEq Field128 := Classical.decEq _

theorem field128_card : Fintype.card Field128 = 2 ^ 128 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 128 (by decide)

noncomputable def concreteDomain : ReedSolomon.Domain Field128 0 512 8192 :=
  domain field128_card

noncomputable def concreteParent : Instance Field128 := parent concreteDomain

noncomputable def concreteChild : Child concreteParent := child concreteDomain

theorem concrete_geometry :
    concreteParent.r = 0 ∧ concreteParent.w = 512 ∧ concreteParent.n = 8192 ∧
      concreteParent.nw = 1 ∧ concreteParent.nq = 0 ∧ concreteParent.q = 1 ∧
      concreteParent.s = 64 ∧ concreteParent.t = 70 ∧
      concreteChild.instance.r = 0 ∧ concreteChild.instance.w = 512 ∧
      concreteChild.instance.n = 8192 ∧ concreteChild.instance.nw = 4 ∧
      concreteChild.instance.nq = 0 ∧ concreteChild.instance.q = 400 ∧
      concreteChild.instance.s = 64 ∧ concreteChild.instance.t = 70 := by
  repeat' constructor

/-- Retuned opening schedule used by the exact three-bit Johnson
certificate. Encoding dimensions and coefficient packing are identical. -/
noncomputable def retunedParent (D : ReedSolomon.Domain F 0 512 8192) : Instance F :=
  { parent D with t := 81, query_le := by change 81 ≤ 8192; decide }

noncomputable def retunedChild (D : ReedSolomon.Domain F 0 512 8192) : Child (retunedParent D) where
  r := 0
  w := 512
  n := 8192
  d := 4
  slots := 400
  s := 64
  t := 80
  domain := D
  layout := ConstraintLayout.logicalPrefix 400 112
  primary_le := by decide
  query_le := by decide
  packing := packing

def retunedVariedRow (D : ReedSolomon.Domain F 0 512 8192) :
    (retunedChild D).instance.WireRow false := by
  change CoreRow 4 0
  refine ⟨.linear, ?_⟩
  change Fin 4
  exact 0

def retunedVariedColumn (D : ReedSolomon.Domain F 0 512 8192) :
    Fin (retunedChild D).instance.n := by
  change Fin 8192
  exact 8191

noncomputable def concreteRetunedParent : Instance Field128 := retunedParent concreteDomain

noncomputable def concreteRetunedChild : Child concreteRetunedParent := retunedChild concreteDomain

theorem concrete_retuned_geometry :
    concreteRetunedParent.r = 0 ∧ concreteRetunedParent.w = 512 ∧ concreteRetunedParent.n = 8192 ∧
      concreteRetunedParent.nw = 1 ∧ concreteRetunedParent.nq = 0 ∧ concreteRetunedParent.q = 1 ∧
      concreteRetunedParent.s = 64 ∧ concreteRetunedParent.t = 81 ∧
      concreteRetunedChild.instance.r = 0 ∧ concreteRetunedChild.instance.w = 512 ∧
      concreteRetunedChild.instance.n = 8192 ∧ concreteRetunedChild.instance.nw = 4 ∧
      concreteRetunedChild.instance.nq = 0 ∧ concreteRetunedChild.instance.q = 400 ∧
      concreteRetunedChild.instance.s = 64 ∧ concreteRetunedChild.instance.t = 80 := by
  repeat' constructor

end RecursivePolygero.Benchmarks.FSGrindingInstance
