import polygero.Local.CoreRows
import polygero.Local.PuncturedDecoder
import Mathlib.LinearAlgebra.Lagrange

/-! Bounded-distance recovery on a supplied restriction. The specification is
finite and exact, and instantiates the generic punctured-code decoder contract. -/
namespace RecursivePolygero
open Polynomial Finset Codes LigeroFamily RecursivePolygero.Local
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] {n k R s : ℕ}

noncomputable def rowErrors (C : RSCode F n R) (W : Word F n)
    (S : Finset (Fin n)) (f : DegreeLT F k) : Finset (Fin n) :=
  puncturedErrors (fun f : DegreeLT F k => fun j => (f : F[X]).eval (C.node j)) W S f

/-- Distinct bounded-degree polynomials cannot both meet the error promise. -/
theorem unique_near_row (C : RSCode F n R) (W : Word F n) (S : Finset (Fin n))
    (hsize : k+2*s ≤ S.card) (f g : DegreeLT F k)
    (hf : (rowErrors C W S f).card ≤ s) (hg : (rowErrors C W S g).card ≤ s) : f = g := by
  classical
  let U := S \ (rowErrors C W S f ∪ rowErrors C W S g)
  have hu : k ≤ U.card := by
    have h := card_le_card_sdiff_add_card (s := S)
      (t := rowErrors C W S f ∪ rowErrors C W S g)
    have h' := card_union_le (rowErrors C W S f) (rowErrors C W S g)
    dsimp only [U]
    omega
  apply Subtype.ext
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq U C.node_injective.injOn
  · exact (mem_degreeLT.mp f.2).trans_le (by exact_mod_cast hu)
  · exact (mem_degreeLT.mp g.2).trans_le (by exact_mod_cast hu)
  · intro j hj
    obtain ⟨hjS, hjbad⟩ := mem_sdiff.mp hj
    have hfj : W j = (f : F[X]).eval (C.node j) := by
      by_contra hn
      exact hjbad (mem_union_left _ (mem_filter.mpr ⟨hjS, hn⟩))
    have hgj : W j = (g : F[X]).eval (C.node j) := by
      by_contra hn
      exact hjbad (mem_union_right _ (mem_filter.mpr ⟨hjS, hn⟩))
    exact hfj.symm.trans hgj

/-- The Reed--Solomon instance of the generic punctured-code decoder.
Only node injectivity and the root bound are used. -/
noncomputable def puncturedRowDecoder (C : RSCode F n R) (k : ℕ) :
    PuncturedDecoder (fun f : DegreeLT F k => fun j => (f : F[X]).eval (C.node j))
      (fun S radius => k+2*radius ≤ S.card) :=
  PuncturedDecoder.of_unique _ _ (fun W S _ hsize f g hf hg =>
    unique_near_row C W S hsize f g hf hg)

noncomputable def recoverRow (C : RSCode F n R) (W : Word F n)
    (S : Finset (Fin n)) (k s : ℕ) : Option (DegreeLT F k) :=
  (puncturedRowDecoder C k).decode W S s

theorem recoverRow_valid (C : RSCode F n R) (W : Word F n) (S : Finset (Fin n))
    (f : DegreeLT F k) (h : recoverRow C W S k s = some f) :
    (rowErrors C W S f).card ≤ s :=
  (puncturedRowDecoder C k).valid W S s f h

theorem recoverRow_eq_some (C : RSCode F n R) (W : Word F n) (S : Finset (Fin n))
    (hsize : k+2*s ≤ S.card) (f : DegreeLT F k)
    (hf : (rowErrors C W S f).card ≤ s) : recoverRow C W S k s = some f :=
  (puncturedRowDecoder C k).complete W S s hsize f hf

end RecursivePolygero
