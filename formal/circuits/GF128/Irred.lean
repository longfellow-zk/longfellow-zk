import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.Finite.Basic
import GF128.Indep
import GF128.Order

/-!
# `P` is irreducible, so `IsGen.indep` is a theorem

The last assumption. `Indep.lean` reduced `indep` to `Irreducible Pgf`; this file discharges it,
and the argument is the one the kernel certificates were always pointing at.

Work in `QR := AdjoinRoot Pgf`, which is `F₂[X]/(P)` — a commutative *ring*, not yet known to be
a field. Two facts about it need no irreducibility:

* `AdjoinRoot.powerBasis'` asks only that `P` be monic, so `QR` has a power basis of size 128.
  That gives `deg (minpoly F₂ ρ) = 128` and hence, by `indep_of_minpoly_degree`, that `eval ρ` is
  injective on bit patterns — and `|QR| = 2^128`.
* Injectivity carries `Poly.alpha_pow_N` and `Poly.alpha_pow_cofactor_ne_one` across, so
  `orderOf ρ = 2^128 − 1`, which is `|QR| − 1`.

Then the counting: `ρ`'s powers are `|QR| − 1` distinct nonzero elements, so they exhaust the
nonzero elements, so every nonzero element has an inverse. A quotient by a maximal ideal, and in
`F₂[X]` — a PID — that makes `P` prime and hence irreducible.

Note the shape of the dependency. The order of `x` modulo `P` is a *computation*, checked by
`decide +kernel` in `Poly.lean`; irreducibility of `P` is a *consequence* of it, not an
independent input. There is no Rabin test here and no factorisation search.
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace GF128

open Polynomial

/-- `F₂[X]/(P)`. -/
abbrev QR := AdjoinRoot Pgf

/-- The class of `X`. -/
noncomputable def rho : QR := AdjoinRoot.root Pgf

theorem Pgf_degree : Pgf.degree = 128 := by
  unfold Pgf
  compute_degree!

theorem Pgf_degree_ne_zero : Pgf.degree ≠ 0 := by
  rw [Pgf_degree]
  decide

theorem Pgf_ne_zero : Pgf ≠ 0 := Pgf_monic.ne_zero

/-- The power basis `P`'s monicity alone provides. -/
noncomputable def pb : PowerBasis (ZMod 2) QR := AdjoinRoot.powerBasis' Pgf_monic

theorem pb_dim : pb.dim = 128 := by
  rw [pb, AdjoinRoot.powerBasis'_dim, Pgf_natDegree]

theorem pb_gen : pb.gen = rho := AdjoinRoot.powerBasis'_gen Pgf_monic

instance : Nontrivial QR :=
  ⟨⟨AdjoinRoot.of Pgf 0, AdjoinRoot.of Pgf 1,
    fun h => zero_ne_one (AdjoinRoot.coe_injective Pgf_degree_ne_zero h)⟩⟩

instance : CharP QR 2 :=
  charP_of_injective_algebraMap (R := ZMod 2) (A := QR)
    (by rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.coe_injective Pgf_degree_ne_zero) 2

/-! ## `ρ` satisfies `IsGen` -/

theorem rho_root : rho ^ 128 = rho ^ 7 + rho ^ 2 + rho + 1 := by
  have h : aeval rho Pgf = 0 := by
    rw [rho, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [Pgf, map_add, map_pow, map_one, aeval_X] at h
  have h2 : (2 : QR) = 0 := CharTwo.two_eq_zero
  linear_combination h - (rho ^ 7 + rho ^ 2 + rho + 1) * h2

theorem minpoly_rho_natDegree : (minpoly (ZMod 2) rho).natDegree = 128 := by
  rw [← pb_gen, pb.natDegree_minpoly, pb_dim]

theorem rho_indep : ∀ n, n < 2 ^ 128 → eval rho n = 0 → n = 0 :=
  indep_of_minpoly_degree rho minpoly_rho_natDegree

theorem isGen_rho : IsGen rho := ⟨rho_root, rho_indep⟩

/-! ## `|QR| = 2^128` and `orderOf ρ = |QR| − 1` -/

noncomputable instance : Fintype QR := Module.fintypeOfFintype pb.basis

theorem card_QR : Fintype.card QR = 2 ^ 128 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), pb.finrank, pb_dim, ZMod.card]

theorem orderOf_rho : orderOf rho = N := orderOf_alpha rho isGen_rho

theorem N_eq : N = 2 ^ 128 - 1 := rfl

/-! ## The counting -/

theorem rho_pow_ne_zero (k : Nat) : rho ^ k ≠ 0 := by
  have hN : rho ^ N = 1 := alpha_pow_N_eq_one rho isGen_rho
  intro h
  have h1 : (rho ^ k) ^ N = 0 := by rw [h, zero_pow (by decide : N ≠ 0)]
  have h2 : (rho ^ k) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hN, one_pow]
  exact one_ne_zero (h2.symm.trans h1)

/-- **Every nonzero element of `QR` is a power of `ρ`.** The powers are `|QR| − 1` distinct
    nonzero elements, and there are exactly that many nonzero elements. -/
theorem exists_pow_eq {a : QR} (ha : a ≠ 0) : ∃ k, rho ^ k = a := by
  classical
  have hinj : Set.InjOn (fun k => rho ^ k) (Finset.range N : Finset Nat) := by
    intro i hi j hj hij
    have h := pow_injOn_Iio_orderOf (x := rho)
    rw [orderOf_rho] at h
    exact h (Set.mem_Iio.mpr (Finset.mem_range.mp (by simpa using hi)))
      (Set.mem_Iio.mpr (Finset.mem_range.mp (by simpa using hj))) hij
  have hcard : ((Finset.range N).image (fun k => rho ^ k)).card = N := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : (Finset.range N).image (fun k => rho ^ k) ⊆ Finset.univ.erase 0 := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨rho_pow_ne_zero k, Finset.mem_univ _⟩
  have hcard2 : (Finset.univ.erase (0 : QR)).card = N := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_QR, N_eq]
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have : a ∈ (Finset.range N).image (fun k => rho ^ k) := by
    rw [heq]
    exact Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp this
  exact ⟨k, hk⟩

theorem isField_QR : IsField QR := by
  classical
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨k, hk⟩ := exists_pow_eq ha
  refine ⟨rho ^ (N - k % N), ?_⟩
  have hN : rho ^ N = 1 := alpha_pow_N_eq_one rho isGen_rho
  have hmod : rho ^ k = rho ^ (k % N) := by
    conv_lhs => rw [← Nat.div_add_mod k N]
    rw [pow_add, pow_mul, hN, one_pow, one_mul]
  have hlt : k % N < N := Nat.mod_lt _ (by decide)
  rw [← hk, hmod, ← pow_add, show k % N + (N - k % N) = N from by omega, hN]

/-! ## …hence `P` is irreducible -/

theorem irreducible_Pgf : Irreducible Pgf := by
  have hmax : (Ideal.span {Pgf}).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ isField_QR
  exact ((Ideal.span_singleton_prime Pgf_ne_zero).mp hmax.isPrime).irreducible

/-! ## The payoff -/

/-- A ring of characteristic 2 is a `ZMod 2`-algebra. Mathlib does not make this an instance, and
    without it every caller of the results below would have to supply one. -/
noncomputable def zmod2Algebra (F : Type*) [CommRing F] [CharP F 2] : Algebra (ZMod 2) F :=
  (ZMod.castHom (dvd_refl 2) F).toAlgebra

variable {F : Type*} [CommRing F] [CharP F 2] [Nontrivial F]

/-- **`IsGen` from `P(α) = 0` alone.** No assumption survives: being a root of the deployed
    reduction polynomial is all it takes, over any nontrivial commutative ring of
    characteristic 2. The hypotheses here are exactly the ones `IsGen` itself needs. -/
theorem isGen_of_root (α : F) (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1) : IsGen α := by
  letI := zmod2Algebra F
  exact isGen_of_irreducible irreducible_Pgf α hroot

/-- `IsGen.indep`, no longer an assumption. -/
theorem indep_of_root (α : F) (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1) :
    ∀ n, n < 2 ^ 128 → eval α n = 0 → n = 0 :=
  (isGen_of_root α hroot).indep

/-- And the end of the chain: the wrapping-sum soundness theorem needs only `P(α) = 0`. -/
example {K : Type} [Field K] [CharP K 2] (α : K)
    (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1) : orderOf α = 2 ^ 128 - 1 :=
  orderOf_alpha α (isGen_of_root α hroot)

end GF128
