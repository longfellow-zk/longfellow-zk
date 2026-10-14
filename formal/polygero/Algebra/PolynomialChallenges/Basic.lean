import polygero.Algebra.Code
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Polynomial correlated agreement: basic objects

This file defines polynomial challenges and their coefficient
coordinates, the many-row response, and agreement on a fixed coordinate set.

The response attached to rows `W i` and challenge polynomials `B i` is

`z ↦ ∑ i, B i (node z) * W i z`.

No decoding choice is made: `AgreesOn` only asserts that
*some* response polynomial of degree `< R` agrees on the prescribed set.
-/

namespace RecursivePolygero.Local

open Finset Function Polynomial
open Codes

variable {F : Type*} [Field F] [DecidableEq F]
variable {n d s R m : ℕ}

/-- Polynomials of degree strictly less than `t`, as a vector space. -/
noncomputable abbrev DegreeLT (F : Type*) [Field F] (t : ℕ) :=
  Polynomial.degreeLT F t

/-- Bounded-degree polynomials over a finite field form a finite type. -/
noncomputable instance degreeLTFintype {F : Type*} [Field F] [Fintype F]
    {t : ℕ} : Fintype (DegreeLT F t) :=
  Fintype.ofEquiv (Fin t → F)
    (Polynomial.degreeLTEquiv F t).symm.toEquiv

omit [DecidableEq F] in
/-- Membership in `DegreeLT F t` gives the corresponding natural-degree
bound when `t` is positive. -/
theorem natDegree_lt_of_mem_degreeLT
    {t : ℕ} (ht : 1 ≤ t) {p : F[X]} (hp : p ∈ degreeLT F t) :
    p.natDegree < t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE,
    ← Polynomial.natDegree_le_iff_degree_le] at hp
  exact Nat.lt_succ_of_le hp

/-- An `m`-row polynomial challenge with polynomial degree at most `s`. -/
abbrev Challenge (F : Type*) [Field F] (m s : ℕ) :=
  Fin m → DegreeLT F (s + 1)

/-- The coordinatewise aggregate response to a polynomial challenge. -/
noncomputable def response (C : RSCode F n R) (W : Fin m → Word F n)
    (B : Challenge F m s) : Word F n :=
  fun z ↦ ∑ i, (B i : F[X]).eval (C.node z) * W i z

omit [DecidableEq F] in
/-- Puncturing commutes definitionally with forming the aggregate response. -/
theorem restrictWord_response
    (C : RSCode F n R) (W : Fin m → Word F n)
    (S : Finset (Fin n)) (hR : R ≤ S.card) (B : Challenge F m s) :
    C.restrictWord S (response C W B) =
      response (C.puncture S hR) (fun i ↦ C.restrictWord S (W i)) B := by
  rfl

/-- A challenge admits a degree-`< R` response polynomial on `S`. -/
def AgreesOn (C : RSCode F n R) (W : Fin m → Word F n)
    (S : Finset (Fin n)) (B : Challenge F m s) : Prop :=
  ∃ p : DegreeLT F R,
    ∀ z, z ∈ S → response C W B z = (p : F[X]).eval (C.node z)

/-- The full agreement set of a challenge and a candidate response polynomial. -/
noncomputable def agreementSet (C : RSCode F n R) (W : Fin m → Word F n)
    (B : Challenge F m s) (p : F[X]) : Finset (Fin n) :=
  Finset.univ.filter fun z ↦ response C W B z = p.eval (C.node z)

@[simp] theorem mem_agreementSet
    (C : RSCode F n R) (W : Fin m → Word F n)
    (B : Challenge F m s) (p : F[X]) (z : Fin n) :
    z ∈ agreementSet C W B p ↔
      response C W B z = p.eval (C.node z) := by
  simp [agreementSet]

/-- Coordinate sets of one prescribed size. -/
abbrev SizedCore (n c : ℕ) :=
  ↥((Finset.univ : Finset (Fin n)).powersetCard c)

@[simp] theorem SizedCore.card {c : ℕ} (S : SizedCore n c) :
    S.1.card = c :=
  (Finset.mem_powersetCard.mp S.2).2

omit [DecidableEq F] in
theorem mul_mem_degreeLT_add_sub_one
    {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    {a b : F[X]} (ha : a ∈ degreeLT F A) (hb : b ∈ degreeLT F B) :
    a * b ∈ degreeLT F (A + B - 1) := by
  have haNat := natDegree_lt_of_mem_degreeLT hA ha
  have hbNat := natDegree_lt_of_mem_degreeLT hB hb
  apply Polynomial.mem_degreeLT.mpr
  apply Polynomial.degree_le_natDegree.trans_lt
  exact_mod_cast (Polynomial.natDegree_mul_le.trans_lt
    (show a.natDegree + b.natDegree < A + B - 1 by omega))

omit [DecidableEq F] in
theorem agreesOn_iff_punctured_univ
    (C : RSCode F n R) (W : Fin m → Word F n)
    (S : Finset (Fin n)) (hR : R ≤ S.card) (B : Challenge F m s) :
    AgreesOn C W S B ↔ AgreesOn (C.puncture S hR)
      (fun i ↦ C.restrictWord S (W i)) Finset.univ B := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    intro j _hj
    let z : S := (Finset.equivFin S).symm j
    have hz := hp z.1 z.2
    have hresponse := congrFun (restrictWord_response C W S hR B) j
    simpa [z, Codes.RSCode.restrictWord] using hresponse.symm.trans hz
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    intro z hz
    let j : Fin S.card := Finset.equivFin S ⟨z, hz⟩
    have hagree := hp j (Finset.mem_univ j)
    have hresponse := congrFun (restrictWord_response C W S hR B) j
    simpa [j, Codes.RSCode.restrictWord] using hresponse.trans hagree

end RecursivePolygero.Local
