import polygero.Algebra.PolynomialChallenges.RowConsistency
import polygero.Algebra.PolynomialChallenges.AffineInstance
import polygero.Local.CandidateTests
import polygero.Local.RowWitness

/-! Fixed row polynomials under full consistency, and the identities certified
by their agreement with sufficiently many good columns. -/
namespace RecursivePolygero
open Polynomial Finset Codes LigeroFamily Local Local.Polygero
open LigeroFamily.PolynomialDirect (primaryCode decodedLinearResidual decodedZRMaskSum)
attribute [local instance] Classical.propDecidable
section Rows
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n m k s : ℕ}

/-- Full affine consistency on any sufficiently large set supplies the mask
polynomial and the lower-degree row polynomials. -/
theorem affine_rows_of_full_consistency
    (C : RSCode F n (k+s)) (W : Fin m → Word F n) (mask : Word F n)
    (S : Finset (Fin n)) (hk : 1 ≤ k) (hsize : k+s < S.card)
    (hfull : Affine.consistent C W mask S = univ) :
    ∃ fstar : DegreeLT F (k+s), ∃ f : Fin m → DegreeLT F k,
      (∀ j ∈ S, (fstar : F[X]).eval (C.node j) = mask j) ∧
      (∀ i j, j ∈ S → W i j = (f i : F[X]).eval (C.node j)) := by
  have hz : (0 : Challenge F m s) ∈ Affine.consistent C W mask S := by rw [hfull]; simp
  obtain ⟨fstar,hstar⟩ := (mem_filter.mp hz).2
  have hlinear : consistentChallenges (s := s) C W S = ⊤ := by
    apply top_unique
    intro B _
    have hb : B ∈ Affine.consistent C W mask S := by rw [hfull]; simp
    simpa only [sub_zero] using (Affine.mem_consistent_iff_sub_mem C W mask S 0 hz B).mp hb
  obtain ⟨f,hf⟩ := rows_of_full_consistency C W S hk hsize hlinear
  refine ⟨fstar,f,?_,hf⟩
  intro j hj
  simpa [response] using hstar j hj

omit [Fintype F] [DecidableEq F] in
/-- Agreement on a sufficiently large set identifies the primary response. -/
theorem primary_eq_of_full_set_agreement
    (C : RSCode F n (k+s)) (W : Fin m → Word F n) (mask : Word F n)
    (S : Finset (Fin n)) (hk : 1 ≤ k) (hsize : k+s ≤ S.card)
    (fstar : DegreeLT F (k+s)) (f : Fin m → DegreeLT F k)
    (hstar : ∀ j ∈ S, (fstar : F[X]).eval (C.node j) = mask j)
    (hf : ∀ i j, j ∈ S → W i j = (f i : F[X]).eval (C.node j))
    (B : Challenge F m s) (p : DegreeLT F (k+s))
    (hp : ∀ j ∈ S, (p : F[X]).eval (C.node j) = response C W B j + mask j) :
    (p : F[X]) = fstar + ∑ i, (B i : F[X]) * (f i : F[X]) := by
  have hprod (i) : (B i : F[X]) * (f i : F[X]) ∈ degreeLT F (k+s) := by
    have h := mul_mem_degreeLT_add_sub_one (by omega : 1 ≤ s+1) hk (B i).2 (f i).2
    convert h using 1
    congr 1
    omega
  have hdeg : (fstar : F[X]) + ∑ i, (B i : F[X]) * (f i : F[X]) ∈ degreeLT F (k+s) :=
    (degreeLT F (k+s)).add_mem fstar.2 ((degreeLT F (k+s)).sum_mem (fun i _ => hprod i))
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S C.node_injective.injOn
  · exact (mem_degreeLT.mp p.2).trans_le (by exact_mod_cast hsize)
  · exact (mem_degreeLT.mp hdeg).trans_le (by exact_mod_cast hsize)
  · intro j hj
    rw [hp j hj]
    simp only [eval_add, eval_finsetSum, eval_mul, hstar j hj, response]
    simp_rw [hf _ j hj]
    exact add_comm _ _
end Rows

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {q r w n nw nq s : ℕ}
variable {D : ReedSolomon.Domain F r w n} {hprimary : r+w+s ≤ n}
variable {oracle : Oracle F nw nq n}

omit [Fintype F] [DecidableEq Equations] in
/-- Above the query-count floor, agreement and the local tests determine both
arithmetic and multiplication identities by ordinary polynomial root counting. -/
theorem identities_of_agreement
    (hk : r+w ≤ n) (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (coin : Coin F Equations nw nq s) (payload : LigeroPayload F (r+w) s)
    (f : Fin (rowCount nw nq) → DegreeLT F (r+w)) (U : Finset (Fin n))
    (hkpos : 1 ≤ r+w) (hsize : 2*(r+w) ≤ U.card)
    (hgood : U ⊆ goodColumns D hk hprimary layout statement oracle coin payload)
    (hagrees : ∀ i j, j ∈ U → oracleWords oracle.ordinary i j =
      (f i : F[X]).eval ((primaryCode D hprimary).node j)) :
    payload.arithmetic = (responseSemantics D hk hprimary layout statement coin.1).canonical 0 f ∧
    ∀ g : Fin nq, (f (leftIndex g) : F[X]) * f (rightIndex g) = (f (outputIndex g) : F[X]) := by
  constructor
  · apply Subtype.ext
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq U (primaryCode D hprimary).node_injective.injOn
    · exact (mem_degreeLT.mp payload.arithmetic.2).trans_le (by exact_mod_cast hsize)
    · exact (mem_degreeLT.mp ((responseSemantics D hk hprimary layout statement coin.1).canonical 0 f).2).trans_le
        (by exact_mod_cast hsize)
    · intro j hj
      have hlocal : (payload.arithmetic : F[X]).eval ((primaryCode D hprimary).node j) =
          linearPointwise D hk layout statement coin.1 j
            (fun i => oracleWords oracle.ordinary i j) := (mem_filter.mp (hgood hj)).2.2.1
      rw [hlocal, (responseSemantics D hk hprimary layout statement coin.1).canonical_eval]
      dsimp only [responseSemantics]
      congr 1
      funext i
      exact hagrees i j hj
  · intro g
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq U (primaryCode D hprimary).node_injective.injOn
    · exact (mem_degreeLT.mp (mul_mem_degreeLT_add_sub_one hkpos hkpos
        (f (leftIndex g)).2 (f (rightIndex g)).2)).trans_le
        (by exact_mod_cast (by omega : r+w+(r+w)-1 ≤ U.card))
    · exact (mem_degreeLT.mp (f (outputIndex g)).2).trans_le
        (by exact_mod_cast (by omega : r+w ≤ U.card))
    · intro j hj
      rw [eval_mul, ← hagrees (leftIndex g) j hj, ← hagrees (rightIndex g) j hj,
        ← hagrees (outputIndex g) j hj]
      simpa only [leftIndex, rightIndex, outputIndex, oracleWords_core] using
        (mem_filter.mp (hgood hj)).2.2.2 g

/-- A failed linear constraint passes the canonical global test only on a
small affine fiber; the arithmetic-mask sum is an arbitrary fixed offset. -/
theorem polynomialArithmeticMatches_card
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (f : Fin (rowCount nw nq) → DegreeLT F (r+w))
    (hfailed : decodedLinearResidual D layout statement (extendRows f) ≠ 0) :
    Fintype.card F *
      (affineEquationSolutions (decodedLinearResidual D layout statement (extendRows f))
        (-decodedZRMaskSum D layout (extendRows f))).card ≤
      Fintype.card (Equations → F) := by
  exact affineEquationSolutions_density _ _ hfailed

end RecursivePolygero
