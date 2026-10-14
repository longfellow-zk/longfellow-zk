import polygero.Algebra.PolynomialChallenges.ConsistencyClosure

/-! Selecting independent coordinate equations from a consistent system. -/
namespace RecursivePolygero.Local.ConsistencyClosure
open Finset
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V] {n : ℕ}

omit [FiniteDimensional F V] in
theorem rank_le_card (A : V →ₗ[F] (Fin n → F)) (S : Finset (Fin n)) :
    rank A S ≤ S.card := by
  have h := Submodule.finrank_le (LinearMap.range ((Shift.restrict S).comp A))
  simpa only [rank,Module.finrank_fin_fun] using h

/-- A consistent system of rank at least `c` contains `c` independent equations. -/
theorem exists_subset_rank_eq_card (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (T : Finset (Fin n)) (hne : (solutions A offset T).Nonempty)
    (c : ℕ) (hc : c ≤ rank A T) :
    ∃ S ⊆ T, S.card = c ∧ rank A S = c := by
  classical
  induction c with
  | zero =>
      refine ⟨∅,empty_subset _,rfl,?_⟩
      have := rank_le_card A ∅
      simpa using this
  | succ c ih =>
      obtain ⟨S,hST,hcard,hrank⟩ := ih (by omega)
      have hneS := hne.mono (solutions_antitone A offset hST)
      have hnot : ¬T ⊆ closure A offset S := by
        intro h
        have hle := rank_mono A h
        rw [closure_rank A offset S hneS,hrank] at hle
        omega
      obtain ⟨j,hjT,hj⟩ := not_subset.mp hnot
      have hjS : j ∉ S := fun h => hj (subset_closure A offset S h)
      have hins : insert j S ⊆ T := insert_subset hjT hST
      have hneI := hne.mono (solutions_antitone A offset hins)
      have hlt : rank A S < rank A (insert j S) := by
        apply lt_of_le_of_ne (rank_mono A (subset_insert j S))
        intro he
        exact hj (subset_closure_of_rank_eq A offset (subset_insert j S) hneI he (mem_insert_self j S))
      refine ⟨insert j S,hins,by simp [card_insert_of_notMem hjS,hcard],?_⟩
      have hle := rank_le_card A (insert j S)
      rw [card_insert_of_notMem hjS,hcard] at hle
      omega

end RecursivePolygero.Local.ConsistencyClosure
