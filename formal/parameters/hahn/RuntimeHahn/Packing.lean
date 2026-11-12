import RuntimeHahn.HahnPolynomial

/-! Protocol-independent exact Hahn packing certificates. Complementing large
agreement sets lets the same small-weight Gram checker handle rate 1/4.
No prover, verifier, transcript or computational security premise occurs here. -/
namespace RuntimeHahn
open Finset

/-- Complementation preserves family size and shifts pairwise intersection sizes. -/
theorem packing_of_complement {n w lam L : ℕ} (hl : 2*w ≤ n+lam)
    (h : CodingTheory.UniformFamilyBound n (n-w) (n+lam-2*w) L) :
    CodingTheory.UniformFamilyBound n w lam L := by
  classical
  intro family hcard hinter
  let complements := family.image (fun A => Aᶜ)
  have hcount : complements.card = family.card := by
    apply card_image_of_injective
    intro A B he
    exact compl_injective he
  rw [← hcount]
  apply h complements
  · intro A hA
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
    simp only [card_compl,Fintype.card_fin,hcard B hB]
  · intro A hA B hB hne
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hA
    obtain ⟨D,hD,rfl⟩ := mem_image.mp hB
    have hCD : C ≠ D := by intro he; subst D; exact hne rfl
    have hi := hinter C hC D hD hCD
    have hu := card_union_add_card_inter C D
    have hc : (C ∪ D).card ≤ n := (card_le_card (subset_univ _)).trans_eq (by simp)
    rw [hcard C hC,hcard D hD] at hu
    rw [← compl_union,card_compl,Fintype.card_fin]
    omega

end RuntimeHahn
