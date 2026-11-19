import WitnessSelection.Collision

/-! Refine frontendError in committed_composition_le. Backend extraction and
outside-list errors remain. Selection concerns the projected frontend cells;
internal Polygero mask rows may still have several lifts. -/
namespace RecursivePolygero.NonrecursiveFS
open Finset
open scoped Classical

variable {F ι Index : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

theorem projected_frontend_decomposition (s : Finset Index)
    (view : Index → WitnessSelection.Candidate F ι)
    (a : WitnessSelection.Coins F ι) (t : F × F)
    (Bad : WitnessSelection.Candidate F ι → Prop)
    (h : ∃ i ∈ s, WitnessSelection.fingerprint a (view i) = t ∧ Bad (view i)) :
    a ∈ WitnessSelection.badCoins (s.image view) ∨
      ∃ w, WitnessSelection.select (s.image view) a t = some w ∧ Bad w := by
  obtain ⟨i,hi,ht,hbad⟩ := h
  exact WitnessSelection.selected_frontend_decomposition (s.image view) a t Bad
    ⟨view i, mem_image.mpr ⟨i,hi,rfl⟩, ht, hbad⟩

/-- Supply selectionError + fixedWitnessError to the existing composition
theorem; no list factor multiplies the fixed-witness frontend charge. -/
theorem selected_frontend_ratio_le {Ω : Type} [Fintype Ω]
    (lists : Ω → Finset Index) (view : Index → WitnessSelection.Candidate F ι)
    (coins : Ω → WitnessSelection.Coins F ι) (target : Ω → F × F)
    (Bad : Ω → WitnessSelection.Candidate F ι → Prop)
    (selectionError fixedWitnessError : ℚ)
    (hselection : ((univ.filter fun ω => coins ω ∈
      WitnessSelection.badCoins ((lists ω).image view)).card : ℚ) / Fintype.card Ω ≤ selectionError)
    (hfixed : ((univ.filter fun ω => ∃ w,
      WitnessSelection.select ((lists ω).image view) (coins ω) (target ω) = some w ∧ Bad ω w).card : ℚ) /
        Fintype.card Ω ≤ fixedWitnessError) :
    ((univ.filter fun ω => ∃ i ∈ lists ω,
      WitnessSelection.fingerprint (coins ω) (view i) = target ω ∧ Bad ω (view i)).card : ℚ) /
        Fintype.card Ω ≤ selectionError + fixedWitnessError := by
  let A := univ.filter fun ω => coins ω ∈ WitnessSelection.badCoins ((lists ω).image view)
  let B := univ.filter fun ω => ∃ w,
    WitnessSelection.select ((lists ω).image view) (coins ω) (target ω) = some w ∧ Bad ω w
  have hsub : (univ.filter fun ω => ∃ i ∈ lists ω,
      WitnessSelection.fingerprint (coins ω) (view i) = target ω ∧ Bad ω (view i)) ⊆ A ∪ B := by
    intro ω hω
    have h := projected_frontend_decomposition (lists ω) view (coins ω) (target ω) (Bad ω)
      (mem_filter.mp hω).2
    simpa [A, B] using h
  have hc : ((univ.filter fun ω => ∃ i ∈ lists ω,
      WitnessSelection.fingerprint (coins ω) (view i) = target ω ∧ Bad ω (view i)).card : ℚ) ≤
      (A.card : ℚ) + B.card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le A B)
  have hd := div_le_div_of_nonneg_right hc (show (0 : ℚ) ≤ Fintype.card Ω by positivity)
  rw [add_div] at hd
  exact hd.trans (add_le_add hselection hfixed)

end RecursivePolygero.NonrecursiveFS
