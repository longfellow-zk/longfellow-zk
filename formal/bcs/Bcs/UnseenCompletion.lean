import Bcs.AffinePotential

/-! Joint completion of coordinates that an adaptive prover has not read.
The terminal choice is held fixed only on its missing footprint. This lets
mutually exclusive completion cases share one intercept budget. -/

namespace Bcs.TotalOracle.Footprint
open Finset Merkle.RandomOracle
open scoped Classical
variable {Q C I : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
  [Fintype I] [DecidableEq I]

/-- A selected, still-unseen footprint costs one local mean, rather than
the sum of the budgets of all possible completion cases. -/
theorem selected_unseen_average_le (select : (Q → C) → I)
    (support : I → Finset Q) (weight : I → (Q → C) → ℚ) (epsilon : ℚ)
    (hoff : ∀ i H H', (∀ q, q ∉ support i → H q = H' q) →
      (select H = i ↔ select H' = i))
    (hlocal : ∀ i off,
      average (fun on => weight i ((split (support i)).symm (on, off))) ≤ epsilon) :
    average (fun H => weight (select H) H) ≤ epsilon := by
  have hi (i : I) :
      average (fun H => if select H = i then weight i H else 0) ≤
        average (fun H => if select H = i then epsilon else 0) := by
    rw [average_split (support i), average_split (support i)]
    apply average_mono
    intro off
    let base := (split (C := C) (support i)).symm
      (fun _ => Classical.choice inferInstance, off)
    have hs (on : Inside (support i) → C) :
        select ((split (support i)).symm (on, off)) = i ↔ select base = i := by
      apply hoff
      intro q hq
      simp [base, split, Equiv.piEquivPiSubtypeProd, hq]
    simp_rw [hs]
    by_cases h : select base = i
    · simpa only [h, ↓reduceIte, average_const] using hlocal i off
    · simp [h]
  have he (H : Q → C) : (∑ i, if select H = i then weight i H else 0) =
      weight (select H) H := by simp
  have hb (H : Q → C) : (∑ i : I, if select H = i then epsilon else 0) = epsilon := by simp
  calc
    _ = average (fun H => ∑ i, if select H = i then weight i H else 0) := by simp_rw [he]
    _ ≤ average (fun H => ∑ i : I, if select H = i then epsilon else 0) := by
      rw [average_sum, average_sum]
      exact sum_le_sum fun i _ => hi i
    _ = _ := by simp_rw [hb]; exact average_const _

variable {Out : Type} [Fintype Out] [DecidableEq Out]

omit [Fintype Q] [Fintype C] [Nonempty C] [Fintype Out] [DecidableEq Out] in
/-- The complete output and queried set remain unchanged when only an
unread footprint is resampled. -/
theorem run_eq_of_avoids {N : ℕ} (tree : Tree Q C Out N)
    (H H' : Q → C) (s : Finset Q)
    (hoff : ∀ q, q ∉ s → H q = H' q)
    (havoid : Disjoint s (queried tree H).toFinset) : tree.run H' = tree.run H := by
  apply Tree.run_congr_on_trace
  intro qa hqa
  have hm : qa.1 ∈ (queried tree H).toFinset := by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨qa, hqa, rfl⟩)
  have hn : qa.1 ∉ s := fun hs => Finset.disjoint_left.mp havoid hs hm
  rw [← hoff qa.1 hn]
  exact (Tree.trace_sound tree H qa hqa).symm

/-- A convenient completion rule indexed by the prover's final output
and the set of coordinates it actually read. -/
theorem trace_completion_average_le {N : ℕ} (tree : Tree Q C Out N)
    (support : Out → Finset Q → Finset Q)
    (weight : Out → Finset Q → (Q → C) → ℚ) (epsilon : ℚ)
    (havoid : ∀ out seen, Disjoint (support out seen) seen)
    (hlocal : ∀ out seen off,
      average (fun on => weight out seen ((split (support out seen)).symm (on, off))) ≤ epsilon) :
    average (fun H => weight (tree.run H).1 (queried tree H).toFinset H) ≤ epsilon := by
  let select (H : Q → C) := ((tree.run H).1, (queried tree H).toFinset)
  apply selected_unseen_average_le select (fun i => support i.1 i.2)
    (fun i => weight i.1 i.2) epsilon ?_ (fun i => hlocal i.1 i.2)
  intro i H H' ho
  have step (A B : Q → C) (h : ∀ q, q ∉ support i.1 i.2 → A q = B q)
      (ha : select A = i) : select B = i := by
    have hav : Disjoint (support i.1 i.2) (queried tree A).toFinset := by
      have he := congrArg Prod.snd ha
      change (queried tree A).toFinset = i.2 at he
      rw [he]
      exact havoid _ _
    have he := run_eq_of_avoids tree A B _ h hav
    have hq : queried tree B = queried tree A := by simp only [queried, he]
    simpa only [select, he, hq] using ha
  exact ⟨step H H' ho, step H' H (fun q hq => (ho q hq).symm)⟩

end Bcs.TotalOracle.Footprint

namespace Bcs.TotalOracle.Footprint
open Finset
open scoped Classical
variable {Q C : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]

theorem average_eval_pair (x y : Q) (hxy : x ≠ y) (f : C → C → ℚ) :
    average (fun H : Q → C => f (H x) (H y)) =
      average (fun a => average (fun b => f a b)) := by
  rw [average_split {x}]
  let ix : Inside ({x} : Finset Q) := ⟨x, by simp⟩
  let oy : Outside ({x} : Finset Q) := ⟨y, by simpa using hxy.symm⟩
  have he (off : Outside ({x} : Finset Q) → C) :
      average (fun on => f ((split {x}).symm (on,off) x) ((split {x}).symm (on,off) y)) =
        average (fun a => f a (off oy)) := by
    simpa [split, Equiv.piEquivPiSubtypeProd, hxy.symm, ix, oy] using
      average_eval ix (fun a => f a (off oy))
  simp_rw [he]
  calc
    _ = average (fun b => average (fun a => f a b)) :=
      average_eval oy (fun b => average (fun a => f a b))
    _ = _ := by
      unfold average
      simp only [← sum_div]
      rw [sum_comm]

omit [Fintype Q] in
/-- A one-point completion can use any charge invariant under changes of
that point's answer, while holding its surrounding oracle fixed. -/
theorem singleton_completion_mean (x : Q) (weight : (Q → C) → C → ℚ)
    (hoff : ∀ H H', AgreeOff x H H' → ∀ c, weight H c = weight H' c)
    (epsilon : ℚ) (hlocal : ∀ H, average (weight H) ≤ epsilon)
    (off : Outside ({x} : Finset Q) → C) :
    average (fun on => weight ((split {x}).symm (on,off))
      ((split {x}).symm (on,off) x)) ≤ epsilon := by
  let base := (split (C := C) {x}).symm (fun _ => Classical.choice inferInstance, off)
  let ix : Inside ({x} : Finset Q) := ⟨x, by simp⟩
  have he (on : Inside ({x} : Finset Q) → C) :
      weight ((split {x}).symm (on,off)) ((split {x}).symm (on,off) x) =
        weight base (on ix) := by
    rw [hoff _ base (by
      intro q hq
      simp [base, split, Equiv.piEquivPiSubtypeProd, hq])]
    simp [split, Equiv.piEquivPiSubtypeProd, ix]
  simp_rw [he]
  exact (average_eval ix (weight base)).trans_le (hlocal base)

end Bcs.TotalOracle.Footprint

namespace Bcs.AffineBlock
open Finset TotalOracle TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical
variable {Q C Out : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]

noncomputable def proverCharge {N : ℕ} (tree : Tree Q C Out N)
    (weight : Q → (Q → C) → C → ℚ) (H : Q → C) : ℚ :=
  ∑ q, if q ∈ queried tree H then weight q H (H q) else 0

/-- Only first exposures by the prover are charged here. All verifier
completion is accounted for separately. -/
theorem proverCharge_average_le {N : ℕ} (tree : Tree Q C Out N)
    (domain : Finset Q) (weight : Q → (Q → C) → C → ℚ)
    (hoff : ∀ q H H', AgreeOff q H H' → ∀ c, weight q H c = weight q H' c)
    (slope : ℚ) (hs : 0 ≤ slope)
    (hlocal : ∀ q H, ∑ c, weight q H c ≤
      if q ∈ domain then Fintype.card C * slope else 0) :
    average (proverCharge tree weight) ≤ slope * average (queryCost domain tree) := by
  classical
  let budget (q : Q) : ℚ := if q ∈ domain then Fintype.card C * slope else 0
  have htotal (H : Q → C) :
      (∑ q ∈ univ.filter (fun q => q ∈ queried tree H), budget q) ≤
        Fintype.card C * slope * queryCost domain tree H := by
    have he : (univ.filter (fun q => q ∈ queried tree H)).filter (fun q => q ∈ domain) =
        (queried tree H).toFinset.filter (fun q => q ∈ domain) := by ext; simp
    simp only [budget, ← sum_filter]
    rw [he, sum_const, nsmul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_right (queried_domain_card_le domain tree H)
      (mul_nonneg (Nat.cast_nonneg (Fintype.card C)) hs)]
  have h := charged_rational_sum_le_expected (fun q H => q ∈ queried tree H)
    (fun q H H' ho => mem_queried_iff tree q ho) weight hoff budget
    (fun H => Fintype.card C * slope * queryCost domain tree H) hlocal
    (fun H => by
      convert htotal H using 1
      apply sum_congr
      · ext q; simp
      · intros; rfl)
  have hc : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℚ) < Fintype.card (Q → C) := by exact_mod_cast Fintype.card_pos
  have hav : (∑ H : Q → C, (Fintype.card C : ℚ) * slope * queryCost domain tree H) =
      Fintype.card C * slope * ∑ H : Q → C, queryCost domain tree H := by rw [mul_sum]
  rw [hav] at h
  unfold average proverCharge
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hn]
  apply (mul_le_mul_iff_left₀ hc).mp
  convert h using 1 <;> first | ring_nf | congr 1

/-- A block may use any nonnegative terminal completion whose expected
cost has one intercept budget. This avoids paying every verifier slot. -/
theorem oracle_sound_of_completion
    (domain : Finset Q) (weight : Q → (Q → C) → C → ℚ)
    (hoff : ∀ q H H', AgreeOff q H H' → ∀ c, weight q H c = weight q H' c)
    (hn : ∀ q H c, 0 ≤ weight q H c)
    (rate : Rate)
    (hlocal : ∀ q H, ∑ c, weight q H c ≤
      if q ∈ domain then Fintype.card C * rate.slope else 0)
    (completion : ∀ {N}, Tree Q C Out N → (Q → C) → ℚ)
    (hcompletion : ∀ N (tree : Tree Q C Out N),
      average (completion tree) ≤ rate.intercept)
    (hc : ∀ N (tree : Tree Q C Out N) H, 0 ≤ completion tree H)
    (failure : Out → (Q → C) → Prop)
    (hpay : ∀ N (tree : Tree Q C Out N) H, failure (tree.run H).1 H →
      1 ≤ proverCharge tree weight H + completion tree H) :
    OracleSound domain failure rate := by
  intro N tree
  refine ⟨queryCost_nonneg _ _, ?_⟩
  have hp (H : Q → C) : (if failure (tree.run H).1 H then (1 : ℚ) else 0) ≤
      proverCharge tree weight H + completion tree H := by
    by_cases hf : failure (tree.run H).1 H
    · simpa only [hf, ↓reduceIte] using hpay N tree H hf
    · simp only [hf, ↓reduceIte]
      exact add_nonneg (sum_nonneg fun q _ => by split_ifs; exact hn _ _ _; rfl) (hc N tree H)
  rw [density_eq_average]
  exact (average_mono hp).trans (by
    rw [average_add]
    linarith [proverCharge_average_le tree domain weight hoff rate.slope rate.slope_nonneg hlocal,
      hcompletion N tree])

end Bcs.AffineBlock
