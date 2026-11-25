import LfzkV1.ZkAdaptiveV1
import LfzkV1.CompiledLigeroZk
import LigeroFamily.Code.ReedSolomon

/-!
# Distinct columns from the three independent v7 Ligero masks

The deployed row interpolators use `k` samples for the proximity blind
and `2k-1` samples for the dot and quadratic masks. The dot mask has zero
sum at witness positions, and the quadratic mask vanishes there. This
file uses the exact degree cuts and never divides by the witness width.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.V7ColumnUniqueness

open Finset LigeroFamily Ligero.V1 Polynomial
open LigeroFamily.ReedSolomon
open LfzkV1.ZkAdaptiveV1 (v1Oracle)
open scoped Classical

variable {F : Type} [Field F] {r w n : ℕ}
variable (D : Domain F r w n)

private theorem degree_bound {p : F[X]} {d : ℕ} (hp : p ∈ Polynomial.degreeLT F d)
    (hne : p ≠ 0) : p.natDegree < d := by
  have h := Polynomial.mem_degreeLT.mp hp
  rw [degree_eq_natDegree hne] at h
  exact WithBot.coe_lt_coe.mp h

private theorem degree_lt_of_natDegree_lt {p : F[X]} {d : ℕ} (hp : p.natDegree < d) :
    p ∈ Polynomial.degreeLT F d := by
  rw [Polynomial.mem_degreeLT]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hp)

/-- The same base code, with the exact product-degree response cut used
by `layout_blinding_rows` and `make_range(0..dblock, ...)`. -/
noncomputable def deployedCode (hk : r + w ≤ n) (hkpos : 0 < r + w) : MultiplicativeCode F r w n where
  __ := multiplicativeCode D hk
  response := evaluationSpace D (2 * (r + w) - 1)
  base_le_response := by
    intro row hrow
    obtain ⟨p, hp, hEval⟩ := (mem_evaluationSpace D).mp hrow
    exact (mem_evaluationSpace D).mpr ⟨p, Polynomial.degreeLT_mono (by omega) hp, hEval⟩
  response_unique := by
    intro x y hx hy S hS hagree
    obtain ⟨p, hp, hpEval⟩ := (mem_evaluationSpace D).mp hx
    obtain ⟨q, hq, hqEval⟩ := (mem_evaluationSpace D).mp hy
    have hp' : p.degree < S.card := by
      rw [hS]
      exact (Polynomial.mem_degreeLT.mp hp).trans_le (by exact_mod_cast Nat.sub_le _ _)
    have hq' : q.degree < S.card := by
      rw [hS]
      exact (Polynomial.mem_degreeLT.mp hq).trans_le (by exact_mod_cast Nat.sub_le _ _)
    have he := Polynomial.eq_of_degrees_lt_of_eval_index_eq S D.injective.injOn hp' hq' (by
      intro i hi
      rw [← hpEval i, ← hqEval i]
      exact hagree i hi)
    funext i
    rw [hpEval i, hqEval i, he]
  mul_mem := by
    intro x y hx hy
    obtain ⟨p, hp, hpx⟩ := (mem_evaluationSpace D).mp hx
    obtain ⟨q, hq, hqy⟩ := (mem_evaluationSpace D).mp hy
    refine (mem_evaluationSpace D).mpr ⟨p * q, ?_, ?_⟩
    · by_cases hp0 : p = 0
      · simp [hp0]
      by_cases hq0 : q = 0
      · simp [hq0]
      have h1 := degree_bound hp hp0
      have h2 := degree_bound hq hq0
      apply degree_lt_of_natDegree_lt
      rw [natDegree_mul hp0 hq0]
      omega
    · intro i
      simp [rowMul, hpx i, hqy i]

variable (hk : r + w ≤ n) (hk3 : 3 ≤ r + w)
private theorem positive_geometry (h : 3 ≤ r + w) : 0 < r + w := by omega
local notation "Tight" => deployedCode D hk (positive_geometry hk3)

/-- The proximity mask can distinguish any two column positions. -/
theorem proximity_separates {i j : Fin n} (hne : i ≠ j) :
    ∃ row : (Tight).base, row.val (codePosition i) ≠ row.val (codePosition j) := by
  refine ⟨⟨D.point, (mem_evaluationSpace D).mpr ⟨Polynomial.X, ?_, by simp⟩⟩, ?_⟩
  · apply degree_lt_of_natDegree_lt
    simp only [natDegree_X]
    omega
  · exact D.injective.ne (fun h => hne (Sum.inr.inj h))

private theorem response_separates_vanishing {i j : Fin n} (hne : i ≠ j) :
    ∃ row : V1QuadraticMaskSpace Tight,
      row.val (codePosition i) ≠ row.val (codePosition j) := by
  let zW : F[X] := ∏ z : Fin w, (X - Polynomial.C (D.point (witnessPosition z)))
  let p : F[X] := zW * (X - Polynomial.C (D.point (codePosition i)))
  let row : EvaluationRow F r w n := fun k => p.eval (D.point k)
  have hp : p ∈ Polynomial.degreeLT F (2 * (r + w) - 1) := by
    apply degree_lt_of_natDegree_lt
    have hz : zW.natDegree = w := by
      simp [zW, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    have hd := Polynomial.natDegree_mul_le (p := zW)
      (q := X - Polynomial.C (D.point (codePosition i)))
    rw [hz, natDegree_X_sub_C] at hd
    dsimp only [p]
    omega
  have hW (z : Fin w) : row (witnessPosition z) = 0 := by
    have h : zW.eval (D.point (witnessPosition z)) = 0 := by
      dsimp only [zW]
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (mem_univ z) (by simp)
    simp [row, p, eval_mul, h]
  refine ⟨⟨row, (mem_evaluationSpace D).mpr ⟨p, hp, fun _ => rfl⟩, hW⟩, ?_⟩
  have hi : row (codePosition i) = 0 := by simp [row, p, eval_mul]
  have hj : row (codePosition j) ≠ 0 := by
    have hv : zW.eval (D.point (codePosition j)) ≠ 0 := by
      dsimp only [zW]
      rw [Polynomial.eval_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro z _
      simp only [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.mpr (D.injective.ne (by simp [codePosition, witnessPosition]))
    have hdiff : D.point (codePosition j) - D.point (codePosition i) ≠ 0 :=
      sub_ne_zero.mpr (D.injective.ne (fun h => hne.symm (Sum.inr.inj h)))
    simpa [row, p, eval_mul] using mul_ne_zero hv hdiff
  exact fun h => hj (h.symm.trans hi)

/-- Distinguish two columns with a legal quadratic mask. -/
theorem quadratic_separates {i j : Fin n} (hne : i ≠ j) :
    ∃ row : V1QuadraticMaskSpace Tight, row.val (codePosition i) ≠ row.val (codePosition j) :=
  response_separates_vanishing D hk hk3 hne

/-- Witness-vanishing directions are also valid dot-mask directions.
This applies in characteristic two, including when the width equals two
and the geometry supplies the necessary degree room. -/
theorem linear_separates {i j : Fin n} (hne : i ≠ j) :
    ∃ row : V1LinearMaskSpace Tight, row.val (codePosition i) ≠ row.val (codePosition j) := by
  obtain ⟨row, hsep⟩ := quadratic_separates D hk hk3 hne
  exact ⟨⟨row.val, row.property.1, by simp [row.property.2]⟩, hsep⟩

section DotSampler

private def correctWitnessSum (first : Fin w) (values : Fin w → F) : Fin w → F :=
  Function.update values first (values first - ∑ i, values i)

private theorem correctWitnessSum_zero (first : Fin w) (values : Fin w → F) :
    ∑ i, correctWitnessSum first values i = 0 := by
  rw [correctWitnessSum, Finset.sum_update_of_mem (mem_univ first),
    Finset.sdiff_singleton_eq_erase, ← Finset.sum_erase_add univ values (mem_univ first)]
  ring

/-- Subtracting the witness-slot sum at one specified slot samples the
zero-sum vectors uniformly. The discarded raw sample is the first factor. -/
def dotSamplerEquiv (first : Fin w) :
    (Fin w → F) ≃ (F × {v : Fin w → F // (∑ i, v i) = 0}) where
  toFun v := (v first, ⟨correctWitnessSum first v, correctWitnessSum_zero first v⟩)
  invFun x := Function.update x.2.val first x.1
  left_inv v := by
    funext j
    by_cases hj : j = first
    · subst j
      exact Function.update_self _ _ _
    · simp only [correctWitnessSum, Function.update_of_ne hj]
  right_inv := by
    rintro ⟨a, v⟩
    refine Prod.ext (Function.update_self _ _ _) (Subtype.ext ?_)
    funext j
    change correctWitnessSum first (Function.update v.val first a) j = v.val j
    by_cases hj : j = first
    · subst j
      simp only [correctWitnessSum, Function.update_self, Finset.sum_update_of_mem (mem_univ first),
        Finset.sdiff_singleton_eq_erase]
      have h := (Finset.sum_erase_add univ v.val (mem_univ first)).trans v.property
      linear_combination -h
    · simp only [correctWitnessSum, Function.update_of_ne hj]

end DotSampler

section Finite

variable [Fintype F]

private def difference (S : Submodule F (EvaluationRow F r w n)) (i j : Fin n) : S →ₗ[F] F where
  toFun row := row.val (codePosition i) - row.val (codePosition j)
  map_add' x y := by
    change x.val (codePosition i) + y.val (codePosition i) -
      (x.val (codePosition j) + y.val (codePosition j)) = _
    ring
  map_smul' a x := by
    change a * x.val (codePosition i) - a * x.val (codePosition j) = _
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

private theorem difference_surjective {S : Submodule F (EvaluationRow F r w n)} {i j : Fin n}
    (hsep : ∃ row : S, row.val (codePosition i) ≠ row.val (codePosition j)) :
    Function.Surjective (difference S i j) := by
  obtain ⟨row, hne⟩ := hsep
  let f := difference S i j
  have hv : f row ≠ 0 := sub_ne_zero.mpr hne
  intro a
  refine ⟨(a / f row) • row, ?_⟩
  change f ((a / f row) • row) = a
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

/-- The three dedicated masks are independent coordinates in the tape. -/
abbrev MaskCoins (C : MultiplicativeCode F r w n) :=
  C.base × V1LinearMaskSpace C × V1QuadraticMaskSpace C

noncomputable instance (C : MultiplicativeCode F r w n) : Fintype (MaskCoins C) :=
  Fintype.ofFinite _

private def differences (C : MultiplicativeCode F r w n) (i j : Fin n) : MaskCoins C →ₗ[F] F × F × F :=
  (difference C.base i j).prodMap
    ((difference (V1LinearMaskSpace C) i j).prodMap (difference (V1QuadraticMaskSpace C) i j))

/-- The difference triple takes every field triple equally often. This
is independent of how the core rows were sampled. -/
theorem differences_surjective {i j : Fin n} (hne : i ≠ j) :
    Function.Surjective (differences Tight i j) := by
  rintro ⟨a, b, c⟩
  obtain ⟨x, hx⟩ := difference_surjective (proximity_separates D hk hk3 hne) a
  obtain ⟨y, hy⟩ := difference_surjective (linear_separates D hk hk3 hne) b
  obtain ⟨z, hz⟩ := difference_surjective (quadratic_separates D hk hk3 hne) c
  exact ⟨(x, y, z), Prod.ext hx (Prod.ext hy hz)⟩

private theorem zero_fiber_card_mul {X Y : Type} [AddCommGroup X] [Module F X] [Fintype X]
    [AddCommGroup Y] [Module F Y] [Fintype Y] (f : X →ₗ[F] Y) (hf : Function.Surjective f) :
    (univ.filter fun x : X => f x = 0).card * Fintype.card Y = Fintype.card X := by
  classical
  choose g hg using hf
  let split : X ≃ (Y × LinearMap.ker f) := {
    toFun x := (f x, ⟨x - g (f x), by rw [LinearMap.mem_ker, map_sub, hg, sub_self]⟩)
    invFun p := g p.1 + p.2.val
    left_inv x := by dsimp only; abel
    right_inv := by
      rintro ⟨y, z⟩
      have h : f (g y + z.val) = y := by
        rw [map_add, hg, LinearMap.mem_ker.mp z.property, add_zero]
      refine Prod.ext h (Subtype.ext ?_)
      change g y + z.val - g (f (g y + z.val)) = z.val
      rw [h, add_sub_cancel_left] }
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  let fiber := univ.filter fun x : X => f x = 0
  let fiberEquiv : ↥fiber ≃ LinearMap.ker f :=
    Equiv.subtypeEquivRight fun x => by simp [fiber, LinearMap.mem_ker]
  have hcard : fiber.card = Fintype.card (LinearMap.ker f) :=
    (Fintype.card_coe fiber).symm.trans (Fintype.card_congr fiberEquiv)
  change fiber.card * Fintype.card Y = Fintype.card X
  rw [hcard, mul_comm, Fintype.card_congr split, Fintype.card_prod]

/-- A fixed core tape and a fresh triple of masks yield one v1 tape. -/
def withMasks (C : MultiplicativeCode F r w n) {nw nq : ℕ}
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F)
    (masks : MaskCoins C) : V1ProverRandomness C nw nq 1 where
  corePadding := core
  proximityBlind _ := masks.1
  linearMask _ := masks.2.1
  quadraticMask _ := masks.2.2

/-- For one deployed repetition, the conditional mask triple is literally
the three remaining factors of the original abstract tape. -/
def tapeEquiv (C : MultiplicativeCode F r w n) {nw nq : ℕ} :
    V1ProverRandomness C nw nq 1 ≃
      (((block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F) × MaskCoins C) where
  toFun t := (t.corePadding, t.proximityBlind 0, t.linearMask 0, t.quadraticMask 0)
  invFun t := withMasks C t.1 t.2
  left_inv := by
    rintro ⟨core, linear, quadratic, blind⟩
    have done {X : Type} (f : Fin 1 → X) : (fun _ : Fin 1 => f 0) = f :=
      funext fun j => congrArg f (Subsingleton.elim 0 j)
    dsimp only [withMasks]
    rw [done linear, done quadratic, done blind]
  right_inv := by rintro ⟨core, ld, dot, quad⟩; rfl

/-- Even at fixed core messages and random prefixes, the probability of
equality of any two distinct complete columns is at most `1/q³`. -/
theorem duplicate_pair_count {nw nq : ℕ} (messages : CoreMessages F nw nq w)
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F)
    {i j : Fin n} (hne : i ≠ j) :
    (univ.filter fun masks : MaskCoins Tight =>
      (v1Oracle messages (withMasks Tight core masks)).column i =
        (v1Oracle messages (withMasks Tight core masks)).column j).card * (Fintype.card F)^3 ≤
      Fintype.card (MaskCoins Tight) := by
  classical
  let f := differences Tight i j
  have hb := zero_fiber_card_mul f (differences_surjective D hk hk3 hne)
  have hr : Fintype.card (F × F × F) = (Fintype.card F)^3 := by simp [pow_succ, Nat.mul_assoc]
  rw [hr] at hb
  refine (Nat.mul_le_mul_right _ (card_le_card ?_)).trans_eq hb
  intro masks hm
  have eq := (mem_filter.mp hm).2
  have hp := congrArg (fun col : SchemeColumn F NoMask Mask nw nq 1 => col.proximityBlind 0) eq
  have hl := congrArg (fun col : SchemeColumn F NoMask Mask nw nq 1 => col.directMask 0 .linear) eq
  have hq := congrArg (fun col : SchemeColumn F NoMask Mask nw nq 1 => col.directMask 0 .quadratic) eq
  simp only [mem_filter, mem_univ, true_and]
  exact Prod.ext (sub_eq_zero.mpr hp) (Prod.ext (sub_eq_zero.mpr hl) (sub_eq_zero.mpr hq))

private theorem increasing_pair_count (n : ℕ) :
    ((univ : Finset (Fin n × Fin n)).filter fun p => p.1 < p.2).card ≤ n.choose 2 := by
  classical
  let pairs := (univ : Finset (Fin n × Fin n)).filter fun p => p.1 < p.2
  let asSet (p : Fin n × Fin n) : Finset (Fin n) := {p.1, p.2}
  have hi : Set.InjOn asSet (pairs : Set (Fin n × Fin n)) := by
    intro a ha b hb h
    have ha' : a.1 < a.2 := (mem_filter.mp ha).2
    have hb' : b.1 < b.2 := (mem_filter.mp hb).2
    have h0 : a.1 ∈ asSet b := h ▸ (by simp [asSet] : a.1 ∈ asSet a)
    have h1 : a.2 ∈ asSet b := h ▸ (by simp [asSet] : a.2 ∈ asSet a)
    simp only [asSet, mem_insert, mem_singleton] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact (ha'.ne (h0.trans h1.symm)).elim
    · exact Prod.ext h0 h1
    · exact (lt_asymm (h0 ▸ h1 ▸ ha') hb').elim
    · exact (ha'.ne (h0.trans h1.symm)).elim
  have hsub : pairs.image asSet ⊆ (univ : Finset (Fin n)).powersetCard 2 := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
    have h : p.1 ≠ p.2 := (mem_filter.mp hp).2.ne
    exact mem_powersetCard.mpr ⟨subset_univ _, by simp [asSet, h]⟩
  calc
    pairs.card = (pairs.image asSet).card := (card_image_of_injOn hi).symm
    _ ≤ ((univ : Finset (Fin n)).powersetCard 2).card := card_le_card hsub
    _ = n.choose 2 := by simp

/-- A union bound over unordered pairs, conditional on any fixed core data. -/
theorem duplicate_columns_count {nw nq : ℕ} (messages : CoreMessages F nw nq w)
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F) :
    (univ.filter fun masks : MaskCoins Tight =>
      ¬ Function.Injective (v1Oracle messages (withMasks Tight core masks)).column).card *
      (Fintype.card F)^3 ≤ n.choose 2 * Fintype.card (MaskCoins Tight) := by
  classical
  let cols (masks : MaskCoins Tight) := (v1Oracle messages (withMasks Tight core masks)).column
  let bad := univ.filter fun masks => ¬ Function.Injective (cols masks)
  let pairs := (univ : Finset (Fin n × Fin n)).filter fun p => p.1 < p.2
  let collision (p : Fin n × Fin n) := univ.filter fun masks => cols masks p.1 = cols masks p.2
  have hsub : bad ⊆ pairs.biUnion collision := by
    intro masks hm
    have hbad : ¬ Function.Injective (cols masks) := (mem_filter.mp hm).2
    have hc : ∃ i j, cols masks i = cols masks j ∧ i ≠ j := by
      by_contra hn
      apply hbad
      intro i j hEq
      by_contra hne
      exact hn ⟨i, j, hEq, hne⟩
    obtain ⟨i, j, he, hne⟩ := hc
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mem_biUnion.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hlt⟩,
        mem_filter.mpr ⟨mem_univ _, he⟩⟩
    · exact mem_biUnion.mpr ⟨(j, i), mem_filter.mpr ⟨mem_univ _, hgt⟩,
        mem_filter.mpr ⟨mem_univ _, he.symm⟩⟩
  change bad.card * (Fintype.card F)^3 ≤ _
  calc
    _ ≤ (∑ p ∈ pairs, (collision p).card) * (Fintype.card F)^3 :=
      Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ p ∈ pairs, (collision p).card * (Fintype.card F)^3 := Finset.sum_mul _ _ _
    _ ≤ ∑ _p ∈ pairs, Fintype.card (MaskCoins Tight) := by
      apply sum_le_sum
      intro p hp
      exact duplicate_pair_count D hk hk3 messages core (mem_filter.mp hp).2.ne
    _ = pairs.card * Fintype.card (MaskCoins Tight) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (increasing_pair_count n)

/-- The fixed-core distinct-column failure probability. -/
theorem duplicate_columns_ratio {nw nq : ℕ} (messages : CoreMessages F nw nq w)
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F) :
    ((univ.filter fun masks : MaskCoins Tight =>
      ¬ Function.Injective (v1Oracle messages (withMasks Tight core masks)).column).card : ℚ) /
      Fintype.card (MaskCoins Tight) ≤ (n.choose 2 : ℚ) / (Fintype.card F : ℚ)^3 := by
  apply (div_le_div_iff₀ (by exact_mod_cast (Fintype.card_pos (α := MaskCoins Tight)))
    (pow_pos (Nat.cast_pos.mpr (Fintype.card_pos (α := F))) _)).mpr
  exact_mod_cast duplicate_columns_count D hk hk3 messages core

/-- A bound that holds in every conditional fibre also holds after sampling
the conditioning coins uniformly. -/
theorem probOf_average_le {A R T : Type} [Fintype A] [Fintype R]
    (f : A → R → T) (p : T → Prop) {e : ℚ} (he : 0 ≤ e)
    (h : ∀ a, probOf (f a) p ≤ e) :
    probOf (fun x : A × R => f x.1 x.2) p ≤ e := by
  rw [probOf_prod f p]
  rcases Nat.eq_zero_or_pos (Fintype.card A) with hA | hA
  · simpa only [hA, Nat.cast_zero, div_zero] using he
  have hcard : (0 : ℚ) < Fintype.card A := by exact_mod_cast hA
  apply (div_le_iff₀ hcard).mpr
  calc
    _ ≤ ∑ _a : A, e := Finset.sum_le_sum fun a _ => h a
    _ = _ := by rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- Averaging over independent core-padding coins preserves the duplicate
bound. The padding sampler may take values in any supported subset. -/
theorem duplicate_columns_sampled {A : Type} [Fintype A] {nw nq : ℕ}
    (messages : CoreMessages F nw nq w)
    (padding : A → (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F) :
    probOf (fun x : A × MaskCoins Tight => (v1Oracle messages (withMasks Tight (padding x.1) x.2)).column)
      (fun cols => ¬ Function.Injective cols) ≤ (n.choose 2 : ℚ) / (Fintype.card F : ℚ)^3 := by
  let cols (a : A) (masks : MaskCoins Tight) : Fin n → SchemeColumn F NoMask Mask nw nq 1 :=
    (v1Oracle messages (withMasks Tight (padding a) masks)).column
  have hf (a : A) : probOf (cols a) (fun c => ¬ Function.Injective c) ≤
      (n.choose 2 : ℚ) / (Fintype.card F : ℚ)^3 := by
    unfold probOf
    convert duplicate_columns_ratio D hk hk3 messages (padding a) using 3
    apply congrArg Finset.card
    ext masks
    simp only [mem_filter, mem_univ, true_and, cols]
  exact probOf_average_le cols _ (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) hf

variable [DecidableEq F]

/-- Restrict the core sampler while preserving the three uniform independent
mask factors of the tape. -/
theorem duplicate_columns_tape_restricted {nw nq : ℕ} (messages : CoreMessages F nw nq w)
    (p : ((block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F) → Prop)
    [Fintype (Subtype p)] [Fintype {ρ : V1ProverRandomness Tight nw nq 1 // p ρ.corePadding}] :
    probOf id (fun x : {ρ : V1ProverRandomness Tight nw nq 1 // p ρ.corePadding} =>
      ¬ Function.Injective (v1Oracle messages x.val).column) ≤ (n.choose 2 : ℚ) / (Fintype.card F : ℚ)^3 := by
  let e : Subtype p × MaskCoins Tight ≃ {ρ : V1ProverRandomness Tight nw nq 1 // p ρ.corePadding} :=
    { toFun := fun x => ⟨withMasks Tight x.1.val x.2, x.1.property⟩
      invFun := fun ρ =>
        let x := tapeEquiv Tight ρ.val
        (⟨x.1, ρ.property⟩, x.2)
      left_inv := fun _ => rfl
      right_inv := fun ρ => Subtype.ext ((tapeEquiv Tight).symm_apply_apply ρ.val) }
  rw [← probOf_equiv e id]
  exact duplicate_columns_sampled D hk hk3 messages Subtype.val

end Finite

section Union

private theorem card_filter_or_le {A : Type} (s : Finset A) (p q : A → Prop)
    (dp : DecidablePred p) (dq : DecidablePred q) (dpq : DecidablePred (fun a => p a ∨ q a)) :
    (@Finset.filter A (fun a => p a ∨ q a) dpq s).card ≤
      (@Finset.filter A p dp s).card + (@Finset.filter A q dq s).card := by
  classical
  calc
    _ = ((@Finset.filter A p dp s) ∪ (@Finset.filter A q dq s)).card := by
      congr 1
      ext a
      simp only [mem_filter, mem_union]
      tauto
    _ ≤ _ := Finset.card_union_le _ _

private theorem probOf_id_or_le {A : Type} [Fintype A] (p q : A → Prop) :
    probOf id (fun a => p a ∨ q a) ≤ probOf id p + probOf id q := by
  classical
  rw [probOf, probOf, probOf, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Nat.cast_add, Nat.cast_le]
  exact card_filter_or_le univ (fun a => p (id a)) (fun a => q (id a)) _ _ _

private theorem probOf_independent_or_le {R S : Type}
    [Fintype R] [Nonempty R] [Fintype S] [Nonempty S] (p : R → Prop) (q : S → Prop) :
    probOf id (fun x : R × S => p x.1 ∨ q x.2) ≤ probOf id p + probOf id q := by
  have hp : probOf id (fun x : R × S => p x.1) = probOf id p :=
    LfzkV1.CompiledLigeroZk.probOf_fst (id : R → R) p
  have hq : probOf id (fun x : R × S => q x.2) = probOf id q := by
    rw [← probOf_equiv (Equiv.prodComm S R) id]
    exact LfzkV1.CompiledLigeroZk.probOf_fst (id : S → S) q
  exact (probOf_id_or_le (fun x : R × S => p x.1) (fun x => q x.2)).trans_eq (congrArg₂ (· + ·) hp hq)

/-- Combine two duplicate-column bounds conditioned on shared shares and
independent front-end blinders. The two core samplers may have different
supports. -/
theorem probOf_two_side_bad_le {A B C R S : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    (bad₁ : A → B → R → Prop) (bad₂ : A → C → S → Prop)
    {e₁ e₂ : ℚ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (h₁ : ∀ a b, probOf id (bad₁ a b) ≤ e₁) (h₂ : ∀ a c, probOf id (bad₂ a c) ≤ e₂) :
    probOf id (fun x : A × (B × R) × (C × S) => bad₁ x.1 x.2.1.1 x.2.1.2 ∨
      bad₂ x.1 x.2.2.1 x.2.2.2) ≤ e₁ + e₂ := by
  let gather : (A × B × C) × (R × S) ≃ A × (B × R) × (C × S) :=
    { toFun := fun x => (x.1.1, (x.1.2.1, x.2.1), x.1.2.2, x.2.2)
      invFun := fun x => ((x.1, x.2.1.1, x.2.2.1), x.2.1.2, x.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← probOf_equiv gather id]
  exact probOf_average_le (fun a rs => gather (a, rs)) _
    (add_nonneg he₁ he₂) (fun a =>
      (probOf_independent_or_le (bad₁ a.1 a.2.1) (bad₂ a.1 a.2.2)).trans
        (add_le_add (h₁ a.1 a.2.1) (h₂ a.1 a.2.2)))

end Union

end LfzkV1.V7ColumnUniqueness
