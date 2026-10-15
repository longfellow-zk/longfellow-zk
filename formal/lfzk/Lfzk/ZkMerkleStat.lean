import Lfzk.ZkHiding
import Merkle.Hiding

/-!
# Statistical hiding of the salted Merkle commitment, against a full view of the oracle

`Lfzk.ZkMerkle` bounds the hiding of the salted Merkle commitment against a distinguisher that
makes `f` queries to a lazily sampled oracle; its bound grows with `f` (guessing an unopened
leaf's nonce).  Here the distinguisher instead receives the Merkle oracle `H : Enc → D` **in full**,
so no query bound appears: the guarantee is statistical, and it needs long nonces.

## The statement

`view_statClose`: commit to `m` under uniform nonces `r : Fin n → Salt` and a uniform oracle
`H`, open the set `I`.  The pair (`H`, root and opening) is `|Iᶜ| · ε`-close to the same pair
computed from **fresh uniform digests** for the unopened leaves, whenever

```
|D| ≤ 4 · ε² · |Salt|
```

The simulated view reads `m` only on `I`, so two messages agreeing on `I` give views
`2 · |Iᶜ| · ε`-close.  At 256-bit digests, `|Salt| = 2^542` gives `ε = 2^-144` per leaf.

## The argument

* **One leaf** (`leaf_statClose`): `(H, H(x(r)))` with `r` uniform and `x` injective is
  `ε`-close to `(H, y)` with `y` uniform.  This is the leftover hash lemma for a uniformly random
  function, by one Cauchy–Schwarz over the pairs `(H, y)`; the expected collision probability of
  `y ↦ H(x(r))` is at most `1/|Salt| + 1/|D|` (`Merkle.RandomOracle.fixed_pair_card_le`).  It is
  stated in the squared form `|D| ≤ 4ε²|Salt|` so that no square root enters `ℚ`.
* **All unopened leaves** (`digests_statClose`): a hybrid replacing the unopened leaves' digests
  one at a time (`hyb`, `hyb_step`).  The leaf being replaced is the only place its nonce enters
  (its nonce is not opened), so each step is the one-leaf lemma with everything else as fixed outer
  randomness.  No nonce-distinctness, no codec disjointness across roles: only injectivity of the
  leaf encoding in the nonce.
* **The Merkle view** (`commitLabels_eq_digestLabels`): every label of the honest heap is a
  function of the leaf digests and `H` (`digestLabels`), so the root and the frontier digests are
  post-processing of the digests.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkMerkleStat

open Merkle Merkle.MH

/-! ## An unread coordinate -/

/-- A coordinate the experiment does not read does not change a probability. -/
theorem probOf_fst {R Z T : Type} [Fintype R] [Fintype Z] [Nonempty Z] (f : R → T)
    (P : T → Prop) : probOf (fun p : R × Z => f p.1) P = probOf f P := by
  classical
  unfold probOf
  have hset : (Finset.filter (fun p : R × Z => P (f p.1)) Finset.univ)
      = (Finset.filter (fun r => P (f r)) Finset.univ) ×ˢ (Finset.univ : Finset Z) := by
    ext p
    simp
  have hZ : ((Fintype.card Z : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hset, Finset.card_product, Finset.card_univ, Fintype.card_prod]
  push_cast
  exact mul_div_mul_right _ _ hZ

/-! ## One leaf: the leftover hash lemma for a uniformly random function

`N(H, y)` is the number of nonces `r` with `H (x r) = y` (`fib`).  The gap between the real and
the ideal probability of an event `P` is `Σ_{H,y} ([P] − ½)(q·N − s) / (h·s·q)` (`sum_centred`, the
`½` is free since `Σ_y (q·N − s) = 0`), and Cauchy–Schwarz bounds its square by
`(h·q/4) · Σ (q·N − s)² / (h·s·q)²`, where `Σ (q·N − s)² ≤ q²·s·h` is the collision count
(`collision_le`, from `Merkle.RandomOracle.fixed_pair_card_le`). -/

section LeafCount

open Finset

open Classical in
/-- Indicator of `P (H, y)`, as a rational. -/
noncomputable def ind {Enc D : Type} (P : (Enc → D) × D → Prop) (H : Enc → D) (y : D) : ℚ :=
  if P (H, y) then 1 else 0

/-- The fibre size `N(H, y) = #{r : H (x r) = y}`, as a rational. -/
def fib {Salt D Enc : Type} [Fintype Salt] [DecidableEq D] (x : Salt → Enc) (H : Enc → D)
    (y : D) : ℚ :=
  ∑ r : Salt, if H (x r) = y then 1 else 0

section
variable {Salt D Enc : Type} [Fintype Salt] [Fintype D] [Fintype Enc]
  [DecidableEq Enc] [DecidableEq D]

omit [Fintype Enc] [DecidableEq Enc] in
lemma sum_fib (x : Salt → Enc) (H : Enc → D) : ∑ y, fib x H y = Fintype.card Salt := by
  unfold fib
  rw [Finset.sum_comm]
  simp

omit [Fintype Enc] [DecidableEq Enc] in
lemma sum_fib_sq (x : Salt → Enc) (H : Enc → D) :
    ∑ y, fib x H y ^ 2 = ∑ r : Salt, ∑ r' : Salt, if H (x r) = H (x r') then (1 : ℚ) else 0 := by
  simp only [fib, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun r' _ => ?_
  simp [eq_comm]

omit [Fintype Salt] in
lemma pair_card_mul_le (x : Salt → Enc) (hx : Function.Injective x) (r r' : Salt)
    (hne : r ≠ r') :
    Fintype.card D * (Finset.filter (fun H : Enc → D => H (x r) = H (x r')) univ).card
      ≤ Fintype.card (Enc → D) := by
  have h1 := Merkle.RandomOracle.fixed_pair_card_le (D := D) (x r) (x r') (hx.ne hne)
  have : Nonempty Enc := ⟨x r⟩
  have hE : Fintype.card Enc ≠ 0 := Fintype.card_ne_zero
  rw [Fintype.card_fun, ← mul_pow_sub_one hE]
  exact Nat.mul_le_mul_left _ h1

lemma collision_le (x : Salt → Enc) (hx : Function.Injective x) :
    (Fintype.card D : ℚ) * ∑ H : Enc → D, ∑ y, fib x H y ^ 2
      ≤ Fintype.card D * Fintype.card Salt * Fintype.card (Enc → D)
        + Fintype.card Salt ^ 2 * Fintype.card (Enc → D) := by
  classical
  have hswap : ∑ H : Enc → D, ∑ y, fib x H y ^ 2
      = ∑ r : Salt, ∑ r' : Salt,
          ((Finset.filter (fun H : Enc → D => H (x r) = H (x r')) univ).card : ℚ) := by
    simp only [sum_fib_sq]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun r' _ => ?_
    rw [Finset.natCast_card_filter]
  have hterm : ∀ r r' : Salt,
      (Fintype.card D : ℚ) * (Finset.filter (fun H : Enc → D => H (x r) = H (x r')) univ).card
        ≤ (if r = r' then (Fintype.card D * Fintype.card (Enc → D) : ℚ) else 0)
          + Fintype.card (Enc → D) := by
    intro r r'
    by_cases h : r = r'
    · subst h
      simp
    · rw [if_neg h, zero_add]
      exact_mod_cast pair_card_mul_le x hx r r' h
  rw [hswap, Finset.mul_sum]
  calc ∑ r : Salt, (Fintype.card D : ℚ) * ∑ r' : Salt,
          ((Finset.filter (fun H : Enc → D => H (x r) = H (x r')) univ).card : ℚ)
      = ∑ r : Salt, ∑ r' : Salt, (Fintype.card D : ℚ) *
          ((Finset.filter (fun H : Enc → D => H (x r) = H (x r')) univ).card : ℚ) := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ r : Salt, ∑ r' : Salt,
          ((if r = r' then (Fintype.card D * Fintype.card (Enc → D) : ℚ) else 0)
            + Fintype.card (Enc → D)) :=
        sum_le_sum fun r _ => sum_le_sum fun r' _ => hterm r r'
    _ = _ := by
        simp [Finset.sum_add_distrib]
        ring

lemma probOf_real (x : Salt → Enc) (P : (Enc → D) × D → Prop) :
    probOf (fun p : (Enc → D) × Salt => (p.1, p.1 (x p.2))) P
      = (∑ H : Enc → D, ∑ y : D, ind P H y * fib x H y)
          / (Fintype.card (Enc → D) * Fintype.card Salt) := by
  unfold probOf
  rw [Finset.natCast_card_filter, Fintype.card_prod, Nat.cast_mul]
  congr 1
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun H _ => ?_
  simp only [fib, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun r _ => ?_
  simp [ind]

omit [DecidableEq D] in
lemma probOf_ideal (P : (Enc → D) × D → Prop) :
    probOf (fun p : (Enc → D) × D => p) P
      = (∑ H : Enc → D, ∑ y : D, ind P H y) / (Fintype.card (Enc → D) * Fintype.card D) := by
  unfold probOf
  rw [Finset.natCast_card_filter, Fintype.card_prod, Nat.cast_mul]
  congr 1
  rw [Fintype.sum_prod_type]
  rfl

omit [Fintype Salt] [DecidableEq D] in
lemma sum_ind_sub_half_sq (P : (Enc → D) × D → Prop) :
    ∑ H : Enc → D, ∑ y : D, (ind P H y - 1 / 2) ^ 2
      = (Fintype.card (Enc → D) : ℚ) * Fintype.card D / 4 := by
  have e : ∀ H y, (ind P H y - 1 / 2) ^ 2 = (1 / 4 : ℚ) := by
    intro H y
    unfold ind
    split_ifs <;> norm_num
  simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [Fintype Enc] [DecidableEq Enc] in
lemma sum_dev (x : Salt → Enc) (H : Enc → D) :
    ∑ y : D, ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_fib]
  simp

omit [Fintype Enc] [DecidableEq Enc] in
lemma sum_dev_sq (x : Salt → Enc) (H : Enc → D) :
    ∑ y : D, ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt) ^ 2
      = (Fintype.card D : ℚ) ^ 2 * ∑ y, fib x H y ^ 2
        - Fintype.card D * Fintype.card Salt ^ 2 := by
  have e : ∀ y, ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt) ^ 2
      = (Fintype.card D : ℚ) ^ 2 * fib x H y ^ 2
        + (-2 * Fintype.card D * Fintype.card Salt) * fib x H y
        + (Fintype.card Salt : ℚ) ^ 2 := fun y => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, sum_fib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- The real-minus-ideal numerator, centred: `Σ_{H,y} [P] (q N − s) = Σ_{H,y} ([P] − ½)(q N − s)`. -/
lemma sum_centred (x : Salt → Enc) (P : (Enc → D) × D → Prop) :
    ∑ H : Enc → D, ∑ y : D,
        (ind P H y - 1 / 2) * ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt)
      = (Fintype.card D : ℚ) * (∑ H : Enc → D, ∑ y : D, ind P H y * fib x H y)
        - Fintype.card Salt * (∑ H : Enc → D, ∑ y : D, ind P H y) := by
  have e1 : ∀ H : Enc → D, ∑ y : D,
        (ind P H y - 1 / 2) * ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt)
      = (Fintype.card D : ℚ) * (∑ y : D, ind P H y * fib x H y)
        - Fintype.card Salt * (∑ y : D, ind P H y) := by
    intro H
    have e : ∑ y : D,
          (ind P H y - 1 / 2) * ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt)
        = ∑ y : D, ((Fintype.card D : ℚ) * (ind P H y * fib x H y)
            - Fintype.card Salt * ind P H y)
          - 1 / 2 * ∑ y : D, ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact sum_congr rfl fun y _ => by ring
    rw [e, sum_dev, mul_zero, sub_zero, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun H _ => e1 H, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.mul_sum]

/-- The collision count bounds the second moment of the centred fibre sizes. -/
lemma sum_dev_sq_le (x : Salt → Enc) (hx : Function.Injective x) :
    ∑ H : Enc → D, ∑ y : D, ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt) ^ 2
      ≤ (Fintype.card D : ℚ) ^ 2 * Fintype.card Salt * Fintype.card (Enc → D) := by
  simp only [sum_dev_sq]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_left (collision_le (D := D) x hx)
    (Nat.cast_nonneg (Fintype.card D) : (0 : ℚ) ≤ Fintype.card D)
  nlinarith

end

/-- **One leaf.**  `(H, H (x r))`, for a uniform oracle `H` and a uniform nonce `r` fed through an
injective encoding `x`, is `ε`-close to `(H, y)` with `y` uniform, when `|D| ≤ 4ε²|Salt|`. -/
theorem leaf_statClose {Salt D Enc : Type} [Fintype Salt] [Fintype D] [Fintype Enc]
    [DecidableEq Enc] [DecidableEq D]
    (x : Salt → Enc) (hx : Function.Injective x) {ε : ℚ} (hε : 0 ≤ ε)
    (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt) :
    StatClose ε (fun p : (Enc → D) × Salt => (p.1, p.1 (x p.2)))
      (fun p : (Enc → D) × D => p) := by
  intro P
  rcases Nat.eq_zero_or_pos (Fintype.card D) with hq0 | hqpos
  · -- `D` is empty: both coin spaces are empty, so both probabilities are `0 / 0 = 0`.
    have hreal : Fintype.card ((Enc → D) × Salt) = 0 := by
      rw [Fintype.card_prod]
      rcases isEmpty_or_nonempty Salt with hS | ⟨⟨r⟩⟩
      · simp
      · have : Nonempty Enc := ⟨x r⟩
        rw [Fintype.card_fun, hq0, zero_pow Fintype.card_ne_zero, zero_mul]
    have hideal : Fintype.card ((Enc → D) × D) = 0 := by
      rw [Fintype.card_prod, hq0, mul_zero]
    simp [probOf, hreal, hideal, hε]
  · have hq : (0 : ℚ) < Fintype.card D := by exact_mod_cast hqpos
    have hs : (0 : ℚ) < Fintype.card Salt := by
      by_contra h
      have h0 : (Fintype.card Salt : ℚ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
      rw [h0, mul_zero] at hD
      linarith
    have hh : (0 : ℚ) < Fintype.card (Enc → D) := by
      have : Nonempty D := Fintype.card_pos_iff.mp hqpos
      exact_mod_cast Fintype.card_pos
    rw [probOf_real, probOf_ideal]
    have hkey : (∑ H : Enc → D, ∑ y : D, ind P H y * fib x H y)
          / (Fintype.card (Enc → D) * Fintype.card Salt)
        - (∑ H : Enc → D, ∑ y : D, ind P H y) / (Fintype.card (Enc → D) * Fintype.card D)
        = (∑ H : Enc → D, ∑ y : D,
            (ind P H y - 1 / 2) * ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt))
          / (Fintype.card (Enc → D) * Fintype.card Salt * Fintype.card D) := by
      rw [sum_centred]
      field_simp
    rw [hkey]
    have hCS : (∑ H : Enc → D, ∑ y : D,
            (ind P H y - 1 / 2) * ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt)) ^ 2
        ≤ (∑ H : Enc → D, ∑ y : D, (ind P H y - 1 / 2) ^ 2)
          * (∑ H : Enc → D, ∑ y : D,
              ((Fintype.card D : ℚ) * fib x H y - Fintype.card Salt) ^ 2) := by
      have := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ((Enc → D) × D))
        (fun p => ind P p.1 p.2 - 1 / 2)
        (fun p => (Fintype.card D : ℚ) * fib x p.1 p.2 - Fintype.card Salt)
      simpa only [Fintype.sum_prod_type] using this
    rw [sum_ind_sub_half_sq] at hCS
    have hB := sum_dev_sq_le (D := D) x hx
    apply abs_le_of_sq_le_sq _ hε
    rw [div_pow, div_le_iff₀ (by positivity)]
    have hA0 : (0 : ℚ) ≤ Fintype.card (Enc → D) * Fintype.card D / 4 := by positivity
    have hstep := le_trans hCS (mul_le_mul_of_nonneg_left hB hA0)
    have hpos : (0 : ℚ) ≤ (Fintype.card (Enc → D) : ℚ) ^ 2 * (Fintype.card D : ℚ) ^ 2
        * Fintype.card Salt := by positivity
    have hD' := mul_le_mul_of_nonneg_left hD hpos
    nlinarith

end LeafCount

/-! ## One leaf, post-processed -/

section Leaf

variable {Salt D Enc : Type} [Fintype Salt] [Fintype D] [Fintype Enc] [DecidableEq Enc]
  [DecidableEq D]

theorem leaf_statClose_map {V : Type} (x : Salt → Enc) (hx : Function.Injective x) {ε : ℚ}
    (hε : 0 ≤ ε) (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt)
    (Ψ : (Enc → D) → D → V) :
    StatClose ε (fun p : (Enc → D) × Salt => Ψ p.1 (p.1 (x p.2)))
      (fun p : (Enc → D) × D => Ψ p.1 p.2) := fun P =>
  leaf_statClose x hx hε hD (fun t => P (Ψ t.1 t.2))

/-- The one-leaf lemma with an unread coordinate on each side (the replaced leaf's fresh digest
on the real side, its nonce on the ideal side). -/
theorem leaf_statClose_pad {V : Type} [Nonempty Salt] [Nonempty D] (x : Salt → Enc)
    (hx : Function.Injective x) {ε : ℚ} (hε : 0 ≤ ε)
    (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt) (Ψ : (Enc → D) → D → V) :
    StatClose ε (fun p : ((Enc → D) × Salt) × D => Ψ p.1.1 (p.1.1 (x p.1.2)))
      (fun p : ((Enc → D) × D) × Salt => Ψ p.1.1 p.1.2) := by
  intro P
  have h1 := probOf_fst (Z := D) (fun q : (Enc → D) × Salt => Ψ q.1 (q.1 (x q.2))) P
  have h2 := probOf_fst (Z := Salt) (fun q : (Enc → D) × D => Ψ q.1 q.2) P
  rw [h1, h2]
  exact leaf_statClose_map x hx hε hD Ψ P

end Leaf

/-! ## All unopened leaves -/

section Leaves

variable {n : ℕ} {Salt D Enc V : Type}
variable (x : Fin n → Salt → Enc) (Q : Finset (Fin n))
variable (Φ : (Enc → D) → ({j // j ∈ Q} → Salt) → (Fin n → D) → V)

/-- **Hybrid `A`.**  The leaves in `A` get the fresh digests `u`, the others their hashes
`H (x j (r j))`; the experiment sees `H`, the nonces on `Q` and the digests. -/
def hyb (A : Finset (Fin n)) (ω : (Fin n → Salt) × (Enc → D) × (Fin n → D)) : V :=
  Φ ω.2.1 (fun j => ω.1 j.1) (fun j => if j ∈ A then ω.2.2 j else ω.2.1 (x j (ω.1 j)))

/-- Put coordinate `k` of the nonces and of the fresh digests aside, real side: the inner coins
are `((H, r k), u k)`. -/
def splitL (k : Fin n) :
    (({j // j ≠ k} → Salt) × ({j // j ≠ k} → D)) × (((Enc → D) × Salt) × D)
      ≃ (Fin n → Salt) × (Enc → D) × (Fin n → D) where
  toFun p := ((Equiv.funSplitAt k Salt).symm (p.2.1.2, p.1.1), p.2.1.1,
    (Equiv.funSplitAt k D).symm (p.2.2, p.1.2))
  invFun ω := ((((Equiv.funSplitAt k Salt) ω.1).2, ((Equiv.funSplitAt k D) ω.2.2).2),
    ((ω.2.1, ((Equiv.funSplitAt k Salt) ω.1).1), ((Equiv.funSplitAt k D) ω.2.2).1))
  left_inv p := by simp
  right_inv ω := by
    obtain ⟨r, H, u⟩ := ω
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]

/-- The same split, ideal side: the inner coins are `((H, u k), r k)`. -/
def splitR (k : Fin n) :
    (({j // j ≠ k} → Salt) × ({j // j ≠ k} → D)) × (((Enc → D) × D) × Salt)
      ≃ (Fin n → Salt) × (Enc → D) × (Fin n → D) where
  toFun p := ((Equiv.funSplitAt k Salt).symm (p.2.2, p.1.1), p.2.1.1,
    (Equiv.funSplitAt k D).symm (p.2.1.2, p.1.2))
  invFun ω := ((((Equiv.funSplitAt k Salt) ω.1).2, ((Equiv.funSplitAt k D) ω.2.2).2),
    ((ω.2.1, ((Equiv.funSplitAt k D) ω.2.2).1), ((Equiv.funSplitAt k Salt) ω.1).1))
  left_inv p := by simp
  right_inv ω := by
    obtain ⟨r, H, u⟩ := ω
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]

/-- The experiment at a hybrid step, as a function of the outer coins, `H` and leaf `k`'s
digest. -/
def stepView (A : Finset (Fin n)) (k : Fin n) (hkQ : k ∉ Q)
    (o : ({j // j ≠ k} → Salt) × ({j // j ≠ k} → D)) (H : Enc → D) (z : D) : V :=
  Φ H (fun j => o.1 ⟨j.1, fun h : j.1 = k => hkQ (h ▸ j.2)⟩)
    (fun j => if h : j = k then z else if j ∈ A then o.2 ⟨j, h⟩ else H (x j (o.1 ⟨j, h⟩)))

theorem hyb_splitL (A : Finset (Fin n)) (k : Fin n) (hkA : k ∉ A) (hkQ : k ∉ Q)
    (o : ({j // j ≠ k} → Salt) × ({j // j ≠ k} → D)) (H : Enc → D) (s : Salt) (y : D) :
    hyb x Q Φ A (splitL k (o, ((H, s), y))) = stepView x Q Φ A k hkQ o H (H (x k s)) := by
  simp only [hyb, splitL, stepView, Equiv.coe_fn_mk, Equiv.funSplitAt_symm_apply]
  congr 1
  · funext j
    rw [dif_neg (fun h : j.1 = k => hkQ (h ▸ j.2))]
  · funext j
    by_cases h : j = k
    · subst h
      simp [hkA]
    · simp [h]

theorem hyb_splitR (A : Finset (Fin n)) (k : Fin n) (hkQ : k ∉ Q)
    (o : ({j // j ≠ k} → Salt) × ({j // j ≠ k} → D)) (H : Enc → D) (y : D) (s : Salt) :
    hyb x Q Φ (insert k A) (splitR k (o, ((H, y), s))) = stepView x Q Φ A k hkQ o H y := by
  simp only [hyb, splitR, stepView, Equiv.coe_fn_mk, Equiv.funSplitAt_symm_apply]
  congr 1
  · funext j
    rw [dif_neg (fun h : j.1 = k => hkQ (h ▸ j.2))]
  · funext j
    by_cases h : j = k
    · subst h
      simp
    · simp [h, Finset.mem_insert]

variable [Fintype Salt] [Fintype D] [Fintype Enc] [DecidableEq Enc] [DecidableEq D]
variable [Nonempty Salt] [Nonempty D]

/-- **One hybrid step**: replacing one more unopened leaf's digest costs `ε`. -/
theorem hyb_step (hx : ∀ j, Function.Injective (x j)) {ε : ℚ} (hε : 0 ≤ ε)
    (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt) (A : Finset (Fin n))
    (k : Fin n) (hkA : k ∉ A) (hkQ : k ∉ Q) :
    StatClose ε (hyb x Q Φ A) (hyb x Q Φ (insert k A)) := by
  have h : StatClose ε (fun p => hyb x Q Φ A (splitL k p))
      (fun p => hyb x Q Φ (insert k A) (splitR k p)) := by
    refine statClose_mix hε (fun o z => hyb x Q Φ A (splitL k (o, z)))
      (fun o z => hyb x Q Φ (insert k A) (splitR k (o, z))) fun o => ?_
    have e1 : (fun z : ((Enc → D) × Salt) × D => hyb x Q Φ A (splitL k (o, z)))
        = fun z => stepView x Q Φ A k hkQ o z.1.1 (z.1.1 (x k z.1.2)) :=
      funext fun z => hyb_splitL x Q Φ A k hkA hkQ o z.1.1 z.1.2 z.2
    have e2 : (fun z : ((Enc → D) × D) × Salt => hyb x Q Φ (insert k A) (splitR k (o, z)))
        = fun z => stepView x Q Φ A k hkQ o z.1.1 z.1.2 :=
      funext fun z => hyb_splitR x Q Φ A k hkQ o z.1.1 z.1.2 z.2
    rw [e1, e2]
    exact leaf_statClose_pad (x k) (hx k) hε hD (stepView x Q Φ A k hkQ o)
  exact statClose_reindex (splitL k).symm (splitR k).symm (fun ω => by simp)
    (fun ω => by simp) h

/-- **The hybrid chain**: replacing the digests of a set `A` of unopened leaves costs
`|A| · ε`. -/
theorem hyb_chain (hx : ∀ j, Function.Injective (x j)) {ε : ℚ} (hε : 0 ≤ ε)
    (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt) (A : Finset (Fin n))
    (hA : Disjoint A Q) :
    StatClose (A.card * ε) (hyb x Q Φ ∅) (hyb x Q Φ A) := by
  induction A using Finset.induction_on with
  | empty =>
      intro P
      simp
  | insert k A hkA ih =>
      have hkQ : k ∉ Q := Finset.disjoint_left.mp hA (Finset.mem_insert_self k A)
      have h := (ih (Finset.disjoint_of_subset_left (Finset.subset_insert k A) hA)).trans
        (hyb_step x Q Φ hx hε hD A k hkA hkQ)
      refine h.mono (le_of_eq ?_)
      rw [Finset.card_insert_of_notMem hkA]
      push_cast
      ring

/--
**All unopened leaves.**  The experiment that sees `H`, the opened nonces and every leaf digest
`H (x j (r j))` is `|Qᶜ| · ε`-close to the one where the unopened leaves' digests are fresh and
uniform.
-/
theorem digests_statClose (hx : ∀ j, Function.Injective (x j)) {ε : ℚ} (hε : 0 ≤ ε)
    (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt) :
    StatClose ((Finset.univ \ Q).card * ε)
      (fun p : (Fin n → Salt) × (Enc → D) =>
        Φ p.2 (fun j => p.1 j.1) (fun j => p.2 (x j (p.1 j))))
      (fun p : (Fin n → Salt) × (Enc → D) × (Fin n → D) =>
        Φ p.2.1 (fun j => p.1 j.1) (fun j => if j ∈ Q then p.2.1 (x j (p.1 j)) else p.2.2 j)) := by
  have h0 : StatClose 0
      (fun p : (Fin n → Salt) × (Enc → D) =>
        Φ p.2 (fun j => p.1 j.1) (fun j => p.2 (x j (p.1 j))))
      (hyb x Q Φ ∅) := by
    intro P
    have hfst := probOf_fst (Z := Fin n → D)
      (fun p : (Fin n → Salt) × (Enc → D) =>
        Φ p.2 (fun j => p.1 j.1) (fun j => p.2 (x j (p.1 j)))) P
    have heq := probOf_equiv (Equiv.prodAssoc (Fin n → Salt) (Enc → D) (Fin n → D)).symm
      (fun q : ((Fin n → Salt) × (Enc → D)) × (Fin n → D) =>
        Φ q.1.2 (fun j => q.1.1 j.1) (fun j => q.1.2 (x j (q.1.1 j)))) P
    have hhyb : (hyb x Q Φ ∅) = fun ω =>
        (fun q : ((Fin n → Salt) × (Enc → D)) × (Fin n → D) =>
          Φ q.1.2 (fun j => q.1.1 j.1) (fun j => q.1.2 (x j (q.1.1 j))))
          ((Equiv.prodAssoc (Fin n → Salt) (Enc → D) (Fin n → D)).symm ω) := by
      funext ω
      simp [hyb]
    rw [hhyb, heq, hfst, sub_self, abs_zero]
  have hchain := hyb_chain x Q Φ hx hε hD (Finset.univ \ Q) Finset.sdiff_disjoint
  have hlast : hyb x Q Φ (Finset.univ \ Q) = fun p : (Fin n → Salt) × (Enc → D) × (Fin n → D) =>
      Φ p.2.1 (fun j => p.1 j.1) (fun j => if j ∈ Q then p.2.1 (x j (p.1 j)) else p.2.2 j) := by
    funext p
    simp only [hyb]
    congr 1
    funext j
    by_cases h : j ∈ Q <;> simp [h]
  rw [hlast] at hchain
  simpa using h0.trans hchain

end Leaves

/-! ## The Merkle view from the leaf digests -/

section View

variable {Salt M D Enc : Type} [Inhabited D]

/-- **The heap labels from the leaf digests `y`**: `commitLabels`' recurrence with the leaves
given; internal nodes are hashed by `H`. -/
def digestLabels (Cod : Codec Salt M D Enc) (H : Enc → D) (n : ℕ) (y : Fin n → D) (v : ℕ) : D :=
  if hleaf : n ≤ v ∧ v < 2 * n then y ⟨v - n, by omega⟩
  else if hint : 0 < v ∧ v < n then
    H (Cod.nodeEnc (digestLabels Cod H n y (2 * v), digestLabels Cod H n y (2 * v + 1)))
  else default
termination_by 2 * n - v
decreasing_by all_goals omega

/-- Every honest label is the label computed from the honest leaf digests. -/
theorem commitLabels_eq_digestLabels (Cod : Codec Salt M D Enc) (H : Enc → D) (n : ℕ)
    (nonce : Fin n → Salt) (m : Fin n → M) (v : ℕ) :
    commitLabels (Cod.withOracle H) n nonce m v
      = digestLabels Cod H n (fun j => H (Cod.leafEnc (nonce j, m j))) v := by
  rw [commitLabels, digestLabels]
  split_ifs with h1 h2
  · rfl
  · change H (Cod.nodeEnc (commitLabels (Cod.withOracle H) n nonce m (2 * v),
        commitLabels (Cod.withOracle H) n nonce m (2 * v + 1))) = _
    rw [commitLabels_eq_digestLabels Cod H n nonce m (2 * v),
      commitLabels_eq_digestLabels Cod H n nonce m (2 * v + 1)]
  · rfl
termination_by 2 * n - v
decreasing_by all_goals omega

/-- **The Merkle view from the leaf digests**: the root, the opened nonces and the frontier
labels. -/
def digestView (Cod : Codec Salt M D Enc) (H : Enc → D) (n : ℕ) (I : Finset (Fin n))
    (nonceI : {j // j ∈ I} → Salt) (y : Fin n → D) : OpeningView n I Salt D :=
  ⟨digestLabels Cod H n y 1, ⟨nonceI, fun v => digestLabels Cod H n y v.1⟩⟩

/-- The honest view is the view of the honest leaf digests. -/
theorem view_eq_digestView (Cod : Codec Salt M D Enc) (H : Enc → D) (n : ℕ) (I : Finset (Fin n))
    (nonce : Fin n → Salt) (m : Fin n → M) :
    (⟨MH.root (Cod.withOracle H) n nonce m, MH.openCore (Cod.withOracle H) n I nonce m⟩ :
        OpeningView n I Salt D)
      = digestView Cod H n I (fun j => nonce j.1) (fun j => H (Cod.leafEnc (nonce j, m j))) := by
  simp only [digestView, MH.root, MH.openCore, commitLabels_eq_digestLabels]

end View

/-! ## The Merkle view -/

/--
**Statistical hiding of the salted Merkle commitment, against a full view of the oracle.**

Commit to `m` under uniform nonces and a uniform oracle `H`, and open `I`.  Every experiment `Φ`
that receives `H` itself and the view (root, opened nonces, frontier digests) is
`|Iᶜ| · ε`-close to the same experiment on the view computed from fresh uniform digests `u` for the
unopened leaves — a view that reads `m` only on `I` — whenever `|D| ≤ 4 · ε² · |Salt|`.
-/
theorem view_statClose {n : ℕ} {Salt M D Enc V : Type} [Fintype Salt] [Fintype D] [Fintype Enc]
    [DecidableEq Enc] [DecidableEq D] [Inhabited D] [Nonempty Salt] (Cod : Codec Salt M D Enc)
    (hleaf : Function.Injective Cod.leafEnc) (m : Fin n → M) (I : Finset (Fin n)) {ε : ℚ}
    (hε : 0 ≤ ε) (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt)
    (Φ : (Enc → D) → OpeningView n I Salt D → V) :
    StatClose ((Finset.univ \ I).card * ε)
      (fun p : (Fin n → Salt) × (Enc → D) =>
        Φ p.2 ⟨MH.root (Cod.withOracle p.2) n p.1 m, MH.openCore (Cod.withOracle p.2) n I p.1 m⟩)
      (fun p : (Fin n → Salt) × (Enc → D) × (Fin n → D) =>
        Φ p.2.1 (digestView Cod p.2.1 n I (fun j => p.1 j.1)
          (fun j => if j ∈ I then p.2.1 (Cod.leafEnc (p.1 j, m j)) else p.2.2 j))) := by
  have h := digests_statClose (fun j s => Cod.leafEnc (s, m j)) I
    (fun H rI y => Φ H (digestView Cod H n I rI y))
    (fun j a b hab => congrArg Prod.fst (hleaf hab)) hε hD
  have e : (fun p : (Fin n → Salt) × (Enc → D) =>
      Φ p.2 ⟨MH.root (Cod.withOracle p.2) n p.1 m, MH.openCore (Cod.withOracle p.2) n I p.1 m⟩)
      = fun p => Φ p.2 (digestView Cod p.2 n I (fun j => p.1 j.1)
          (fun j => p.2 (Cod.leafEnc (p.1 j, m j)))) :=
    funext fun p => by rw [view_eq_digestView]
  rw [e]
  exact h

end Lfzk.ZkMerkleStat
