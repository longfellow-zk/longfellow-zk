import Mathlib

/-!
# Weighted finite-decoder balance for graded transcript charges

Longfellow's random oracle returns an encoded answer.  A role decoder maps
it to a field challenge or a column query.  The existing balance condition
bounds each fiber's cardinality.  This lemma transports a nonnegative
rational positive-increase charge through that decoder without replacing it
by a worst-case Boolean event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkPotentialBalance

open Finset
open scoped Classical

/-- A balanced decoder's fiber count can be removed from a nonnegative
clipped local budget, even when the un-clipped rational expression has an
unknown sign.  This gives a context-independent hash-answer budget. -/
theorem max_zero_nat_mul_le
    {a b : ℕ} (hab : a ≤ b) (x : ℚ) :
    max 0 ((a : ℚ) * x) ≤ max 0 ((b : ℚ) * x) := by
  apply max_le
  · exact le_max_left _ _
  · by_cases hx : 0 ≤ x
    · exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hx).trans
        (le_max_right _ _)
    · have hax : (a : ℚ) * x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_ge hx)
      exact hax.trans (le_max_left _ _)

theorem decoded_weight_sum_le
    {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (decode : C → X) (weight : X → ℚ)
    (hnonneg : ∀ x, 0 ≤ weight x)
    (k : ℕ)
    (hbalance : ∀ x,
      (univ.filter fun c : C => decode c = x).card ≤ k) :
    ∑ c : C, weight (decode c) ≤ k * ∑ x : X, weight x := by
  classical
  have hfiber (x : X) :
      (∑ c : C, if decode c = x then weight x else 0) =
        ((univ.filter fun c : C => decode c = x).card : ℚ) * weight x := by
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ c : C, weight (decode c)) =
        ∑ c : C, ∑ x : X, if decode c = x then weight x else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          simp
    _ = ∑ x : X, ∑ c : C,
          if decode c = x then weight x else 0 := Finset.sum_comm
    _ = ∑ x : X,
          ((univ.filter fun c : C => decode c = x).card : ℚ) * weight x := by
          apply Finset.sum_congr rfl
          intro x _
          exact hfiber x
    _ ≤ ∑ x : X, (k : ℚ) * weight x := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hbalance x) (hnonneg x)
    _ = k * ∑ x : X, weight x := by rw [Finset.mul_sum]

/-- Convert a uniform challenge expectation into the exact local hash-answer
budget, retaining the decoder's fiber factor. -/
theorem decoded_mean_le
    {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X] [Nonempty X]
    (decode : C → X) (weight : X → ℚ)
    (hnonneg : ∀ x, 0 ≤ weight x)
    (k : ℕ)
    (hbalance : ∀ x,
      (univ.filter fun c : C => decode c = x).card ≤ k)
    (bound : ℚ)
    (hmean : (∑ x : X, weight x) / Fintype.card X ≤ bound) :
    ∑ c : C, weight (decode c) ≤
      k * Fintype.card X * bound := by
  have hx : (0 : ℚ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ x : X, weight x) ≤ Fintype.card X * bound := by
    simpa only [mul_comm] using (div_le_iff₀ hx).mp hmean
  calc
    (∑ c : C, weight (decode c)) ≤
        k * ∑ x : X, weight x :=
          decoded_weight_sum_le decode weight hnonneg k hbalance
    _ ≤ k * (Fintype.card X * bound) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = k * Fintype.card X * bound := by ring

/-- The same transfer for the residual query charge after a fixed
combination challenge.  A response may be chosen after that challenge. -/
theorem decoded_query_charge_le
    {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (decode : C → Q) (accepts : Q → Prop) [DecidablePred accepts]
    (remaining : ℚ) (hremaining : 0 ≤ remaining)
    (k : ℕ)
    (hbalance : ∀ q,
      (univ.filter fun c : C => decode c = q).card ≤ k)
    (cost : ℚ)
    (hcost : remaining *
      (((univ.filter accepts).card : ℚ) / Fintype.card Q) ≤ cost) :
    ∑ c : C, (if accepts (decode c) then remaining else 0) ≤
      k * Fintype.card Q * cost := by
  have hmean : (∑ q : Q, if accepts q then remaining else 0) /
      Fintype.card Q ≤ cost := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    convert hcost using 1
    ring
  exact decoded_mean_le decode
    (fun q => if accepts q then remaining else 0)
    (by intro q; split <;> positivity)
    k hbalance cost hmean

/-- Keep the final challenge and query as a pair.  Applying decoder balance
to each coordinate preserves the joint acceptance mass, with precisely the
product of the two fiber bounds and no response-list factor. -/
theorem decoded_pair_weight_sum_le
    {C Challenge Query : Type*}
    [Fintype C] [Fintype Challenge] [DecidableEq Challenge]
    [Fintype Query] [DecidableEq Query]
    (decodeChallenge : C → Challenge) (decodeQuery : C → Query)
    (weight : Challenge → Query → ℚ)
    (hnonneg : ∀ challenge query, 0 ≤ weight challenge query)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : C => decodeChallenge c = challenge).card ≤ kchal)
    (hquery : ∀ query,
      (univ.filter fun c : C => decodeQuery c = query).card ≤ kquery) :
    (∑ c : C, ∑ d : C, weight (decodeChallenge c) (decodeQuery d)) ≤
      (kchal * kquery : ℚ) *
        ∑ challenge : Challenge, ∑ query : Query, weight challenge query := by
  have hinner (c : C) :
      (∑ d : C, weight (decodeChallenge c) (decodeQuery d)) ≤
        kquery * ∑ query : Query, weight (decodeChallenge c) query :=
    decoded_weight_sum_le decodeQuery (weight (decodeChallenge c))
      (hnonneg (decodeChallenge c)) kquery hquery
  have houter :
      (∑ c : C, ∑ query : Query, weight (decodeChallenge c) query) ≤
        kchal * ∑ challenge : Challenge, ∑ query : Query,
          weight challenge query :=
    decoded_weight_sum_le decodeChallenge
      (fun challenge => ∑ query : Query, weight challenge query)
      (fun challenge => Finset.sum_nonneg fun query _ => hnonneg challenge query)
      kchal hchal
  calc
    (∑ c : C, ∑ d : C, weight (decodeChallenge c) (decodeQuery d))
        ≤ ∑ c : C, kquery * ∑ query : Query,
            weight (decodeChallenge c) query :=
          Finset.sum_le_sum fun c _ => hinner c
    _ = kquery * ∑ c : C, ∑ query : Query,
          weight (decodeChallenge c) query := by rw [Finset.mul_sum]
    _ ≤ kquery * (kchal * ∑ challenge : Challenge, ∑ query : Query,
          weight challenge query) :=
          mul_le_mul_of_nonneg_left houter (Nat.cast_nonneg _)
    _ = (kchal * kquery : ℚ) *
          ∑ challenge : Challenge, ∑ query : Query,
            weight challenge query := by ring

/-- Cardinality form of the joint decoder-balance inequality. -/
theorem decoded_pair_card_le
    {C Challenge Query : Type*}
    [Fintype C] [Fintype Challenge] [DecidableEq Challenge]
    [Fintype Query] [DecidableEq Query]
    (decodeChallenge : C → Challenge) (decodeQuery : C → Query)
    (accepts : Challenge → Query → Prop)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : C => decodeChallenge c = challenge).card ≤ kchal)
    (hquery : ∀ query,
      (univ.filter fun c : C => decodeQuery c = query).card ≤ kquery) :
    ((univ.filter fun p : C × C =>
        accepts (decodeChallenge p.1) (decodeQuery p.2)).card : ℚ) ≤
      (kchal * kquery : ℚ) *
        (univ.filter fun p : Challenge × Query => accepts p.1 p.2).card := by
  classical
  have h := decoded_pair_weight_sum_le decodeChallenge decodeQuery
    (fun challenge query => if accepts challenge query then 1 else 0)
    (by intro challenge query; split <;> positivity)
    kchal kquery hchal hquery
  simpa only [Finset.card_filter, Fintype.sum_prod_type, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using h

/-- A response may depend on the *raw* first hash answer, not merely on the
decoded combination challenge.  A response-uniform IOP envelope still bounds
the joint decoded challenge/query hash pair, without counting possible
responses. -/
theorem decoded_pair_ratio_le_uniform
    {C Challenge Query Response : Type*}
    [Fintype C] [Nonempty C]
    [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
    [Fintype Query] [DecidableEq Query] [Nonempty Query]
    (decodeChallenge : C → Challenge) (decodeQuery : C → Query)
    (respond : C → Response)
    (accepts : Challenge → Response → Query → Prop)
    (envelope : Challenge → ℚ)
    (henv_nonneg : ∀ challenge, 0 ≤ envelope challenge)
    (hquery : ∀ challenge response,
      ((univ.filter fun query : Query =>
        accepts challenge response query).card : ℚ) /
          Fintype.card Query ≤ envelope challenge)
    (epsilon : ℚ)
    (hmean : (∑ challenge : Challenge, envelope challenge) /
      Fintype.card Challenge ≤ epsilon)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : C => decodeChallenge c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : C => decodeQuery c = query).card ≤ kquery) :
    ((univ.filter fun p : C × C =>
      accepts (decodeChallenge p.1) (respond p.1) (decodeQuery p.2)).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2 ≤
      ((kchal * kquery : ℚ) * Fintype.card Challenge *
        Fintype.card Query / (Fintype.card C : ℚ) ^ 2) * epsilon := by
  classical
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hQ : (0 : ℚ) < Fintype.card Query := by exact_mod_cast Fintype.card_pos
  have hX : (0 : ℚ) < Fintype.card Challenge := by exact_mod_cast Fintype.card_pos
  have hq (c : C) :
      ((univ.filter fun d : C =>
        accepts (decodeChallenge c) (respond c) (decodeQuery d)).card : ℚ) ≤
        kquery * Fintype.card Query * envelope (decodeChallenge c) := by
    have hdecoded := decoded_weight_sum_le decodeQuery
      (fun query => if accepts (decodeChallenge c) (respond c) query then
        (1 : ℚ) else 0)
      (by intro query; split <;> positivity) kquery hqueryBalance
    have hbound := (div_le_iff₀ hQ).mp
      (hquery (decodeChallenge c) (respond c))
    have hbound' :
        ((univ.filter fun query : Query =>
          accepts (decodeChallenge c) (respond c) query).card : ℚ) ≤
          Fintype.card Query * envelope (decodeChallenge c) := by
      simpa only [mul_comm] using hbound
    calc
      ((univ.filter fun d : C =>
        accepts (decodeChallenge c) (respond c) (decodeQuery d)).card : ℚ) =
          ∑ d : C, if accepts (decodeChallenge c) (respond c)
            (decodeQuery d) then (1 : ℚ) else 0 := by
              simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
                Nat.cast_one, Nat.cast_zero]
      _ ≤ kquery * ∑ query : Query,
          if accepts (decodeChallenge c) (respond c) query then
            (1 : ℚ) else 0 := hdecoded
      _ = kquery * ((univ.filter fun query : Query =>
          accepts (decodeChallenge c) (respond c) query).card : ℚ) := by
            simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
              Nat.cast_one, Nat.cast_zero]
      _ ≤ kquery * (Fintype.card Query *
          envelope (decodeChallenge c)) :=
            mul_le_mul_of_nonneg_left hbound' (Nat.cast_nonneg _)
      _ = kquery * Fintype.card Query * envelope (decodeChallenge c) := by ring
  have hXsum :
      (∑ challenge : Challenge, envelope challenge) ≤
        Fintype.card Challenge * epsilon := by
    simpa only [mul_comm] using (div_le_iff₀ hX).mp hmean
  have hdecodedChal := decoded_weight_sum_le decodeChallenge envelope
    henv_nonneg kchal hchal
  have hnum :
      ((univ.filter fun p : C × C =>
        accepts (decodeChallenge p.1) (respond p.1) (decodeQuery p.2)).card : ℚ) ≤
        ((kchal * kquery : ℚ) * Fintype.card Challenge *
          Fintype.card Query) * epsilon := by
    calc
      ((univ.filter fun p : C × C =>
        accepts (decodeChallenge p.1) (respond p.1) (decodeQuery p.2)).card : ℚ) =
          ∑ c : C, ((univ.filter fun d : C =>
            accepts (decodeChallenge c) (respond c) (decodeQuery d)).card : ℚ) := by
              simp only [Finset.card_filter, Fintype.sum_prod_type, Nat.cast_sum]
      _ ≤ ∑ c : C, kquery * Fintype.card Query *
          envelope (decodeChallenge c) :=
            Finset.sum_le_sum fun c _ => hq c
      _ = (kquery * Fintype.card Query : ℚ) *
          ∑ c : C, envelope (decodeChallenge c) := by rw [Finset.mul_sum]
      _ ≤ (kquery * Fintype.card Query : ℚ) *
          (kchal * ∑ challenge : Challenge, envelope challenge) :=
            mul_le_mul_of_nonneg_left hdecodedChal (by positivity)
      _ ≤ (kquery * Fintype.card Query : ℚ) *
          (kchal * (Fintype.card Challenge * epsilon)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hXsum (Nat.cast_nonneg _)
      _ = ((kchal * kquery : ℚ) * Fintype.card Challenge *
          Fintype.card Query) * epsilon := by ring
  have hpow : (0 : ℚ) < (Fintype.card C : ℚ) ^ 2 := pow_pos hC _
  have hscaled := div_le_div_of_nonneg_right hnum hpow.le
  calc
    ((univ.filter fun p : C × C =>
      accepts (decodeChallenge p.1) (respond p.1) (decodeQuery p.2)).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2 ≤
      (((kchal * kquery : ℚ) * Fintype.card Challenge *
        Fintype.card Query) * epsilon) /
          (Fintype.card C : ℚ) ^ 2 := hscaled
    _ = ((kchal * kquery : ℚ) * Fintype.card Challenge *
        Fintype.card Query / (Fintype.card C : ℚ) ^ 2) * epsilon := by ring

/-- Exact decoder coverage on each of the two terminal answers makes the
raw-hash-pair multiplicity factor at most one. -/
theorem decoder_pair_factor_le_one
    {C Challenge Query : Type*}
    [Fintype C] [Nonempty C] [Fintype Challenge] [Fintype Query]
    (kchal kquery : ℕ)
    (hchal : kchal * Fintype.card Challenge ≤ Fintype.card C)
    (hquery : kquery * Fintype.card Query ≤ Fintype.card C) :
    ((kchal * kquery : ℚ) * Fintype.card Challenge *
      Fintype.card Query / (Fintype.card C : ℚ) ^ 2) ≤ 1 := by
  have hprod :
      (kchal * Fintype.card Challenge) *
        (kquery * Fintype.card Query) ≤ (Fintype.card C) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hchal hquery
  have hq : ((kchal * Fintype.card Challenge : ℕ) : ℚ) *
      ((kquery * Fintype.card Query : ℕ) : ℚ) ≤
        (Fintype.card C : ℚ) ^ 2 := by
    exact_mod_cast hprod
  have hC : (0 : ℚ) < Fintype.card C := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ (pow_pos hC 2)).mpr
  have heq : (kchal * kquery : ℚ) * Fintype.card Challenge *
      Fintype.card Query =
        ((kchal * Fintype.card Challenge : ℕ) : ℚ) *
          ((kquery * Fintype.card Query : ℕ) : ℚ) := by
    push_cast
    ring
  simpa only [one_mul, heq] using hq

end Lfzk.ZkPotentialBalance
