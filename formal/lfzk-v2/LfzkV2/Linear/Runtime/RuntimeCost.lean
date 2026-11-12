import LfzkV2.Linear.Runtime.Cost
import LfzkV2.Packed.RuntimeProfiles

/-! Current packed runtime costs. These are bounds on the charges in the
actual two-field extraction theorem, with the degree-one signature path
contributing no packing challenge. -/

namespace LfzkV2.Linear.Runtime

open Finset RecursivePolygero

namespace CompiledSide

variable {F C Context : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input : ℕ} {circuit : Native.Circuit F out input} {I : Instance F}

/-- Bind the analysis-side list size and terminal budgets to a certified
profile. The two budget equalities are reflexive for the profile potential;
they also permit any equivalent terminal potential. -/
structure Profiled (S : CompiledSide F C Context circuit I) (p : LfzkV2.RuntimeProfiles.Profile) where
  geometry : LfzkV2.RuntimeProfiles.Geometry p I
  sampling : LfzkV2.RuntimeProfiles.BackendSampling I S.decodeCoin S.decodeQuery
  cutoff_eq : S.cutoff = p.cutoff
  bound_eq : S.bound = p.candidates
  challenge_eq : S.potential.challengeBudget =
    (p.potential I geometry.n geometry.k geometry.s geometry.t S.decodeCoin S.decodeQuery
      sampling.kCoin sampling.kQuery sampling.coin_bound sampling.query_bound).challengeBudget
  query_eq : S.potential.queryBudget =
    (p.potential I geometry.n geometry.k geometry.s geometry.t S.decodeCoin S.decodeQuery
      sampling.kCoin sampling.kQuery sampling.coin_bound sampling.query_bound).queryBudget

theorem Profiled.budgets_le [Nonempty C] {S : CompiledSide F C Context circuit I}
    {p : LfzkV2.RuntimeProfiles.Profile} (cert : S.Profiled p)
    (hfield : p.minimumField ≤ Fintype.card F) :
    S.potential.challengeBudget/Fintype.card C ≤ (p.capacities+1 : ℕ)/(p.minimumField : ℚ) ∧
      S.potential.queryBudget/Fintype.card C ≤ p.queryUnits/(2^128 : ℚ) := by
  rw [cert.challenge_eq,cert.query_eq]
  exact p.potential_budgets_le I cert.geometry.n cert.geometry.k cert.geometry.s cert.geometry.t
    (by simpa only [Nat.card_eq_fintype_card] using hfield) S.decodeCoin S.decodeQuery
    cert.sampling.kCoin cert.sampling.kQuery cert.sampling.coin_bound cert.sampling.query_bound
    cert.sampling.coin_balanced cert.sampling.query_balanced

end CompiledSide

namespace RuntimeCost

open TwoFieldReplay LfzkV2.Packed.RuntimeProfiles

def coefficient : ℚ := 925/(2^128 : ℚ)
def constant : ℚ := 19303/(2^128 : ℚ)+21661/(2^255 : ℚ)

theorem coefficient_lt_117 : coefficient < 1/(2^117 : ℚ) := by norm_num [coefficient]

private theorem div_nat_le {a b q q₀ : ℕ} (hq₀ : 0 < q₀) (hab : a ≤ b) (hq : q₀ ≤ q) :
    (a : ℚ)/q ≤ (b : ℚ)/q₀ := by
  have hqpos : (0 : ℚ) < q₀ := by exact_mod_cast hq₀
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hab) (Nat.cast_nonneg q)).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg b) hqpos (by exact_mod_cast hq))

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C] [Nonempty C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C S₁.Selected circuit₂ I₂)
variable (cert₁ : S₁.Profiled Hash.profile) (cert₂ : S₂.Profiled Signature.profile)

include cert₁ cert₂

theorem terminal_rates (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂) :
    (S₁.potential.challengeBudget/Fintype.card C ≤ 244/(2^128 : ℚ) ∧
      S₁.potential.queryBudget/Fintype.card C ≤ 925/(2^128 : ℚ)) ∧
    (S₂.potential.challengeBudget/Fintype.card C ≤ 244/(2^255 : ℚ) ∧
      S₂.potential.queryBudget/Fintype.card C ≤ 459/(2^128 : ℚ)) :=
  ⟨cert₁.budgets_le hfield₁,cert₂.budgets_le hfield₂⟩

variable (hpacked₁ : S₁.packed = true) (hpacked₂ : S₂.packed = false)
variable (hpacking : S₁.packingBudget = (S₁.sampling.fieldFiber : ℚ)*S₁.bound)

include hpacked₁ hpacked₂ hpacking

omit [Field Fmac] [DecidableEq Fmac] in
theorem coefficient_le (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂)
    (hmac : 2^128 ≤ Fintype.card Fmac) (hout₁ : out₁ ≤ 5) (hout₂ : out₂ ≤ 3) :
    TwoFieldFS.coefficient (Fmac := Fmac) S₁ S₂ ≤ coefficient := by
  obtain ⟨h₁,h₂⟩ := terminal_rates S₁ S₂ cert₁ cert₂ hfield₁ hfield₂
  have hb₁ : S₁.bound = 25 := cert₁.bound_eq
  have hb₂ : S₂.bound = 33 := cert₂.bound_eq
  have hm : (25 : ℚ)*33/Fintype.card Fmac ≤ 825/(2^128 : ℚ) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,show (25 : ℚ)*33 = 825 by norm_num] using
      (div_nat_le (a := 825) (b := 825) (q₀ := 2^128) (by decide) le_rfl hmac)
  have hf₁ : (25 : ℚ)*max out₁ 2/Fintype.card F₁ ≤ 125/(2^128 : ℚ) := by
    have h := div_nat_le (by decide : 0 < 2^128) (by omega : 25*max out₁ 2 ≤ 125) hfield₁
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h
  have hf₂ : (33 : ℚ)*max out₂ 2/Fintype.card F₂ ≤ 99/(2^255 : ℚ) := by
    have h := div_nat_le (by decide : 0 < 2^255) (by omega : 33*max out₂ 2 ≤ 99) hfield₂
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h
  have hp : (25 : ℚ)/Fintype.card F₁ ≤ 25/(2^128 : ℚ) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      (div_nat_le (a := 25) (b := 25) (q₀ := 2^128) (by decide) le_rfl hfield₁)
  have ht₁ : (25 : ℚ)*(2/((Fintype.card F₁-1 : ℕ) : ℚ)) ≤ 100/(2^128 : ℚ) := by
    have h := div_nat_le (a := 50) (b := 50) (q₀ := 2^128-1) (by decide) le_rfl
      (Nat.sub_le_sub_right hfield₁ 1)
    have he : (25 : ℚ)*(2/((Fintype.card F₁-1 : ℕ) : ℚ)) = 50/((Fintype.card F₁-1 : ℕ) : ℚ) := by ring
    rw [he]
    exact h.trans (by norm_num)
  have ht₂ : (33 : ℚ)*(2/((Fintype.card F₂-1 : ℕ) : ℚ)) ≤ 132/(2^255 : ℚ) := by
    have h := div_nat_le (a := 66) (b := 66) (q₀ := 2^255-1) (by decide) le_rfl
      (Nat.sub_le_sub_right hfield₂ 1)
    have he : (33 : ℚ)*(2/((Fintype.card F₂-1 : ℕ) : ℚ)) = 66/((Fintype.card F₂-1 : ℕ) : ℚ) := by ring
    rw [he]
    exact h.trans (by norm_num)
  unfold TwoFieldFS.coefficient TwoFieldFS.macCost CompiledSide.coefficient
  rw [S₁.packingRate_eq hpacked₁ hpacking, S₂.direct_packingRate hpacked₂, hb₁,hb₂]
  norm_num only [Nat.cast_ofNat]
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 25),
    mul_max_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 33)]
  simp only [mul_div_assoc] at hf₁ hf₂
  norm_num only [show (25 : ℚ)*33 = 825 by norm_num] at hm
  simp only [max_le_iff]
  repeat' apply And.intro
  all_goals first
    | exact hm.trans (by norm_num [coefficient])
    | exact hf₁.trans (by norm_num [coefficient])
    | exact hf₂.trans (by norm_num [coefficient])
    | exact ht₁.trans (by norm_num [coefficient])
    | exact ht₂.trans (by norm_num [coefficient])
    | exact hp.trans (by norm_num [coefficient])
    | exact h₁.1.trans (by norm_num [coefficient])
    | exact h₁.2.trans (by norm_num [coefficient])
    | exact h₂.1.trans (by norm_num [coefficient])
    | exact h₂.2.trans (by norm_num [coefficient])
    | norm_num [coefficient]

omit [Field Fmac] [DecidableEq Fmac] in
theorem constant_le (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂)
    (hmac : 2^128 ≤ Fintype.card Fmac)
    (hfront₁ : out₁+circuit₁.sharpLayerBudget ≤ 593) (hfront₂ : out₂+circuit₂.sharpLayerBudget ≤ 565)
    (hlayers₁ : circuit₁.layers ≤ 20) (hlayers₂ : circuit₂.layers ≤ 21) :
    TwoFieldFS.constant (Fmac := Fmac) S₁ S₂ ≤ constant := by
  obtain ⟨h₁,h₂⟩ := terminal_rates S₁ S₂ cert₁ cert₂ hfield₁ hfield₂
  have hb₁ : S₁.bound = 25 := cert₁.bound_eq
  have hb₂ : S₂.bound = 33 := cert₂.bound_eq
  have hm : (25 : ℚ)*33/Fintype.card Fmac ≤ 825/(2^128 : ℚ) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,show (25 : ℚ)*33 = 825 by norm_num] using
      (div_nat_le (a := 825) (b := 825) (q₀ := 2^128) (by decide) le_rfl hmac)
  have hf₁ : (25 : ℚ)*(out₁+circuit₁.sharpLayerBudget)/Fintype.card F₁ ≤ 14825/(2^128 : ℚ) := by
    have h := div_nat_le (by decide : 0 < 2^128)
      (by omega : 25*(out₁+circuit₁.sharpLayerBudget) ≤ 14825) hfield₁
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using h
  have hf₂ : (33 : ℚ)*(out₂+circuit₂.sharpLayerBudget)/Fintype.card F₂ ≤ 18645/(2^255 : ℚ) := by
    have h := div_nat_le (by decide : 0 < 2^255)
      (by omega : 33*(out₂+circuit₂.sharpLayerBudget) ≤ 18645) hfield₂
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using h
  have hp : (25 : ℚ)/Fintype.card F₁ ≤ 25/(2^128 : ℚ) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      (div_nat_le (a := 25) (b := 25) (q₀ := 2^128) (by decide) le_rfl hfield₁)
  have ht₁ : (25 : ℚ)*((2*circuit₁.layers : ℕ)/((Fintype.card F₁-1 : ℕ) : ℚ)) ≤
      2000/(2^128 : ℚ) := by
    have h := div_nat_le (q₀ := 2^128-1) (by decide)
      (by omega : 25*(2*circuit₁.layers) ≤ 1000) (Nat.sub_le_sub_right hfield₁ 1)
    refine le_trans ?_ (by norm_num : (1000 : ℚ)/(2^128-1 : ℕ) ≤ 2000/(2^128 : ℚ))
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc] using h
  have ht₂ : (33 : ℚ)*((2*circuit₂.layers : ℕ)/((Fintype.card F₂-1 : ℕ) : ℚ)) ≤
      2772/(2^255 : ℚ) := by
    have h := div_nat_le (q₀ := 2^255-1) (by decide)
      (by omega : 33*(2*circuit₂.layers) ≤ 1386) (Nat.sub_le_sub_right hfield₂ 1)
    refine le_trans ?_ (by norm_num : (1386 : ℚ)/(2^255-1 : ℕ) ≤ 2772/(2^255 : ℚ))
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc] using h
  unfold TwoFieldFS.constant TwoFieldFS.macCost CompiledSide.constant
  rw [S₁.packingRate_eq hpacked₁ hpacking, S₂.direct_packingRate hpacked₂, hb₁,hb₂]
  calc
    _ ≤ 825/(2^128 : ℚ) + (14825/(2^128 : ℚ)+2000/(2^128 : ℚ)+25/(2^128 : ℚ)+244/(2^128 : ℚ)+925/(2^128 : ℚ)) +
        (18645/(2^255 : ℚ)+2772/(2^255 : ℚ)+0+244/(2^255 : ℚ)+459/(2^128 : ℚ)) := by
      convert add_le_add (add_le_add hm (add_le_add (add_le_add (add_le_add (add_le_add hf₁ ht₁) hp) h₁.1) h₁.2))
        (add_le_add (add_le_add (add_le_add (add_le_add hf₂ ht₂) (le_rfl : (0 : ℚ) ≤ 0)) h₂.1) h₂.2) using 2 <;>
        push_cast <;> first | rfl | ring
    _ = constant := by norm_num [constant]

theorem error_le (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂)
    (hmac : 2^128 ≤ Fintype.card Fmac) (hout₁ : out₁ ≤ 5) (hout₂ : out₂ ≤ 3)
    (hfront₁ : out₁+circuit₁.sharpLayerBudget ≤ 593) (hfront₂ : out₂+circuit₂.sharpLayerBudget ≤ 565)
    (hlayers₁ : circuit₁.layers ≤ 20) (hlayers₂ : circuit₂.layers ≤ 21)
    (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)
    (N : ℕ) (proof : Proof S₁ S₂) :
    (N*TwoFieldFS.maxBudget S₁ S₂ M + ∑ i, TwoFieldFS.slotBudget S₁ S₂ M i)/Fintype.card C ≤
        N*coefficient+constant := by
  rw [TwoFieldFS.error_eq S₁ S₂ M N proof]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (coefficient_le S₁ S₂ cert₁ cert₂ hpacked₁ hpacked₂ hpacking hfield₁ hfield₂ hmac hout₁ hout₂)
    (Nat.cast_nonneg N))
    (constant_le S₁ S₂ cert₁ cert₂ hpacked₁ hpacked₂ hpacking hfield₁ hfield₂ hmac hfront₁ hfront₂ hlayers₁ hlayers₂)

end RuntimeCost
end LfzkV2.Linear.Runtime
