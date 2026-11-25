import LfzkV1.MerkleWork125

/-!
# The arithmetic of the v1 125-bit bound

The algebraic charge is only incurred on the branch where the two Merkle
replays force at least thirteen distinct adversarial Merkle preimages. This
absorbs the fixed replay cost before adding the Merkle exceptions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.SoundnessBudget125

open LfzkV1.MerkleWork125

def q : ℚ := 2 ^ 128

theorem initialCharge_le : (7 / q) * (1 + 1 / 2 ^ 108) ≤ (7001 / 1000) / q := by
  norm_num [q]

theorem openingCharge_le : ((319 / 100 + 1593 / 500) / q) + (7 / q) / 2 ^ 32 + 1 / 2 ^ 202
      ≤ (64 / 10) / q := by
  norm_num [q]

set_option maxHeartbeats 1000000 in
/-- Every observed role uses the same counter. The fixed terms cover one
appended key, one appended opening and the entire signature replay. -/
theorem covered_charges_le (key signature field batch opening N : ℕ)
    (hN : key + signature + field + batch + opening ≤ N) :
    (4 / q) * (key + 1 : ℚ) + (1426 / 1000 / q) * (signature + 1 : ℚ) +
      ((7 / q) * (1 + 1 / 2 ^ 108)) * (field : ℚ) + (319 / 100 / q) * (batch : ℚ) +
      ((3188 / 500 / q) + (7 / q) / 2 ^ 32 + 1 / 2 ^ 202) * (opening : ℚ) +
      ((3188 / 500 / q) + 1 / 2 ^ 202) ≤ (15016 / 1000 + N * (7001 / 1000)) / q := by
  let cap : ℚ := (7001 / 1000) / q
  let fixed : ℚ := (4 / q) + (1426 / 1000 / q) + (3188 / 500 / q) + 1 / 2 ^ 202
  have hkey : (4 : ℚ) / q ≤ cap := by norm_num [q, cap]
  have hsig : (1426 / 1000 : ℚ) / q ≤ cap := by norm_num [q, cap]
  have hbatch : (319 / 100 : ℚ) / q ≤ cap := by norm_num [q, cap]
  have hopen : ((3188 / 500 : ℚ) / q) + (7 / q) / 2^32 + 1 / 2^202 ≤ cap := by
    norm_num [q, cap]
  have hadd : fixed ≤ (15016 / 1000) / q := by norm_num [q, fixed]
  have hn : 0 ≤ cap := by norm_num [q, cap]
  have hsum : (key : ℚ) + signature + field + batch + opening ≤ N := by exact_mod_cast hN
  have hbounded := mul_le_mul_of_nonneg_left hsum hn
  calc
    _ = (4 / q) * (key : ℚ) + (1426 / 1000 / q) * (signature : ℚ) +
        ((7 / q) * (1 + 1 / 2 ^ 108)) * (field : ℚ) + (319 / 100 / q) * (batch : ℚ) +
        ((3188 / 500 / q) + (7 / q) / 2 ^ 32 + 1 / 2 ^ 202) * (opening : ℚ) + fixed := by
      dsimp [fixed]
      ring
    _ ≤ cap * (key : ℚ) + cap * (signature : ℚ) + cap * (field : ℚ) +
        cap * (batch : ℚ) + cap * (opening : ℚ) + (15016 / 1000) / q := by
      exact add_le_add (add_le_add (add_le_add (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right hkey (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_right hsig (Nat.cast_nonneg _)))
        (mul_le_mul_of_nonneg_right initialCharge_le (Nat.cast_nonneg _)))
        (mul_le_mul_of_nonneg_right hbatch (Nat.cast_nonneg _)))
        (mul_le_mul_of_nonneg_right hopen (Nat.cast_nonneg _))) hadd
    _ = cap * ((key : ℚ) + signature + field + batch + opening) + (15016 / 1000) / q := by ring
    _ ≤ cap * (N : ℚ) + (15016 / 1000) / q := add_le_add hbounded le_rfl
    _ = _ := by dsimp [cap]; ring

/-- Losing at most `2^14 / q` of the completions of an identity view fits
inside the final charge budget. The `81 / q` nonidentity charge is separate. -/
theorem replay_charges_le (N : ℕ) :
    (81 + ((15016 : ℚ) / 1000 + N * (7001 / 1000)) / (1 - 2 ^ 14 / q)) / q ≤
      (97 + N * (701 / 100)) / q := by
  have hq : 0 < q := by norm_num [q]
  have hc : ((15016 : ℚ) / 1000) / (1 - 2 ^ 14 / q) ≤ 16 := by norm_num [q]
  have hk : ((7001 : ℚ) / 1000) / (1 - 2 ^ 14 / q) ≤ 701 / 100 := by norm_num [q]
  rw [div_le_div_iff_of_pos_right hq, add_div, mul_div_assoc]
  linarith [mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg (α := ℚ) N)]

/-- The Merkle work floor absorbs the replay charge when the adversary
has positive query fuel. At zero fuel, only the Merkle exception remains. -/
theorem bound_of_charges {p : ℚ} {fc L N tA : ℕ}
    (hp1 : p ≤ 1) (hfc : fc ≤ 14000) (hL : L ≤ 1200)
    (hp : p ≤ (if 13 ≤ tA then (97 + N * (701 / 100)) / q else 0)
      + (adaptiveMerkleNumerator fc tA (L + N) : ℚ) / q ^ 2) :
    p ≤ if N + tA = 0 then 33628000 / 2 ^ 256 else (N + tA : ℚ) / 2 ^ 125 := by
  have hq : 0 < q := by norm_num [q]
  have htarget : (2 ^ 125 : ℚ) = q / 8 := by norm_num [q]
  by_cases hz : N + tA = 0
  · have hN : N = 0 := by omega
    have hA : tA = 0 := by omega
    subst N
    subst tA
    have hm : adaptiveMerkleNumerator fc 0 (L + 0) ≤ 33628000 := by
      simpa [adaptiveMerkleNumerator] using
        (Nat.mul_le_mul_left 2 (Nat.add_le_add hfc (Nat.mul_le_mul hfc hL)) :
          2 * (fc + fc * L) ≤ 33628000)
    simp only [zero_add, if_neg (by decide : ¬13 ≤ 0)] at hp
    change p ≤ (33628000 : ℚ) / 2 ^ 256
    have hm' : (adaptiveMerkleNumerator fc 0 (L + 0) : ℚ) ≤ 33628000 := by exact_mod_cast hm
    have h := hp.trans (div_le_div_of_nonneg_right hm' (sq_nonneg q))
    simpa only [q, ← pow_mul, Nat.reduceMul, Nat.add_zero] using h
  · rw [if_neg hz]
    let T : ℚ := (N : ℚ) + tA
    have hT : 1 ≤ T := by
      dsimp [T]
      exact_mod_cast (show 1 ≤ N + tA by omega)
    change p ≤ T / 2 ^ 125
    by_cases ht : T ≤ q / 8
    · have hm : (adaptiveMerkleNumerator fc tA (L + N) : ℚ) ≤ 6 * T ^ 2 + 2 ^ 28 * T := by
        have hc : (adaptiveMerkleNumerator fc tA (L + N) : ℚ) ≤
            6 * (1 + T) ^ 2 + 2 ^ 26 * (1 + T) := by
          dsimp [T]
          have hm := adaptiveMerkleNumerator_le_v7 fc L N tA hfc hL
          exact_mod_cast (show adaptiveMerkleNumerator fc tA (L + N) ≤
            6 * (1 + (N + tA)) ^ 2 + 2 ^ 26 * (1 + (N + tA)) by
              simpa only [Nat.add_assoc, Nat.reducePow] using hm)
        nlinarith only [hc, hT]
      have hmerkle (c : ℚ) (hc : 6 * T + 2 ^ 28 ≤ c * q) :
          (adaptiveMerkleNumerator fc tA (L + N) : ℚ) / q ≤ c * T := by
        rw [div_le_iff₀ hq]
        calc
          _ ≤ 6 * T ^ 2 + 2 ^ 28 * T := hm
          _ = (6 * T + 2 ^ 28) * T := by ring
          _ ≤ _ := by
            simpa only [mul_right_comm] using
              mul_le_mul_of_nonneg_right hc ((zero_le_one : (0 : ℚ) ≤ 1).trans hT)
      let algebra : ℚ := if 13 ≤ tA then 97 + N * (701 / 100) else 0
      have hsum : algebra + (adaptiveMerkleNumerator fc tA (L + N) : ℚ) / q ≤ 8 * T := by
        by_cases hs : T ≤ 32
        · have ha : algebra ≤ (15 / 2) * T := by
            unfold algebra T
            split_ifs with hf
            · have h13 : (13 : ℚ) ≤ tA := by exact_mod_cast hf
              linarith [Nat.cast_nonneg (α := ℚ) N]
            · exact mul_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          have hb := hmerkle (1 / 2) (by
            have hcap : 6 * 32 + 2 ^ 28 ≤ (1 / 2 : ℚ) * q := by norm_num [q]
            linarith)
          linarith
        · have ha : algebra ≤ (36 / 5) * T := by
            unfold algebra
            split_ifs with hf
            · have h13 : (13 : ℚ) ≤ tA := by exact_mod_cast hf
              have hT' : (32 : ℚ) ≤ T := le_of_lt (lt_of_not_ge hs)
              dsimp only [T] at hT' ⊢
              linarith
            · exact mul_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          have hb := hmerkle (4 / 5) (by
            have hcap : 6 * (q / 8) + 2 ^ 28 ≤ (4 / 5 : ℚ) * q := by norm_num [q]
            linarith)
          linarith
      have hscaled : p * q ≤ algebra + (adaptiveMerkleNumerator fc tA (L + N) : ℚ) / q := by
        have h := mul_le_mul_of_nonneg_right hp hq.le
        have hcancel (x : ℚ) : x / q * q = x := by field_simp
        have hcancel₂ (x : ℚ) : x / q ^ 2 * q = x / q := by field_simp
        simpa only [add_mul, hcancel₂, ite_mul, zero_mul, hcancel, algebra] using h
      rw [htarget, div_div_eq_mul_div, le_div_iff₀ hq]
      simpa only [mul_comm T 8] using hscaled.trans hsum
    · apply hp1.trans
      rw [htarget, le_div_iff₀ (by positivity), one_mul]
      exact le_of_lt (lt_of_not_ge ht)

end LfzkV1.SoundnessBudget125
