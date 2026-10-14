/-
# Copyright 2026 Google LLC.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
-/
module

public import ECDSA.PowMod

/-!
# Pratt certificates for the two curve primes

A number n is prime if there exists a witness "a" such that:
  - a^(n-1) ≡ 1 (mod n)
  - gcd(a^((n-1)/q) - 1, n) = 1 for every prime q | n-1

Besides the simple calculation, one needs the factorization of
n as well as a certificate of primality for the divisors q.
In this way, a recursive certificate of primality can be
produced for n.

This file verifies those certificates for the two primes
needed for our formalization of P256 and k1.
-/

public section

namespace ECDSA

set_option maxRecDepth 40000
set_option exponentiation.threshold 300

theorem prime_204061199 : Nat.Prime 204061199 := by
  refine lucas_primality 204061199 ((11 : ℕ) : ZMod 204061199) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 204061199 - 1 = ([2, 11, 23, 107, 3769] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_nil _⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_34282281433 : Nat.Prime 34282281433 := by
  refine lucas_primality 34282281433 ((17 : ℕ) : ZMod 34282281433) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 34282281433 - 1 = ([2, 2, 2, 3, 7, 204061199] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_204061199, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_66417393611 : Nat.Prime 66417393611 := by
  refine lucas_primality 66417393611 ((6 : ℕ) : ZMod 66417393611) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 66417393611 - 1 = ([2, 5, 53, 173, 197, 3677] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_11290956913871 : Nat.Prime 11290956913871 := by
  refine lucas_primality 11290956913871 ((13 : ℕ) : ZMod 11290956913871) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 11290956913871 - 1 = ([2, 5, 17, 66417393611] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_66417393611, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_46076956964474543 : Nat.Prime 46076956964474543 := by
  refine lucas_primality 46076956964474543 ((5 : ℕ) : ZMod 46076956964474543) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 46076956964474543 - 1 = ([2, 23, 18169, 78283, 704251] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_nil _⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_774023187263532362759620327192479577272145303 : Nat.Prime 774023187263532362759620327192479577272145303 := by
  refine lucas_primality 774023187263532362759620327192479577272145303 ((3 : ℕ) : ZMod 774023187263532362759620327192479577272145303) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 774023187263532362759620327192479577272145303 - 1 = ([2, 3, 3, 2411, 34282281433, 11290956913871, 46076956964474543] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_34282281433, List.forall_mem_cons.mpr ⟨prime_11290956913871, List.forall_mem_cons.mpr ⟨prime_46076956964474543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_835945042244614951780389953367877943453916927241 : Nat.Prime 835945042244614951780389953367877943453916927241 := by
  refine lucas_primality 835945042244614951780389953367877943453916927241 ((11 : ℕ) : ZMod 835945042244614951780389953367877943453916927241) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 835945042244614951780389953367877943453916927241 - 1 = ([2, 2, 2, 3, 3, 3, 5, 774023187263532362759620327192479577272145303] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_774023187263532362759620327192479577272145303, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_115792089210356248762697446949407573530086143415290314195533631308867097853951 : Nat.Prime 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  refine lucas_primality 115792089210356248762697446949407573530086143415290314195533631308867097853951 ((6 : ℕ) : ZMod 115792089210356248762697446949407573530086143415290314195533631308867097853951) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 115792089210356248762697446949407573530086143415290314195533631308867097853951 - 1 = ([2, 3, 5, 5, 17, 257, 641, 1531, 65537, 490463, 6700417, 835945042244614951780389953367877943453916927241] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_835945042244614951780389953367877943453916927241, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_173378833005251801 : Nat.Prime 173378833005251801 := by
  refine lucas_primality 173378833005251801 ((6 : ℕ) : ZMod 173378833005251801) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 173378833005251801 - 1 = ([2, 2, 2, 5, 5, 2621, 24809, 13331831] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_22149492674086928081353 : Nat.Prime 22149492674086928081353 := by
  refine lucas_primality 22149492674086928081353 ((5 : ℕ) : ZMod 22149492674086928081353) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 22149492674086928081353 - 1 = ([2, 2, 2, 3, 5323, 173378833005251801] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_173378833005251801, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_132896956044521568488119 : Nat.Prime 132896956044521568488119 := by
  refine lucas_primality 132896956044521568488119 ((6 : ℕ) : ZMod 132896956044521568488119) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 132896956044521568488119 - 1 = ([2, 3, 22149492674086928081353] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_22149492674086928081353, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_107590001 : Nat.Prime 107590001 := by
  refine lucas_primality 107590001 ((3 : ℕ) : ZMod 107590001) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 107590001 - 1 = ([2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_255515944373312847190720520512484175977 : Nat.Prime 255515944373312847190720520512484175977 := by
  refine lucas_primality 255515944373312847190720520512484175977 ((3 : ℕ) : ZMod 255515944373312847190720520512484175977) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 255515944373312847190720520512484175977 - 1 = ([2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_107590001, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_205115282021455665897114700593932402728804164701536103180137503955397371 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  refine lucas_primality 205115282021455665897114700593932402728804164701536103180137503955397371 ((10 : ℕ) : ZMod 205115282021455665897114700593932402728804164701536103180137503955397371) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 205115282021455665897114700593932402728804164701536103180137503955397371 - 1 = ([2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_132896956044521568488119, List.forall_mem_cons.mpr ⟨prime_255515944373312847190720520512484175977, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_115792089237316195423570985008687907853269984665640564039457584007908834671663 : Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  refine lucas_primality 115792089237316195423570985008687907853269984665640564039457584007908834671663 ((3 : ℕ) : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 115792089237316195423570985008687907853269984665640564039457584007908834671663 - 1 = ([2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨(by norm_num), List.forall_mem_cons.mpr ⟨prime_205115282021455665897114700593932402728804164701536103180137503955397371, List.forall_mem_nil _⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

end ECDSA

end
