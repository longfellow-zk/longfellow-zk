import Lfzk.CompiledZkProfileSepMacK

/-!
# T-security with the ideal-cipher terms: `T = tA + N + Q_E`

`Lfzk.IdealCipherStream` reduces the deployed composite `prefix ↦ AES-CTR_{SHA256(prefix)}` (SHA-256
a random oracle, AES-256 an ideal cipher queried `Q_E` times) to a uniformly random function into
injective block tuples **up to two collision events**: two of the `N + L` relevant prefixes sharing
a key (`card_collide_le`, at most `(N + L)²/2 / 2^256`) and a relevant key queried to the cipher
before it was hashed (`card_key_mem`, at most `Q_E · (N + L) / 2^256`).  Only the non-adaptive form
of that hop is formalised (`IdealCipherStream.composite_le`).  This file proves that, **given the
hop**, 115-bit T-security survives with the cipher queries counted:

```text
p  ≤  [the random-function-into-injective-tuples bound]  +  ((N + L)²/2 + Q_E (N + L)) / 2^256
  ⟹  p  ≤  (1 + tA + N + Q_E) / 2^115
```

* `tsec_real_hop`, `tsec_of_uncapped_hop` — `TSec.tsec_real`, `tsec_of_uncapped` with the two hop
  terms: below `N, tA ≤ G = 2^(d − λ − 4)` the key birthday term is at most `N · 2^-λ / 16` plus
  a constant `L² · 2^-d`, and the freshness term at most `Q_E · 2^-λ / 8` (whatever `Q_E`); above
  `G` the right-hand side exceeds one.  The per-query coefficient must leave `2^-λ / 16` of room,
  so the coefficient numerals are certified at `2^-(λ+2)`;
* `twofield_tsecK_hop` — at a pair, with the virtual-card factor `lam ≤ lam₀`;
* `v7P256Sha{1,2,3,4}_sep_hop_tsec` — at the deployed v7 pairs with the separate-MAC slot, from the
  numerals `v7P256ShaK_sep_slackK_hop_bound` (the constant slack now also carries `L² · 2^-256`)
  and `_coeff` (`native_decide`).  Composed with
  `CompiledZkProfileK.twofield_circuit_ratio_leT_sepK` at `StreamSide.toK` over injective streams
  (`StreamCircuitSide`) this is the end-to-end bound, conditional on the hop.

## What is a hypothesis

The game hop `hp`: that the ideal-cipher experiment's success probability is at most the random
function's plus the two collision terms.  It is the standard identical-until-bad argument; it is
**not** proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.TSec

open Finset

theorem half_sq_le (n l : ℚ) : (n + l) * (n + l) / 2 ≤ n * n + l * l := by
  nlinarith [sq_nonneg (n - l)]

/-- **The arithmetic of T-security with the hop terms**, over `ℚ`: `TSec.tsec_real` at the
constant `A + l² δ` and the per-query coefficient `K + ε/16`, plus `q · ε/8`. -/
theorem tsec_real_hop {A K ε δ k n t q f T l g AN : ℚ}
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hδ : 0 ≤ δ) (hk0 : 0 ≤ k) (hk : k ≤ 2)
    (hn : 0 ≤ n) (ht : 0 ≤ t) (hq : 0 ≤ q) (hf : 0 ≤ f) (hl : 1 ≤ l) (hT : 32 ≤ T)
    (hnG : n ≤ g) (htG : t ≤ g) (hfT : 2 * f ≤ T)
    (hA : A + k * (T * l) * δ + l * l * δ ≤ ε) (hK : K + k * T * δ ≤ 7 * ε / 16)
    (hG : 16 * g * δ ≤ ε) (hlδ : l * δ ≤ ε / 16)
    (hAN : AN ≤ 3 * (t * t) + t * (2 * f + 1) + f + (f + t) * (l + n)) :
    A + n * K + k * AN * δ + ((n + l) * (n + l) / 2 + q * (n + l)) * δ
      ≤ (1 + n + t + q) * ε := by
  have hg0 : 0 ≤ g := le_trans hn hnG
  have hε : 0 ≤ ε := le_trans (mul_nonneg (mul_nonneg (by norm_num) hg0) hδ) hG
  have hgδ : g * δ ≤ ε / 16 := by linarith
  have hll : 0 ≤ l * l * δ := by
    have : 0 ≤ l := by linarith
    positivity
  -- the key birthday term: `(n + l)²/2 ≤ n² + l²`, and `n² δ ≤ n · g δ ≤ n ε/16`
  have e7 : (n + l) * (n + l) / 2 * δ ≤ n * (ε / 16) + l * l * δ := by
    have h1 : (n + l) * (n + l) / 2 * δ ≤ (n * n + l * l) * δ :=
      mul_le_mul_of_nonneg_right (half_sq_le n l) hδ
    have h2 : n * (n * δ) ≤ n * (g * δ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnG hδ) hn
    have h3 : n * (g * δ) ≤ n * (ε / 16) := mul_le_mul_of_nonneg_left hgδ hn
    have h4 : (n * n + l * l) * δ = n * (n * δ) + l * l * δ := by ring
    linarith
  -- the freshness term: `q (n + l) δ ≤ q (g δ + l δ) ≤ q ε/8`
  have e8 : q * (n + l) * δ ≤ q * (ε / 8) := by
    have h1 : n * δ ≤ g * δ := mul_le_mul_of_nonneg_right hnG hδ
    have h2 : (n + l) * δ ≤ ε / 8 := by
      have : (n + l) * δ = n * δ + l * δ := by ring
      linarith
    have h3 : q * ((n + l) * δ) ≤ q * (ε / 8) := mul_le_mul_of_nonneg_left h2 hq
    have : q * (n + l) * δ = q * ((n + l) * δ) := by ring
    linarith
  have key := tsec_real (A := A + l * l * δ) (K := K + ε / 16) (ε := ε) (δ := δ) (k := k)
    (n := n) (t := t) (f := f) (T := T) (l := l) (g := g) (AN := AN)
    (by linarith) (by linarith) hδ hk0 hk hn ht hf hl hT hnG htG hfT (by linarith)
    (by linarith) hG hAN
  have hq8 : q * (ε / 8) ≤ q * ε := mul_le_mul_of_nonneg_left (by linarith) hq
  have r1 : n * (K + ε / 16) = n * K + n * (ε / 16) := by ring
  have r2 : (1 + n + t + q) * ε = (1 + n + t) * ε + q * ε := by ring
  have r3 : ((n + l) * (n + l) / 2 + q * (n + l)) * δ
      = (n + l) * (n + l) / 2 * δ + q * (n + l) * δ := by ring
  linarith

/-- **T-security from an uncapped bound with the hop terms.**  Below `N, tA, Q_E ≤ G` by
`tsec_real_hop`; above, the right-hand side is at least `G · ε ≥ 1`. -/
theorem tsec_of_uncapped_hop {p A K ε δ k : ℚ} {fc T0 L N tA QE G : ℕ} (hp1 : p ≤ 1)
    (hp : p ≤ A + N * K + k * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) * δ
      + (((N + L) * (N + L) : ℚ) / 2 + QE * (N + L)) * δ)
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hδ : 0 ≤ δ) (hk0 : 0 ≤ k) (hk : k ≤ 2)
    (hA : A + k * ((T0 * L : ℕ) : ℚ) * δ + (L : ℚ) * L * δ ≤ ε)
    (hK : K + k * (T0 : ℚ) * δ ≤ 7 * ε / 16)
    (hG : 16 * (G : ℚ) * δ ≤ ε) (hGe : 1 ≤ (G : ℚ) * ε) (hLδ : (L : ℚ) * δ ≤ ε / 16)
    (hT0 : 32 ≤ T0) (hfc : 2 * fc ≤ T0) (hL : 1 ≤ L) :
    p ≤ (1 + N + tA + QE) * ε := by
  have hε : 0 ≤ ε := le_trans (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ) hG
  by_cases hs : N ≤ G ∧ tA ≤ G
  · refine hp.trans (tsec_real_hop (n := (N : ℚ)) (t := (tA : ℚ)) (q := (QE : ℚ)) (f := (fc : ℚ))
      (T := (T0 : ℚ)) (l := (L : ℚ)) (g := (G : ℚ))
      (AN := (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ))
      hA0 hK0 hδ hk0 hk (Nat.cast_nonneg N) (Nat.cast_nonneg tA) (Nat.cast_nonneg QE)
      (Nat.cast_nonneg fc) (by exact_mod_cast hL) (by exact_mod_cast hT0)
      (by exact_mod_cast hs.1) (by exact_mod_cast hs.2) (by exact_mod_cast hfc) (by push_cast at hA; exact hA) hK hG hLδ ?_)
    have := adaptiveNumerator_le_poly fc tA (L + N)
    exact_mod_cast this
  · have hGN : (G : ℚ) ≤ N + tA + QE := by
      have : G ≤ N + tA + QE := by
        by_contra hc
        exact hs ⟨by omega, by omega⟩
      exact_mod_cast this
    calc p ≤ 1 := hp1
      _ ≤ (G : ℚ) * ε := hGe
      _ ≤ (1 + N + tA + QE) * ε := mul_le_mul_of_nonneg_right (by linarith) hε

end Lfzk.TSec

namespace Lfzk.CompiledZkProfileK

open Finset Lfzk.TSec Lfzk.CertifiedV1 Lfzk.NizkZk Lfzk.NizkAdaptiveTwoField Lfzk.TwoFieldV1Rows

/-- **T-security for two fields at a virtual card, with the ideal-cipher hop terms**:
`twofield_tsecK` with `((N + L)²/2 + Q_E (N + L)) / 2^d` added to the bound, `L = len2`. -/
theorem twofield_tsecK_hop {R₁ R₂ : Row} {l₁ l₂ a b fc tA N QE : ℕ} {p m lam lam₀' : ℚ}
    (hp1 : p ≤ 1)
    (hp : p ≤ lam * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m
        + N * max (max (R₁.zkCoefficient l₁) (R₂.zkCoefficient l₂)) m)
      + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA (len2 R₁ R₂ + N) : ℚ)
        / 2 ^ R₁.params.digestBits)
      + (((N + len2 R₁ R₂) * (N + len2 R₁ R₂) : ℚ) / 2 + QE * (N + len2 R₁ R₂))
        / 2 ^ R₁.params.digestBits)
    (hm0 : 0 ≤ m) (hlam0 : 0 ≤ lam) (hlam : lam ≤ lam₀')
    (hsb : lam₀' * (R₂.zkBound l₂ + R₁.zkBound l₁ + m)
        + 2 * (((R₂.tape * len2 R₂ R₁ : ℕ) : ℚ) / 2 ^ R₂.params.digestBits)
        + ((len2 R₂ R₁ : ℚ) * len2 R₂ R₁) / 2 ^ R₂.params.digestBits ≤ 1 / 2 ^ a)
    (hsc : lam₀' * max (max (R₂.zkCoefficient l₂) (R₁.zkCoefficient l₁)) m
        + 2 * ((R₂.tape : ℚ) / 2 ^ R₂.params.digestBits) ≤ 1 / 2 ^ b)
    (hlδ : (len2 R₂ R₁ : ℚ) / 2 ^ R₂.params.digestBits ≤ 1 / 2 ^ a / 16)
    (hab : a + 2 ≤ b) (hdg : R₁.params.digestBits = R₂.params.digestBits)
    (hT0 : 32 ≤ R₂.tape) (hfc : 2 * fc ≤ R₂.tape) (hd : 2 * a + 4 ≤ R₁.params.digestBits) :
    p ≤ (1 + N + tA + QE) / 2 ^ a := by
  obtain ⟨hG, hGe⟩ := pow_facts hd
  have hδ : (0 : ℚ) ≤ 1 / 2 ^ R₁.params.digestBits := by positivity
  have hl : len2 R₂ R₁ = len2 R₁ R₂ := by unfold len2; omega
  rw [hl, ← hdg] at hsb hlδ
  rw [← hdg] at hsc
  have hb : (1 : ℚ) / 2 ^ b ≤ 1 / 2 ^ a / 4 := by
    rw [div_div, show (2 : ℚ) ^ a * 4 = 2 ^ (a + 2) by rw [pow_add]; norm_num]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hab)
  have hε0 : (0 : ℚ) ≤ 1 / 2 ^ a := by positivity
  have hc₁ := zkCoreAt_le_zkBound R₁ l₁
  have hc₂ := zkCoreAt_le_zkBound R₂ l₂
  have hn₁ := zkCoreAt_nonneg R₁ l₁ R₁.cardCand
  have hn₂ := zkCoreAt_nonneg R₂ l₂ R₂.cardCand
  set MM := max (max (R₁.zkCoefficient l₁) (R₂.zkCoefficient l₂)) m with hMM
  have hMM0 : 0 ≤ MM := le_trans hm0 (le_max_right _ _)
  have hmax : max (max (R₂.zkCoefficient l₂) (R₁.zkCoefficient l₁)) m = MM := by
    rw [hMM, max_comm (R₁.zkCoefficient l₁)]
  rw [hmax] at hsc
  have hX0 : 0 ≤ zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m := by linarith
  have hA' : lam * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m)
      ≤ lam₀' * (R₂.zkBound l₂ + R₁.zkBound l₁ + m) := by
    calc lam * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m)
        ≤ lam₀' * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m) :=
          mul_le_mul_of_nonneg_right hlam hX0
      _ ≤ lam₀' * (R₂.zkBound l₂ + R₁.zkBound l₁ + m) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_trans hlam0 hlam)
  have hK' : lam * MM ≤ lam₀' * MM := mul_le_mul_of_nonneg_right hlam hMM0
  have key := tsec_of_uncapped_hop (k := 2) (QE := QE)
    (A := lam * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m))
    (K := lam * MM) (ε := 1 / 2 ^ a)
    (δ := 1 / 2 ^ R₁.params.digestBits) (fc := fc) (T0 := R₂.tape) (L := len2 R₁ R₂)
    (N := N) (tA := tA) (G := 2 ^ (R₁.params.digestBits - a - 4)) hp1
    (hp.trans_eq (by ring)) (mul_nonneg hlam0 hX0) (mul_nonneg hlam0 hMM0) hδ (by norm_num)
    (by norm_num)
    (by
      have : (2 : ℚ) * ((R₂.tape * len2 R₁ R₂ : ℕ) : ℚ) * (1 / 2 ^ R₁.params.digestBits)
          + (len2 R₁ R₂ : ℚ) * len2 R₁ R₂ * (1 / 2 ^ R₁.params.digestBits)
          = 2 * (((R₂.tape * len2 R₁ R₂ : ℕ) : ℚ) / 2 ^ R₁.params.digestBits)
            + ((len2 R₁ R₂ : ℚ) * len2 R₁ R₂) / 2 ^ R₁.params.digestBits := by ring
      linarith)
    (by
      have : (2 : ℚ) * (R₂.tape : ℚ) * (1 / 2 ^ R₁.params.digestBits)
          = 2 * ((R₂.tape : ℚ) / 2 ^ R₁.params.digestBits) := by ring
      rw [this]; linarith)
    hG hGe (by rw [mul_one_div]; exact hlδ) hT0 hfc (by unfold len2; omega)
  exact key.trans_eq (by ring)


/-- `v7P256Sha1` with the separate-MAC slot, inflated by `lam₀`, with the key-birthday constant
`len2² / 2^256`, at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha1_sep_slackK_hop_bound :
    lam₀ * (v7P256Sha1.ecdsa.zkBound 8 + v7P256Sha1.sha.zkBound 3
        + (v7P256Sha1.sha.cardCand : ℚ) * v7P256Sha1.ecdsa.cardCand / (v7P256Sha1.macFieldSize : ℚ))
        + 2 * (((v7P256Sha1.ecdsa.tape * len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
        + ((len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℚ) * len2 v7P256Sha1.ecdsa v7P256Sha1.sha)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha1`'s worst coefficient with the separate-MAC slot, inflated by `lam₀`, plus the per-query
term: at most `2^-117`. -/
theorem v7P256Sha1_sep_slackK_coeff117 :
    lam₀ * max (max (v7P256Sha1.ecdsa.zkCoefficient 8) (v7P256Sha1.sha.zkCoefficient 3))
        ((v7P256Sha1.sha.cardCand : ℚ) * v7P256Sha1.ecdsa.cardCand / (v7P256Sha1.macFieldSize : ℚ))
      + 2 * ((v7P256Sha1.ecdsa.tape : ℚ) / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha1`'s transcript length is far below the key space: `len2 / 2^256 ≤ 2^-115 / 16`. -/
theorem v7P256Sha1_len2_le :
    (len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℚ) / 2 ^ v7P256Sha1.ecdsa.params.digestBits ≤ (1 : ℚ) / 2 ^ 115 / 16 := by
  native_decide

/-- **`v7P256Sha1`, separate MAC witnesses, T-secure at `λ = 115` with the cipher queries counted,
given the ideal-cipher hop.**  For any `p ≤ 1` below the virtual-card bound of
`twofield_circuit_ratio_leT_sepK` at `lam ≤ lam₀` plus the hop terms
`((N + L)²/2 + Q_E (N + L)) / 2^256`:

```text
p  ≤  (1 + tA + N + Q_E) · 2^-115
```
-/
theorem v7P256Sha1_sep_hop_tsec {tA N QE fc : ℕ} {p lam : ℚ} {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) (hp1 : p ≤ 1) (hlam0 : 0 ≤ lam) (hlam : lam ≤ lam₀)
    (hfc : fc = 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n)
    (hp : p ≤ lam * (zkCoreAt v7P256Sha1.sha 3 v7P256Sha1.sha.cardCand
          + zkCoreAt v7P256Sha1.ecdsa 8 v7P256Sha1.ecdsa.cardCand
          + (v7P256Sha1.sha.cardCand * v7P256Sha1.ecdsa.cardCand : ℚ) / (Fintype.card Fmac : ℚ)
          + N * max (max (v7P256Sha1.sha.zkCoefficient 3) (v7P256Sha1.ecdsa.zkCoefficient 8))
            ((v7P256Sha1.sha.cardCand * v7P256Sha1.ecdsa.cardCand : ℚ) / (Fintype.card Fmac : ℚ)))
        + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA (len2 v7P256Sha1.sha v7P256Sha1.ecdsa + N) : ℚ)
          / 2 ^ v7P256Sha1.sha.params.digestBits)
        + (((N + len2 v7P256Sha1.sha v7P256Sha1.ecdsa) * (N + len2 v7P256Sha1.sha v7P256Sha1.ecdsa) : ℚ) / 2
          + QE * (N + len2 v7P256Sha1.sha v7P256Sha1.ecdsa)) / 2 ^ v7P256Sha1.sha.params.digestBits) :
    p ≤ (1 + N + tA + QE : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha1_valid
  have hm : ((v7P256Sha1.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha1_sep_slackK_hop_bound
  have hsc := v7P256Sha1_sep_slackK_coeff117
  rw [hm] at hsb hsc
  subst hfc
  exact twofield_tsecK_hop hp1 hp (by positivity) hlam0 hlam hsb hsc v7P256Sha1_len2_le (by norm_num)
    (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

/-- `v7P256Sha2` with the separate-MAC slot, inflated by `lam₀`, with the key-birthday constant
`len2² / 2^256`, at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha2_sep_slackK_hop_bound :
    lam₀ * (v7P256Sha2.ecdsa.zkBound 8 + v7P256Sha2.sha.zkBound 4
        + (v7P256Sha2.sha.cardCand : ℚ) * v7P256Sha2.ecdsa.cardCand / (v7P256Sha2.macFieldSize : ℚ))
        + 2 * (((v7P256Sha2.ecdsa.tape * len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
        + ((len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℚ) * len2 v7P256Sha2.ecdsa v7P256Sha2.sha)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha2`'s worst coefficient with the separate-MAC slot, inflated by `lam₀`, plus the per-query
term: at most `2^-117`. -/
theorem v7P256Sha2_sep_slackK_coeff117 :
    lam₀ * max (max (v7P256Sha2.ecdsa.zkCoefficient 8) (v7P256Sha2.sha.zkCoefficient 4))
        ((v7P256Sha2.sha.cardCand : ℚ) * v7P256Sha2.ecdsa.cardCand / (v7P256Sha2.macFieldSize : ℚ))
      + 2 * ((v7P256Sha2.ecdsa.tape : ℚ) / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha2`'s transcript length is far below the key space: `len2 / 2^256 ≤ 2^-115 / 16`. -/
theorem v7P256Sha2_len2_le :
    (len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℚ) / 2 ^ v7P256Sha2.ecdsa.params.digestBits ≤ (1 : ℚ) / 2 ^ 115 / 16 := by
  native_decide

/-- **`v7P256Sha2`, separate MAC witnesses, T-secure at `λ = 115` with the cipher queries counted,
given the ideal-cipher hop.**  For any `p ≤ 1` below the virtual-card bound of
`twofield_circuit_ratio_leT_sepK` at `lam ≤ lam₀` plus the hop terms
`((N + L)²/2 + Q_E (N + L)) / 2^256`:

```text
p  ≤  (1 + tA + N + Q_E) · 2^-115
```
-/
theorem v7P256Sha2_sep_hop_tsec {tA N QE fc : ℕ} {p lam : ℚ} {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) (hp1 : p ≤ 1) (hlam0 : 0 ≤ lam) (hlam : lam ≤ lam₀)
    (hfc : fc = 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n)
    (hp : p ≤ lam * (zkCoreAt v7P256Sha2.sha 4 v7P256Sha2.sha.cardCand
          + zkCoreAt v7P256Sha2.ecdsa 8 v7P256Sha2.ecdsa.cardCand
          + (v7P256Sha2.sha.cardCand * v7P256Sha2.ecdsa.cardCand : ℚ) / (Fintype.card Fmac : ℚ)
          + N * max (max (v7P256Sha2.sha.zkCoefficient 4) (v7P256Sha2.ecdsa.zkCoefficient 8))
            ((v7P256Sha2.sha.cardCand * v7P256Sha2.ecdsa.cardCand : ℚ) / (Fintype.card Fmac : ℚ)))
        + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA (len2 v7P256Sha2.sha v7P256Sha2.ecdsa + N) : ℚ)
          / 2 ^ v7P256Sha2.sha.params.digestBits)
        + (((N + len2 v7P256Sha2.sha v7P256Sha2.ecdsa) * (N + len2 v7P256Sha2.sha v7P256Sha2.ecdsa) : ℚ) / 2
          + QE * (N + len2 v7P256Sha2.sha v7P256Sha2.ecdsa)) / 2 ^ v7P256Sha2.sha.params.digestBits) :
    p ≤ (1 + N + tA + QE : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha2_valid
  have hm : ((v7P256Sha2.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha2_sep_slackK_hop_bound
  have hsc := v7P256Sha2_sep_slackK_coeff117
  rw [hm] at hsb hsc
  subst hfc
  exact twofield_tsecK_hop hp1 hp (by positivity) hlam0 hlam hsb hsc v7P256Sha2_len2_le (by norm_num)
    (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

/-- `v7P256Sha3` with the separate-MAC slot, inflated by `lam₀`, with the key-birthday constant
`len2² / 2^256`, at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha3_sep_slackK_hop_bound :
    lam₀ * (v7P256Sha3.ecdsa.zkBound 8 + v7P256Sha3.sha.zkBound 4
        + (v7P256Sha3.sha.cardCand : ℚ) * v7P256Sha3.ecdsa.cardCand / (v7P256Sha3.macFieldSize : ℚ))
        + 2 * (((v7P256Sha3.ecdsa.tape * len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
        + ((len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℚ) * len2 v7P256Sha3.ecdsa v7P256Sha3.sha)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha3`'s worst coefficient with the separate-MAC slot, inflated by `lam₀`, plus the per-query
term: at most `2^-117`. -/
theorem v7P256Sha3_sep_slackK_coeff117 :
    lam₀ * max (max (v7P256Sha3.ecdsa.zkCoefficient 8) (v7P256Sha3.sha.zkCoefficient 4))
        ((v7P256Sha3.sha.cardCand : ℚ) * v7P256Sha3.ecdsa.cardCand / (v7P256Sha3.macFieldSize : ℚ))
      + 2 * ((v7P256Sha3.ecdsa.tape : ℚ) / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha3`'s transcript length is far below the key space: `len2 / 2^256 ≤ 2^-115 / 16`. -/
theorem v7P256Sha3_len2_le :
    (len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℚ) / 2 ^ v7P256Sha3.ecdsa.params.digestBits ≤ (1 : ℚ) / 2 ^ 115 / 16 := by
  native_decide

/-- **`v7P256Sha3`, separate MAC witnesses, T-secure at `λ = 115` with the cipher queries counted,
given the ideal-cipher hop.**  For any `p ≤ 1` below the virtual-card bound of
`twofield_circuit_ratio_leT_sepK` at `lam ≤ lam₀` plus the hop terms
`((N + L)²/2 + Q_E (N + L)) / 2^256`:

```text
p  ≤  (1 + tA + N + Q_E) · 2^-115
```
-/
theorem v7P256Sha3_sep_hop_tsec {tA N QE fc : ℕ} {p lam : ℚ} {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) (hp1 : p ≤ 1) (hlam0 : 0 ≤ lam) (hlam : lam ≤ lam₀)
    (hfc : fc = 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n)
    (hp : p ≤ lam * (zkCoreAt v7P256Sha3.sha 4 v7P256Sha3.sha.cardCand
          + zkCoreAt v7P256Sha3.ecdsa 8 v7P256Sha3.ecdsa.cardCand
          + (v7P256Sha3.sha.cardCand * v7P256Sha3.ecdsa.cardCand : ℚ) / (Fintype.card Fmac : ℚ)
          + N * max (max (v7P256Sha3.sha.zkCoefficient 4) (v7P256Sha3.ecdsa.zkCoefficient 8))
            ((v7P256Sha3.sha.cardCand * v7P256Sha3.ecdsa.cardCand : ℚ) / (Fintype.card Fmac : ℚ)))
        + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA (len2 v7P256Sha3.sha v7P256Sha3.ecdsa + N) : ℚ)
          / 2 ^ v7P256Sha3.sha.params.digestBits)
        + (((N + len2 v7P256Sha3.sha v7P256Sha3.ecdsa) * (N + len2 v7P256Sha3.sha v7P256Sha3.ecdsa) : ℚ) / 2
          + QE * (N + len2 v7P256Sha3.sha v7P256Sha3.ecdsa)) / 2 ^ v7P256Sha3.sha.params.digestBits) :
    p ≤ (1 + N + tA + QE : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha3_valid
  have hm : ((v7P256Sha3.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha3_sep_slackK_hop_bound
  have hsc := v7P256Sha3_sep_slackK_coeff117
  rw [hm] at hsb hsc
  subst hfc
  exact twofield_tsecK_hop hp1 hp (by positivity) hlam0 hlam hsb hsc v7P256Sha3_len2_le (by norm_num)
    (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

/-- `v7P256Sha4` with the separate-MAC slot, inflated by `lam₀`, with the key-birthday constant
`len2² / 2^256`, at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha4_sep_slackK_hop_bound :
    lam₀ * (v7P256Sha4.ecdsa.zkBound 8 + v7P256Sha4.sha.zkBound 5
        + (v7P256Sha4.sha.cardCand : ℚ) * v7P256Sha4.ecdsa.cardCand / (v7P256Sha4.macFieldSize : ℚ))
        + 2 * (((v7P256Sha4.ecdsa.tape * len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
        + ((len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℚ) * len2 v7P256Sha4.ecdsa v7P256Sha4.sha)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha4`'s worst coefficient with the separate-MAC slot, inflated by `lam₀`, plus the per-query
term: at most `2^-117`. -/
theorem v7P256Sha4_sep_slackK_coeff117 :
    lam₀ * max (max (v7P256Sha4.ecdsa.zkCoefficient 8) (v7P256Sha4.sha.zkCoefficient 5))
        ((v7P256Sha4.sha.cardCand : ℚ) * v7P256Sha4.ecdsa.cardCand / (v7P256Sha4.macFieldSize : ℚ))
      + 2 * ((v7P256Sha4.ecdsa.tape : ℚ) / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha4`'s transcript length is far below the key space: `len2 / 2^256 ≤ 2^-115 / 16`. -/
theorem v7P256Sha4_len2_le :
    (len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℚ) / 2 ^ v7P256Sha4.ecdsa.params.digestBits ≤ (1 : ℚ) / 2 ^ 115 / 16 := by
  native_decide

/-- **`v7P256Sha4`, separate MAC witnesses, T-secure at `λ = 115` with the cipher queries counted,
given the ideal-cipher hop.**  For any `p ≤ 1` below the virtual-card bound of
`twofield_circuit_ratio_leT_sepK` at `lam ≤ lam₀` plus the hop terms
`((N + L)²/2 + Q_E (N + L)) / 2^256`:

```text
p  ≤  (1 + tA + N + Q_E) · 2^-115
```
-/
theorem v7P256Sha4_sep_hop_tsec {tA N QE fc : ℕ} {p lam : ℚ} {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) (hp1 : p ≤ 1) (hlam0 : 0 ≤ lam) (hlam : lam ≤ lam₀)
    (hfc : fc = 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n)
    (hp : p ≤ lam * (zkCoreAt v7P256Sha4.sha 5 v7P256Sha4.sha.cardCand
          + zkCoreAt v7P256Sha4.ecdsa 8 v7P256Sha4.ecdsa.cardCand
          + (v7P256Sha4.sha.cardCand * v7P256Sha4.ecdsa.cardCand : ℚ) / (Fintype.card Fmac : ℚ)
          + N * max (max (v7P256Sha4.sha.zkCoefficient 5) (v7P256Sha4.ecdsa.zkCoefficient 8))
            ((v7P256Sha4.sha.cardCand * v7P256Sha4.ecdsa.cardCand : ℚ) / (Fintype.card Fmac : ℚ)))
        + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA (len2 v7P256Sha4.sha v7P256Sha4.ecdsa + N) : ℚ)
          / 2 ^ v7P256Sha4.sha.params.digestBits)
        + (((N + len2 v7P256Sha4.sha v7P256Sha4.ecdsa) * (N + len2 v7P256Sha4.sha v7P256Sha4.ecdsa) : ℚ) / 2
          + QE * (N + len2 v7P256Sha4.sha v7P256Sha4.ecdsa)) / 2 ^ v7P256Sha4.sha.params.digestBits) :
    p ≤ (1 + N + tA + QE : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha4_valid
  have hm : ((v7P256Sha4.macFieldSize : ℕ) : ℚ) = (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha4_sep_slackK_hop_bound
  have hsc := v7P256Sha4_sep_slackK_coeff117
  rw [hm] at hsb hsc
  subst hfc
  exact twofield_tsecK_hop hp1 hp (by positivity) hlam0 hlam hsb hsc v7P256Sha4_len2_le (by norm_num)
    (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

end Lfzk.CompiledZkProfileK
