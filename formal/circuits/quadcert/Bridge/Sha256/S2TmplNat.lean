/-
# The `Nat` half of the wrapping-sum meaning

`S2TmplWrap` gives the field half: the assertion forces `wrapPoly n (2^32) z = 0`. Reaching the
arithmetic statement `P = C % 2^32` needs `SHA256F.wrap_sum_of_zero`'s other three hypotheses,
`z = C - P`, `C < n·2^32` and `P < 2^32`, and those are about the *addends* rather than the shape
of the product tree.

They are still template-uniform, and the reason is the coefficient structure. `z` is a flat linear
form `Σ 2^j · x_{a,j} - Σ 2^j · y_j` over input nodes that booleanity has already pinned to
`{0,1}`. So:

* the value of each half is the cast of a `Nat` -- `sum_of_bits`, proven once by induction;
* that `Nat` is bounded by the **sum of the coefficients**, which is data the generator has in
  hand. For 32-bit words `Σ_{j<32} 2^j = 2^32 - 1`, so `n` addend words give
  `C ≤ n(2^32 - 1) < n·2^32` and the output word gives `P ≤ 2^32 - 1 < 2^32`. The bounds are
  arithmetic on the coefficient list, not facts about the circuit.

What remains genuinely per-instance is only *which* inputs are addend bits and which are output
bits -- the split of `z`'s term list into the two halves. That is a fact about the layout, and it
enters below as `hz`.
-/

import Mathlib.Tactic.Ring
import SHA.Wrap

namespace SHA256F

variable {F : Type} [Field F]

/-- A linear form over field elements known to be bits is the cast of a `Nat`, bounded by the sum
    of its coefficients. Proven once; every wrapping-sum instance uses it twice. -/
theorem sum_of_bits :
    ∀ (l : List (Nat × F)), (∀ q ∈ l, q.2 = 0 ∨ q.2 = 1) →
      ∃ N : Nat, (l.map (fun q => (q.1 : F) * q.2)).sum = (N : F) ∧
        N ≤ (l.map Prod.fst).sum
  | [], _ => ⟨0, by simp, by simp⟩
  | q :: rest, h => by
      obtain ⟨N, hval, hbd⟩ := sum_of_bits rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      rcases h q (List.mem_cons_self ..) with hq | hq
      · refine ⟨N, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, hq, hval]; ring
        · simp only [List.map_cons, List.sum_cons]; omega
      · refine ⟨q.1 + N, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, hq, hval]; push_cast; ring
        · simp only [List.map_cons, List.sum_cons]; omega

/-- **The `Nat` half.** Booleanity of the addend and output bits, plus coefficient sums, turn the
    field-side product assertion into 32-bit arithmetic. -/
theorem wrap_nat_of_bits {p : Nat} [CharP F p] (n : Nat) (cs ds : List (Nat × F)) (z : F)
    (hc : ∀ q ∈ cs, q.2 = 0 ∨ q.2 = 1)
    (hd : ∀ q ∈ ds, q.2 = 0 ∨ q.2 = 1)
    (hcb : (cs.map Prod.fst).sum < n * 2 ^ 32)
    (hdb : (ds.map Prod.fst).sum < 2 ^ 32)
    (hnp : n * 2 ^ 32 ≤ p)
    (hz : z = (cs.map (fun q => (q.1 : F) * q.2)).sum
              - (ds.map (fun q => (q.1 : F) * q.2)).sum)
    (hroot : wrapPoly n ((2 ^ 32 : Nat) : F) z = 0) :
    ∃ C P : Nat,
      (cs.map (fun q => (q.1 : F) * q.2)).sum = (C : F) ∧
      (ds.map (fun q => (q.1 : F) * q.2)).sum = (P : F) ∧
      P = C % 2 ^ 32 := by
  obtain ⟨C, hCval, hCbd⟩ := sum_of_bits cs hc
  obtain ⟨P, hPval, hPbd⟩ := sum_of_bits ds hd
  refine ⟨C, P, hCval, hPval, ?_⟩
  exact wrap_sum_of_zero n C P z (lt_of_le_of_lt hCbd hcb) (lt_of_le_of_lt hPbd hdb) hnp
    (by rw [hz, hCval, hPval]) hroot

/-- **The two-addend case, split.** The eight `final` assertions add two witnessed words, and
    `SHA/Sound.lean`'s `hout` wants the result as `w32 (A + B)` — one `Nat` per word — rather than
    as `C % 2^32` for a single opaque `C` covering both. Splitting the addend list is the whole
    difference, and it is why the generated `csA`/`csB` are emitted separately: the term *order*
    inside `z` is whatever the compiler scheduled, but the `ring` that closes the linear form does
    not care, so the bridge is free to group the coefficients by word. -/
theorem wrap_two_words {p : Nat} [CharP F p] (csA csB ds : List (Nat × F)) (z : F)
    (hA : ∀ q ∈ csA, q.2 = 0 ∨ q.2 = 1)
    (hB : ∀ q ∈ csB, q.2 = 0 ∨ q.2 = 1)
    (hd : ∀ q ∈ ds, q.2 = 0 ∨ q.2 = 1)
    (hAb : (csA.map Prod.fst).sum < 2 ^ 32)
    (hBb : (csB.map Prod.fst).sum < 2 ^ 32)
    (hdb : (ds.map Prod.fst).sum < 2 ^ 32)
    (hnp : 2 * 2 ^ 32 ≤ p)
    (hz : z = ((csA ++ csB).map (fun q => (q.1 : F) * q.2)).sum
              - (ds.map (fun q => (q.1 : F) * q.2)).sum)
    (hroot : wrapPoly 2 ((2 ^ 32 : Nat) : F) z = 0) :
    ∃ A B P : Nat,
      (csA.map (fun q => (q.1 : F) * q.2)).sum = (A : F) ∧
      (csB.map (fun q => (q.1 : F) * q.2)).sum = (B : F) ∧
      (ds.map (fun q => (q.1 : F) * q.2)).sum = (P : F) ∧
      P = SHA256.w32 (A + B) := by
  obtain ⟨A, hAval, hAbd⟩ := sum_of_bits csA hA
  obtain ⟨B, hBval, hBbd⟩ := sum_of_bits csB hB
  obtain ⟨P, hPval, hPbd⟩ := sum_of_bits ds hd
  refine ⟨A, B, P, hAval, hBval, hPval, ?_⟩
  have hsum : ((csA ++ csB).map (fun q => (q.1 : F) * q.2)).sum = ((A + B : Nat) : F) := by
    rw [List.map_append, List.sum_append, hAval, hBval]; push_cast; ring
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hCb : A + B < 2 * 2 ^ 32 := by omega
  show P = (A + B) % 2 ^ 32
  exact wrap_sum_of_zero 2 (A + B) P z hCb (lt_of_le_of_lt hPbd hdb) hnp
    (by rw [hz, hsum, hPval]) hroot

/-- **The four-addend case, split by word.** The sibling of `wrap_two_words` for the 48
    `sha256/schedule/N` assertions, whose `z` adds four 32-bit quantities: `σ₁ (W (t-2))`,
    `W (t-7)`, `σ₀ (W (t-15))` and `W (t-16)`.

    The two `σ` groups are not input bits — each entry is an *intermediate* circuit node holding
    `a + b - 2ab`, the compiler's xor. That does not matter here: `sum_of_bits` only asks that
    each entry evaluate to `0` or `1`, which a xor of bits does, and `SHA256.sigma0_bits` is what
    later identifies the resulting `Nat` with `σ₀` of the packed word. -/
theorem wrap_four_words {p : Nat} [CharP F p] (c₀ c₁ c₂ c₃ ds : List (Nat × F)) (z : F)
    (h₀ : ∀ q ∈ c₀, q.2 = 0 ∨ q.2 = 1) (h₁ : ∀ q ∈ c₁, q.2 = 0 ∨ q.2 = 1)
    (h₂ : ∀ q ∈ c₂, q.2 = 0 ∨ q.2 = 1) (h₃ : ∀ q ∈ c₃, q.2 = 0 ∨ q.2 = 1)
    (hd : ∀ q ∈ ds, q.2 = 0 ∨ q.2 = 1)
    (hb₀ : (c₀.map Prod.fst).sum < 2 ^ 32) (hb₁ : (c₁.map Prod.fst).sum < 2 ^ 32)
    (hb₂ : (c₂.map Prod.fst).sum < 2 ^ 32) (hb₃ : (c₃.map Prod.fst).sum < 2 ^ 32)
    (hdb : (ds.map Prod.fst).sum < 2 ^ 32)
    (hnp : 4 * 2 ^ 32 ≤ p)
    (hz : z = ((c₀ ++ c₁ ++ c₂ ++ c₃).map (fun q => (q.1 : F) * q.2)).sum
              - (ds.map (fun q => (q.1 : F) * q.2)).sum)
    (hroot : wrapPoly 4 ((2 ^ 32 : Nat) : F) z = 0) :
    ∃ A B C D P : Nat,
      (c₀.map (fun q => (q.1 : F) * q.2)).sum = (A : F) ∧
      (c₁.map (fun q => (q.1 : F) * q.2)).sum = (B : F) ∧
      (c₂.map (fun q => (q.1 : F) * q.2)).sum = (C : F) ∧
      (c₃.map (fun q => (q.1 : F) * q.2)).sum = (D : F) ∧
      (ds.map (fun q => (q.1 : F) * q.2)).sum = (P : F) ∧
      A < 2 ^ 32 ∧ B < 2 ^ 32 ∧ C < 2 ^ 32 ∧ D < 2 ^ 32 ∧ P < 2 ^ 32 ∧
      P = SHA256.w32 (A + B + C + D) := by
  obtain ⟨A, hAv, hAb⟩ := sum_of_bits c₀ h₀
  obtain ⟨B, hBv, hBb⟩ := sum_of_bits c₁ h₁
  obtain ⟨C, hCv, hCb⟩ := sum_of_bits c₂ h₂
  obtain ⟨D, hDv, hDb⟩ := sum_of_bits c₃ h₃
  obtain ⟨P, hPv, hPb⟩ := sum_of_bits ds hd
  refine ⟨A, B, C, D, P, hAv, hBv, hCv, hDv, hPv,
    lt_of_le_of_lt hAb hb₀, lt_of_le_of_lt hBb hb₁, lt_of_le_of_lt hCb hb₂,
    lt_of_le_of_lt hDb hb₃, lt_of_le_of_lt hPb hdb, ?_⟩
  have hsum : ((c₀ ++ c₁ ++ c₂ ++ c₃).map (fun q => (q.1 : F) * q.2)).sum
      = ((A + B + C + D : Nat) : F) := by
    rw [List.map_append, List.map_append, List.map_append, List.sum_append, List.sum_append,
      List.sum_append, hAv, hBv, hCv, hDv]
    push_cast; ring
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hCbd : A + B + C + D < 4 * 2 ^ 32 := by omega
  show P = (A + B + C + D) % 2 ^ 32
  exact wrap_sum_of_zero 4 (A + B + C + D) P z hCbd (lt_of_le_of_lt hPb hdb) hnp
    (by rw [hz, hsum, hPv]) hroot

/-- **The `n = 6` case**: five bit groups and the round constant `K`.

    The `round_step` assertions differ from the schedule's in one way that matters here — one of
    their addends is not a witnessed word but a compile-time constant. Measured on the artifact it
    appears as a single constant term in the cone's merged linear node (`0x428a2f98` for round 0),
    which is how the generator recovers the round index. So `K` enters as a `Nat` parameter, not
    as a group, and only the bound `K < 2 ^ 32` is needed of it. -/
theorem wrap_six_words {p : Nat} [CharP F p] (c₀ c₁ c₂ c₃ c₄ ds : List (Nat × F))
    (K : Nat) (z : F)
    (h₀ : ∀ q ∈ c₀, q.2 = 0 ∨ q.2 = 1) (h₁ : ∀ q ∈ c₁, q.2 = 0 ∨ q.2 = 1)
    (h₂ : ∀ q ∈ c₂, q.2 = 0 ∨ q.2 = 1) (h₃ : ∀ q ∈ c₃, q.2 = 0 ∨ q.2 = 1)
    (h₄ : ∀ q ∈ c₄, q.2 = 0 ∨ q.2 = 1) (hd : ∀ q ∈ ds, q.2 = 0 ∨ q.2 = 1)
    (hb₀ : (c₀.map Prod.fst).sum < 2 ^ 32) (hb₁ : (c₁.map Prod.fst).sum < 2 ^ 32)
    (hb₂ : (c₂.map Prod.fst).sum < 2 ^ 32) (hb₃ : (c₃.map Prod.fst).sum < 2 ^ 32)
    (hb₄ : (c₄.map Prod.fst).sum < 2 ^ 32) (hdb : (ds.map Prod.fst).sum < 2 ^ 32)
    (hK : K < 2 ^ 32) (hnp : 6 * 2 ^ 32 ≤ p)
    (hz : z = ((c₀ ++ c₁ ++ c₂ ++ c₃ ++ c₄).map (fun q => (q.1 : F) * q.2)).sum + (K : F)
              - (ds.map (fun q => (q.1 : F) * q.2)).sum)
    (hroot : wrapPoly 6 ((2 ^ 32 : Nat) : F) z = 0) :
    ∃ A B C D E P : Nat,
      (c₀.map (fun q => (q.1 : F) * q.2)).sum = (A : F) ∧
      (c₁.map (fun q => (q.1 : F) * q.2)).sum = (B : F) ∧
      (c₂.map (fun q => (q.1 : F) * q.2)).sum = (C : F) ∧
      (c₃.map (fun q => (q.1 : F) * q.2)).sum = (D : F) ∧
      (c₄.map (fun q => (q.1 : F) * q.2)).sum = (E : F) ∧
      (ds.map (fun q => (q.1 : F) * q.2)).sum = (P : F) ∧
      A < 2 ^ 32 ∧ B < 2 ^ 32 ∧ C < 2 ^ 32 ∧ D < 2 ^ 32 ∧ E < 2 ^ 32 ∧ P < 2 ^ 32 ∧
      P = SHA256.w32 (A + B + C + D + E + K) := by
  obtain ⟨A, hAv, hAb⟩ := sum_of_bits c₀ h₀
  obtain ⟨B, hBv, hBb⟩ := sum_of_bits c₁ h₁
  obtain ⟨C, hCv, hCb⟩ := sum_of_bits c₂ h₂
  obtain ⟨D, hDv, hDb⟩ := sum_of_bits c₃ h₃
  obtain ⟨E, hEv, hEb⟩ := sum_of_bits c₄ h₄
  obtain ⟨P, hPv, hPb⟩ := sum_of_bits ds hd
  refine ⟨A, B, C, D, E, P, hAv, hBv, hCv, hDv, hEv, hPv,
    lt_of_le_of_lt hAb hb₀, lt_of_le_of_lt hBb hb₁, lt_of_le_of_lt hCb hb₂,
    lt_of_le_of_lt hDb hb₃, lt_of_le_of_lt hEb hb₄, lt_of_le_of_lt hPb hdb, ?_⟩
  have hsum : ((c₀ ++ c₁ ++ c₂ ++ c₃ ++ c₄).map (fun q => (q.1 : F) * q.2)).sum + (K : F)
      = ((A + B + C + D + E + K : Nat) : F) := by
    simp only [List.map_append, List.sum_append, hAv, hBv, hCv, hDv, hEv]
    push_cast; ring
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hCbd : A + B + C + D + E + K < 6 * 2 ^ 32 := by omega
  show P = (A + B + C + D + E + K) % 2 ^ 32
  exact wrap_sum_of_zero 6 (A + B + C + D + E + K) P z hCbd (lt_of_le_of_lt hPb hdb) hnp
    (by rw [hz, hsum, hPv]) hroot

/-- **The `n = 7` case**: six bit groups and the round constant. -/
theorem wrap_seven_words {p : Nat} [CharP F p] (c₀ c₁ c₂ c₃ c₄ c₅ ds : List (Nat × F))
    (K : Nat) (z : F)
    (h₀ : ∀ q ∈ c₀, q.2 = 0 ∨ q.2 = 1) (h₁ : ∀ q ∈ c₁, q.2 = 0 ∨ q.2 = 1)
    (h₂ : ∀ q ∈ c₂, q.2 = 0 ∨ q.2 = 1) (h₃ : ∀ q ∈ c₃, q.2 = 0 ∨ q.2 = 1)
    (h₄ : ∀ q ∈ c₄, q.2 = 0 ∨ q.2 = 1) (h₅ : ∀ q ∈ c₅, q.2 = 0 ∨ q.2 = 1)
    (hd : ∀ q ∈ ds, q.2 = 0 ∨ q.2 = 1)
    (hb₀ : (c₀.map Prod.fst).sum < 2 ^ 32) (hb₁ : (c₁.map Prod.fst).sum < 2 ^ 32)
    (hb₂ : (c₂.map Prod.fst).sum < 2 ^ 32) (hb₃ : (c₃.map Prod.fst).sum < 2 ^ 32)
    (hb₄ : (c₄.map Prod.fst).sum < 2 ^ 32) (hb₅ : (c₅.map Prod.fst).sum < 2 ^ 32)
    (hdb : (ds.map Prod.fst).sum < 2 ^ 32)
    (hK : K < 2 ^ 32) (hnp : 7 * 2 ^ 32 ≤ p)
    (hz : z = ((c₀ ++ c₁ ++ c₂ ++ c₃ ++ c₄ ++ c₅).map (fun q => (q.1 : F) * q.2)).sum + (K : F)
              - (ds.map (fun q => (q.1 : F) * q.2)).sum)
    (hroot : wrapPoly 7 ((2 ^ 32 : Nat) : F) z = 0) :
    ∃ A B C D E G P : Nat,
      (c₀.map (fun q => (q.1 : F) * q.2)).sum = (A : F) ∧
      (c₁.map (fun q => (q.1 : F) * q.2)).sum = (B : F) ∧
      (c₂.map (fun q => (q.1 : F) * q.2)).sum = (C : F) ∧
      (c₃.map (fun q => (q.1 : F) * q.2)).sum = (D : F) ∧
      (c₄.map (fun q => (q.1 : F) * q.2)).sum = (E : F) ∧
      (c₅.map (fun q => (q.1 : F) * q.2)).sum = (G : F) ∧
      (ds.map (fun q => (q.1 : F) * q.2)).sum = (P : F) ∧
      A < 2 ^ 32 ∧ B < 2 ^ 32 ∧ C < 2 ^ 32 ∧ D < 2 ^ 32 ∧ E < 2 ^ 32 ∧ G < 2 ^ 32 ∧
      P < 2 ^ 32 ∧
      P = SHA256.w32 (A + B + C + D + E + G + K) := by
  obtain ⟨A, hAv, hAb⟩ := sum_of_bits c₀ h₀
  obtain ⟨B, hBv, hBb⟩ := sum_of_bits c₁ h₁
  obtain ⟨C, hCv, hCb⟩ := sum_of_bits c₂ h₂
  obtain ⟨D, hDv, hDb⟩ := sum_of_bits c₃ h₃
  obtain ⟨E, hEv, hEb⟩ := sum_of_bits c₄ h₄
  obtain ⟨G, hGv, hGb⟩ := sum_of_bits c₅ h₅
  obtain ⟨P, hPv, hPb⟩ := sum_of_bits ds hd
  refine ⟨A, B, C, D, E, G, P, hAv, hBv, hCv, hDv, hEv, hGv, hPv,
    lt_of_le_of_lt hAb hb₀, lt_of_le_of_lt hBb hb₁, lt_of_le_of_lt hCb hb₂,
    lt_of_le_of_lt hDb hb₃, lt_of_le_of_lt hEb hb₄, lt_of_le_of_lt hGb hb₅,
    lt_of_le_of_lt hPb hdb, ?_⟩
  have hsum : ((c₀ ++ c₁ ++ c₂ ++ c₃ ++ c₄ ++ c₅).map (fun q => (q.1 : F) * q.2)).sum + (K : F)
      = ((A + B + C + D + E + G + K : Nat) : F) := by
    simp only [List.map_append, List.sum_append, hAv, hBv, hCv, hDv, hEv, hGv]
    push_cast; ring
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hCbd : A + B + C + D + E + G + K < 7 * 2 ^ 32 := by omega
  show P = (A + B + C + D + E + G + K) % 2 ^ 32
  exact wrap_sum_of_zero 7 (A + B + C + D + E + G + K) P z hCbd (lt_of_le_of_lt hPb hdb) hnp
    (by rw [hz, hsum, hPv]) hroot

/-- The characteristic side condition, for the `n` the SHA-256 circuit actually uses. P-256's
    prime is 256 bits and `7 · 2^32 < 2^35`, so this is arithmetic, not an assumption. -/
theorem wrap_hnp (n : Nat) (hn : n ≤ 7) :
    n * 2 ^ 32 ≤ 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF := by
  have : n * 2 ^ 32 ≤ 7 * 2 ^ 32 := Nat.mul_le_mul_right _ hn
  omega

end SHA256F
