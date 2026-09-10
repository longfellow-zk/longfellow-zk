/-
# The two-addend wrap, with bounds

`SHA256F.wrap_two_words` returns the three `Nat`s but not their ranges, and
`SHA256F.group_val_eq'` needs `A < p` to identify a group's value with `ofBits` of its bits.

This lives in its own module rather than in `S2TmplNat` on purpose: that file is imported by
every generated bridge in the tree, so touching it invalidates about forty modules and several
hours of `decide +kernel`. A leaf module costs one rebuild.

The four-, six- and seven-addend versions already carry their bounds, so only `n = 2` needs this.
-/

import quadcert.Bridge.Sha256.S2TmplNat

namespace SHA256F

variable {F : Type} [Field F]

/-- `wrap_two_words`, with the ranges of the three words. -/
theorem wrap_two_words' {p : Nat} [CharP F p] (csA csB ds : List (Nat × F)) (z : F)
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
      A < 2 ^ 32 ∧ B < 2 ^ 32 ∧ P < 2 ^ 32 ∧
      P = SHA256.w32 (A + B) := by
  obtain ⟨A, hAv, hAbd⟩ := sum_of_bits csA hA
  obtain ⟨B, hBv, hBbd⟩ := sum_of_bits csB hB
  obtain ⟨P, hPv, hPbd⟩ := sum_of_bits ds hd
  refine ⟨A, B, P, hAv, hBv, hPv, lt_of_le_of_lt hAbd hAb, lt_of_le_of_lt hBbd hBb,
    lt_of_le_of_lt hPbd hdb, ?_⟩
  have hsum : ((csA ++ csB).map (fun q => (q.1 : F) * q.2)).sum = ((A + B : Nat) : F) := by
    rw [List.map_append, List.sum_append, hAv, hBv]; push_cast; ring
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hCb : A + B < 2 * 2 ^ 32 := by omega
  show P = (A + B) % 2 ^ 32
  exact wrap_sum_of_zero 2 (A + B) P z hCb (lt_of_le_of_lt hPbd hdb) hnp
    (by rw [hz, hsum, hPv]) hroot

end SHA256F
