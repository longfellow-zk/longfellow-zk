import LfzkV2.Joint.RuntimeCost

/-! Work-normalized arithmetic for the joint runtime certificate. The
authenticated raw-proof endpoint uses one joint tree; the smaller-trace case
counts digest guesses directly. -/

namespace LfzkV2.Joint.RuntimeSecurity

open RuntimeCost

theorem tsec_116_of_merkle_ge {p : ℚ} {N tA L : ℕ}
    (hp₁ : p ≤ 1) (hL : L ≤ 1204) (ht : 8 ≤ tA)
    (hp : p ≤ (1+N : ℕ)*coefficient+constant+
      (Bcs.AdaptiveCommit.adaptiveNumerator 5824 tA (L+(1+N)) : ℚ)/(2^256 : ℚ)) :
    p ≤ (1+N+tA : ℚ)/(2^116 : ℚ) := by
  by_cases htA : tA ≤ 2^116
  · let A : ℚ := constant+coefficient+((5824*(1+1205) : ℕ) : ℚ)/(2^256 : ℚ)
    let K : ℚ := coefficient+((5824+2^116 : ℕ) : ℚ)/(2^256 : ℚ)
    let T : ℚ := ((3*2^116+2*5824+1+1205 : ℕ) : ℚ)/(2^256 : ℚ)
    have hcountNat : Bcs.AdaptiveCommit.adaptiveNumerator 5824 tA (L+(1+N)) ≤
        5824*(1+1205)+N*(5824+2^116)+tA*(3*2^116+2*5824+1+1205) := by
      rw [show L+(1+N) = (L+1)+N by omega]
      apply (LfzkV1.TSec.adaptiveNumerator_le_linear
        (fc := 5824) (L := L+1) (N := N) htA).trans
      gcongr <;> omega
    have hcount : (Bcs.AdaptiveCommit.adaptiveNumerator 5824 tA (L+(1+N)) : ℚ) ≤
        ((5824*(1+1205) : ℕ) : ℚ)+(N : ℚ)*((5824+2^116 : ℕ) : ℚ)+
          (tA : ℚ)*((3*2^116+2*5824+1+1205 : ℕ) : ℚ) := by
      exact_mod_cast hcountNat
    have hprob : p ≤ A+N*K+tA*T := by
      calc
        p ≤ (1+N : ℕ)*coefficient+constant+
            (Bcs.AdaptiveCommit.adaptiveNumerator 5824 tA (L+(1+N)) : ℚ)/(2^256 : ℚ) := hp
        _ ≤ (1+N : ℕ)*coefficient+constant+
            (((5824*(1+1205) : ℕ) : ℚ)+(N : ℚ)*((5824+2^116 : ℕ) : ℚ)+
              (tA : ℚ)*((3*2^116+2*5824+1+1205 : ℕ) : ℚ))/(2^256 : ℚ) := by gcongr
        _ = A+N*K+tA*T := by dsimp only [A,K,T]; push_cast; ring
    have hbase : A+8*T ≤ 9/(2^116 : ℚ) := by norm_num [A,T,constant,coefficient]
    have hslope : K ≤ 1/(2^116 : ℚ) := by norm_num [K,coefficient]
    have hmerkle : T ≤ 1/(2^116 : ℚ) := by norm_num [T]
    have htq : (8 : ℚ) ≤ tA := by exact_mod_cast ht
    have hstep := mul_le_mul_of_nonneg_left hslope (Nat.cast_nonneg N : (0 : ℚ) ≤ N)
    have htstep := mul_le_mul_of_nonneg_left hmerkle (sub_nonneg.mpr htq)
    have h : p ≤ (1+N+tA : ℚ)*(1/(2^116 : ℚ)) := by
      calc
        p ≤ A+N*K+tA*T := hprob
        _ = (A+8*T)+N*K+(tA-8 : ℚ)*T := by ring
        _ ≤ 9/(2^116 : ℚ)+(N : ℚ)*(1/(2^116 : ℚ))+
            (tA-8 : ℚ)*(1/(2^116 : ℚ)) := add_le_add (add_le_add hbase hstep) htstep
        _ = (1+N+tA : ℚ)*(1/(2^116 : ℚ)) := by ring
    simpa only [mul_one_div] using h
  · apply hp₁.trans
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2^116)).mpr
    have hlarge : (2^116 : ℚ) ≤ tA := by exact_mod_cast (by omega : 2^116 ≤ tA)
    have hnonneg : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    linarith

end LfzkV2.Joint.RuntimeSecurity
