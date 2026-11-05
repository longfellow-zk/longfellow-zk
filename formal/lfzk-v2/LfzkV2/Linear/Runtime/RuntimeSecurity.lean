import LfzkV2.Linear.Runtime.RuntimeCost

/-! Work-normalized arithmetic for the packed runtime certificate. The
authenticated raw-proof endpoint applies this bound when at least eight
Merkle queries were made; the smaller case counts digest guesses directly. -/

namespace LfzkV2.Linear.Runtime.RuntimeSecurity

open RuntimeCost

theorem slots_le {F₁ F₂ : Type} {out₁ input₁ out₂ input₂ : ℕ}
    (circuit₁ : Native.Circuit F₁ out₁ input₁) (circuit₂ : Native.Circuit F₂ out₂ input₂)
    (hfront₁ : out₁+circuit₁.sharpLayerBudget ≤ 593)
    (hfront₂ : out₂+circuit₂.sharpLayerBudget ≤ 565)
    (hlayers₁ : circuit₁.layers ≤ 20) (hlayers₂ : circuit₂.layers ≤ 21) :
    1+(LfzkV2.Linear.Replay.slots circuit₁+1+2)+(LfzkV2.Linear.Replay.slots circuit₂+2) ≤ 1205 := by
  have hs {F : Type} {out input : ℕ} (circuit : Native.Circuit F out input) :
      LfzkV2.Linear.Replay.slots circuit = LfzkV2.Replay.slots circuit.shape + circuit.layers := by
    have h : LfzkV2.Linear.Replay.layerSlots circuit =
        LfzkV2.Replay.layerSlots circuit.shape + circuit.layers := by
      induction circuit with
      | input => rfl
      | layer a body rest ih =>
          simp only [LfzkV2.Linear.Replay.layerSlots, Native.Circuit.shape,
            LfzkV2.Replay.layerSlots, Native.Circuit.layers]
          omega
    simp only [LfzkV2.Linear.Replay.slots, LfzkV2.Replay.slots, h]
    omega
  have h₁ := (circuit₁.replay_slots_le_budget).trans hfront₁
  have h₂ := (circuit₂.replay_slots_le_budget).trans hfront₂
  rw [hs, hs]
  omega

theorem tsec_116_of_merkle_ge {p : ℚ} {N tA L : ℕ}
    (hp₁ : p ≤ 1) (hL : L ≤ 1205) (ht : 8 ≤ tA)
    (hp : p ≤ (1+N : ℕ)*coefficient+constant+
      2*(Bcs.AdaptiveCommit.adaptiveNumerator 11648 tA (L+(1+N)) : ℚ)/(2^256 : ℚ)) :
    p ≤ (1+N+tA : ℚ)/(2^116 : ℚ) := by
  by_cases htA : tA ≤ 2^116
  · let A : ℚ := constant+coefficient+2*((11648*(1+1206) : ℕ) : ℚ)/(2^256 : ℚ)
    let K : ℚ := coefficient+2*((11648+2^116 : ℕ) : ℚ)/(2^256 : ℚ)
    let T : ℚ := 2*((3*2^116+2*11648+1+1206 : ℕ) : ℚ)/(2^256 : ℚ)
    have hcountNat : Bcs.AdaptiveCommit.adaptiveNumerator 11648 tA (L+(1+N)) ≤
        11648*(1+1206)+N*(11648+2^116)+tA*(3*2^116+2*11648+1+1206) := by
      rw [show L+(1+N) = (L+1)+N by omega]
      apply (LfzkV1.TSec.adaptiveNumerator_le_linear
        (fc := 11648) (L := L+1) (N := N) htA).trans
      gcongr <;> omega
    have hcount : (Bcs.AdaptiveCommit.adaptiveNumerator 11648 tA (L+(1+N)) : ℚ) ≤
        ((11648*(1+1206) : ℕ) : ℚ)+(N : ℚ)*((11648+2^116 : ℕ) : ℚ)+
          (tA : ℚ)*((3*2^116+2*11648+1+1206 : ℕ) : ℚ) := by
      exact_mod_cast hcountNat
    have hprob : p ≤ A+N*K+tA*T := by
      calc
        p ≤ (1+N : ℕ)*coefficient+constant+
            2*(Bcs.AdaptiveCommit.adaptiveNumerator 11648 tA (L+(1+N)) : ℚ)/(2^256 : ℚ) := hp
        _ ≤ (1+N : ℕ)*coefficient+constant+2*
            (((11648*(1+1206) : ℕ) : ℚ)+(N : ℚ)*((11648+2^116 : ℕ) : ℚ)+
              (tA : ℚ)*((3*2^116+2*11648+1+1206 : ℕ) : ℚ))/(2^256 : ℚ) := by gcongr
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

end LfzkV2.Linear.Runtime.RuntimeSecurity
