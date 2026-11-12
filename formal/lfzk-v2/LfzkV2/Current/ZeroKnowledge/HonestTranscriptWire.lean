import LfzkV2.Current.ZeroKnowledge.HonestTranscriptRoles

/-! The optional write at every frontend slot decodes to the same logical
message as the existing frontend writer. Empty assertion slots and the
shared input boundary are included in this identity. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.Prefix
open SumcheckV2
open scoped Classical
variable {F : Type} [Field F]

omit [Field F] in
theorem writeFrom_before {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Layered.Replay.Payload circuit) (start q : ℕ) (before : q ≤ start) :
    FrontendTranscript.writeFrom circuit payload start q = .empty := by
  induction circuit generalizing start with
  | input => rfl
  | entry _ _ _ ih => exact ih payload start before
  | @layer out mid input assertions body rest ih =>
      have round : ¬ (start+1 ≤ q ∧ q < start+1+mid) := by omega
      have cross : q ≠ start+1+mid := by omega
      have claims : q ≠ start+mid+2 := by omega
      simp only [FrontendTranscript.writeFrom,dif_neg round,cross,claims,↓reduceIte]
      apply ih
      split_ifs <;> omega

omit [Field F] in
theorem writeFrom_translate {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Layered.Replay.Payload circuit) (start q shift : ℕ) :
    FrontendTranscript.writeFrom circuit payload (start+shift) (q+shift) =
      FrontendTranscript.writeFrom circuit payload start q := by
  induction circuit generalizing start q with
  | input => rfl
  | entry _ _ _ ih => exact ih payload start q
  | @layer out mid input assertions body rest ih =>
      by_cases round : start+1 ≤ q ∧ q < start+1+mid
      · have shifted : start+shift+1 ≤ q+shift ∧ q+shift < start+shift+1+mid := by omega
        simp only [FrontendTranscript.writeFrom,dif_pos round,dif_pos shifted]
        congr 2
        apply Fin.ext
        change q+shift-(start+shift+1) = q-(start+1)
        omega
      · have shifted : ¬ (start+shift+1 ≤ q+shift ∧ q+shift < start+shift+1+mid) := by omega
        simp only [FrontendTranscript.writeFrom,dif_neg round,dif_neg shifted]
        by_cases cross : q = start+1+mid
        · have shiftedCross : q+shift = start+shift+1+mid := by omega
          rw [if_pos cross,if_pos shiftedCross]
        · have shiftedCross : q+shift ≠ start+shift+1+mid := by omega
          rw [if_neg cross,if_neg shiftedCross]
          by_cases claims : q = start+mid+2
          · have shiftedClaims : q+shift = start+shift+mid+2 := by omega
            rw [if_pos claims,if_pos shiftedClaims]
          · have shiftedClaims : q+shift ≠ start+shift+mid+2 := by omega
            rw [if_neg claims,if_neg shiftedClaims]
            cases h : FrontendReplay.hasLayers rest <;>
              simpa [h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
                ih payload.2 (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2) q

omit [Field F] in
theorem circuit_continue {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (payload : Layered.Replay.Payload body)
    (layers : FrontendReplay.hasLayers body = true) :
    Prefix.circuit plan payload true = Prefix.circuit plan payload false := by
  cases plan <;> try rfl
  all_goals simp only [FrontendReplay.hasLayers,Bool.false_eq_true] at layers

omit [Field F] in
theorem layer_wire {out mid input assertions : ℕ}
    (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F)
    (rest : Layered.Circuit F mid input) (tail : FrontendSchedule.Plan F rest)
    (payload : Layered.Replay.Payload (.layer assertions body rest))
    (induction : ∀ q, q < FrontendReplay.slots rest →
      ((Prefix.circuit tail payload.2 false)[q]?).map (fun item => item.getD .empty) =
        some (FrontendTranscript.write rest payload.2 q))
    (q : ℕ) (bound : q < FrontendReplay.slots (.layer assertions body rest)) :
    ((none :: layer payload.1 ++ Prefix.circuit tail payload.2 true)[q]?).map (fun item => item.getD .empty) =
      some (FrontendTranscript.write (.layer assertions body rest) payload q) := by
  cases q with
  | zero =>
      rw [List.cons_append,List.getElem?_cons_zero]
      rw [FrontendTranscript.write,writeFrom_before _ _ 0 0 (le_refl _)]
      rfl
  | succ q =>
      simp only [List.cons_append,List.getElem?_cons_succ,layer,rounds,List.append_assoc]
      by_cases round : q < mid
      · rw [List.getElem?_append_left (by simpa only [List.length_ofFn] using round)]
        simp only [List.getElem?_ofFn,round,↓reduceDIte,Option.map_some,Option.getD_some]
        have inRound : 0+1 ≤ q+1 ∧ q+1 < 0+1+mid := by omega
        simp only [FrontendTranscript.write,FrontendTranscript.writeFrom,dif_pos inRound]
        congr 2
      · rw [List.getElem?_append_right (by simpa only [List.length_ofFn] using Nat.le_of_not_gt round)]
        simp only [List.length_ofFn]
        by_cases cross : q = mid
        · subst q
          simp only [Nat.sub_self,List.getElem?_cons_zero,Option.map_some,Option.getD_some]
          have notRound : ¬ (0+1 ≤ mid+1 ∧ mid+1 < 0+1+mid) := by omega
          have isCross : mid+1 = 0+1+mid := by omega
          simp only [FrontendTranscript.write,FrontendTranscript.writeFrom,dif_neg notRound,if_pos isCross]
        · by_cases claims : q = mid+1
          · subst q
            have index : mid+1-mid = 1 := by omega
            simp only [index,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.map_some,Option.getD_some]
            have notRound : ¬ (0+1 ≤ mid+1+1 ∧ mid+1+1 < 0+1+mid) := by omega
            have notCross : mid+1+1 ≠ 0+1+mid := by omega
            have isClaims : mid+1+1 = 0+mid+2 := by omega
            simp only [FrontendTranscript.write,FrontendTranscript.writeFrom,dif_neg notRound,
              if_neg notCross,if_pos isClaims]
          · have after : 2 ≤ q-mid := by omega
            simp only [List.getElem?_cons,if_neg (show q-mid ≠ 0 by omega),
              if_neg (show q-mid-1 ≠ 0 by omega),List.nil_append]
            have index : q-mid-1-1 = q-(mid+2) := by omega
            rw [index]
            by_cases layers : FrontendReplay.hasLayers rest = true
            · have restBound : q-(mid+2) < FrontendReplay.slots rest := by
                simp only [FrontendReplay.slots,layers,↓reduceIte] at bound
                omega
              rw [circuit_continue tail payload.2 layers,induction _ restBound]
              have notRound : ¬ (0+1 ≤ q+1 ∧ q+1 < 0+1+mid) := by omega
              have notCross : q+1 ≠ 0+1+mid := by omega
              have notClaims : q+1 ≠ 0+mid+2 := by omega
              simp only [FrontendTranscript.write,FrontendTranscript.writeFrom,dif_neg notRound,
                if_neg notCross,if_neg notClaims,layers,↓reduceIte]
              have shifted := writeFrom_translate rest payload.2 0 (q-(mid+2)) (mid+3)
              simp only [Nat.zero_add] at shifted
              rw [show q+1 = (q-(mid+2))+(mid+3) by omega]
              simpa only [Nat.zero_add] using congrArg some shifted.symm
            · simp only [FrontendReplay.slots,layers,Bool.false_eq_true,↓reduceIte] at bound
              omega

omit [Field F] in
theorem circuit_wire {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (payload : Layered.Replay.Payload body)
    (q : ℕ) (bound : q < FrontendReplay.slots body) :
    ((Prefix.circuit plan payload false)[q]?).map (fun item => item.getD .empty) =
      some (FrontendTranscript.write body payload q) := by
  induction plan generalizing q with
  | input =>
      have zero : q = 0 := by simpa only [FrontendReplay.slots] using Nat.lt_one_iff.mp bound
      subst q
      rfl
  | inputEntry =>
      have zero : q = 0 := by simpa only [FrontendReplay.slots] using Nat.lt_one_iff.mp bound
      subst q
      rfl
  | layer _ tail ih => exact layer_wire _ _ tail payload (ih payload.2) q bound
  | entryLayer _ _ _ tail ih => exact layer_wire _ _ tail payload (ih payload.2) q bound

end LfzkV2.Current.ZeroKnowledge.Frontend.Prefix
