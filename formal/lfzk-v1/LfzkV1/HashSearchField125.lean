import LfzkV1.HashFieldProfile125
import LfzkV1.TwoFieldCover125

/-! Field charges on the actual two-field search. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.HashSearchField125

open Finset Bcs.TotalOracle Bcs.TotalOracleCommit Merkle.MH Merkle.RandomOracle
open LfzkV1.CertifiedV1 LfzkV1.SoundnessAudit LfzkV1.CompiledZk
open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.NizkAdaptiveTwoField (SideCtx)
open LfzkV1.NizkDeployedHash LfzkV1.NizkDeployedHashTwoField LfzkV1.TwoFieldCover125
open scoped Classical

variable {C D K Enc Early X MsgH MsgS Out Salt F : Type}
variable [Fintype C] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
variable [Inhabited Salt] [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
variable [Inhabited MsgH] [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS]
variable {M nt nlin tA N L TM : ℕ}
variable {i : Fin 4} {hR : (v7HashRow i).Valid} {hr : 0 < (v7HashRow i).params.row.openings}
variable {codec : Codec Salt (Col F (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {dec : RoleDecoders codec}

local notation "HPoint" => HashFieldProfile125.HashPoint i (SideCtx D K Early) MsgH
local notation "Pt" => SignatureBudget125.PairPoint D K Early MsgH MsgS (v7HashRow i)

variable (Side : CircuitSide (v7HashRow i) hR hr (v7HashLogv i) C F MsgH M nt nlin X dec Prod.fst)
variable (S : Setup Enc D (SignatureBudget125.PairPoint D K Early MsgH MsgS (v7HashRow i))
    C Out (D × D) tA N L) (mt : Fin TM → D)
variable (represent : K → C) (publicOf : Early → X)

/-- The field test reads the actual side-1 ancestors and the cut named by
this point. Its final answer is a separate argument. -/
def bad (H : Pt → C) (p : Pt) (coin : C) : Prop :=
  match p with
  | .inr (.inl q) =>
    let cut := (S.atOracle H).ctxAt mt Setup.emptyTape (S.key p)
    let σ := (cut, represent q.ctx.2.1, publicOf q.ctx.2.2)
    let oracle (point : HPoint) := H (Sum.inr (Sum.inl point))
    HashFieldProfile125.bad Side σ q (mpoints.chal oracle q) coin
  | _ => False

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
theorem bad_off (p : Pt) {H H' : Pt → C} (hoff : AgreeOff p H H') (coin : C) :
    bad Side S mt represent publicOf H p coin ↔ bad Side S mt represent publicOf H' p coin := by
  rcases p with p | p | p
  · rfl
  · let q : Pt := .inr (.inl p)
    have hcut := S.ctxAt_off mt H H' q hoff
    have hop : AgreeOff p (fun x : HPoint => H (Sum.inr (Sum.inl x)))
        (fun x : HPoint => H' (Sum.inr (Sum.inl x))) :=
      fun x h => hoff _ (fun he => h (Sum.inl.inj (Sum.inr.inj he)))
    have hchal := mpoints.chal_congr hop
    dsimp only [bad]
    rw [hcut, hchal]
  · rfl

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
theorem bad_sum_le [Nonempty C] (p : Pt) (H : Pt → C) :
    (∑ coin : C, if bad Side S mt represent publicOf H p coin then (1 : ℚ) else 0) ≤
      Fintype.card C * (7 / 2^128) := by
  rcases p with p | p | p
  · simp [bad]
  · dsimp only [bad]
    have h := HashFieldProfile125.bad_sum_le Side
      ((S.atOracle H).ctxAt mt Setup.emptyTape (S.key (Sum.inr (Sum.inl p))),
        represent p.ctx.2.1, publicOf p.ctx.2.2)
      p (mpoints.chal (fun x => H (Sum.inr (Sum.inl x))) p)
    refine h.trans ?_
    split_ifs
    · exact le_rfl
    · gcongr
      norm_num
  · simp [bad]

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
theorem field_role_of_bad (H : Pt → C) (p : Pt) (coin : C)
    (hp : bad Side S mt represent publicOf H p coin) : queryRole p = .field := by
  rcases p with p | p | p
  · cases hp
  · have hslot := HashFieldProfile125.bad_field_slot Side _ p _ _ hp
    cases hrole : p.role <;> simp [queryRole, hrole, Rounds.Role.slot] at hslot ⊢
  · cases hp

section Counting

variable [Fintype D] [Fintype K] [Fintype Early] [Fintype MsgH] [Fintype MsgS] [Nonempty C]

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
/-- Charge a bad field address only when the adversary actually queried it.
The exact expected count fits the common original-query budget. -/
theorem observed_field_count_le :
    ((univ.filter fun H : Pt → C => ∃ p ∈ observedRole (S.search mt) .field H,
      bad Side S mt represent publicOf H p (H p)).card : ℚ) ≤
      (7 / 2^128) * ∑ H : Pt → C, ((observedRole (S.search mt) .field H).card : ℚ) := by
  classical
  let seen (p : Pt) (H : Pt → C) := p ∈ observedRole (S.search mt) .field H
  let event (p : Pt) (H : Pt → C) (coin : C) := bad Side S mt represent publicOf H p coin
  have hseen (p : Pt) (H H' : Pt → C) (h : AgreeOff p H H') : seen p H ↔ seen p H' := by
    simp only [seen, observedRole, MacCharge125.observedKeys, mem_filter, List.mem_toFinset]
    rw [mem_queried_iff (S.search mt) p h]
  have hloc (p : Pt) (H : Pt → C) :
      (∑ a : C, @ite ℚ (event p H a) (Classical.propDecidable _) 1 0) ≤
      Fintype.card C * (7 / 2^128) := by
    exact bad_sum_le Side S mt represent publicOf p H
  have hl := CanonicalOpening125.causal_sum_le id seen hseen event (7 / 2^128)
    (fun p _ _ h a => bad_off Side S mt represent publicOf p h a) hloc
  have hcount (H : Pt → C) :
      (∑ p : Pt, @ite ℚ (seen p H) (Classical.propDecidable _) 1 0) =
      ((observedRole (S.search mt) .field H).card : ℚ) := by
    letI : DecidablePred (fun p : Pt => seen p H) := fun _ => Classical.propDecidable _
    rw [← sum_filter (fun p : Pt => seen p H) (fun _ => (1 : ℚ))]
    have hfilter : (univ.filter fun p => seen p H) = observedRole (S.search mt) .field H := by
      ext p
      simp [seen]
    rw [hfilter]
    simp
  simp only [hcount] at hl
  let active (H : Pt → C) := ∃ p, seen p H ∧ event p H (H p)
  calc
    _ = ∑ H : Pt → C, (if active H then (1 : ℚ) else 0) := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one, active, seen, event]
    _ ≤ ∑ H : Pt → C, ∑ p : Pt,
        @ite ℚ (seen p H ∧ event p H (H p)) (Classical.propDecidable _) 1 0 := by
      apply sum_le_sum
      intro H _
      by_cases h : active H
      · obtain ⟨p, hp⟩ := h
        simpa only [if_pos (show active H from ⟨p, hp⟩), if_pos hp] using
          (single_le_sum (f := fun p =>
            @ite ℚ (seen p H ∧ event p H (H p)) (Classical.propDecidable _) 1 0)
            (fun _ _ => by split <;> positivity) (mem_univ p))
      · rw [if_neg h]
        exact sum_nonneg fun _ _ => by split <;> positivity
    _ ≤ _ := hl

end Counting

end LfzkV1.HashSearchField125
