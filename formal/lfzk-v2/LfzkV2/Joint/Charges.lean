import LfzkV2.Joint.Replay
import LfzkV2.TwoFieldPotential

/-!
# Charges on the joint transcript

Each field keeps its own algebraic potential. At the common opening point
both residual charges are added before averaging over the single challenge.
This is a union bound on correlated events; no independence is used.
-/

namespace LfzkV2.Joint.Charges

open Finset RecursivePolygero Bcs.TotalOracle Replay
open scoped Classical

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : Linear.Runtime.CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : Linear.Runtime.CompiledSide F₂ C (Side.Frontend S₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

noncomputable def one (W : I₁.layer.Oracle) (p : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot p) → C) (c : C) : ℚ :=
  match localOne S₁ S₂ p with
  | some x => S₁.charge W x (firstPrefix S₁ S₂ p pref x) c
  | none => 0

noncomputable def two (W : I₂.layer.Oracle) (p : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot p) → C) (c : C) : ℚ :=
  match localTwo S₁ S₂ p with
  | some x => S₂.charge W x (secondPrefix S₁ S₂ p pref x) c
  | none => 0

noncomputable def budgetOne (p : Domain S₁ S₂) : ℚ :=
  match localOne S₁ S₂ p with | some x => S₁.budget x | none => 0

noncomputable def budgetTwo (p : Domain S₁ S₂) : ℚ :=
  match localTwo S₁ S₂ p with | some x => S₂.budget x | none => 0

noncomputable def mac (W : I₁.layer.Oracle × I₂.layer.Oracle) (c : C) : ℚ :=
  indicator (M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff)
    (Counting.committedCandidates I₂ W.2 S₂.cutoff) c)

noncomputable def charge (W : I₁.layer.Oracle × I₂.layer.Oracle) (p : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot p) → C) (c : C) : ℚ :=
  (if (points S₁ S₂).slot p = 0 then mac S₁ S₂ M W c else 0) +
    one S₁ S₂ W.1 p pref c + two S₁ S₂ W.2 p pref c

noncomputable def budget (p : Domain S₁ S₂) : ℚ :=
  (if (points S₁ S₂).slot p = 0 then (S₁.bound*S₂.bound*M.fiber : ℕ) else 0) +
    budgetOne S₁ S₂ p + budgetTwo S₁ S₂ p

theorem one_nonneg (W : I₁.layer.Oracle) (p : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot p) → C) (c : C) : 0 ≤ one S₁ S₂ W p pref c := by
  unfold one
  split
  · exact S₁.charge_nonneg W _ _ c
  · exact le_rfl

theorem two_nonneg (W : I₂.layer.Oracle) (p : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot p) → C) (c : C) : 0 ≤ two S₁ S₂ W p pref c := by
  unfold two
  split
  · exact S₂.charge_nonneg W _ _ c
  · exact le_rfl

theorem charge_nonneg (W : I₁.layer.Oracle × I₂.layer.Oracle) (p : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot p) → C) (c : C) : 0 ≤ charge S₁ S₂ M W p pref c := by
  have hmac : 0 ≤ (if (points S₁ S₂).slot p = 0 then mac S₁ S₂ M W c else 0) := by
    split_ifs
    · exact indicator_nonneg _
    · exact le_rfl
  exact add_nonneg (add_nonneg hmac (one_nonneg S₁ S₂ W.1 p pref c))
    (two_nonneg S₁ S₂ W.2 p pref c)

theorem budgetOne_nonneg (p : Domain S₁ S₂) : 0 ≤ budgetOne S₁ S₂ p := by
  unfold budgetOne
  split
  · exact S₁.budget_nonneg _
  · exact le_rfl

theorem budgetTwo_nonneg (p : Domain S₁ S₂) : 0 ≤ budgetTwo S₁ S₂ p := by
  unfold budgetTwo
  split
  · exact S₂.budget_nonneg _
  · exact le_rfl

theorem budget_nonneg (p : Domain S₁ S₂) : 0 ≤ budget S₁ S₂ M p := by
  unfold budget
  have hmac : (0 : ℚ) ≤
      (if (points S₁ S₂).slot p = 0 then (S₁.bound*S₂.bound*M.fiber : ℕ) else 0) := by
    split_ifs <;> positivity
  exact add_nonneg (add_nonneg hmac (budgetOne_nonneg S₁ S₂ p)) (budgetTwo_nonneg S₁ S₂ p)

theorem one_sum_le (W : I₁.layer.Oracle) (p : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot p) → C) :
    (∑ c, one S₁ S₂ W p pref c) ≤ budgetOne S₁ S₂ p := by
  unfold one budgetOne
  split
  · exact S₁.charge_sum_le W _ _
  · simp only [sum_const_zero, le_refl]

theorem two_sum_le (W : I₂.layer.Oracle) (p : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot p) → C) :
    (∑ c, two S₁ S₂ W p pref c) ≤ budgetTwo S₁ S₂ p := by
  unfold two budgetTwo
  split
  · exact S₂.charge_sum_le W _ _
  · simp only [sum_const_zero, le_refl]

theorem charge_sum_le (W : I₁.layer.Oracle × I₂.layer.Oracle) (p : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot p) → C) :
    (∑ c, charge S₁ S₂ M W p pref c) ≤ budget S₁ S₂ M p := by
  have hmac : (∑ c, mac S₁ S₂ M W c) ≤ (S₁.bound*S₂.bound*M.fiber : ℕ) :=
    M.charge_sum_le _ _ S₁.bound S₂.bound
      (Counting.committedCandidates_card_le I₁ W.1 S₁.cutoff S₁.bound S₁.cutoff_gt S₁.packing)
      (Counting.committedCandidates_card_le I₂ W.2 S₂.cutoff S₂.bound S₂.cutoff_gt S₂.packing)
  unfold charge budget
  rw [sum_add_distrib, sum_add_distrib]
  apply add_le_add (add_le_add ?_ (one_sum_le S₁ S₂ W.1 p pref)) (two_sum_le S₁ S₂ W.2 p pref)
  split_ifs
  · exact hmac
  · simp only [sum_const_zero, Nat.cast_zero, le_refl]

theorem one_at (W : I₁.layer.Oracle) (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) (j : ℕ) (hj : j < S₁.slots) :
    let p := hashInput S₁ S₂ proof (firstSlot S₁ S₂ j)
    let x := S₁.hashInput (selectedOne S₁ S₂ proof) j
    one S₁ S₂ W p ((points S₁ S₂).chal H p) (H p) =
      S₁.charge W x (S₁.points.chal (firstOracle S₁ S₂ H proof) x)
        (firstOracle S₁ S₂ H proof x) := by
  dsimp only
  rw [one, localOne_at _ _ _ _ hj]
  dsimp only
  rw [firstPrefix_at _ _ _ _ _ hj, firstOracle_at _ _ _ _ _ hj]

theorem two_at (W : I₂.layer.Oracle) (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) (j : ℕ) (hj : j < S₂.slots) :
    let p := hashInput S₁ S₂ proof (secondSlot S₁ S₂ j)
    let x := S₂.hashInput (selectedTwo S₁ S₂ proof) j
    two S₁ S₂ W p ((points S₁ S₂).chal H p) (H p) =
      S₂.charge W x (S₂.points.chal (secondOracle S₁ S₂ H proof) x)
        (secondOracle S₁ S₂ H proof x) := by
  dsimp only
  rw [two, localTwo_at _ _ _ _ hj]
  dsimp only
  rw [secondPrefix_at _ _ _ _ _ hj, secondOracle_at _ _ _ _ _ hj]

end LfzkV2.Joint.Charges
