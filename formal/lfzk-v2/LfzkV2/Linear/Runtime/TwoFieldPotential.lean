import LfzkV2.Linear.Runtime.TwoFieldReplay

/-! The merged charge for native sides: a shared affine MAC challenge,
then the actual packing/frontend/backend charge of each side. -/

namespace LfzkV2.Linear.Runtime.TwoFieldPotential

open Finset RecursivePolygero Bcs.TotalOracle TwoFieldReplay
open scoped Classical

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C S₁.Selected circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

def sliceOne (p : S₁.Domain)
    (pref : Fin ((points S₁ S₂).slot (.inr (.inl p))) → C) :
    Fin ((S₁.points).slot p) → C :=
  fun i => pref ⟨1+i.val,by change 1+i.val < 1+(S₁.points).slot p; omega⟩

def sliceTwo (p : S₂.Domain)
    (pref : Fin ((points S₁ S₂).slot (.inr (.inr p))) → C) :
    Fin ((S₂.points).slot p) → C :=
  fun i => pref ⟨1+S₁.slots+i.val,by
    change 1+S₁.slots+i.val <
      1+S₁.slots+(S₂.points).slot p
    omega⟩

noncomputable def charge (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (point : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot point) → C) (c : C) : ℚ :=
  match point with
  | .inl _ => RecursivePolygero.indicator
    (M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff) (Counting.committedCandidates I₂ W.2 S₂.cutoff) c)
  | .inr (.inl p) => S₁.charge W.1 p (sliceOne S₁ S₂ p pref) c
  | .inr (.inr p) => S₂.charge W.2 p (sliceTwo S₁ S₂ p pref) c

noncomputable def budget (point : Domain S₁ S₂) : ℚ :=
  match point with
  | .inl _ => (S₁.bound*S₂.bound*M.fiber : ℕ)
  | .inr (.inl p) => S₁.budget p
  | .inr (.inr p) => S₂.budget p

theorem charge_nonneg (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (point : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot point) → C) (c : C) :
    0 ≤ charge S₁ S₂ M W point pref c := by
  rcases point with key | p | p
  · exact RecursivePolygero.indicator_nonneg _
  · exact S₁.charge_nonneg W.1 p _ c
  · exact S₂.charge_nonneg W.2 p _ c

theorem budget_nonneg (point : Domain S₁ S₂) :
    0 ≤ budget S₁ S₂ M point := by
  rcases point with key | p | p
  · exact Nat.cast_nonneg _
  · exact S₁.budget_nonneg p
  · exact S₂.budget_nonneg p

theorem charge_sum_le (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (point : Domain S₁ S₂)
    (pref : Fin ((points S₁ S₂).slot point) → C) :
    (∑ c : C, charge S₁ S₂ M W point pref c) ≤
      budget S₁ S₂ M point := by
  rcases point with key | p | p
  · exact M.charge_sum_le _ _ S₁.bound S₂.bound
      (Counting.committedCandidates_card_le I₁ W.1 S₁.cutoff S₁.bound S₁.cutoff_gt S₁.packing)
      (Counting.committedCandidates_card_le I₂ W.2 S₂.cutoff S₂.bound S₂.cutoff_gt S₂.packing)
  · exact S₁.charge_sum_le W.1 p _
  · exact S₂.charge_sum_le W.2 p _

theorem charge_one_eq (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain S₁ S₂ → C) (p : S₁.Domain) :
    charge S₁ S₂ M W (.inr (.inl p))
        ((points S₁ S₂).chal H (.inr (.inl p))) (H (.inr (.inl p))) =
      S₁.charge W.1 p ((S₁.points).chal (fun x => H (.inr (.inl x))) p)
        (H (.inr (.inl p))) := by
  change S₁.charge W.1 p _ _ = _
  congr 1
  funext i
  exact prefix_one S₁ S₂ H p i

theorem charge_two_eq (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain S₁ S₂ → C)
    (p : S₂.Domain) :
    charge S₁ S₂ M W (.inr (.inr p))
        ((points S₁ S₂).chal H (.inr (.inr p))) (H (.inr (.inr p))) =
      S₂.charge W.2 p ((S₂.points).chal (fun x => H (.inr (.inr x))) p)
        (H (.inr (.inr p))) := by
  change S₂.charge W.2 p _ _ = _
  congr 1
  funext i
  exact prefix_two S₁ S₂ H p i

/-- Finite witness search in the two fixed committed lists. The result
satisfies both actual circuits and agrees on the common message. -/
noncomputable def extract (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (proof : Proof S₁ S₂) :
    Option ((Counting.tupleCounts I₁).Index × (Counting.tupleCounts I₂).Index) :=
  if h : ∃ g₁ g₂, S₁.Good (context S₁ S₂ proof) W.1 g₁ ∧
      S₂.Good (selectedOne S₁ S₂ proof) W.2 g₂ ∧ M.commonOne g₁ = M.commonTwo g₂ then
    some (h.choose,h.choose_spec.choose)
  else none

theorem extract_none_iff (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (proof : Proof S₁ S₂) :
    extract S₁ S₂ M W proof = none ↔
      ¬ ∃ g₁ g₂, S₁.Good (context S₁ S₂ proof) W.1 g₁ ∧
        S₂.Good (selectedOne S₁ S₂ proof) W.2 g₂ ∧ M.commonOne g₁ = M.commonTwo g₂ := by
  unfold extract
  split_ifs with h
  · simp only [h, not_true_eq_false]
  · simp only [h, not_false_eq_true]

theorem extract_valid (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (proof : Proof S₁ S₂)
    (pair : (Counting.tupleCounts I₁).Index × (Counting.tupleCounts I₂).Index)
    (h : extract S₁ S₂ M W proof = some pair) :
    S₁.Good (context S₁ S₂ proof) W.1 pair.1 ∧
      S₂.Good (selectedOne S₁ S₂ proof) W.2 pair.2 ∧
        M.commonOne pair.1 = M.commonTwo pair.2 := by
  unfold extract at h
  split_ifs at h with hex
  · have he := Option.some.inj h
    rw [← he]
    exact hex.choose_spec.choose_spec

noncomputable def totalOne (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) : ℚ :=
  ∑ i : Fin S₁.slots,
    let p := S₁.hashInput (selectedOne S₁ S₂ proof) i.val
    S₁.charge W.1 p ((S₁.points).chal (fun x => H (.inr (.inl x))) p)
      (H (.inr (.inl p)))

noncomputable def totalTwo (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) : ℚ :=
  ∑ i : Fin S₂.slots,
    let p := S₂.hashInput proof i.val
    S₂.charge W.2 p ((S₂.points).chal (fun x => H (.inr (.inr x))) p)
      (H (.inr (.inr p)))

theorem totalOne_nonneg (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) :
    0 ≤ totalOne S₁ S₂ W H proof :=
  sum_nonneg (fun _ _ => S₁.charge_nonneg W.1 _ _ _)

theorem totalTwo_nonneg (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) :
    0 ≤ totalTwo S₁ S₂ W H proof :=
  sum_nonneg (fun _ _ => S₂.charge_nonneg W.2 _ _ _)

theorem sum_charge (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) :
    (∑ i : Fin (1+S₁.slots+S₂.slots),
      let p := hashInput S₁ S₂ proof i.val
      charge S₁ S₂ M W p ((points S₁ S₂).chal H p) (H p)) =
    RecursivePolygero.indicator (M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff)
      (Counting.committedCandidates I₂ W.2 S₂.cutoff) (H (.inl (context S₁ S₂ proof).1))) +
      totalOne S₁ S₂ W H proof + totalTwo S₁ S₂ W H proof := by
  let f := fun p : Domain S₁ S₂ =>
    charge S₁ S₂ M W p ((points S₁ S₂).chal H p) (H p)
  change (∑ i : Fin (slots S₁ S₂),
    f (hashInput S₁ S₂ proof i.val)) = _
  rw [TwoFieldReplay.sum_hashInput S₁ S₂ proof f]
  simp only [f, charge_one_eq, charge_two_eq, totalOne, totalTwo]
  rfl

/-- The separate private MAC blinds enter through the two affine row
identities. No equality between those blinds is assumed. -/
theorem path_charge_ge_one (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂)
    (hkey : (context S₁ S₂ proof).2.1 = H (.inl (context S₁ S₂ proof).1))
    (hacceptOne : S₁.Accepts W.1 (fun x => H (.inr (.inl x)))
      (selectedOne S₁ S₂ proof))
    (hacceptTwo : S₂.Accepts W.2 (fun x => H (.inr (.inr x)))
      proof)
    (tag : Fin blocks → Fmac)
    (hrowOne : ∀ g, S₁.Good (context S₁ S₂ proof) W.1 g →
      M.macOne g (M.decode (context S₁ S₂ proof).2.1) = tag)
    (hrowTwo : ∀ g, S₂.Good (selectedOne S₁ S₂ proof) W.2 g →
      M.macTwo g (M.decode (context S₁ S₂ proof).2.1) = tag)
    (hbad : ¬ ∃ g₁ g₂, S₁.Good (context S₁ S₂ proof) W.1 g₁ ∧
      S₂.Good (selectedOne S₁ S₂ proof) W.2 g₂ ∧ M.commonOne g₁ = M.commonTwo g₂) :
    1 ≤ ∑ i : Fin (1+S₁.slots+S₂.slots),
      let p := hashInput S₁ S₂ proof i.val
      charge S₁ S₂ M W p ((points S₁ S₂).chal H p) (H p) := by
  rw [sum_charge]
  have hzeroOne := totalOne_nonneg S₁ S₂ W H proof
  have hzeroTwo := totalTwo_nonneg S₁ S₂ W H proof
  have hzeroKey := RecursivePolygero.indicator_nonneg (M.Bad
    (Counting.committedCandidates I₁ W.1 S₁.cutoff) (Counting.committedCandidates I₂ W.2 S₂.cutoff)
    (H (.inl (context S₁ S₂ proof).1)))
  by_cases hone : ∃ g, S₁.Good (context S₁ S₂ proof) W.1 g
  · by_cases htwo : ∃ g, S₂.Good (selectedOne S₁ S₂ proof) W.2 g
    · obtain ⟨g₁,hg₁⟩ := hone
      obtain ⟨g₂,hg₂⟩ := htwo
      have hne : M.commonOne g₁ ≠ M.commonTwo g₂ := fun he => hbad ⟨g₁,g₂,hg₁,hg₂,he⟩
      have hmac : M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff)
          (Counting.committedCandidates I₂ W.2 S₂.cutoff) (H (.inl (context S₁ S₂ proof).1)) := by
        rw [← hkey]
        exact ⟨g₁,hg₁.1,g₂,hg₂.1,hne,(hrowOne g₁ hg₁).trans (hrowTwo g₂ hg₂).symm⟩
      rw [show RecursivePolygero.indicator (M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff)
          (Counting.committedCandidates I₂ W.2 S₂.cutoff) (H (.inl (context S₁ S₂ proof).1))) = 1 by
        simp only [RecursivePolygero.indicator, if_pos hmac]]
      linarith
    · have hp : 1 ≤ totalTwo S₁ S₂ W H proof :=
        S₂.path_charge_ge_one W.2 (fun x => H (.inr (.inr x)))
          proof htwo hacceptTwo
      linarith
  · have hp : 1 ≤ totalOne S₁ S₂ W H proof :=
      S₁.path_charge_ge_one W.1 (fun x => H (.inr (.inl x)))
        (selectedOne S₁ S₂ proof) hone hacceptOne
    linarith

end LfzkV2.Linear.Runtime.TwoFieldPotential
