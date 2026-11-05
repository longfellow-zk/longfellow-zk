import LfzkV2.Layered.Joint.Charges

/-! Candidate extraction for both actual circuits and their common MAC
message. The single opening contributes both fields' charges. -/

namespace LfzkV2.Layered.Joint.Extraction

open Finset RecursivePolygero Bcs.TotalOracle Replay
open LfzkV2.Joint (Participant Family)
open scoped Classical

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Layered.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Layered.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : Layered.Runtime.CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : Layered.Runtime.CompiledSide F₂ C (Side.Frontend S₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

noncomputable def extract (W : I₁.layer.Oracle × I₂.layer.Oracle) (proof : Proof S₁ S₂) :
    Option ((Counting.tupleCounts I₁).Index × (Counting.tupleCounts I₂).Index) :=
  if h : ∃ g₁ g₂, S₁.Good (context S₁ S₂ proof) W.1 g₁ ∧
      S₂.Good (firstFrontend S₁ S₂ proof) W.2 g₂ ∧ M.commonOne g₁ = M.commonTwo g₂ then
    some (h.choose,h.choose_spec.choose)
  else none

theorem extract_none_iff (W : I₁.layer.Oracle × I₂.layer.Oracle) (proof : Proof S₁ S₂) :
    extract S₁ S₂ M W proof = none ↔
      ¬ ∃ g₁ g₂, S₁.Good (context S₁ S₂ proof) W.1 g₁ ∧
        S₂.Good (firstFrontend S₁ S₂ proof) W.2 g₂ ∧ M.commonOne g₁ = M.commonTwo g₂ := by
  unfold extract
  split_ifs with h <;> simp only [h, not_true_eq_false, not_false_eq_true]

theorem extract_valid (W : I₁.layer.Oracle × I₂.layer.Oracle) (proof : Proof S₁ S₂)
    (pair : (Counting.tupleCounts I₁).Index × (Counting.tupleCounts I₂).Index)
    (h : extract S₁ S₂ M W proof = some pair) :
    S₁.Good (context S₁ S₂ proof) W.1 pair.1 ∧
      S₂.Good (firstFrontend S₁ S₂ proof) W.2 pair.2 ∧ M.commonOne pair.1 = M.commonTwo pair.2 := by
  unfold extract at h
  split_ifs at h with hex
  · have he := Option.some.inj h
    rw [← he]
    exact hex.choose_spec.choose_spec

noncomputable def total (W : I₁.layer.Oracle × I₂.layer.Oracle) (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) : ℚ :=
  ∑ i : Fin (slots S₁ S₂),
    let p := hashInput S₁ S₂ proof i.val
    Charges.charge S₁ S₂ M W p ((points S₁ S₂).chal H p) (H p)

private theorem sum_injective_le {m n : ℕ} (f : Fin n → ℚ) (map : Fin m → Fin n)
    (hinj : Function.Injective map) (hzero : ∀ i, 0 ≤ f i) :
    (∑ i, f (map i)) ≤ ∑ j, f j := by
  rw [← sum_image (fun a _ b _ h => hinj h)]
  exact sum_le_univ_sum_of_nonneg hzero

theorem totalOne_le (W : I₁.layer.Oracle × I₂.layer.Oracle) (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) :
    (∑ j : Fin S₁.slots,
      let x := S₁.hashInput (selectedOne S₁ S₂ proof) j.val
      S₁.charge W.1 x (S₁.points.chal (firstOracle S₁ S₂ H proof) x)
        (firstOracle S₁ S₂ H proof x)) ≤ total S₁ S₂ M W H proof := by
  let map := firstIndex S₁ S₂
  have hinj : Function.Injective map := firstIndex_injective S₁ S₂
  apply le_trans _ (sum_injective_le _ map hinj
    (fun j => Charges.charge_nonneg S₁ S₂ M W _ _ _))
  apply sum_le_sum
  intro j _
  rw [← Charges.one_at S₁ S₂ W.1 H proof j.val j.isLt]
  have hmac : 0 ≤ (if (points S₁ S₂).slot (hashInput S₁ S₂ proof (firstSlot S₁ S₂ j.val)) = 0
      then Charges.mac S₁ S₂ M W (H (hashInput S₁ S₂ proof (firstSlot S₁ S₂ j.val))) else 0) := by
    split_ifs
    · exact indicator_nonneg _
    · exact le_rfl
  have htwo := Charges.two_nonneg S₁ S₂ W.2
    (hashInput S₁ S₂ proof (firstSlot S₁ S₂ j.val))
    ((points S₁ S₂).chal H (hashInput S₁ S₂ proof (firstSlot S₁ S₂ j.val)))
    (H (hashInput S₁ S₂ proof (firstSlot S₁ S₂ j.val)))
  change _ ≤ Charges.charge S₁ S₂ M W _ _ _
  unfold Charges.charge
  dsimp only [map, firstIndex]
  exact (le_add_of_nonneg_left hmac).trans (le_add_of_nonneg_right htwo)

theorem totalTwo_le (W : I₁.layer.Oracle × I₂.layer.Oracle) (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) :
    (∑ j : Fin S₂.slots,
      let x := S₂.hashInput (selectedTwo S₁ S₂ proof) j.val
      S₂.charge W.2 x (S₂.points.chal (secondOracle S₁ S₂ H proof) x)
        (secondOracle S₁ S₂ H proof x)) ≤ total S₁ S₂ M W H proof := by
  let map := secondIndex S₁ S₂
  have hinj : Function.Injective map := secondIndex_injective S₁ S₂
  apply le_trans _ (sum_injective_le _ map hinj
    (fun j => Charges.charge_nonneg S₁ S₂ M W _ _ _))
  apply sum_le_sum
  intro j _
  rw [← Charges.two_at S₁ S₂ W.2 H proof j.val j.isLt]
  have hmac : 0 ≤ (if (points S₁ S₂).slot (hashInput S₁ S₂ proof (secondSlot S₁ S₂ j.val)) = 0
      then Charges.mac S₁ S₂ M W (H (hashInput S₁ S₂ proof (secondSlot S₁ S₂ j.val))) else 0) := by
    split_ifs
    · exact indicator_nonneg _
    · exact le_rfl
  have hone := Charges.one_nonneg S₁ S₂ W.1
    (hashInput S₁ S₂ proof (secondSlot S₁ S₂ j.val))
    ((points S₁ S₂).chal H (hashInput S₁ S₂ proof (secondSlot S₁ S₂ j.val)))
    (H (hashInput S₁ S₂ proof (secondSlot S₁ S₂ j.val)))
  change _ ≤ Charges.charge S₁ S₂ M W _ _ _
  unfold Charges.charge
  dsimp only [map, secondIndex]
  exact le_add_of_nonneg_left (add_nonneg hmac hone)

theorem mac_le_total (W : I₁.layer.Oracle × I₂.layer.Oracle) (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) :
    Charges.mac S₁ S₂ M W (H (hashInput S₁ S₂ proof 0)) ≤ total S₁ S₂ M W H proof := by
  let zero : Fin (slots S₁ S₂) := ⟨0,by unfold slots; omega⟩
  apply le_trans _ (single_le_sum
    (fun j _ => Charges.charge_nonneg S₁ S₂ M W _ _ _) (mem_univ zero))
  have hone := Charges.one_nonneg S₁ S₂ W.1 (hashInput S₁ S₂ proof 0)
    ((points S₁ S₂).chal H (hashInput S₁ S₂ proof 0)) (H (hashInput S₁ S₂ proof 0))
  have htwo := Charges.two_nonneg S₁ S₂ W.2 (hashInput S₁ S₂ proof 0)
    ((points S₁ S₂).chal H (hashInput S₁ S₂ proof 0)) (H (hashInput S₁ S₂ proof 0))
  change _ ≤ Charges.charge S₁ S₂ M W _ _ _
  rw [Charges.charge, slot_hashInput _ _ _ _ zero.isLt, if_pos rfl]
  linarith

/-- If neither candidate pair is a joint witness, acceptance pays at least
one unit at a frontend/backend failure or at the shared MAC point. -/
theorem path_charge_ge_one (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂)
    (hkey : (context S₁ S₂ proof).2.1 = H (hashInput S₁ S₂ proof 0))
    (hacceptOne : S₁.Accepts W.1 (firstOracle S₁ S₂ H proof) (selectedOne S₁ S₂ proof))
    (hacceptTwo : S₂.Accepts W.2 (secondOracle S₁ S₂ H proof) (selectedTwo S₁ S₂ proof))
    (tag : Fin blocks → Fmac)
    (hrowOne : ∀ g, S₁.Good (context S₁ S₂ proof) W.1 g →
      M.macOne g (M.decode (context S₁ S₂ proof).2.1) = tag)
    (hrowTwo : ∀ g, S₂.Good (firstFrontend S₁ S₂ proof) W.2 g →
      M.macTwo g (M.decode (context S₁ S₂ proof).2.1) = tag)
    (hbad : ¬ ∃ g₁ g₂, S₁.Good (context S₁ S₂ proof) W.1 g₁ ∧
      S₂.Good (firstFrontend S₁ S₂ proof) W.2 g₂ ∧ M.commonOne g₁ = M.commonTwo g₂) :
    1 ≤ total S₁ S₂ M W H proof := by
  by_cases hone : ∃ g, S₁.Good (context S₁ S₂ proof) W.1 g
  · by_cases htwo : ∃ g, S₂.Good (firstFrontend S₁ S₂ proof) W.2 g
    · obtain ⟨g₁,hg₁⟩ := hone
      obtain ⟨g₂,hg₂⟩ := htwo
      have hne : M.commonOne g₁ ≠ M.commonTwo g₂ := fun he => hbad ⟨g₁,g₂,hg₁,hg₂,he⟩
      have hmac : M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff)
          (Counting.committedCandidates I₂ W.2 S₂.cutoff) (H (hashInput S₁ S₂ proof 0)) := by
        rw [← hkey]
        exact ⟨g₁,hg₁.1,g₂,hg₂.1,hne,(hrowOne g₁ hg₁).trans (hrowTwo g₂ hg₂).symm⟩
      have h := mac_le_total S₁ S₂ M W H proof
      simpa only [Charges.mac, indicator, if_pos hmac] using h
    · exact (S₂.path_charge_ge_one W.2 (secondOracle S₁ S₂ H proof)
        (selectedTwo S₁ S₂ proof) htwo hacceptTwo).trans (totalTwo_le S₁ S₂ M W H proof)
  · exact (S₁.path_charge_ge_one W.1 (firstOracle S₁ S₂ H proof)
      (selectedOne S₁ S₂ proof) hone hacceptOne).trans (totalOne_le S₁ S₂ M W H proof)

end LfzkV2.Layered.Joint.Extraction
