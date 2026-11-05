import LfzkV2.Packed.CompiledSide

/-!
# The shared MAC challenge followed by two native sides

The second side's context is the complete selected first-side transcript.
This includes U, A, and the backend response. No future message is present in
a prefix: each side supplies its own staged packing/backend schedule.
-/

namespace LfzkV2.Packed.TwoFieldReplay

open RecursivePolygero Bcs.TotalOracle
open scoped Classical

variable {F₁ F₂ Key C Public : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}

abbrev Context (Key C Public : Type) := Key × C × Public

variable (S₁ : CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C S₁.Selected circuit₂ I₂)

abbrev Domain := Key ⊕ (S₁.Domain ⊕ S₂.Domain)
abbrev Proof := S₂.Selected

def context (proof : Proof S₁ S₂) : Context Key C Public := S₁.context (S₂.context proof)
def selectedOne (proof : Proof S₁ S₂) : S₁.Selected := S₂.context proof

def key : Domain S₁ S₂ → Key
  | .inl k => k
  | .inr (.inl p) => (S₁.key p).1
  | .inr (.inr p) => (S₁.context (S₂.key p)).1

def slots : ℕ := 1 + S₁.slots + S₂.slots

def points : PrefixPoints (Domain S₁ S₂) where
  slot
    | .inl _ => 0
    | .inr (.inl p) => 1 + S₁.points.slot p
    | .inr (.inr p) => 1 + S₁.slots + S₂.points.slot p
  anc point j := match point with
    | .inl k => .inl k
    | .inr (.inl p) => if j = 0 then .inl (S₁.key p).1 else
        .inr (.inl (S₁.points.anc p (j-1)))
    | .inr (.inr p) => if j = 0 then .inl (S₁.context (S₂.key p)).1 else
        if j < 1 + S₁.slots then
          .inr (.inl (S₁.hashInput (S₂.key p) (j-1)))
        else .inr (.inr (S₂.points.anc p (j-1-S₁.slots)))
  anc_ne point j hj := by
    rcases point with k | p | p
    · change j < 0 at hj
      omega
    · dsimp
      split_ifs with hzero
      · intro heq; cases heq
      · intro heq
        exact S₁.points.anc_ne p (j-1)
          (by change j < 1 + S₁.points.slot p at hj; omega)
          (Sum.inl.inj (Sum.inr.inj heq))
    · dsimp
      split_ifs with hzero hearlier
      · intro heq; cases heq
      · intro heq; cases heq
      · intro heq
        exact S₂.points.anc_ne p (j-1-S₁.slots)
          (by change j < 1 + S₁.slots + S₂.points.slot p at hj; omega)
          (Sum.inr.inj (Sum.inr.inj heq))

def hashInput (proof : Proof S₁ S₂) (j : ℕ) : Domain S₁ S₂ :=
  if j = 0 then .inl (context S₁ S₂ proof).1
  else if j < 1 + S₁.slots then .inr (.inl (S₁.hashInput (selectedOne S₁ S₂ proof) (j-1)))
  else .inr (.inr (S₂.hashInput proof (j-1-S₁.slots)))

theorem hashInput_zero (proof : Proof S₁ S₂) :
    hashInput S₁ S₂ proof 0 = .inl (context S₁ S₂ proof).1 := by
  rw [hashInput, if_pos rfl]

theorem hashInput_one (proof : Proof S₁ S₂) (i : Fin S₁.slots) :
    hashInput S₁ S₂ proof (1+i.val) =
      .inr (.inl (S₁.hashInput (selectedOne S₁ S₂ proof) i.val)) := by
  rw [hashInput, if_neg (by omega), if_pos (by omega), show 1+i.val-1=i.val by omega]

theorem hashInput_two (proof : Proof S₁ S₂) (j : ℕ) :
    hashInput S₁ S₂ proof (1+S₁.slots+j) = .inr (.inr (S₂.hashInput proof j)) := by
  rw [hashInput, if_neg (by omega), if_neg (by omega), show 1+S₁.slots+j-1-S₁.slots=j by omega]

theorem hashInput_key (proof : Proof S₁ S₂) (j : ℕ) :
    key S₁ S₂ (hashInput S₁ S₂ proof j) = (context S₁ S₂ proof).1 := by
  unfold hashInput
  split_ifs
  · rfl
  · exact congrArg Prod.fst (S₁.hashInput_key (selectedOne S₁ S₂ proof) (j-1))
  · exact congrArg (fun s => (S₁.context s).1) (S₂.hashInput_key proof (j-1-S₁.slots))

theorem slot_hashInput (proof : Proof S₁ S₂) (j : ℕ) (hj : j < slots S₁ S₂) :
    (points S₁ S₂).slot (hashInput S₁ S₂ proof j) = j := by
  change j < 1 + S₁.slots + S₂.slots at hj
  unfold hashInput
  split_ifs with hzero hone
  · exact hzero.symm
  · change 1 + S₁.points.slot _ = j
    rw [S₁.slot_hashInput _ _ (by omega)]
    omega
  · change 1 + S₁.slots + S₂.points.slot _ = j
    rw [S₂.slot_hashInput _ _ (by omega)]
    omega

theorem hashInput_injective (proof : Proof S₁ S₂) :
    Function.Injective (fun i : Fin (slots S₁ S₂) => hashInput S₁ S₂ proof i.val) := by
  intro i j heq
  apply Fin.ext
  have h := congrArg (points S₁ S₂).slot heq
  simpa only [slot_hashInput S₁ S₂ proof _ i.isLt, slot_hashInput S₁ S₂ proof _ j.isLt] using h

theorem prefix_one (H : Domain S₁ S₂ → C) (p : S₁.Domain) (i : Fin (S₁.points.slot p)) :
    (points S₁ S₂).chal H (.inr (.inl p))
        ⟨1+i.val,by change 1+i.val < 1+S₁.points.slot p; omega⟩ =
      S₁.points.chal (fun x => H (.inr (.inl x))) p i := by
  dsimp only [PrefixPoints.chal, points]
  rw [if_neg (by omega), show 1+i.val-1=i.val by omega]

theorem prefix_two (H : Domain S₁ S₂ → C) (p : S₂.Domain) (i : Fin (S₂.points.slot p)) :
    (points S₁ S₂).chal H (.inr (.inr p))
        ⟨1+S₁.slots+i.val,by change 1+S₁.slots+i.val < 1+S₁.slots+S₂.points.slot p; omega⟩ =
      S₂.points.chal (fun x => H (.inr (.inr x))) p i := by
  dsimp only [PrefixPoints.chal, points]
  rw [if_neg (by omega), if_neg (by omega), show 1+S₁.slots+i.val-1-S₁.slots=i.val by omega]

theorem prefix_one_key (H : Domain S₁ S₂ → C) (p : S₁.Domain) :
    (points S₁ S₂).chal H (.inr (.inl p))
        ⟨0,by change 0 < 1+S₁.points.slot p; omega⟩ = H (.inl (S₁.key p).1) := rfl

theorem prefix_two_key (H : Domain S₁ S₂ → C) (p : S₂.Domain) :
    (points S₁ S₂).chal H (.inr (.inr p))
        ⟨0,by change 0 < 1+S₁.slots+S₂.points.slot p; omega⟩ =
      H (.inl (S₁.context (S₂.key p)).1) := rfl

theorem prefix_two_first (H : Domain S₁ S₂ → C) (p : S₂.Domain) (i : Fin S₁.slots) :
    (points S₁ S₂).chal H (.inr (.inr p))
        ⟨1+i.val,by change 1+i.val < 1+S₁.slots+S₂.points.slot p; omega⟩ =
      H (.inr (.inl (S₁.hashInput (S₂.key p) i.val))) := by
  dsimp only [PrefixPoints.chal, points]
  rw [if_neg (by omega), if_pos (by omega), show 1+i.val-1=i.val by omega]

theorem sum_hashInput {A : Type} [AddCommMonoid A] (proof : Proof S₁ S₂)
    (f : Domain S₁ S₂ → A) :
    (∑ i : Fin (slots S₁ S₂), f (hashInput S₁ S₂ proof i.val)) =
      f (.inl (context S₁ S₂ proof).1) +
      (∑ i : Fin S₁.slots, f (.inr (.inl (S₁.hashInput (selectedOne S₁ S₂ proof) i.val)))) +
      (∑ i : Fin S₂.slots, f (.inr (.inr (S₂.hashInput proof i.val)))) := by
  let g : ℕ → A := fun i => f (hashInput S₁ S₂ proof i)
  change (∑ i : Fin (1+S₁.slots+S₂.slots), g i.val) = _
  rw [Fin.sum_univ_eq_sum_range g, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one]
  have hz : g 0 = f (.inl (context S₁ S₂ proof).1) := congrArg f (hashInput_zero S₁ S₂ proof)
  rw [hz]
  congr 1
  · congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => congrArg f (hashInput_one S₁ S₂ proof i))
  · rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => congrArg f (hashInput_two S₁ S₂ proof i.val))

end LfzkV2.Packed.TwoFieldReplay
