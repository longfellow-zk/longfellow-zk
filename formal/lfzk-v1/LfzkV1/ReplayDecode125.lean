import LfzkV1.ReplayView125
import LfzkV1.ResidualReplay125
import LfzkV1.TwoFieldV1Rows

/-! Exact decoders at distinct unseen addresses yield a joint uniform replay assignment. -/

open BigOperators Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.ReplayDecode125

open Bcs.TotalOracle Merkle.RandomOracle
open LfzkV1.ReplayView125 LfzkV1.TwoFieldV1Rows

section Decoder

variable {C Y Z : Type} [Fintype C] [Fintype Y] [DecidableEq Y]

/-- The two exact-balance inequalities force equality in every fiber. -/
theorem card_decoder_fiber (d : ExactDecoder C Y) (y : Y) :
    Fintype.card {c : C // d.decode c = y} = d.k := by
  rw [Fintype.card_subtype]
  apply le_antisymm (d.hbal y)
  by_contra! hy
  have hs : Fintype.card C < d.k * Fintype.card Y := by
    have hsum := Finset.card_eq_sum_card_fiberwise
      (f := d.decode) (s := (univ : Finset C)) (t := (univ : Finset Y))
      (fun _ _ => Finset.mem_univ _)
    simp only [card_univ] at hsum
    rw [hsum]
    calc
      _ < ∑ _ : Y, d.k := Finset.sum_lt_sum (fun z _ => d.hbal z) ⟨y, mem_univ _, hy⟩
      _ = _ := by simp [mul_comm]
  exact (not_lt_of_ge d.hexact) hs

/-- Split a raw answer into the decoded answer and one index in its constant-size fiber. -/
noncomputable def decoderSplit (d : ExactDecoder C Y) : C ≃ Y × Fin d.k :=
  (Equiv.sigmaFiberEquiv d.decode).symm.trans <|
    Equiv.sigmaEquivProdOfEquiv fun y =>
      Fintype.equivOfCardEq (by rw [card_decoder_fiber, Fintype.card_fin])

@[simp] theorem decoderSplit_fst (d : ExactDecoder C Y) (c : C) :
    (decoderSplit d c).1 = d.decode c := rfl

/-- An equivalence on the challenge alphabet does not change the decoder balance. -/
def reindex [Fintype Z] [DecidableEq Z] (d : ExactDecoder C Y) (e : Y ≃ Z) :
    ExactDecoder C Z where
  decode c := e (d.decode c)
  k := d.k
  hbal z := by
    have he (c : C) : e (d.decode c) = z ↔ d.decode c = e.symm z :=
      e.apply_eq_iff_eq_symm_apply
    simpa only [he] using d.hbal (e.symm z)
  hexact := by
    rw [← Fintype.card_congr e]
    exact d.hexact

/-- A scalar role contributes one coordinate. -/
noncomputable def scalarDecoder (d : ExactDecoder C Y) : ExactDecoder C (Fin 1 → Y) :=
  reindex d (Equiv.funUnique (Fin 1) Y).symm

@[simp] theorem scalarDecoder_apply (d : ExactDecoder C Y) (c : C) (i : Fin 1) :
    (scalarDecoder d).decode c i = d.decode c := rfl

/-- The two coordinates of a later-layer pair become two independent scalars. -/
noncomputable def pairDecoder {F : Type} [Fintype F] [DecidableEq F]
    (d : ExactDecoder C (F × F)) : ExactDecoder C (Fin 2 → F) :=
  reindex d (finTwoArrowEquiv F).symm

@[simp] theorem pairDecoder_zero {F : Type} [Fintype F] [DecidableEq F]
    (d : ExactDecoder C (F × F)) (c : C) : (pairDecoder d).decode c 0 = (d.decode c).1 := rfl

@[simp] theorem pairDecoder_one {F : Type} [Fintype F] [DecidableEq F]
    (d : ExactDecoder C (F × F)) (c : C) : (pairDecoder d).decode c 1 = (d.decode c).2 := rfl

/-- The grouped initial draw flattens to the output coordinates, then beta and alpha. -/
noncomputable def initDecoder {F : Type} [Fintype F] [DecidableEq F] {logv : ℕ}
    (d : ExactDecoder C ((Fin logv → F) × F × F)) :
    ExactDecoder C (Fin (logv + 2) → F) :=
  reindex d (((Equiv.refl (Fin logv → F)).prodCongr (finTwoArrowEquiv F).symm).trans
    (Fin.appendEquiv logv 2))

@[simp] theorem initDecoder_point {F : Type} [Fintype F] [DecidableEq F] {logv : ℕ}
    (d : ExactDecoder C ((Fin logv → F) × F × F)) (c : C) (i : Fin logv) :
    (initDecoder d).decode c (Fin.castAdd 2 i) = (d.decode c).1 i :=
  Fin.append_left _ _ _

@[simp] theorem initDecoder_beta {F : Type} [Fintype F] [DecidableEq F] {logv : ℕ}
    (d : ExactDecoder C ((Fin logv → F) × F × F)) (c : C) :
    (initDecoder d).decode c (Fin.natAdd logv (0 : Fin 2)) = (d.decode c).2.1 :=
  Fin.append_right _ _ _

@[simp] theorem initDecoder_alpha {F : Type} [Fintype F] [DecidableEq F] {logv : ℕ}
    (d : ExactDecoder C ((Fin logv → F) × F × F)) (c : C) :
    (initDecoder d).decode c (Fin.natAdd logv (1 : Fin 2)) = (d.decode c).2.2 :=
  Fin.append_right _ _ _

end Decoder

section Density

variable {A B T R : Type} [Fintype A] [Fintype B] [Fintype T] [DivisionSemiring R] [CharZero R]

private def restrictFst (p : B → Prop) : {b : B × T // p b.1} ≃ {b : B // p b} × T where
  toFun b := (⟨b.val.1, b.property⟩, b.val.2)
  invFun b := ⟨(b.1.val, b.2), b.1.property⟩
  left_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl
  right_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl

open Classical in
/-- Under an equivalence to a product, projecting to one factor preserves exact uniform density. -/
theorem density_equiv_fst [Nonempty A] (e : A ≃ B × T) (p : B → Prop) :
    ((univ.filter fun a => p (e a).1).card : R) / Fintype.card A =
      ((univ.filter p).card : R) / Fintype.card B := by
  have hT : Nonempty T := (inferInstance : Nonempty A).map fun a => (e a).2
  have hcount := Fintype.card_congr
    ((Equiv.subtypeEquivOfSubtype (p := fun b => p b.1) e).trans (restrictFst p))
  rw [Fintype.card_subtype, Fintype.card_prod, Fintype.card_subtype] at hcount
  rw [hcount, Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')

end Density

section View

variable {Q C Out I : Type} {fuel : ℕ}
variable {Y : I → Type}
variable (tree : Tree Q C Out fuel) (lookups : Out → List Q) (H : Q → C)

abbrev ViewFiber := {H' : Q → C // view tree lookups H' = view tree lookups H}
abbrev Unseen := {q : Q // q ∉ revealed tree lookups H}

variable {tree lookups H}

abbrev Unselected (address : I ↪ Unseen tree lookups H) :=
  {q : Unseen tree lookups H // q ∉ Set.range address}

private def piProductEquiv {A B : I → Type} :
    ((i : I) → A i × B i) ≃ ((i : I) → A i) × ((i : I) → B i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun f i := (f.1 i, f.2 i)
  left_inv := by intro f; funext i; exact Prod.eta _
  right_inv := by intro f; cases f; rfl

private noncomputable def rawSplit {U : Type} (address : I ↪ U) :
    (U → C) ≃ (I → C) × ({q : U // q ∉ Set.range address} → C) := by
  classical
  let selected := Equiv.ofInjective address address.injective
  exact (Equiv.piEquivPiSubtypeProd (· ∈ Set.range address) (fun _ => C)).trans
    ((selected.symm.arrowCongr (Equiv.refl C)).prodCongr (Equiv.refl _))

private theorem rawSplit_fst {U : Type} (address : I ↪ U) (f : U → C) (i : I) :
    (rawSplit address f).1 i = f (address i) := rfl

variable [Fintype C] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]

/-- On a fixed view, the decoded assignment is a free product coordinate. Unused raw answers
and fiber indices remain free independently of that assignment. The embedding certifies that
the selected addresses are distinct and unrevealed. -/
noncomputable def viewDecoderEquiv (address : I ↪ Unseen tree lookups H)
    (d : ∀ i, ExactDecoder C (Y i)) :
    ViewFiber tree lookups H ≃
      ((i : I) → Y i) × ((i : I) → Fin (d i).k) × (Unselected address → C) :=
  (viewFiberEquiv tree lookups H).trans <| (rawSplit address).trans <|
    (((Equiv.piCongrRight fun i => decoderSplit (d i)).trans piProductEquiv).prodCongr
      (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

theorem viewDecoderEquiv_fst (address : I ↪ Unseen tree lookups H)
    (d : ∀ i, ExactDecoder C (Y i)) (H' : ViewFiber tree lookups H) (i : I) :
    (viewDecoderEquiv address d H').1 i = (d i).decode (H'.val (address i).val) := by
  change (decoderSplit (d i)
    ((rawSplit address (viewFiberEquiv tree lookups H H')).1 i)).1 = _
  rw [decoderSplit_fst, rawSplit_fst]
  rfl

open Classical in
/-- Any event defined on the joint decoded assignment has the same density in the view fiber
as it does in the full product of decoded challenge alphabets. -/
theorem view_decoder_density {R : Type} [DivisionSemiring R] [CharZero R]
    [Fintype Q] [Fintype I] (address : I ↪ Unseen tree lookups H)
    (d : ∀ i, ExactDecoder C (Y i)) (p : ((i : I) → Y i) → Prop) :
    ((univ.filter fun H' : ViewFiber tree lookups H =>
        p (fun i => (d i).decode (H'.val (address i).val))).card : R) /
      Fintype.card (ViewFiber tree lookups H) =
      ((univ.filter p).card : R) / Fintype.card ((i : I) → Y i) := by
  have h : Nonempty (ViewFiber tree lookups H) := ⟨⟨H, rfl⟩⟩
  have he (H' : ViewFiber tree lookups H) :
      (viewDecoderEquiv address d H').1 = fun i => (d i).decode (H'.val (address i).val) :=
    funext (viewDecoderEquiv_fst address d H')
  simpa only [he] using (density_equiv_fst (R := R) (viewDecoderEquiv address d) p)

open Classical in
/-- Counts on the view-fiber type are also ordinary counts constrained to that view. -/
theorem view_count_eq [Fintype Q] (p : (Q → C) → Prop) :
    (univ.filter fun H' : ViewFiber tree lookups H => p H'.val).card =
      (univ.filter fun H' : Q → C => view tree lookups H' = view tree lookups H ∧ p H').card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun a => ⟨a.val.val, a.val.property, a.property⟩
      invFun := fun a => ⟨⟨a.val, a.property.1⟩, a.property.2⟩
      left_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl
      right_inv := by rintro ⟨_, _, _⟩; rfl }

end View

section Scalars

variable {I F : Type} {k : ℕ} {width : I → ℕ}

/-- Give the components of grouped role draws ordinary polynomial-variable indices. -/
def flatten (index : (Σ i, Fin (width i)) ≃ Fin k) :
    ((i : I) → Fin (width i) → F) ≃ (Fin k → F) :=
  (Equiv.piCurry (fun _ _ => F)).symm.trans (index.arrowCongr (Equiv.refl F))

@[simp] theorem flatten_apply (index : (Σ i, Fin (width i)) ≃ Fin k)
    (xs : (i : I) → Fin (width i) → F) (i : I) (j : Fin (width i)) :
    flatten index xs (index ⟨i, j⟩) = xs i j := by
  rw [flatten, Equiv.trans_apply, Equiv.arrowCongr_apply]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.refl_apply]
  rfl

open Classical in
/-- The hidden polynomial variables are jointly uniform after each grouped challenge is
flattened. This is the density used for one-equation replay. -/
theorem view_scalar_density {Q C Out R : Type} {fuel : ℕ} [Fintype Q] [Fintype C] [Fintype I]
    [Fintype F] [DecidableEq F] [DivisionSemiring R] [CharZero R]
    {tree : Tree Q C Out fuel} {lookups : Out → List Q} {H : Q → C}
    (address : I ↪ Unseen tree lookups H) (d : ∀ i, ExactDecoder C (Fin (width i) → F))
    (index : (Σ i, Fin (width i)) ≃ Fin k) (p : (Fin k → F) → Prop) :
    ((univ.filter fun H' : ViewFiber tree lookups H =>
        p (flatten index fun i => (d i).decode (H'.val (address i).val))).card : R) /
      Fintype.card (ViewFiber tree lookups H) =
      ((univ.filter p).card : R) / (Fintype.card F ^ k : R) := by
  have h : (univ.filter (p ∘ flatten index)).card = (univ.filter p).card := by
    rw [← Fintype.card_subtype (p ∘ flatten index), ← Fintype.card_subtype p]
    exact Fintype.card_congr ((flatten (F := F) index).subtypeEquivOfSubtype (p := p))
  calc
    _ = ((univ.filter (p ∘ flatten index)).card : R) /
        Fintype.card ((i : I) → Fin (width i) → F) :=
      view_decoder_density address d (p ∘ flatten index)
    _ = _ := by
      rw [h, Fintype.card_congr (flatten (F := F) index), Fintype.card_fun, Fintype.card_fin,
        Nat.cast_pow]

open Classical in
/-- Charge an event that forces all residuals to vanish on a nonidentity view. Its count is
at most degree over field size times the number of full oracle tables in the view. -/
theorem view_nonidentity_count_le {Q C Out J : Type} {fuel : ℕ}
    [Fintype Q] [Fintype C] [Fintype I] [Field F] [Fintype F] [DecidableEq F]
    {tree : Tree Q C Out fuel} {lookups : Out → List Q} {H : Q → C}
    (address : I ↪ Unseen tree lookups H) (d : ∀ i, ExactDecoder C (Fin (width i) → F))
    (index : (Σ i, Fin (width i)) ≃ Fin k) (p : J → MvPolynomial (Fin k) F)
    {degree : ℕ} (hdegree : ∀ j, (p j).totalDegree ≤ degree) (hnz : ∃ j, p j ≠ 0)
    (event : (Q → C) → Prop)
    (hevent : ∀ H' : ViewFiber tree lookups H, event H'.val →
      ∀ j, MvPolynomial.eval
        (flatten index fun i => (d i).decode (H'.val (address i).val)) (p j) = 0) :
    ((univ.filter fun H' : Q → C =>
      view tree lookups H' = view tree lookups H ∧ event H').card : ℚ) ≤
      ((degree : ℚ) / Fintype.card F) *
        ((univ.filter fun H' : Q → C => view tree lookups H' = view tree lookups H).card : ℚ) := by
  let T := ViewFiber tree lookups H
  let zeroRows := fun x : Fin k → F => ∀ j, MvPolynomial.eval x (p j) = 0
  have h₀ := ResidualReplay125.nonidentity_bound p hdegree hnz
  have h₁ := view_scalar_density (R := ℚ≥0) address d index zeroRows
  have h₂ : ((univ.filter fun H' : T => event H'.val).card : ℚ≥0) / Fintype.card T ≤
      (degree : ℚ≥0) / Fintype.card F := calc
    _ ≤ ((univ.filter fun H' : T =>
        zeroRows (flatten index fun i => (d i).decode (H'.val (address i).val))).card : ℚ≥0) /
        Fintype.card T := by
      gcongr with H'
      exact hevent H'
    _ ≤ _ := h₁.trans_le h₀
  have hT : Nonempty T := ⟨⟨H, rfl⟩⟩
  have h₃ := (div_le_iff₀ (show (0 : ℚ≥0) < Fintype.card T by exact_mod_cast Fintype.card_pos)).mp h₂
  have hsize : Fintype.card T =
      (univ.filter fun H' : Q → C => view tree lookups H' = view tree lookups H).card := by
    simpa using view_count_eq (tree := tree) (lookups := lookups) (H := H) (fun _ => True)
  rw [view_count_eq, hsize] at h₃
  exact_mod_cast h₃

end Scalars

section ReplayCoordinates

open MvPolynomial LfzkV1.ResidualReplay125
open scoped Classical

variable {Q C Out I F : Type} {fuel k : ℕ} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable {tree : Tree Q C Out fuel} {lookups : Out → List Q} {H : Q → C}
variable (address : I ↪ Q) {width : I → ℕ}

abbrev HiddenRole := {i : I // address i ∉ revealed tree lookups H}

/-- Restrict distinct scheduled addresses to the still unseen roles. -/
def hiddenAddress : HiddenRole (tree := tree) (lookups := lookups) (H := H) address ↪
    Unseen tree lookups H where
  toFun i := ⟨address i.val, i.property⟩
  inj' _ _ h := Subtype.ext (address.injective (congrArg Subtype.val h))

variable (d : ∀ i, ExactDecoder C (Fin (width i) → F))
variable (index : (Σ i : HiddenRole (tree := tree) (lookups := lookups) (H := H) address,
  Fin (width i.val)) ≃ Fin k)

/-- A scheduled scalar is frozen at its observed value, or named by one
polynomial variable in the tuple of all remaining decoded answers. -/
noncomputable def replayCoordinate (i : I) (j : Fin (width i)) : Poly (Fin k) F :=
  if h : address i ∈ revealed tree lookups H then MvPolynomial.C ((d i).decode (H (address i)) j)
  else X (index ⟨⟨i, h⟩, j⟩)

theorem replayCoordinate_degree (i : I) (j : Fin (width i)) :
    (replayCoordinate address d index i j).totalDegree ≤ 1 := by
  unfold replayCoordinate
  split_ifs <;> simp [totalDegree_X]

theorem replayCoordinate_eval (H' : ViewFiber tree lookups H) (i : I) (j : Fin (width i)) :
    eval (flatten index fun h => (d h.val).decode (H'.val (address h.val)))
      (replayCoordinate address d index i j) = (d i).decode (H'.val (address i)) j := by
  unfold replayCoordinate
  split_ifs with hi
  · rw [eval_C, (view_eq_iff tree lookups H H'.val).mp H'.property _ hi]
  · rw [eval_X, flatten_apply]

end ReplayCoordinates

end LfzkV1.ReplayDecode125
