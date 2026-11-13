import LfzkV2.Current.PrimeClaim
import LfzkV2.Layered.Replay
import LfzkV2.Packed.Backend

/-! Physical full-cell addresses at zk-v2's selected commitment boundary.
The two fingerprint masks follow every original frontend cell. Prime shared
inputs are absent from this vector; their values are supplied by binary input
reconstruction. Backend row/column addresses are ordinary quotient/remainder
coordinates after the row's random prefix. -/
noncomputable section
namespace LfzkV2.Current.CellLayout
open SumcheckV2
open scoped Classical

/-- The selector adds precisely its two dedicated backend cells. -/
def selected (cells : ℕ) : (Fin cells ⊕ Fin 2) ≃ Fin (cells+2) := finSumFinEquiv

@[simp] theorem selected_original (cells : ℕ) (i : Fin cells) :
    (selected cells (.inl i)).val = i.val := rfl

@[simp] theorem selected_mask (cells : ℕ) (i : Fin 2) :
    (selected cells (.inr i)).val = cells+i.val := by simp [selected, finSumFinEquiv]

/-- All frontend cells, including its appended masks, use the same logical
witness prefix in the ordinary Polygero rows. -/
def primary {cells rows width : ℕ} (hwidth : 0 < width) (capacity : cells ≤ rows*width) :
    Fin cells ↪ (Fin rows × Fin width) where
  toFun i := (⟨i.val/width, Nat.div_lt_of_lt_mul (by
      have hi := lt_of_lt_of_le i.isLt capacity
      simpa only [Nat.mul_comm] using hi)⟩,⟨i.val%width,Nat.mod_lt _ hwidth⟩)
  inj' := by
    intro i j h
    have hd := congrArg (fun x => x.1.val) h
    have hm := congrArg (fun x => x.2.val) h
    apply Fin.ext
    have hi := Nat.mod_add_div i.val width
    have hj := Nat.mod_add_div j.val width
    change i.val/width = j.val/width at hd
    change i.val%width = j.val%width at hm
    rw [hd, hm] at hi
    exact hi.symm.trans hj

@[simp] theorem primary_row {cells rows width : ℕ} (hw : 0 < width)
    (hc : cells ≤ rows*width) (i : Fin cells) : (primary hw hc i).1.val = i.val/width := rfl
@[simp] theorem primary_column {cells rows width : ℕ} (hw : 0 < width)
    (hc : cells ≤ rows*width) (i : Fin cells) : (primary hw hc i).2.val = i.val%width := rfl

namespace Binary

/-- Nontrivial binary packing: words, independent masks followed by r and b, then the
complete sumcheck-pad suffix. The selector's two cells follow this count. -/
def cells (words degree pads : ℕ) : ℕ := words+(degree+1)+pads

def word (words degree pads : ℕ) (i : Fin words) : Fin (cells words degree pads+2) :=
  ⟨i.val,by dsimp [cells]; omega⟩
def mask (words degree pads : ℕ) (i : Fin (degree-1)) : Fin (cells words degree pads+2) :=
  ⟨words+i.val,by have := i.isLt; dsimp [cells]; omega⟩
def random (words degree pads : ℕ) : Fin (cells words degree pads+2) :=
  ⟨words+(degree-1),by dsimp [cells]; omega⟩
def frobenius (words degree pads : ℕ) : Fin (cells words degree pads+2) :=
  ⟨words+degree,by dsimp [cells]; omega⟩
def pad (words degree pads : ℕ) (i : Fin pads) : Fin (cells words degree pads+2) :=
  ⟨words+(degree+1)+i.val,by have := i.isLt; dsimp [cells]; omega⟩

/-- Pivot-zero packing uses the same physical mask order as the runtime:
t_1,...,t_(m-1),r,b. No standalone input-bitness constraints are introduced. -/
def packing {F : Type} [Field F] [Algebra (ZMod 2) F]
    {words degree pads : ℕ} (hd : 1 < degree) (basis : Module.Basis (Fin degree) (ZMod 2) F)
    (coefficients : Fin words → Fin degree → F)
    (target : LinearRow (Fin (cells words degree pads+2)) F) :
    Packed.Statement (ZMod 2) F (Fin degree) (Fin words) (Fin (cells words degree pads+2)) where
  basis := basis
  pivot := ⟨0,by omega⟩
  word := word words degree pads
  mask i := mask words degree pads ⟨i.val.val-1,by
    have hi := i.val.isLt
    have hn : i.val.val ≠ 0 := by intro h; apply i.property; exact Fin.ext h
    omega⟩
  random := random words degree pads
  frobeniusCell := frobenius words degree pads
  coefficients := coefficients
  target := target

@[simp] theorem pad_val (words degree pads : ℕ) (i : Fin pads) :
    (pad words degree pads i).val = words+(degree+1)+i.val := rfl

end Binary

namespace Prime

/-- The two selector masks are present in the full cell view, but have no
prime input or pad address. Thus their frontend coefficients are zero. -/
abbrev Other (remaining pads : ℕ) := Fin remaining ⊕ (Fin pads ⊕ Fin 2)
abbrev Slot (remaining pads : ℕ) := Other remaining pads ⊕ Unit

def cells (remaining pads : ℕ) : ℕ := remaining+1+pads

private def unitFin : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := Subsingleton.elim _ _

/-- Reorder the typed slots into the exact physical order: remaining private
inputs, hiding scalar R, prime sumcheck pads, then both fingerprint masks. -/
def index (remaining pads : ℕ) : Slot remaining pads ≃ Fin (cells remaining pads+2) :=
  ((Equiv.sumAssoc (Fin remaining) (Fin pads ⊕ Fin 2) Unit).trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _))).trans
    ((Equiv.sumCongr (Equiv.refl _)
      ((Equiv.sumCongr unitFin finSumFinEquiv).trans finSumFinEquiv)).trans
      (finSumFinEquiv.trans (finCongr (by dsimp [cells]; omega))))

/-- Every original prime cell and the two fresh masks are selected. -/
def layout (remaining pads : ℕ) :
    (Fin (cells remaining pads) ⊕ Fin 2) ≃ Slot remaining pads :=
  (selected (cells remaining pads)).trans (index remaining pads).symm

@[simp] theorem index_private (remaining pads : ℕ) (i : Fin remaining) :
    (index remaining pads (.inl (.inl i))).val = i.val := rfl
@[simp] theorem index_hiding (remaining pads : ℕ) :
    (index remaining pads (.inr ())).val = remaining := by
  simp [index, unitFin, finSumFinEquiv]
@[simp] theorem index_pad (remaining pads : ℕ) (i : Fin pads) :
    (index remaining pads (.inl (.inr (.inl i)))).val = remaining+1+i.val := by
  simp [index, finSumFinEquiv, Nat.add_assoc]
@[simp] theorem index_fingerprint (remaining pads : ℕ) (i : Fin 2) :
    (index remaining pads (.inl (.inr (.inr i)))).val = cells remaining pads+i.val := by
  change remaining+(1+(pads+i.val)) = cells remaining pads+i.val
  simp [cells, Nat.add_assoc]

/-- Reconstruct only logical prime inputs. Shared bits occupy a separate
summand and never obtain a committed prime coordinate. -/
def input (shared remaining pads : ℕ) : Fin (shared+remaining) → Fin shared ⊕ Other remaining pads :=
  fun i => match finSumFinEquiv.symm i with
    | .inl j => .inl j
    | .inr j => .inr (.inl j)

def pad (remaining pads : ℕ) (i : Fin pads) : Other remaining pads := .inr (.inl i)
def fingerprint (remaining pads : ℕ) (i : Fin 2) : Other remaining pads := .inr (.inr i)

@[simp] theorem pad_ne_fingerprint (remaining pads : ℕ) (i : Fin pads) (j : Fin 2) :
    pad remaining pads i ≠ fingerprint remaining pads j := by simp [pad, fingerprint]

theorem input_ne_fingerprint (shared remaining pads : ℕ) (i : Fin (shared+remaining)) (j : Fin 2) :
    input shared remaining pads i ≠ .inr (fingerprint remaining pads j) := by
  unfold input
  cases finSumFinEquiv.symm i <;> simp [fingerprint]

/-- The prime compiler names only private inputs and sumcheck pads. Its
full-cell selector nevertheless retains the later dedicated fingerprint cells. -/
def rows {F : Type} [Field F] {shared remaining pads nPublic : ℕ}
    (cs : Linear.Constraints (Fin pads) F)
    (publicWeights publicInputs : Fin nPublic → F)
    (privateWeights : Fin (shared+remaining) → F) :
    List (LinearRow (Fin shared ⊕ Other remaining pads) F) :=
  Linear.compile cs (fun i => .inr (pad remaining pads i))
    (input shared remaining pads) publicWeights publicInputs privateWeights

/-- No frontend row can use a dedicated fingerprint-mask address. -/
theorem rows_avoid_fingerprint {F : Type} [Field F] {shared remaining pads nPublic : ℕ}
    (cs : Linear.Constraints (Fin pads) F)
    (publicWeights publicInputs : Fin nPublic → F)
    (privateWeights : Fin (shared+remaining) → F) (j : Fin 2)
    (row : LinearRow (Fin shared ⊕ Other remaining pads) F)
    (hr : row ∈ rows cs publicWeights publicInputs privateWeights)
    (term : (Fin shared ⊕ Other remaining pads) × F) (ht : term ∈ row.terms) :
    term.1 ≠ .inr (fingerprint remaining pads j) := by
  simp only [rows, Linear.compile, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨r,_,rfl⟩ | rfl
  · obtain ⟨t,_,rfl⟩ := List.mem_map.mp ht
    simp [mapTerms, pad, fingerprint] at *
  · simp only [compileInput, List.mem_append, List.mem_ofFn, mapTerms, List.mem_map] at ht
    rcases ht with ⟨i,rfl⟩ | ⟨t,_,rfl⟩
    · exact input_ne_fingerprint _ _ _ _ _
    · simp [pad, fingerprint]

/-- The split claim of the prime compiler on its physical cells: the layer
rows on native pad cells and the split input equation. -/
def claim {F : Type} [Field F] {shared remaining pads nPublic : ℕ}
    (cs : Linear.Constraints (Fin pads) F)
    (publicWeights publicInputs : Fin nPublic → F)
    (privateWeights : Fin (shared+remaining) → F) :
    LfzkV2.Current.Prime.Claim (Fin shared) (Other remaining pads) F :=
  LfzkV2.Current.Prime.Claim.ofConstraints cs (pad remaining pads) (input shared remaining pads)
    publicWeights publicInputs privateWeights

/-- The split claim retains zero weights on both fingerprint cells, and its
layer rows never read them; only the selection wrapper appends equations
mentioning them. -/
theorem claim_fingerprint_zero {F : Type} [Field F] {shared remaining pads nPublic : ℕ}
    (cs : Linear.Constraints (Fin pads) F)
    (publicWeights publicInputs : Fin nPublic → F)
    (privateWeights : Fin (shared+remaining) → F) (j : Fin 2) :
    (claim cs publicWeights publicInputs privateWeights).otherWeights (fingerprint remaining pads j) = 0 ∧
      ∀ row ∈ (claim cs publicWeights publicInputs privateWeights).layers, ∀ term ∈ row.terms,
        term.1 ≠ fingerprint remaining pads j := by
  constructor
  · have hinput := rows_avoid_fingerprint cs publicWeights publicInputs privateWeights j _
      (List.mem_append_right _ (List.mem_singleton_self _))
    unfold claim LfzkV2.Current.Prime.Claim.ofConstraints LfzkV2.Current.Prime.Claim.split
      LfzkV2.Current.Prime.coefficients
    simp only [neg_eq_zero]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
    simp [hinput t ht]
  · intro row hrow term hterm
    simp only [claim, LfzkV2.Current.Prime.Claim.ofConstraints, LfzkV2.Current.Prime.Claim.split,
      LfzkV2.Current.Prime.nativeLayers, List.mem_map] at hrow
    obtain ⟨r,_,rfl⟩ := hrow
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hterm
    simp [pad, fingerprint]

end Prime

namespace Pads

/-- Each ordinary layer owns two cells per round, followed by A,B,AB,D. -/
def count {F : Type} : {out input : ℕ} → Layered.Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .entry _ _ rest => count rest
  | _, _, .layer (mid := mid) _ _ rest => 2*mid+4+count rest

/-- A total typed allocation of exactly the runtime suffix. The supplied
address map usually adds the fixed packing/prime prefix to these indices. -/
def plan {F Pad : Type} {out input : ℕ} (circuit : Layered.Circuit F out input)
    (address : Fin (count circuit) → Pad) : Layered.Replay.PadPlan (Pad := Pad) circuit :=
  match circuit with
  | .input => ()
  | .entry _ _ rest => plan rest address
  | .layer (mid := mid) _ _ rest =>
      ({ round := fun i => (address ⟨2*i.val,by have := i.isLt; dsimp [count]; omega⟩,
            address ⟨2*i.val+1,by have := i.isLt; dsimp [count]; omega⟩)
         a := address ⟨2*mid,by dsimp [count]; omega⟩
         b := address ⟨2*mid+1,by dsimp [count]; omega⟩
         ab := address ⟨2*mid+2,by dsimp [count]; omega⟩
         d := address ⟨2*mid+3,by dsimp [count]; omega⟩ },
       plan rest (fun i => address ⟨2*mid+4+i.val,by have := i.isLt; dsimp [count]; omega⟩))

end Pads
end LfzkV2.Current.CellLayout
