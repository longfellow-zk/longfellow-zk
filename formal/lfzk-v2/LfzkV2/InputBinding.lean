import SumcheckV2.DotProduct

/-! Public/private input binding and zero padding, shared by circuit models. -/
namespace LfzkV2
open SumcheckV2 Classical
variable {F ι κ : Type} [Field F] [Fintype ι] [Fintype κ]

noncomputable def zeroExtend (index : ι ↪ κ) (values : ι → F) (j : κ) : F :=
  ∑ i, if index i = j then values i else 0

omit [Fintype κ] in
@[simp] theorem zeroExtend_apply (index : ι ↪ κ) (values : ι → F) (i : ι) :
    zeroExtend index values (index i) = values i := by
  simp [zeroExtend, index.injective.eq_iff]

omit [Fintype κ] in
theorem zeroExtend_outside (index : ι ↪ κ) (values : ι → F) (j : κ)
    (hout : ∀ i, index i ≠ j) : zeroExtend index values j = 0 := by
  simp [zeroExtend, hout]

theorem dot_zeroExtend (index : ι ↪ κ) (weights : κ → F) (values : ι → F) :
    dot weights (zeroExtend index values) = dot (weights ∘ index) values := by
  simp only [dot, zeroExtend, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite]

/-- A physical input vector contains exactly the public prefix and the committed
private suffix; every other position of the padded cube is zero. -/
noncomputable def circuitInputs {n nPublic nPrivate : ℕ} {Slot : Type}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube n)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (witness : Slot → F) : Cube n → F :=
  zeroExtend index (Sum.elim publicInputs (witness ∘ privateCoordinate))

theorem input_sum {n nPublic nPrivate : ℕ} {Slot : Type}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube n) (weights : Cube n → F)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (witness : Slot → F) :
    dot weights (circuitInputs index publicInputs privateCoordinate witness) =
      dot (Sum.elim (fun i => weights (index (.inl i))) (fun i => weights (index (.inr i))))
        (Sum.elim publicInputs (witness ∘ privateCoordinate)) := by
  rw [circuitInputs, dot_zeroExtend]
  congr 1
  funext i
  cases i <;> rfl

/-! ## Virtual inputs

A participant may reserve the suffix of its input array for virtual inputs:
per-proof affine views `constant + coefficient * x[source]` of committed
private inputs. They are neither public nor committed. Constraint compilation
substitutes their definitions like public inputs: each constant joins the
public side, and each coefficient joins the weight of its committed source.
This is `compile_packed` in the runtime's constraint compiler. -/

/-- One virtual input entry over a committed private input. -/
structure VirtualInput (Private F : Type) where
  source : Private
  constant : F
  coefficient : F

def VirtualInput.value {Private : Type} (v : VirtualInput Private F) (privateValues : Private → F) : F :=
  v.constant + v.coefficient * privateValues v.source

/-- The physical input vector `[public | committed | virtual]`: the committed
prefix as before, plus each virtual value at its own address. -/
noncomputable def virtualInputs {n nPublic nPrivate nVirtual : ℕ}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube n) (virtualIndex : Fin nVirtual ↪ Cube n)
    (publicInputs : Fin nPublic → F) (privateValues : Fin nPrivate → F)
    (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F) : Cube n → F :=
  circuitInputs index publicInputs id privateValues +
    zeroExtend virtualIndex fun v => (entries v).value privateValues

/-- Public-side weights after substitution: the public prefix, then one
entry per virtual input. -/
def substitutedPublicWeights {nPublic nVirtual : ℕ} (publicWeights : Fin nPublic → F)
    (virtualWeights : Fin nVirtual → F) : Fin (nPublic+nVirtual) → F :=
  Fin.append publicWeights virtualWeights

/-- Public-side values after substitution: each virtual input contributes
its constant, exactly as a public input would. -/
def substitutedPublicInputs {nPublic nPrivate nVirtual : ℕ} (publicInputs : Fin nPublic → F)
    (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F) : Fin (nPublic+nVirtual) → F :=
  Fin.append publicInputs fun v => (entries v).constant

/-- Committed weights after substitution: each virtual coefficient joins the
weight of its committed source. -/
noncomputable def substitutedPrivateWeights {nPrivate nVirtual : ℕ} (privateWeights : Fin nPrivate → F)
    (virtualWeights : Fin nVirtual → F) (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F)
    (i : Fin nPrivate) : F :=
  privateWeights i + ∑ v, if (entries v).source = i then virtualWeights v * (entries v).coefficient else 0

theorem dot_append {a b : ℕ} (x y : Fin a → F) (u v : Fin b → F) :
    dot (Fin.append x u) (Fin.append y v) = dot x y + dot u v := by
  simp only [dot,Fin.sum_univ_add,Fin.append_left,Fin.append_right]

/-- The `input_sum` identity with a third, disjoint index of virtual inputs:
the final input claim over `[public | committed | virtual]` equals the
substituted claim over the public side and the committed inputs only. -/
theorem virtual_input_sum {n nPublic nPrivate nVirtual : ℕ}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube n) (virtualIndex : Fin nVirtual ↪ Cube n)
    (weights : Cube n → F) (publicInputs : Fin nPublic → F) (privateValues : Fin nPrivate → F)
    (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F) :
    dot weights (virtualInputs index virtualIndex publicInputs privateValues entries) =
      dot (Sum.elim
          (substitutedPublicWeights (fun i => weights (index (.inl i))) (fun v => weights (virtualIndex v)))
          (substitutedPrivateWeights (fun i => weights (index (.inr i)))
            (fun v => weights (virtualIndex v)) entries))
        (Sum.elim (substitutedPublicInputs publicInputs entries) privateValues) := by
  have hsplit : dot weights (virtualInputs index virtualIndex publicInputs privateValues entries) =
      dot weights (circuitInputs index publicInputs id privateValues) +
        dot weights (zeroExtend virtualIndex fun v => (entries v).value privateValues) := by
    simp only [virtualInputs,dot,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  rw [hsplit,input_sum,dot_zeroExtend]
  simp only [dot,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,substitutedPublicWeights,
    substitutedPublicInputs,substitutedPrivateWeights,Fin.sum_univ_add,Fin.append_left,
    Fin.append_right,Function.comp_apply,id_eq,VirtualInput.value,add_mul,
    Finset.sum_add_distrib,mul_add]
  have hswap : (∑ i : Fin nPrivate, (∑ v : Fin nVirtual,
      if (entries v).source = i then weights (virtualIndex v) * (entries v).coefficient else 0) *
        privateValues i) =
      ∑ v : Fin nVirtual, weights (virtualIndex v) * ((entries v).coefficient *
        privateValues (entries v).source) := by
    simp only [Finset.sum_mul,ite_mul,zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ,if_true]
    ring
  rw [hswap]
  ring

/-- With disjoint addresses, every virtual address holds its virtual value. -/
theorem virtualInputs_virtual {n nPublic nPrivate nVirtual : ℕ}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube n) (virtualIndex : Fin nVirtual ↪ Cube n)
    (disjoint : ∀ j v, index j ≠ virtualIndex v)
    (publicInputs : Fin nPublic → F) (privateValues : Fin nPrivate → F)
    (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F) (v : Fin nVirtual) :
    virtualInputs index virtualIndex publicInputs privateValues entries (virtualIndex v) =
      (entries v).value privateValues := by
  simp only [virtualInputs,Pi.add_apply,circuitInputs,zeroExtend_apply]
  rw [zeroExtend_outside index _ _ (fun j => disjoint j v),zero_add]

/-- Addresses outside the virtual suffix keep their committed values. -/
theorem virtualInputs_committed {n nPublic nPrivate nVirtual : ℕ}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube n) (virtualIndex : Fin nVirtual ↪ Cube n)
    (publicInputs : Fin nPublic → F) (privateValues : Fin nPrivate → F)
    (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F) (u : Cube n)
    (outside : ∀ v, virtualIndex v ≠ u) :
    virtualInputs index virtualIndex publicInputs privateValues entries u =
      circuitInputs index publicInputs id privateValues u := by
  simp only [virtualInputs,Pi.add_apply]
  rw [zeroExtend_outside virtualIndex _ _ outside,add_zero]

end LfzkV2
