import Mathlib
import Merkle

/-!
# Collision extraction and standard-model binding

The first-divergence argument is pointwise in an arbitrary hash function. It
uses injectivity of each same-role serialization, but never assumes that leaf
and node serialization ranges are disjoint.
-/

open Finset Nat Heap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

universe uSalt uMsg uDigest uEnc

variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest}
variable {Enc : Type uEnc}
variable (S : Scheme Salt M D Enc) [Inhabited D]

/-- A genuine collision is equality of hash answers at distinct encoded
inputs.  Stated for a bare oracle, since the ROM games quantify over `H` with
the codec held fixed. -/
def Collision (H : Enc → D) : Prop := ∃ x₀ x₁ : Enc, x₀ ≠ x₁ ∧ H x₀ = H x₁

/-- The query-answer pairs relevant to one selected opened index inside a
possibly pruned multi-opening check. -/
def InIndexTrace (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (i : Fin n) (hi : i ∈ I)
    (x : Enc) (y : D) : Prop :=
  (x = S.leafEnc (pf.nonce ⟨i, hi⟩, a i) ∧
      y = checkValues S n I a pf (n + i.val)) ∨
    ∃ v : ℕ, v ∈ Heap.pathOf n i ∧ v < n ∧
      x = S.nodeEnc
        (checkValues S n I a pf (2 * v),
         checkValues S n I a pf (2 * v + 1)) ∧
      y = checkValues S n I a pf v

/-- Every recorded query-answer pair is consistent with `H`. -/
theorem indexTrace_sound (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (i : Fin n) (hi : i ∈ I)
    (x : Enc) (y : D)
    (hxy : InIndexTrace S n I a pf i hi x y) :
    y = S.H x := by
  rcases hxy with hleaf | hnode
  · rcases hleaf with ⟨rfl, rfl⟩
    exact checkValues_leaf S n I a pf i hi
  · rcases hnode with ⟨v, hvpath, hvlt, rfl, rfl⟩
    have hvpos : 0 < v := (Heap.mem_pathOf.mp hvpath).1
    have hvset : v ∈ Heap.pathSet n I :=
      Heap.mem_pathSet.mpr ⟨i, hi, hvpath⟩
    exact checkValues_node S n I a pf v
      ⟨hvpos, hvlt, hvset⟩

/-- If two checks disagree at a vertex on a common leaf path but agree at the
root, their node queries collide at the first parent where the values merge. -/
private theorem node_collision_of_value_diff
    (hnodeInj : Function.Injective S.nodeEnc)
    (n : ℕ) (I₀ I₁ : Finset (Fin n)) (a₀ a₁ : Fin n → M)
    (pf₀ : Opening n I₀ Salt D) (pf₁ : Opening n I₁ Salt D)
    (i : Fin n) (hi₀ : i ∈ I₀) (hi₁ : i ∈ I₁)
    (hroot : checkValues S n I₀ a₀ pf₀ 1 =
      checkValues S n I₁ a₁ pf₁ 1)
    (w : ℕ) (hw : w ∈ Heap.pathOf n i)
    (hdiff : checkValues S n I₀ a₀ pf₀ w ≠
      checkValues S n I₁ a₁ pf₁ w) :
    ∃ x₀ x₁ y,
      InIndexTrace S n I₀ a₀ pf₀ i hi₀ x₀ y ∧
      InIndexTrace S n I₁ a₁ pf₁ i hi₁ x₁ y ∧
      x₀ ≠ x₁ := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    by_cases hwroot : w = 1
    · subst w
      exact False.elim (hdiff hroot)
    · have hwpos : 0 < w := (Heap.mem_pathOf.mp hw).1
      have hwgt : 1 < w := by omega
      let p : ℕ := w / 2
      have hplt : p < w := by
        dsimp [p]
        exact Heap.parent_lt w (by omega)
      have hppath : p ∈ Heap.pathOf n i := by
        dsimp [p]
        exact Heap.parent_mem_pathOf hw hwgt
      have hppos : 0 < p := by
        dsimp [p]
        omega
      have hwbounds : 1 ≤ w ∧ w ≤ n + i.val :=
        Finset.mem_Icc.mp (Heap.pathOf_mem_nodes_iff hw)
      have hwle : w ≤ n + i.val := hwbounds.2
      have hpn : p < n := by
        dsimp [p]
        have hil := i.isLt
        omega
      have hp₀ : p ∈ Heap.pathSet n I₀ :=
        Heap.mem_pathSet.mpr ⟨i, hi₀, hppath⟩
      have hp₁ : p ∈ Heap.pathSet n I₁ :=
        Heap.mem_pathSet.mpr ⟨i, hi₁, hppath⟩
      by_cases hpeq : checkValues S n I₀ a₀ pf₀ p =
          checkValues S n I₁ a₁ pf₁ p
      · let q₀ : Enc := S.nodeEnc
          (checkValues S n I₀ a₀ pf₀ (2 * p),
           checkValues S n I₀ a₀ pf₀ (2 * p + 1))
        let q₁ : Enc := S.nodeEnc
          (checkValues S n I₁ a₁ pf₁ (2 * p),
           checkValues S n I₁ a₁ pf₁ (2 * p + 1))
        have hchild : w = 2 * p ∨ w = 2 * p + 1 := by
          dsimp [p]
          omega
        have hpairs :
            (checkValues S n I₀ a₀ pf₀ (2 * p),
             checkValues S n I₀ a₀ pf₀ (2 * p + 1)) ≠
            (checkValues S n I₁ a₁ pf₁ (2 * p),
             checkValues S n I₁ a₁ pf₁ (2 * p + 1)) := by
          intro heq
          rcases hchild with hwleft | hwright
          · apply hdiff
            rw [hwleft]
            exact congrArg Prod.fst heq
          · apply hdiff
            rw [hwright]
            exact congrArg Prod.snd heq
        have hqne : q₀ ≠ q₁ := by
          intro heq
          exact hpairs (hnodeInj heq)
        have hnode₀ := checkValues_node S n I₀ a₀ pf₀ p
          ⟨hppos, hpn, hp₀⟩
        have hnode₁ := checkValues_node S n I₁ a₁ pf₁ p
          ⟨hppos, hpn, hp₁⟩
        refine ⟨q₀, q₁,
          checkValues S n I₀ a₀ pf₀ p, ?_, ?_, hqne⟩
        · right
          exact ⟨p, hppath, hpn, rfl, rfl⟩
        · right
          refine ⟨p, hppath, hpn, rfl, ?_⟩
          exact hpeq
      · exact ih p hplt hppath hpeq

/-- Collision lemma for a common opened index. The returned pair contains one
query from each selected-index trace. -/
theorem mh_collision_lemma (hinj : S.Inj) (n : ℕ) (rt : D)
    (I₀ I₁ : Finset (Fin n)) (a₀ a₁ : Fin n → M)
    (pf₀ : Opening n I₀ Salt D) (pf₁ : Opening n I₁ Salt D)
    (hacc₀ : Accepts S n rt I₀ a₀ pf₀)
    (hacc₁ : Accepts S n rt I₁ a₁ pf₁)
    (i : Fin n) (hi₀ : i ∈ I₀) (hi₁ : i ∈ I₁)
    (hmsg : a₀ i ≠ a₁ i) :
    ∃ x₀ x₁ y,
      InIndexTrace S n I₀ a₀ pf₀ i hi₀ x₀ y ∧
      InIndexTrace S n I₁ a₁ pf₁ i hi₁ x₁ y ∧
      x₀ ≠ x₁ := by
  let leaf₀ : Enc := S.leafEnc (pf₀.nonce ⟨i, hi₀⟩, a₀ i)
  let leaf₁ : Enc := S.leafEnc (pf₁.nonce ⟨i, hi₁⟩, a₁ i)
  have hleafne : leaf₀ ≠ leaf₁ := by
    intro heq
    have hp := hinj.leaf heq
    exact hmsg (congrArg Prod.snd hp)
  have hroot : checkValues S n I₀ a₀ pf₀ 1 =
      checkValues S n I₁ a₁ pf₁ 1 := by
    rw [hacc₀.2, hacc₁.2]
  by_cases hleafval :
      checkValues S n I₀ a₀ pf₀ (n + i.val) =
      checkValues S n I₁ a₁ pf₁ (n + i.val)
  · refine ⟨leaf₀, leaf₁,
      checkValues S n I₀ a₀ pf₀ (n + i.val), ?_, ?_, hleafne⟩
    · left
      exact ⟨rfl, rfl⟩
    · left
      exact ⟨rfl, hleafval⟩
  · exact node_collision_of_value_diff S hinj.node n I₀ I₁
      a₀ a₁ pf₀ pf₁ i hi₀ hi₁ hroot (n + i.val)
      (Heap.leaf_mem_pathOf n i) hleafval

/-- The trace-level collision lemma implies a genuine collision of `H`. -/
theorem mh_collision (hinj : S.Inj) (n : ℕ) (rt : D)
    (I₀ I₁ : Finset (Fin n)) (a₀ a₁ : Fin n → M)
    (pf₀ : Opening n I₀ Salt D) (pf₁ : Opening n I₁ Salt D)
    (hacc₀ : Accepts S n rt I₀ a₀ pf₀)
    (hacc₁ : Accepts S n rt I₁ a₁ pf₁)
    (i : Fin n) (hi₀ : i ∈ I₀) (hi₁ : i ∈ I₁)
    (hmsg : a₀ i ≠ a₁ i) : Collision S.H := by
  rcases mh_collision_lemma S hinj n rt I₀ I₁
      a₀ a₁ pf₀ pf₁ hacc₀ hacc₁ i hi₀ hi₁ hmsg with
    ⟨x₀, x₁, y, hx₀, hx₁, hne⟩
  refine ⟨x₀, x₁, hne, ?_⟩
  rw [← indexTrace_sound S n I₀ a₀ pf₀ i hi₀ x₀ y hx₀,
    ← indexTrace_sound S n I₁ a₁ pf₁ i hi₁ x₁ y hx₁]

/-- A successful binding-game output. -/
structure BindingBreak (n : ℕ) (Salt : Type uSalt) (M : Type uMsg)
    (D : Type uDigest) (S : Scheme Salt M D Enc) [Inhabited D] where
  rt : D
  I₀ : Finset (Fin n)
  I₁ : Finset (Fin n)
  a₀ : Fin n → M
  a₁ : Fin n → M
  pf₀ : Opening n I₀ Salt D
  pf₁ : Opening n I₁ Salt D
  accepts₀ : Accepts S n rt I₀ a₀ pf₀
  accepts₁ : Accepts S n rt I₁ a₁ pf₁
  disagreement : ∃ i : Fin n, i ∈ I₀ ∧ i ∈ I₁ ∧ a₀ i ≠ a₁ i

/-- Standard-model binding reduction: every binding break constructively
yields a collision. No random-oracle assumption is used. -/
theorem mh_binding_of_collision (hinj : S.Inj) (n : ℕ)
    (out : BindingBreak n Salt M D S) : Collision S.H := by
  rcases out.disagreement with ⟨i, hi₀, hi₁, hmsg⟩
  exact mh_collision S hinj n out.rt
    out.I₀ out.I₁ out.a₀ out.a₁ out.pf₀ out.pf₁ out.accepts₀ out.accepts₁
    i hi₀ hi₁ hmsg

/-! ## Assumption-boundary regression -/

/-- If the leaf encoding is not injective, two different messages can open
the same one-leaf root without producing a collision. This executable theorem
guards the injectivity hypothesis of `mh_collision_lemma`. -/
theorem constant_leaf_encoding_break_without_collision :
    let S : Scheme Unit Bool Unit Unit :=
      { leafEnc := fun _ => (), nodeEnc := fun _ => (), H := fun _ => () }
    let I : Finset (Fin 1) := Finset.univ
    let pf : Opening 1 I Unit Unit :=
      { nonce := fun _ => (), frontierValue := fun _ => () }
    Accepts S 1 () I (fun _ => false) pf ∧
    Accepts S 1 () I (fun _ => true) pf ∧
    (∀ i : Fin 1, (fun _ : Fin 1 => false) i ≠ (fun _ : Fin 1 => true) i) ∧
    ¬Collision S.H := by
  dsimp
  refine ⟨⟨by simp, Subsingleton.elim _ _⟩,
    ⟨by simp, Subsingleton.elim _ _⟩, ?_, ?_⟩
  · intro i
    decide
  · rintro ⟨x₀, x₁, hne, _⟩
    exact hne (Subsingleton.elim _ _)

end MH

end Merkle
