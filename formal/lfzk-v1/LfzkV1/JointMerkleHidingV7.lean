import Merkle.CheckPass

/-! Joint leaf programming for the two independent v7 Merkle oracles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LfzkV1.JointMerkleHidingV7

open Finset Merkle.MH Merkle.RandomOracle
open scoped Classical

section Programming

variable {Index Enc D : Type}

/-- Program the selected leaf addresses. If several selected indices name
the same address, retain one fixed choice, independent of the background table. -/
def program (address : Index → Enc) (selected : Index → Prop) (H : Enc → D)
    (leaves : Index → D) (x : Enc) : D :=
  if h : ∃ i, selected i ∧ address i = x then leaves (Classical.choose h) else H x

theorem program_at (address : Index → Enc) (selected : Index → Prop) (H : Enc → D)
    (leaves : Index → D) (injective : Function.Injective address) (i : Index)
    (hi : selected i) : program address selected H leaves (address i) = leaves i := by
  have h : ∃ j, selected j ∧ address j = address i := ⟨i, hi, rfl⟩
  rw [program, dif_pos h, injective (Classical.choose_spec h).2]

theorem program_off (address : Index → Enc) (selected : Index → Prop) (H : Enc → D)
    (leaves : Index → D) (x : Enc) (absent : ∀ i, selected i → address i ≠ x) :
    program address selected H leaves x = H x := by
  unfold program
  exact dif_neg (fun ⟨i, hi, he⟩ => absent i hi he)

private theorem program_restore (address : Index → Enc) (H : Enc → D) (leaves : Index → D)
    (injective : Function.Injective address) :
    program address (fun _ => True) (program address (fun _ => True) H leaves)
      (fun i => H (address i)) = H := by
  funext x
  by_cases present : ∃ i, address i = x
  · obtain ⟨i, rfl⟩ := present
    exact program_at address _ _ _ injective i trivial
  · have off (i : Index) : address i ≠ x := fun he => present ⟨i, he⟩
    rw [program_off _ _ _ _ _ (fun i _ => off i), program_off _ _ _ _ _ (fun i _ => off i)]

/-- Swap the background oracle's leaves with independent labels. The
collision branch is the identity, so the map is a permutation on all coins. -/
def swap (address : Index → Enc) (coins : (Enc → D) × (Index → D)) :
    (Enc → D) × (Index → D) :=
  if Function.Injective address then
    (program address (fun _ => True) coins.1 coins.2, fun i => coins.1 (address i))
  else coins

theorem swap_involutive (address : Index → Enc) :
    Function.Involutive (swap (D := D) address) := by
  rintro ⟨H, leaves⟩
  by_cases hi : Function.Injective address
  · simp only [swap, if_pos hi]
    exact Prod.ext (program_restore address H leaves hi)
      (funext fun i => program_at address _ H leaves hi i trivial)
  · simp only [swap, if_neg hi]

def swapEquiv (address : Index → Enc) :
    ((Enc → D) × (Index → D)) ≃ ((Enc → D) × (Index → D)) where
  toFun := swap address
  invFun := swap address
  left_inv := swap_involutive address
  right_inv := swap_involutive address

theorem swap_oracle_of_injective (address : Index → Enc) (injective : Function.Injective address)
    (H : Enc → D) (leaves : Index → D) :
    (swapEquiv address (H, leaves)).1 = program address (fun _ => True) H leaves := by
  simp only [swapEquiv, Equiv.coe_fn_mk, swap, if_pos injective]

/-- Compare the full programmed oracle with a public observer's oracle.
The observer may see opened addresses and any ordinary node addresses. -/
theorem run_program_eq_of_no_hidden_hit {Out : Type} {fuel : ℕ}
    (address : Index → Enc) (opened : Index → Prop) (H : Enc → D) (leaves : Index → D)
    (injective : Function.Injective address) (observer : Tree Enc D Out fuel)
    (miss : ∀ qa ∈ (observer.run (program address opened H leaves)).2,
      ∀ i, ¬ opened i → address i ≠ qa.1) :
    observer.run (program address (fun _ => True) H leaves) =
      observer.run (program address opened H leaves) := by
  apply Tree.run_congr_on_trace
  intro qa hqa
  rw [Tree.trace_sound observer _ qa hqa]
  by_cases h : ∃ i, address i = qa.1
  · obtain ⟨i, hi⟩ := h
    have ho : opened i := by_contra fun hno => miss qa hqa i hno hi
    rw [← hi, program_at _ _ _ _ injective _ trivial, program_at _ _ _ _ injective _ ho]
  · rw [program_off _ _ _ _ _ (fun i _ hi => h ⟨i, hi⟩),
        program_off _ _ _ _ _ (fun i _ hi => h ⟨i, hi⟩)]

end Programming

section Trees

variable {Salt M D Enc : Type} [Inhabited D] {n : ℕ}

private def ghostCodec (codec : Codec Salt M D Enc) : Codec (Fin n) Unit D (Enc ⊕ Fin n) where
  leafEnc sm := .inr sm.1
  nodeEnc children := .inl (codec.nodeEnc children)

/-- Compute all vertices using the ordinary node oracle and independent
leaf labels. Neither opened nor hidden preimages enter this computation. -/
def labels (codec : Codec Salt M D Enc) (H : Enc → D) (leaves : Fin n → D) : ℕ → D :=
  commitLabels ((ghostCodec codec).withOracle (Sum.elim H leaves)) n id (fun _ => ())

private theorem commit_eq_labels (codec : Codec Salt M D Enc) (H full : Enc → D)
    (nonces : Fin n → Salt) (columns : Fin n → M) (leaves : Fin n → D)
    (leafAnswers : ∀ i, full (codec.leafEnc (nonces i, columns i)) = leaves i)
    (nodeAnswers : ∀ children, full (codec.nodeEnc children) = H (codec.nodeEnc children))
    (v : ℕ) :
    commitLabels (codec.withOracle full) n nonces columns v = labels codec H leaves v := by
  unfold labels
  conv_lhs => rw [commitLabels]
  conv_rhs => rw [commitLabels]
  split_ifs with hl hn
  · exact leafAnswers _
  · change full (codec.nodeEnc (commitLabels (codec.withOracle full) n nonces columns (2 * v),
      commitLabels (codec.withOracle full) n nonces columns (2 * v + 1))) =
      H (codec.nodeEnc (labels codec H leaves (2 * v), labels codec H leaves (2 * v + 1)))
    rw [nodeAnswers,
      commit_eq_labels codec H full nonces columns leaves leafAnswers nodeAnswers (2 * v),
      commit_eq_labels codec H full nonces columns leaves leafAnswers nodeAnswers (2 * v + 1)]
  · rfl
termination_by 2 * n - v
decreasing_by all_goals omega

end Trees

section TwoTrees

variable {Salt M₁ M₂ D Enc₁ Enc₂ : Type} {n₁ n₂ : ℕ}

def leafAddress (codec₁ : Codec Salt M₁ D Enc₁) (codec₂ : Codec Salt M₂ D Enc₂)
    (columns₁ : Fin n₁ → M₁) (columns₂ : Fin n₂ → M₂) :
    (Fin n₁ ⊕ Fin n₂) → Salt → Enc₁ ⊕ Enc₂
  | .inl i, salt => .inl (codec₁.leafEnc (salt, columns₁ i))
  | .inr i, salt => .inr (codec₂.leafEnc (salt, columns₂ i))

theorem leafAddress_injective (codec₁ : Codec Salt M₁ D Enc₁) (codec₂ : Codec Salt M₂ D Enc₂)
    (columns₁ : Fin n₁ → M₁) (columns₂ : Fin n₂ → M₂)
    (enc₁ : Function.Injective codec₁.leafEnc) (enc₂ : Function.Injective codec₂.leafEnc)
    (unique₁ : Function.Injective columns₁) (unique₂ : Function.Injective columns₂) :
    Function.Injective (Function.uncurry (leafAddress codec₁ codec₂ columns₁ columns₂)) := by
  rintro ⟨i | i, a⟩ ⟨j | j, b⟩ he
  · have h := enc₁ (Sum.inl.inj he)
    exact Prod.ext (congrArg Sum.inl (unique₁ (congrArg Prod.snd h))) (congrArg Prod.fst h)
  · cases he
  · cases he
  · have h := enc₂ (Sum.inr.inj he)
    exact Prod.ext (congrArg Sum.inr (unique₂ (congrArg Prod.snd h))) (congrArg Prod.fst h)

variable [Inhabited D]

/-- On the injective branch, both roots and frontiers come from the same
label functions the real verifier would recompute. -/
theorem coupled_labels_eq (codec₁ : Codec Salt M₁ D Enc₁) (codec₂ : Codec Salt M₂ D Enc₂)
    (salts : Fin n₁ ⊕ Fin n₂ → Salt)
    (columns₁ : Fin n₁ → M₁) (columns₂ : Fin n₂ → M₂)
    (H : Enc₁ ⊕ Enc₂ → D) (leaves : Fin n₁ ⊕ Fin n₂ → D)
    (node₁ : ∀ children sm, codec₁.nodeEnc children ≠ codec₁.leafEnc sm)
    (node₂ : ∀ children sm, codec₂.nodeEnc children ≠ codec₂.leafEnc sm)
    (injective : Function.Injective (fun i => leafAddress codec₁ codec₂ columns₁ columns₂ i (salts i))) :
    let address := fun i => leafAddress codec₁ codec₂ columns₁ columns₂ i (salts i)
    let full := (swapEquiv address (H, leaves)).1
    commitLabels (codec₁.withOracle (full ∘ Sum.inl)) n₁ (salts ∘ Sum.inl) columns₁ =
      labels codec₁ (H ∘ Sum.inl) (leaves ∘ Sum.inl) ∧
    commitLabels (codec₂.withOracle (full ∘ Sum.inr)) n₂ (salts ∘ Sum.inr) columns₂ =
      labels codec₂ (H ∘ Sum.inr) (leaves ∘ Sum.inr) := by
  dsimp only
  rw [swap_oracle_of_injective _ injective]
  constructor <;> funext v
  · apply commit_eq_labels
    · intro i
      exact program_at _ _ _ _ injective (.inl i) trivial
    · intro children
      apply program_off
      rintro (i | i) _ hi
      · exact node₁ _ _ (Sum.inl.inj hi).symm
      · cases hi
  · apply commit_eq_labels
    · intro i
      exact program_at _ _ _ _ injective (.inr i) trivial
    · intro children
      apply program_off
      rintro (i | i) _ hi
      · cases hi
      · exact node₂ _ _ (Sum.inr.inj hi).symm

end TwoTrees

end LfzkV1.JointMerkleHidingV7
