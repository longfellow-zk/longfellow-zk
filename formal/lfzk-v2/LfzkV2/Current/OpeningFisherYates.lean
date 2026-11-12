import LfzkV2.Current.OpeningSampling

/-! The opening sampler's partial Fisher–Yates permutation. One chooses a
uniform offset in the remaining array, swaps it to the front, emits that
column, and continues on the tail. The recursion below is the same array
operation as the runtime loop after shifting its index `i` to zero. -/
noncomputable section
namespace LfzkV2.Current.OpeningFisherYates
open LigeroFamily
open scoped Classical

/-- The successive integer draws have sizes `n,n-1,...,n-t+1`. -/
def Choices (n t : ℕ) : Type :=
  match t with
  | 0 => Unit
  | t+1 => match n with
    | 0 => Empty
    | n+1 => Fin (n+1) × Choices n t
termination_by structural t

instance choicesFintype (n t : ℕ) : Fintype (Choices n t) :=
  match t with
  | 0 => inferInstanceAs (Fintype Unit)
  | t+1 => match n with
    | 0 => inferInstanceAs (Fintype Empty)
    | n+1 => by
      letI := choicesFintype n t
      exact inferInstanceAs (Fintype (Fin (n+1) × Choices n t))
termination_by structural t

/-- A selected head and an injective tail avoiding that head describe
exactly one ordered opening. -/
def headTail (n t : ℕ) :
    (Fin (t+1) ↪ Fin (n+1)) ≃
      (Σ head : Fin (n+1), Fin t ↪ {column : Fin (n+1) // column ≠ head}) where
  toFun indices := ⟨indices 0,{
    toFun i := ⟨indices i.succ,by
      intro h
      exact Fin.succ_ne_zero i (indices.injective h)⟩
    inj' _ _ h := Fin.succ_injective t (indices.injective (congrArg Subtype.val h)) }⟩
  invFun pair := {
    toFun := Fin.cases pair.1 (fun i => (pair.2 i).val)
    inj' := by
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _; rfl
        · intro h; exact False.elim ((pair.2 j).property h.symm)
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro h; exact False.elim ((pair.2 i).property h)
        · intro h; exact congrArg Fin.succ (pair.2.injective (Subtype.ext h)) }
  left_inv indices := by
    apply Function.Embedding.ext
    intro i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv pair := by
    rcases pair with ⟨head,tail⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Function.Embedding.ext
    intro i
    rfl

/-- Swapping the chosen position with zero leaves this precise enumeration
of the remaining tail. It preserves the runtime array order, rather than
sorting or deleting the chosen value. -/
def remaining (n : ℕ) (head : Fin (n+1)) : Fin n ≃ {column : Fin (n+1) // column ≠ head} :=
  (finSuccAboveEquiv (0 : Fin (n+1))).trans
    ((Equiv.swap (0 : Fin (n+1)) head).subtypeEquiv (by
      intro column
      constructor
      · intro hne heq
        exact hne ((Equiv.swap (0 : Fin (n+1)) head).injective
          (heq.trans (Equiv.swap_apply_left _ _).symm))
      · intro hne heq
        subst column
        exact hne (Equiv.swap_apply_left _ _)))

@[simp] theorem remaining_val (n : ℕ) (head : Fin (n+1)) (i : Fin n) :
    ((remaining n head) i).val = Equiv.swap (0 : Fin (n+1)) head i.succ := by
  change Equiv.swap (0 : Fin (n+1)) head ((0 : Fin (n+1)).succAbove i) = _
  rw [Fin.succAbove_zero]

/-- The first offset and the remaining normalized opening are independent
product coordinates of the whole ordered opening. -/
def step (n t : ℕ) : (Fin (t+1) ↪ Fin (n+1)) ≃ Fin (n+1) × (Fin t ↪ Fin n) :=
  (headTail n t).trans
    ((Equiv.sigmaCongrRight fun head =>
      (Equiv.refl (Fin t)).embeddingCongr (remaining n head).symm).trans
        (Equiv.sigmaEquivProd _ _))

/-- The exact partial shuffle is a bijection from its independent bounded
integer offsets to ordered samples without replacement. -/
def ordered : (n t : ℕ) → Choices n t ≃ (Fin t ↪ Fin n)
  | n, 0 => {
      toFun _ := ⟨Fin.elim0,by intro i; exact Fin.elim0 i⟩
      invFun _ := ()
      left_inv value := by cases value; rfl
      right_inv indices := by apply Function.Embedding.ext; intro i; exact Fin.elim0 i }
  | 0, t+1 => {
      toFun := Empty.elim
      invFun indices := Fin.elim0 (indices 0)
      left_inv value := Empty.elim value
      right_inv indices := Fin.elim0 (indices 0) }
  | n+1, t+1 =>
      (Equiv.prodCongr (Equiv.refl (Fin (n+1))) (ordered n t)).trans (step n t).symm

@[simp] theorem ordered_zero (n t : ℕ) (head : Fin (n+1)) (tail : Choices n t) :
    ordered (n+1) (t+1) (head,tail) 0 = head := rfl

@[simp] theorem ordered_succ (n t : ℕ) (head : Fin (n+1)) (tail : Choices n t) (i : Fin t) :
    ordered (n+1) (t+1) (head,tail) i.succ =
      Equiv.swap (0 : Fin (n+1)) head (ordered n t tail i).succ :=
  remaining_val n head (ordered n t tail i)

/-- Integer sampling and order forgetting compose through proved bijections;
no uniform-opening certificate is supplied to the final decoder. -/
def queryDecoder {Raw Unused : Type} [Fintype Raw] [Fintype Unused]
    (n t : ℕ) (factor : Raw ≃ Choices n t × Unused) : BalancedDecoder Raw (QuerySet n t) :=
  OpeningSampling.decoder (factor.trans
    (Equiv.prodCongr (ordered n t) (Equiv.refl Unused)))

@[simp] theorem queryDecoder_decode {Raw Unused : Type} [Fintype Raw] [Fintype Unused]
    (n t : ℕ) (factor : Raw ≃ Choices n t × Unused) (raw : Raw) :
    (queryDecoder n t factor).decode raw = OrderedOpening.query (ordered n t (factor raw).1) := rfl

end LfzkV2.Current.OpeningFisherYates
