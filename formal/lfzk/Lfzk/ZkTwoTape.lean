import Merkle.TreeCompose

/-!
# Two independent lazily sampled oracles

The two-field protocol commits two Merkle trees, one per circuit.  This file runs a distinguisher
that may query **both** Merkle oracles, interleaved and adaptively, against two independent lazy
tapes (`lazyRun2`), and proves the one fact the hybrid argument needs: seen from either oracle, the
other is just more coins.  `proj₁ τ₂` answers the second oracle's queries internally from its tape
`τ₂` and keeps the first oracle's queries as queries; `lazyRun_proj₁` says running the projection on
`τ₁` is running the two-oracle tree.  So a two-oracle distinguisher is a one-oracle distinguisher
for either commitment, with the same query budget — which is what lets each side's opening-hiding
bound apply in turn.

(The deployed trees both use SHA-256 on raw strings; treating them as two independent random
oracles is a domain-separation idealisation, stated where it is used.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkTwoTape

open Merkle.RandomOracle

variable {Q₁ Q₂ D A : Type} [DecidableEq Q₁] [DecidableEq Q₂] {T₁ T₂ : ℕ}

/-- **A tree over two independent lazy oracles.**  `inl` queries read tape `τ₁` at their slot in
`s₁`, `inr` queries read `τ₂` at their slot in `s₂`. -/
def lazyRun2 (τ₁ : Fin T₁ → D) (τ₂ : Fin T₂ → D) (dflt : D) :
    {fuel : ℕ} → Tree (Q₁ ⊕ Q₂) D A fuel → List Q₁ → List Q₂ → A
  | _, .done a, _, _ => a
  | _, .query (.inl q) next, s₁, s₂ =>
      lazyRun2 τ₁ τ₂ dflt
        (next (tapeAt τ₁ dflt ((if q ∈ s₁ then s₁ else s₁ ++ [q]).idxOf q)))
        (if q ∈ s₁ then s₁ else s₁ ++ [q]) s₂
  | _, .query (.inr q) next, s₁, s₂ =>
      lazyRun2 τ₁ τ₂ dflt
        (next (tapeAt τ₂ dflt ((if q ∈ s₂ then s₂ else s₂ ++ [q]).idxOf q)))
        s₁ (if q ∈ s₂ then s₂ else s₂ ++ [q])

/-- **Seen from the first oracle**: answer the second oracle's queries from `τ₂`. -/
def proj₁ (τ₂ : Fin T₂ → D) (dflt : D) :
    {fuel : ℕ} → Tree (Q₁ ⊕ Q₂) D A fuel → List Q₂ → Tree Q₁ D A fuel
  | _, .done a, _ => .done a
  | _, .query (.inl q) next, s₂ => .query q fun y => proj₁ τ₂ dflt (next y) s₂
  | _, .query (.inr q) next, s₂ =>
      (proj₁ τ₂ dflt (next (tapeAt τ₂ dflt ((if q ∈ s₂ then s₂ else s₂ ++ [q]).idxOf q)))
        (if q ∈ s₂ then s₂ else s₂ ++ [q])).weaken

/-- **Seen from the second oracle**: answer the first oracle's queries from `τ₁`. -/
def proj₂ (τ₁ : Fin T₁ → D) (dflt : D) :
    {fuel : ℕ} → Tree (Q₁ ⊕ Q₂) D A fuel → List Q₁ → Tree Q₂ D A fuel
  | _, .done a, _ => .done a
  | _, .query (.inr q) next, s₁ => .query q fun y => proj₂ τ₁ dflt (next y) s₁
  | _, .query (.inl q) next, s₁ =>
      (proj₂ τ₁ dflt (next (tapeAt τ₁ dflt ((if q ∈ s₁ then s₁ else s₁ ++ [q]).idxOf q)))
        (if q ∈ s₁ then s₁ else s₁ ++ [q])).weaken

/-- **The projection runs the two-oracle tree.** -/
theorem lazyRun_proj₁ (τ₁ : Fin T₁ → D) (τ₂ : Fin T₂ → D) (dflt : D) :
    ∀ {fuel : ℕ} (t : Tree (Q₁ ⊕ Q₂) D A fuel) (s₁ : List Q₁) (s₂ : List Q₂),
      (lazyRun τ₁ dflt (proj₁ τ₂ dflt t s₂) s₁).1 = lazyRun2 τ₁ τ₂ dflt t s₁ s₂
  | _, .done _, _, _ => rfl
  | _, .query (.inl q) next, s₁, s₂ => by
      show (lazyRun τ₁ dflt (Tree.query q fun y => proj₁ τ₂ dflt (next y) s₂) s₁).1 = _
      rw [lazyRun_query]
      exact lazyRun_proj₁ τ₁ τ₂ dflt _ _ _
  | _, .query (.inr q) next, s₁, s₂ => by
      show (lazyRun τ₁ dflt (proj₁ τ₂ dflt
          (next (tapeAt τ₂ dflt ((if q ∈ s₂ then s₂ else s₂ ++ [q]).idxOf q)))
          (if q ∈ s₂ then s₂ else s₂ ++ [q])).weaken s₁).1 = _
      rw [lazyRun_weaken]
      exact lazyRun_proj₁ τ₁ τ₂ dflt _ _ _

/-- **The projection runs the two-oracle tree**, from the second oracle's side. -/
theorem lazyRun_proj₂ (τ₁ : Fin T₁ → D) (τ₂ : Fin T₂ → D) (dflt : D) :
    ∀ {fuel : ℕ} (t : Tree (Q₁ ⊕ Q₂) D A fuel) (s₁ : List Q₁) (s₂ : List Q₂),
      (lazyRun τ₂ dflt (proj₂ τ₁ dflt t s₁) s₂).1 = lazyRun2 τ₁ τ₂ dflt t s₁ s₂
  | _, .done _, _, _ => rfl
  | _, .query (.inr q) next, s₁, s₂ => by
      show (lazyRun τ₂ dflt (Tree.query q fun y => proj₂ τ₁ dflt (next y) s₁) s₂).1 = _
      rw [lazyRun_query]
      exact lazyRun_proj₂ τ₁ τ₂ dflt _ _ _
  | _, .query (.inl q) next, s₁, s₂ => by
      show (lazyRun τ₂ dflt (proj₂ τ₁ dflt
          (next (tapeAt τ₁ dflt ((if q ∈ s₁ then s₁ else s₁ ++ [q]).idxOf q)))
          (if q ∈ s₁ then s₁ else s₁ ++ [q])).weaken s₂).1 = _
      rw [lazyRun_weaken]
      exact lazyRun_proj₂ τ₁ τ₂ dflt _ _ _

end Lfzk.ZkTwoTape
