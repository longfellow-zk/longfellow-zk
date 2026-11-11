import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleSlice
import LfzkV2.Current.ZeroKnowledge.SHAOracleWindowProbability

/-! Replace the finite typed leaf table by the identical table at its raw
byte addresses. Averaging arbitrary complementary oracle coordinates then
uses the existing shared-oracle theorem, without a second hiding loss. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandLeafWindow
open LigeroFamily
open scoped Classical

variable {Leaf Raw Answer : Type} [Fintype Leaf] [DecidableEq Raw]
variable (encode : Leaf ↪ Raw)

def window : Finset Raw := Finset.univ.image encode

theorem encode_mem (leaf : Leaf) : encode leaf ∈ window encode :=
  Finset.mem_image.mpr ⟨leaf,Finset.mem_univ _,rfl⟩

def addressEquiv : Leaf ≃ {raw // raw ∈ window encode} :=
  Equiv.ofBijective (fun leaf => ⟨encode leaf,encode_mem encode leaf⟩) (by
    constructor
    · intro first second same
      exact encode.injective (congrArg Subtype.val same)
    · intro raw
      obtain ⟨leaf,_,same⟩ := Finset.mem_image.mp raw.property
      exact ⟨leaf,Subtype.ext same⟩)

theorem oracle_eq_extend (outside : Raw → Answer) (table : Leaf → Answer) :
    StrandGhostMerkle.Swap.Slice.oracle encode outside table =
      OracleWindow.extend (window encode)
        (fun raw => table ((addressEquiv encode).symm raw)) outside := by
  funext raw
  by_cases member : raw ∈ window encode
  · obtain ⟨leaf,_,rfl⟩ := Finset.mem_image.mp member
    rw [StrandGhostMerkle.Swap.Slice.oracle_at,OracleWindow.extend_mem _ _ _ _ member]
    exact congrArg table ((addressEquiv encode).symm_apply_apply leaf).symm
  · rw [OracleWindow.extend,dif_neg member]
    apply StrandGhostMerkle.Swap.replace_off
    intro leaf same
    exact member (same ▸ encode_mem encode leaf)

-- Reuse the caller's equality decision when enumerating leaf tables.
-- A separately synthesized classical decision can force downstream theorem
-- matching to unfold an enormous, but equivalent, function-space enumeration.
variable [DecidableEq Leaf]
variable {R S View : Type} [Fintype R] [Fintype S] [Fintype Answer]
variable (real : R → (Raw → Answer) → View) (simulate : S → (Raw → Answer) → View)

/-- The same typed-leaf bound holds on any larger uniform raw oracle
table. The complement is sampled independently before the execution;
neither the window nor the partition is selected from an observed trace. -/
theorem statClose_of_extension (large : Finset Raw) (contains : window encode ⊆ large)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon)
    (fallback : Raw → Answer)
    (each : ∀ table : {raw // raw ∈ large} → Answer, StatClose epsilon
      (fun coin : R × (Leaf → Answer) => real coin.1 (StrandGhostMerkle.Swap.Slice.oracle encode
        (OracleWindow.extend large table fallback) coin.2))
      (fun coin : S × (Leaf → Answer) => simulate coin.1 (StrandGhostMerkle.Swap.Slice.oracle encode
        (OracleWindow.extend large table fallback) coin.2))) :
    StatClose epsilon
      (fun coin : R × ({raw // raw ∈ large} → Answer) => real coin.1 (OracleWindow.extend large coin.2 fallback))
      (fun coin : S × ({raw // raw ∈ large} → Answer) => simulate coin.1 (OracleWindow.extend large coin.2 fallback)) := by
  apply SHAOracleWindowProbability.window_statClose_of_extension (window encode) large contains nonnegative fallback real simulate
  intro table
  let outside := OracleWindow.extend large table fallback
  let tableChange := Equiv.arrowCongr (addressEquiv encode).symm (Equiv.refl Answer)
  apply Probability.changeFintype (statClose_reindex
    (Equiv.prodCongr (Equiv.refl R) tableChange) (Equiv.prodCongr (Equiv.refl S) tableChange) ?_ ?_ (each table))
  · intro coin
    rw [oracle_eq_extend]
    apply congrArg (real coin.1)
    apply congrArg (fun table => OracleWindow.extend (window encode) table outside)
    funext raw
    exact congrArg coin.2 ((addressEquiv encode).apply_symm_apply raw).symm
  · intro coin
    rw [oracle_eq_extend]
    apply congrArg (simulate coin.1)
    apply congrArg (fun table => OracleWindow.extend (window encode) table outside)
    funext raw
    exact congrArg coin.2 ((addressEquiv encode).apply_symm_apply raw).symm

/-- The same typed-leaf bound holds on any larger uniform raw oracle
table. The complement is sampled independently before the execution;
neither the window nor the partition is selected from an observed trace. -/
theorem statClose (large : Finset Raw) (contains : window encode ⊆ large)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon)
    (each : ∀ outside : Raw → Answer, StatClose epsilon
      (fun coin : R × (Leaf → Answer) => real coin.1 (StrandGhostMerkle.Swap.Slice.oracle encode outside coin.2))
      (fun coin : S × (Leaf → Answer) => simulate coin.1 (StrandGhostMerkle.Swap.Slice.oracle encode outside coin.2)))
    (fallback : Raw → Answer) :
    StatClose epsilon
      (fun coin : R × ({raw // raw ∈ large} → Answer) => real coin.1 (OracleWindow.extend large coin.2 fallback))
      (fun coin : S × ({raw // raw ∈ large} → Answer) => simulate coin.1 (OracleWindow.extend large coin.2 fallback)) := by
  exact statClose_of_extension encode real simulate large contains epsilon nonnegative fallback
    (fun table => each (OracleWindow.extend large table fallback))

end LfzkV2.Current.ZeroKnowledge.StrandLeafWindow
