import Bcs.EnvelopeFiatShamir

/-! Prefix congruence of the defining alpha slot for fixed-key FS compilation. -/
namespace Bcs.EnvelopeFiatShamir.Linear
open Bcs.TypedFiatShamir
variable {Alpha Subset Response : Type*}
variable [Fintype Alpha] [Fintype Subset] [DecidableEq Alpha] [DecidableEq Subset]
variable [Nonempty Alpha] [Nonempty Subset]
variable {AlphaKey Output : Type*} [DecidableEq AlphaKey] [DecidableEq Response]
variable {N : ℕ}
variable (adversary : Merkle.RandomOracle.Tree
  (Query AlphaKey (AlphaKey × Response)) (Answer Alpha Subset) Output N)
variable (dflt : Answer Alpha Subset) (alphaKey : AlphaKey) (responseOf : Output → Response)

omit [DecidableEq Alpha] [DecidableEq Subset] [Nonempty Alpha] [Nonempty Subset] in

theorem alphaSlot_gate_congr (j : Fin (N + 2))
    (left right : Fin (N + 2) → Answer Alpha Subset)
    (hag : ∀ k, k.val < j.val → left k = right k) :
    ((trace adversary dflt alphaKey responseOf).alphaSlot left = j ↔
      (trace adversary dflt alphaKey responseOf).alphaSlot right = j) := by
  classical
  let seen := fun tape : Fin (N + 2) → Answer Alpha Subset =>
    (Merkle.RandomOracle.lazyRun tape dflt adversary []).2.1
  let query : Query AlphaKey (AlphaKey × Response) := .alpha alphaKey
  let first := fun tape => appendIfMissing (seen tape) query
  have hidx (tape : Fin (N + 2) → Answer Alpha Subset) :
      (first tape).idxOf query = ((trace adversary dflt alphaKey responseOf).alphaSlot tape).val := by
    symm
    exact idxOf_appendIfMissing_of_mem (first tape)
      (.subset (alphaKey, responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1))
      query (mem_appendIfMissing _ _)
  have ht : (first left).take (j.val + 1) = (first right).take (j.val + 1) := by
    apply take_appendIfMissing_congr
    exact Merkle.RandomOracle.lazyRun_seen_take_congr left right dflt j.val hag adversary []
  have go (a b : Fin (N + 2) → Answer Alpha Subset)
      (ht : (first a).take (j.val + 1) = (first b).take (j.val + 1))
      (h : (trace adversary dflt alphaKey responseOf).alphaSlot a = j) :
      (trace adversary dflt alphaKey responseOf).alphaSlot b = j := by
    apply Fin.ext
    rw [← hidx b]
    apply idxOf_eq_of_take_congr (first a) (first b) query j.val
      (mem_appendIfMissing _ _) _ ht
    rw [hidx a, h]
  exact ⟨go left right ht, go right left ht.symm⟩


end Bcs.EnvelopeFiatShamir.Linear
