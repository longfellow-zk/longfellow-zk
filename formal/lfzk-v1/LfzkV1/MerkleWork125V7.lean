import LfzkV1.MerkleWork125
import LfzkV1.NizkAdaptiveTwoField
import LfzkV1.CertifiedV7

/-!
# V7 scope of the Merkle work lemma

The two-field verifier replays both opened-column claims against one oracle. The frozen
parameters supply the heap depth and the disjoint input lengths used by the work bound.
-/

set_option autoImplicit false

namespace LfzkV1.MerkleWork125

open Merkle Merkle.MH Merkle.RandomOracle LfzkV1.NizkAdaptive LfzkV1.NizkAdaptiveTwoField
open LfzkV1.CertifiedV1

section Check

variable {Salt₁ M₁ Salt₂ M₂ D Enc Out : Type} [Inhabited D] [DecidableEq Enc]
  {n₁ n₂ : ℕ}
variable (codec₁ : Codec Salt₁ M₁ D Enc) (dec₁ : RoleDecoders codec₁)
  (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D)
  (codec₂ : Codec Salt₂ M₂ D Enc) (dec₂ : RoleDecoders codec₂)
  (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)

/-- The first opening is the first pass of the compiled two-field check. -/
def check2LeftReplay {Key : Type} (rootOf₁ : Key → D) :
    OpeningReplay Salt₁ M₁ D Enc Out Key n₁ (check2 codec₁ claimOf₁ codec₂ claimOf₂) where
  codec := codec₁
  dec := dec₁
  rootOf := rootOf₁
  claimOf := claimOf₁
  replays := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_left _ (lfCheck_trace codec₁ claimOf₁ H out qa hqa)

/-- The second opening is the second pass of the compiled two-field check. -/
def check2RightReplay {Key : Type} (rootOf₂ : Key → D) :
    OpeningReplay Salt₂ M₂ D Enc Out Key n₂ (check2 codec₁ claimOf₁ codec₂ claimOf₂) where
  codec := codec₂
  dec := dec₂
  rootOf := rootOf₂
  claimOf := claimOf₂
  replays := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_right _ (lfCheck_trace codec₂ claimOf₂ H out qa hqa)

end Check

/-- A v7 hash profile, indexed by its number of requested attributes. -/
def v7HashProfile (attributes : Fin 4) : Row :=
  ![v7Hash1, v7Hash2, v7Hash3, v7Hash4] attributes

/-- Hash leaf preimages contain their 32-byte nonce and the full-width field values of the
opened column, including values represented more compactly on the proof wire. See
v1 Merkle commitment verification and v1 Ligero's opened-column hash callback. -/
def leafInputBytes (runtimeRows fieldBytes : ℕ) : ℕ :=
  32 + runtimeRows * fieldBytes

/-- The deployed hash tableau heights from the archive inspector, recorded in
formal/lfzk-v1/scripts/v7-circuit-profiles.json. -/
def v7HashTableauRows (attributes : Fin 4) : ℕ :=
  ![266, 268, 277, 279] attributes

theorem v7Sig_path_size : 2048 ≤ v7Sig.params.row.n := by decide

theorem v7Hash_path_size (attributes : Fin 4) : 2048 ≤ (v7HashProfile attributes).params.row.n := by
  fin_cases attributes <;> decide

theorem v7Sig_leaf_input_size : leafInputBytes 19 32 = 640 := by decide

theorem v7Hash_leaf_input_size (attributes : Fin 4) :
    leafInputBytes (v7HashTableauRows attributes) 16 = ![4288, 4320, 4464, 4496] attributes := by
  fin_cases attributes <;> decide

theorem v7Hash_leaf_input_disjoint (attributes : Fin 4) :
    leafInputBytes (v7HashTableauRows attributes) 16 ≠ leafInputBytes 19 32 ∧
    leafInputBytes (v7HashTableauRows attributes) 16 ≠ 64 := by
  fin_cases attributes <;> decide

theorem v7_merkle_replay_fuel_le (attributes : Fin 4) :
    2 * (v7HashProfile attributes).params.row.n + 2 * v7Sig.params.row.n ≤ 14000 := by
  fin_cases attributes <;> decide

theorem v7_fs_replay_fuel_le (attributes : Fin 4) :
    len2 v7Sig (v7HashProfile attributes) ≤ 1200 := by
  fin_cases attributes <;> decide


/-- The coarse numerator bound specialized to the deployed combined replay profiles. -/
theorem v7AdaptiveMerkleNumerator_le (attributes : Fin 4) (N budget : ℕ) :
    adaptiveMerkleNumerator
      (2 * (v7HashProfile attributes).params.row.n + 2 * v7Sig.params.row.n)
      budget (len2 v7Sig (v7HashProfile attributes) + N) ≤
      6 * (1 + N + budget)^2 + 2^26 * (1 + N + budget) :=
  adaptiveMerkleNumerator_le_v7 _ _ _ _
    (v7_merkle_replay_fuel_le attributes) (v7_fs_replay_fuel_le attributes)

end LfzkV1.MerkleWork125
