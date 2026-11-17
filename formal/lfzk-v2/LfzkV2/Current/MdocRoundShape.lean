import LfzkV2.Current.Schedule
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Public mdoc challenge schedules extracted from the current compiler by
scripts/mdoc_round_shapes.rs. Entries are log wire widths, one per sumcheck layer. -/
namespace LfzkV2.Current.MdocRoundShape

def binaryRounds (attributes : Fin 4) : List ℕ :=
  match attributes.val with
  | 0 => [5, 5, 6, 6, 8, 8, 9, 13, 14, 15, 16, 15, 15, 16, 16, 18, 19, 19, 20, 19]
  | 1 => [6, 6, 7, 7, 8, 8, 9, 13, 14, 15, 16, 15, 15, 16, 17, 18, 19, 19, 20, 19]
  | 2 => [6, 7, 7, 8, 9, 9, 9, 13, 14, 15, 16, 15, 16, 16, 17, 18, 19, 19, 20, 19]
  | _ => [7, 7, 8, 8, 9, 9, 10, 13, 14, 15, 16, 15, 16, 16, 17, 18, 19, 19, 20, 19]

def primeRounds : List ℕ := [4, 5, 6, 11, 11, 13, 14, 14, 14, 14, 12]

def roundCount (attributes : Fin 4) : ℕ :=
  (binaryRounds attributes).sum + primeRounds.sum + 2*(20+11) + 7

theorem counts : List.ofFn roundCount = [449,454,459,462] := by decide

structure Matches (g : Geometry) (attributes : Fin 4) : Prop where
  binary : g.binary.stages.map Stage.rounds = binaryRounds attributes
  prime : g.prime.stages.map Stage.rounds = primeRounds
  packing : g.packingDegree ≠ 1

def Supported (g : Geometry) : Prop := ∃ attributes, Matches g attributes

theorem sumcheckRounds_eq (f : Frontend) :
    f.sumcheckRounds = (f.stages.map Stage.rounds).sum := by
  simp only [Frontend.sumcheckRounds, ← List.sum_ofFn]
  congr 1
  ext i
  simp

theorem binary_length (attributes : Fin 4) : (binaryRounds attributes).length = 20 := by
  fin_cases attributes <;> rfl

theorem rounds_eq (g : Geometry) (attributes : Fin 4) (shape : Matches g attributes) :
    g.roles.length = roundCount attributes := by
  have binaryLength : g.binary.stages.length = 20 := by
    have h := congrArg List.length shape.binary
    simpa only [List.length_map, binary_length] using h
  have primeLength : g.prime.stages.length = 11 := by
    have h := congrArg List.length shape.prime
    simpa only [List.length_map, primeRounds, List.length_cons, List.length_nil] using h
  rw [Geometry.roles_length, Frontend.roles_length, Frontend.roles_length]
  simp only [sumcheckRounds_eq, shape.binary, shape.prime, binaryLength, primeLength, shape.packing,
    roundCount, if_false]
  omega

theorem rounds_le (g : Geometry) (shape : Supported g) : g.roles.length ≤ 499 := by
  obtain ⟨attributes, shape⟩ := shape
  rw [rounds_eq g attributes shape]
  fin_cases attributes <;> decide

end LfzkV2.Current.MdocRoundShape
