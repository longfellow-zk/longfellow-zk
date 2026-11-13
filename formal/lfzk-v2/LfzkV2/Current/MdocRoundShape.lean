import LfzkV2.Current.Schedule
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Public mdoc challenge schedules extracted from the current compiler by
scripts/mdoc_round_shapes.rs. Entries are log wire widths, one per sumcheck layer. -/
namespace LfzkV2.Current.MdocRoundShape

def binaryRounds (attributes : Fin 4) : List ℕ :=
  match attributes.val with
  | 0 => [5, 5, 6, 6, 8, 8, 9, 13, 14, 15, 16, 15, 15, 16, 17, 18, 19, 19, 20, 19]
  | 1 => [6, 6, 7, 7, 8, 8, 9, 13, 14, 15, 16, 15, 15, 16, 17, 18, 19, 19, 20, 19]
  | 2 => [6, 7, 7, 8, 9, 9, 9, 13, 14, 15, 16, 15, 16, 16, 17, 18, 19, 19, 20, 19]
  | _ => [7, 7, 8, 8, 9, 9, 10, 13, 14, 15, 16, 15, 16, 16, 17, 18, 19, 19, 20, 19]

def primeRounds : List ℕ := [4, 5, 11, 11, 13, 14, 13, 14, 14, 14, 12]

def roundCount (attributes : Fin 4) : ℕ :=
  (binaryRounds attributes).sum + primeRounds.sum + 3*(20+11) + 6

theorem counts : List.ofFn roundCount = [487,491,496,499] := by decide

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
  have binaryNonempty : g.binary.stages.isEmpty = false := by
    cases h : g.binary.stages with
    | nil => simp [h] at binaryLength
    | cons _ _ => rfl
  have primeNonempty : g.prime.stages.isEmpty = false := by
    cases h : g.prime.stages with
    | nil => simp [h] at primeLength
    | cons _ _ => rfl
  rw [Geometry.roles_length, Frontend.roles_length, Frontend.roles_length]
  simp only [binaryNonempty, primeNonempty, Bool.false_eq_true, ↓reduceIte,
    sumcheckRounds_eq, shape.binary, shape.prime, binaryLength, primeLength, shape.packing, roundCount]
  omega

theorem rounds_le (g : Geometry) (shape : Supported g) : g.roles.length ≤ 499 := by
  obtain ⟨attributes, shape⟩ := shape
  rw [rounds_eq g attributes shape]
  fin_cases attributes <;> decide

/-- Closed public challenge skeleton. Cell contents and gate semantics do not
enter the round count and remain in the actual application geometry. -/
def skeleton (attributes : Fin 4) : Geometry where
  binary := ⟨(binaryRounds attributes).map (fun n => ⟨[],[],n⟩),[]⟩
  prime := ⟨primeRounds.map (fun n => ⟨[],[],n⟩),[]⟩
  binaryCells := 0
  primeCells := 0
  packingDegree := 128
  packingPositive := by decide
  rowDimension := 349
  maskingDegree := 12
  columns := 2443
  openings := 84
  openingsPositive := by decide
  openings_lt := by decide
  openings_le := by decide
  responseFits := by decide
  productFits := by decide

theorem skeleton_matches (attributes : Fin 4) : Matches (skeleton attributes) attributes := by
  constructor
  · simp [skeleton, List.map_map, Function.comp_def]
  · simp [skeleton, List.map_map, Function.comp_def]
  · norm_num [skeleton]

theorem skeleton_rounds (attributes : Fin 4) :
    (skeleton attributes).roles.length = roundCount attributes :=
  rounds_eq _ attributes (skeleton_matches attributes)

end LfzkV2.Current.MdocRoundShape
