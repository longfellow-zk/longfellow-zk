import LfzkV2.Current.Schedule

/-! Public challenge schedules for the four-slot NEXT mdoc circuit, extracted by
scripts/mdoc_round_shapes.rs. Entries are log wire widths, one per sumcheck layer. -/
namespace LfzkV2.Current.MdocRoundShape

def binaryRounds : List ℕ :=
  [6, 7, 8, 8, 9, 11, 12, 14, 15, 16, 16, 15, 16, 16, 17, 18, 19, 20, 19]

def primeRounds : List ℕ := [4, 5, 6, 11, 11, 13, 14, 14, 14, 14, 12]

def roundCount : ℕ :=
  binaryRounds.sum + primeRounds.sum + 2 * (binaryRounds.length + primeRounds.length) + 7

theorem roundCount_eq : roundCount = 447 := by decide

structure Supported (g : Geometry) : Prop where
  binary : g.binary.stages.map Stage.rounds = binaryRounds
  prime : g.prime.stages.map Stage.rounds = primeRounds
  packing : g.packingDegree ≠ 1

theorem sumcheckRounds_eq (f : Frontend) :
    f.sumcheckRounds = (f.stages.map Stage.rounds).sum := by
  simp only [Frontend.sumcheckRounds, ← List.sum_ofFn]
  congr 1
  ext i
  simp

theorem rounds_eq (g : Geometry) (shape : Supported g) : g.roles.length = roundCount := by
  have binaryLength : g.binary.stages.length = binaryRounds.length := by
    simpa only [List.length_map] using congrArg List.length shape.binary
  have primeLength : g.prime.stages.length = primeRounds.length := by
    simpa only [List.length_map] using congrArg List.length shape.prime
  rw [Geometry.roles_length, Frontend.roles_length, Frontend.roles_length]
  simp only [sumcheckRounds_eq, shape.binary, shape.prime, binaryLength, primeLength, shape.packing,
    roundCount, if_false]
  omega

theorem rounds_le (g : Geometry) (shape : Supported g) : g.roles.length ≤ 499 := by
  rw [rounds_eq g shape, roundCount_eq]
  decide

end LfzkV2.Current.MdocRoundShape
