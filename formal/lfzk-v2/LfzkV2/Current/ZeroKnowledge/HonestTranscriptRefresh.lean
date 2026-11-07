import LfzkV2.Current.ZeroKnowledge.HonestTranscriptMdocRank

/-! Whole-answer refresh for the actual honest mdoc causal program. The
programmed experiment fixes the original oracle and an independent whole
answer. Its observer receives the updated oracle, not the original table.
External prior queries are composed separately and pay the primary-mask
fresh-hit bound; the internal program never queries its own later input. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
open Merkle.RandomOracle SumcheckV2 ApplicationSetup ConcreteSetup Frontend
open scoped Classical
variable {B Key Base C View : Type} [Field B] [Fintype B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Point" => CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base)
local notation "Pending" => Mdoc.Pending binary prime primePlan (Key := Key) (Base := Base) (C := C)

/-- The fallback only makes this map total on values outside the program's
image. The exact counter theorem below proves that every generated value
uses the ordinary opening branch. -/
def openingInput (context : Key) (pending : Pending) : Point :=
  if inside : pending.state.rank.val < (G).roles.length then
    CompleteTranscript.query base pending.state inside
  else CompleteTranscript.query base (CompleteTranscript.initial context samples.fallback)
    (by change 0 < (G).roles.length; exact Nat.zero_lt_of_lt (G).openingIndex.isLt)

variable (coefficients : C →
  WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
variable (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
variable (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B))
variable (respond : CompleteSimulation.RawResult binary prime primePlan Key Base C → C →
  (Response (CompleteSimulation.geometry binary prime primePlan) B ×
    Response (CompleteSimulation.geometry binary prime primePlan) Adapter.Mdoc.P))

theorem openingInput_atRun (H : Point → Digest × C) :
    Input.rank (openingInput binary prime primePlan samples base context
      ((openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H).1) =
      (G).openingIndex.val := by
  have rank := openingPrefix_rank binary prime primePlan samples base coefficients context original remaining tape masks respond H
  have inside : ((openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H).1.state.rank.val < (G).roles.length := by
    rw [rank]
    exact (G).openingIndex.isLt
  unfold openingInput
  rw [dif_pos inside]
  exact rank

theorem opening_fresh (H : Point → Digest × C) :
    MerklePrequery.fresh
      (openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond)
      (openingInput binary prime primePlan samples base context) H := by
  intro qa member same
  have internal := openingPrefix_progress binary prime primePlan samples base coefficients context original remaining tape masks respond H
  have earlier := internal.2 qa member
  dsimp only at earlier
  rw [same,MerklePrequery.location,openingInput_atRun,
    openingPrefix_rank binary prime primePlan samples base coefficients context original remaining tape masks respond H] at earlier
  exact (Nat.lt_irrefl _) earlier

/-- This coupling keeps the entire updated oracle available for arbitrary
later queries. The link and all challenge coordinates are one answer coin. -/
theorem opening_refresh_sameDistribution [Fintype Point] [Fintype C] [DecidableEq View]
    (observe : (Pending × List (Point × (Digest × C))) → (Digest × C) → (Point → Digest × C) → View) :
    LigeroFamily.SameDistribution
      (fun coins : (Point → Digest × C) × (Digest × C) =>
        let before := (openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run coins.1
        observe before coins.2 (Function.update coins.1
          (openingInput binary prime primePlan samples base context before.1) coins.2))
      (fun coins : (Point → Digest × C) × (Digest × C) =>
        let before := (openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run coins.1
        observe before (coins.1 (openingInput binary prime primePlan samples base context before.1)) coins.1) := by
  have refreshed := MerklePrequery.refresh_sameDistribution
    (openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond)
    (openingInput binary prime primePlan samples base context) observe
  simpa only [MerklePrequery.refreshedAnswer,MerklePrequery.swap,
    opening_fresh binary prime primePlan samples base coefficients context original remaining tape masks respond,
    ↓reduceIte,MerklePrequery.location] using refreshed

end LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
