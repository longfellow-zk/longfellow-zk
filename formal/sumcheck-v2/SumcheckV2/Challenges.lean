import SumcheckV2.Layer

/-!
# Local V2 challenge reductions

A fixed false round polynomial has at most two repairing challenges, and a
fixed false final combination has at most one. The Fiat–Shamir analysis uses
these local counts after reconstructing the preceding message prefix.
-/

namespace SumcheckV2

open Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

inductive ChallengeKind where
  | round
  | combine
  deriving DecidableEq

def ChallengeKind.budget : ChallengeKind → ℕ
  | .round => 2
  | .combine => 1

structure RoundData (F : Type) [Field F] where
  truth : Polynomial F
  message : RoundPoly F
  claim : F

structure CombineData (F : Type) where
  trueA : F
  trueB : F
  claimA : F
  claimB : F

def ChallengeData (F : Type) [Field F] : ChallengeKind → Type
  | .round => RoundData F
  | .combine => CombineData F

def ChallengeData.Valid {kind : ChallengeKind} : ChallengeData F kind → Prop :=
  match kind with
  | .round => fun data => data.truth.natDegree ≤ 2
  | .combine => fun _ => True

def ChallengeData.Bad {kind : ChallengeKind} : ChallengeData F kind → F → Prop :=
  match kind with
  | .round => fun data z => BadRoundEvent data.truth data.message data.claim z
  | .combine => fun data alpha =>
      BadCombineEvent data.trueA data.trueB data.claimA data.claimB alpha

theorem challenge_bad_card_le {kind : ChallengeKind} (data : ChallengeData F kind)
    (hvalid : data.Valid) :
    (Finset.univ.filter fun z => data.Bad z).card ≤ kind.budget := by
  cases kind with
  | round => exact bad_round_roots data.truth data.message data.claim hvalid
  | combine => exact bad_combine_roots data.trueA data.trueB data.claimA data.claimB

end SumcheckV2
