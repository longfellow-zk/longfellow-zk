import LfzkV2.Current.ZeroKnowledge.OracleRefresh

/-! The programmed hybrid keeps the base transcript oracle and the chosen
whole opening answer as independent product coins. It computes the honest
causal prefix using that base oracle, then returns its update at the actual
opening input. The post-proof observer receives only that updated oracle.

In particular the chosen answer is not asserted independent after
conditioning on the complete updated table: its location depends on the
private masks. Backend/frontend changes of variables fix the base table and
chosen answer and preserve the complete public input being updated. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRefresh
open Merkle.RandomOracle
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C Request Observed : Type}
variable {fuel : ℕ}
local notation "Point" => Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base)

variable (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (before : Tree (Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base)) (Digest × C) Request fuel)
variable (start : Request → At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) 0)
variable (writes openingWrites : Request → Frontend.CompleteTranscript.State g fields Advice Key Base C →
  ProtocolWrites.Fresh g fields Advice)
variable (observe :
  (Finished (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base)
    (C := C) (Request := Request) × List
      ((Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
        (Authentication := Authentication) (Key := Key) (Base := Base)) × (Digest × C))) →
  (Digest × C) → ((Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
    (Authentication := Authentication) (Key := Key) (Base := Base)) → Digest × C) → Observed)

def honestHybrid (coins : (Point → Digest × C) × (Digest × C)) : Observed :=
  let earlier := (compile bindOnly before start writes).run coins.1
  observe earlier (coins.1 (opening bindOnly openingWrites earlier.1)) coins.1

def guardedHybrid (coins : (Point → Digest × C) × (Digest × C)) : Observed :=
  observe ((compile bindOnly before start writes).run coins.1)
    (MerklePrequery.refreshedAnswer (compile bindOnly before start writes) (opening bindOnly openingWrites) coins)
    (swap bindOnly before start writes openingWrites coins).1

/-- This is the actual unguarded simulator-side programming operation.
All other computation may still use the independent base oracle and chosen
answer internally, while subsequent observable calls use the returned update. -/
def programmedHybrid (coins : (Point → Digest × C) × (Digest × C)) : Observed :=
  let earlier := (compile bindOnly before start writes).run coins.1
  let point := opening bindOnly openingWrites earlier.1
  observe earlier coins.2 (Function.update coins.1 point coins.2)

theorem programmed_eq_guarded (coins : (Point → Digest × C) × (Digest × C))
    (fresh : MerklePrequery.fresh (compile bindOnly before start writes) (opening bindOnly openingWrites) coins.1) :
    programmedHybrid bindOnly before start writes openingWrites observe coins =
      guardedHybrid bindOnly before start writes openingWrites observe coins := by
  simp only [programmedHybrid,guardedHybrid,swap,MerklePrequery.swap,
    MerklePrequery.refreshedAnswer,fresh,↓reduceIte,MerklePrequery.location]

/-- The guarded game is exactly the honest law; the only difference from
the explicit independent-answer programmed hybrid is the separately counted
prior-query hit branch. -/
theorem guarded_sameDistribution [Fintype Point] [Fintype C] [DecidableEq Observed] :
    LigeroFamily.SameDistribution
      (guardedHybrid bindOnly before start writes openingWrites observe)
      (honestHybrid bindOnly before start writes openingWrites observe) :=
  refresh_sameDistribution bindOnly before start writes openingWrites observe

end LfzkV2.Current.ZeroKnowledge.OracleRefresh
