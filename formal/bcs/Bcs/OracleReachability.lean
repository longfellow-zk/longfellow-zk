import Bcs.TotalOracle

/-! Witness conditions apply to results actually returned by an oracle
program. A public-setup family is reached only with the setup derived from
that same oracle, excluding inconsistent frozen-setup experiments. -/
namespace Bcs.OracleReachability
open Merkle.RandomOracle

variable {Raw Answer Context Setup : Type} {fuel : ℕ}

def Returns (before : Tree Raw Answer Context fuel) (context : Context) : Prop :=
  ∃ H : Raw → Answer, (before.run H).1 = context

def FamilyReturns (values : (Raw → Answer) → Setup)
    (before : Setup → Tree Raw Answer Context fuel) (context : Context) : Prop :=
  ∃ H : Raw → Answer, ((before (values H)).run H).1 = context

theorem returns_run (before : Tree Raw Answer Context fuel) (H : Raw → Answer) :
    Returns before (before.run H).1 := ⟨H,rfl⟩

theorem familyReturns_run (values : (Raw → Answer) → Setup)
    (before : Setup → Tree Raw Answer Context fuel) (H : Raw → Answer) :
    FamilyReturns values before ((before (values H)).run H).1 := ⟨H,rfl⟩

theorem familyReturns_of_setup (values : (Raw → Answer) → Setup)
    (before : Setup → Tree Raw Answer Context fuel) (H : Raw → Answer) (visible : Setup)
    (consistent : values H = visible) :
    FamilyReturns values before ((before visible).run H).1 := by
  exact ⟨H,by rw [consistent]⟩

theorem valid_on_run (before : Tree Raw Answer Context fuel) (valid : Context → Prop)
    (onReturned : ∀ context, Returns before context → valid context) (H : Raw → Answer) :
    valid (before.run H).1 := onReturned _ (returns_run before H)

end Bcs.OracleReachability
