import LfzkV2.Current.ApplicationCharging
import LfzkV2.Current.BackendOracle
import LfzkV2.Current.BackendPositions

/-! Numerical role budgets. Application and backend positions are disjoint;
the parent slot includes the grouped high-response cost before taking one maximum. -/
noncomputable section
namespace LfzkV2.Current.RoleBudgets
open RecursivePolygero ProfileAnalysis ApplicationCharging
open scoped Classical
variable {g : Geometry} {Context Block Link Body B : Type} [Fintype B]
variable {p M K LB LN k s n t : ℕ}
variable (P R : Joint.Participant k s n t)
variable (encode : JointResponse.Response P R → Block) (cutoff : ℕ × ℕ) (ε : ℚ)
local notation "Point" => Input g.roles Context Block Link Body

def openingBudget : ℚ := ε + ((cutoff.1+s-1).choose t : ℚ)/n.choose t +
  ((cutoff.2+s-1).choose t : ℚ)/n.choose t

def budget (pc : ProfileParameters P.backend) (rc : ProfileParameters R.backend) (point : Point) : ℚ :=
  ApplicationCharging.budget (B := B) (p := p) (M := M) (K := K) (LB := LB) (LN := LN) point +
    BackendOracle.singleBudget P R g.batchingIndex_next encode
      (pc.rankError+rc.rankError) (openingBudget (s := s) (n := n) (t := t) cutoff ε) point

end LfzkV2.Current.RoleBudgets

namespace LfzkV2.Current.RoleBudgets
open RecursivePolygero ProfileAnalysis Finset ApplicationCharging
open scoped Classical

variable {g : Geometry} {Context Block Link Body B : Type} [Fintype B]
variable {p M K LB LN k s n t : ℕ}
variable [Fintype Context] [Fintype Block] [Fintype Link]
variable [DecidableEq (Input g.roles Context Block Link Body)]

local notation "Point" => Input g.roles Context Block Link Body
local notation "Parent" => BackendQueries.Parent g.roles Context Block Link g.batchingIndex

/-- Public numerical bounds suffice to close the global role maximum.
At the backend's two actual positions the application dispatch is zero;
at every other position both backend contributions are zero. Thus these
inequalities are checked separately, without adding protocol budgets. -/
theorem point_budget_le (P R : Joint.Participant k s n t)
    (encode : JointResponse.Response P R → Block) (hencode : Function.Injective encode)
    (cutoff : ℕ × ℕ) (ε : ℚ)
    (pc : ProfileParameters P.backend) (rc : ProfileParameters R.backend)
    (highBudget total : ℚ)
    (happ : ∀ role, roundBudget B p M K LB LN role ≤ total)
    (hp : pc.rankError+rc.rankError+highBudget ≤ total)
    (ho : openingBudget (s := s) (n := n) (t := t) cutoff ε ≤ total)
    (ht : 0 ≤ total) (point : Point) :
    budget (B := B) (p := p) (M := M) (K := K) (LB := LB) (LN := LN)
        P R encode cutoff ε pc rc point +
      (∑ parent : Parent, if parent.point = point then highBudget else 0) ≤ total := by
  have hb := BackendOracle.point_budget P R g.batchingIndex_next encode
    (pc.rankError+rc.rankError) (openingBudget (s := s) (n := n) (t := t) cutoff ε)
    highBudget total hp ho ht point
  have hzero (h : point.rank = g.batchingIndex.val ∨ point.rank = g.openingIndex.val) :
      ApplicationCharging.budget (B := B) (p := p) (M := M) (K := K)
        (LB := LB) (LN := LN) point = 0 := by
    cases point with
    | round i history block =>
        rcases h with h | h
        · have hi : i = g.batchingIndex := Fin.ext h
          subst i
          simp only [ApplicationCharging.budget, g.get_batchingIndex, roundBudget]
        · have hi : i = g.openingIndex := Fin.ext h
          subst i
          simp only [ApplicationCharging.budget, g.get_openingIndex, roundBudget]
    | finalSeal history body => rfl
  unfold budget
  by_cases hbatch : point.rank = g.batchingIndex.val
  · rw [hzero (Or.inl hbatch), zero_add]
    exact hb
  · by_cases hopen : point.rank = g.batchingIndex.val+1
    · rw [hzero (Or.inr (hopen.trans g.openingIndex_val.symm)), zero_add]
      exact hb
    · rw [BackendOracle.singleBudget_zero_of_rank P R g.batchingIndex_next encode hencode
        (pc.rankError+rc.rankError) (openingBudget (s := s) (n := n) (t := t) cutoff ε)
        point hbatch hopen]
      have hparent := BackendOracle.parent_mass (i := g.batchingIndex) highBudget point
      rw [BackendOracle.parentOf_none_of_rank point hbatch] at hparent
      rw [hparent, add_zero, add_zero]
      cases point with
      | round i history block => exact happ (g.roles.get i)
      | finalSeal history body => exact ht

end LfzkV2.Current.RoleBudgets
