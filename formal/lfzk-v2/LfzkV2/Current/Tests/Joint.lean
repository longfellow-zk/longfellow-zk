import polygero.Local.CommonColumns
import TranscriptV2.SharedCharging

namespace LfzkV2.Current.Tests.Joint
open Finset RecursivePolygero

def left : Unit → Finset (Finset (Fin 3)) := fun _ => {{0,1}, {1,2}}
def right : Bool → Finset (Finset (Fin 3))
  | false => {{0,1}}
  | true => {{1,2}}

-- Projection loses a query distinction: one left label belongs to two
-- different pairs. The joint construction retains both common column sets.
example : ∃ d e : JointFamilies.Label left right, d.1.1 = e.1.1 ∧ d ≠ e := by
  obtain ⟨d,hd,_,_⟩ := JointFamilies.common_set left right () false {0,1}
    (by decide) (by decide)
  obtain ⟨e,he,_,_⟩ := JointFamilies.common_set left right () true {1,2}
    (by decide) (by decide)
  refine ⟨d,e,?_,?_⟩
  · rw [hd,he]
  · intro h
    have hh := congrArg (fun x : JointFamilies.Label left right => x.1.2) h
    rw [hd,he] at hh
    cases hh

-- Each field accepts two of three singleton openings, but their shared
-- opening accepts one of three. Multiplying their marginal probabilities
-- would incorrectly give four of nine.
example : (LigeroFamily.queriesWithin (r := 1) ({0,1} : Finset (Fin 3))).card = 2 ∧
    (LigeroFamily.queriesWithin (r := 1) ({1,2} : Finset (Fin 3))).card = 2 ∧
    (LigeroFamily.queriesWithin (r := 1) (({0,1} : Finset (Fin 3)) ∩ {1,2})).card = 1 := by
  simp only [LigeroFamily.card_queriesWithin]
  decide

-- Enumerating both possible claimed links adds no factor: only the link
-- equal to the parent answer contributes. There are four answer pairs.
example : (∑ r : Bool × Unit, ∑ a : Bool × Unit, ∑ _b : Bool × Unit,
    if a.1 = r.1 then (1 : ℚ) else 0) = 4 := by
  have h := TranscriptV2.feedback_sum (Link := Bool) (fun (_ : Unit) (_ _ : Unit) => (1 : ℚ))
  convert! h using 1 <;> norm_num

end LfzkV2.Current.Tests.Joint
