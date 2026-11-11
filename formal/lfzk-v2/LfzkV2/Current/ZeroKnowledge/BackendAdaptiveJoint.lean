import LfzkV2.Current.ZeroKnowledge.BackendAdaptiveCorrection
import LfzkV2.Current.ZeroKnowledge.BackendAdaptiveSelection
import LfzkV2.Current.ZeroKnowledge.BackendJoint

/-! Exact simulation at the actual response-selected backend opening.

Fix the public frontend, ghost tree, and actual SHA oracle. In the current
runtime all equation-batching scalars and row-batching polynomials are read
before H and Z. They are fixed parameters here. The only adaptive operation
is the opening reader, applied after BOTH fields' complete responses.

The public simulator samples one reference tape, computes those responses,
and runs that same reader. Its public correction-normalization equivalence
then supplies the selected columns while preserving H and Z. A failed
reader remains a failed reader. The witness-dependent equivalence occurs
only in the proof of equality of distributions, never in the simulator. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend.Adaptive
open Polynomial LigeroFamily RecursivePolygero.Local
open scoped Classical

variable {B N : Type} [Field B] [Field N] [Fintype B] [Fintype N]
variable {r w n bw nw s : ℕ}
variable (binary : PolygeroZk.Geometry B r w 0 n) (prime : PolygeroZk.Geometry N r w 0 n)
variable {BE NE : Type} [Fintype BE] [Fintype NE]

abbrev JointTape := Tape binary bw s × Tape prime nw s
abbrev Responses := LigeroPayload B (r+w) s × LigeroPayload N (r+w) s
abbrev Opened (Q : QuerySet n r) := Polygero.Opening B bw 0 n r Q × Polygero.Opening N nw 0 n r Q

/-- Retain the reader's complete result, including an ordered query vector
or additional state. The algebra uses only its underlying coordinate set. -/
abbrev JointOutput {Selection : Type} (queryOf : Selection → QuerySet n r) :=
  Responses (B := B) (N := N) (r := r) (w := w) (s := s) ×
    Option ((choice : Selection) × Opened (B := B) (N := N) (bw := bw) (nw := nw) (queryOf choice))

variable (reference : QuerySet n r) (pivot : Fin w)
variable (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
variable (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)

def jointNormalize (selected : QuerySet n r) : JointTape (bw := bw) (nw := nw) (s := s) binary prime ≃
    JointTape (bw := bw) (nw := nw) (s := s) binary prime :=
  (normalize binary statements.1 coins.1 reference selected pivot).prodCongr
    (normalize prime statements.2 coins.2 reference selected pivot)

def publicResponse (Q : QuerySet n r) (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    Responses (B := B) (N := N) (r := r) (w := w) (s := s) :=
  ((jointSimulate binary prime Q pivot statements coins tape).1.2,
    (jointSimulate binary prime Q pivot statements coins tape).2.2)

omit [Fintype B] [Fintype N] in
theorem jointNormalize_response (selected : QuerySet n r)
    (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    publicResponse binary prime pivot statements coins selected
        (jointNormalize binary prime reference pivot statements coins selected tape) =
      publicResponse binary prime pivot statements coins reference tape :=
  Prod.ext (normalize_payload binary statements.1 coins.1 reference selected pivot tape.1)
    (normalize_payload prime statements.2 coins.2 reference selected pivot tape.2)

def publicOpened (Q : QuerySet n r) (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    Opened (B := B) (N := N) (bw := bw) (nw := nw) Q :=
  ((jointSimulate binary prime Q pivot statements coins tape).1.1,
    (jointSimulate binary prime Q pivot statements coins tape).2.1)

variable {Selection : Type} (queryOf : Selection → QuerySet n r)
variable (select : Responses (B := B) (N := N) (r := r) (w := w) (s := s) → Option Selection)

/-- The selector can be the actual SHA/PRF opening reader at any fixed
oracle. No challenge row is independently sampled or overwritten. -/
def simulate (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    JointOutput (B := B) (N := N) (w := w) (bw := bw) (nw := nw) (s := s) queryOf :=
  let response := publicResponse binary prime pivot statements coins reference tape
  (response,(select response).map fun choice =>
    ⟨choice,publicOpened binary prime pivot statements coins (queryOf choice)
      (jointNormalize binary prime reference pivot statements coins (queryOf choice) tape)⟩)

variable (cells : Cells B bw w × Cells N nw w)

def honestResponse (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    Responses (B := B) (N := N) (r := r) (w := w) (s := s) :=
  (PolygeroZk.payload binary binary.positive statements.1 coins.1 (messages cells.1) tape.1,
    PolygeroZk.payload prime prime.positive statements.2 coins.2 (messages cells.2) tape.2)

def honest (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    JointOutput (B := B) (N := N) (w := w) (bw := bw) (nw := nw) (s := s) queryOf :=
  let response := honestResponse binary prime statements coins cells tape
  (response,(select response).map fun choice =>
    ⟨choice,(jointReal binary prime (queryOf choice) cells statements coins tape).1.1,
      (jointReal binary prime (queryOf choice) cells statements coins tape).2.1⟩)

variable (satisfied : statements.1.Satisfies (logical cells.1) ∧ statements.2.Satisfies (logical cells.2))

/-- First use the existing fixed-opening algebraic coupling, then return
to the public reference response fiber. Neither operation changes H or Z. -/
def referenceCoupling (selected : QuerySet n r) :
    JointTape (bw := bw) (nw := nw) (s := s) binary prime ≃
      JointTape (bw := bw) (nw := nw) (s := s) binary prime :=
  (jointCoupling binary prime selected pivot cells statements satisfied coins).trans
    (jointNormalize binary prime reference pivot statements coins selected).symm

theorem referenceCoupling_response (selected : QuerySet n r)
    (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    publicResponse binary prime pivot statements coins reference
        (referenceCoupling binary prime reference pivot statements coins cells satisfied selected tape) =
      honestResponse binary prime statements coins cells tape := by
  have normalized := jointNormalize_response binary prime reference pivot statements coins selected
    ((jointNormalize binary prime reference pivot statements coins selected).symm
      (jointCoupling binary prime selected pivot cells statements satisfied coins tape))
  rw [Equiv.apply_symm_apply] at normalized
  change publicResponse binary prime pivot statements coins reference
    ((jointNormalize binary prime reference pivot statements coins selected).symm
      (jointCoupling binary prime selected pivot cells statements satisfied coins tape)) = _
  rw [← normalized]
  exact congrArg (fun view => (view.1.2,view.2.2))
    (jointCoupling_view binary prime selected pivot cells statements satisfied coins tape)

def adaptiveCoupling : JointTape (bw := bw) (nw := nw) (s := s) binary prime ≃
    JointTape (bw := bw) (nw := nw) (s := s) binary prime :=
  selectionEquiv (honestResponse binary prime statements coins cells)
    (publicResponse binary prime pivot statements coins reference)
    (fun response => ((select response).map queryOf).getD reference)
    (referenceCoupling binary prime reference pivot statements coins cells satisfied)
    (referenceCoupling_response binary prime reference pivot statements coins cells satisfied)

theorem adaptiveCoupling_view (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    simulate binary prime reference pivot statements coins queryOf select
        (adaptiveCoupling binary prime reference pivot statements coins queryOf select cells satisfied tape) =
      honest binary prime statements coins queryOf select cells tape := by
  let response := honestResponse binary prime statements coins cells tape
  let chosen := ((select response).map queryOf).getD reference
  have same := referenceCoupling_response binary prime reference pivot statements coins cells satisfied chosen tape
  change publicResponse binary prime pivot statements coins reference
    (referenceCoupling binary prime reference pivot statements coins cells satisfied chosen tape) = response at same
  unfold simulate honest
  rw [show adaptiveCoupling binary prime reference pivot statements coins queryOf select cells satisfied tape =
      referenceCoupling binary prime reference pivot statements coins cells satisfied chosen tape from rfl,same]
  dsimp only
  refine Prod.ext (by rfl) ?_
  cases decision : select response with
  | none => rfl
  | some choice =>
      have chosenQuery : chosen = queryOf choice := by
        simp only [chosen,decision,Option.map_some,Option.getD_some]
      rw [chosenQuery]
      change some (⟨choice,publicOpened binary prime pivot statements coins (queryOf choice)
          (jointNormalize binary prime reference pivot statements coins (queryOf choice)
            ((jointNormalize binary prime reference pivot statements coins (queryOf choice)).symm
              (jointCoupling binary prime (queryOf choice) pivot cells statements satisfied coins tape)))⟩ :
          (choice : Selection) × Opened (B := B) (N := N) (bw := bw) (nw := nw) (queryOf choice)) = _
      rw [Equiv.apply_symm_apply]
      exact congrArg (fun view :
          View (F := B) w bw s (queryOf choice) × View (F := N) w nw s (queryOf choice) =>
        some (⟨choice,(view.1.1,view.2.1)⟩ :
          (choice : Selection) × Opened (B := B) (N := N) (bw := bw) (nw := nw) (queryOf choice)))
        (jointCoupling_view binary prime (queryOf choice) pivot cells statements satisfied coins tape)

include satisfied in
/-- Exact equality of the full response-selected two-field view, including
the failure branch, under every further deterministic observation. Fixed
SHA replay, authentication preparation and later observer state can all be
part of that observation. -/
theorem sameDistribution {Observed : Type} [DecidableEq Observed]
    (observe : JointOutput (B := B) (N := N) (w := w)
      (bw := bw) (nw := nw) (s := s) queryOf → Observed) :
    SameDistribution
      (fun tape => observe (honest binary prime statements coins queryOf select cells tape))
      (fun tape => observe (simulate binary prime reference pivot statements coins queryOf select tape)) := by
  apply sameDistribution_of_equiv
    (adaptiveCoupling binary prime reference pivot statements coins queryOf select cells satisfied)
  intro tape
  exact congrArg observe
    (adaptiveCoupling_view binary prime reference pivot statements coins queryOf select cells satisfied tape).symm

end LfzkV2.Current.ZeroKnowledge.Backend.Adaptive
