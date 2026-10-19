import polygero.Local.HonestCompletion

/-! Realization of parent acceptance as an actual typed recursive-FS
failure. A parent payload fixes the unmasked child commitment before the
query. Varying one child wire entry supplies different real hash inputs;
the same honest completion works whenever the sampled terminal query
avoids that entry. These are verifier and extraction statements, without
a probabilistic lower bound or a claimed adversarial query-tree strategy.
-/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset ProfileAnalysis ProfileAnalysis.HonestCompletion Local Local.Polygero
open LigeroFamily
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

/-- A family of actual core-only child commitments, fixed independently
of the parent query and all subsequent oracle answers. -/
noncomputable def grindingCommitment (payload : I.layer.Payload)
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (c : F) : child.instance.layer.Oracle :=
  child.instance.expandWireOracle false
    (varyWireEntry child.instance (packedWireOracle child payload) row col c)

/-- The child response is computed after the actual child challenge is
known. Its canonical row tableau remains the encoding of the fixed packed
parent payload. -/
noncomputable def grindingProof (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (payload : I.layer.Payload)
    (row : child.instance.WireRow false) (col : Fin child.instance.n) (c : F)
    (Q : I.layer.Query) (H : HashInput child → Answer child) : Proof child :=
  let V := grindingCommitment child payload row col c
  let b := (H (childGamma W V Q)).2.1
  (W, V, Q, GrindingAlgebra.canonicalPayload child.instance hk
    (child.link.statement sigma W (H (gamma W)).1.1 Q) b
    (rows child.instance (unflatten (pack child.packing payload))))

/-- Different entry values induce different actual parent-query hash
inputs. This is a physical wire-format family, rather than transcript
padding or unused bits. -/
theorem grinding_query_injective (W : I.layer.Oracle) (payload : I.layer.Payload)
    (row : child.instance.WireRow false) (col : Fin child.instance.n) :
    Function.Injective (fun c : F =>
      (query W (grindingCommitment child payload row col c) : HashInput child)) := by
  exact varied_wire_query_injective child W (packedWireOracle child payload) row col

theorem grinding_query_count (W : I.layer.Oracle) (payload : I.layer.Payload)
    (row : child.instance.WireRow false) (col : Fin child.instance.n) :
    (univ.image (fun c : F =>
      (query W (grindingCommitment child payload row col c) : HashInput child))).card =
      Fintype.card F := by
  rw [card_image_of_injective _ (grinding_query_injective child W payload row col), card_univ]

/-- Conditional only on the actual sampled gates: parent acceptance,
the correct parent query at its tagged hash input, and a terminal query
avoiding the changed child coordinate. All recursive arithmetic and
completion obligations are discharged by the concrete protocol lemmas. -/
theorem grindingProof_accepts (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (payload : I.layer.Payload)
    (row : child.instance.WireRow false) (col : Fin child.instance.n) (c : F)
    (Q : I.layer.Query) (H : HashInput child → Answer child)
    (hparent : I.layer.verify sigma W (H (gamma W)).1.1 payload Q)
    (hquery : (H (query W (grindingCommitment child payload row col c))).1.2 = Q)
    (havoid : col ∉ (H (terminal
      (grindingProof child hk sigma W payload row col c Q H))).2.2.coordinates) :
    accepts child sigma H (grindingProof child hk sigma W payload row col c Q H) := by
  apply (accepts_iff child sigma H _).mpr
  refine ⟨hquery, ?_, ?_⟩
  · exact (packed_response_satisfies I.domain (by have := I.primary_le; omega) I.layout sigma
      child.packing (H (gamma W)).1.1 Q (openOracle W Q) payload hparent).1
  · exact varied_verify_avoiding child.instance hk rfl
      (unflatten (pack child.packing payload))
      (child.link.statement sigma W (H (gamma W)).1.1 Q)
      (GrindingAlgebra.packed_child_satisfies child sigma W (H (gamma W)).1.1 payload Q hparent)
      (H (childGamma W (grindingCommitment child payload row col c) Q)).2.1
      (H (terminal (grindingProof child hk sigma W payload row col c Q H))).2.2
      row col c havoid

/-- On a false parent statement, actual recursive acceptance is already
actual extraction failure, by validity of the concrete recursive extractor. -/
theorem failure_of_accepts_of_false (p : HahnSystemCertificate I)
    (cp : HahnSystemCertificate child.instance) (sigma : I.layer.Statement)
    (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    (H : HashInput child → Answer child) (d : Proof child)
    (ha : accepts child sigma H d) :
    failure child p cp sigma (fun _ => False) H d := by
  apply (failure_empty_iff child p cp sigma H d).mpr
  refine ⟨ha, ?_⟩
  cases he : (twoProof child p cp).run sigma d.1 (constantMessages child d) (proofCoins child H d) with
  | none => rfl
  | some g =>
    exact (hfalse _ ((twoProof child p cp).run_valid sigma d.1
      (constantMessages child d) (proofCoins child H d) g he)).elim

/-- The construction realizes the sampled gates as the exact failure
predicate used by the existing two-level ROM upper bounds. -/
theorem grindingProof_failure (p : HahnSystemCertificate I)
    (cp : HahnSystemCertificate child.instance)
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    (W : I.layer.Oracle) (payload : I.layer.Payload)
    (row : child.instance.WireRow false) (col : Fin child.instance.n) (c : F)
    (Q : I.layer.Query) (H : HashInput child → Answer child)
    (hparent : I.layer.verify sigma W (H (gamma W)).1.1 payload Q)
    (hquery : (H (query W (grindingCommitment child payload row col c))).1.2 = Q)
    (havoid : col ∉ (H (terminal
      (grindingProof child hk sigma W payload row col c Q H))).2.2.coordinates) :
    failure child p cp sigma (fun _ => False) H
      (grindingProof child hk sigma W payload row col c Q H) :=
  failure_of_accepts_of_false child p cp sigma hfalse H _
    (grindingProof_accepts child hk sigma W payload row col c Q H hparent hquery havoid)

end RecursivePolygero.FiatShamir.TwoLevel
