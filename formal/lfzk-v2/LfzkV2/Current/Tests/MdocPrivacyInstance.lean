import LfzkV2.Current.Tests.MdocInstance
import LfzkV2.Current.GeneratorChecks
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralDomain

/-! The canonical toy mdoc instance for the deployed privacy and honest
endpoints: every premise of `Mdoc.ZeroKnowledge.statClose_rust`,
`Mdoc.VerifierPrivacy.acceptance_probability_rust` and
`Mdoc.Completeness.accepts_rust` is discharged, at the Rust reader. The
field premises (`pivotOne`, `primitive`) need a basis whose first vector is
one and whose second generates the unit group: the powers of an abstract
generator of GF(2^128). It is not Rust's
`x mod x^128+x^7+x^2+x+1`; inhabitation needs only its existence. The toy
circuits have no checks, so every witness satisfies them. -/
noncomputable section
namespace LfzkV2.Current.Tests.MdocInstance
open LfzkV2.Current LfzkV2.Current.ConcreteSetup LfzkV2.Current.ZeroKnowledge
open scoped Classical

theorem card_GF : Nat.card GF = 2 ^ 128 := GaloisField.card 2 128 (by decide)

theorem card_units : Nat.card GFˣ = 2 ^ 128 - 1 := by
  rw [Nat.card_units, card_GF]

theorem exists_gen : ∃ g : GFˣ, Subgroup.zpowers g = ⊤ :=
  isCyclic_iff_exists_zpowers_eq_top.mp inferInstance

def gen : GFˣ := Classical.choose exists_gen

theorem gen_top : Subgroup.zpowers gen = ⊤ := Classical.choose_spec exists_gen

theorem gen_order : orderOf gen = 2 ^ 128 - 1 := by
  rw [← Nat.card_zpowers, gen_top, Subgroup.card_top, card_units]

theorem adjoin_top : IntermediateField.adjoin (ZMod 2) {(gen : GF)} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  by_cases hy : y = 0
  · rw [hy]; exact IntermediateField.zero_mem _
  · have mem : Units.mk0 y hy ∈ Subgroup.zpowers gen := by rw [gen_top]; trivial
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).mpr mem
    have : y = (gen : GF) ^ k := by
      have := congrArg Units.val hk
      simpa using this.symm
    rw [this]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)) k

def powerBasis : PowerBasis (ZMod 2) GF :=
  (IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (gen : GF))).map
    ((IntermediateField.equivOfEq adjoin_top).trans IntermediateField.topEquiv)

theorem dim : powerBasis.dim = 128 := by
  rw [← powerBasis.finrank]; exact GaloisField.finrank 2 (by decide)

/-- The pivot basis: `1, g, g^2, ...`. -/
def pivot : Module.Basis (Fin 128) (ZMod 2) GF := powerBasis.basis.reindex (finCongr dim)

theorem pivot_zero : pivot 0 = 1 := by
  simp [pivot, Module.Basis.reindex_apply, powerBasis.basis_eq_pow]

theorem pivot_one : pivot 1 = (gen : GF) := by
  simp [pivot, Module.Basis.reindex_apply, powerBasis, PowerBasis.map]

theorem primitive : Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX pivot) = true := by
  have hx : MdocRuntime.polynomialX pivot = gen := by
    apply Units.ext; simp [MdocRuntime.polynomialX, pivot_one]
  rw [hx, Adapter.Mdoc.generatorCheck, List.all_eq_true]
  intro q hq
  have qs : ∀ q ∈ Adapter.Mdoc.orderFactors, 1 < q ∧ q ≤ Adapter.Mdoc.groupOrder := by decide +kernel
  obtain ⟨q1, q2⟩ := qs q hq
  rw [decide_eq_true_iff]
  apply pow_ne_one_of_lt_orderOf
  · have := Nat.div_pos q2 (by omega); omega
  · rw [gen_order]
    exact Nat.div_lt_self (by unfold Adapter.Mdoc.groupOrder Adapter.Mdoc.binaryOrder; decide) q1

/-- A circuit with no checks anywhere. -/
def checkFree {F : Type} [Field F] : {out input : ℕ} → Layered.Circuit F out input → Bool
  | _, _, .input => true
  | _, _, .entry k _ rest => k == 0 && checkFree rest
  | _, _, .layer a _ rest => a == 0 && checkFree rest

theorem satisfies_of_checkFree {F : Type} [Field F] : {out input : ℕ} → (c : Layered.Circuit F out input) →
    checkFree c = true → ∀ w, c.Satisfies w
  | _, _, .input, _, _ => trivial
  | _, _, .entry k e rest, h, w => by
      simp only [checkFree, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨fun i => Fin.elim0 i, satisfies_of_checkFree rest h w⟩
  | _, _, .layer a body rest, h, w => by
      simp only [checkFree, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨fun i => Fin.elim0 i, satisfies_of_checkFree rest h w⟩

/-- The toy hash circuit with the pivot basis. -/
def binaryP : BinaryCircuit GF := { binary 1 with basis := pivot }

def boundsP : MdocIdentifiers.Bounds binaryP prime where
  inputFits := by decide +kernel
  privateFits := by decide +kernel
  padsFit := by decide +kernel
  binaryCellsFit := by decide +kernel
  primeCellsFit := by decide +kernel
  layerFits := by decide +kernel
  primeLayerFits := by decide +kernel
  committedFit := by decide +kernel
  hashDepthFit := by decide +kernel
  adapterDepth_lt_hashDepth := by decide +kernel
  primeDepthFit := by decide +kernel
  adapterDepthFit := by decide +kernel
  binaryRowsFit := by decide +kernel
  primeRowsFit := by decide +kernel

abbrev Sh := MdocRuntime.shape binaryP.description prime.description binaryP.plan prime.plan
  boundsP.inputFits boundsP.privateFits (Frontend.RuntimeStatement.degreeFits binaryP)

def requestP : CanonicalRequest.Request Sh binaryP.nPublic := ⟨⟨[], by decide⟩, Fin.elim0, fun _ => 0⟩

theorem validP : MdocWitness.HashValid
    (RequestedSimulator.requestedBinary binaryP prime.description prime.plan Sh requestP) (fun _ => false) :=
  satisfies_of_checkFree _ (by decide +kernel) _

/-- Every premise of the deployed privacy endpoint, inhabited: no prior or
later observer queries, an empty additional window. -/
def privacy :=
  Mdoc.ZeroKnowledge.statClose_rust binaryP prime cantor scalars ids boundsP
    (Context := Unit) (Observed := Unit) (preQueries := 0) (postQueries := 0)
    (fun _ => .done ()) (fun _ => requestP) (fun _ _ _ => .done ())
    (fun _ _ => false) (fun _ _ => 0) pivot_zero primitive
    (fun _ _ => validP) (fun _ _ => by dsimp only; exact satisfies_of_checkFree _ (by decide +kernel) _) ∅ (fun _ => 0)

/-- Every premise of the deployed simulator-acceptance endpoint, inhabited. -/
def acceptance :=
  Mdoc.VerifierPrivacy.acceptance_probability_rust binaryP prime cantor scalars ids boundsP
    (Context := Unit) (preQueries := 0) (fun _ => .done ()) (fun _ => requestP)
    (fun _ _ => false) (fun _ _ => 0) pivot_zero primitive
    (fun _ _ => validP) (fun _ _ => by dsimp only; exact satisfies_of_checkFree _ (by decide +kernel) _) ∅ (fun _ => 0)

/-- The setup of the completeness instance. -/
abbrev runtimeP := Mdoc.Setup.runtime binaryP prime cantor scalars ids boundsP

theorem setupWidthP : Protocol.RustSampler.setupWidth runtimeP.protocol ≤ 2 ^ 40 := by
  decide +kernel

theorem fitsP : (MdocRuntime.geometry binaryP.description prime.description binaryP.plan prime.plan).roles.length <
    2 ^ 64 := by
  decide +kernel

/-- Every premise of the deployed completeness endpoint, inhabited, for
every prover coin and every SHA answer outside the PRF inputs. -/
def completeness :=
  fun coins nonces outside => Mdoc.Completeness.accepts_rust runtimeP (fun _ => false) (fun _ => 0) requestP
    pivot_zero primitive validP (by dsimp only; exact satisfies_of_checkFree _ (by decide +kernel) _)
    coins nonces outside setupWidthP fitsP

run_cmd ProofAudit.standardAxioms #[``privacy, ``acceptance, ``completeness, ``primitive, ``pivot_zero]

end LfzkV2.Current.Tests.MdocInstance
