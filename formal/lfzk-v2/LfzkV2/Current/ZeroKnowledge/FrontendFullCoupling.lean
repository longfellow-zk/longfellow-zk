import LfzkV2.Current.ZeroKnowledge.FrontendGlobalCoins
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteCoupling
import LfzkV2.Current.ZeroKnowledge.FrontendCompletePacking
import LfzkV2.Current.HashCircuit

/-! The whole frontend coin change follows the public order of messages.
Later fibers are indexed by earlier public payloads, including both
fingerprints. Only the coupling recovers private cells; the public
simulator remains the forward sampler in `CompleteSimulation`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace LfzkV2.Current.ZeroKnowledge.Frontend.FullCoupling
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)
variable (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)

def nativeStage (responses : CompleteHonest.Masks (B := B)) :
    CircuitTape prime.circuit ≃ CircuitTape prime.circuit :=
  CompleteCoupling.primeEquiv binary prime primePlan samples base H
    (CompleteSimulation.selectedState binary prime primePlan samples base H context responses)
    (CompleteHonest.primeInputs binary prime original remaining)

def nativePrefix (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit) :
    CompleteSimulation.PrimePrefix binary prime primePlan Key Base C :=
  CompleteSimulation.primePrefix binary prime primePlan samples base H
    (CompleteSimulation.selectedState binary prime primePlan samples base H context responses)
    (simulateCircuit prime.circuit coin)

def adapterStage (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit) :
    (P × Fin (2^24)) ≃ ((P × MdocAdvice.Value) × Fin 16) :=
  CompleteCoupling.adapterEquiv binary prime primePlan samples base H
    (nativePrefix binary prime primePlan samples base H context responses coin)
    (WitnessInputs.shared binary original)

def convertedPrefix (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) :
    CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C :=
  CompleteSimulation.conversionPrefix binary prime primePlan samples base H
    (nativePrefix binary prime primePlan samples base H context responses coin) converted.1.1

def recoveredPrivate (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) : Fin binary.nPrivate → Bool :=
  let native := nativePrefix binary prime primePlan samples base H context responses coin
  CompleteInputs.recoveredPrivate binary original native.claim.sharedWeights native.eta.val
    (CompleteCoupling.alphas binary prime primePlan samples base H native) converted.1.1 converted.1.2

def binaryStage (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) :
    CircuitTape binary.description.template ≃ CircuitTape binary.description.template :=
  CompleteCoupling.binaryEquiv binary prime primePlan samples base H
    (nativePrefix binary prime primePlan samples base H context responses coin)
    (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2
    (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
      (recoveredPrivate binary prime primePlan samples base H context original responses coin converted))

/-- The source of a public prefix recovers the original pads, the common
prime/binary scalar and the OTP bits. Packing coins are recovered last. -/
def source (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template) :
    CompleteHonest.Tape binary prime where
  prime := (nativeStage binary prime primePlan samples base H context original remaining responses).symm coin
  mask := ((adapterStage binary prime primePlan samples base H context original responses coin).symm converted).1
  otp := ((adapterStage binary prime primePlan samples base H context original responses coin).symm converted).2
  binary := (binaryStage binary prime primePlan samples base H context original responses coin converted).symm binaryCoin
  packing := 0

omit [Fintype B] [DecidableEq B] in
theorem source_private (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template) :
    CompleteHonest.privateBits binary prime original
      (source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin) =
        recoveredPrivate binary prime primePlan samples base H context original responses coin converted := by
  unfold CompleteHonest.privateBits source recoveredPrivate adapterStage CompleteCoupling.adapterEquiv
    Adapter.Mdoc.coupling Adapter.rawMuAdviceEquiv Adapter.muAdviceEquiv
    CompleteInputs.recoveredPrivate
  dsimp only [Equiv.symm_trans_apply,Equiv.prodCongr_symm,Equiv.prodCongr_apply,
    Equiv.symm_symm,Equiv.prodComm_apply,Equiv.prodAssoc_apply,Equiv.prodAssoc_symm_apply,
    Adapter.muEquiv,Equiv.coe_fn_symm_mk,Equiv.prodCongrRight_symm,Equiv.prodCongrRight_apply]
  congr 1
  funext tree i
  exact (AdapterBits.rawOtp_bits _ tree i).symm.trans
    (congrArg (fun pair : MdocAdvice.Value × Fin 16 => MdocAdvice.bits pair.1 tree i)
      (AdapterBits.rawOtpEquiv.apply_symm_apply _))

omit [Fintype B] [DecidableEq B] in
theorem source_payload (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template) :
    CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H
      (nativePrefix binary prime primePlan samples base H context responses coin)
      (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
        (recoveredPrivate binary prime primePlan samples base H context original responses coin converted))
      (source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin).binary =
        simulateCircuit binary.description.template binaryCoin := by
  exact (CompleteCoupling.binaryEquiv_payload binary prime primePlan samples base H _ _ _ _ _).symm.trans
    (congrArg (simulateCircuit binary.description.template)
      ((binaryStage binary prime primePlan samples base H context original responses coin converted).apply_symm_apply binaryCoin))

omit [Fintype B] [DecidableEq B] in
theorem source_native (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template) :
    realCircuit (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
      primePlan (CompleteHonest.primeInputs binary prime original remaining) 0
      (CompleteSimulation.selectedState binary prime primePlan samples base H context responses)
      (source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin).prime =
        simulateCircuit prime.circuit coin := by
  exact (CompleteCoupling.primeEquiv_payload binary prime primePlan samples base H _ _ _).symm.trans
    (congrArg (simulateCircuit prime.circuit)
      ((nativeStage binary prime primePlan samples base H context original remaining responses).apply_symm_apply coin))

omit [Fintype B] [DecidableEq B] in
theorem source_adapter (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template) :
    let tape := source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
    let native := nativePrefix binary prime primePlan samples base H context responses coin
    let mu := Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val+tape.mask
    let quotient := Adapter.Mdoc.advice native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val
      (CompleteCoupling.alphas binary prime primePlan samples base H native) mu
    (mu,AdapterBits.xorEquiv quotient (AdapterBits.rawOtpEquiv tape.otp).1) = converted.1 := by
  let native := nativePrefix binary prime primePlan samples base H context responses coin
  exact Adapter.rawMuAdviceEquiv_inverse_response
    (Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val)
    (Adapter.Mdoc.advice native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val
      (CompleteCoupling.alphas binary prime primePlan samples base H native)) converted

def packingBase (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template) :=
  CompleteHonest.packingInstance binary prime primePlan samples base H
    (nativePrefix binary prime primePlan samples base H context responses coin)
    (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2
    (simulateCircuit binary.description.template binaryCoin) original
    (source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin)

omit [DecidableEq B] in
theorem packingBase_valid (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template)
    (valid : (CompleteSimulation.generatedCircuit binary prime primePlan
      (nativePrefix binary prime primePlan samples base H context responses coin)
      (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2).Satisfies
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
        (recoveredPrivate binary prime primePlan samples base H context original responses coin converted))) :
    let inst := packingBase binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
    inst.target = inst.trueValue := by
  let recovered := source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
  have hp := source_private binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
  have hv := Eq.mpr (congrArg (fun bits => (CompleteSimulation.generatedCircuit binary prime primePlan
      (nativePrefix binary prime primePlan samples base H context responses coin)
      (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2).Satisfies
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary bits)) hp) valid
  have h := CompletePacking.packingInstance_valid binary prime primePlan samples base H _ _ _ original recovered hv
  have hmessages := (congrArg (fun bits => CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H
      (nativePrefix binary prime primePlan samples base H context responses coin)
      (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary bits) recovered.binary) hp).trans
        (source_payload binary prime primePlan samples base H context original remaining responses coin converted binaryCoin)
  exact Eq.mp (congrArg (fun payload =>
    let inst := CompleteHonest.packingInstance binary prime primePlan samples base H
      (nativePrefix binary prime primePlan samples base H context responses coin)
      (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2 payload original recovered
    inst.target = inst.trueValue) hmessages) h

def packingDelta (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template)
    (u : Fin 128 → DualPacking.ArtinSchreier.Masking.TraceZero (ZMod 2) B) (i : Fin 128) : B :=
  let read := CompleteSimulation.binaryReplay binary prime primePlan samples base H
    (nativePrefix binary prime primePlan samples base H context responses coin)
    (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2
    (simulateCircuit binary.description.template binaryCoin)
  let state := CompleteTranscript.bind read.2 fun writes => { writes with packingU := some (fun i => (u i).val) }
  samples.binary (CompleteTranscript.step base H state).1 i.val

def hashChecks (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) : Prop :=
  let native := nativePrefix binary prime primePlan samples base H context responses coin
  let conversion := convertedPrefix binary prime primePlan samples base H context responses coin converted
  HashCircuit.Checks binary.description.layout binary.description.output binary.description.shape binary.description.others
    binary.description.carry binary.description.above binary.description.sources binary.description.advice
    (CompleteSimulation.powers binary prime primePlan native conversion) (CompleteSimulation.generatorBase binary)
    (MdocAdvice.bits converted.1.2) (CompleteSimulation.targets binary prime primePlan conversion)
    (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
      (recoveredPrivate binary prime primePlan samples base H context original responses coin converted))

omit [Fintype B] [DecidableEq B] in
theorem generated_valid (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16)
    (hash : hashChecks binary prime primePlan samples base H context original responses coin converted) :
    (CompleteSimulation.generatedCircuit binary prime primePlan
      (nativePrefix binary prime primePlan samples base H context responses coin)
      (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2).Satisfies
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
        (recoveredPrivate binary prime primePlan samples base H context original responses coin converted)) := by
  letI : CharP B 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) B).injective 2
  apply (HashCircuit.build_satisfies_iff _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨hash,?_⟩
  let native := nativePrefix binary prime primePlan samples base H context responses coin
  exact CompleteInputs.recovered_adapter_satisfies binary original (MdocRuntime.generator binary.basis)
    native.claim.sharedWeights native.eta.val (CompleteCoupling.alphas binary prime primePlan samples base H native)
    converted.1.1 converted.1.2

def packingStage (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, hashChecks binary prime primePlan samples base H context original responses coin converted)
    (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template) :
    Packing.Tape (F := B) (0 : Fin 128) ≃ Packing.Tape (F := B) (0 : Fin 128) :=
  Packing.coupling (packingBase binary prime primePlan samples base H context original remaining responses coin converted binaryCoin)
    pivotOne (packingBase_valid binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
      (generated_valid binary prime primePlan samples base H context original responses coin converted (hash responses coin converted)))
    (packingDelta binary prime primePlan samples base H context responses coin converted binaryCoin)

variable (pivotOne : binary.basis 0 = 1)
variable (hash : ∀ responses coin converted, hashChecks binary prime primePlan samples base H context original responses coin converted)

def inner (responses : CompleteHonest.Masks (B := B)) :
    CompleteHonest.Tape binary prime ≃ GlobalCoins.Public binary prime :=
  GlobalCoins.stages binary prime
    (nativeStage binary prime primePlan samples base H context original remaining responses)
    (adapterStage binary prime primePlan samples base H context original responses)
    (binaryStage binary prime primePlan samples base H context original responses)
    (packingStage binary prime primePlan samples base H context original remaining pivotOne hash responses)

omit [DecidableEq B] in
theorem inner_symm (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template)
    (packingCoin : Packing.Tape (F := B) (0 : Fin 128)) :
    (inner binary prime primePlan samples base H context original remaining pivotOne hash responses).symm
      (coin,converted,binaryCoin,packingCoin) =
        { source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin with
          packing := (packingStage binary prime primePlan samples base H context original remaining pivotOne hash
            responses coin converted binaryCoin).symm packingCoin } := rfl

omit [DecidableEq B] in
theorem recovered_packing (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template)
    (packingCoin : Packing.Tape (F := B) (0 : Fin 128)) :
    let recoveredCoins := (packingStage binary prime primePlan samples base H context original remaining pivotOne hash
      responses coin converted binaryCoin).symm packingCoin
    let recovered := { source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin with
      packing := recoveredCoins }
    let inst := CompleteHonest.packingInstance binary prime primePlan samples base H
      (nativePrefix binary prime primePlan samples base H context responses coin)
      (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2
      (simulateCircuit binary.description.template binaryCoin) original recovered
    let view := Packing.simulate binary.basis 0 packingCoin
    (fun i => (view.1 i).val) = inst.honestU ∧
      view.2 = inst.honestA (packingDelta binary prime primePlan samples base H context responses coin converted binaryCoin view.1) := by
  dsimp only
  let inst := packingBase binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
  let delta := packingDelta binary prime primePlan samples base H context responses coin converted binaryCoin
  let valid := packingBase_valid binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
    (generated_valid binary prime primePlan samples base H context original responses coin converted (hash responses coin converted))
  let e := packingStage binary prime primePlan samples base H context original remaining pivotOne hash responses coin converted binaryCoin
  have view := Packing.honest_view inst pivotOne valid delta (e.symm packingCoin)
  have apply : Packing.coupling inst pivotOne valid delta (e.symm packingCoin) = packingCoin := e.apply_symm_apply packingCoin
  rw [apply] at view
  have instance_eq := CompletePacking.packingInstance_change_coins binary prime primePlan samples base H
    (nativePrefix binary prime primePlan samples base H context responses coin)
    (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2
    (simulateCircuit binary.description.template binaryCoin) original
    (source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin)
    (e.symm packingCoin)
  exact ⟨view.1.trans (congrArg (fun inst => inst.honestU) instance_eq.symm),
    view.2.trans (congrArg (fun inst => inst.honestA (delta (Packing.simulate binary.basis 0 packingCoin).1)) instance_eq.symm)⟩

omit [DecidableEq B] in
theorem inner_view (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (P × MdocAdvice.Value) × Fin 16) (binaryCoin : CircuitTape binary.description.template)
    (packingCoin : Packing.Tape (F := B) (0 : Fin 128)) :
    CompleteHonest.runSelected binary prime primePlan samples base H
      (CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)).2 responses original remaining
      ((inner binary prime primePlan samples base H context original remaining pivotOne hash responses).symm
        (coin,converted,binaryCoin,packingCoin)) =
    (CompleteSimulation.simulate binary prime primePlan samples base H context
      (GlobalCoins.coinsEquiv binary prime (responses,coin,converted,binaryCoin,packingCoin))).raw := by
  rw [inner_symm]
  have hn := source_native binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
  have ha := source_adapter binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
  have hp := source_private binary prime primePlan samples base H context original remaining responses coin converted binaryCoin
  have hb := (congrArg (fun bits => CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H
      (nativePrefix binary prime primePlan samples base H context responses coin)
      (convertedPrefix binary prime primePlan samples base H context responses coin converted) converted.1.2
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary bits)
      (source binary prime primePlan samples base H context original remaining responses coin converted binaryCoin).binary) hp).trans
        (source_payload binary prime primePlan samples base H context original remaining responses coin converted binaryCoin)
  have hpack := recovered_packing binary prime primePlan samples base H context original remaining pivotOne hash
    responses coin converted binaryCoin packingCoin
  have hpa := hpack.2
  unfold packingDelta at hpa
  dsimp only [nativePrefix,convertedPrefix,CompleteSimulation.selectedState] at hpa
  dsimp only [CompleteSimulation.selectedState] at hn
  dsimp only [packingDelta,nativePrefix,convertedPrefix,CompleteSimulation.selectedState] at ha hb hpack
  have hm := congrArg Prod.fst ha
  have had := congrArg Prod.snd ha
  dsimp only at hm had
  rw [hm,Adapter.Mdoc.advice_at] at had
  dsimp only [CompleteCoupling.alphas] at had
  dsimp only [CompleteHonest.privateBits] at hb
  dsimp only [CompleteHonest.runSelected,CompleteSimulation.simulate,CompleteSimulation.Result.raw,
    GlobalCoins.coinsEquiv,Equiv.coe_fn_mk]
  rw [hn]
  rw [hm,had]
  dsimp only [CompleteHonest.privateBits]
  rw [hb]
  rw [← hpack.1]
  erw [← hpa]
  rfl

variable (coefficients : C → WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)

/-- Both dedicated pairs of masks are recovered only after every selected
cell. The first-round coefficients are sampled before either response. -/
def coupling : (CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)) ≃
    CompleteSimulation.Coins binary prime :=
  GlobalCoins.selectedEquiv binary prime
    (coefficients (CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)).1)
    original remaining (inner binary prime primePlan samples base H context original remaining pivotOne hash)

omit [DecidableEq B] in
theorem coupling_symm_tape (coins : CompleteSimulation.Coins binary prime) :
    ((coupling binary prime primePlan samples base H context original remaining pivotOne hash coefficients).symm coins).1 =
      (inner binary prime primePlan samples base H context original remaining pivotOne hash coins.fingerprints).symm
        (coins.prime,((coins.mu,coins.advice),coins.otpUnused),coins.binary,coins.packing) := rfl

omit [DecidableEq B] in
theorem recovered_view (coins : CompleteSimulation.Coins binary prime) :
    let recovered := (coupling binary prime primePlan samples base H context original remaining pivotOne hash coefficients).symm coins
    CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining recovered.1 recovered.2 =
      (CompleteSimulation.simulate binary prime primePlan samples base H context coins).raw := by
  dsimp only
  have fingerprints := GlobalCoins.recovered_fingerprints binary prime
    (coefficients (CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)).1)
    original remaining (inner binary prime primePlan samples base H context original remaining pivotOne hash) coins
  have hf : CompleteHonest.responses binary prime
      (coefficients (CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)).1)
      original remaining
      ((coupling binary prime primePlan samples base H context original remaining pivotOne hash coefficients).symm coins).1
      ((coupling binary prime primePlan samples base H context original remaining pivotOne hash coefficients).symm coins).2 =
        coins.fingerprints := fingerprints
  dsimp only [CompleteHonest.run]
  rw [hf]
  rw [coupling_symm_tape]
  exact inner_view binary prime primePlan samples base H context original remaining pivotOne hash
    coins.fingerprints coins.prime ((coins.mu,coins.advice),coins.otpUnused) coins.binary coins.packing

omit [DecidableEq B] in
theorem coupling_view (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) :
    CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining tape masks =
      (CompleteSimulation.simulate binary prime primePlan samples base H context
        (coupling binary prime primePlan samples base H context original remaining pivotOne hash coefficients (tape,masks))).raw := by
  have h := recovered_view binary prime primePlan samples base H context original remaining pivotOne hash coefficients
    (coupling binary prime primePlan samples base H context original remaining pivotOne hash coefficients (tape,masks))
  rw [(coupling binary prime primePlan samples base H context original remaining pivotOne hash coefficients).symm_apply_apply] at h
  exact h

include pivotOne hash in
omit [DecidableEq B] in
theorem sameDistribution {Observed : Type} [DecidableEq Observed]
    (observe : CompleteSimulation.RawResult binary prime primePlan Key Base C → Observed) :
    LigeroFamily.SameDistribution
      (fun coins : CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B) =>
        observe (CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining coins.1 coins.2))
      (fun coins : CompleteSimulation.Coins binary prime =>
        observe (CompleteSimulation.simulate binary prime primePlan samples base H context coins).raw) := by
  apply LigeroFamily.sameDistribution_of_equiv
    (coupling binary prime primePlan samples base H context original remaining pivotOne hash coefficients)
  intro coins
  exact congrArg observe (coupling_view binary prime primePlan samples base H context original remaining
    pivotOne hash coefficients coins.1 coins.2)

end LfzkV2.Current.ZeroKnowledge.Frontend.FullCoupling
