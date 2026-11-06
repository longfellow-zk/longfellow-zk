import LfzkV2.Current.AdapterFragment
import LfzkV2.Current.CellLayout
import LfzkV2.Current.FrontendVerifier
import LfzkV2.Current.GeneratorChecks

/-! Construct the application's frontend system from public circuit data and
parsed messages. The binary circuit is generated from the prime claim and
the adapter challenges. Its product semantics and physical cell addresses
are constructed here; neither is accepted as a semantic certificate. -/
noncomputable section
namespace LfzkV2.Current.ApplicationSetup
open SumcheckV2 WitnessSelection Application
open scoped Classical

variable {B N C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]

/-- Logical prime input indices and its fixed circuit. Shared inputs receive
no prime committed address. All pad coordinates are allocated below. -/
structure PrimePublic (N : Type) [Field N] (shared : ℕ) where
  out : ℕ
  input : ℕ
  nPublic : ℕ
  remaining : ℕ
  circuit : Layered.Circuit N out input
  inputIndex : (Fin nPublic ⊕ Fin (shared+remaining)) ↪ Cube input
  publicInputs : Fin nPublic → N

namespace PrimePublic
variable [Field N] {shared : ℕ} (s : PrimePublic N shared)

def pads : ℕ := CellLayout.Pads.count s.circuit
abbrev Other := CellLayout.Prime.Other s.remaining s.pads
abbrev Original := Fin (CellLayout.Prime.cells s.remaining s.pads)

def setup : FrontendVerifier.PrimeSetup N (Fin shared ⊕ s.Other) (Fin s.pads) where
  out := s.out
  input := s.input
  nPublic := s.nPublic
  nPrivate := shared+s.remaining
  circuit := s.circuit
  inputIndex := s.inputIndex
  publicInputs := s.publicInputs
  privateCoordinate := CellLayout.Prime.input shared s.remaining s.pads
  coordinate i := .inr (CellLayout.Prime.pad s.remaining s.pads i)
  plan := CellLayout.Pads.plan s.circuit id

end PrimePublic

namespace ShapeTopology

def pads (layout : Adapter.Circuit.Layout) : {d q : ℕ} → Adapter.Circuit.Shape d q → ℕ
  | _, _, .root => 0
  | d, q, .pair next => 2*layout.log d q+4+pads layout next

theorem reduction_pads {F : Type} [Field F] {d q input : ℕ} (layout : Adapter.Circuit.Layout)
    (other : ∀ d q, Adapter.Circuit.Fragment.Extension (F := F) (mid := layout.log d q)
      (layout.flat (Adapter.Circuit.half d) (Adapter.Circuit.half q))) (shape : Adapter.Circuit.Shape d q)
    (rest : Layered.Circuit F (layout.log d q) input) :
    CellLayout.Pads.count (Adapter.Circuit.Fragment.reduction layout other shape rest) =
      pads layout shape+CellLayout.Pads.count rest := by
  induction shape with
  | root => simp [Adapter.Circuit.Fragment.reduction, pads]
  | pair next ih => simp only [Adapter.Circuit.Fragment.reduction, ih, CellLayout.Pads.count, pads]; omega

end ShapeTopology

namespace AboveTopology

def pads {F : Type} : {out mid : ℕ} → Adapter.Circuit.Fragment.Above F out mid → ℕ
  | _, _, .hole => 0
  | _, _, .entry _ _ next => pads next
  | _, _, .layer (mid := mid) _ _ next => 2*mid+4+pads next

theorem plug_pads {F : Type} [Field F] {out mid input : ℕ}
    (above : Adapter.Circuit.Fragment.Above F out mid) (rest : Layered.Circuit F mid input) :
    CellLayout.Pads.count (above.plug rest) = pads above+CellLayout.Pads.count rest := by
  induction above with
  | hole => simp [Adapter.Circuit.Fragment.Above.plug, pads]
  | entry checks mapping next ih => simpa [Adapter.Circuit.Fragment.Above.plug, CellLayout.Pads.count, pads] using ih rest
  | layer checks body next ih => simp only [Adapter.Circuit.Fragment.Above.plug, CellLayout.Pads.count, ih, pads]; omega

end AboveTopology

/-- Public binary input layout, packing basis and the ordinary hash fragments.
The adapter itself is always generated here. Source maps are typed private
input addresses, and all public circuit inputs are Boolean values. -/
structure BinaryPublic (B : Type) [Field B] [Algebra (ZMod 2) B] (shared maskBits adviceBits : ℕ) where
  input : ℕ
  nPublic : ℕ
  nPrivate : ℕ
  words : ℕ
  degree : ℕ
  final : ℕ
  out : ℕ
  upper : ℕ
  degree_gt : 1 < degree
  basis : Module.Basis (Fin degree) (ZMod 2) B
  capacity : nPrivate ≤ words*degree
  inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input
  publicBits : Fin nPublic → Bool
  sharedPrivate : Fin shared → Fin nPrivate
  maskPrivate : Fin maskBits → Fin nPrivate
  advicePrivate : Fin 2 → Fin adviceBits → Fin nPrivate
  data_pos : 0 < shared+maskBits
  advice_pos : 0 < adviceBits
  layout : Adapter.Circuit.Layout
  output : Fin 2 ↪ Cube final
  others : Adapter.Circuit.Fragment.Others (F := B) layout (shared+maskBits) adviceBits input final output
  carry : Cube out → Option (Cube final)
  above : Adapter.Circuit.Fragment.Above B upper out

namespace BinaryPublic
variable {shared maskBits adviceBits : ℕ} (s : BinaryPublic B shared maskBits adviceBits)

def shape : Adapter.Circuit.Shape (shared+maskBits) adviceBits := Adapter.Circuit.plan _ _ s.data_pos s.advice_pos

def sources : Fin (shared+maskBits) → Cube s.input :=
  Fin.addCases (fun i => s.inputIndex (.inr (s.sharedPrivate i)))
    (fun i => s.inputIndex (.inr (s.maskPrivate i)))
def advice : Fin 2 → Fin adviceBits → Cube s.input :=
  fun tree i => s.inputIndex (.inr (s.advicePrivate tree i))

def circuit (powers : Fin 2 → Fin (shared+maskBits) → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin adviceBits → Bool) (targets : Fin 2 → Bˣ) :
    Layered.Circuit B s.upper s.input :=
  s.above.plug (Adapter.Circuit.Fragment.build s.layout s.output s.shape s.others s.carry s.sources s.advice
    powers base masked targets)

/-- This count depends only on public topology, not challenge coefficients. -/
def pads : ℕ := AboveTopology.pads s.above+(2*s.layout.log 1 1+4)+
  ShapeTopology.pads s.layout s.shape+(2*s.input+4)

omit [Fintype B] [DecidableEq B] in
theorem circuit_pads (powers : Fin 2 → Fin (shared+maskBits) → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin adviceBits → Bool) (targets : Fin 2 → Bˣ) :
    CellLayout.Pads.count (s.circuit powers base masked targets) = s.pads := by
  simp only [circuit, AboveTopology.plug_pads, Adapter.Circuit.Fragment.build, CellLayout.Pads.count, Adapter.Circuit.Fragment.body,
    ShapeTopology.reduction_pads]
  simp only [pads]
  omega

def cells : ℕ := CellLayout.Binary.cells s.words s.degree s.pads
abbrev Slot := Fin (s.cells+2)
abbrev Original := Fin s.cells
abbrev Pad := Fin s.pads

def packing : Packed.Statement (ZMod 2) B (Fin s.degree) (Fin s.words) s.Slot :=
  CellLayout.Binary.packing s.degree_gt s.basis 0 ⟨0,[]⟩

def packedIndex : Fin s.nPrivate ↪ (Fin s.words × Fin s.degree) :=
  CellLayout.primary (by have := s.degree_gt; omega) s.capacity

def setup (powers : Fin 2 → Fin (shared+maskBits) → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin adviceBits → Bool) (targets : Fin 2 → Bˣ) :
    FrontendVerifier.PackedSetup B (Fin s.degree) (Fin s.words) s.Slot s.Pad where
  out := s.upper
  input := s.input
  nPublic := s.nPublic
  nPrivate := s.nPrivate
  circuit := s.circuit powers base masked targets
  packing := s.packing
  inputIndex := s.inputIndex
  packedIndex := s.packedIndex
  publicInputs := Adapter.Circuit.bitValue ∘ s.publicBits
  coordinate := CellLayout.Binary.pad s.words s.degree s.pads
  plan := CellLayout.Pads.plan _ (Fin.cast (s.circuit_pads powers base masked targets))

/-- Canonical full-field input reconstruction is independent of all frontend
messages and all generated adapter coefficients. -/
def inputs (values : s.Slot → B) : Cube s.input → B :=
  s.packing.inputs s.inputIndex s.packedIndex (Adapter.Circuit.bitValue ∘ s.publicBits) values

omit [Fintype B] [DecidableEq B] in
theorem inputs_bit (values : s.Slot → B) (i : Cube s.input) :
    s.inputs values i = 0 ∨ s.inputs values i = 1 := by
  by_cases h : ∃ j, s.inputIndex j = i
  · obtain ⟨j,rfl⟩ := h
    cases j with
    | inl j =>
        simp only [inputs, Packed.Statement.inputs, circuitInputs, zeroExtend_apply, Sum.elim_inl]
        cases s.publicBits j <;> simp [Adapter.Circuit.bitValue]
    | inr j =>
        simp only [inputs, Packed.Statement.inputs, circuitInputs, zeroExtend_apply, Sum.elim_inr,
          Function.comp_id]
        exact s.packing.unpack_binary_bit s.packedIndex values j
  · have hz : s.inputs values i = 0 := by
      unfold inputs Packed.Statement.inputs circuitInputs
      apply zeroExtend_outside
      simpa only [not_exists] using h
    exact Or.inl hz

def bits (candidate : Candidate B s.Original) : Cube s.input → Bool :=
  fun i => decide (s.inputs (FingerprintRows.realize (CellLayout.selected s.cells) candidate) i = 1)

omit [Fintype B] in
theorem inputs_eq_bits (candidate : Candidate B s.Original) :
    s.inputs (FingerprintRows.realize (CellLayout.selected s.cells) candidate) = Adapter.Circuit.bitValue ∘ s.bits candidate := by
  funext i
  have hi := s.inputs_bit (FingerprintRows.realize (CellLayout.selected s.cells) candidate) i
  rcases hi with hi | hi <;> simp [bits, Adapter.Circuit.bitValue, hi]

def sharedValues (candidate : Candidate B s.Original) : Fin shared → Bool :=
  fun i => s.bits candidate (s.inputIndex (.inr (s.sharedPrivate i)))
def mask (candidate : Candidate B s.Original) : Fin maskBits → Bool :=
  fun i => s.bits candidate (s.inputIndex (.inr (s.maskPrivate i)))
def quotient (masked : Fin 2 → Fin adviceBits → Bool) (candidate : Candidate B s.Original) : Fin 2 → ℕ :=
  fun tree => Adapter.Tree.binaryValue
    (List.ofFn fun i => Bool.xor (s.bits candidate (s.advice tree i)) (masked tree i))

omit [Fintype B] in
theorem values_eq (candidate : Candidate B s.Original) :
    s.bits candidate ∘ s.sources = Handoff.values (s.sharedValues candidate) (s.mask candidate) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [sources, sharedValues, mask, Handoff.values]

end BinaryPublic

/-- Parsed prime messages and their boundary answers. All rows and the
batched claim are computed from these values by the existing compiler. -/
structure PrimeData {p shared : ℕ} [Fact p.Prime] (n : PrimePublic (ZMod p) shared) (C : Type) where
  payload : Layered.Replay.Payload n.circuit
  decode : C → ℕ → ZMod p
  nonzero : C → Linear.TerminalSampling.Nonzero (ZMod p)
  answers : ℕ → C
  rho : Fin (n.setup.prepare payload decode nonzero answers).rows.length → ZMod p

namespace PrimeData
variable {p shared : ℕ} [Fact p.Prime] {n : PrimePublic (ZMod p) shared} (d : PrimeData n C)
def frontend := n.setup.prepare d.payload d.decode d.nonzero d.answers
def replay := n.setup.replay d.payload d.decode d.nonzero d.answers
def claim := Prime.Claim.fromRow (Prime.batchRows d.frontend.rows.get d.rho)
end PrimeData

/-- The generated binary payload is typed by the circuit reconstructed from
this prime claim, the rescaling/conversion answers and the masked advice.
There is no caller-supplied generated circuit or product-equation proof. -/
structure BinaryData {p shared maskBits adviceBits : ℕ} [Fact p.Prime]
    (s : BinaryPublic B shared maskBits adviceBits) {n : PrimePublic (ZMod p) shared}
    (prime : PrimeData n C) (generator : Bˣ) where
  eta : ZMod p
  mu : ZMod p
  alpha : Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p)
  masked : Fin 2 → Fin adviceBits → Bool
  payload : Layered.Replay.Payload (s.circuit
    (fun tree i => generator^((alpha tree).val * (Handoff.weights prime.claim.sharedWeights eta i)).val)
    (generator^(-(p : ℤ))) masked (fun tree => generator^((alpha tree).val*mu).val))
  decode : C → ℕ → B
  nonzero : C → Linear.TerminalSampling.Nonzero B
  answers : ℕ → C
  U : Fin s.degree → B
  delta : Fin s.degree → B
  A : B

namespace BinaryData
variable {p shared maskBits adviceBits : ℕ} [Fact p.Prime]
  {s : BinaryPublic B shared maskBits adviceBits} {n : PrimePublic (ZMod p) shared}
  {prime : PrimeData n C} {generator : Bˣ} (d : BinaryData s prime generator)
def powers (tree : Fin 2) (i : Fin (shared+maskBits)) : Bˣ :=
  generator^((d.alpha tree).val * (Handoff.weights prime.claim.sharedWeights d.eta i)).val
def targets (tree : Fin 2) : Bˣ := generator^((d.alpha tree).val*d.mu).val
def setup := s.setup d.powers (generator^(-(p : ℤ))) d.masked d.targets
def frontend := d.setup.prepare d.payload d.decode d.nonzero d.answers d.U d.delta d.A
def replay := d.setup.replay d.payload d.decode d.nonzero d.answers d.U d.delta d.A
end BinaryData

/-- Trace is checked, while packing/compilation/replay, the cell layouts,
quotient range and generated adapter semantics are all derived. Generator
order is a public algebraic invariant; `decodeChecked` obtains it from the
runtime's primitive-generator check below. -/
def decode {p shared maskBits adviceBits M K : ℕ} [Fact p.Prime]
    (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic (ZMod p) shared)
    (prime : PrimeData n C) (generator : Bˣ) (order : orderOf generator = M)
    (bound : 2^adviceBits ≤ K) (data : BinaryData s prime generator) :
    Option (System B (Fin s.degree) (Fin s.words) s.Slot s.Pad n.Other (Fin n.pads)
      s.Original n.Original C C p shared maskBits M K) :=
  if ht : ∀ k, DualPacking.ArtinSchreier.traceF (ZMod 2) (data.U k) = 0 then
    some {
      binary := data.frontend
      prime := prime.frontend
      binaryReplay := data.replay
      primeReplay := prime.replay
      binaryLayout := CellLayout.selected s.cells
      primeLayout := CellLayout.Prime.layout n.remaining n.pads
      sharedValues := s.sharedValues
      mask := s.mask
      rho := prime.rho
      eta := data.eta
      mu := data.mu
      alpha := data.alpha
      generator := generator
      order := order
      quotient := fun w => s.quotient data.masked w.1
      quotient_lt := by
        intro w tree
        apply lt_of_lt_of_le _ bound
        simpa only [BinaryPublic.quotient, List.length_ofFn] using
          (Adapter.Tree.binaryValue_lt (List.ofFn fun i =>
            Bool.xor (s.bits w.1 (s.advice tree i)) (data.masked tree i)))
      trace := ht
      products := by
        intro w hs tree
        letI : CharP B 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) B).injective 2
        have hc : (s.circuit data.powers (generator^(-(p : ℤ))) data.masked data.targets).Satisfies
            (Adapter.Circuit.bitValue ∘ s.bits w.1) := by
          change (s.circuit data.powers (generator^(-(p : ℤ))) data.masked data.targets).Satisfies
            (s.inputs (FingerprintRows.realize (CellLayout.selected s.cells) w.1)) at hs
          rwa [s.inputs_eq_bits] at hs
        have hp := Adapter.Circuit.Fragment.full_product_check s.layout s.output s.shape s.others
          s.carry s.above s.sources s.advice generator
          (Handoff.weights prime.claim.sharedWeights data.eta) data.mu
          (fun tree => (data.alpha tree).val) data.masked (s.bits w.1) hc
        simpa only [BinaryPublic.quotient, s.values_eq, PrimeData.claim] using hp.2 tree }
  else none

/-- Concrete mdoc generator validation supplies full group order. Neither a
primitive-order certificate nor an adapter-semantics certificate is an input
to the protocol decoder. The trace check is performed by `decode`. -/
def decodeChecked {shared maskBits adviceBits : ℕ}
    (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
    (prime : PrimeData n C) (hcard : Fintype.card B = Adapter.Mdoc.binaryOrder) (x : Bˣ)
    (bound : 2^adviceBits ≤ Adapter.Mdoc.quotientBound)
    (data : BinaryData s prime (x^Adapter.Mdoc.generatorExponent)) :
    Option (System B (Fin s.degree) (Fin s.words) s.Slot s.Pad n.Other (Fin n.pads)
      s.Original n.Original C C Adapter.Mdoc.primeOrder shared maskBits Adapter.Mdoc.groupOrder
        Adapter.Mdoc.quotientBound) :=
  if hx : Adapter.Mdoc.generatorCheck x = true then
    decode s n prime _ (Adapter.Mdoc.generator_order_of_check hcard x hx) bound data
  else none

end LfzkV2.Current.ApplicationSetup
