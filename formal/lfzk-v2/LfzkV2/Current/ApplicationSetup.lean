import LfzkV2.Current.AdapterFragment
import LfzkV2.Current.CellLayout
import LfzkV2.Current.FrontendVerifier
import LfzkV2.Current.GeneratorChecks

/-! Construct the application's frontend system from public circuit data and
parsed messages. The binary circuit is fixed: the hash circuit and the archived
adapter fragment. Per-proof adapter values are virtual inputs, derived from the
prime claim and the adapter exchange. Product semantics and cell addresses
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

def pads (layout : Adapter.Fragment.Layout) : {n : ℕ} → Adapter.ProductTree.Shape n → ℕ
  | _, .root => 0
  | n, .pair next => 2*layout.log n+4+pads layout next

theorem reduction_pads {F : Type} [Field F] {n input : ℕ} (layout : Adapter.Fragment.Layout)
    (other : ∀ n, Adapter.Fragment.Extension (F := F) (mid := layout.log n)
      (layout.flat (Adapter.Circuit.half n))) (shape : Adapter.ProductTree.Shape n)
    (rest : Layered.Circuit F (layout.log n) input) :
    CellLayout.Pads.count (Adapter.Fragment.reduction layout other shape rest) =
      pads layout shape+CellLayout.Pads.count rest := by
  induction shape with
  | root => simp [Adapter.Fragment.reduction, pads]
  | pair next ih => simp only [Adapter.Fragment.reduction, ih, CellLayout.Pads.count, pads]; omega

end ShapeTopology

namespace AboveTopology

def pads {F : Type} : {out mid : ℕ} → Adapter.Fragment.Above F out mid → ℕ
  | _, _, .hole => 0
  | _, _, .entry _ _ next => pads next
  | _, _, .layer (mid := mid) _ _ next => 2*mid+4+pads next

theorem plug_pads {F : Type} [Field F] {out mid input : ℕ}
    (above : Adapter.Fragment.Above F out mid) (rest : Layered.Circuit F mid input) :
    CellLayout.Pads.count (above.plug rest) = pads above+CellLayout.Pads.count rest := by
  induction above with
  | hole => simp [Adapter.Fragment.Above.plug, pads]
  | entry checks mapping next ih => simpa [Adapter.Fragment.Above.plug, CellLayout.Pads.count, pads] using ih rest
  | layer checks body next ih => simp only [Adapter.Fragment.Above.plug, CellLayout.Pads.count, ih, pads]; omega

end AboveTopology

/-- Public binary input layout, packing basis, the ordinary hash fragments
and the fixed adapter fragment. The shared input array is
`[public | committed private | virtual]`: the virtual suffix holds one
adapter leaf per entry, tree-major. Source maps are typed private input
addresses, and all public circuit inputs are Boolean values. -/
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
  virtualIndex : Fin (2*(shared+maskBits+adviceBits)) ↪ Cube input
  virtualDisjoint : ∀ j v, inputIndex j ≠ virtualIndex v
  publicBits : Fin nPublic → Bool
  sharedPrivate : Fin shared → Fin nPrivate
  maskPrivate : Fin maskBits → Fin nPrivate
  advicePrivate : Fin 2 → Fin adviceBits → Fin nPrivate
  data_pos : 0 < shared+maskBits
  leaves_gt : 2 < shared+maskBits+adviceBits
  layout : Adapter.Fragment.Layout
  output : Fin 2 ↪ Cube final
  others : Adapter.Fragment.Others (F := B) layout (shared+maskBits+adviceBits) input final output
  carry : Cube out → Option (Cube final)
  above : Adapter.Fragment.Above B upper out

namespace BinaryPublic
variable {shared maskBits adviceBits : ℕ} (s : BinaryPublic B shared maskBits adviceBits)

/-- Leaves per tree: data leaves (shared bits, then mask bits), then quotient leaves. -/
abbrev leaves : ℕ := shared+maskBits+adviceBits

def shape : Adapter.ProductTree.Shape (Adapter.Circuit.half (shared+maskBits+adviceBits)) :=
  Adapter.ProductTree.plan _ (by have := s.leaves_gt; dsimp [Adapter.Circuit.half]; omega)

/-- The adapter's first reduction reads leaf `(tree,i)` at virtual entry
`tree*leaves+i`. -/
def read : Adapter.ProductTree.Wire (shared+maskBits+adviceBits) → Cube s.input :=
  fun w => s.virtualIndex (Adapter.ProductTree.wireIndex _ w)

/-- The fixed joint circuit. No challenge, advice or target enters it. -/
def circuit : Layered.Circuit B s.upper s.input :=
  s.above.plug (Adapter.Fragment.build s.layout s.output s.shape s.others s.carry s.read)

def pads : ℕ := AboveTopology.pads s.above+(2*s.layout.log 2+4)+
  ShapeTopology.pads s.layout s.shape+(2*s.input+4)

omit [Fintype B] [DecidableEq B] in
theorem circuit_pads : CellLayout.Pads.count s.circuit = s.pads := by
  simp only [circuit, AboveTopology.plug_pads, Adapter.Fragment.build, CellLayout.Pads.count,
    Adapter.Fragment.body, ShapeTopology.reduction_pads]
  simp only [pads]
  omega

def cells : ℕ := CellLayout.Binary.cells s.words s.degree s.pads
abbrev Slot := Fin (s.cells+2)
abbrev Original := Fin s.cells
abbrev Pad := Fin s.pads

/-- The fixed pad plan of the fixed circuit. -/
def padPlan : Layered.Replay.PadPlan (Pad := s.Pad) s.circuit :=
  CellLayout.Pads.plan _ (Fin.cast s.circuit_pads)

def packing : Packed.Statement (ZMod 2) B (Fin s.degree) (Fin s.words) s.Slot :=
  CellLayout.Binary.packing s.degree_gt s.basis 0 ⟨0,[]⟩

def packedIndex : Fin s.nPrivate ↪ (Fin s.words × Fin s.degree) :=
  CellLayout.primary (by have := s.degree_gt; omega) s.capacity

/-- Committed sources of the data leaves: shared bits, then mask bits. -/
def sources : Fin (shared+maskBits) → Fin s.nPrivate :=
  Fin.addCases s.sharedPrivate s.maskPrivate

/-- Per-proof virtual definitions in fragment order: tree-major, data leaves
then quotient leaves, each tree's target folded into its first leaf. -/
def entries (powers : Fin 2 → Fin (shared+maskBits) → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin adviceBits → Bool) (targets : Fin 2 → Bˣ) :
    Fin (2*(shared+maskBits+adviceBits)) → VirtualInput (Fin s.nPrivate) B := fun v =>
  match (Adapter.ProductTree.wireIndex _).symm v with
  | (tree,i) => Adapter.Leaves.tree s.sources (powers tree) (s.advicePrivate tree) base
      (masked tree) (targets tree) i

/-- The circuit and its pad plan are fixed; only the substituted virtual
definitions vary between proofs. -/
def setup (entries : Fin (2*(shared+maskBits+adviceBits)) → VirtualInput (Fin s.nPrivate) B) :
    FrontendVerifier.PackedSetup B (Fin s.degree) (Fin s.words) s.Slot s.Pad where
  out := s.upper
  input := s.input
  nPublic := s.nPublic
  nPrivate := s.nPrivate
  circuit := s.circuit
  packing := s.packing
  inputIndex := s.inputIndex
  packedIndex := s.packedIndex
  publicInputs := Adapter.Circuit.bitValue ∘ s.publicBits
  nVirtual := 2*(shared+maskBits+adviceBits)
  virtualIndex := s.virtualIndex
  virtualInputs := entries
  coordinate := CellLayout.Binary.pad s.words s.degree s.pads
  plan := s.padPlan

/-- Committed inputs only: the public prefix and the decoded private cells.
It is independent of all frontend messages and adapter values. -/
def committed (values : s.Slot → B) : Cube s.input → B :=
  s.packing.inputs s.inputIndex s.packedIndex (Adapter.Circuit.bitValue ∘ s.publicBits) values

/-- The complete input array, with the per-proof virtual suffix. -/
def inputs (entries : Fin (2*(shared+maskBits+adviceBits)) → VirtualInput (Fin s.nPrivate) B)
    (values : s.Slot → B) : Cube s.input → B :=
  s.packing.virtualInputs s.inputIndex s.virtualIndex s.packedIndex
    (Adapter.Circuit.bitValue ∘ s.publicBits) entries values

omit [Fintype B] [DecidableEq B] in
theorem committed_bit (values : s.Slot → B) (i : Cube s.input) :
    s.committed values i = 0 ∨ s.committed values i = 1 := by
  by_cases h : ∃ j, s.inputIndex j = i
  · obtain ⟨j,rfl⟩ := h
    cases j with
    | inl j =>
        simp only [committed, Packed.Statement.inputs, circuitInputs, zeroExtend_apply, Sum.elim_inl]
        cases s.publicBits j <;> simp [Adapter.Circuit.bitValue]
    | inr j =>
        simp only [committed, Packed.Statement.inputs, circuitInputs, zeroExtend_apply, Sum.elim_inr,
          Function.comp_id]
        exact s.packing.unpack_binary_bit s.packedIndex values j
  · have hz : s.committed values i = 0 := by
      unfold committed Packed.Statement.inputs circuitInputs
      apply zeroExtend_outside
      simpa only [not_exists] using h
    exact Or.inl hz

def bits (candidate : Candidate B s.Original) : Cube s.input → Bool :=
  fun i => decide (s.committed (FingerprintRows.realize (CellLayout.selected s.cells) candidate) i = 1)

omit [Fintype B] in
theorem committed_eq_bits (candidate : Candidate B s.Original) :
    s.committed (FingerprintRows.realize (CellLayout.selected s.cells) candidate) =
      Adapter.Circuit.bitValue ∘ s.bits candidate := by
  funext i
  have hi := s.committed_bit (FingerprintRows.realize (CellLayout.selected s.cells) candidate) i
  rcases hi with hi | hi <;> simp [bits, Adapter.Circuit.bitValue, hi]

/-- The committed private bits of a selected candidate. -/
def privateBits (candidate : Candidate B s.Original) : Fin s.nPrivate → Bool :=
  fun i => s.bits candidate (s.inputIndex (.inr i))

omit [Fintype B] in
theorem unpack_eq (candidate : Candidate B s.Original) :
    LfzkV2.Packed.unpack s.packing.basis s.packing.word s.packedIndex
        (FingerprintRows.realize (CellLayout.selected s.cells) candidate) =
      Adapter.Circuit.bitValue ∘ s.privateBits candidate := by
  funext i
  have h := congrFun (s.committed_eq_bits candidate) (s.inputIndex (.inr i))
  simp only [committed, Packed.Statement.inputs, circuitInputs, zeroExtend_apply, Sum.elim_inr,
    Function.comp_id] at h
  exact h

def sharedValues (candidate : Candidate B s.Original) : Fin shared → Bool :=
  fun i => s.privateBits candidate (s.sharedPrivate i)
def mask (candidate : Candidate B s.Original) : Fin maskBits → Bool :=
  fun i => s.privateBits candidate (s.maskPrivate i)
def quotient (masked : Fin 2 → Fin adviceBits → Bool) (candidate : Candidate B s.Original) : Fin 2 → ℕ :=
  fun tree => Adapter.Tree.binaryValue
    (List.ofFn fun i => Bool.xor (s.privateBits candidate (s.advicePrivate tree i)) (masked tree i))

omit [Fintype B] in
theorem values_eq (candidate : Candidate B s.Original) :
    s.privateBits candidate ∘ s.sources = Handoff.values (s.sharedValues candidate) (s.mask candidate) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [sources, sharedValues, mask, Handoff.values]

omit [Fintype B] in
/-- The fixed fragment's checks on the actual input array are the
conversion proof's product equations: each tree's virtual leaves have unit
product exactly when its product check holds for the decoded quotient. -/
theorem products [CharP B 2] {p : ℕ} [Fact p.Prime] (generator : Bˣ)
    (weights : Fin (shared+maskBits) → ZMod p) (target : ZMod p) (alpha : Fin 2 → ZMod p)
    (masked : Fin 2 → Fin adviceBits → Bool) (candidate : Candidate B s.Original)
    (h : s.circuit.Satisfies (s.inputs
      (s.entries (fun tree i => generator^(alpha tree*weights i).val) (generator^(-(p : ℤ))) masked
        (fun tree => generator^(alpha tree*target).val))
      (FingerprintRows.realize (CellLayout.selected s.cells) candidate))) (tree : Fin 2) :
    Adapter.ProductCheck generator weights (s.privateBits candidate ∘ s.sources) target (alpha tree)
      (s.quotient masked candidate tree) := by
  have hp := Adapter.Fragment.full_products s.layout s.output s.shape s.others s.carry s.above s.read _ h tree
  have hleaf (i : Fin (shared+maskBits+adviceBits)) :
      s.inputs (s.entries (fun tree i => generator^(alpha tree*weights i).val) (generator^(-(p : ℤ))) masked
          (fun tree => generator^(alpha tree*target).val))
        (FingerprintRows.realize (CellLayout.selected s.cells) candidate) (s.read (tree,i)) =
      (Adapter.Leaves.tree s.sources (fun j => generator^(alpha tree*weights j).val) (s.advicePrivate tree)
        (generator^(-(p : ℤ))) (masked tree) (generator^(alpha tree*target).val) i).value
          (Adapter.Circuit.bitValue ∘ s.privateBits candidate) := by
    simp only [inputs, read, Packed.Statement.virtualInputs]
    rw [virtualInputs_virtual _ _ s.virtualDisjoint, ← s.unpack_eq candidate]
    simp only [entries, Equiv.symm_apply_apply]
  simp only [hleaf] at hp
  exact (Adapter.Leaves.tree_product_check s.data_pos generator weights target (alpha tree) s.sources
    (s.advicePrivate tree) (masked tree) (s.privateBits candidate)).mp hp

end BinaryPublic

/-- Parsed prime messages and their boundary answers. All rows and the
split claim are computed from these values by the existing compiler; no
challenge after the prime frontend enters them. -/
structure PrimeData {p shared : ℕ} [Fact p.Prime] (n : PrimePublic (ZMod p) shared) (C : Type) where
  payload : Layered.Replay.Payload n.circuit
  decode : C → ℕ → ZMod p
  nonzero : C → Linear.TerminalSampling.Nonzero (ZMod p)
  answers : ℕ → C

namespace PrimeData
variable {p shared : ℕ} [Fact p.Prime] {n : PrimePublic (ZMod p) shared} (d : PrimeData n C)
def frontend := n.setup.prepare d.payload d.decode d.nonzero d.answers
def replay := n.setup.replay d.payload d.decode d.nonzero d.answers
def claim := Composition.splitClaim d.frontend (CellLayout.Prime.pad n.remaining n.pads)
end PrimeData

/-- Parsed binary messages and the adapter exchange. The payload is typed by
the fixed circuit; the conversion answers, `mu` and the masked words only
determine the substituted virtual definitions. -/
structure BinaryData {p shared maskBits adviceBits : ℕ} [Fact p.Prime]
    (s : BinaryPublic B shared maskBits adviceBits) {n : PrimePublic (ZMod p) shared}
    (prime : PrimeData n C) (generator : Bˣ) where
  eta : ZMod p
  mu : ZMod p
  alpha : Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p)
  masked : Fin 2 → Fin adviceBits → Bool
  payload : Layered.Replay.Payload s.circuit
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
def entries := s.entries d.powers (generator^(-(p : ℤ))) d.masked d.targets
def setup := s.setup d.entries
def frontend := d.setup.prepare d.payload d.decode d.nonzero d.answers d.U d.delta d.A
def replay := d.setup.replay d.payload d.decode d.nonzero d.answers d.U d.delta d.A
end BinaryData

/-- Trace is checked, while packing/compilation/replay, the cell layouts,
quotient range and the fixed fragment's semantics are all derived. Generator
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
      padCell := CellLayout.Prime.pad n.remaining n.pads
      pads_native := fun _ => rfl
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
            Bool.xor (s.privateBits w.1 (s.advicePrivate tree i)) (data.masked tree i)))
      trace := ht
      products := by
        intro w hs tree
        letI : CharP B 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) B).injective 2
        have hp := s.products generator (Handoff.weights prime.claim.sharedWeights data.eta) data.mu
          (fun tree => (data.alpha tree).val) data.masked w.1 hs tree
        simpa only [s.values_eq, PrimeData.claim] using hp }
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
