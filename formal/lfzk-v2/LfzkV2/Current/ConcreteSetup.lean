import LfzkV2.Current.StatementCompiler
import LfzkV2.Current.WireBlocks
import LfzkV2.Current.ConcreteAdapterTopology
import LfzkV2.Current.ApplicationSetup
import Mathlib.Data.Nat.Bitwise

/-! Public dimensions for the current rate-1/7 runtime. The trusted inputs
are arithmetic representations and circuit topology. Row counts, logical
coordinates, zero values and wire-format counts are computed here rather
than independently supplied to the verifier. -/
noncomputable section
namespace LfzkV2.Current.ConcreteSetup
open Application ApplicationSetup SumcheckV2
open scoped Classical
set_option maxRecDepth 2048

/-- The two selector masks follow the original frontend cells. Each data
row then has 84 random-prefix slots and 265 logical witness slots. -/
def rows (cells : ℕ) : ℕ := (cells+2+264)/265

theorem rows_capacity (cells : ℕ) : cells+2 ≤ rows cells*265 := by
  have h := Nat.mod_add_div (cells+2+264) 265
  have hm := Nat.mod_lt (cells+2+264) (by decide : 0<265)
  dsimp [rows]
  omega

/-- Prefix masks, logical cells and oracle columns occupy consecutive
positions, in precisely that order. -/
def positionIndex : LigeroFamily.Position 84 265 2443 ≃ Fin 2792 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

@[simp] theorem random_position (i : Fin 84) :
    (positionIndex (LigeroFamily.randomPosition i)).val = i.val := rfl

@[simp] theorem witness_position (i : Fin 265) :
    (positionIndex (LigeroFamily.witnessPosition i)).val = 84+i.val := rfl

@[simp] theorem oracle_position (i : Fin 2443) :
    (positionIndex (LigeroFamily.codePosition i)).val = 349+i.val := rfl

/-- The FFT used for prime interpolation is an implementation detail: its
evaluation points are the integers 0, 1, 2, ... in the prime field. -/
def primeNodes : Fin 2792 ↪ ZMod Adapter.Mdoc.primeOrder where
  toFun i := i.val
  inj' := by
    intro i j h
    apply Fin.ext
    have hi : i.val < Adapter.Mdoc.primeOrder := lt_of_lt_of_le i.isLt (by decide)
    have hj : j.val < Adapter.Mdoc.primeOrder := lt_of_lt_of_le j.isLt (by decide)
    have hval := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hi,ZMod.val_natCast_of_lt hj] using hval

/-- The field representation supplies its fixed Cantor basis. Index bits
select basis vectors, just as `BinaryInterpolatorFactory::point` does.
Injectivity follows from the basis laws, without a domain certificate. -/
def binaryNodes {B : Type} [Field B] [Algebra (ZMod 2) B]
    (cantor : Module.Basis (Fin 128) (ZMod 2) B) : Fin 2792 ↪ B where
  toFun value := cantor.equivFun.symm fun i => if value.val.testBit i.val then 1 else 0
  inj' := by
    intro left right h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 128
    · have hv := congrFun (congrArg cantor.equivFun h) ⟨i,hi⟩
      simp only [LinearEquiv.apply_symm_apply] at hv
      cases hl : left.val.testBit i <;> cases hr : right.val.testBit i <;>
        simp_all
    · have hpow : 2792 ≤ 2^i := le_trans (by decide : 2792 ≤ 2^128)
        (Nat.pow_le_pow_right (by decide) (by omega : 128 ≤ i))
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le left.isLt hpow),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le right.isLt hpow)]

@[simp] theorem binaryNodes_zero {B : Type} [Field B] [Algebra (ZMod 2) B]
    (cantor : Module.Basis (Fin 128) (ZMod 2) B) : binaryNodes cantor 0 = 0 := by
  simp [binaryNodes]

/-- Ordered evaluation nodes are supplied by the field implementation.
This is the arithmetic interface: binary nodes use the Cantor basis and
prime nodes are the successive natural numbers. It is not a choice of
logical row layout or of a protocol constraint system. -/
def backend {F : Type} [Field F] (nodes : Fin 2792 ↪ F) (cells : ℕ) :
    FieldBackend F 349 12 2443 84 where
  backend := {
    q := 265
    r := 84
    w := 265
    n := 2443
    nw := rows cells
    nq := 0
    s := 12
    t := 84
    Equations := Fin 0
    equationsFinite := inferInstance
    equationsDecidable := inferInstance
    domain := ⟨nodes ∘ positionIndex,nodes.injective.comp positionIndex.injective⟩
    layout := LigeroFamily.ConstraintLayout.identity 265
    primary_le := by decide
    query_le := by decide }
  dimension := rfl
  batching := rfl
  columns := rfl
  openings := rfl
  linearOnly := rfl

@[simp] theorem backend_logical {F : Type} [Field F]
    (nodes : Fin 2792 ↪ F) (cells : ℕ) (i : Fin 265) :
    (backend nodes cells).backend.layout.logical i = i := rfl

variable {B : Type} [Field B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)

/-- Frontend role lists are derived from the trusted topology's plans;
the remaining geometry is the current profile and actual committed cells. -/
def geometry (binaryFrontend primeFrontend : Frontend) : Geometry where
  binary := binaryFrontend
  prime := primeFrontend
  binaryCells := binary.cells
  primeCells := CellLayout.Prime.cells prime.remaining prime.pads
  packingDegree := binary.degree
  packingPositive := by have := binary.degree_gt; omega
  rowDimension := 349
  maskingDegree := 12
  columns := 2443
  openings := 84
  openingsPositive := by decide
  openings_lt := by decide
  openings_le := by decide
  responseFits := by decide
  productFits := by decide

@[simp] theorem geometry_binaryRows (binaryFrontend primeFrontend : Frontend) :
    (geometry binary prime binaryFrontend primeFrontend).dataRows .binary = rows binary.cells := by
  simp only [Geometry.dataRows,geometry,Geometry.cells,rows]
  norm_num

@[simp] theorem geometry_primeRows (binaryFrontend primeFrontend : Frontend) :
    (geometry binary prime binaryFrontend primeFrontend).dataRows .prime =
      rows (CellLayout.Prime.cells prime.remaining prime.pads) := by
  simp only [Geometry.dataRows,geometry,Geometry.cells,rows]
  norm_num

/-- Only ordinary machine-size bounds remain: these are public allocation
limits. Packing writes its input and auxiliary cell counts with the runtime's
eight-byte count framing, while its derived coefficients stay local. -/
def shape {fields : Fields} (binaryFrontend primeFrontend : Frontend)
    (binaryField : fields .binary ≃ B)
    (primeField : fields .prime ≃ ZMod Adapter.Mdoc.primeOrder)
    (inputFits : shared+prime.remaining+prime.pads < 2^64)
    (sharedFits : shared+1 < 2^64)
    (privateFits : binary.nPrivate < 2^64)
    (degreeFits : binary.degree < 2^64) :
    WireBlocks.Shape (geometry binary prime binaryFrontend primeFrontend) fields where
  binaryPublic := binary.nPublic
  primePublic := prime.nPublic
  primeInputs := shared+prime.remaining+prime.pads
  sharedBits := shared
  packingInputs := binary.nPrivate
  binary128Packing := true
  zero := fun side => match side with
    | .binary => binaryField.symm 0
    | .prime => primeField.symm 0
  sliceFits := by
    intro count h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact inputFits
    · exact sharedFits
    · exact privateFits
    · exact degreeFits
    · exact (by decide : 349+12 < 2^64)
    · exact (by decide : 2*349 < 2^64)

/-- Public capacity validation succeeds for the constructed backend. The
returned coordinates are the quotient/remainder map used by the runtime. -/
def addresses (binaryNodes : Fin 2792 ↪ B)
    (primeNodes : Fin 2792 ↪ ZMod Adapter.Mdoc.primeOrder) :
    StatementCompiler.Addresses (backend binaryNodes binary.cells)
      (backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
      binary.cells prime.remaining prime.pads where
  binary := CellLayout.primary (by decide : 0<265) (rows_capacity binary.cells)
  prime := (CellLayout.Prime.index prime.remaining prime.pads).toEmbedding.trans
    (CellLayout.primary (by decide : 0<265)
      (rows_capacity (CellLayout.Prime.cells prime.remaining prime.pads)))

theorem addresses_eq (binaryNodes : Fin 2792 ↪ B)
    (primeNodes : Fin 2792 ↪ ZMod Adapter.Mdoc.primeOrder) :
    StatementCompiler.addresses (backend binaryNodes binary.cells)
      (backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
      binary.cells prime.remaining prime.pads = some (addresses binary prime binaryNodes primeNodes) := by
  unfold StatementCompiler.addresses
  rw [dif_pos]
  · rfl
  · exact ⟨(by decide : 0<265),rows_capacity binary.cells,(by decide : 0<265),
      rows_capacity (CellLayout.Prime.cells prime.remaining prime.pads)⟩

end LfzkV2.Current.ConcreteSetup

namespace LfzkV2.Current.ConcreteSetup
open ApplicationSetup SumcheckV2
open scoped Classical

/-- Dense arrays use the first cube coordinate as the least significant
bit. The sumcheck even/odd split therefore reads consecutive array pairs. -/
def cubeIndex : (n : ℕ) → Cube n ≃ Fin (2^n)
  | 0 => {
      toFun := fun _ => 0
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun i => by
        apply Fin.ext
        have h := i.isLt
        change i.val < 1 at h
        change 0 = i.val
        omega }
  | n+1 => ((Equiv.prodComm Bool (Cube n)).trans
      ((Equiv.prodCongr (cubeIndex n) finTwoEquiv.symm).trans finProdFinEquiv)).trans
        (finCongr (by rw [pow_succ]))

/-- Public cells precede private cells in the unpadded input array. Only
the final embedding adds the usual power-of-two cube padding. -/
def inputIndex (publicCount privateCount input : ℕ)
    (capacity : publicCount+privateCount ≤ 2^input) :
    (Fin publicCount ⊕ Fin privateCount) ↪ Cube input :=
  finSumFinEquiv.toEmbedding.trans
    ((⟨Fin.castLE capacity,Fin.castLE_injective capacity⟩ :
      Fin (publicCount+privateCount) ↪ Fin (2^input)).trans (cubeIndex input).symm.toEmbedding)

@[simp] theorem inputIndex_public (publicCount privateCount input : ℕ)
    (capacity : publicCount+privateCount ≤ 2^input) (i : Fin publicCount) :
    (cubeIndex input (inputIndex publicCount privateCount input capacity (.inl i))).val = i.val := by
  simp [inputIndex]

@[simp] theorem inputIndex_private (publicCount privateCount input : ℕ)
    (capacity : publicCount+privateCount ≤ 2^input) (i : Fin privateCount) :
    (cubeIndex input (inputIndex publicCount privateCount input capacity (.inr i))).val = publicCount+i.val := by
  simp [inputIndex]

/-- A component's natural input prefix of the shared input array. -/
def prefixIndex (width input : ℕ) (capacity : width ≤ 2^input) : Fin width ↪ Cube input :=
  (⟨Fin.castLE capacity,Fin.castLE_injective capacity⟩ : Fin width ↪ Fin (2^input)).trans
    (cubeIndex input).symm.toEmbedding

@[simp] theorem prefixIndex_val (width input : ℕ) (capacity : width ≤ 2^input) (i : Fin width) :
    (cubeIndex input (prefixIndex width input capacity i)).val = i.val := by
  simp [prefixIndex]

/-- Consecutive entries of the shared input array from `start`. -/
def rangeIndex (start count input : ℕ) (capacity : start+count ≤ 2^input) : Fin count ↪ Cube input where
  toFun v := (cubeIndex input).symm ⟨start+v.val,by have := v.isLt; omega⟩
  inj' := by
    intro v w h
    have hv := congrArg (fun u => (cubeIndex input u).val) h
    simp only [Equiv.apply_symm_apply] at hv
    exact Fin.ext (by omega)

@[simp] theorem rangeIndex_val (start count input : ℕ) (capacity : start+count ≤ 2^input) (v : Fin count) :
    (cubeIndex input (rangeIndex start count input capacity v)).val = start+v.val := by
  simp [rangeIndex]

/-- The trusted signature circuit includes its sparse component topology.
The algebraic circuit and its transcript plan are both constructed from it. -/
structure PrimeCircuit where
  out : ℕ
  input : ℕ
  nPublic : ℕ
  remaining : ℕ
  topology : ConcreteTopology.Circuit (ZMod Adapter.Mdoc.primeOrder) out input
  inputCapacity : nPublic+(768+remaining) ≤ 2^input
  publicInputs : Fin nPublic → ZMod Adapter.Mdoc.primeOrder

namespace PrimeCircuit
def description (circuit : PrimeCircuit) : PrimePublic (ZMod Adapter.Mdoc.primeOrder) 768 where
  out := circuit.out
  input := circuit.input
  nPublic := circuit.nPublic
  remaining := circuit.remaining
  circuit := (circuit.topology.withComponent 0).algebraic
  inputIndex := inputIndex circuit.nPublic (768+circuit.remaining) circuit.input circuit.inputCapacity
  publicInputs := circuit.publicInputs

def plan (circuit : PrimeCircuit) : FrontendSchedule.Plan (ZMod Adapter.Mdoc.primeOrder) circuit.description.circuit :=
  (circuit.topology.withComponent 0).plan
end PrimeCircuit

/-- The trusted hash circuit, archived at its natural width, beside the fixed
adapter fragment. The shared input array is

`[public | hash private | R | O_0 | O_1 | virtual leaves]`.

The hash's own input width is `nPublic+hashPrivate`; its input-boundary
fragments are typed by that prefix, so it cannot read R (256 bits), the two
ten-bit quotient pads or the 2*1034 virtual leaves. Packing commits exactly the
`hashPrivate+276` committed private inputs in degree-128 words. -/
structure BinaryCircuit (B : Type) [Field B] [Algebra (ZMod 2) B] where
  input : ℕ
  nPublic : ℕ
  hashPrivate : ℕ
  final : ℕ
  out : ℕ
  upper : ℕ
  basis : Module.Basis (Fin 128) (ZMod 2) B
  inputCapacity : nPublic+(hashPrivate+276)+2*(768+256+10) ≤ 2^input
  hashCapacity : 21272 ≤ hashPrivate
  publicBits : Fin nPublic → Bool
  layout : Adapter.Fragment.Layout
  output : Fin 2 ↪ Cube final
  others : ConcreteAdapterTopology.Others layout (768+256+10) (nPublic+hashPrivate) input final
    (prefixIndex (nPublic+hashPrivate) input (le_trans (by omega) inputCapacity)) output B
  carry : Cube out → Option (ConcreteAdapterTopology.Avoid output)
  above : ConcreteAdapterTopology.Above B upper out

namespace BinaryCircuit
variable {B : Type} [Field B] [Algebra (ZMod 2) B]

/-- Committed private inputs: the hash's, then R and the two pads. -/
def nPrivate (circuit : BinaryCircuit B) : ℕ := circuit.hashPrivate+276

/-- The hash's natural input width. -/
def hashWidth (circuit : BinaryCircuit B) : ℕ := circuit.nPublic+circuit.hashPrivate

theorem committedCapacity (circuit : BinaryCircuit B) :
    circuit.nPublic+circuit.nPrivate ≤ 2^circuit.input :=
  le_trans (by unfold nPrivate; omega) circuit.inputCapacity

theorem virtualCapacity (circuit : BinaryCircuit B) :
    circuit.nPublic+circuit.nPrivate+2*(768+256+10) ≤ 2^circuit.input :=
  le_trans (by unfold nPrivate; omega) circuit.inputCapacity

/-- The hash's input prefix in the shared array. -/
def hashIndex (circuit : BinaryCircuit B) : Fin circuit.hashWidth ↪ Cube circuit.input :=
  prefixIndex (circuit.nPublic+circuit.hashPrivate) circuit.input
    (le_trans (by omega) circuit.inputCapacity)

@[simp] theorem hashIndex_val (circuit : BinaryCircuit B) (x : Fin circuit.hashWidth) :
    (cubeIndex circuit.input (circuit.hashIndex x)).val = x.val :=
  prefixIndex_val _ _ _ x

/-- Hash allocation stores the issuer digest first. Device coordinates
follow 40 SHA blocks, the 16-bit MSO length and the 8-bit block count. -/
def sharedPrivate (circuit : BinaryCircuit B) (i : Fin 768) : Fin circuit.nPrivate :=
  ⟨if i.val < 256 then i.val else 20760+(i.val-256),by
    have hi := i.isLt
    have hc := circuit.hashCapacity
    unfold nPrivate
    split_ifs <;> omega⟩

/-- R follows the hash's own private inputs. -/
def maskPrivate (circuit : BinaryCircuit B) (i : Fin 256) : Fin circuit.nPrivate :=
  ⟨circuit.hashPrivate+i.val,by have := i.isLt; unfold nPrivate; omega⟩

/-- The two independent ten-bit quotient pads follow R. -/
def advicePrivate (circuit : BinaryCircuit B) (tree : Fin 2) (i : Fin 10) : Fin circuit.nPrivate :=
  ⟨circuit.hashPrivate+256+10*tree.val+i.val,by
    have := tree.isLt
    have := i.isLt
    unfold nPrivate
    omega⟩

/-- Shared data lies inside the hash's own inputs. -/
theorem shared_lt_hash (circuit : BinaryCircuit B) (i : Fin 768) :
    (circuit.sharedPrivate i).val < circuit.hashPrivate := by
  have := i.isLt
  have := circuit.hashCapacity
  simp only [sharedPrivate]
  split_ifs <;> omega

def committedIndex (circuit : BinaryCircuit B) : (Fin circuit.nPublic ⊕ Fin circuit.nPrivate) ↪ Cube circuit.input :=
  inputIndex circuit.nPublic circuit.nPrivate circuit.input circuit.committedCapacity

/-- The virtual suffix follows every committed input. -/
def virtualIndex (circuit : BinaryCircuit B) : Fin (2*(768+256+10)) ↪ Cube circuit.input :=
  rangeIndex (circuit.nPublic+circuit.nPrivate) (2*(768+256+10)) circuit.input circuit.virtualCapacity

theorem virtualDisjoint (circuit : BinaryCircuit B) (j : Fin circuit.nPublic ⊕ Fin circuit.nPrivate)
    (v : Fin (2*(768+256+10))) : circuit.committedIndex j ≠ circuit.virtualIndex v := by
  intro h
  have hv := congrArg (fun u => (cubeIndex circuit.input u).val) h
  simp only [committedIndex,virtualIndex,rangeIndex_val] at hv
  cases j with
  | inl j => rw [inputIndex_public] at hv; have := j.isLt; omega
  | inr j => rw [inputIndex_private] at hv; have := j.isLt; omega

def description (circuit : BinaryCircuit B) : BinaryPublic B 768 256 10 where
  input := circuit.input
  nPublic := circuit.nPublic
  nPrivate := circuit.nPrivate
  words := (circuit.nPrivate+127)/128
  degree := 128
  final := circuit.final
  out := circuit.out
  upper := circuit.upper
  degree_gt := by decide
  basis := circuit.basis
  capacity := by
    have h := Nat.mod_add_div (circuit.nPrivate+127) 128
    have hm := Nat.mod_lt (circuit.nPrivate+127) (by decide : 0<128)
    omega
  inputIndex := circuit.committedIndex
  virtualIndex := circuit.virtualIndex
  virtualDisjoint := circuit.virtualDisjoint
  publicBits := circuit.publicBits
  sharedPrivate := circuit.sharedPrivate
  maskPrivate := circuit.maskPrivate
  advicePrivate := circuit.advicePrivate
  data_pos := by decide
  leaves_gt := by decide
  layout := circuit.layout
  output := circuit.output
  others := (circuit.others.withComponent 0).algebraic
  carry := ConcreteAdapterTopology.carryWires circuit.carry
  above := (circuit.above.withComponent 0).algebraic

/-- No annotation or protocol-equivalence hypothesis is supplied: this
plan follows the same constructors that build the fixed binary circuit. -/
def plan (circuit : BinaryCircuit B) : FrontendSchedule.Plan B circuit.description.circuit :=
  (circuit.above.withComponent 0).plan _
    (ConcreteAdapterTopology.buildPlan circuit.description.shape (circuit.others.withComponent 0)
      circuit.carry circuit.description.read)

end BinaryCircuit
end LfzkV2.Current.ConcreteSetup
