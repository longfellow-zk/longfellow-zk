import LfzkV2.Current.Composition
import LfzkV2.Current.BackendSelection
import LfzkV2.Current.FrontendFailures
import LfzkV2.Current.AdapterTree

/-! The application boundary of the current protocol.  A selected pair fixes
all private cells, including the pads.  The prime circuit sees the shared
bits unpacked by the binary participant; its backend authenticates only the
rescaled handoff row.  This module reduces those actual rows to circuit truth
or the explicit algebraic events, and locates circuit events at current
transcript boundaries. -/
noncomputable section
namespace LfzkV2.Current.Application
open SumcheckV2 DualPacking.ArtinSchreier WitnessSelection

variable {F Pad C : Type} [Field F]

/-- A replay identity is a correspondence with the messages parsed from the
accepted proof.  It asserts no soundness property. -/
structure Replay {out input : ℕ} (circuit : Layered.Circuit F out input)
    (messages : Layered.Circuit.Messages Pad circuit) (C : Type) where
  decode : C → ℕ → F
  nonzero : C → Linear.TerminalSampling.Nonzero F
  plan : Layered.Replay.PadPlan (Pad := Pad) circuit
  payload : Layered.Replay.Payload circuit
  answers : ℕ → C
  agrees : messages = FrontendReplay.read decode nonzero circuit plan payload answers

namespace Replay
variable {out input : ℕ} {circuit : Layered.Circuit F out input}
  {messages : Layered.Circuit.Messages Pad circuit}

def BadAt (r : Replay circuit messages C) (w : Cube input → F) (pads : Pad → F)
    (query : ℕ) : Prop :=
  FrontendReplay.BadAt r.decode r.nonzero circuit r.plan r.payload r.answers w pads query

/-- A compiler-produced circuit failure is located at an actual boundary,
without an assumed accepted-failure cover. -/
theorem bad_cover (r : Replay circuit messages C) (w : Cube input → F) (pads : Pad → F)
    (hbad : Layered.Circuit.Bad circuit messages w 0 pads 0) :
    ∃ query < FrontendReplay.slots circuit, r.BadAt w pads query := by
  rw [r.agrees] at hbad
  obtain ⟨role,hr⟩ := FrontendReplay.bad_at_role r.decode r.nonzero circuit r.plan
    r.payload r.answers 0 0 w 0 pads 0 hbad
  exact ⟨FrontendReplay.queryIndex circuit role 0,
    by simpa using FrontendReplay.queryIndex_lt circuit role 0, role,rfl,hr⟩

end Replay

/-- A generated adapter need only establish its final product-tree
assertions.  The bounded quotients and both conversion equations follow
from the tree algebra, even for advice chosen after the challenges. -/
theorem adapter_products_of_roots {B : Type} [Field B] [CharP B 2]
    {p bits adviceBits K : ℕ} [Fact p.Prime]
    (generator : Bˣ) (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target : ZMod p) (alpha : Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p))
    (pad masked : Fin 2 → Fin adviceBits → Bool) (steps : ℕ)
    (hbound : 2^adviceBits ≤ K)
    (hroots : ∀ j,
      let advice := List.ofFn (fun i => Bool.xor (pad j i) (masked j i))
      let data := List.ofFn (fun i => if values i then generator^((alpha j).val * weights i).val else 1)
      let quotient := Adapter.Tree.quotientLeaves (generator^(-(p : ℤ))) advice
      ((Adapter.Tree.reduce steps data).prod : B) *
        ((Adapter.Tree.reduce steps quotient).prod : B) +
        ((generator^((alpha j).val * target).val : Bˣ) : B) = 0) :
    ∃ quotient : Fin 2 → ℕ, (∀ j, quotient j < K) ∧
      ∀ j, Adapter.ProductCheck generator weights values target (alpha j).val (quotient j) := by
  let quotient := fun j => Adapter.Tree.binaryValue
    (List.ofFn (fun i => Bool.xor (pad j i) (masked j i)))
  have h := fun j => Adapter.Tree.product_check generator weights values target (alpha j).val
    (pad j) (masked j) steps (hroots j)
  exact ⟨quotient, fun j => lt_of_lt_of_le (h j).1 hbound, fun j => (h j).2⟩

variable {B I J SlotB PadB Other PadN IB IN CB CN : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
  [Fintype I] [DecidableEq I] [Fintype J] [Fintype Other]
  [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN]
variable {p shared maskBits M K : ℕ} [Fact p.Prime]

/-- Public layouts, parsed messages and the actual frontend challenges.  The
only circuit-specific semantic premise is that the generated binary adapter
assertions imply its product equations.  It relates concrete circuit
semantics to concrete equations, rather than postulating a failure cover. -/
structure System (B I J SlotB PadB Other PadN IB IN CB CN : Type)
    [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype Other]
    [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN]
    (p shared maskBits M K : ℕ) [Fact p.Prime] where
  binary : Frontend.Packed B I J SlotB PadB
  prime : Frontend.Prime (ZMod p) (Fin shared ⊕ Other) PadN
  binaryReplay : Replay binary.circuit binary.messages CB
  primeReplay : Replay prime.circuit prime.messages CN
  binaryLayout : (IB ⊕ Fin 2) ≃ SlotB
  primeLayout : (IN ⊕ Fin 2) ≃ (Other ⊕ Unit)
  sharedValues : Candidate B IB → Fin shared → Bool
  mask : Candidate B IB → Fin maskBits → Bool
  rho : Fin prime.rows.length → ZMod p
  eta : ZMod p
  mu : ZMod p
  alpha : Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p)
  generator : Bˣ
  order : orderOf generator = M
  quotient : Selection.Pair B (ZMod p) IB IN → Fin 2 → ℕ
  quotient_lt : ∀ w j, quotient w j < K
  trace : ∀ k, traceF (ZMod 2) (binary.U k) = 0
  products : ∀ w : Selection.Pair B (ZMod p) IB IN,
    binary.circuit.Satisfies (binary.inputs (FingerprintRows.realize binaryLayout w.1)) →
    ∀ j, Adapter.ProductCheck generator
      (Handoff.weights (Prime.Claim.fromRow (Prime.batchRows prime.rows.get rho)).sharedWeights eta)
      (Handoff.values (sharedValues w.1) (mask w.1)) mu (alpha j).val (quotient w j)

namespace System
variable (A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K)

abbrev Pair (_A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K) :=
  Selection.Pair B (ZMod p) IB IN

def binaryRead (w : A.Pair) : SlotB → B := FingerprintRows.realize A.binaryLayout w.1
def primeRead (w : A.Pair) : Other ⊕ Unit → ZMod p :=
  FingerprintRows.realize A.primeLayout w.2
def other (w : A.Pair) : Other → ZMod p := fun i => A.primeRead w (.inl i)
def primeMask (w : A.Pair) : ZMod p := A.primeRead w (.inr ())
def fullPrimeRead (w : A.Pair) : Fin shared ⊕ Other → ZMod p :=
  Sum.elim (fun i => if A.sharedValues w.1 i then 1 else 0) (A.other w)
def claim : Prime.Claim (Fin shared) Other (ZMod p) :=
  Prime.Claim.fromRow (Prime.batchRows A.prime.rows.get A.rho)
def primeRows : List (LinearRow (Other ⊕ Unit) (ZMod p)) := [A.claim.row A.eta A.mu]

def True (w : A.Pair) : Prop :=
  A.binary.circuit.Satisfies (A.binary.inputs (A.binaryRead w)) ∧
    A.prime.circuit.Satisfies (A.prime.inputs (A.fullPrimeRead w))

/-- Each alternative is a concrete local algebraic event.  Circuit failures
carry the current query index; the remaining events retain their own
packing, prime-batching, rescaling, or conversion challenge block. -/
def Bad (w : A.Pair) : Prop :=
  (∃ query < FrontendReplay.slots A.binary.circuit,
    A.binaryReplay.BadAt (A.binary.inputs (A.binaryRead w))
      (A.binaryRead w ∘ A.binary.coordinate) query) ∨
  A.binary.source.Bad (A.binaryRead w) A.binary.U A.binary.delta ∨
  (∃ query < FrontendReplay.slots A.prime.circuit,
    A.primeReplay.BadAt (A.prime.inputs (A.fullPrimeRead w))
      (A.fullPrimeRead w ∘ A.prime.coordinate) query) ∨
  Prime.BatchBad (fun i => (A.prime.rows.get i).eval (A.fullPrimeRead w)) A.rho ∨
  Prime.RescalingBad
    (A.claim.residual (fun i => if A.sharedValues w.1 i then 1 else 0) (A.other w))
    (Handoff.binaryMask (A.mask w.1) - A.primeMask w) A.eta ∨
  Handoff.ConversionBad A.claim.sharedWeights A.eta A.mu
    (A.sharedValues w.1) (A.mask w.1) M K A.alpha

theorem primeRead_eq (w : A.Pair) :
    A.primeRead w = Sum.elim (A.other w) (fun _ => A.primeMask w) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i; rfl

/-- Authentication of the actual binary compiled rows and the singleton
prime handoff row suffices for the complete algebraic application reduction.
In particular, equality of the two independently committed hiding masks is
not an assumption. -/
theorem rows_reduction (w : A.Pair)
    (hbinary : RowsHold A.binary.rows (A.binaryRead w))
    (hprime : RowsHold A.primeRows (A.primeRead w)) : A.True w ∨ A.Bad w := by
  have hrow : (A.claim.row A.eta A.mu).eval
      (Sum.elim (A.other w) (fun _ => A.primeMask w)) = 0 := by
    rw [← A.primeRead_eq w]
    exact hprime _ (by simp [primeRows])
  rcases Composition.rows_reduction A.binary A.prime (A.binaryRead w) (A.other w)
    (A.sharedValues w.1) (A.mask w.1) A.rho A.eta A.mu (A.primeMask w) A.alpha
    A.generator A.order (A.quotient w) (A.quotient_lt w) A.trace hbinary
    (A.products w) hrow with htrue | hb | hn | hbatch | hscale | hconversion
  · exact Or.inl htrue
  · rcases hb with hc | hp
    · exact Or.inr (Or.inl (A.binaryReplay.bad_cover _ _ hc))
    · exact Or.inr (Or.inr (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (A.primeReplay.bad_cover _ _ hn))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbatch))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hscale)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hconversion)))))

end System
end LfzkV2.Current.Application
