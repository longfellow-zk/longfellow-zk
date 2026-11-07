import LfzkV2.Current.ZeroKnowledge.MerklePreparationLabels
import LfzkV2.Current.ZeroKnowledge.MerkleCacheBackend

/-! Two causal preparation bridges around joint backend/Merkle hiding.
Logical frontend cells are fixed before commitment. Public frontend messages,
affine rows and batching coins may depend on the honest heap labels. The
backend change of masks keeps those labels and the earlier public state fixed.
The simulator commits zero logical cells and uses the public affine correction.

This is the compiled backend law at a fixed shared opening set. Programming
the complete opening-oracle answer and simulating frontend messages are the
neighboring composition steps. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendCompiled

open Merkle Merkle.MH Merkle.RandomOracle LigeroFamily RecursivePolygero.Local
open scoped Classical
set_option maxHeartbeats 1000000

variable {B N : Type} [Field B] [Field N] [Fintype B] [Fintype N]
variable {r w n bw nw s : ℕ}
variable (binary : PolygeroZk.Geometry B r w 0 n) (prime : PolygeroZk.Geometry N r w 0 n)
variable {BE NE : Type} [Fintype BE] [Fintype NE]
variable {Index Nonce D Enc FrontCoin Request Front Observed : Type}
variable [Fintype Nonce] [Nonempty Nonce] [DecidableEq Nonce]
variable [Fintype D] [DecidableEq D] [Inhabited D]
variable [Fintype Enc] [DecidableEq Enc] [DecidableEq Observed] [Fintype FrontCoin]

abbrev Leaf := MerkleBackend.Leaf (B := B) (N := N) (bw := bw) (nw := nw)
abbrev Masks := MerkleBackend.MaskTape binary prime (bw := bw) (nw := nw) (s := s)
abbrev Responses := MerkleBackend.Responses (B := B) (N := N) (r := r) (w := w) (s := s)
abbrev Labels (n : ℕ) (D : Type) := Fin (2*n-1) → D

variable (C : Codec (Index × Nonce) (Leaf (B := B) (N := N) (bw := bw) (nw := nw)) D Enc)
variable {priorQueries : ℕ} (before : Tree Enc D Request priorQueries)
variable (queries : ℕ) (Q : QuerySet n r) (pivot : Fin w) (index : Fin n → Index)
variable (cells : FrontCoin → Request → Backend.Cells B bw w × Backend.Cells N nw w)
variable (front : FrontCoin → Request → Labels n D → Front)
variable (statements : FrontCoin → Request → Labels n D →
  ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
variable (batching : FrontCoin → Request → Labels n D →
  Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
variable (observer : Request → (Front × Responses (B := B) (N := N) (r := r) (w := w) (s := s)) →
  ({i : Fin n // i ∈ Q.coordinates} → Leaf (B := B) (N := N) (bw := bw) (nw := nw)) →
  Labels n D → OpeningView n Q.coordinates Nonce D → Tree Enc D Observed queries)

def realMessages (a : FrontCoin) (mask : Masks binary prime (bw := bw) (nw := nw) (s := s))
    (request : Request) (i : Fin n) : Index × Leaf (B := B) (N := N) (bw := bw) (nw := nw) :=
  (index i,MerkleBackend.realColumns binary prime (cells a request) mask i)

def simMessages (mask : Masks binary prime (bw := bw) (nw := nw) (s := s))
    (_request : Request) (i : Fin n) : Index × Leaf (B := B) (N := N) (bw := bw) (nw := nw) :=
  (index i,MerkleBackend.simColumns binary prime mask i)

def runView (request : Request) (columns : Fin n → Leaf (B := B) (N := N) (bw := bw) (nw := nw))
    (publicView : Front × Responses (B := B) (N := N) (r := r) (w := w) (s := s))
    (nonce : Fin n → Nonce) (H : Enc → D) (labels : Labels n D) : Observed :=
  let values := ((commitPass (MerkleSimulation.nonceCodec C) n nonce
    (fun i => (index i,columns i)) (2*n-1) (fun _ => default)).run H).1
  let opening : OpeningView n Q.coordinates Nonce D :=
    ⟨values 1,{ nonce := fun i => nonce i.val,frontierValue := fun vertex => values vertex.val }⟩
  ((observer request publicView (fun i => columns i.val) labels opening).run H).1

def realObserve (a : FrontCoin) (mask : Masks binary prime (bw := bw) (nw := nw) (s := s))
    (nonce : Fin n → Nonce) (request : Request) (H : Enc → D) (labels : Labels n D) : Observed :=
  runView C queries Q index observer request
    (MerkleBackend.realColumns binary prime (cells a request) mask)
    (front a request labels,MerkleBackend.realResponses binary prime Q (cells a request)
      (statements a request labels) (batching a request labels) mask) nonce H labels

def simObserve (a : FrontCoin) (mask : Masks binary prime (bw := bw) (nw := nw) (s := s))
    (nonce : Fin n → Nonce) (request : Request) (H : Enc → D) (labels : Labels n D) : Observed :=
  runView C queries Q index observer request
    (MerkleBackend.simColumns binary prime mask)
    (front a request labels,MerkleBackend.simResponses binary prime Q pivot
      (statements a request labels) (batching a request labels) mask) nonce H labels

abbrev Outer := FrontCoin × Masks binary prime (bw := bw) (nw := nw) (s := s)
abbrev Coins := Outer (FrontCoin := FrontCoin) binary prime (bw := bw) (nw := nw) (s := s) ×
  MerklePreparation.Coins (Salt := Nonce) (Enc := Enc) (Digest := D) n

def real (coin : Coins (FrontCoin := FrontCoin) (Nonce := Nonce) (Enc := Enc) (D := D)
    binary prime (bw := bw) (nw := nw) (s := s)) : Observed :=
  realObserve binary prime C queries Q index cells front statements batching observer
    coin.1.1 coin.1.2 coin.2.2.1 (before.run coin.2.1).1 coin.2.1
    (MerklePreparation.honestLabels (MerkleSimulation.nonceCodec C) n before
      (realMessages binary prime index cells coin.1.1 coin.1.2) coin.2.2.1 coin.2.1)

def simulate (coin : Coins (FrontCoin := FrontCoin) (Nonce := Nonce) (Enc := Enc) (D := D)
    binary prime (bw := bw) (nw := nw) (s := s)) : Observed :=
  simObserve binary prime C queries Q pivot index front statements batching observer
    coin.1.1 coin.1.2 coin.2.2.1 (before.run coin.2.1).1 coin.2.1
    (MerklePreparation.honestLabels (MerkleSimulation.nonceCodec C) n before
      (simMessages binary prime index coin.1.2) coin.2.2.1 coin.2.1)

def preparedReal (coin : Coins (FrontCoin := FrontCoin) (Nonce := Nonce) (Enc := Enc) (D := D)
    binary prime (bw := bw) (nw := nw) (s := s)) : Observed :=
  MerklePreparation.labelledPrepared (MerkleSimulation.nonceCodec C) n before
    (realMessages binary prime index cells coin.1.1 coin.1.2) coin.2.1
    (realObserve binary prime C queries Q index cells front statements batching observer coin.1.1 coin.1.2) coin.2.2

def preparedSim (coin : Coins (FrontCoin := FrontCoin) (Nonce := Nonce) (Enc := Enc) (D := D)
    binary prime (bw := bw) (nw := nw) (s := s)) : Observed :=
  MerklePreparation.labelledPrepared (MerkleSimulation.nonceCodec C) n before
    (simMessages binary prime index coin.1.2) coin.2.1
    (simObserve binary prime C queries Q pivot index front statements batching observer coin.1.1 coin.1.2) coin.2.2

theorem prepare_real (atLeastTwo : 1 < n) (codecInjective : C.Inj) :
    StatClose (MerklePreparation.error (Fintype.card Nonce) (Fintype.card D) n priorQueries)
      (real binary prime C before queries Q index cells front statements batching observer)
      (preparedReal binary prime C before queries Q index cells front statements batching observer) := by
  have nonnegative : 0 ≤ MerklePreparation.error (Fintype.card Nonce) (Fintype.card D) n priorQueries := by
    unfold MerklePreparation.error
    positivity
  exact statClose_mix nonnegative
    (fun outer merkle => real binary prime C before queries Q index cells front statements batching observer (outer,merkle))
    (fun outer merkle => preparedReal binary prime C before queries Q index cells front statements batching observer (outer,merkle))
    (fun outer => MerklePreparation.labelled_preparation_statClose (MerkleSimulation.nonceCodec C) n before
      (realMessages binary prime index cells outer.1 outer.2) atLeastTwo
      (MerkleSimulation.nonceCodec_inj C codecInjective)
      (realObserve binary prime C queries Q index cells front statements batching observer outer.1 outer.2))

theorem prepare_sim (atLeastTwo : 1 < n) (codecInjective : C.Inj) :
    StatClose (MerklePreparation.error (Fintype.card Nonce) (Fintype.card D) n priorQueries)
      (simulate binary prime C before queries Q pivot index front statements batching observer)
      (preparedSim binary prime C before queries Q pivot index front statements batching observer) := by
  have nonnegative : 0 ≤ MerklePreparation.error (Fintype.card Nonce) (Fintype.card D) n priorQueries := by
    unfold MerklePreparation.error
    positivity
  exact statClose_mix nonnegative
    (fun outer merkle => simulate binary prime C before queries Q pivot index front statements batching observer (outer,merkle))
    (fun outer merkle => preparedSim binary prime C before queries Q pivot index front statements batching observer (outer,merkle))
    (fun outer => MerklePreparation.labelled_preparation_statClose (MerkleSimulation.nonceCodec C) n before
      (simMessages binary prime index outer.2) atLeastTwo
      (MerkleSimulation.nonceCodec_inj C codecInjective)
      (simObserve binary prime C queries Q pivot index front statements batching observer outer.1 outer.2))

/-- Keep the public frontend coin and background table together while
averaging the joint backend masking theorem, then restore the protocol's
coin order. This changes no random variables or independence assumptions. -/
def cacheOrder : Coins (FrontCoin := FrontCoin) (Nonce := Nonce) (Enc := Enc) (D := D)
    binary prime (bw := bw) (nw := nw) (s := s) ≃
    (FrontCoin × (Enc → D)) ×
      (Masks binary prime (bw := bw) (nw := nw) (s := s) × HidingSample n (2*n-1) Nonce D) where
  toFun coin := ((coin.1.1,coin.2.1),coin.1.2,coin.2.2)
  invFun coin := ((coin.1.1,coin.2.1),coin.1.2,coin.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem cached_hiding_on_runs (positive : 0 < n) (codecInjective : C.Inj)
    (satisfied : ∀ a (H : Enc → D) labels,
      (statements a (before.run H).1 labels).1.Satisfies (Backend.logical (cells a (before.run H).1).1) ∧
      (statements a (before.run H).1 labels).2.Satisfies (Backend.logical (cells a (before.run H).1).2)) :
    StatClose (MerkleSimulation.openingError (Fintype.card Nonce) (Fintype.card D)
        n (n-Q.coordinates.card) queries)
      (preparedReal binary prime C before queries Q index cells front statements batching observer)
      (preparedSim binary prime C before queries Q pivot index front statements batching observer) := by
  have nonnegative : 0 ≤ MerkleSimulation.openingError (Fintype.card Nonce) (Fintype.card D)
      n (n-Q.coordinates.card) queries := by
    unfold MerkleSimulation.openingError
    positivity
  let first := fun (outer : FrontCoin × (Enc → D)) =>
    MerkleCache.compiled C n (2*n-1) queries Q.coordinates index outer.2
      (fun _ mask => MerkleBackend.realColumns binary prime (cells outer.1 (before.run outer.2).1) mask)
      (fun labels mask => (front outer.1 (before.run outer.2).1 labels,
        MerkleBackend.realResponses binary prime Q (cells outer.1 (before.run outer.2).1)
          (statements outer.1 (before.run outer.2).1 labels) (batching outer.1 (before.run outer.2).1 labels) mask))
      (observer (before.run outer.2).1)
  let second := fun (outer : FrontCoin × (Enc → D)) =>
    MerkleCache.compiled C n (2*n-1) queries Q.coordinates index outer.2
      (fun _ mask => MerkleBackend.simColumns binary prime mask)
      (fun labels mask => (front outer.1 (before.run outer.2).1 labels,
        MerkleBackend.simResponses binary prime Q pivot
          (statements outer.1 (before.run outer.2).1 labels) (batching outer.1 (before.run outer.2).1 labels) mask))
      (observer (before.run outer.2).1)
  have each (outer : FrontCoin × (Enc → D)) : StatClose
      (MerkleSimulation.openingError (Fintype.card Nonce) (Fintype.card D)
        n (n-Q.coordinates.card) queries) (first outer) (second outer) :=
    MerkleBackend.joint_cache_hiding binary prime C (2*n-1) queries Q pivot index outer.2
      (front outer.1 (before.run outer.2).1)
      (fun _ => cells outer.1 (before.run outer.2).1)
      (statements outer.1 (before.run outer.2).1) (batching outer.1 (before.run outer.2).1)
      codecInjective positive (by omega) (le_refl _)
      (satisfied outer.1 outer.2) (observer (before.run outer.2).1)
  have mixed := statClose_mix nonnegative first second each
  exact statClose_reindex (cacheOrder binary prime) (cacheOrder binary prime)
    (fun _ => rfl) (fun _ => rfl) mixed

/-- The universal statement form remains a convenience wrapper. The
underlying law needs ordinary row truth only at actual prior outputs. -/
theorem cached_hiding (positive : 0 < n) (codecInjective : C.Inj)
    (satisfied : ∀ a request labels,
      (statements a request labels).1.Satisfies (Backend.logical (cells a request).1) ∧
      (statements a request labels).2.Satisfies (Backend.logical (cells a request).2)) :
    StatClose (MerkleSimulation.openingError (Fintype.card Nonce) (Fintype.card D)
        n (n-Q.coordinates.card) queries)
      (preparedReal binary prime C before queries Q index cells front statements batching observer)
      (preparedSim binary prime C before queries Q pivot index front statements batching observer) :=
  cached_hiding_on_runs binary prime C before queries Q pivot index cells front statements batching observer
    positive codecInjective (fun a H labels => satisfied a (before.run H).1 labels)

/-- The compiled backend simulator uses zero logical cells and the public
affine statement. Its only witness premise is that the honest frontend cells
satisfy those ordinary affine rows. Both preparation costs are explicit. -/
theorem simulator_statClose_on_runs (atLeastTwo : 1 < n) (codecInjective : C.Inj)
    (satisfied : ∀ a (H : Enc → D) labels,
      (statements a (before.run H).1 labels).1.Satisfies (Backend.logical (cells a (before.run H).1).1) ∧
      (statements a (before.run H).1 labels).2.Satisfies (Backend.logical (cells a (before.run H).1).2)) :
    StatClose
      (2*MerklePreparation.error (Fintype.card Nonce) (Fintype.card D) n priorQueries +
        MerkleSimulation.openingError (Fintype.card Nonce) (Fintype.card D) n (n-Q.coordinates.card) queries)
      (real binary prime C before queries Q index cells front statements batching observer)
      (simulate binary prime C before queries Q pivot index front statements batching observer) := by
  have start := prepare_real binary prime C before queries Q index cells front statements batching observer
    atLeastTwo codecInjective
  have middle := cached_hiding_on_runs binary prime C before queries Q pivot index cells front statements batching observer
    (by omega) codecInjective satisfied
  have finish := prepare_sim binary prime C before queries Q pivot index front statements batching observer
    atLeastTwo codecInjective
  have combined := start.trans (middle.trans finish.symm)
  exact StatClose.mono (by ring_nf; rfl) combined

/-- This wrapper preserves the existing API; applications with an adaptive
request should use the run-scoped premise above. -/
theorem simulator_statClose (atLeastTwo : 1 < n) (codecInjective : C.Inj)
    (satisfied : ∀ a request labels,
      (statements a request labels).1.Satisfies (Backend.logical (cells a request).1) ∧
      (statements a request labels).2.Satisfies (Backend.logical (cells a request).2)) :
    StatClose
      (2*MerklePreparation.error (Fintype.card Nonce) (Fintype.card D) n priorQueries +
        MerkleSimulation.openingError (Fintype.card Nonce) (Fintype.card D) n (n-Q.coordinates.card) queries)
      (real binary prime C before queries Q index cells front statements batching observer)
      (simulate binary prime C before queries Q pivot index front statements batching observer) :=
  simulator_statClose_on_runs binary prime C before queries Q pivot index cells front statements batching observer
    atLeastTwo codecInjective (fun a H labels => satisfied a (before.run H).1 labels)

end LfzkV2.Current.ZeroKnowledge.BackendCompiled
