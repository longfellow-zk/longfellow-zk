import LfzkV2.Current.ZeroKnowledge.MerkleBound

/-! Merkle labels and backend masks must be coupled together.  Conditioning on
the commitment root and then applying a fixed-opening backend hiding theorem
would be invalid: the honest root depends on those masks.

Here the lazy-oracle label tape stays fixed while a bijection changes backend
coins.  At paired coins, the public transcript and every opened tuple column
agree.  Merkle hiding is applied before averaging over the backend coins; a
fiberwise change of variables then gives the simulator's actual distribution.
The commitment may therefore depend on every backend coin.

This theorem concerns the commit-first Merkle experiment.  Moving an adaptive
observer's pre-commitment queries across the commitment is a separate step. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CommonLabels

set_option maxHeartbeats 600000

open Merkle Merkle.MH Finset
open scoped Classical

/-- Change backend coins while keeping the nonce schedule and all common
Merkle labels fixed.  The bijection may depend on those labels. -/
def fiberEquiv {Tape Backend Nonce : Type} (shift : Tape → Backend ≃ Backend) :
    (Backend × (Nonce × Tape)) ≃ (Backend × (Nonce × Tape)) where
  toFun x := (shift x.2.2 x.1,x.2)
  invFun x := ((shift x.2.2).symm x.1,x.2)
  left_inv x := by simp
  right_inv x := by simp

section Compiler
variable {Index Nonce Leaf D Enc V Backend Public : Type}
variable [Fintype Nonce] [Nonempty Nonce] [DecidableEq Nonce]
variable [Fintype D] [DecidableEq D] [Inhabited D]
variable [DecidableEq Enc] [DecidableEq V] [Fintype Backend]
variable (C : Codec (Index × Nonce) Leaf D Enc)
variable (n T queries : ℕ) (I : Finset (Fin n)) (index : Fin n → Index)

/-- The observer gets the public frontend/backend transcript, the opened
columns, the Merkle opening and ordinary oracle access.  Hidden columns are
not arguments to the observer. -/
def compiled
    (columns : (Fin T → D) → Backend → Fin n → Leaf)
    (publicView : (Fin T → D) → Backend → Public)
    (observer : Public → ({i : Fin n // i ∈ I} → Leaf) →
      (Fin T → D) → OpeningView n I Nonce D → RandomOracle.Tree Enc D V queries)
    (coin : Backend × HidingSample n T Nonce D) : V :=
  openingHidingView (MerkleSimulation.nonceCodec C) n I
    (fun tape i => (index i,columns tape coin.1 i))
    (fun tape opening => observer (publicView tape coin.1)
      (fun i => columns tape coin.1 i.val) tape opening) coin.2

/-- A fixed label tape permits the backend's fixed-opening masking bijection
without requiring backend coins to remain independent after conditioning on
the honest commitment root.  The only cryptographic error here is the explicit
Merkle hiding bound. -/
theorem compiled_hiding
    (injective : C.Inj) (positive : 0 < n)
    (fits : 2*n-2 < T) (fitsAll : 2*n-1 ≤ T)
    (realColumns simColumns : (Fin T → D) → Backend → Fin n → Leaf)
    (realPublic simPublic : (Fin T → D) → Backend → Public)
    (shift : (Fin T → D) → Backend ≃ Backend)
    (sameColumns : ∀ tape coin i, i ∈ I →
      realColumns tape coin i = simColumns tape (shift tape coin) i)
    (samePublic : ∀ tape coin,
      realPublic tape coin = simPublic tape (shift tape coin))
    (observer : Public → ({i : Fin n // i ∈ I} → Leaf) →
      (Fin T → D) → OpeningView n I Nonce D → RandomOracle.Tree Enc D V queries) :
    StatClose (MerkleSimulation.openingError
      (Fintype.card Nonce) (Fintype.card D) n (n-I.card) queries)
      (compiled C n T queries I index realColumns realPublic observer)
      (compiled C n T queries I index simColumns simPublic observer) := by
  let intermediate : Backend → HidingSample n T Nonce D → V := fun coin =>
    openingHidingView (MerkleSimulation.nonceCodec C) n I
      (fun tape i => (index i,simColumns tape (shift tape coin) i))
      (fun tape opening => observer (realPublic tape coin)
        (fun i => realColumns tape coin i.val) tape opening)
  have nonnegative : 0 ≤ MerkleSimulation.openingError
      (Fintype.card Nonce) (Fintype.card D) n (n-I.card) queries := by
    unfold MerkleSimulation.openingError
    positivity
  have masked : StatClose (MerkleSimulation.openingError
      (Fintype.card Nonce) (Fintype.card D) n (n-I.card) queries)
      (compiled C n T queries I index realColumns realPublic observer)
      (fun coin : Backend × HidingSample n T Nonce D => intermediate coin.1 coin.2) := by
    have perCoin (coin : Backend) : StatClose (MerkleSimulation.openingError
        (Fintype.card Nonce) (Fintype.card D) n (n-I.card) queries)
        (fun sample => compiled C n T queries I index realColumns realPublic observer (coin,sample))
        (intermediate coin) :=
      MerkleSimulation.opening_hiding C injective n positive I T index
        (fun tape i => realColumns tape coin i)
        (fun tape i => simColumns tape (shift tape coin) i)
        (fun tape i hi => sameColumns tape coin i hi)
        (fun tape opening => observer (realPublic tape coin)
          (fun i => realColumns tape coin i.val) tape opening) fits fitsAll
    exact statClose_mix nonnegative
      (fun coin sample => compiled C n T queries I index realColumns realPublic observer (coin,sample))
      intermediate perCoin
  apply statClose_reindex (Equiv.refl _) (fiberEquiv shift).symm
    (fun _ => rfl) _ masked
  intro coin
  rcases coin with ⟨backend,nonce,tape⟩
  change compiled C n T queries I index simColumns simPublic observer
      (backend,nonce,tape) = intermediate ((shift tape).symm backend) (nonce,tape)
  unfold compiled intermediate openingHidingView
  have restored : shift tape ((shift tape).symm backend) = backend :=
    (shift tape).apply_symm_apply backend
  have publicEq : realPublic tape ((shift tape).symm backend) = simPublic tape backend := by
    simpa only [restored] using samePublic tape ((shift tape).symm backend)
  have openedEq : (fun i : {i : Fin n // i ∈ I} =>
      realColumns tape ((shift tape).symm backend) i.val) =
      (fun i : {i : Fin n // i ∈ I} => simColumns tape backend i.val) := by
    funext i
    simpa only [restored] using sameColumns tape ((shift tape).symm backend) i.val i.property
  simp only [restored,publicEq,openedEq]

end Compiler
end LfzkV2.Current.ZeroKnowledge.CommonLabels
