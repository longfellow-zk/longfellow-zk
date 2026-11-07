import LfzkV2.Current.ZeroKnowledge.MerkleCacheBound
import LfzkV2.Current.ZeroKnowledge.MerkleBackend

/-! Backend masking and Merkle hiding with the complete prior oracle table
retained.  The witness-dependent bijection changes backend masks at fixed
common labels.  It never changes the background oracle, the prior public
state, the shared opening set, or the tuple columns visible at that set. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleCache
open Merkle Merkle.MH Finset
open scoped Classical
set_option maxHeartbeats 800000

variable {Index Nonce Leaf D Enc Observed Backend Public : Type}
variable [Fintype Nonce] [Nonempty Nonce] [DecidableEq Nonce]
variable [Fintype D] [DecidableEq D] [Inhabited D]
variable [DecidableEq Enc] [DecidableEq Observed]
variable (C : Codec (Index × Nonce) Leaf D Enc) (n T queries : ℕ)
variable (I : Finset (Fin n)) (index : Fin n → Index) (background : Enc → D)

theorem indexed_hiding (injective : C.Inj) (positive : 0 < n)
    (fits : 2*n-2 < T) (fitsAll : 2*n-1 ≤ T)
    (first second : (Fin T → D) → Fin n → Leaf)
    (agree : ∀ labels i, i ∈ I → first labels i = second labels i)
    (observer : (Fin T → D) → OpeningView n I Nonce D → RandomOracle.Tree Enc D Observed queries) :
    StatClose (MerkleSimulation.openingError (Fintype.card Nonce) (Fintype.card D)
      n (n-I.card) queries)
      (experiment (MerkleSimulation.nonceCodec C) n I background observer
        (fun labels i => (index i,first labels i)))
      (experiment (MerkleSimulation.nonceCodec C) n I background observer
        (fun labels i => (index i,second labels i))) := by
  let different : Finset (Fin n) := univ \ I
  have count : different.card = n-I.card := by
    dsimp only [different]
    rw [card_sdiff_of_subset (subset_univ I),card_univ,Fintype.card_fin]
  have nonceInj (messages : (Fin T → D) → Fin n → Leaf) (labels : Fin T → D) (i : Fin n) :
      Function.Injective fun nonce : Nonce =>
        (MerkleSimulation.nonceCodec C).leafEnc (nonce,(index i,messages labels i)) := by
    intro a b equal
    exact congrArg Prod.fst ((MerkleSimulation.nonceCodec_inj C injective).leaf equal)
  rw [← count]
  apply opening_hiding (MerkleSimulation.nonceCodec C) n I background _ _ different observer
    fits positive fitsAll (MerkleSimulation.nonceCodec_inj C injective)
  · intro i hi
    exact (mem_sdiff.mp hi).2
  · intro labels i hi
    apply Prod.ext
    · rfl
    · exact agree labels i (by simpa only [different,mem_sdiff,mem_univ,true_and,not_not] using hi)
  · exact nonceInj first
  · exact nonceInj second

variable [Fintype Backend]

def compiled
    (columns : (Fin T → D) → Backend → Fin n → Leaf)
    (publicView : (Fin T → D) → Backend → Public)
    (observer : Public → ({i : Fin n // i ∈ I} → Leaf) →
      (Fin T → D) → OpeningView n I Nonce D → RandomOracle.Tree Enc D Observed queries)
    (coin : Backend × HidingSample n T Nonce D) : Observed :=
  experiment (MerkleSimulation.nonceCodec C) n I background
    (fun labels opening => observer (publicView labels coin.1)
      (fun i => columns labels coin.1 i.val) labels opening)
    (fun labels i => (index i,columns labels coin.1 i)) coin.2

/-- The actual simulator distribution follows by a fiberwise change of
backend randomness, not by conditioning on a witness-dependent honest root. -/
theorem compiled_hiding (injective : C.Inj) (positive : 0 < n)
    (fits : 2*n-2 < T) (fitsAll : 2*n-1 ≤ T)
    (realColumns simColumns : (Fin T → D) → Backend → Fin n → Leaf)
    (realPublic simPublic : (Fin T → D) → Backend → Public)
    (shift : (Fin T → D) → Backend ≃ Backend)
    (sameColumns : ∀ labels coin i, i ∈ I →
      realColumns labels coin i = simColumns labels (shift labels coin) i)
    (samePublic : ∀ labels coin, realPublic labels coin = simPublic labels (shift labels coin))
    (observer : Public → ({i : Fin n // i ∈ I} → Leaf) →
      (Fin T → D) → OpeningView n I Nonce D → RandomOracle.Tree Enc D Observed queries) :
    StatClose (MerkleSimulation.openingError (Fintype.card Nonce) (Fintype.card D) n (n-I.card) queries)
      (compiled C n T queries I index background realColumns realPublic observer)
      (compiled C n T queries I index background simColumns simPublic observer) := by
  let intermediate : Backend → HidingSample n T Nonce D → Observed := fun coin =>
    experiment (MerkleSimulation.nonceCodec C) n I background
      (fun labels opening => observer (realPublic labels coin)
        (fun i => realColumns labels coin i.val) labels opening)
      (fun labels i => (index i,simColumns labels (shift labels coin) i))
  have nonnegative : 0 ≤ MerkleSimulation.openingError
      (Fintype.card Nonce) (Fintype.card D) n (n-I.card) queries := by
    unfold MerkleSimulation.openingError
    positivity
  have masked : StatClose (MerkleSimulation.openingError
      (Fintype.card Nonce) (Fintype.card D) n (n-I.card) queries)
      (compiled C n T queries I index background realColumns realPublic observer)
      (fun coin : Backend × HidingSample n T Nonce D => intermediate coin.1 coin.2) := by
    have perCoin (coin : Backend) : StatClose (MerkleSimulation.openingError
        (Fintype.card Nonce) (Fintype.card D) n (n-I.card) queries)
        (fun sample => compiled C n T queries I index background realColumns realPublic observer (coin,sample))
        (intermediate coin) :=
      indexed_hiding C n T queries I index background injective positive fits fitsAll
        (fun labels i => realColumns labels coin i)
        (fun labels i => simColumns labels (shift labels coin) i)
        (fun labels i hi => sameColumns labels coin i hi)
        (fun labels opening => observer (realPublic labels coin)
          (fun i => realColumns labels coin i.val) labels opening)
    exact statClose_mix nonnegative
      (fun coin sample => compiled C n T queries I index background realColumns realPublic observer (coin,sample))
      intermediate perCoin
  apply statClose_reindex (Equiv.refl _) (CommonLabels.fiberEquiv shift).symm
    (fun _ => rfl) _ masked
  intro coin
  rcases coin with ⟨backend,nonce,labels⟩
  change compiled C n T queries I index background simColumns simPublic observer
      (backend,nonce,labels) = intermediate ((shift labels).symm backend) (nonce,labels)
  unfold compiled intermediate experiment
  have restored : shift labels ((shift labels).symm backend) = backend :=
    (shift labels).apply_symm_apply backend
  have publicEq : realPublic labels ((shift labels).symm backend) = simPublic labels backend := by
    simpa only [restored] using samePublic labels ((shift labels).symm backend)
  have openedEq : (fun i : {i : Fin n // i ∈ I} =>
      realColumns labels ((shift labels).symm backend) i.val) =
      (fun i : {i : Fin n // i ∈ I} => simColumns labels backend i.val) := by
    funext i
    simpa only [restored] using sameColumns labels ((shift labels).symm backend) i.val i.property
  simp only [restored,publicEq,openedEq]

end LfzkV2.Current.ZeroKnowledge.MerkleCache

namespace LfzkV2.Current.ZeroKnowledge.MerkleBackend
open Merkle Merkle.MH LigeroFamily RecursivePolygero.Local
open scoped Classical
variable {B N : Type} [Field B] [Field N] [Fintype B] [Fintype N]
variable {r w n bw nw s : ℕ}
variable (binary : PolygeroZk.Geometry B r w 0 n) (prime : PolygeroZk.Geometry N r w 0 n)
variable {BE NE : Type} [Fintype BE] [Fintype NE]
variable {Index Nonce D Enc Front Observed : Type}
variable [Fintype Nonce] [Nonempty Nonce] [DecidableEq Nonce]
variable [Fintype D] [DecidableEq D] [Inhabited D]
variable [DecidableEq Enc] [DecidableEq Observed]
variable (C : Codec (Index × Nonce) (Leaf (B := B) (N := N) (bw := bw) (nw := nw)) D Enc)
variable (T queries : ℕ) (Q : QuerySet n r) (pivot : Fin w) (index : Fin n → Index)
variable (background : Enc → D) (front : (Fin T → D) → Front)
variable (cells : (Fin T → D) → Backend.Cells B bw w × Backend.Cells N nw w)
variable (statements : (Fin T → D) → ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
variable (coins : (Fin T → D) → Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)

/-- Concrete two-field masking with all earlier oracle answers retained.
The simulator commits zero cells; its public correction depends on the shared
Q. Both full H/Z pairs, opened tuple rows and authentication are included. -/
theorem joint_cache_hiding
    (injective : C.Inj) (positive : 0 < n) (fits : 2*n-2 < T) (fitsAll : 2*n-1 ≤ T)
    (satisfied : ∀ labels,
      (statements labels).1.Satisfies (Backend.logical (cells labels).1) ∧
      (statements labels).2.Satisfies (Backend.logical (cells labels).2))
    (observer : (Front × Responses (B := B) (N := N) (r := r) (w := w) (s := s)) →
      ({i : Fin n // i ∈ Q.coordinates} → Leaf (B := B) (N := N) (bw := bw) (nw := nw)) →
      (Fin T → D) → OpeningView n Q.coordinates Nonce D →
      RandomOracle.Tree Enc D Observed queries) :
    StatClose (MerkleSimulation.openingError
      (Fintype.card Nonce) (Fintype.card D) n (n-Q.coordinates.card) queries)
      (MerkleCache.compiled C n T queries Q.coordinates index background
        (fun labels tape => realColumns binary prime (cells labels) tape)
        (fun labels tape => (front labels,
          realResponses binary prime Q (cells labels) (statements labels) (coins labels) tape)) observer)
      (MerkleCache.compiled C n T queries Q.coordinates index background
        (fun _ tape => simColumns binary prime tape)
        (fun labels tape => (front labels,
          simResponses binary prime Q pivot (statements labels) (coins labels) tape)) observer) := by
  apply MerkleCache.compiled_hiding C n T queries Q.coordinates index background
    injective positive fits fitsAll _ _ _ _
    (fun labels => Backend.jointCoupling binary prime Q pivot (cells labels)
      (statements labels) (satisfied labels) (coins labels))
  · intro labels tape i hi
    exact columns_coupling binary prime Q pivot (cells labels) (statements labels)
      (satisfied labels) (coins labels) tape i hi
  · intro labels tape
    exact congrArg (fun response => (front labels,response))
      (responses_coupling binary prime Q pivot (cells labels) (statements labels)
        (satisfied labels) (coins labels) tape)

end LfzkV2.Current.ZeroKnowledge.MerkleBackend
