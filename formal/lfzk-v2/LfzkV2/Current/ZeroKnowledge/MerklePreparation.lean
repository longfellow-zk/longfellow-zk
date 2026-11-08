import LfzkV2.Current.ZeroKnowledge.MerkleCommitPrepared
import LfzkV2.Current.ZeroKnowledge.MerklePriorHits

/-! Statistical cost of replacing one causal honest commitment by its
independent-label prepared table after an adaptive prior query stage.
The earlier request is preserved by the explicit refresh bijection.
The bound counts commitment collisions and prior nonce/child-label guesses;
it never conditions fresh labels or nonces on the eventual commitment root. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerklePreparation

set_option maxHeartbeats 700000

open Merkle Merkle.MH Merkle.RandomOracle Finset
open scoped Classical

def error (S D n queries : ℕ) : ℚ :=
  ((2*n^2+n*queries : ℕ) : ℚ)/S +
    (((2*n-1)*(2*n-2) : ℕ) : ℚ)/(2*D) +
    (((n-1)*queries : ℕ) : ℚ)/D^2

def numerator (S D n queries : ℕ) : ℕ :=
  (2*n^2+n*queries)*(S^(n-1)*D^(2*n-1)) +
    ((2*n-1)*(2*n-2)/2)*(S^n*D^(2*n-2)) +
    ((n-1)*queries)*(S^n*D^(2*n-3))

theorem numerator_ratio_le (S D n queries : ℕ)
    (saltPositive : 0 < S) (digestPositive : 0 < D) (atLeastTwo : 1 < n) :
    (numerator S D n queries : ℚ) / ((S:ℚ)^n*(D:ℚ)^(2*n-1)) ≤ error S D n queries := by
  have hs : (S:ℚ)^(n-1)*(S:ℚ) = (S:ℚ)^n := by
    rw [←pow_succ]
    congr 1
    omega
  have hd : (D:ℚ)^(2*n-3)*(D:ℚ)^2 = (D:ℚ)^(2*n-1) := by
    rw [←pow_add]
    congr 1
    omega
  have step : (D:ℚ)^(2*n-3)*(D:ℚ) = (D:ℚ)^(2*n-2) := by
    rw [←pow_succ]
    congr 1
    omega
  have hS : (S:ℚ) ≠ 0 := by positivity
  have hD : (D:ℚ) ≠ 0 := by positivity
  have half : ((((2*n-1)*(2*n-2)/2 : ℕ) : ℚ)) ≤
      (((2*n-1)*(2*n-2) : ℕ) : ℚ)/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℚ) < 2)).mpr
    exact_mod_cast (show ((2*n-1)*(2*n-2)/2)*2 ≤ (2*n-1)*(2*n-2) by omega)
  calc
    _ = ((2*n^2+n*queries : ℕ) : ℚ)/S +
        (((2*n-1)*(2*n-2)/2 : ℕ) : ℚ)/D +
        (((n-1)*queries : ℕ) : ℚ)/D^2 := by
      unfold numerator
      push_cast
      rw [←hs,←hd,←step]
      field_simp
    _ ≤ ((2*n^2+n*queries : ℕ) : ℚ)/S +
        ((((2*n-1)*(2*n-2) : ℕ) : ℚ)/2)/D +
        (((n-1)*queries : ℕ) : ℚ)/D^2 := by gcongr
    _ = _ := by unfold error; push_cast; ring

theorem error_mono (S D n : ℕ) {queries larger : ℕ} (bound : queries ≤ larger) :
    error S D n queries ≤ error S D n larger := by
  unfold error
  gcongr

section Counting
variable {Salt Message Digest Enc Request Value : Type}
variable [Fintype Salt] [DecidableEq Salt]
variable [Fintype Digest] [DecidableEq Digest] [Inhabited Digest]
variable [DecidableEq Enc] [DecidableEq Value]
variable (codec : Codec Salt Message Digest Enc) (n : ℕ)
variable {fuel : ℕ} (before : Tree Enc Digest Request fuel)
variable (cells : Request → Fin n → Message)

def prior (background : Enc → Digest) : Finset Enc :=
  ((before.run background).2.map Prod.fst).toFinset

omit [Fintype Digest] [DecidableEq Digest] [Inhabited Digest] in
theorem prior_card (background : Enc → Digest) : (prior before background).card ≤ fuel := by
  have length : (before.run background).2.length ≤ fuel := by
    induction before with
    | done out => simp only [Tree.run_done,List.length_nil,Nat.zero_le]
    | @query bound query next ih =>
        simpa only [Tree.run_query,List.length_cons] using Nat.add_le_add_right (ih (background query)) 1
  exact le_trans (List.toFinset_card_le _) (by simpa only [List.length_map] using length)

def priorLeaf (messages : Fin n → Message) (old : Finset Enc) :
    Finset (HidingSample n (2*n-1) Salt Digest) :=
  univ.filter fun coin => ∃ column, codec.leafEnc (coin.1 column,messages column) ∈ old

def priorNode (old : Finset Enc) : Finset (HidingSample n (2*n-1) Salt Digest) :=
  univ.filter fun coin => ∃ vertex : MerklePriorHits.Node n,
    codec.nodeEnc (coin.2 (MerklePriorHits.left n (2*n-1) (le_refl _) vertex),
      coin.2 (MerklePriorHits.right n (2*n-1) (le_refl _) vertex)) ∈ old

omit [Fintype Salt] [DecidableEq Salt] [Fintype Digest] [DecidableEq Digest] [DecidableEq Enc] in
theorem nodeInput_eq (tape : Fin (2*n-1) → Digest) (vertex : MerklePriorHits.Node n) :
    tapeNodeInput codec n tape vertex.val.val =
      codec.nodeEnc (tape (MerklePriorHits.left n (2*n-1) (le_refl _) vertex),
        tape (MerklePriorHits.right n (2*n-1) (le_refl _) vertex)) := by
  unfold tapeNodeInput tapeAt
  have positive := vertex.property
  have bounded := vertex.val.isLt
  rw [dif_pos (by omega),dif_pos (by omega)]
  rfl

omit [Inhabited Digest] in
theorem priorLeaf_card (codecInjective : codec.Inj)
    (messages : Fin n → Message) (old : Finset Enc) :
    (priorLeaf codec n messages old).card ≤
      Fintype.card Digest^(2*n-1) * (n*(old.card*Fintype.card Salt^(n-1))) := by
  exact (card_filter_prod_le_of_snd _ _ fun _ =>
    MerklePriorHits.leaves_card_le codec codecInjective n messages old).trans_eq (by simp)

omit [Inhabited Digest] in
theorem priorNode_card (codecInjective : codec.Inj) (old : Finset Enc) :
    (priorNode (Salt := Salt) codec n old).card ≤
      Fintype.card Salt^n * (((n-1)*old.card)*Fintype.card Digest^((2*n-1)-2)) := by
  exact (card_filter_prod_le_of_fst _ _ fun _ =>
    MerklePriorHits.nodes_card_le codec codecInjective n (2*n-1) (le_refl _) old).trans_eq (by simp)

def bad (messages : Fin n → Message) (old : Finset Enc) :
    Finset (HidingSample n (2*n-1) Salt Digest) :=
  commitInjectiveFailure codec n (2*n-1) (fun _ => messages) ∪
    priorLeaf codec n messages old ∪ priorNode (Salt := Salt) codec n old

theorem bad_card (positive : 0 < n) (codecInjective : codec.Inj)
    (messages : Fin n → Message) (old : Finset Enc) :
    (bad codec n messages old).card ≤ numerator (Fintype.card Salt) (Fintype.card Digest) n old.card := by
  have salts (_tape : Fin (2*n-1) → Digest) (column : Fin n) :
      Function.Injective fun salt : Salt => codec.leafEnc (salt,messages column) := by
    intro first second equal
    exact congrArg Prod.fst (codecInjective.leaf equal)
  have collisions := commitInjective_failure_card_le codec n positive (2*n-1)
    (fun _ => messages) (le_refl _) codecInjective salts
  have leafBound := priorLeaf_card codec n codecInjective messages old
  have nodeBound := priorNode_card (Salt := Salt) codec n codecInjective old
  calc
    _ ≤ (commitInjectiveFailure codec n (2*n-1) (fun _ => messages)).card +
          (priorLeaf codec n messages old).card+(priorNode (Salt := Salt) codec n old).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add collisions leafBound) nodeBound
    _ = _ := by
      unfold numerator
      have first : (2*n-1)-1 = 2*n-2 := by omega
      have second : (2*n-1)-2 = 2*n-3 := by omega
      rw [first,second]
      ring

/-- Off the explicitly counted set the causal refresh returns the prepared
oracle, and the canonical commitment itself has distinct inputs. -/
theorem prepared_off_bad (positive : 0 < n) (background : Enc → Digest)
    (coin : HidingSample n (2*n-1) Salt Digest)
    (outside : coin ∉ bad codec n (cells (before.run background).1) (prior before background)) :
    commitInputsInjective codec n coin.1 (cells (before.run background).1)
        (commitOracle codec n coin.1 (cells (before.run background).1) coin.2) ∧
      (MerkleRefresh.refresh (MerkleCommitRefresh.initial before)
        (MerkleCommitRefresh.input codec n (fun _ => coin.1) cells)
        (MerkleCommitRefresh.update n) (2*n-1) (le_refl _) (background,coin.2)).1 =
      MerkleCache.prepared codec n coin.1 (cells (before.run background).1) coin.2 background := by
  have disjoint := outside
  simp only [bad,mem_union,not_or,and_assoc] at disjoint
  have injective : commitInputsInjective codec n coin.1 (cells (before.run background).1)
      (commitOracle codec n coin.1 (cells (before.run background).1) coin.2) := by
    simpa only [commitInjectiveFailure,mem_filter,mem_univ,true_and,not_not] using disjoint.1
  have noLeaf : ∀ qa ∈ (before.run background).2, ∀ column : Fin n,
      qa.1 ≠ codec.leafEnc (coin.1 column,cells (before.run background).1 column) := by
    intro qa earlier column same
    apply disjoint.2.1
    refine mem_filter.mpr ⟨mem_univ _,column,?_⟩
    rw [← same]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨qa,earlier,rfl⟩)
  have noNode : ∀ qa ∈ (before.run background).2, ∀ vertex : ℕ,
      0 < vertex → vertex < n → qa.1 ≠ tapeNodeInput codec n coin.2 vertex := by
    intro qa earlier vertex above below same
    apply disjoint.2.2
    refine mem_filter.mpr ⟨mem_univ _,⟨⟨vertex,below⟩,above⟩,?_⟩
    rw [← nodeInput_eq codec n coin.2 ⟨⟨vertex,below⟩,above⟩,← same]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨qa,earlier,rfl⟩)
  exact ⟨injective,MerkleCommitRefresh.refresh_eq_prepared_of_injective n codec (fun _ => coin.1) cells before
    positive background coin.2 injective
    (MerkleCommitRefresh.priorAvoids_of_no_hit n codec (fun _ => coin.1) cells before
      positive background coin.2 injective noLeaf noNode)⟩

/-- The private nonce schedule is independent of the prior oracle; the
request-dependent message vector is fixed in this fibre. -/
theorem disagreement_card (positive : 0 < n) (codecInjective : codec.Inj)
    (background : Enc → Digest) (observe : (Fin n → Salt) → (Enc → Digest) → Value) :
    (univ.filter fun coin : HidingSample n (2*n-1) Salt Digest =>
      observe coin.1
        (MerkleRefresh.refresh (MerkleCommitRefresh.initial before)
          (MerkleCommitRefresh.input codec n (fun _ => coin.1) cells)
          (MerkleCommitRefresh.update n) (2*n-1) (le_refl _) (background,coin.2)).1 ≠
      observe coin.1 (MerkleCache.prepared codec n coin.1 (cells (before.run background).1) coin.2 background)).card ≤
        numerator (Fintype.card Salt) (Fintype.card Digest) n (prior before background).card := by
  apply le_trans (card_le_card ?_)
    (bad_card codec n positive codecInjective (cells (before.run background).1) (prior before background))
  intro coin member
  by_contra outside
  exact (mem_filter.mp member).2
    (congrArg (observe coin.1) (prepared_off_bad codec n before cells positive background coin outside).2)

def refreshedView (background : Enc → Digest)
    (observe : (Fin n → Salt) → (Enc → Digest) → Value)
    (coin : HidingSample n (2*n-1) Salt Digest) : Value :=
  observe coin.1
    (MerkleRefresh.refresh (MerkleCommitRefresh.initial before)
      (MerkleCommitRefresh.input codec n (fun _ => coin.1) cells)
      (MerkleCommitRefresh.update n) (2*n-1) (le_refl _) (background,coin.2)).1

def preparedView (background : Enc → Digest)
    (observe : (Fin n → Salt) → (Enc → Digest) → Value)
    (coin : HidingSample n (2*n-1) Salt Digest) : Value :=
  observe coin.1 (MerkleCache.prepared codec n coin.1 (cells (before.run background).1) coin.2 background)

theorem fixed_statClose [Nonempty Salt] (atLeastTwo : 1 < n) (codecInjective : codec.Inj)
    (background : Enc → Digest) (observe : (Fin n → Salt) → (Enc → Digest) → Value) :
    StatClose (error (Fintype.card Salt) (Fintype.card Digest) n fuel)
      (refreshedView codec n before cells background observe)
      (preparedView codec n before cells background observe) := by
  have counted : CountingClose
      (numerator (Fintype.card Salt) (Fintype.card Digest) n (prior before background).card)
      (refreshedView codec n before cells background observe)
      (preparedView codec n before cells background observe) :=
    disagreement_card codec n before cells (by omega) codecInjective background observe
  have normalized := LfzkV1.ZkMerkle.statClose_of_countingClose counted
  apply StatClose.mono _ normalized
  have size : Fintype.card (HidingSample n (2*n-1) Salt Digest) =
      Fintype.card Salt^n*Fintype.card Digest^(2*n-1) := by simp [HidingSample]
  rw [size]
  push_cast
  exact (numerator_ratio_le _ _ _ _ Fintype.card_pos Fintype.card_pos atLeastTwo).trans
    (error_mono _ _ _ (prior_card before background))

abbrev Coins := (Enc → Digest) × HidingSample n (2*n-1) Salt Digest

def refreshFor (salt : Fin n → Salt) :
    ((Enc → Digest) × (Fin (2*n-1) → Digest)) ≃
      ((Enc → Digest) × (Fin (2*n-1) → Digest)) :=
  MerkleRefresh.refresh (MerkleCommitRefresh.initial before)
    (MerkleCommitRefresh.input codec n (fun _ => salt) cells)
    (MerkleCommitRefresh.update n) (2*n-1) (le_refl _)

/-- The nonce schedule stays fixed while the causal oracle/label swap acts.
This is one global bijection, not a conditioning on the chosen request. -/
def refreshEquiv : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n ≃
    Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n where
  toFun coin :=
    let next := refreshFor codec n before cells coin.2.1 (coin.1,coin.2.2)
    (next.1,coin.2.1,next.2)
  invFun coin :=
    let previous := (refreshFor codec n before cells coin.2.1).symm (coin.1,coin.2.2)
    (previous.1,coin.2.1,previous.2)
  left_inv coin := by
    rcases coin with ⟨background,salt,tape⟩
    change (((refreshFor codec n before cells salt).symm
        (refreshFor codec n before cells salt (background,tape))).1,salt,
      ((refreshFor codec n before cells salt).symm
        (refreshFor codec n before cells salt (background,tape))).2) = _
    rw [Equiv.symm_apply_apply]
  right_inv coin := by
    rcases coin with ⟨background,salt,tape⟩
    change ((refreshFor codec n before cells salt
        ((refreshFor codec n before cells salt).symm (background,tape))).1,salt,
      (refreshFor codec n before cells salt
        ((refreshFor codec n before cells salt).symm (background,tape))).2) = _
    rw [Equiv.apply_symm_apply]

/-- Any subsequent protocol/observer computation has the same view up to
the explicit preparation error. `observe` receives the actual resulting
oracle; the original background table is never appended to its public view.
The finite input type is the full reachable-query window, not all bytes. -/
theorem preparation_statClose [Fintype Enc] [Nonempty Salt]
    (atLeastTwo : 1 < n) (codecInjective : codec.Inj)
    (observe : (Fin n → Salt) → (Enc → Digest) → Value) :
    StatClose (error (Fintype.card Salt) (Fintype.card Digest) n fuel)
      (fun coin : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n => observe coin.2.1 coin.1)
      (fun coin : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n =>
        preparedView codec n before cells coin.1 observe coin.2) := by
  have nonnegative : 0 ≤ error (Fintype.card Salt) (Fintype.card Digest) n fuel := by
    unfold error
    positivity
  have mixture : StatClose (error (Fintype.card Salt) (Fintype.card Digest) n fuel)
      (fun coin : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n =>
        refreshedView codec n before cells coin.1 observe coin.2)
      (fun coin : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n =>
        preparedView codec n before cells coin.1 observe coin.2) :=
    statClose_mix nonnegative
      (fun background => refreshedView codec n before cells background observe)
      (fun background => preparedView codec n before cells background observe)
      (fun background => fixed_statClose codec n before cells atLeastTwo codecInjective background observe)
  apply statClose_reindex (refreshEquiv codec n before cells).symm (Equiv.refl _) _ (fun _ => rfl) mixture
  intro coin
  exact (congrArg
    (fun result : Coins (Salt := Salt) (Enc := Enc) (Digest := Digest) n => observe result.2.1 result.1)
    ((refreshEquiv codec n before cells).apply_symm_apply coin)).symm

end Counting

set_option exponentiation.threshold 1024 in
/-- The current 2443-column profile uses a 320-bit nonce and 256-bit digest.
Only the earlier observer queries enter this preparation term. -/
theorem rate7_error (queries : ℕ) :
    error (2^320) (2^256) 2443 queries =
      (11936498+2443*(queries:ℚ))/(2:ℚ)^320 +
        11929170/(2:ℚ)^256 +
        2442*(queries:ℚ)/(2:ℚ)^512 := by
  unfold error
  push_cast
  norm_num

end LfzkV2.Current.ZeroKnowledge.MerklePreparation
