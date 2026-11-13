import RuntimeHahn.Budget
import RuntimeHahn.Hash
import RuntimeHahn.Signature
import polygero.FiatShamir.Nonrecursive

/-!
Exact counting certificates for the nonrecursive Rust Polygero implementation.
The endpoint is the concrete one-level Polygero verifier in the ideal-binding,
uniform-sampler Fiat-Shamir model. The Rust codec, Merkle binding reduction,
mixed-field privacy, and Longfellow v2 composition are outside this certificate.

Universal profiles retain the field-explicit coefficient 1/q + 2^-129.
The adaptive multiplier is explicit.
The extraction endpoint also permits satisfiable statements depending on
earlier transcript answers, provided its two backend hash answers are held out.
No joint-farness premise is used.
Check against Longfellow's built formal library using zk_tool check-profiles --protocol polygero.
-/
noncomputable section
namespace Polygero.RustHahnProfiles
open Polynomial Finset RecursivePolygero
open scoped Classical
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 0


/-- Sufficient conditions under a declared field-size and per-query budget. -/
structure Profile (n k s t : ℕ) (budget : RuntimeHahn.Budget := .universal) where
  positive : 1 ≤ k
  large : max (k+2*s+1) (2*k+s) ≤ n
  query_pos : 1 ≤ t
  privacy : 2*t < k
  domain : 2*n ≤ 2^128
  query_bound : t ≤ n
  overlap_lt : k+2*s-1 < n
  floor : (((max (k+2*s+1) (2*k+s)-1).choose t : ℚ)/n.choose t) ≤ budget.threshold
  cutoff : ℕ
  count : ℕ
  cutoff_large : max (k+2*s+1) (2*k+s) ≤ cutoff
  cutoff_le_n : cutoff ≤ n
  packing : CodingTheory.UniformFamilyBound n cutoff (k+2*s-1) count
  count_bound : count ≤ budget.minimumField
  active_floor : (((cutoff-1).choose t : ℚ)/n.choose t) ≤ budget.threshold
  condition : DiscreteThreshold.Condition count (((k+2*s-1).choose t : ℚ)/n.choose t) budget.threshold
  rank : (n.choose (k+s+s+1) : ℚ) ≤ (budget.minimumField : ℚ)^s / budget.rankDivisor

variable {budget : RuntimeHahn.Budget}
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private def rankError (n k s q : ℕ) : ℚ := (n.choose (k+s+s+1) : ℚ)/(q : ℚ)^(s+1)

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem rank_bounds {n k s t : ℕ} (p : Profile n k s t budget)
    (hq : budget.minimumField ≤ Nat.card F) :
    rankError n k s (Nat.card F) ≤ budget.rankBudget ∧
    rankError n k s (Nat.card F) ≤ 1/(Nat.card F : ℚ) := by
  simpa only [rankError, RuntimeHahn.Budget.rankError] using budget.rank_bounds p.rank hq

/-- Instantiate the existing Polygero counting theorem with the tuned geometry. -/
def Profile.parameters {n k s t : ℕ} (p : Profile n k s t budget) (I : Instance F)
    (hn : I.n = n) (hk : I.r+I.w = k) (hs : I.s = s) (ht : I.t = t)
    (hq : budget.minimumField ≤ Nat.card F) : HahnSystemCertificate I := by
  have hr := rank_bounds p hq
  have hqmin : (budget.minimumField : ℚ) ≤ Nat.card F := by exact_mod_cast hq
  have hmin0 : (0 : ℚ) < budget.minimumField := by exact_mod_cast budget.field_pos
  let base : ProfileParameters I := {
    positive_degree := by simpa only [hk] using p.positive
    large_le := by simpa only [hn,hk,hs,two_mul,Nat.add_assoc] using p.large
    query_pos := by simpa only [ht] using p.query_pos
    overlap_lt := by simpa only [hn,hk,hs] using p.overlap_lt }
  refine {
    toProfileParameters := base
    columnCutoff := p.cutoff
    listBound := p.count
    threshold := budget.threshold
    large_le_cutoff := by simpa only [ProfileParameters.largeSize,ProfileParameters.coreSize,hn,hk,hs,two_mul,Nat.add_assoc] using p.cutoff_large
    cutoff_le_n := by simpa only [hn] using p.cutoff_le_n
    active_bound := Or.inl (by simpa only [ProfileParameters.overlapSize,hn,hk,hs] using p.packing)
    floor_le := ?_
    threshold_lt_one := budget.threshold_lt_one
    excess_condition := ?_
    field_error_lt_one := ?_ }
  · simpa only [ProfileParameters.columnFloorAt,hn,ht] using p.active_floor
  · apply Or.inr
    apply Or.inr
    rw [min_eq_right (p.count_bound.trans hq)]
    simpa only [ProfileParameters.overlapSize,hn,hk,hs,ht] using p.condition
  · change rankError I.n (I.r+I.w) I.s (Nat.card F)+1/(Nat.card F : ℚ) < 1
    rw [hn,hk,hs]
    have hinv : 1/(Nat.card F : ℚ) ≤ 1/(budget.minimumField : ℚ) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hqmin
    have hsmall : budget.rankBudget + 1/(budget.minimumField : ℚ) < 1 := budget.field_error_lt_one
    linarith [hr.1]

omit [Fintype F] [DecidableEq F] in
private theorem profile_error {n k s t : ℕ} (p : Profile n k s t budget) (I : Instance F)
    (hn : I.n = n) (hk : I.r+I.w = k)
    (hs : I.s = s) (ht : I.t = t)
    (hq : budget.minimumField ≤ Nat.card F) :
    (p.parameters I hn hk hs ht hq).error ≤ 1/(Nat.card F : ℚ)+budget.additiveBudget := by
  have hr := rank_bounds p hq
  change budget.threshold+(1-budget.threshold)*(rankError I.n (I.r+I.w) I.s (Nat.card F)+1/(Nat.card F : ℚ)) ≤ _
  rw [hn,hk,hs]
  have hnonneg : 0 ≤ rankError n k s (Nat.card F) := by unfold rankError; positivity
  have hfield : 0 ≤ 1/(Nat.card F : ℚ) := by positivity
  have hproduct := mul_nonneg budget.threshold_nonneg (add_nonneg hnonneg hfield)
  unfold RuntimeHahn.Budget.additiveBudget
  nlinarith [hr.1]

omit [Fintype F] [DecidableEq F] in
/-- Runtime certificates supply both hypotheses of the adaptive extraction
theorem, with a common 127-bit coefficient for every retained profile. -/
theorem Profile.parameters_bounds {n k s t : ℕ} (p : Profile n k s t budget)
    (I : Instance F) (hn : I.n = n) (hk : I.r+I.w = k)
    (hs : I.s = s) (ht : I.t = t) (hq : budget.minimumField ≤ Nat.card F) :
    (p.parameters I hn hk hs ht hq).rankError ≤ 1/(Nat.card F : ℚ) ∧
      (p.parameters I hn hk hs ht hq).error ≤ 1/(2^127 : ℚ) := by
  constructor
  · simpa only [ProfileParameters.rankError, ProfileParameters.coreSize, hn, hk, hs,
      rankError] using (rank_bounds p hq).2
  · exact (profile_error p I hn hk hs ht hq).trans (budget.per_query_le_127 hq)

/-- Acceptance without extraction for a transcript-dependent backend statement.
Frontend query domains may be included in `Pt`; only the two backend answers
must be excluded from its context. Merkle binding is a separate reduction. -/
theorem Profile.fs_extraction_failure_127 {n k s t : ℕ} (p : Profile n k s t budget)
    (I : Instance F) (hn : I.n = n) (hk : I.r+I.w = k)
    (hs : I.s = s) (ht : I.t = t) (hq : budget.minimumField ≤ Nat.card F)
    {C Pt Out Parent State : Type}
    [Fintype C] [Nonempty C] [Fintype Pt] [DecidableEq Pt] [Fintype Parent]
    {N : ℕ} (tree : Merkle.RandomOracle.Tree Pt C Out N)
    (selected : Out → Parent × I.layer.Payload)
    (parent : Parent → Pt) (child : Parent → I.layer.Payload → Pt)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective (fun i : Parent × I.layer.Payload => child i.1 i.2))
    (hdisjoint : ∀ j j' payload, parent j ≠ child j' payload)
    (state : Parent → (Pt → C) → State)
    (hstateOff : ∀ j payload H H',
      (∀ z, z ≠ parent j → z ≠ child j payload → H z = H' z) → state j H = state j H')
    (statement : State → Parent → I.layer.Statement)
    (oracle : State → Parent → I.layer.Oracle)
    [DecidableEq I.layer.Coin] [DecidableEq I.layer.Query]
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
    (hquery : ∀ Q, (univ.filter fun b : C => decodeQuery b = Q).card ≤ kQuery)
    (hkCoin : kCoin*Fintype.card I.layer.Coin ≤ Fintype.card C)
    (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C) :
    let failure := fun H : Pt → C =>
      let i := selected (tree.run H).1
      let σ := statement (state i.1 H) i.1
      let W := oracle (state i.1 H) i.1
      let coin := decodeCoin (H (parent i.1))
      I.layer.verify σ W coin i.2 (decodeQuery (H (child i.1 i.2))) ∧
        scanRecoverAt I σ W coin i.2 = none
    ((univ.filter failure).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Pt ≤
      (N+1 : ℕ)*(1/(2^127 : ℚ)) := by
  have hb := p.parameters_bounds I hn hk hs ht hq
  exact (NonrecursiveFS.extraction_failure_le I (p.parameters I hn hk hs ht hq) hb.1
    tree selected parent child hparent hchild hdisjoint state hstateOff statement oracle
    decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery).trans
    (mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg _))

abbrev Point (I : Instance F) (Commitment : Type) := Commitment ⊕ (Commitment × I.layer.Payload)
abbrev Answer (I : Instance F) := I.layer.Coin × I.layer.Query

def accepts {Commitment : Type} {N : ℕ} (I : Instance F)
    (σ : I.layer.Statement) (oracle : Commitment → I.layer.Oracle)
    (tree : Merkle.RandomOracle.Tree (Point I Commitment) (Answer I) (Commitment × I.layer.Payload) N)
    (H : Point I Commitment → Answer I) : Prop :=
  let i := (tree.run H).1
  I.layer.verify σ (oracle i.1) (H (.inl i.1)).1 i.2 (H (.inr i)).2

/-- Concrete nonrecursive FS endpoint with the same coefficient budget as the universal profile family. -/
theorem Profile.fs_soundness {n k s t : ℕ} (p : Profile n k s t budget) (I : Instance F)
    (hn : I.n = n) (hk : I.r+I.w = k) (hs : I.s = s) (ht : I.t = t)
    (hq : budget.minimumField ≤ Nat.card F)
    {Commitment : Type} [Fintype Commitment]
    (σ : I.layer.Statement) (hfalse : ∀ w, ¬ I.layer.satisfies σ w)
    (oracle : Commitment → I.layer.Oracle) {N : ℕ}
    (tree : Merkle.RandomOracle.Tree (Point I Commitment) (Answer I) (Commitment × I.layer.Payload) N) :
    ((univ.filter (accepts I σ oracle tree)).card : ℚ)/
      (Fintype.card (Answer I) : ℚ)^Fintype.card (Point I Commitment) ≤
      (N+1 : ℕ)*(1/(Nat.card F : ℚ)+budget.additiveBudget) := by
  let params := p.parameters I hn hk hs ht hq
  have hsmall : params.rankError ≤ 1/(Nat.card F : ℚ) := by
    simpa only [ProfileParameters.rankError,ProfileParameters.coreSize,hn,hk,hs,rankError] using (rank_bounds p hq).2
  have hc (c : I.layer.Coin) :
      (univ.filter fun a : Answer I => a.1 = c).card ≤ Fintype.card I.layer.Query := by
    have he : (univ.filter fun a : Answer I => a.1 = c) = {c} ×ˢ univ := by ext ⟨a,b⟩; simp [eq_comm]
    rw [he,card_product,card_singleton,card_univ,one_mul]
  have hQ (Q : I.layer.Query) :
      (univ.filter fun a : Answer I => a.2 = Q).card ≤ Fintype.card I.layer.Coin := by
    have he : (univ.filter fun a : Answer I => a.2 = Q) = univ ×ˢ {Q} := by ext ⟨a,b⟩; simp [eq_comm]
    rw [he,card_product,card_singleton,card_univ,mul_one]
  exact (NonrecursiveFS.soundness_le I params hsmall tree id Sum.inl (fun j a => Sum.inr (j,a))
    Sum.inl_injective (fun _ _ h => Sum.inr_injective h) (by intro j j' payload h; cases h)
    (fun _ _ => ()) (fun _ _ _ _ _ => rfl) (fun _ _ => σ) (fun _ j => oracle j)
    (fun _ _ => hfalse) Prod.fst Prod.snd (Fintype.card I.layer.Query)
    (Fintype.card I.layer.Coin) hc hQ (by simp [Answer,mul_comm]) (by simp [Answer])).trans
    (mul_le_mul_of_nonneg_left (profile_error p I hn hk hs ht hq) (Nat.cast_nonneg _))


/-- Common per-query FS bound for all retained runtime profiles. Commitment
binding and concrete sampler errors are accounted for by their own reductions. -/
theorem Profile.fs_soundness_127 {n k s t : ℕ} (p : Profile n k s t budget) (I : Instance F)
    (hn : I.n = n) (hk : I.r+I.w = k) (hs : I.s = s) (ht : I.t = t)
    (hq : budget.minimumField ≤ Nat.card F)
    {Commitment : Type} [Fintype Commitment]
    (σ : I.layer.Statement) (hfalse : ∀ w, ¬ I.layer.satisfies σ w)
    (oracle : Commitment → I.layer.Oracle) {N : ℕ}
    (tree : Merkle.RandomOracle.Tree (Point I Commitment) (Answer I) (Commitment × I.layer.Payload) N) :
    ((univ.filter (accepts I σ oracle tree)).card : ℚ)/
      (Fintype.card (Answer I) : ℚ)^Fintype.card (Point I Commitment) ≤
      (N+1 : ℕ)*(1/(2^127 : ℚ)) := by
  exact (p.fs_soundness I hn hk hs ht hq σ hfalse oracle tree).trans
    (mul_le_mul_of_nonneg_left (budget.per_query_le_127 hq) (Nat.cast_nonneg _))

namespace Hash
def profile : Profile 3584 512 18 87 .universal where
  positive := by decide
  large := by decide
  query_pos := by decide
  overlap_lt := by decide
  cutoff_large := by decide
  cutoff_le_n := by decide
  cutoff := 1301
  count := 784573465925695847172202806496161
  packing := RuntimeHahn.Hash.packing
  count_bound := by decide
  active_floor := by norm_num [RuntimeHahn.Budget.threshold,RuntimeHahn.Budget.minimumField,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]
  condition := ⟨1, by decide, by decide, by
    norm_num [DiscreteThreshold.candidate,RuntimeHahn.Budget.threshold,RuntimeHahn.Budget.minimumField,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]⟩
  privacy := by decide
  domain := by decide
  query_bound := by decide
  floor := by norm_num [RuntimeHahn.Budget.threshold,RuntimeHahn.Budget.minimumField,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]
  rank := by norm_num [RuntimeHahn.Budget.minimumField,RuntimeHahn.Budget.rankDivisor,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]
end Hash

namespace Signature
def profile : Profile 2912 416 15 86 .universal where
  positive := by decide
  large := by decide
  query_pos := by decide
  overlap_lt := by decide
  cutoff_large := by decide
  cutoff_le_n := by decide
  cutoff := 1050
  count := 35399303759672813850417310351178
  packing := RuntimeHahn.Signature.packing
  count_bound := by decide
  active_floor := by norm_num [RuntimeHahn.Budget.threshold,RuntimeHahn.Budget.minimumField,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]
  condition := ⟨1, by decide, by decide, by
    norm_num [DiscreteThreshold.candidate,RuntimeHahn.Budget.threshold,RuntimeHahn.Budget.minimumField,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]⟩
  privacy := by decide
  domain := by decide
  query_bound := by decide
  floor := by norm_num [RuntimeHahn.Budget.threshold,RuntimeHahn.Budget.minimumField,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]
  rank := by norm_num [RuntimeHahn.Budget.minimumField,RuntimeHahn.Budget.rankDivisor,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]
end Signature

theorem hash_fs_soundness (I : Instance F)
    (hn : I.n = 3584) (hk : I.r+I.w = 512)
    (hs : I.s = 18) (ht : I.t = 87)
    (hq : 2^128 ≤ Nat.card F)
    {Commitment : Type} [Fintype Commitment]
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    (oracle : Commitment → I.layer.Oracle) {N : ℕ}
    (tree : Merkle.RandomOracle.Tree (Point I Commitment) (Answer I)
      (Commitment × I.layer.Payload) N) :
    ((univ.filter (accepts I σ oracle tree)).card : ℚ)/
      (Fintype.card (Answer I) : ℚ)^Fintype.card (Point I Commitment) ≤
      (N+1 : ℕ)*(1/(Nat.card F : ℚ)+1/2^129) := by
  simpa only [RuntimeHahn.Budget.additiveBudget_universal] using
    Hash.profile.fs_soundness I hn hk hs ht hq σ hfalse oracle tree

theorem signature_fs_soundness (I : Instance F)
    (hn : I.n = 2912) (hk : I.r+I.w = 416)
    (hs : I.s = 15) (ht : I.t = 86)
    (hq : 2^128 ≤ Nat.card F)
    {Commitment : Type} [Fintype Commitment]
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    (oracle : Commitment → I.layer.Oracle) {N : ℕ}
    (tree : Merkle.RandomOracle.Tree (Point I Commitment) (Answer I)
      (Commitment × I.layer.Payload) N) :
    ((univ.filter (accepts I σ oracle tree)).card : ℚ)/
      (Fintype.card (Answer I) : ℚ)^Fintype.card (Point I Commitment) ≤
      (N+1 : ℕ)*(1/(Nat.card F : ℚ)+1/2^129) := by
  simpa only [RuntimeHahn.Budget.additiveBudget_universal] using
    Signature.profile.fs_soundness I hn hk hs ht hq σ hfalse oracle tree

end Polygero.RustHahnProfiles
end

open Lean Elab Command
run_cmd do
  for endpoint in #[``Polygero.RustHahnProfiles.Profile.fs_extraction_failure_127,
      ``Polygero.RustHahnProfiles.Profile.fs_soundness_127,
      ``Polygero.RustHahnProfiles.hash_fs_soundness, ``Polygero.RustHahnProfiles.signature_fs_soundness] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom in Hahn verifier endpoint {endpoint}: {ax}"
