import polygero.FiatShamir.Nonrecursive

/-!
Exact counting certificates for the nonrecursive Rust Polygero implementation.
The endpoint is the concrete one-level Polygero verifier in the ideal-binding,
uniform-sampler Fiat-Shamir model. The Rust codec, Merkle binding reduction,
mixed-field privacy, and Longfellow v2 composition are outside this certificate.

For fields of size q at least 2^128, the one-level coefficient is at most
1/q + 2^-129. The adaptive
random-oracle multiplier is explicit. No joint-farness premise is used.
Check against Longfellow's built formal library using zk_tool check-profiles --protocol polygero.
-/
noncomputable section
namespace Polygero.RustProfiles
open Polynomial Finset RecursivePolygero
open scoped Classical
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def theta : ℚ := 1 / 2^130

/-- Sufficient, field-independent conditions used by the bounded parameter tuner. -/
structure Profile (n k s t : ℕ) : Prop where
  positive : 1 ≤ k
  large : max (k+2*s+1) (2*k+s) ≤ n
  query_pos : 1 ≤ t
  privacy : 2*t < k
  domain : 2*n ≤ 2^128
  query_bound : t ≤ n
  overlap_lt : k+2*s-1 < n
  floor : (((max (k+2*s+1) (2*k+s)-1).choose t : ℚ)/n.choose t) ≤ theta
  overlap : (((k+2*s-1).choose t : ℚ)/n.choose t) ≤ theta^2
  rank : (n.choose (k+s+s+1) : ℚ) ≤ (2^128 : ℚ)^s / 4

/-- A second-moment overlap budget supplies the existing discrete certificate.
The ceiling selects one integer incidence cutoff; it does not modify the verifier. -/
private theorem condition_of_square {q : ℕ} {p θ : ℚ}
    (hq : 2 ≤ q) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hp : p ≤ θ^2) :
    DiscreteThreshold.Condition q p θ := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  let a : ℚ := ((q : ℚ)-1)*θ
  let u : ℕ := ⌈a⌉₊
  have ha : 0 < a := mul_pos (by linarith) hθ
  have hu : 1 ≤ u := Nat.one_le_ceil_iff.mpr ha
  have huaq : a ≤ (u : ℚ) := Nat.le_ceil a
  have hual : (u : ℚ) < a+1 := Nat.ceil_lt_add_one ha.le
  have huq : u ≤ q := Nat.ceil_le.mpr (by dsimp [a]; nlinarith)
  refine ⟨u,hu,huq,?_⟩
  have hu0 : (0 : ℚ) < u := by exact_mod_cast hu
  have hqm : (0 : ℚ) < q-1 := by linarith
  have hδ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr huaq)
    (show (u : ℚ)-a-1 ≤ 0 by linarith)
  have haθ : 0 ≤ a*(1-θ) := mul_nonneg ha.le (by linarith)
  have hp' := mul_le_mul_of_nonneg_left hp
    (show (0 : ℚ) ≤ q*(q-1) by positivity)
  have hb : (u : ℚ)*(u-1)+(q : ℚ)*(q-1)*p ≤ 2*(q-1)*u*θ := by
    dsimp [a] at hδ haθ
    nlinarith
  unfold DiscreteThreshold.candidate
  apply (le_of_sub_nonpos ?_)
  have he : ((u : ℚ)-1)/(2*(q-1))+(q : ℚ)*p/(2*u)-θ =
      ((u : ℚ)*(u-1)+(q : ℚ)*(q-1)*p-2*(q-1)*u*θ)/(2*(q-1)*u) := by
    field_simp
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private def rankError (n k s q : ℕ) : ℚ := (n.choose (k+s+s+1) : ℚ)/(q : ℚ)^(s+1)

omit [DecidableEq F] in
private theorem rank_bounds {n k s t : ℕ} (p : Profile n k s t)
    (hq : 2^128 ≤ Nat.card F) :
    rankError n k s (Nat.card F) ≤ theta ∧
    rankError n k s (Nat.card F) ≤ 1/(Nat.card F : ℚ) := by
  have hq0 : (0 : ℚ) < Nat.card F := by exact_mod_cast Nat.card_pos (α := F)
  have hqmin : (2^128 : ℚ) ≤ Nat.card F := by exact_mod_cast hq
  have hp : (2^128 : ℚ)^s ≤ (Nat.card F : ℚ)^s :=
    pow_le_pow_left₀ (by positivity) hqmin _
  have hnum : (n.choose (k+s+s+1) : ℚ) ≤ (Nat.card F : ℚ)^s / 4 :=
    p.rank.trans (div_le_div_of_nonneg_right hp (by norm_num))
  have hquot : (n.choose (k+s+s+1) : ℚ)/(Nat.card F : ℚ)^s ≤ 1/4 := by
    apply (div_le_iff₀ (pow_pos hq0 _)).mpr
    linarith
  have hr : rankError n k s (Nat.card F) ≤ (1/4)/(Nat.card F : ℚ) := by
    unfold rankError
    rw [pow_succ, div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hquot hq0.le
  constructor
  · apply hr.trans
    apply (div_le_div_of_nonneg_left (by norm_num : (0:ℚ) ≤ 1/4)
      (by positivity : (0:ℚ) < 2^128) hqmin).trans_eq
    norm_num [theta]
  · exact hr.trans (div_le_div_of_nonneg_right (by norm_num) hq0.le)

/-- Instantiate the existing Polygero counting theorem with the tuned geometry. -/
def Profile.parameters {n k s t : ℕ} (p : Profile n k s t) (I : Instance F)
    (hn : I.n = n) (hk : I.r+I.w = k) (hs : I.s = s) (ht : I.t = t)
    (hq : 2^128 ≤ Nat.card F) : HahnSystemCertificate I := by
  have hr := rank_bounds p hq
  have hqmin : (2^128 : ℚ) ≤ Nat.card F := by exact_mod_cast hq
  let base : ProfileParameters I := {
    positive_degree := by simpa only [hk] using p.positive
    large_le := by simpa only [hn,hk,hs,two_mul,Nat.add_assoc] using p.large
    query_pos := by simpa only [ht] using p.query_pos
    overlap_lt := by simpa only [hn,hk,hs] using p.overlap_lt }
  refine {
    toProfileParameters := base
    columnCutoff := base.largeSize
    listBound := Nat.card F
    threshold := theta
    large_le_cutoff := le_rfl
    cutoff_le_n := base.large_le
    active_bound := Or.inr le_rfl
    floor_le := ?_
    threshold_lt_one := by norm_num [theta]
    excess_condition := ?_
    field_error_lt_one := ?_ }
  · simpa only [ProfileParameters.columnFloorAt,ProfileParameters.largeSize,
      ProfileParameters.coreSize,hn,hk,hs,ht,two_mul,Nat.add_assoc] using p.floor
  · apply Or.inr
    apply Or.inr
    rw [min_self]
    apply condition_of_square (by omega : 2 ≤ Nat.card F)
      (by norm_num [theta]) (by norm_num [theta])
    simpa only [ProfileParameters.overlapSize,hn,hk,hs,ht] using p.overlap
  · change rankError I.n (I.r+I.w) I.s (Nat.card F)+1/(Nat.card F : ℚ) < 1
    rw [hn,hk,hs]
    have hinv : 1/(Nat.card F : ℚ) ≤ 1/(2^128 : ℚ) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hqmin
    have hsmall : theta + 1/(2^128 : ℚ) < 1 := by norm_num [theta]
    linarith [hr.1]

omit [DecidableEq F] in
private theorem profile_error {n k s t : ℕ} (p : Profile n k s t) (I : Instance F)
    (hn : I.n = n) (hk : I.r+I.w = k) (hs : I.s = s) (ht : I.t = t)
    (hq : 2^128 ≤ Nat.card F) :
    (p.parameters I hn hk hs ht hq).error ≤ 1/(Nat.card F : ℚ)+1/2^129 := by
  have hr := (rank_bounds p hq).1
  change theta+(1-theta)*(rankError I.n (I.r+I.w) I.s (Nat.card F)+1/(Nat.card F : ℚ)) ≤ _
  rw [hn,hk,hs]
  have hnonneg : 0 ≤ rankError n k s (Nat.card F) := by unfold rankError; positivity
  have hfield : 0 ≤ 1/(Nat.card F : ℚ) := by positivity
  have htheta : 0 ≤ theta := by norm_num [theta]
  have hsum : theta+theta = (1:ℚ)/2^129 := by norm_num [theta]
  nlinarith

abbrev Point (I : Instance F) (Commitment : Type) := Commitment ⊕ (Commitment × I.layer.Payload)
abbrev Answer (I : Instance F) := I.layer.Coin × I.layer.Query

def accepts {Commitment : Type} {N : ℕ} (I : Instance F)
    (σ : I.layer.Statement) (oracle : Commitment → I.layer.Oracle)
    (tree : Merkle.RandomOracle.Tree (Point I Commitment) (Answer I) (Commitment × I.layer.Payload) N)
    (H : Point I Commitment → Answer I) : Prop :=
  let i := (tree.run H).1
  I.layer.verify σ (oracle i.1) (H (.inl i.1)).1 i.2 (H (.inr i)).2

/-- Concrete nonrecursive FS endpoint with the same coefficient budget as the universal profile family. -/
theorem Profile.fs_soundness {n k s t : ℕ} (p : Profile n k s t) (I : Instance F)
    (hn : I.n = n) (hk : I.r+I.w = k) (hs : I.s = s) (ht : I.t = t)
    (hq : 2^128 ≤ Nat.card F)
    {Commitment : Type} [Fintype Commitment]
    (σ : I.layer.Statement) (hfalse : ∀ w, ¬ I.layer.satisfies σ w)
    (oracle : Commitment → I.layer.Oracle) {N : ℕ}
    (tree : Merkle.RandomOracle.Tree (Point I Commitment) (Answer I) (Commitment × I.layer.Payload) N) :
    ((univ.filter (accepts I σ oracle tree)).card : ℚ)/
      (Fintype.card (Answer I) : ℚ)^Fintype.card (Point I Commitment) ≤
      (N+1 : ℕ)*(1/(Nat.card F : ℚ)+1/2^129) := by
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

end Polygero.RustProfiles
end

open Lean Elab Command
run_cmd do
  for ax in ← collectAxioms ``Polygero.RustProfiles.Profile.fs_soundness do
    unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
      throwError "Unexpected axiom in Polygero profile endpoint: {ax}"
