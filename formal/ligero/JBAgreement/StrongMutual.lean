import JBAgreement.CertificateMinimum

/-!
# Haböck's strong mutual correlated agreement

`Mutual.lean` proves the *per-line* mutual statement: for the one pair `(v₀, v₁)`
produced by correlated agreement, among parameters close to *that* line at most `e`
see agreement beyond the correlated set.  Haböck's notion (Hab25) is stronger in two
ways: it quantifies over **every** proximate codeword of every parameter — the whole
list, not the designated line point — and it demands each agreement set be
**contained** in the joint agreement set of some *explaining* pair of codewords.

This file proves the exact-certificate strong form.  The pipeline never cared
which proximate is tracked (the interpolant vanishes on the graph of the line,
so *any* `e`-close codeword is a root of every specialisation), so one simply chooses,
for each allegedly bad parameter, one unexplained proximate, and runs the machinery on
those choices (`exists_affine_bucket_of_GS_sharp_noFieldSize`).  On the bucket the chosen proximates
*are* the line `v₀ + z·v₁`; if such a proximate were unexplained even by `(v₀, v₁)`,
its agreement set would exit the correlated set at some coordinate — and by the
one-affine-root lemma each coordinate can serve at most one parameter, so at most
`|pairDisagree| ≤ e` of the `> e + 1` bucket parameters can be bad.  Contradiction.

* `explains` — the pair `(p₀, p₁)` explains the proximate `p` at `z`: it decomposes
  `p` along the line and its joint agreement contains the agreement set of `p`.
* `HasUnexplainedProximate` — `z` admits a dimension-`k` codeword within distance `e`
  of `u₀ + z·u₁` that no pair explains.
* `strong_mutual_unconditional` — no set of such parameters can reach the threshold.
-/

namespace JBAgreement

open Polynomial Finset

section Strong

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(p₀, p₁)` *explains* the proximate `p` of the line point at `z`: it decomposes
`p` along the line, and every coordinate where the line point agrees with `p` is a
coordinate of simultaneous agreement with `(p₀, p₁)`. -/
def explains (dom : ι → F) (u₀ u₁ : ι → F) (z : F) (p p₀ p₁ : F[X]) : Prop :=
  p = p₀ + C z * p₁ ∧
  ∀ x : ι, u₀ x + z * u₁ x = p.eval (dom x) →
    u₀ x = p₀.eval (dom x) ∧ u₁ x = p₁.eval (dom x)

/-- `z` admits an *unexplained proximate*: a dimension-`k` codeword within distance `e`
of `u₀ + z·u₁` that no pair of dimension-`k` codewords explains.  Haböck's mutual
correlated agreement is the statement that few `z` have this property. -/
def HasUnexplainedProximate (dom : ι → F) (u₀ u₁ : ι → F) (k e : ℕ) (z : F) : Prop :=
  ∃ p : F[X], p.natDegree < k ∧
    (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e ∧
    ∀ p₀ p₁ : F[X], p₀.natDegree < k → p₁.natDegree < k →
      ¬ explains dom u₀ u₁ z p p₀ p₁

/-- **Strong mutual correlated agreement, unconditional form.**  A set of parameters
all of which have an unexplained proximate cannot reach the correlated agreement
threshold. -/
theorem strong_mutual_unconditional
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F)
    (hbad : ∀ z ∈ S, HasUnexplainedProximate dom u₀ u₁ k e z)
    (m D dY dZ : ℕ)
    (hkdY : (k - 1) * dY ≤ D)
    (hcnt : Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - (k - 1) * (dY * (dY + 1))) *
          (dZ + 1))
    (hroot : D < m * (Fintype.card ι - e))
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) + dZ + 3 * (dY * dZ) < S.card) :
    False := by
  classical
  -- Choose, for each bad parameter, one unexplained proximate.
  have hchoice : ∀ z : F, ∃ p : F[X], z ∈ S → (p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e ∧
      ∀ p₀ p₁ : F[X], p₀.natDegree < k → p₁.natDegree < k →
        ¬ explains dom u₀ u₁ z p p₀ p₁) := by
    intro z
    by_cases hz : z ∈ S
    · obtain ⟨p, hp⟩ := hbad z hz
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose p hp using hchoice
  -- The Guruswami–Sudan package for these choices.
  obtain ⟨Q, hQ0, hQY, hQX, hQZ, hGS⟩ :=
    exists_gs_for dom hdom u₀ u₁ k e S p (fun z hz => (hp z hz).1)
      (fun z hz => (hp z hz).2.1) m D dY dZ hkdY hcnt hroot
  -- The affine bucket: the chosen proximates are the line on `S'`.
  obtain ⟨v₀, v₁, S', hS'S, hS'card, hdeg₀, hdeg₁, hpz⟩ :=
    exists_affine_bucket_of_GS_sharp_noFieldSize dom hdom u₀ u₁ k e hk S p
      (fun z hz => (hp z hz).1) (fun z hz => (hp z hz).2.1)
      Q hQ0 D dY dZ hQY hQX hQZ hGS hslack hS
  -- Correlated agreement of `(v₀, v₁)` with the words.
  have hE : (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e := by
    refine correlatedAgreement_of_branch dom u₀ u₁ v₀ v₁ e S' hS'card ?_
    intro z hz
    have h := (hp z (hS'S hz)).2.1
    rw [hpz z hz] at h
    exact h
  -- Each bucket parameter, being unexplained even by `(v₀, v₁)`, consumes a
  -- coordinate of the pair-disagreement set.
  have hdeg₀' : v₀.natDegree < k := hdeg₀
  have hdeg₁' : v₁.natDegree < k := hdeg₁
  have hwit : ∀ z ∈ S', ∃ x : ι,
      u₀ x + z * u₁ x = v₀.eval (dom x) + z * v₁.eval (dom x) ∧
      x ∈ pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) := by
    intro z hz
    have hunex := (hp z (hS'S hz)).2.2 v₀ v₁ hdeg₀' hdeg₁'
    have hnall : ¬ ∀ x : ι, u₀ x + z * u₁ x = (p z).eval (dom x) →
        u₀ x = v₀.eval (dom x) ∧ u₁ x = v₁.eval (dom x) := by
      intro hall
      exact hunex ⟨hpz z hz, hall⟩
    push Not at hnall
    obtain ⟨x, hxline, hxnot⟩ := hnall
    refine ⟨x, ?_, ?_⟩
    · rw [hpz z hz] at hxline
      simpa using hxline
    · rw [mem_pairDisagree]
      simp only [RSeval_apply]
      by_cases h0 : u₀ x = v₀.eval (dom x)
      · exact Or.inr (hxnot h0)
      · exact Or.inl h0
  choose xw hxw using fun z (hz : z ∈ S') => hwit z hz
  -- One coordinate per parameter: the witness map is injective on the bucket.
  have hinj : ∀ z (hz : z ∈ S') z' (hz' : z' ∈ S'), xw z hz = xw z' hz' → z = z' := by
    intro z hz z' hz' hxx
    have h1 := hxw z hz
    have h2 := hxw z' hz'
    rw [hxx] at h1
    exact eq_of_mem_pairDisagree h2.2 h1.1 h2.1
  -- Count: the bucket injects into the pair-disagreement set.
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp (by omega : 0 < S'.card)
  haveI : Nonempty ι := ⟨xw z₀ hz₀⟩
  have hcard : S'.card ≤ (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card := by
    have hmap : ∀ z ∈ S', (if hz : z ∈ S' then xw z hz else Classical.arbitrary ι)
        ∈ pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) := by
      intro z hz
      rw [dif_pos hz]
      exact (hxw z hz).2
    refine Finset.card_le_card_of_injOn _ hmap ?_
    intro z hz z' hz' hxx
    rw [Finset.mem_coe] at hz hz'
    simp only [dif_pos hz, dif_pos hz'] at hxx
    exact hinj z hz z' hz' hxx
  omega

end Strong

/-! ### The Johnson-regime statements -/

section Johnson

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- **Strong mutual correlated agreement in the Johnson regime** (Hab25, negative
form): the number of parameters admitting *any* unexplained proximate is below the
correlated agreement threshold — of size `O_ρ(n/η³)` by `johnsonThreshold_le`. -/
theorem strong_mutual_johnson
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ) (η : ℝ)
    (hk2 : 2 ≤ k) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hηn : 1 ≤ η * (Fintype.card ι))
    (ht4 : 4 * η * (Fintype.card ι) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hJ : ((k - 1 : ℕ) : ℝ) * (Fintype.card ι)
        ≤ (((Fintype.card ι - e : ℕ) : ℝ) - 4 * η * (Fintype.card ι)) ^ 2) :
    ((univ.filter fun z => HasUnexplainedProximate dom u₀ u₁ k e z).card : ℝ)
      < johnsonThreshold k (Fintype.card ι) e η := by
  apply lt_of_not_ge
  intro hcon
  set Bad : Finset F := univ.filter fun z => HasUnexplainedProximate dom u₀ u₁ k e z
    with hBad
  obtain ⟨m, D, dY, dZ, hkdY, hcnt, hroot, hslack, hSnat⟩ :=
    johnson_numeric k (Fintype.card ι) e Bad.card η
      hk2 hη hη4 hηn ht4 hJ hcon
  exact strong_mutual_unconditional dom hdom u₀ u₁ k e (by omega) Bad
    (fun z hz => (Finset.mem_filter.mp hz).2) m D dY dZ
    hkdY hcnt hroot hslack hSnat


end Johnson

end JBAgreement
