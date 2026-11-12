import Mathlib.LinearAlgebra.Lagrange
import JBAgreement.Select
import JBAgreement.Mutual
import Mathlib.Data.Real.Basic

/-!
# The end-to-end theorem: correlated agreement from Guruswami–Sudan alone

`correlatedAgreement_of_GS_sharp` is the deliverable: BCIKS correlated agreement in the
Johnson regime, together with Haböck's mutual strengthening, assuming **only** the
Guruswami–Sudan interpolant.  Everything between GS and the conclusion — branch
selection, the inseparable case, the good slice, the finite jet with its ledger, the
resultant counting, the incidence argument, interpolation and the affine endgame — is
proved.

**Assumed** (the hypotheses named `Q`, `hQ0`, `hQY`, `hQX`, `hQZ`, `hGS`): a nonzero
trivariate interpolant of `Y`-degree ≤ `dY`, `X`-degree ≤ `dX`, `Z`-height ≤ `dZ`,
vanishing on the graph of every proximate.  This is exactly the output of
Guruswami–Sudan interpolation applied over `F[Z]` to the line `u₀ + Z·u₁`; `GS.lean`
constructs it for the unconditional theorem.

**Numeric side conditions** (not assumptions, part of the theorem):
* `2·dY·dX < |F|` — room for the good slice; the standard field-size requirement, also
  present in BCIKS (their error term carries a `1/q`).
* the weighted threshold `hS`, whose leading factor capacity is linear in `dY·dZ`
  and therefore has size `O_ρ(n/η³)`.

The flow: `exists_bucket_sharp` (§6.2/§6.6) → `recenter` → `exists_goodCoords_sharp` (§1–§3 via
the ledger) → Frobenius untwisting → Lagrange → §4.  The mutual clause is
`mutual_correlatedAgreement` applied to the produced pair.
-/

namespace JBAgreement

open Polynomial Finset

section EndToEnd

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The total exact factor capacity after summing all fiber factors. -/
def sharpGSBound (k dY dZ : ℕ) : ℕ := 4 * k * (dY * dZ) + dY

/-- **The affine bucket.**  The shared core of the end-to-end theorems: from the GS
data, a pair `(v₀, v₁)` of dimension-`k` polynomials and a sub-bucket `S' ⊆ S` with
`|S'| > e + 1` on which *the chosen proximates are exactly the line*:
`p z = v₀ + z·v₁`.  Everything downstream (plain CA, per-line mutual CA, and the
strong mutual CA of `StrongMutual.lean`) is endgame bookkeeping on this output.

Hypotheses:
* `hpdeg`, `hprox` — for each `z ∈ S` a proximate `p z` with natural degree `< k` within
  distance `e` of the line point `u₀ + z·u₁`;
* `Q, …, hGS` — **the assumed GS interpolant**: nonzero, `Y`-degree ≤ `dY`,
  `X`-degree ≤ `dX`, `Z`-height ≤ `dZ`, with `Q(X, p_z(X), z) = 0` for `z ∈ S`;
* `hfield` — the field is large enough for a good slice;
* `hslack`, `hS` — the weighted threshold, of size `O_ρ(n/η³)`.

Conclusion: a single pair `(v₀, v₁)` of dimension-`k` polynomials with
* **correlated agreement**: `(u₀, u₁)` differs from `(v₀, v₁)` on at most `e`
  coordinates, and
* **mutual correlated agreement** (Haböck): on any parameter set where the line stays
  `e`-close to the line of `(v₀, v₁)`, at most `e` parameters see any agreement beyond
  the correlated agreement set. -/
theorem exists_affine_bucket_of_GS_sharp
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hfield : 2 * dY * dX < Fintype.card F)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * sharpGSBound k dY dZ /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ (v₀ v₁ : F[X]) (S' : Finset F), S' ⊆ S ∧ e + 1 < S'.card ∧
      v₀.natDegree < k ∧ v₁.natDegree < k ∧
      ∀ z ∈ S', p z = v₀ + C z * v₁ := by
  -- ### The bucket.
  obtain ⟨S', N, d', Sf, x₀, H, hS'S, hS'card, ⟨f, hNf⟩, hd'1, hSfd', hd'N, hSfZ,
    hirrH, hHdeg, hHd', hHZ, hHZexact, hcount, hper⟩ :=
    exists_bucket_sharp S p Q hQ0 dX dY dZ hQY hQX hQZ hGS hfield k
      (Fintype.card ι - k) e (Fintype.card ι - e - k) hslack hS
  set pc := ringChar F with hpc
  haveI hpcP : Fact pc.Prime := ⟨CharP.char_is_prime F pc⟩
  have hN1 : 1 ≤ N := by
    rw [hNf]
    exact Nat.one_le_pow _ _ hpcP.out.pos
  -- ### The twisted data.
  set κ := k * N with hκ
  set q : F → F[X] := fun z => (p z) ^ N with hq
  set w₀ : ι → F := fun x => (u₀ x) ^ N with hw₀
  set w₁ : ι → F := fun x => (u₁ x) ^ N with hw₁
  have hFrobinj : Function.Injective (fun c : F => c ^ N) := by
    rw [hNf]
    exact pow_char_pow_injective pc f
  have htwist : ∀ a b z : F, (a + z * b) ^ N = a ^ N + z ^ N * b ^ N := by
    intro a b z
    rw [hNf]
    exact add_mul_pow_char_pow pc f a b z
  -- The twisted proximity: the disagreement sets are literally equal.
  have hproxT : ∀ z ∈ S',
      (disagree (fun x => w₀ x + z ^ N * w₁ x) (RSeval dom (q z))).card ≤ e := by
    intro z hz
    have hset : disagree (fun x => w₀ x + z ^ N * w₁ x) (RSeval dom (q z))
        = disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z)) := by
      ext x
      simp only [mem_disagree, RSeval_apply, hq, hw₀, hw₁, eval_pow]
      rw [← htwist]
      constructor
      · intro hne heq
        exact hne (by rw [heq])
      · intro hne heq
        exact hne (hFrobinj heq)
    rw [hset]
    exact hprox z (hS'S hz)
  -- ### The recentered branch and its inputs.
  set R₀ := recenter x₀ Sf with hR₀
  have hqdeg : ∀ z ∈ S', (q z).natDegree ≤ κ := by
    intro z hz
    rw [hq]
    calc ((p z) ^ N).natDegree ≤ N * (p z).natDegree := natDegree_pow_le
      _ ≤ N * k := Nat.mul_le_mul_left _ (Nat.le_of_lt (hpdeg z (hS'S hz)))
      _ = κ := by rw [hκ]; ring
  have hroot : ∀ z ∈ S',
      (R₀.map (mapRingHom (spec z ((q z).eval x₀)))).eval ((q z).comp (X + C x₀)) = 0 := by
    intro z hz
    exact eval_recenter_spec z x₀ _ Sf (q z) (hper z hz).1
  have hxiB : ∀ z ∈ S', spec z ((q z).eval x₀) (xi R₀ (X : F[X][X])) ≠ 0 := by
    intro z hz
    rw [hR₀, xi_recenter, spec_fiberAt, hasseDeriv_one']
    exact (hper z hz).2.1
  have hH0 : ∀ z ∈ S', spec z ((q z).eval x₀) H = 0 := fun z hz => (hper z hz).2.2
  -- ### The counting hypothesis for the bucket.
  have hcountB : (Fintype.card ι - k) *
      sharpFiberCapacity κ d' dZ N H.natDegree (swap F H).natDegree <
        (Fintype.card ι - e - k) * S'.card := by
    simpa [hκ] using hcount
  -- ### The good coordinates.
  have hκ1 : 1 ≤ κ := by
    rw [hκ]
    exact Nat.mul_pos (by omega) hN1
  obtain ⟨I, hIcard, hgood⟩ :
      ∃ I : Finset ι, k < I.card ∧ ∀ x ∈ I, ∀ z ∈ S',
        (q z).eval (dom x) = w₀ x + z ^ N * w₁ x := by
    apply exists_goodCoords_sharp dom w₀ w₁ k κ e N hκ1 x₀ R₀ d' dZ
      (recenter_natDegree_le x₀ Sf hSfd') hd'1
      (fun j i => recenter_coeff_natDegree x₀ Sf j i)
      (fun j i => recenter_coeff_isHeightLE x₀ Sf hSfZ j i)
      S' q hqdeg hproxT hroot hxiB H hH0 hirrH hHdeg
        H.natDegree (swap F H).natDegree le_rfl hHZexact
    simpa using hcountB
  -- ### Untwist the coordinate values.
  have hgood' : ∀ x ∈ I, ∀ z ∈ S', (p z).eval (dom x) = u₀ x + z * u₁ x := by
    intro x hx z hz
    have h1 := hgood x hx z hz
    rw [hq] at h1
    apply hFrobinj
    show ((p z).eval (dom x)) ^ N = (u₀ x + z * u₁ x) ^ N
    rw [htwist, ← eval_pow]
    exact h1
  -- ### Lagrange interpolation through `k` good coordinates.
  obtain ⟨T, hTI, hTcard⟩ := Finset.exists_subset_card_eq (n := k) (s := I) (by omega)
  set v₀ : F[X] := Lagrange.interpolate T dom u₀ with hv₀
  set v₁ : F[X] := Lagrange.interpolate T dom u₁ with hv₁
  have hinj : Set.InjOn dom ↑T := hdom.injOn
  have hdeg₀ : v₀.natDegree < k := by
    have h := Lagrange.degree_interpolate_lt (r := u₀) hinj
    rw [hTcard] at h
    rcases eq_or_ne v₀ 0 with hv | hv
    · simpa [hv] using (show 0 < k by omega)
    · exact (natDegree_lt_iff_degree_lt hv).mpr h
  have hdeg₁ : v₁.natDegree < k := by
    have h := Lagrange.degree_interpolate_lt (r := u₁) hinj
    rw [hTcard] at h
    rcases eq_or_ne v₁ 0 with hv | hv
    · simpa [hv] using (show 0 < k by omega)
    · exact (natDegree_lt_iff_degree_lt hv).mpr h
  have hpz : ∀ z ∈ S', p z = v₀ + C z * v₁ := by
    intro z hz
    have hdegsum : (v₀ + C z * v₁).natDegree < k := by
      refine (natDegree_add_le _ _).trans_lt (max_lt hdeg₀ ?_)
      exact (natDegree_C_mul_le _ _).trans_lt hdeg₁
    refine eq_of_eval_eq_of_degree_le
      (natDegree_le_iff_degree_le.mp (Nat.le_pred_of_lt (hpdeg z (hS'S hz))))
      (natDegree_le_iff_degree_le.mp (Nat.le_pred_of_lt hdegsum))
      (T.image dom) ?_ ?_
    · rw [Finset.card_image_of_injective _ hdom, hTcard]
      rw [Nat.pred_eq_sub_one, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    · intro y hy
      obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hy
      rw [eval_add, eval_mul, eval_C, hv₀, hv₁,
        Lagrange.eval_interpolate_at_node _ hinj hxT,
        Lagrange.eval_interpolate_at_node _ hinj hxT]
      exact hgood' x (hTI hxT) z hz
  exact ⟨v₀, v₁, S', hS'S, by omega, hdeg₀, hdeg₁, hpz⟩

/-- **Sharp end-to-end correlated agreement.**  The derivative-sensitive branch
ledger gives total capacity `4k·dY·dZ+dY`. -/
theorem correlatedAgreement_of_GS_sharp
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hfield : 2 * dY * dX < Fintype.card F)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
      (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e ∧
      (∀ S₂ : Finset F, e + 1 < S₂.card →
        (∀ z ∈ S₂, (disagree (fun x => u₀ x + z * u₁ x)
            (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) →
        (S₂.filter fun z =>
          lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z
            ≠ corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e) := by
  obtain ⟨v₀, v₁, S', hS'S, hS'card, hdeg₀, hdeg₁, hpz⟩ :=
    exists_affine_bucket_of_GS_sharp dom hdom u₀ u₁ k e hk S p hpdeg hprox Q hQ0
      dX dY dZ hQY hQX hQZ hGS hfield hslack hS
  refine ⟨v₀, v₁, hdeg₀, hdeg₁, ?_, ?_⟩
  · refine correlatedAgreement_of_branch dom u₀ u₁ v₀ v₁ e S' hS'card ?_
    intro z hz
    have h := hprox z (hS'S hz)
    rw [hpz z hz] at h
    exact h
  · intro S₂ hS₂ hagree
    exact mutual_correlatedAgreement dom u₀ u₁ v₀ v₁ e S₂ hS₂ hagree

end EndToEnd

/-! ### The eta-cubed size of the sharp factor capacity -/

/-- The summed factor capacity is `O(k/eta³)` when `dY = O(1/eta)` and
 dZ is O(1/eta^2).  This is the bound used by the weighted selector. -/
theorem sharpGSThreshold_le {k dY dZ : ℕ} {η c₁ c₂ : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hDY : (dY : ℝ) ≤ c₁ / η) (hDZ : (dZ : ℝ) ≤ c₂ / η ^ 2) :
    (sharpGSBound k dY dZ : ℝ) ≤
      (4 * (k : ℕ) * c₁ * c₂ + c₁) / η ^ 3 := by
  have hDY' : (dY : ℝ) * η ≤ c₁ := (le_div_iff₀ hη).mp hDY
  have hDZ' : (dZ : ℝ) * η ^ 2 ≤ c₂ := (le_div_iff₀ (by positivity)).mp hDZ
  have hc₁ : 0 ≤ c₁ := le_trans (by positivity) hDY'
  have hc₂ : 0 ≤ c₂ := le_trans (by positivity) hDZ'
  have hprod : (dY : ℝ) * dZ * η ^ 3 ≤ c₁ * c₂ := by
    calc (dY : ℝ) * dZ * η ^ 3 = ((dY : ℝ) * η) * ((dZ : ℝ) * η ^ 2) := by ring
      _ ≤ c₁ * c₂ := mul_le_mul hDY' hDZ' (by positivity) hc₁
  have hlinear : (dY : ℝ) * η ^ 3 ≤ c₁ := by
    have hη2 : η ^ 2 ≤ 1 := by nlinarith
    calc (dY : ℝ) * η ^ 3 = ((dY : ℝ) * η) * η ^ 2 := by ring
      _ ≤ c₁ * 1 := mul_le_mul hDY' hη2 (by positivity) hc₁
      _ = c₁ := by ring
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < η ^ 3)]
  have hcast : (sharpGSBound k dY dZ : ℝ) =
      4 * (k : ℝ) * ((dY : ℝ) * dZ) + dY := by
    rw [sharpGSBound]
    push_cast
    ring
  rw [hcast]
  calc (4 * (k : ℝ) * ((dY : ℝ) * dZ) + dY) * η ^ 3
      = 4 * (k : ℝ) * ((dY : ℝ) * dZ * η ^ 3) +
          (dY : ℝ) * η ^ 3 := by ring
    _ ≤ 4 * (k : ℝ) * (c₁ * c₂) + c₁ :=
      add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity)) hlinear
    _ = 4 * (k : ℕ) * c₁ * c₂ + c₁ := by ring

end JBAgreement
