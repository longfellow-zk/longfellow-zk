import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Combinatorial core of the finite-jet correlated agreement proof

This file develops the two purely combinatorial counting arguments of the
finite-jet reorganisation of the BCIKS Johnson-regime correlated agreement
theorem.  Neither depends on any algebraic geometry, so both are proved outright.

* `incidence_bound` / `card_exceptional_ge` are §3 of the plan: they replace the
  popular-coordinate bookkeeping of BCIKS Claims 5.10--5.11 by a single incidence
  inequality.

* `eq_of_mem_pairDisagree` and `card_pairDisagree_le` are §4: the elementary
  endgame, one affine root per coordinate.  The same lemma carries Haböck's
  upgrade to mutual correlated agreement.
-/

namespace JBAgreement

open Finset

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι]

/-! ### Disagreement sets -/

/-- Coordinates at which `u` and `v` differ. -/
def disagree (u v : ι → F) : Finset ι := univ.filter fun x => u x ≠ v x

/-- Coordinates at which the pair `(u₀, u₁)` differs from `(v₀, v₁)`.
This is the set `E` of §4 of the plan. -/
def pairDisagree (u₀ u₁ v₀ v₁ : ι → F) : Finset ι :=
  univ.filter fun x => u₀ x ≠ v₀ x ∨ u₁ x ≠ v₁ x

omit [Field F] in
@[simp] lemma mem_disagree {u v : ι → F} {x : ι} : x ∈ disagree u v ↔ u x ≠ v x := by
  simp [disagree]

omit [Field F] in
@[simp] lemma mem_pairDisagree {u₀ u₁ v₀ v₁ : ι → F} {x : ι} :
    x ∈ pairDisagree u₀ u₁ v₀ v₁ ↔ (u₀ x ≠ v₀ x ∨ u₁ x ≠ v₁ x) := by
  simp [pairDisagree]

/-! ### §4: one affine root per coordinate -/

/-- At a coordinate where the pair `(u₀, u₁)` differs from `(v₀, v₁)`, the equation
`u₀ x + z * u₁ x = v₀ x + z * v₁ x` is a *nontrivial* affine equation in `z`, so it
has at most one solution.

This single fact is the whole endgame: it is what stops a bad parameter `z` from
manufacturing agreement outside the genuine correlated agreement set. -/
theorem eq_of_mem_pairDisagree {u₀ u₁ v₀ v₁ : ι → F} {x : ι}
    (hx : x ∈ pairDisagree u₀ u₁ v₀ v₁) {z z' : F}
    (hz : u₀ x + z * u₁ x = v₀ x + z * v₁ x)
    (hz' : u₀ x + z' * u₁ x = v₀ x + z' * v₁ x) :
    z = z' := by
  have hb : (z - z') * (u₁ x - v₁ x) = 0 := by linear_combination hz - hz'
  rcases mul_eq_zero.mp hb with h | h
  · exact sub_eq_zero.mp h
  · have h₁ : u₁ x = v₁ x := sub_eq_zero.mp h
    have h₀ : u₀ x = v₀ x := by linear_combination hz - z * h₁
    rw [mem_pairDisagree] at hx
    rcases hx with hx | hx
    · exact absurd h₀ hx
    · exact absurd h₁ hx

/-- **Endgame of correlated agreement (§4).**

Suppose every point `u₀ + z • u₁` of the line, for `z` ranging over `S`, differs
from the corresponding point `v₀ + z • v₁` of a *fixed* line of codewords in at most
`e` coordinates.  If `|S| > e + 1`, then the pair `(u₀, u₁)` already differs from
`(v₀, v₁)` in at most `e` coordinates — i.e. correlated agreement holds.

The proof is a disjointness count: the sets of coordinates in `E` where the parameter
`z` produces an *accidental* agreement are pairwise disjoint as `z` varies, by
`eq_of_mem_pairDisagree`, yet each has size at least `|E| - e`. -/
theorem card_pairDisagree_le {u₀ u₁ v₀ v₁ : ι → F} {e : ℕ} {S : Finset F}
    [DecidableEq ι]
    (hdis : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (fun x => v₀ x + z * v₁ x)).card ≤ e)
    (hS : e + 1 < S.card) :
    (pairDisagree u₀ u₁ v₀ v₁).card ≤ e := by
  apply Nat.le_of_not_lt
  intro hcon
  set E : Finset ι := pairDisagree u₀ u₁ v₀ v₁ with hEdef
  -- `A z` : coordinates of `E` where the parameter `z` accidentally produces agreement.
  set A : F → Finset ι := fun z =>
    E.filter fun x => u₀ x + z * u₁ x = v₀ x + z * v₁ x with hAdef
  have hAsub : ∀ z, A z ⊆ E := fun z => filter_subset _ _
  -- Disjointness: a coordinate of `E` admits at most one such `z`.
  have hdisj : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → Disjoint (A z) (A z') := by
    intro z _ z' _ hne
    rw [Finset.disjoint_left]
    intro x hxz hxz'
    rw [hAdef] at hxz hxz'
    simp only [mem_filter] at hxz hxz'
    exact hne (eq_of_mem_pairDisagree hxz.1 hxz.2 hxz'.2)
  -- Each `A z` is large: outside it, `z` genuinely disagrees.
  have hlow : ∀ z ∈ S, E.card - e ≤ (A z).card := by
    intro z hz
    have hsub : E \ A z ⊆
        disagree (fun x => u₀ x + z * u₁ x) (fun x => v₀ x + z * v₁ x) := by
      intro x hx
      rw [mem_sdiff, hAdef] at hx
      simp only [mem_filter, not_and] at hx
      simp only [mem_disagree]
      exact hx.2 hx.1
    have hcard : (E \ A z).card = E.card - (A z).card := card_sdiff_of_subset (hAsub z)
    have := (card_le_card hsub).trans (hdis z hz)
    omega
  -- Double count.
  have hbi : (S.biUnion A).card = ∑ z ∈ S, (A z).card := card_biUnion hdisj
  have hle : ∑ z ∈ S, (A z).card ≤ E.card := by
    rw [← hbi]
    exact card_le_card fun x hx => by
      obtain ⟨z, _, hz⟩ := mem_biUnion.mp hx
      exact hAsub z hz
  have hge : S.card * (E.card - e) ≤ ∑ z ∈ S, (A z).card := by
    calc S.card * (E.card - e) = ∑ _z ∈ S, (E.card - e) := by
          rw [sum_const, smul_eq_mul]
      _ ≤ ∑ z ∈ S, (A z).card := sum_le_sum hlow
  have hkey : S.card * (E.card - e) ≤ E.card := hge.trans hle
  -- Arithmetic: with `E.card = e + t`, `t ≥ 1`, this forces `S.card ≤ e + 1`.
  obtain ⟨t, ht, hEt⟩ : ∃ t, 1 ≤ t ∧ E.card = e + t := ⟨E.card - e, by omega, by omega⟩
  rw [hEt] at hkey
  have hsimp : e + t - e = t := by omega
  rw [hsimp] at hkey
  nlinarith [hkey, ht, hS]

/-! ### §3: the incidence inequality

This replaces the BCIKS "most popular coordinates" bookkeeping (Claims 5.10-5.11)
by a single double count. -/

section Incidence

variable {α β : Type*} [Fintype α] [DecidableEq α]

/-- **Abstract incidence bound.**

`P x z` is an incidence relation between coordinates and parameters.  If every
parameter `z ∈ S` is incident to at least `a` coordinates (a *row* bound), and every
coordinate outside an exceptional set `I` is incident to at most `B` parameters (a
*column* bound), then

`a * |S| ≤ |I| * |S| + (n - |I|) * B`. -/
theorem incidence_bound (S : Finset β) (I : Finset α) (P : α → β → Prop)
    [∀ x z, Decidable (P x z)] (a B : ℕ)
    (hrow : ∀ z ∈ S, a ≤ (univ.filter fun x => P x z).card)
    (hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B) :
    a * S.card ≤ I.card * S.card + (Fintype.card α - I.card) * B := by
  -- Count incidences both ways.
  have hfubini : ∑ z ∈ S, (univ.filter fun x => P x z).card
      = ∑ x : α, (S.filter fun z => P x z).card := by
    simp_rw [card_filter]
    exact sum_comm
  -- Row bound.
  have hrowsum : a * S.card ≤ ∑ z ∈ S, (univ.filter fun x => P x z).card := by
    calc a * S.card = ∑ _z ∈ S, a := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum hrow
  -- Column bound, split along `I`.
  have hIsub : I ⊆ univ := subset_univ I
  have hsplit : ∑ x : α, (S.filter fun z => P x z).card
      = (∑ x ∈ I, (S.filter fun z => P x z).card)
        + ∑ x ∈ univ \ I, (S.filter fun z => P x z).card := by
    rw [← sum_union (disjoint_sdiff)]
    congr 1
    exact (union_sdiff_of_subset hIsub).symm
  have hI : (∑ x ∈ I, (S.filter fun z => P x z).card) ≤ I.card * S.card := by
    calc (∑ x ∈ I, (S.filter fun z => P x z).card) ≤ ∑ _x ∈ I, S.card :=
          sum_le_sum fun x _ => card_filter_le _ _
      _ = I.card * S.card := by rw [sum_const, smul_eq_mul]
  have hout : (∑ x ∈ univ \ I, (S.filter fun z => P x z).card)
      ≤ (Fintype.card α - I.card) * B := by
    have hcardsdiff : (univ \ I).card = Fintype.card α - I.card := by
      rw [card_sdiff_of_subset hIsub, card_univ]
    calc (∑ x ∈ univ \ I, (S.filter fun z => P x z).card) ≤ ∑ _x ∈ univ \ I, B :=
          sum_le_sum fun x hx => hcol x (mem_sdiff.mp hx).2
      _ = (univ \ I).card * B := by rw [sum_const, smul_eq_mul]
      _ = (Fintype.card α - I.card) * B := by rw [hcardsdiff]
  omega

/-- **The exceptional set carries more than `k` incidences per parameter on
average.**

This is the mass form of `card_exceptional_ge`.  Under the same strict
incidence budget, it retains the information discarded by the cardinality
conclusion: the total number of incidences *inside* `I` is greater than
`k * |S|`.  In particular, the conclusion is useful when the points of `I`
are selected agreement columns rather than generic identity columns. -/
theorem exceptional_incidence_mass_gt
    (S : Finset β) (I : Finset α) (P : α → β → Prop)
    [∀ x z, Decidable (P x z)] (a k B : ℕ) (hka : k ≤ a)
    (hrow : ∀ z ∈ S, a ≤ (univ.filter fun x => P x z).card)
    (hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B)
    (hS : Fintype.card α * B < (a - k) * S.card) :
    k * S.card < ∑ z ∈ S, (I.filter fun x => P x z).card := by
  have hfubini : ∑ z ∈ S, (univ.filter fun x => P x z).card =
      ∑ x : α, (S.filter fun z => P x z).card := by
    simp_rw [card_filter]
    exact sum_comm
  have hrowsum : a * S.card ≤
      ∑ z ∈ S, (univ.filter fun x => P x z).card := by
    calc
      a * S.card = ∑ _z ∈ S, a := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum hrow
  have hIsub : I ⊆ univ := subset_univ I
  have hsplit : ∑ x : α, (S.filter fun z => P x z).card =
      (∑ x ∈ I, (S.filter fun z => P x z).card) +
        ∑ x ∈ univ \ I, (S.filter fun z => P x z).card := by
    rw [← sum_union (disjoint_sdiff)]
    congr 1
    exact (union_sdiff_of_subset hIsub).symm
  have hout : (∑ x ∈ univ \ I, (S.filter fun z => P x z).card) ≤
      Fintype.card α * B := by
    calc
      (∑ x ∈ univ \ I, (S.filter fun z => P x z).card) ≤
          ∑ _x ∈ univ \ I, B :=
        sum_le_sum fun x hx => hcol x (mem_sdiff.mp hx).2
      _ = (univ \ I).card * B := by rw [sum_const, smul_eq_mul]
      _ ≤ Fintype.card α * B := by
        exact Nat.mul_le_mul_right B
          (card_le_card (subset_univ (univ \ I)))
  have hinside : a * S.card ≤
      (∑ x ∈ I, (S.filter fun z => P x z).card) +
        Fintype.card α * B := by
    rw [hfubini, hsplit] at hrowsum
    omega
  have hfubiniI : ∑ x ∈ I, (S.filter fun z => P x z).card =
      ∑ z ∈ S, (I.filter fun x => P x z).card := by
    simp_rw [card_filter]
    exact sum_comm
  rw [hfubiniI] at hinside
  have hak : k * S.card + (a - k) * S.card = a * S.card := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hka]
  omega

/-- **Surplus incidence mass survives deletion of an arbitrary core.**

Suppose the strict detector budget is run with cutoff `k+s`, so the
exceptional set carries more than `(k+s)|S|` incidences.  Deleting any
`k`-element core can remove at most `k|S|` of them, leaving more than
`s|S|` incidences on `I \ K`.

This is the quantitative form needed for a singular-anchor core: the columns
of `K` may have completely unbounded occupancy. -/
theorem exceptional_incidence_mass_off_core_gt
    (S : Finset β) (I K : Finset α) (P : α → β → Prop)
    [∀ x z, Decidable (P x z)] (a k s B : ℕ)
    (hks : k + s ≤ a)
    (hrow : ∀ z ∈ S, a ≤ (univ.filter fun x => P x z).card)
    (hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B)
    (hKI : K ⊆ I) (hK : K.card ≤ k)
    (hS : Fintype.card α * B < (a - (k + s)) * S.card) :
    s * S.card < ∑ z ∈ S, ((I \ K).filter fun x => P x z).card := by
  have hmass := exceptional_incidence_mass_gt S I P a (k + s) B hks
    hrow hcol hS
  have hsplit : ∑ z ∈ S, (I.filter fun x => P x z).card ≤
      (∑ z ∈ S, (K.filter fun x => P x z).card) +
        ∑ z ∈ S, ((I \ K).filter fun x => P x z).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _hz
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    by_cases hxK : x ∈ K
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxK, hx'.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hx'.1, hxK⟩, hx'.2⟩)
  have hKle : K.card ≤ k :=
    (le_min hK (Finset.card_le_card hKI)).trans (min_le_left _ _)
  have hcore : ∑ z ∈ S, (K.filter fun x => P x z).card ≤ k * S.card := by
    calc
      ∑ z ∈ S, (K.filter fun x => P x z).card ≤ ∑ _z ∈ S, K.card :=
        Finset.sum_le_sum fun z _ => Finset.card_filter_le _ _
      _ = K.card * S.card := by simp [mul_comm]
      _ ≤ k * S.card := Nat.mul_le_mul_right S.card hKle
  have hmass' : (k + s) * S.card < k * S.card +
      ∑ z ∈ S, ((I \ K).filter fun x => P x z).card :=
    hmass.trans_le (hsplit.trans (Nat.add_le_add_right hcore _))
  rw [Nat.add_mul] at hmass'
  omega

/-- **The output of §3.**

If every parameter in `S` is incident to at least `a` coordinates, every coordinate
outside `I` is incident to at most `B` parameters, and `S` is large enough, then the
exceptional set `I` has more than `k` elements.

Downstream `k` is the code dimension and `I = {x | g x = 0}`.  A dimension-`k`
polynomial is determined by `k` evaluations; the stronger conclusion `k < |I|`
therefore supplies enough coordinates. -/
theorem card_exceptional_ge (S : Finset β) (I : Finset α) (P : α → β → Prop)
    [∀ x z, Decidable (P x z)] (a k B : ℕ) (hka : k ≤ a)
    (hrow : ∀ z ∈ S, a ≤ (univ.filter fun x => P x z).card)
    (hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B)
    (hS : Fintype.card α * B < (a - k) * S.card) :
    k < I.card := by
  apply Nat.lt_of_not_ge
  intro hcon
  have hinc := incidence_bound S I P a B hrow hcol
  -- Weaken `(n - |I|) * B` to `n * B`.
  have hweak : a * S.card ≤ I.card * S.card + Fintype.card α * B := by
    have : (Fintype.card α - I.card) * B ≤ Fintype.card α * B :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  -- Cancel the common `|I| * S.card`.
  have hIa : I.card ≤ a := le_trans hcon hka
  obtain ⟨d, hd⟩ : ∃ d, a = I.card + d := ⟨a - I.card, by omega⟩
  have hd_s : d * S.card ≤ Fintype.card α * B := by
    rw [hd, add_mul] at hweak
    omega
  have hak : a - k ≤ d := by omega
  have : (a - k) * S.card ≤ d * S.card := Nat.mul_le_mul_right _ hak
  omega

/-- **The exact rectangular form of `card_exceptional_ge`.**

The older statement weakens the number of nonexceptional coordinates from
`n - |I|` to `n`.  Retaining the rectangle gives the sharper sufficient condition

`(n - k) * B < (a - k) * |S|`.

This is the form needed by the sharp skeleton count: at `a = n - e`, its quotient is
`(n - k) / (n - e - k)` rather than `n / (n - e - k)`. -/
theorem card_exceptional_ge_rect (S : Finset β) (I : Finset α) (P : α → β → Prop)
    [∀ x z, Decidable (P x z)] (a k B : ℕ)
    (hka : k ≤ a) (han : a ≤ Fintype.card α)
    (hrow : ∀ z ∈ S, a ≤ (univ.filter fun x => P x z).card)
    (hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B)
    (hS : (Fintype.card α - k) * B < (a - k) * S.card) :
    k < I.card := by
  apply Nat.lt_of_not_ge
  intro hIk
  have hinc := incidence_bound S I P a B hrow hcol
  by_cases hMB : S.card ≤ B
  · have hnk : a - k ≤ Fintype.card α - k := Nat.sub_le_sub_right han k
    have hle : (a - k) * S.card ≤ (Fintype.card α - k) * B :=
      Nat.mul_le_mul hnk hMB
    exact (not_le_of_gt hS) hle
  · have hBM : B < S.card := Nat.lt_of_not_ge hMB
    have hIa : I.card ≤ a := hIk.trans hka
    have hIn : I.card ≤ Fintype.card α := hIa.trans han
    have haeq : a = I.card + (a - I.card) := by omega
    have hneq : Fintype.card α = I.card + (Fintype.card α - I.card) := by omega
    have hrect : (a - I.card) * S.card ≤
        (Fintype.card α - I.card) * B := by
      have hsum : I.card * S.card + (a - I.card) * S.card ≤
          I.card * S.card + (Fintype.card α - I.card) * B := calc
        I.card * S.card + (a - I.card) * S.card
            = (I.card + (a - I.card)) * S.card := by rw [add_mul]
        _ = a * S.card := by rw [← haeq]
        _ ≤ I.card * S.card + (Fintype.card α - I.card) * B := hinc
      exact Nat.le_of_add_le_add_left hsum
    have hakeq : a - I.card = (a - k) + (k - I.card) := by omega
    have hnkeq : Fintype.card α - I.card =
        (Fintype.card α - k) + (k - I.card) := by omega
    have hdelta : (k - I.card) * B ≤ (k - I.card) * S.card :=
      Nat.mul_le_mul_left _ (le_of_lt hBM)
    have hle : (a - k) * S.card ≤ (Fintype.card α - k) * B := by
      have hsum : (a - k) * S.card + (k - I.card) * B ≤
          (Fintype.card α - k) * B + (k - I.card) * B := calc
        (a - k) * S.card + (k - I.card) * B
            ≤ (a - k) * S.card + (k - I.card) * S.card :=
              Nat.add_le_add_left hdelta _
        _ = ((a - k) + (k - I.card)) * S.card := by rw [add_mul]
        _ = (a - I.card) * S.card := by rw [← hakeq]
        _ ≤ (Fintype.card α - I.card) * B := hrect
        _ = ((Fintype.card α - k) + (k - I.card)) * B := by rw [hnkeq]
        _ = (Fintype.card α - k) * B + (k - I.card) * B := by rw [add_mul]
      exact Nat.le_of_add_le_add_right hsum
    exact (not_le_of_gt hS) hle

end Incidence

end JBAgreement
