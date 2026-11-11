import SumcheckV1.Counting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Generic finite statistical distance and coupling composition.

These are protocol-independent probability statements, originally housed
beside the V1 pad layout. Global declaration names are preserved so existing
V1 and Polygero clients keep their public API without importing a runtime.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true

open SumcheckV1 BigOperators Classical Finset

/-- `f` and `g` are `eps`-close: some bijection on coins makes them agree, except on at most
`eps` coins. -/
def ZkClose {R S T : Type} [Fintype R] [Fintype S] (eps : ℕ) (f : R → T) (g : S → T) : Prop :=
  ∃ φ : R ≃ S, event_card (Finset.filter (fun r => g (φ r) ≠ f r) Finset.univ) ≤ eps

/-- An exact bijection is `0`-close: perfect. -/
lemma zkClose_zero {R S T : Type} [Fintype R] [Fintype S]
    (φ : R ≃ S) (f : R → T) (g : S → T) (h : ∀ r, g (φ r) = f r) : ZkClose 0 f g := by
  refine ⟨φ, ?_⟩
  have : Finset.filter (fun r => g (φ r) ≠ f r) Finset.univ = ∅ := by
    ext r; simp [h r]
  simp [event_card, this]

lemma ZkClose.mono {R S T : Type} [Fintype R] [Fintype S] {eps eps' : ℕ} {f : R → T} {g : S → T}
    (h : eps ≤ eps') : ZkClose eps f g → ZkClose eps' f g := by
  rintro ⟨φ, hφ⟩; exact ⟨φ, le_trans hφ h⟩

/-- Counting a product fibrewise: `m` bad second coordinates per first coordinate gives at
most `|R₁| * m` bad pairs. -/
lemma prod_bad_card {R₁ R₂ : Type} [Fintype R₁] [Fintype R₂] (Q : R₁ → R₂ → Prop) (m : ℕ)
    (hQ : ∀ r : R₁, (Finset.filter (fun s : R₂ => Q r s) Finset.univ).card ≤ m) :
    (Finset.filter (fun p : R₁ × R₂ => Q p.1 p.2) Finset.univ).card ≤ Fintype.card R₁ * m := by
  classical
  rw [card_prod_filter Q]
  calc ∑ r : R₁, (Finset.filter (fun s : R₂ => Q r s) Finset.univ).card
      ≤ ∑ _r : R₁, m := Finset.sum_le_sum (fun r _ => hQ r)
    _ = Fintype.card R₁ * m := by simp [mul_comm]

lemma ZkClose.symm {R S T : Type} [Fintype R] [Fintype S] {eps : ℕ} {f : R → T} {g : S → T} :
    ZkClose eps f g → ZkClose eps g f := by
  classical
  rintro ⟨φ, hφ⟩
  refine ⟨φ.symm, le_trans (le_of_eq ?_) hφ⟩
  dsimp [event_card]
  refine Finset.card_bij (fun s _ => φ.symm s) ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rw [Equiv.apply_symm_apply]
    exact fun hc => hs hc.symm
  · intro s _ s' _ h
    exact φ.symm.injective h
  · intro r hr
    refine ⟨φ r, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rw [Equiv.symm_apply_apply]
    exact fun hc => hr hc.symm

lemma ZkClose.trans {R S T U : Type} [Fintype R] [Fintype S] [Fintype T]
    {e₁ e₂ : ℕ} {f : R → U} {g : S → U} {h : T → U} :
    ZkClose e₁ f g → ZkClose e₂ g h → ZkClose (e₁ + e₂) f h := by
  classical
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩
  refine ⟨φ.trans ψ, ?_⟩
  have hsub : Finset.filter (fun r => h ((φ.trans ψ) r) ≠ f r) Finset.univ
      ⊆ Finset.filter (fun r => g (φ r) ≠ f r) Finset.univ
        ∪ Finset.filter (fun r => h (ψ (φ r)) ≠ g (φ r)) Finset.univ := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Equiv.trans_apply] at hr ⊢
    by_cases hc : g (φ r) = f r
    · right; rw [hc]; exact hr
    · left; exact hc
  have hmap : (Finset.filter (fun r => h (ψ (φ r)) ≠ g (φ r)) Finset.univ).card
      = (Finset.filter (fun s => h (ψ s) ≠ g s) Finset.univ).card := by
    refine Finset.card_bij (fun r _ => φ r) ?_ ?_ ?_
    · intro r hr
      simpa using hr
    · intro r _ r' _ hh
      exact φ.injective hh
    · intro s hs
      refine ⟨φ.symm s, ?_, by simp⟩
      simpa using hs
  calc event_card (Finset.filter (fun r => h ((φ.trans ψ) r) ≠ f r) Finset.univ)
      ≤ (Finset.filter (fun r => g (φ r) ≠ f r) Finset.univ
          ∪ Finset.filter (fun r => h (ψ (φ r)) ≠ g (φ r)) Finset.univ).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.filter (fun r => g (φ r) ≠ f r) Finset.univ).card
        + (Finset.filter (fun r => h (ψ (φ r)) ≠ g (φ r)) Finset.univ).card :=
        Finset.card_union_le _ _
    _ ≤ e₁ + e₂ := Nat.add_le_add hφ (le_trans (le_of_eq hmap) hψ)

/--
**Sequential composition.**

Stage one is perfect and its output `a` is public.  Stage two may depend on that output, and
is `eps`-close *uniformly* in it.  Then the composite is `|R₁| · eps`-close — the same
*fraction* `eps / |R₂|`, since the sample space grew by the factor `|R₁|`.

This is the shape the protocol needs: sampling the transmitted values is perfect and
witness-free, the constraint system is a function of them, and Ligero's simulator is invoked
on that system.
-/
theorem zkClose_seq {R₁ S₁ R₂ S₂ A B : Type}
    [Fintype R₁] [Fintype S₁] [Fintype R₂] [Fintype S₂]
    (φ₁ : R₁ ≃ S₁) (a : R₁ → A) (b : S₁ → A) (h1 : ∀ r, b (φ₁ r) = a r)
    (f₂ : R₁ → R₂ → B) (g₂ : S₁ → S₂ → B) (eps : ℕ)
    (h2 : ∀ r : R₁, ZkClose eps (f₂ r) (g₂ (φ₁ r))) :
    ZkClose (Fintype.card R₁ * eps)
      (fun p : R₁ × R₂ => (a p.1, f₂ p.1 p.2))
      (fun q : S₁ × S₂ => (b q.1, g₂ q.1 q.2)) := by
  classical
  choose φ₂ hφ₂ using h2
  refine ⟨(Equiv.prodCongrRight φ₂).trans (φ₁.prodCongr (Equiv.refl S₂)), ?_⟩
  refine le_trans (le_of_eq ?_) (prod_bad_card (fun r s => g₂ (φ₁ r) (φ₂ r s) ≠ f₂ r s) eps
    (fun r => by simpa [event_card] using hφ₂ r))
  dsimp [event_card]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show ((b (φ₁ p.1), g₂ (φ₁ p.1) (φ₂ p.1 p.2)) ≠ (a p.1, f₂ p.1 p.2))
      ↔ ¬ g₂ (φ₁ p.1) (φ₂ p.1 p.2) = f₂ p.1 p.2
  constructor
  · intro h hc
    exact h (by rw [h1 p.1, hc])
  · intro h hc
    exact h (congrArg Prod.snd hc)

/-- The probability that `f` of a uniform coin lands in `P`. -/
noncomputable def probOf {R T : Type} [Fintype R] (f : R → T) (P : T → Prop) : ℚ :=
  ((Finset.filter (fun r => P (f r)) Finset.univ).card : ℚ) / Fintype.card R

/--
**`eps`-indistinguishable.**

No test separates `f` from `g` by more than `eps`, where `P` ranges over *all* predicates on
the output — unbounded and non-uniform, so this is statistical, not computational.  The two
coin spaces are unrelated: `R` and `S` need not even have the same size, which is what a real
simulator needs.
-/
def StatClose {R S T : Type} [Fintype R] [Fintype S] (eps : ℚ) (f : R → T) (g : S → T) : Prop :=
  ∀ P : T → Prop, |probOf f P - probOf g P| ≤ eps

lemma StatClose.mono {R S T : Type} [Fintype R] [Fintype S] {eps eps' : ℚ} {f : R → T}
    {g : S → T} (h : eps ≤ eps') : StatClose eps f g → StatClose eps' f g :=
  fun hc P => le_trans (hc P) h

lemma StatClose.symm {R S T : Type} [Fintype R] [Fintype S] {eps : ℚ} {f : R → T} {g : S → T} :
    StatClose eps f g → StatClose eps g f := by
  intro h P
  rw [abs_sub_comm]
  exact h P

lemma StatClose.trans {R S U T : Type} [Fintype R] [Fintype S] [Fintype U]
    {e₁ e₂ : ℚ} {f : R → T} {g : S → T} {h : U → T} :
    StatClose e₁ f g → StatClose e₂ g h → StatClose (e₁ + e₂) f h := fun h₁ h₂ P =>
  le_trans (abs_sub_le (probOf f P) (probOf g P) (probOf h P))
    (add_le_add (h₁ P) (h₂ P))

/-- Reindexing along a bijection does not change a probability. -/
lemma probOf_equiv {R S T : Type} [Fintype R] [Fintype S] (φ : R ≃ S) (g : S → T)
    (P : T → Prop) : probOf (fun r => g (φ r)) P = probOf g P := by
  classical
  have hcard : (Finset.filter (fun r => P (g (φ r))) Finset.univ).card
      = (Finset.filter (fun s => P (g s)) Finset.univ).card := by
    refine Finset.card_bij (fun r _ => φ r) ?_ ?_ ?_
    · intro r hr; simpa using hr
    · intro r _ r' _ h; exact φ.injective h
    · intro s hs
      refine ⟨φ.symm s, ?_, by simp⟩
      simpa using hs
  rw [probOf, probOf, hcard, Fintype.card_congr φ]

/-- Two events differing only inside a set of size `≤ eps` have card within `eps`. -/
lemma card_close_of_sdiff {R : Type} [Fintype R] {eps : ℕ} (A B Bad : Finset R)
    (hBad : Bad.card ≤ eps) (hAB : A \ B ⊆ Bad) (hBA : B \ A ⊆ Bad) :
    |(A.card : ℚ) - (B.card : ℚ)| ≤ (eps : ℚ) := by
  have h1 : A.card ≤ B.card + eps := by
    have hsplit : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
    have h2 : (A \ B).card ≤ eps := le_trans (Finset.card_le_card hAB) hBad
    have h3 : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have h1' : B.card ≤ A.card + eps := by
    have hsplit : (B \ A).card + (B ∩ A).card = B.card := Finset.card_sdiff_add_card_inter B A
    have h2 : (B \ A).card ≤ eps := le_trans (Finset.card_le_card hBA) hBad
    have h3 : (B ∩ A).card ≤ A.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have hA : ((A.card : ℚ)) ≤ (B.card : ℚ) + eps := by exact_mod_cast h1
  have hB : ((B.card : ℚ)) ≤ (A.card : ℚ) + eps := by exact_mod_cast h1'
  rw [abs_le]
  constructor <;> linarith

/--
**A coupling is an indistinguishability bound.**

`eps` bad coins out of `|R|` means no test succeeds with advantage more than `eps/|R|`.  This
is the direction that matters: it turns the coupling the pad argument produces into the
statement the literature uses.

The converse also holds for uniform coins on equal-size spaces — the maximum matching between
fibres is `Σ_t min(a_t, b_t) = |R|·(1 − Δ)` — but it is **not** formalised here, so `ZkClose`
is used as a *sufficient* condition throughout and never as a characterisation.
-/
theorem zkClose_statClose {R S T : Type} [Fintype R] [Fintype S] {eps : ℕ}
    {f : R → T} {g : S → T} (h : ZkClose eps f g) :
    StatClose ((eps : ℚ) / Fintype.card R) f g := by
  classical
  obtain ⟨φ, hφ⟩ := h
  intro P
  rcases Nat.eq_zero_or_pos (Fintype.card R) with hR | hR
  · have hSe : Fintype.card S = 0 := by rw [← Fintype.card_congr φ, hR]
    simp [probOf, hR, hSe]
  have hRq : (0 : ℚ) < Fintype.card R := by exact_mod_cast hR
  have hkey : |((Finset.filter (fun r => P (f r)) Finset.univ).card : ℚ)
      - ((Finset.filter (fun r => P (g (φ r))) Finset.univ).card : ℚ)| ≤ (eps : ℚ) := by
    refine card_close_of_sdiff _ _ (Finset.filter (fun r => g (φ r) ≠ f r) Finset.univ)
      (by simpa [event_card] using hφ) ?_ ?_ <;>
      intro r hr <;>
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢ <;>
      · intro hc; rw [hc] at hr; exact hr.2 hr.1
  rw [← probOf_equiv φ g P, probOf, probOf, div_sub_div_same, abs_div, abs_of_pos hRq]
  gcongr

/-!
### Total variation distance

`StatClose` is the *distinguisher* form.  `statDist` is the sum form — total variation
distance — and `statDist_le_of_statClose` says the distinguisher bound implies it, by testing
the single event where `f` is more likely than `g`.  This is the statement to quote when the
result is compared against a paper.
-/

/-- Total variation distance between the output distributions of `f` and `g`. -/
noncomputable def statDist {R S T : Type} [Fintype R] [Fintype S] [Fintype T] [DecidableEq T]
    (f : R → T) (g : S → T) : ℚ :=
  (∑ t : T, |probOf f (fun x => x = t) - probOf g (fun x => x = t)|) / 2

/-- A probability decomposes over the fibres of the outcome. -/
lemma probOf_eq_sum {R T : Type} [Fintype R] [Fintype T] [DecidableEq T] (f : R → T)
    (P : T → Prop) :
    probOf f P = ∑ t ∈ Finset.univ.filter P, probOf f (fun x => x = t) := by
  classical
  have hcard : (Finset.filter (fun r => P (f r)) Finset.univ).card
      = ∑ t ∈ Finset.univ.filter P,
          (Finset.filter (fun r => f r = t) Finset.univ).card := by
    have hmem : ∀ r ∈ Finset.filter (fun r => P (f r)) Finset.univ,
        f r ∈ Finset.univ.filter P := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hr
    refine (Finset.card_eq_sum_card_fiberwise hmem).trans ?_
    refine Finset.sum_congr rfl (fun t ht => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hft⟩; exact hft
    · intro hft; exact ⟨by rw [hft]; exact ht, hft⟩
  simp only [probOf, hcard, Nat.cast_sum, Finset.sum_div]

/--
**The distinguisher bound gives total variation distance.**

Test the event where `f` is at least as likely as `g`: on it the summands are the positive
parts of the differences, and on its complement the negative parts, so the sum of absolute
values is at most `2·eps`.
-/
theorem statDist_le_of_statClose {R S T : Type} [Fintype R] [Fintype S] [Fintype T]
    [DecidableEq T] {eps : ℚ} {f : R → T} {g : S → T} (h : StatClose eps f g) :
    statDist f g ≤ eps := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : T → Prop,
      Q = fun t => 0 ≤ probOf f (fun x => x = t) - probOf g (fun x => x = t) := ⟨_, rfl⟩
  have h1 : (∑ t ∈ Finset.univ.filter Q,
      (probOf f (fun x => x = t) - probOf g (fun x => x = t))) ≤ eps := by
    have heq : (∑ t ∈ Finset.univ.filter Q,
        (probOf f (fun x => x = t) - probOf g (fun x => x = t)))
        = probOf f Q - probOf g Q := by
      rw [probOf_eq_sum f Q, probOf_eq_sum g Q, ← Finset.sum_sub_distrib]
    rw [heq]
    exact le_trans (le_abs_self _) (h Q)
  have h2 : (∑ t ∈ Finset.univ.filter (fun t => ¬ Q t),
      (probOf g (fun x => x = t) - probOf f (fun x => x = t))) ≤ eps := by
    have heq : (∑ t ∈ Finset.univ.filter (fun t => ¬ Q t),
        (probOf g (fun x => x = t) - probOf f (fun x => x = t)))
        = probOf g (fun t => ¬ Q t) - probOf f (fun t => ¬ Q t) := by
      rw [probOf_eq_sum f (fun t => ¬ Q t), probOf_eq_sum g (fun t => ¬ Q t),
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr (by ext t; simp) (fun _ _ => rfl)
    rw [heq]
    exact le_trans (le_abs_self _) (StatClose.symm h (fun t => ¬ Q t))
  have hsplit : (∑ t : T, |probOf f (fun x => x = t) - probOf g (fun x => x = t)|)
      = (∑ t ∈ Finset.univ.filter Q,
            (probOf f (fun x => x = t) - probOf g (fun x => x = t)))
        + (∑ t ∈ Finset.univ.filter (fun t => ¬ Q t),
            (probOf g (fun x => x = t) - probOf f (fun x => x = t))) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ Q
      (fun t => |probOf f (fun x => x = t) - probOf g (fun x => x = t)|)]
    congr 1
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ] at ht
      exact abs_of_nonneg ht
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ, not_le] at ht
      rw [abs_of_neg ht]; ring
  have hstat : statDist f g
      = (∑ t : T, |probOf f (fun x => x = t) - probOf g (fun x => x = t)|) / 2 := rfl
  rw [hstat, hsplit]
  linarith

/-- A probability over a product is the average of the fibre probabilities. -/
lemma probOf_prod {R₁ R₂ T : Type} [Fintype R₁] [Fintype R₂] (F : R₁ → R₂ → T) (P : T → Prop) :
    probOf (fun p : R₁ × R₂ => F p.1 p.2) P
      = (∑ r : R₁, probOf (F r) P) / Fintype.card R₁ := by
  classical
  simp only [probOf, Fintype.card_prod]
  rw [card_prod_filter (fun (r : R₁) (s : R₂) => P (F r s)), Nat.cast_sum, Finset.sum_div,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [div_div, mul_comm]
  push_cast
  ring

/--
**Closeness passes to a mixture over a shared first stage.**

If at every value of a shared coin the two second stages are `eps`-close, then they are `eps`-close
jointly.  The first stage is *identical* on the two sides — not merely coupled by a bijection, which
is what `statClose_seq` handles — so this is the case where stage one is public randomness both
parties read.

It is the step that makes deriving a challenge from a hash tape free: the tape is shared, and the
bound holds at each tape.
-/
theorem statClose_mix {R₁ R₂ S₂ T : Type} [Fintype R₁] [Fintype R₂] [Fintype S₂]
    {eps : ℚ} (heps : 0 ≤ eps) (f : R₁ → R₂ → T) (g : R₁ → S₂ → T)
    (h : ∀ r, StatClose eps (f r) (g r)) :
    StatClose eps (fun p : R₁ × R₂ => f p.1 p.2) (fun q : R₁ × S₂ => g q.1 q.2) := by
  classical
  intro P
  rw [probOf_prod f P, probOf_prod g P]
  rcases Nat.eq_zero_or_pos (Fintype.card R₁) with hR | hR
  · simp [hR, heps]
  have hRq : (0 : ℚ) < Fintype.card R₁ := by exact_mod_cast hR
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hRq,
    div_le_iff₀ hRq]
  calc |∑ r : R₁, (probOf (f r) P - probOf (g r) P)|
      ≤ ∑ r : R₁, |probOf (f r) P - probOf (g r) P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R₁, eps := Finset.sum_le_sum fun r _ => h r P
    _ = eps * Fintype.card R₁ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/--
**Sequential composition, in fractions.**

Stage one is perfect and its output `a` is public.  Stage two may depend on that output and is
`eps`-indistinguishable *uniformly* in it.  Then the composite is `eps`-indistinguishable — no
factor for the first stage's coin space, because probabilities are already normalised.

This is the shape the protocol needs: sampling the transmitted values is perfect and
witness-free, the constraint system is a function of them, and Ligero's simulator is invoked on
that system with its **own** randomness, which need not match the prover's.
-/
theorem statClose_seq {R₁ S₁ R₂ S₂ A B : Type}
    [Fintype R₁] [Fintype S₁] [Fintype R₂] [Fintype S₂]
    (φ₁ : R₁ ≃ S₁) (a : R₁ → A) (b : S₁ → A) (h1 : ∀ r, b (φ₁ r) = a r)
    (f₂ : R₁ → R₂ → B) (g₂ : S₁ → S₂ → B) (eps : ℚ) (heps : 0 ≤ eps)
    (h2 : ∀ r : R₁, StatClose eps (f₂ r) (g₂ (φ₁ r))) :
    StatClose eps
      (fun p : R₁ × R₂ => (a p.1, f₂ p.1 p.2))
      (fun q : S₁ × S₂ => (b q.1, g₂ q.1 q.2)) := by
  classical
  intro P
  rw [probOf_prod (fun r s => (a r, f₂ r s)) P, probOf_prod (fun s t => (b s, g₂ s t)) P]
  rcases Nat.eq_zero_or_pos (Fintype.card R₁) with hR | hR
  · have hS : Fintype.card S₁ = 0 := by rw [← Fintype.card_congr φ₁, hR]
    simp [hR, hS, heps]
  have hRq : (0 : ℚ) < Fintype.card R₁ := by exact_mod_cast hR
  -- reindex the simulated average along the perfect first stage
  have hre : (∑ s : S₁, probOf (fun t => (b s, g₂ s t)) P) / Fintype.card S₁
      = (∑ r : R₁, probOf (fun t => (a r, g₂ (φ₁ r) t)) P) / Fintype.card R₁ := by
    rw [Fintype.card_congr φ₁]
    congr 1
    refine (Fintype.sum_equiv φ₁ (fun r => probOf (fun t => (a r, g₂ (φ₁ r) t)) P)
      (fun s => probOf (fun t => (b s, g₂ s t)) P) (fun r => ?_)).symm
    rw [h1 r]
  rw [hre, div_sub_div_same, abs_div, abs_of_pos hRq]
  rw [div_le_iff₀ hRq]
  calc |∑ r : R₁, probOf (fun t => (a r, f₂ r t)) P
          - ∑ r : R₁, probOf (fun t => (a r, g₂ (φ₁ r) t)) P|
      = |∑ r : R₁, (probOf (fun t => (a r, f₂ r t)) P
          - probOf (fun t => (a r, g₂ (φ₁ r) t)) P)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ r : R₁, |probOf (fun t => (a r, f₂ r t)) P
          - probOf (fun t => (a r, g₂ (φ₁ r) t)) P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R₁, eps := Finset.sum_le_sum (fun r _ => h2 r (fun x => P (a r, x)))
    _ = eps * Fintype.card R₁ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-!
### Post-processing, relabelling, and two parallel stages

Four more `StatClose` combinators, none specific to any protocol.  `statClose_parallel` is the one
with content: it is `statClose_mix` applied twice, and it is what a *composition of two arguments*
consumes — the two-field construction of `LfzkV1.TwoFieldZk` replaces one side's transcript and then
the other's, exactly this shape.

**`statClose_reindex` is stated pointwise on purpose.**  The natural form,

```
(φ : R' ≃ R) (h : StatClose eps f g) : StatClose eps (fun r => f (φ r)) (fun s => g (ψ s))
```

does not survive use.  At a call site the goal's two functions are hand-written lambdas, and asking
the elaborator to see them as `f ∘ φ` unfolds `StatClose` into `probOf` and `Finset.filter` and does
not come back — not at five times the heartbeat budget.  Taking the relabelled functions as *given*
and relating them to the originals pointwise makes each use a `fun _ => rfl`.  The same applies to
`statClose_zero_of_equiv`.
-/

/-- Post-processing preserves closeness: `P` ranges over *all* predicates, so test with `P ∘ φ`. -/
lemma statClose_map {R S T U : Type} [Fintype R] [Fintype S] {eps : ℚ} {f : R → T} {g : S → T}
    (φ : T → U) (h : StatClose eps f g) :
    StatClose eps (fun r => φ (f r)) (fun s => φ (g s)) := fun P => h (fun t => P (φ t))

/-- Relabelling the coins on either side preserves closeness.  See the note above on why the
relabelled functions are taken as given rather than written `f ∘ φ`. -/
lemma statClose_reindex {R R' S S' T : Type} [Fintype R] [Fintype R'] [Fintype S] [Fintype S']
    {eps : ℚ} {f : R → T} {g : S → T} {f' : R' → T} {g' : S' → T}
    (φ : R' ≃ R) (ψ : S' ≃ S)
    (hf : ∀ r, f' r = f (φ r)) (hg : ∀ s, g' s = g (ψ s))
    (h : StatClose eps f g) : StatClose eps f' g' := by
  intro P
  have e1 : probOf f' P = probOf f P := by
    rw [show f' = fun r => f (φ r) from funext hf, probOf_equiv φ f P]
  have e2 : probOf g' P = probOf g P := by
    rw [show g' = fun s => g (ψ s) from funext hg, probOf_equiv ψ g P]
  rw [e1, e2]
  exact h P

/-- A bijective change of coins is *free*.  This is the shape every perfect step in this development
takes — `blindEquiv` at the pad stage, `LfzkV1.Mac.macBlindEquiv` at the two-field MAC tag. -/
lemma statClose_zero_of_equiv {R R' T : Type} [Fintype R] [Fintype R'] {f : R → T} {g : R' → T}
    (φ : R ≃ R') (hf : ∀ r, f r = g (φ r)) : StatClose 0 f g := by
  intro P
  have e1 : probOf f P = probOf g P := by
    rw [show f = fun r => g (φ r) from funext hf, probOf_equiv φ g P]
  rw [e1, sub_self, abs_zero]

/-- `A × R₁ × R₂ ≃ (A × R₂) × R₁` — regroup so that the *second* stage is shared. -/
def Equiv.prodPullSnd (A R₁ R₂ : Type) : A × R₁ × R₂ ≃ (A × R₂) × R₁ where
  toFun p := ((p.1, p.2.2), p.2.1)
  invFun q := (q.1.1, q.2, q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `A × R₁ × R₂ ≃ (A × R₁) × R₂` — regroup so that the *first* stage is shared. -/
def Equiv.prodPullFst (A R₁ R₂ : Type) : A × R₁ × R₂ ≃ (A × R₁) × R₂ where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun q := (q.1.1, q.1.2, q.2)
  left_inv _ := rfl
  right_inv _ := rfl

/--
**Two parallel stages, replaced one at a time.**

A shared stage `A`, then two independent stages whose outputs are combined by `out`.  If each can be
replaced at cost `eᵢ` uniformly in `A`, the pair can be replaced at cost `e₁ + e₂`.

This is the hybrid argument of a two-instance composition, done once: `statClose_mix` with the
shared stage taken to be `(a, r₂)` and then `(a, s₁)`, and `statClose_reindex` to put the coin space
back in a fixed order.  `LfzkV1.TwoFieldZk.hybrid_sides` is the instance.
-/
theorem statClose_parallel {A R₁ S₁ R₂ S₂ B₁ B₂ T : Type}
    [Fintype A] [Fintype R₁] [Fintype S₁] [Fintype R₂] [Fintype S₂]
    {e₁ e₂ : ℚ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (out : A → B₁ → B₂ → T)
    (f₁ : A → R₁ → B₁) (g₁ : A → S₁ → B₁)
    (f₂ : A → R₂ → B₂) (g₂ : A → S₂ → B₂)
    (h₁ : ∀ a, StatClose e₁ (f₁ a) (g₁ a))
    (h₂ : ∀ a, StatClose e₂ (f₂ a) (g₂ a)) :
    StatClose (e₁ + e₂)
      (fun p : A × R₁ × R₂ => out p.1 (f₁ p.1 p.2.1) (f₂ p.1 p.2.2))
      (fun q : A × S₁ × S₂ => out q.1 (g₁ q.1 q.2.1) (g₂ q.1 q.2.2)) := by
  -- replace side one, sharing `(a, r₂)`
  have mix₁ : StatClose e₁
      (fun p : (A × R₂) × R₁ => out p.1.1 (f₁ p.1.1 p.2) (f₂ p.1.1 p.1.2))
      (fun q : (A × R₂) × S₁ => out q.1.1 (g₁ q.1.1 q.2) (f₂ q.1.1 q.1.2)) :=
    statClose_mix he₁
      (fun (ar : A × R₂) (r₁ : R₁) => out ar.1 (f₁ ar.1 r₁) (f₂ ar.1 ar.2))
      (fun (ar : A × R₂) (s₁ : S₁) => out ar.1 (g₁ ar.1 s₁) (f₂ ar.1 ar.2))
      (fun ar : A × R₂ =>
        statClose_map (fun b₁ : B₁ => out ar.1 b₁ (f₂ ar.1 ar.2)) (h₁ ar.1))
  have step1 : StatClose e₁
      (fun p : A × R₁ × R₂ => out p.1 (f₁ p.1 p.2.1) (f₂ p.1 p.2.2))
      (fun p : A × S₁ × R₂ => out p.1 (g₁ p.1 p.2.1) (f₂ p.1 p.2.2)) :=
    statClose_reindex (Equiv.prodPullSnd A R₁ R₂) (Equiv.prodPullSnd A S₁ R₂)
      (fun _ => rfl) (fun _ => rfl) mix₁
  -- replace side two, sharing `(a, s₁)`
  have mix₂ : StatClose e₂
      (fun p : (A × S₁) × R₂ => out p.1.1 (g₁ p.1.1 p.1.2) (f₂ p.1.1 p.2))
      (fun q : (A × S₁) × S₂ => out q.1.1 (g₁ q.1.1 q.1.2) (g₂ q.1.1 q.2)) :=
    statClose_mix he₂
      (fun (as : A × S₁) (r₂ : R₂) => out as.1 (g₁ as.1 as.2) (f₂ as.1 r₂))
      (fun (as : A × S₁) (s₂ : S₂) => out as.1 (g₁ as.1 as.2) (g₂ as.1 s₂))
      (fun as : A × S₁ =>
        statClose_map (fun b₂ : B₂ => out as.1 (g₁ as.1 as.2) b₂) (h₂ as.1))
  have step2 : StatClose e₂
      (fun p : A × S₁ × R₂ => out p.1 (g₁ p.1 p.2.1) (f₂ p.1 p.2.2))
      (fun q : A × S₁ × S₂ => out q.1 (g₁ q.1 q.2.1) (g₂ q.1 q.2.2)) :=
    statClose_reindex (Equiv.prodPullFst A S₁ R₂) (Equiv.prodPullFst A S₁ S₂)
      (fun _ => rfl) (fun _ => rfl) mix₂
  exact step1.trans step2
