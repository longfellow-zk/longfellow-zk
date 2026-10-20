import Bcs.TerminalCharges
import Bcs.FiniteRenewal

/-! Remaining-budget potentials for the actual finite total random oracle.
Repeated queries read the cache; only previously unread coordinates are
averaged. The payoff may inspect unread verifier coordinates at termination.
No freshness or ordering condition is imposed on the adversary's tree. -/
namespace Bcs.TotalOracle.CachedPotential
open Finset Merkle.RandomOracle Footprint
open scoped Classical
variable {Q C Out : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]

abbrev Cache (Q C : Type) := Q → Option C

def complete (cache : Cache Q C) (H : Q → C) : Q → C :=
  fun q => (cache q).getD (H q)

def record (cache : Cache Q C) (q : Q) (c : C) : Cache Q C :=
  Function.update cache q (some c)

omit [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C] in
@[simp] theorem complete_empty (H : Q → C) : complete (fun _ => none) H = H := rfl

omit [Fintype Q] [Fintype C] [Nonempty C] in
theorem complete_record (cache : Cache Q C) (H : Q → C) (q : Q) (c : C) :
    complete (record cache q c) H = Function.update (complete cache H) q c := by
  funext x
  by_cases hx : x = q
  · subst x; simp [complete, record]
  · simp [complete, record, Function.update_of_ne hx]

omit [Fintype Q] [Fintype C] [Nonempty C] in
theorem complete_record_fresh (cache : Cache Q C) (H : Q → C) (q : Q)
    (hq : cache q = none) : complete (record cache q (H q)) H = complete cache H := by
  rw [complete_record]
  have he : complete cache H q = H q := by simp [complete, hq]
  rw [← he, Function.update_eq_self]

/-- Conditional expectation on precisely the answers already read. -/
noncomputable def conditional (cache : Cache Q C) (f : (Q → C) → ℚ) : ℚ :=
  average (fun H => f (complete cache H))

/-- Exact deferred sampling, including arbitrary dependence on all the
other coordinates. A cache miss is one uniform answer; a cache hit is not. -/
theorem conditional_fresh (cache : Cache Q C) (q : Q) (hq : cache q = none)
    (f : (Q → C) → ℚ) :
    conditional cache f = average (fun c => conditional (record cache q c) f) := by
  unfold conditional
  have h := average_resample q (fun H c => f (complete (record cache q c) H)) (by
    intro H H' ho c
    congr 1
    rw [complete_record, complete_record]
    funext x
    by_cases hx : x = q
    · subst x; simp
    · simp [Function.update_of_ne hx, complete, ho x hx])
  simpa only [complete_record_fresh cache _ q hq] using h

/-- A cached execution expectation, with verifier completion left in the
terminal payoff rather than charged as extra adversarial oracle work. -/
noncomputable def expectation (payoff : Out → (Q → C) → ℚ) :
    {N : ℕ} → Tree Q C Out N → Cache Q C → ℚ
  | _, .done out, cache => conditional cache (payoff out)
  | _, .query q next, cache => match cache q with
    | some c => expectation payoff (next c) cache
    | none => average (fun c => expectation payoff (next c) (record cache q c))

/-- The cache semantics is exactly a uniformly sampled total function,
even with repeated, adaptively chosen, or descendant-first queries. -/
theorem totalOracle_eq_expectation {N : ℕ} (tree : Tree Q C Out N)
    (cache : Cache Q C) (payoff : Out → (Q → C) → ℚ) :
    conditional cache (fun H => payoff (tree.run H).1 H) = expectation payoff tree cache := by
  induction tree generalizing cache with
  | done out => rfl
  | query q next ih =>
    cases hq : cache q with
    | some c =>
      simp only [expectation, hq]
      change average (fun H => payoff ((next (complete cache H q)).run (complete cache H)).1
        (complete cache H)) = _
      simp only [complete, hq, Option.getD_some]
      exact ih c cache
    | none =>
      simp only [expectation, hq]
      rw [conditional_fresh cache q hq]
      change average (fun c => conditional (record cache q c)
        (fun H => payoff ((next (H q)).run H).1 H)) =
          average (fun c => expectation payoff (next c) (record cache q c))
      apply congrArg average
      funext c
      have he : conditional (record cache q c) (fun H => payoff ((next (H q)).run H).1 H) =
          conditional (record cache q c) (fun H => payoff ((next c).run H).1 H) := by
        unfold conditional
        congr 1
        funext H
        simp [complete, record]
      rw [he]
      exact ih c (record cache q c)

omit [Nonempty C] in
/-- The exact Bellman interface on a real ROM cache. `hstop` includes all
unread verifier lookups. `hhit` spends work without resampling an old answer.
`hmiss` is the only probabilistic transition obligation. -/
theorem expectation_le_timePotential
    (payoff : Out → (Q → C) → ℚ) (potential : ℕ → Cache Q C → ℚ)
    (hstop : ∀ n cache out, conditional cache (payoff out) ≤ potential n cache)
    (hhit : ∀ n cache, potential n cache ≤ potential (n+1) cache)
    (hmiss : ∀ n cache q, cache q = none →
      average (fun c => potential n (record cache q c)) ≤ potential (n+1) cache)
    {N : ℕ} (tree : Tree Q C Out N) (cache : Cache Q C) :
    expectation payoff tree cache ≤ potential N cache := by
  induction tree generalizing cache with
  | done out => exact hstop _ cache out
  | query q next ih =>
    cases hq : cache q with
    | some c => simpa only [expectation, hq] using (ih c cache).trans (hhit _ cache)
    | none =>
      simpa only [expectation, hq] using
        (average_mono (fun c => ih c (record cache q c))).trans (hmiss _ cache q hq)

/-- Actual-ROM transport of the remaining-budget potential, starting with
an empty cache. This theorem has no ordered-query or no-repeat premise. -/
theorem totalOracle_le_timePotential
    (payoff : Out → (Q → C) → ℚ) (potential : ℕ → Cache Q C → ℚ)
    (hstop : ∀ n cache out, conditional cache (payoff out) ≤ potential n cache)
    (hhit : ∀ n cache, potential n cache ≤ potential (n+1) cache)
    (hmiss : ∀ n cache q, cache q = none →
      average (fun c => potential n (record cache q c)) ≤ potential (n+1) cache)
    {N : ℕ} (tree : Tree Q C Out N) :
    average (fun H => payoff (tree.run H).1 H) ≤ potential N (fun _ => none) := by
  have he := totalOracle_eq_expectation tree (fun _ => none) payoff
  simp only [conditional, complete_empty] at he
  rw [he]
  exact expectation_le_timePotential payoff potential hstop hhit hmiss tree _

end Bcs.TotalOracle.CachedPotential
