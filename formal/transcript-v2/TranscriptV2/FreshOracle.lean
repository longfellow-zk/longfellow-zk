import Bcs.PotentialOracle
import Mathlib.Tactic.Positivity.Finset

/-! A memoized adaptive oracle program samples each fresh coordinate once.
Its uniform expectation therefore depends on answer branching, not on the
names of the fresh inputs. This supplies the probability step for online
byte decoding without a fixed global inverse codec. -/
noncomputable section
namespace TranscriptV2.FreshOracle
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P A Out : Type}

def FreshFrom (known : P → Prop) : {fuel : ℕ} → Tree P A Out fuel → Prop
  | _, .done _ => True
  | _, .query p next => ¬known p ∧ ∀ answer, FreshFrom (fun q => q = p ∨ known q) (next answer)

def mean [Fintype A] (value : Out → ℚ) : {fuel : ℕ} → Tree P A Out fuel → ℚ
  | _, .done output => value output
  | _, .query _ next => (∑ answer, mean value (next answer))/Fintype.card A

theorem FreshFrom.not_queried {fuel : ℕ} {known : P → Prop} {tree : Tree P A Out fuel}
    (fresh : FreshFrom known tree) (H : P → A) (p : P) (member : known p) :
    p ∉ queried tree H := by
  induction tree generalizing known with
  | done output => simp
  | query q next ih =>
      intro hit
      rcases List.mem_cons.mp hit with same | tail
      · cases same
        exact fresh.1 member
      · exact ih (H q) (fresh.2 (H q)) (Or.inr member) tail

theorem uniform_mean [Fintype P] [DecidableEq P] [Fintype A] [Nonempty A]
    {fuel : ℕ} (value : Out → ℚ) (tree : Tree P A Out fuel) {known : P → Prop}
    (fresh : FreshFrom known tree) :
    (∑ H : P → A, value (tree.run H).1)/(Fintype.card A : ℚ)^Fintype.card P = mean value tree := by
  have ha : (Fintype.card A : ℚ) ≠ 0 := by positivity
  have hk : ((Fintype.card A : ℚ)^Fintype.card P) ≠ 0 := pow_ne_zero _ ha
  induction tree generalizing known with
  | done output =>
      simp [mean,Nat.cast_pow,hk]
  | query p next ih =>
      let weight := fun H answer => value ((next answer).run H).1
      have off H H' (agree : AgreeOff p H H') answer : weight H answer = weight H' answer := by
        have missing := (fresh.2 answer).not_queried H p (Or.inl rfl)
        exact congrArg (fun result => value result.1) (run_eq_of_not_mem (next answer) p agree missing).symm
      have identity := sum_coord_mul_rat p weight off
      have each answer : (∑ H : P → A, weight H answer) =
          mean value (next answer)*(Fintype.card A : ℚ)^Fintype.card P :=
        (div_eq_iff hk).mp (ih answer (fresh.2 answer))
      change (∑ H : P → A, weight H (H p))/(Fintype.card A : ℚ)^Fintype.card P =
        (∑ answer, mean value (next answer))/Fintype.card A
      apply (div_eq_div_iff hk ha).mpr
      calc
        _ = ∑ H : P → A, ∑ answer, weight H answer := identity
        _ = ∑ answer, ∑ H : P → A, weight H answer := sum_comm
        _ = _ := by simp_rw [each]; rw [sum_mul]

theorem mean_weaken [Fintype A] {fuel : ℕ} (value : Out → ℚ) (tree : Tree P A Out fuel) :
    mean value tree.weaken = mean value tree := by
  induction tree with
  | done output => rfl
  | query p next ih =>
      simp only [Tree.weaken,mean]
      exact congrArg (fun x : ℚ => x/Fintype.card A) (sum_congr rfl (fun answer _ => ih answer))

end TranscriptV2.FreshOracle
