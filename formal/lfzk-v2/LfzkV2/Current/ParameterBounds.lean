import LfzkV2.Current.AdapterParameters

/-! Exact numerical budgets for the shared mdoc coding geometry. -/
namespace LfzkV2.Current.ParameterBounds

/-- Probability that one uniform t-subset lies in c fixed columns. -/
def tail (n t c : ℕ) : ℚ := (c.choose t : ℚ) / n.choose t

/-- The exceptional rank charge for a field with q elements. -/
def rankError (n k s q : ℕ) : ℚ :=
  (n.choose (k+2*s+1) : ℚ) / (q:ℚ)^(s+1)

/-- Both fields use the same active joint-label family. Its total capacity
multiplies the sum of the two exceptional-coin rates. -/
def parentBudget (n k s t a L : ℕ) : ℚ :=
  rankError n k s Adapter.Mdoc.binaryOrder + rankError n k s Adapter.Mdoc.primeOrder +
    (1/(Adapter.Mdoc.binaryOrder:ℚ)+1/(Adapter.Mdoc.primeOrder:ℚ))*
      (1-tail n t (a-1)+(L:ℚ)*tail n t (a-1))

/-- The participants share one opening set. Add their outside-list tails
without assuming independence. -/
def openingBudget (n s t a b c : ℕ) : ℚ :=
  tail n t (a-1)+tail n t (b+s-1)+tail n t (c+s-1)

end LfzkV2.Current.ParameterBounds
