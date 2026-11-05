import LfzkV2.Layered.Runtime.Cost
import LfzkV2.Packed.RuntimeProfiles
import LfzkV2.Packed.FrontendSizes
import LfzkV2.RuntimeSide

/-! Current packed runtime costs. These are bounds on the charges in the
actual two-field extraction theorem, with the degree-one signature path
contributing no packing challenge. -/

namespace LfzkV2.Layered.Runtime

open Finset RecursivePolygero

namespace CompiledSide

variable {F C Context : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input : ℕ} {circuit : Layered.Circuit F out input} {I : Instance F}

/-- Bind the analysis-side list size and terminal budgets to a certified
profile. The two budget equalities are reflexive for the profile potential;
they also permit any equivalent terminal potential. -/
structure Profiled (S : CompiledSide F C Context circuit I) (p : LfzkV2.RuntimeProfiles.Profile) where
  geometry : LfzkV2.RuntimeProfiles.Geometry p I
  sampling : LfzkV2.RuntimeProfiles.BackendSampling I S.decodeCoin S.decodeQuery
  cutoff_eq : S.cutoff = p.cutoff
  bound_eq : S.bound = p.candidates
  challenge_eq : S.potential.challengeBudget =
    (p.potential I geometry.n geometry.k geometry.s geometry.t S.decodeCoin S.decodeQuery
      sampling.kCoin sampling.kQuery sampling.coin_bound sampling.query_bound).challengeBudget
  query_eq : S.potential.queryBudget =
    (p.potential I geometry.n geometry.k geometry.s geometry.t S.decodeCoin S.decodeQuery
      sampling.kCoin sampling.kQuery sampling.coin_bound sampling.query_bound).queryBudget

theorem Profiled.budgets_le [Nonempty C] {S : CompiledSide F C Context circuit I}
    {p : LfzkV2.RuntimeProfiles.Profile} (cert : S.Profiled p)
    (hfield : p.minimumField ≤ Fintype.card F) :
    S.potential.challengeBudget/Fintype.card C ≤ (p.capacities+1 : ℕ)/(p.minimumField : ℚ) ∧
      S.potential.queryBudget/Fintype.card C ≤ p.queryUnits/(2^128 : ℚ) := by
  rw [cert.challenge_eq,cert.query_eq]
  exact p.potential_budgets_le I cert.geometry.n cert.geometry.k cert.geometry.s cert.geometry.t
    (by simpa only [Nat.card_eq_fintype_card] using hfield) S.decodeCoin S.decodeQuery
    cert.sampling.kCoin cert.sampling.kQuery cert.sampling.coin_bound cert.sampling.query_bound
    cert.sampling.coin_balanced cert.sampling.query_balanced

end CompiledSide

end LfzkV2.Layered.Runtime
