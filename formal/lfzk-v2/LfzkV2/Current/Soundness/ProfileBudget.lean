import LfzkV2.Current.CertifiedProfile

/-! Expose the exact existing backend coefficient before its loose public
upper bound. No change to the profile certificate is needed. -/
namespace Survival.ProfileBudget
open LfzkV2 LfzkV2.Current RecursivePolygero ProfileAnalysis ParameterBounds

theorem parameters_parent_eq (c : CertifiedProfile) (P R : Joint.Participant c.k c.s c.n c.t)
    (hP : Nat.card P.Carrier = Adapter.Mdoc.binaryOrder)
    (hR : Nat.card R.Carrier = Adapter.Mdoc.primeOrder) :
    let pc := c.parameters P.backend P.columns P.dimension P.batching P.openings (Or.inl hP)
    let rc := c.parameters R.backend R.columns R.dimension R.batching R.openings (Or.inr hR)
    pc.rankError+rc.rankError+JointResponse.activeHighBudget P R pc =
      parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList := by
  intro pc rc
  rw [c.parameters_rankError P.backend P.columns P.dimension P.batching P.openings (Or.inl hP),
    c.parameters_rankError R.backend R.columns R.dimension R.batching R.openings (Or.inr hR), hP, hR]
  simp only [JointResponse.activeHighBudget, pc, CertifiedProfile.parameters, CertifiedProfile.threshold,
    hP, hR, parentBudget]

end Survival.ProfileBudget
