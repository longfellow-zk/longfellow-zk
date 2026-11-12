import Bcs.PotentialGrinding

/-! A verifier lookup can annotate a raw prover output without becoming an
extra adversarial query charge. Its point already belongs to the verifier
path. The off-coordinate potential compiler is unchanged. -/

namespace Bcs.TotalOracle

open Finset Merkle.RandomOracle
open scoped Classical

namespace VerifierQuery

variable {Q C Out : Type} {N : ℕ}

def prepare (tree : Tree Q C Out N) (point : Out → Q) : Tree Q C (Out × C) (1+N) :=
  tree.bind fun out => Tree.query (point out) (fun c => Tree.done (out,c))

theorem prepare_output (tree : Tree Q C Out N) (point : Out → Q) (H : Q → C) :
    ((prepare tree point).run H).1 = ((tree.run H).1,H (point (tree.run H).1)) := by
  simp [prepare,Tree.run_bind]

theorem prepare_queried (tree : Tree Q C Out N) (point : Out → Q) (H : Q → C) :
    queried (prepare tree point) H = queried tree H ++ [point (tree.run H).1] := by
  simp [queried,prepare,Tree.run_bind]

end VerifierQuery

namespace CtxGrinding

variable {C Q Out Key K : Type} [Fintype C] [DecidableEq Q] {N L : ℕ}

/-- Only the original prover queries and the verifier slots are charged.
The appended lookup supplies the annotation used by the fixed-input model. -/
theorem verifierQuery_budget_le [Fintype Q]
    (G : CtxGrinding C Q (Out × C) Key K (1+N) L)
    (tree : Tree Q C Out N) (point : Out → Q)
    (hadversary : G.adversary = VerifierQuery.prepare tree point)
    (hL : 0 < L) (hpoint : ∀ out c, G.hashInput (out,c) 0 = point out)
    (budget : Q → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax) (hmax : ∀ x, budget x ≤ betaMax)
    (slotBeta : Fin L → ℚ) (hslot : ∀ out i, budget (G.hashInput out i.val) ≤ slotBeta i)
    (H : Q → C) :
    ∑ x ∈ (univ.filter fun x => G.Charged x H), budget x ≤
      N*betaMax+∑ i, slotBeta i := by
  -- H is fixed in this pointwise counting argument. The mapped tree is
  -- used only to bound its charged set, never as an oracle adversary in
  -- a probability theorem.
  let short : CtxGrinding C Q (Out × C) Key K N L :=
    { G with adversary := tree.map fun out => (out,H (point out)) }
  have houtput : short.proof H = G.proof H := by
    change ((tree.map fun out => (out,H (point out))).run H).1 = (G.adversary.run H).1
    rw [hadversary,Tree.run_map,VerifierQuery.prepare_output]
  have hshortpoint (i : Fin L) : short.point H i.val = G.point H i.val :=
    congrArg (fun out => G.hashInput out i.val) houtput
  have hcover : (univ.filter fun x => G.Charged x H) ⊆
      (univ.filter fun x => short.Charged x H) := by
    intro x hx
    have h := (mem_filter.mp hx).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases h with hq | ⟨i,hi⟩
    · rw [hadversary,VerifierQuery.prepare_queried] at hq
      rcases List.mem_append.mp hq with hraw | hkey
      · left
        simpa only [short,queried,Tree.run_map] using hraw
      · right
        refine ⟨⟨0,hL⟩,?_⟩
        rw [hshortpoint]
        change G.hashInput (G.adversary.run H).1 0 = x
        rw [hadversary,VerifierQuery.prepare_output,hpoint]
        exact (List.mem_singleton.mp hkey).symm
    · exact Or.inr ⟨i,(hshortpoint i).trans hi⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun x _ _ => hbudget x)).trans
    (short.charged_rational_budget_le budget hbudget betaMax hbetaMax hmax slotBeta hslot H)

variable (G : CtxGrinding C Q Out Key K N L)

/-- The same rational oracle compiler with a separately proved total
charged budget, for example after a verifier-key annotation. -/
theorem potential_ratio_le_of_total [Fintype Q] [Nonempty C]
    (charge : K → (x : Q) → (Fin (G.pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (budget : Q → ℚ) (hlocal : ∀ κ x pref, ∑ c : C, charge κ x pref c ≤ budget x)
    (B : ℚ) (htotal : ∀ H, ∑ x ∈ (univ.filter fun x => G.Charged x H), budget x ≤ B)
    (E : (Q → C) → Prop) [DecidablePred E]
    (haccept : ∀ H, E H → 1 ≤ ∑ x : Q, if G.Charged x H then
      charge (G.ctxAt H (G.key x)) x (G.pts.chal H x) (H x) else 0) :
    ((univ.filter E).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Q ≤ B/Fintype.card C := by
  let wt (x : Q) (H : Q → C) (c : C) : ℚ :=
    charge (G.ctxAt H (G.key x)) x (G.pts.chal H x) c
  have hoff x H H' (h : AgreeOff x H H') c : wt x H c = wt x H' c := by
    dsimp only [wt]
    rw [G.ctxAt_off H H' x h,← G.pts.chal_congr h]
  have hcharged x H H' (h : AgreeOff x H H') : G.Charged x H ↔ G.Charged x H' :=
    ⟨G.charged_off h,G.charged_off h.symm⟩
  exact potential_event_ratio_le_budget E G.Charged hcharged wt hoff budget B
    (fun x H => hlocal (G.ctxAt H (G.key x)) x (G.pts.chal H x)) htotal
    (fun x H c => hnonneg (G.ctxAt H (G.key x)) x (G.pts.chal H x) c) haccept

end CtxGrinding
end Bcs.TotalOracle
