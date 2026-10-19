import Lfzk.AffineSide

/-! Forked circuit-side FS, with a common context and independent message
prefixes. The prover's tree may interleave the two branches arbitrarily.
This is the extracted-circuit core; commitment binding and MAC agreement
are separate blocks, rather than implicit conclusions of this theorem. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Lfzk.AffineFork
open Finset Bcs.AffineBlock Bcs.TotalOracle Merkle.RandomOracle
open Lfzk.NizkDeployedHash Lfzk.NizkZkTwoField Lfzk.RbrZkSplit Lfzk.RbrZkFlat
open scoped Classical

abbrev Input (Key Ctx Msg₁ Msg₂ : Type) (R₁ R₂ : Lfzk.CertifiedV1.Row) :=
  Key ⊕ (MPoint Ctx Msg₁ R₁.params.nl R₁.params.rounds ⊕
    MPoint Ctx Msg₂ R₂.params.nl R₂.params.rounds)

def left {Key Ctx Msg₁ Msg₂ : Type} {R₁ R₂ : Lfzk.CertifiedV1.Row} :
    MPoint Ctx Msg₁ R₁.params.nl R₁.params.rounds ↪ Input Key Ctx Msg₁ Msg₂ R₁ R₂ :=
  ⟨fun p => .inr (.inl p), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
def right {Key Ctx Msg₁ Msg₂ : Type} {R₁ R₂ : Lfzk.CertifiedV1.Row} :
    MPoint Ctx Msg₂ R₂.params.nl R₂.params.rounds ↪ Input Key Ctx Msg₁ Msg₂ R₁ R₂ :=
  ⟨fun p => .inr (.inr p), fun _ _ h => Sum.inr.inj (Sum.inr.inj h)⟩

variable {Key Ctx Msg₁ Msg₂ : Type} {R₁ R₂ : Lfzk.CertifiedV1.Row}
  [Fintype Key] [Fintype Ctx] [Fintype Msg₁] [Fintype Msg₂]

noncomputable def domain (i : Fin 2) : Finset (Input Key Ctx Msg₁ Msg₂ R₁ R₂) :=
  if i = 0 then univ.image left else univ.image right

omit [Fintype Key] in
theorem domains_disjoint : Pairwise (fun i j => Disjoint
    (domain (Key := Key) (Ctx := Ctx) (Msg₁ := Msg₁) (Msg₂ := Msg₂) (R₁ := R₁) (R₂ := R₂) i)
    (domain (Key := Key) (Ctx := Ctx) (Msg₁ := Msg₁) (Msg₂ := Msg₂) (R₁ := R₁) (R₂ := R₂) j)) := by
  intro i j hn
  fin_cases i <;> fin_cases j <;> simp_all [domain, Finset.disjoint_left, left, right]

variable {C Out : Type} [Fintype C] [Nonempty C]
variable {logv₁ : ℕ} {Sig₁ F₁ X₁ Q₁ Witness₁ : Type}
  [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [Fintype X₁] [DecidableEq X₁] [Fintype Q₁] [DecidableEq Q₁] [Inhabited Msg₁]
  {M₁ ninp₁ logw₁ logc₁ : ℕ}
variable (S₁ : ZkSide R₁ logv₁ Sig₁ C F₁ X₁ Q₁ Msg₁ Witness₁ M₁ ninp₁ logw₁ logc₁)
variable {logv₂ : ℕ} {Sig₂ F₂ X₂ Q₂ Witness₂ : Type}
  [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [Fintype X₂] [DecidableEq X₂] [Fintype Q₂] [DecidableEq Q₂] [Inhabited Msg₂]
  {M₂ ninp₂ logw₂ logc₂ : ℕ}
variable (S₂ : ZkSide R₂ logv₂ Sig₂ C F₂ X₂ Q₂ Msg₂ Witness₂ M₂ ninp₂ logw₂ logc₂)

/-- Actual two-circuit acceptance with no pair of satisfying candidates.
The intercepts add, and each prover query pays at most the larger side
slope. No independence or serial scheduling of the prover is assumed. -/
theorem forked_circuits_bound
    (ctx : Out → Ctx)
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (messages₁ : Out → ℕ → Msg₁)
    (sigAt₁ : (Input Key Ctx Msg₁ Msg₂ R₁ R₂ → C) → Ctx → Sig₁)
    (hsig₁ : ∀ p H H', AgreeOff (left p) H H' → sigAt₁ H p.ctx = sigAt₁ H' p.ctx)
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (bc₁ bq₁ : ℚ) (hc₁ : 0 ≤ bc₁) (hq₁ : 0 ≤ bq₁)
    (hpc₁ : ∀ σ, (P₁ σ).challengeBudget ≤ bc₁)
    (hpq₁ : ∀ σ, (P₁ σ).queryBudget ≤ bq₁)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (messages₂ : Out → ℕ → Msg₂)
    (sigAt₂ : (Input Key Ctx Msg₁ Msg₂ R₁ R₂ → C) → Ctx → Sig₂)
    (hsig₂ : ∀ p H H', AgreeOff (right p) H H' → sigAt₂ H p.ctx = sigAt₂ H' p.ctx)
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (bc₂ bq₂ : ℚ) (hc₂ : 0 ≤ bc₂) (hq₂ : 0 ≤ bq₂)
    (hpc₂ : ∀ σ, (P₂ σ).challengeBudget ≤ bc₂)
    (hpq₂ : ∀ σ, (P₂ σ).queryBudget ≤ bq₂)
    {N : ℕ} (tree : Tree (Input Key Ctx Msg₁ Msg₂ R₁ R₂) C Out N) :
    let rate₁ := Lfzk.AffineSide.sideRate R₁ logv₁ (Fintype.card C) bc₁ bq₁ hc₁ hq₁
    let rate₂ := Lfzk.AffineSide.sideRate R₂ logv₂ (Fintype.card C) bc₂ bq₂ hc₂ hq₂
    Bcs.FiniteProbability.density (fun H =>
      let out := (tree.run H).1
      let σ₁ := sigAt₁ H (ctx out)
      let σ₂ := sigAt₂ H (ctx out)
      (¬ ∃ ℓ₁ ℓ₂, S₁.Sat σ₁ ℓ₁ ∧ S₂.Sat σ₂ ℓ₂) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.V σ₁) (S₁.LD σ₁) (messages₁ out))
        (fun i => H (left (msgPoint (ctx out) messages₁ out i.val))) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.V σ₂) (S₂.LD σ₂) (messages₂ out))
        (fun i => H (right (msgPoint (ctx out) messages₂ out i.val)))) ≤
      rate₁.intercept + rate₂.intercept + N * max rate₁.slope rate₂.slope := by
  dsimp only
  have h₁ := Lfzk.AffineSide.side_oracle_sound S₁ hF₁ left
    (domain 0) (fun p => by simp [domain]) ctx messages₁ sigAt₁ hsig₁
    P₁ bc₁ bq₁ hc₁ hq₁ hpc₁ hpq₁
  let rate₁ := Lfzk.AffineSide.sideRate R₁ logv₁ (Fintype.card C) bc₁ bq₁ hc₁ hq₁
  let event₁ := fun out H =>
    (∀ ℓ, ¬ S₁.Sat (sigAt₁ H (ctx out)) ℓ) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds)
          (S₁.V (sigAt₁ H (ctx out))) (S₁.LD (sigAt₁ H (ctx out))) (messages₁ out))
        (fun i => H (left (msgPoint (ctx out) messages₁ out i.val)))
  have h₂ := Lfzk.AffineSide.side_oracle_sound S₂ hF₂ right
    (domain 1) (fun p => by simp [domain]) ctx messages₂ sigAt₂ hsig₂
    P₂ bc₂ bq₂ hc₂ hq₂ hpc₂ hpq₂
  let rate₂ := Lfzk.AffineSide.sideRate R₂ logv₂ (Fintype.card C) bc₂ bq₂ hc₂ hq₂
  let event₂ := fun out H =>
    (∀ ℓ, ¬ S₂.Sat (sigAt₂ H (ctx out)) ℓ) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds)
          (S₂.V (sigAt₂ H (ctx out))) (S₂.LD (sigAt₂ H (ctx out))) (messages₂ out))
        (fun i => H (right (msgPoint (ctx out) messages₂ out i.val)))
  let events : Fin 2 → Out → (Input Key Ctx Msg₁ Msg₂ R₁ R₂ → C) → Prop := ![event₁, event₂]
  let rates : Fin 2 → Rate := ![rate₁, rate₂]
  have cert : ∀ i, OracleSound (domain i) (events i) (rates i) := by
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
  have hc := oracle_parallel_certificate domain events rates cert
    (fun out H =>
      (¬ ∃ ℓ₁ ℓ₂, S₁.Sat (sigAt₁ H (ctx out)) ℓ₁ ∧ S₂.Sat (sigAt₂ H (ctx out)) ℓ₂) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds)
          (S₁.V (sigAt₁ H (ctx out))) (S₁.LD (sigAt₁ H (ctx out))) (messages₁ out))
        (fun i => H (left (msgPoint (ctx out) messages₁ out i.val))) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds)
          (S₂.V (sigAt₂ H (ctx out))) (S₂.LD (sigAt₂ H (ctx out))) (messages₂ out))
        (fun i => H (right (msgPoint (ctx out) messages₂ out i.val))))
    (by
      intro out H ⟨hn, ha₁, ha₂⟩
      by_cases h : ∃ ℓ₁, S₁.Sat (sigAt₁ H (ctx out)) ℓ₁
      · obtain ⟨ℓ₁, hl₁⟩ := h
        exact ⟨1, (fun ℓ₂ hl₂ => hn ⟨ℓ₁, ℓ₂, hl₁, hl₂⟩), ha₂⟩
      · exact ⟨0, (fun ℓ hl => h ⟨ℓ, hl⟩), ha₁⟩)
    domains_disjoint (max rate₁.slope rate₂.slope)
    (rate₁.slope_nonneg.trans (le_max_left _ _))
    (by intro i; fin_cases i; exact le_max_left _ _; exact le_max_right _ _)
  have hb := (hc N tree).cap (N : ℚ) (fun H => by
    rw [queryCost_biUnion domain domains_disjoint]
    exact queryCost_sum_le domain (ownership_of_disjoint domain domains_disjoint) tree H)
  simpa [aggregate, rates, Fin.sum_univ_succ, mul_comm] using hb

end Lfzk.AffineFork
