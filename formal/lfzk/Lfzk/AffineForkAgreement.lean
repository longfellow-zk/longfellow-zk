import Lfzk.AffineFork
import Lfzk.AffineMac

/-! Forked circuit extraction with a common MAC-bound witness value.
The binding predicate records deterministic verifier/context checks. The
counting hypotheses are the actual side data and MAC collision counts. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Lfzk.AffineFork
open Finset Bcs.AffineBlock Bcs.TotalOracle Merkle.RandomOracle
open Lfzk.NizkDeployedHash Lfzk.NizkZkTwoField Lfzk.RbrZkSplit Lfzk.RbrZkFlat Lfzk.MacSep
open scoped Classical
variable {Key Ctx Msg₁ Msg₂ : Type} {R₁ R₂ : Lfzk.CertifiedV1.Row}
  [Fintype Key] [Fintype Ctx] [Fintype Msg₁] [Fintype Msg₂]

def branch : Input Key Ctx Msg₁ Msg₂ R₁ R₂ → Fin 3
  | .inl _ => 2
  | .inr (.inl _) => 0
  | .inr (.inr _) => 1

noncomputable def branchDomain (i : Fin 3) : Finset (Input Key Ctx Msg₁ Msg₂ R₁ R₂) :=
  univ.filter (fun x => branch x = i)

theorem branchDomains_disjoint : Pairwise (fun i j => Disjoint
    (branchDomain (Key := Key) (Ctx := Ctx) (Msg₁ := Msg₁) (Msg₂ := Msg₂) (R₁ := R₁) (R₂ := R₂) i)
    (branchDomain (Key := Key) (Ctx := Ctx) (Msg₁ := Msg₁) (Msg₂ := Msg₂) (R₁ := R₁) (R₂ := R₂) j)) := by
  intro i j hn
  apply disjoint_left.mpr
  intro x hi hj
  exact hn ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)
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

theorem forked_agreement_bound
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
    {D Enc Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
    (selectedKey : Out → Key)
    (context : (Input Key Ctx Msg₁ Msg₂ R₁ R₂ → C) → Key → (D × D) × List (Enc × D))
    (hoff : ∀ k H H', AgreeOff (.inl k) H H' → context H k = context H' k)
    (binding : Out → (Input Key Ctx Msg₁ Msg₂ R₁ R₂ → C) → Prop)
    (cands₁ : ((D × D) × List (Enc × D)) → Finset Witness₁)
    (cands₂ : ((D × D) × List (Enc × D)) → Finset Witness₂)
    {B₁ B₂ kmac nblk : ℕ}
    (hcard₁ : ∀ κ, (cands₁ κ).card ≤ B₁)
    (hcard₂ : ∀ κ, (cands₂ κ).card ≤ B₂)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : Witness₁ → Fmac → Fin nblk → Fmac) (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (aP : ((D × D) × List (Enc × D)) → Fmac) (decode : C → Fmac)
    (hbal : ∀ x, (univ.filter fun c => decode c = x).card ≤ kmac)
    (tag : Out → Fin nblk → Fmac)
    (hcands₁ : ∀ out H, binding out H → ∀ a, S₁.Good (sigAt₁ H (ctx out)) a →
      a ∈ cands₁ (context H (selectedKey out)))
    (hcands₂ : ∀ out H, binding out H → ∀ a, S₂.Good (sigAt₂ H (ctx out)) a →
      a ∈ cands₂ (context H (selectedKey out)))
    (hrow₁ : ∀ out H, binding out H → ∀ a, S₁.Good (sigAt₁ H (ctx out)) a →
      mac₁ a (aP (context H (selectedKey out)) + decode (H (.inl (selectedKey out)))) = tag out)
    (hrow₂ : ∀ out H, binding out H → ∀ a, S₂.Good (sigAt₂ H (ctx out)) a →
      mac₂ a (aP (context H (selectedKey out)) + decode (H (.inl (selectedKey out)))) = tag out)
    {N : ℕ} (tree : Tree (Input Key Ctx Msg₁ Msg₂ R₁ R₂) C Out N) :
    let rate₁ := Lfzk.AffineSide.sideRate R₁ logv₁ (Fintype.card C) bc₁ bq₁ hc₁ hq₁
    let rate₂ := Lfzk.AffineSide.sideRate R₂ logv₂ (Fintype.card C) bc₂ bq₂ hc₂ hq₂
    Bcs.FiniteProbability.density (fun H =>
      let out := (tree.run H).1
      let σ₁ := sigAt₁ H (ctx out)
      let σ₂ := sigAt₂ H (ctx out)
      binding out H ∧
      (¬ ∃ a₁ a₂, S₁.Good σ₁ a₁ ∧ S₂.Good σ₂ a₂ ∧ common₁ a₁ = common₂ a₂) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.V σ₁) (S₁.LD σ₁) (messages₁ out))
        (fun i => H (left (msgPoint (ctx out) messages₁ out i.val))) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.V σ₂) (S₂.LD σ₂) (messages₂ out))
        (fun i => H (right (msgPoint (ctx out) messages₂ out i.val)))) ≤
      rate₁.intercept + rate₂.intercept + (B₁ * B₂ * kmac : ℚ) / Fintype.card C +
        N * max (max rate₁.slope rate₂.slope) ((B₁ * B₂ * kmac : ℚ) / Fintype.card C) := by
  dsimp only
  have h₁ := Lfzk.AffineSide.side_oracle_sound S₁ hF₁ left
    (branchDomain 0) (fun p => by simp [branchDomain, branch, left]) ctx messages₁ sigAt₁ hsig₁
    P₁ bc₁ bq₁ hc₁ hq₁ hpc₁ hpq₁
  let rate₁ := Lfzk.AffineSide.sideRate R₁ logv₁ (Fintype.card C) bc₁ bq₁ hc₁ hq₁
  let event₁ := fun out H =>
    (∀ ℓ, ¬ S₁.Sat (sigAt₁ H (ctx out)) ℓ) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds)
          (S₁.V (sigAt₁ H (ctx out))) (S₁.LD (sigAt₁ H (ctx out))) (messages₁ out))
        (fun i => H (left (msgPoint (ctx out) messages₁ out i.val)))
  have h₂ := Lfzk.AffineSide.side_oracle_sound S₂ hF₂ right
    (branchDomain 1) (fun p => by simp [branchDomain, branch, right]) ctx messages₂ sigAt₂ hsig₂
    P₂ bc₂ bq₂ hc₂ hq₂ hpc₂ hpq₂
  let rate₂ := Lfzk.AffineSide.sideRate R₂ logv₂ (Fintype.card C) bc₂ bq₂ hc₂ hq₂
  let event₂ := fun out H =>
    (∀ ℓ, ¬ S₂.Sat (sigAt₂ H (ctx out)) ℓ) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds)
          (S₂.V (sigAt₂ H (ctx out))) (S₂.LD (sigAt₂ H (ctx out))) (messages₂ out))
        (fun i => H (right (msgPoint (ctx out) messages₂ out i.val)))
  let keyEmbed : Key ↪ Input Key Ctx Msg₁ Msg₂ R₁ R₂ := ⟨Sum.inl, Sum.inl_injective⟩
  let eps : ℚ := (B₁ * B₂ * kmac : ℚ) / Fintype.card C
  let km := max (max rate₁.slope rate₂.slope) eps
  let rateM := Rate.diagonal eps (by dsimp [eps]; positivity)
  let eventM := fun out H => SepMacBad
    (cands₁ (context H (selectedKey out))) (cands₂ (context H (selectedKey out)))
    common₁ common₂ mac₁ mac₂
    (aP (context H (selectedKey out)) + decode (H (.inl (selectedKey out))))
  have hM := Lfzk.AffineMac.mac_oracle_sound keyEmbed (branchDomain 2)
    (fun k => by simp [branchDomain, branch, keyEmbed]) selectedKey context hoff
    cands₁ cands₂ hcard₁ hcard₂ common₁ common₂ mac₁ mac₂ hcoll aP decode hbal
  let events : Fin 3 → Out → (Input Key Ctx Msg₁ Msg₂ R₁ R₂ → C) → Prop := ![event₁, event₂, eventM]
  let rates : Fin 3 → Rate := ![rate₁, rate₂, rateM]
  have cert : ∀ i, OracleSound (branchDomain i) (events i) (rates i) := by
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
    · exact hM
  have hc := oracle_parallel branchDomain events rates cert
    (fun out H => binding out H ∧
      (¬ ∃ a₁ a₂, S₁.Good (sigAt₁ H (ctx out)) a₁ ∧ S₂.Good (sigAt₂ H (ctx out)) a₂ ∧
        common₁ a₁ = common₂ a₂) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds)
          (S₁.V (sigAt₁ H (ctx out))) (S₁.LD (sigAt₁ H (ctx out))) (messages₁ out))
        (fun i => H (left (msgPoint (ctx out) messages₁ out i.val))) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds)
          (S₂.V (sigAt₂ H (ctx out))) (S₂.LD (sigAt₂ H (ctx out))) (messages₂ out))
        (fun i => H (right (msgPoint (ctx out) messages₂ out i.val))))
    (by
      intro out H ⟨hbind, hn, ha₁, ha₂⟩
      by_cases h₁ : ∃ ℓ, S₁.Sat (sigAt₁ H (ctx out)) ℓ
      · obtain ⟨ℓ₁, hl₁⟩ := h₁
        by_cases h₂ : ∃ ℓ, S₂.Sat (sigAt₂ H (ctx out)) ℓ
        · obtain ⟨ℓ₂, hl₂⟩ := h₂
          let a₁ := S₁.wit (sigAt₁ H (ctx out)) ℓ₁
          let a₂ := S₂.wit (sigAt₂ H (ctx out)) ℓ₂
          have hg₁ : S₁.Good (sigAt₁ H (ctx out)) a₁ := ⟨ℓ₁, hl₁, rfl⟩
          have hg₂ : S₂.Good (sigAt₂ H (ctx out)) a₂ := ⟨ℓ₂, hl₂, rfl⟩
          exact ⟨2, a₁, hcands₁ out H hbind a₁ hg₁, a₂, hcands₂ out H hbind a₂ hg₂,
            (fun he => hn ⟨a₁, a₂, hg₁, hg₂, he⟩),
            (hrow₁ out H hbind a₁ hg₁).trans (hrow₂ out H hbind a₂ hg₂).symm⟩
        · exact ⟨1, (fun ℓ hl => h₂ ⟨ℓ, hl⟩), ha₂⟩
      · exact ⟨0, (fun ℓ hl => h₁ ⟨ℓ, hl⟩), ha₁⟩)
    branchDomains_disjoint km (rateM.slope_nonneg.trans (le_max_right _ _))
    (by
      intro i
      fin_cases i
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact le_max_right _ _) tree
  simpa [rates, rateM, Rate.diagonal, Fin.sum_univ_succ, add_assoc] using hc

end Lfzk.AffineFork
