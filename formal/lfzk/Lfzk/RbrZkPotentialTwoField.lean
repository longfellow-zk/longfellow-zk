import Lfzk.RbrZkPotentialPath
import Lfzk.RbrZkPotentialSide
import Lfzk.NizkZkDeployedHashSepMac

/-!
# The merged two-field graded charge

The key point retains the separate-witness MAC collision event.  Each side
point carries the exact field/challenge/query potential of its own built
system.  The ancestor slices are those of the deployed two-field hash input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkZkDeployedHash

open Finset Bcs Lfzk.NizkGrinding Lfzk.NizkDeployedHash
  Lfzk.NizkDeployedHashTwoField
  Lfzk.NizkZkTwoField Lfzk.RbrZkFlat
  Lfzk.NizkZk Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.RbrLayerStepS
open Lfzk.NizkAdaptiveTwoField (SideCtx)
open Lfzk.MacSep
open scoped Classical

variable {R₁ R₂ : Lfzk.CertifiedV1.Row} {logv₁ logv₂ : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C]
variable {D : Type} {Enc X : Type}
variable {F₁ X₁ Q₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁]
  [DecidableEq F₁] [SumcheckInterp F₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Q₁] [DecidableEq Q₁] [Inhabited Msg₁]
  {M₁ ninp₁ logw₁ logc₁ : ℕ}
variable {F₂ X₂ Q₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂]
  [DecidableEq F₂] [SumcheckInterp F₂] [Fintype X₂] [DecidableEq X₂]
  [Fintype Q₂] [DecidableEq Q₂] [Inhabited Msg₂]
  {M₂ ninp₂ logw₂ logc₂ : ℕ}

private abbrev PKey (D Enc : Type) := (D × D) × List (Enc × D)
private abbrev PSig (D C X Enc : Type) := PKey D Enc × C × X

variable (S₁ : ZkSide R₁ logv₁ (PSig D C X Enc) C F₁ X₁ Q₁ Msg₁ Witness₁
  M₁ ninp₁ logw₁ logc₁)
variable (S₂ : ZkSide R₂ logv₂ (PSig D C X Enc) C F₂ X₂ Q₂ Msg₂ Witness₂
  M₂ ninp₂ logw₂ logc₂)

omit [DecidableEq C] in
/-- The exact key-point count for two separately witnessed MAC circuits. -/
theorem twoFieldMacKey_local
    {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
    {nblk : ℕ}
    (cands₁ : PKey D Enc → Finset Witness₁)
    (cands₂ : PKey D Enc → Finset Witness₂)
    {B₁ B₂ kmac : ℕ}
    (hcard₁ : ∀ κ, (cands₁ κ).card ≤ B₁)
    (hcard₂ : ∀ κ, (cands₂ κ).card ≤ B₂)
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : Witness₁ → Fmac → Fin nblk → Fmac)
    (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (aP : PKey D Enc → Fmac) (decode : C → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (κ : PKey D Enc) :
    (∑ c : C, if SepMacBad (cands₁ κ) (cands₂ κ)
      common₁ common₂ mac₁ mac₂ (aP κ + decode c) then (1 : ℚ) else 0) ≤
      (B₁ * B₂ * kmac : ℚ) := by
  have hc := sepMacBad_card_le (cands₁ κ) (cands₂ κ)
    common₁ common₂ mac₁ mac₂ hcoll (aP κ) decode hbal
  have hn : (univ.filter fun c : C => SepMacBad (cands₁ κ) (cands₂ κ)
      common₁ common₂ mac₁ mac₂ (aP κ + decode c)).card ≤ B₁ * B₂ * kmac :=
    hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul (hcard₁ κ) (hcard₂ κ)))
  have hq : ((univ.filter fun c : C => SepMacBad (cands₁ κ) (cands₂ κ)
      common₁ common₂ mac₁ mac₂ (aP κ + decode c)).card : ℚ) ≤
      (B₁ * B₂ * kmac : ℚ) := by exact_mod_cast hn
  simpa [Finset.sum_ite] using hq

omit [DecidableEq C] [Inhabited Msg₁] [Inhabited Msg₂] in
/-- If both sides have satisfying candidates but no pair agrees on the
common value, their two accepted MAC rows force the key-point event.
The candidate lists depend only on the commitment context. -/
theorem twoFieldMacKey_of_disagreement
    {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
    {nblk : ℕ}
    (cands₁ : PKey D Enc → Finset Witness₁)
    (cands₂ : PKey D Enc → Finset Witness₂)
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : Witness₁ → Fmac → Fin nblk → Fmac)
    (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (aP : PKey D Enc → Fmac) (decode : C → Fmac)
    (tag : Fin nblk → Fmac)
    (σ : PSig D C X Enc) (c : C)
    (hcands₁ : ∀ a, S₁.Good σ a → a ∈ cands₁ σ.1)
    (hcands₂ : ∀ a, S₂.Good σ a → a ∈ cands₂ σ.1)
    (hrow₁ : ∀ a, S₁.Good σ a →
      mac₁ a (aP σ.1 + decode c) = tag)
    (hrow₂ : ∀ a, S₂.Good σ a →
      mac₂ a (aP σ.1 + decode c) = tag)
    (hdisagree : ¬ ∃ a₁ a₂, S₁.Good σ a₁ ∧ S₂.Good σ a₂ ∧
      common₁ a₁ = common₂ a₂)
    (hgood₁ : ¬ ZkFails S₁.Sat σ)
    (hgood₂ : ¬ ZkFails S₂.Sat σ) :
    SepMacBad (cands₁ σ.1) (cands₂ σ.1)
      common₁ common₂ mac₁ mac₂ (aP σ.1 + decode c) := by
  simp only [ZkFails, not_forall, not_not] at hgood₁ hgood₂
  obtain ⟨ℓ₁, hs₁⟩ := hgood₁
  obtain ⟨ℓ₂, hs₂⟩ := hgood₂
  let a₁ := S₁.wit σ ℓ₁
  let a₂ := S₂.wit σ ℓ₂
  have hg₁ : S₁.Good σ a₁ := ⟨ℓ₁, hs₁, rfl⟩
  have hg₂ : S₂.Good σ a₂ := ⟨ℓ₂, hs₂, rfl⟩
  exact ⟨a₁, hcands₁ a₁ hg₁, a₂, hcands₂ a₂ hg₂,
    (fun heq => hdisagree ⟨a₁, a₂, hg₁, hg₂, heq⟩),
    (hrow₁ a₁ hg₁).trans (hrow₂ a₂ hg₂).symm⟩

/-- The extraction target is a pair of satisfying side witnesses with the
same MAC-bound common value. -/
def twoFieldGoodPair {nblk : ℕ} {Fmac : Type}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (σ : PSig D C X Enc) (a : Witness₁ × Witness₂) : Prop :=
  S₁.Good σ a.1 ∧ S₂.Good σ a.2 ∧ common₁ a.1 = common₂ a.2

/-- Choice of a pair is an analysis-side extractor: the committed lift
lists, represented by the two `ZkSide`s, contain every possible output. -/
noncomputable def twoFieldExtract {nblk : ℕ} {Fmac : Type}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (σ : PSig D C X Enc) : Option (Witness₁ × Witness₂) :=
  if h : ∃ a : Witness₁ × Witness₂,
      twoFieldGoodPair S₁ S₂ common₁ common₂ σ a then
    some (Classical.choose h)
  else none

omit [DecidableEq C] [Inhabited Msg₁] [Inhabited Msg₂] in
theorem twoFieldExtract_valid {nblk : ℕ} {Fmac : Type}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (σ : PSig D C X Enc) (a : Witness₁ × Witness₂)
    (h : twoFieldExtract S₁ S₂ common₁ common₂ σ = some a) :
    twoFieldGoodPair S₁ S₂ common₁ common₂ σ a := by
  unfold twoFieldExtract at h
  split_ifs at h with hex
  · have heq := Option.some.inj h
    subst a
    exact Classical.choose_spec hex

omit [DecidableEq C] [Inhabited Msg₁] [Inhabited Msg₂] in
theorem twoFieldExtract_none_iff {nblk : ℕ} {Fmac : Type}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (σ : PSig D C X Enc) :
    twoFieldExtract S₁ S₂ common₁ common₂ σ = none ↔
      ¬ ∃ a₁ a₂, S₁.Good σ a₁ ∧ S₂.Good σ a₂ ∧
        common₁ a₁ = common₂ a₂ := by
  classical
  unfold twoFieldExtract
  simp only [twoFieldGoodPair]
  by_cases h : ∃ a : Witness₁ × Witness₂,
      S₁.Good σ a.1 ∧ S₂.Good σ a.2 ∧ common₁ a.1 = common₂ a.2
  · simp only [dif_pos h, reduceCtorEq, false_iff]
    obtain ⟨a, ha⟩ := h
    exact fun hf => hf ⟨a.1, a.2, ha⟩
  · simp only [dif_neg h, true_iff]
    intro ⟨a₁, a₂, ha⟩
    exact h ⟨(a₁, a₂), ha⟩

omit [DecidableEq C] [Inhabited Msg₁] [Inhabited Msg₂] in
/-- Failure of the actual pair extractor is precisely the disagreement
premise consumed by the key-point MAC argument. -/
theorem twoFieldMacKey_of_extract_none
    {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
    {nblk : ℕ}
    (cands₁ : PKey D Enc → Finset Witness₁)
    (cands₂ : PKey D Enc → Finset Witness₂)
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : Witness₁ → Fmac → Fin nblk → Fmac)
    (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (aP : PKey D Enc → Fmac) (decode : C → Fmac)
    (tag : Fin nblk → Fmac)
    (σ : PSig D C X Enc) (c : C)
    (hcands₁ : ∀ a, S₁.Good σ a → a ∈ cands₁ σ.1)
    (hcands₂ : ∀ a, S₂.Good σ a → a ∈ cands₂ σ.1)
    (hrow₁ : ∀ a, S₁.Good σ a →
      mac₁ a (aP σ.1 + decode c) = tag)
    (hrow₂ : ∀ a, S₂.Good σ a →
      mac₂ a (aP σ.1 + decode c) = tag)
    (hfail : twoFieldExtract S₁ S₂ common₁ common₂ σ = none)
    (hgood₁ : ¬ ZkFails S₁.Sat σ)
    (hgood₂ : ¬ ZkFails S₂.Sat σ) :
    SepMacBad (cands₁ σ.1) (cands₂ σ.1)
      common₁ common₂ mac₁ mac₂ (aP σ.1 + decode c) := by
  exact twoFieldMacKey_of_disagreement S₁ S₂ cands₁ cands₂ common₁ common₂
    mac₁ mac₂ aP decode tag σ c hcands₁ hcands₂ hrow₁ hrow₂
    ((twoFieldExtract_none_iff S₁ S₂ common₁ common₂ σ).mp hfail)
    hgood₁ hgood₂

/-- A single rational charge on the three disjoint classes of deployed
hash inputs.  The two `ZkFails` guards charge only extraction failures;
the key point is fixed by the committed cut trace. -/
noncomputable def twoFieldPotentialCharge
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
    (κ : PKey D Enc)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds)
    (pref : Fin (pts2.slot p) → C) (c : C) : ℚ :=
  match p with
  | Sum.inl _ => if keyBad κ c then 1 else 0
  | Sum.inr (Sum.inl p) =>
      let σ : PSig D C X Enc := (κ, p.ctx.2.1, p.ctx.2.2)
      if ZkFails S₁.Sat σ then
        sidePointCharge (H := S₁.H σ) (Sat := S₁.Sat σ)
          (S₁.LD σ) (P₁ σ) p
          (fun j => pget dflt pref (1 + j.val)) c
      else 0
  | Sum.inr (Sum.inr p) =>
      let σ : PSig D C X Enc := (κ, p.ctx.1.2.1, p.ctx.1.2.2)
      if ZkFails S₂.Sat σ then
        sidePointCharge (H := S₂.H σ) (Sat := S₂.Sat σ)
          (S₂.LD σ) (P₂ σ) p
          (fun j => pget dflt pref
            (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + j.val)) c
      else 0

omit [DecidableEq C] in
theorem twoFieldPotentialCharge_nonneg
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
    (κ : PKey D Enc)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds)
    (pref : Fin (pts2.slot p) → C) (c : C) :
    0 ≤ twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt κ p pref c := by
  rcases p with p | p | p
  · simp only [twoFieldPotentialCharge]
    split_ifs <;> norm_num
  · simp only [twoFieldPotentialCharge]
    split_ifs
    · exact sidePointCharge_nonneg _ _ _ _ _
    · exact le_refl _
  · simp only [twoFieldPotentialCharge]
    split_ifs
    · exact sidePointCharge_nonneg _ _ _ _ _
    · exact le_refl _

/-- A context-independent point budget for the merged schedule.  The
concrete side budgets can vary by role, including different graded budgets
at the combination challenge and at the final query. -/
def twoFieldPotentialBudget
    (keyBudget : ℚ)
    (budget₁ : MPoint (SideCtx D C X) Msg₁ R₁.params.nl R₁.params.rounds → ℚ)
    (budget₂ : MPoint (SideCtx D C X ×
      (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → Msg₁))
      Msg₂ R₂.params.nl R₂.params.rounds → ℚ) :
    Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → ℚ
  | Sum.inl _ => keyBudget
  | Sum.inr (Sum.inl p) => budget₁ p
  | Sum.inr (Sum.inr p) => budget₂ p

/-- The exact total and worst-slot budgets used by the two-field potential
compiler.  Terminal inputs are rational hash-answer counts. -/
def twoFieldPotentialTotalBudget (R₁ R₂ : Lfzk.CertifiedV1.Row)
    (logv₁ logv₂ cardC : ℕ)
    (keyBudget βchallenge₁ βquery₁ βchallenge₂ βquery₂ : ℚ) : ℚ :=
  keyBudget +
    (sideFieldSlotBudget R₁ logv₁ cardC + βchallenge₁ + βquery₁) +
    (sideFieldSlotBudget R₂ logv₂ cardC + βchallenge₂ + βquery₂)

/-- The exact slot sum is controlled by field densities for any combined
challenge alphabet.  MAC balance converts the decoder multiplicity into a
single field-sized key term; no assumption `|C| = |Fmac|` is needed. -/
theorem twoFieldPotentialTotalBudget_le_density
    (R₁ R₂ : Lfzk.CertifiedV1.Row)
    (logv₁ logv₂ cardC cardFmac B₁ B₂ kmac : ℕ)
    (hC : 0 < cardC) (hFmac : 0 < cardFmac)
    (hF₁ : 0 < R₁.params.row.fieldSize)
    (hF₂ : 0 < R₂.params.row.fieldSize)
    (hmac : kmac * cardFmac ≤ cardC)
    (b₁c b₁q b₂c b₂q : ℚ)
    (hb₁c : 0 ≤ b₁c) (hb₁q : 0 ≤ b₁q)
    (hb₂c : 0 ≤ b₂c) (hb₂q : 0 ≤ b₂q) :
    twoFieldPotentialTotalBudget R₁ R₂ logv₁ logv₂ cardC
        (B₁ * B₂ * kmac : ℚ)
        (max 0 ((cardC : ℚ) * b₁c))
        (max 0 ((cardC : ℚ) * b₁q))
        (max 0 ((cardC : ℚ) * b₂c))
        (max 0 ((cardC : ℚ) * b₂q)) / cardC ≤
      (B₁ * B₂ : ℚ) / cardFmac +
        (R₁.cardCand : ℚ) * zkFieldDensity R₁ logv₁ + b₁c + b₁q +
        (R₂.cardCand : ℚ) * zkFieldDensity R₂ logv₂ + b₂c + b₂q := by
  have hc : (0 : ℚ) < cardC := by exact_mod_cast hC
  have hf : (0 : ℚ) < cardFmac := by exact_mod_cast hFmac
  have hk : (B₁ * B₂ * kmac : ℚ) ≤
      (cardC : ℚ) * ((B₁ * B₂ : ℚ) / cardFmac) := by
    have hh : (B₁ * B₂ * kmac) * cardFmac ≤ (B₁ * B₂) * cardC := by
      calc
        (B₁ * B₂ * kmac) * cardFmac =
            (B₁ * B₂) * (kmac * cardFmac) := by ring
        _ ≤ (B₁ * B₂) * cardC := Nat.mul_le_mul_left _ hmac
    have hhq : ((B₁ * B₂ * kmac) * cardFmac : ℚ) ≤
        ((B₁ * B₂) * cardC : ℕ) := by exact_mod_cast hh
    calc
      (B₁ * B₂ * kmac : ℚ) =
          ((B₁ * B₂ * kmac) * cardFmac : ℚ) / cardFmac := by
            field_simp
      _ ≤ ((B₁ * B₂) * cardC : ℕ) / (cardFmac : ℚ) :=
        div_le_div_of_nonneg_right hhq hf.le
      _ = (cardC : ℚ) * ((B₁ * B₂ : ℚ) / cardFmac) := by
        push_cast
        ring
  have hfield₁ := sideFieldSlotBudget_le_density R₁ logv₁ cardC hF₁
  have hfield₂ := sideFieldSlotBudget_le_density R₂ logv₂ cardC hF₂
  have hβ₁c : max 0 ((cardC : ℚ) * b₁c) = (cardC : ℚ) * b₁c :=
    max_eq_right (mul_nonneg hc.le hb₁c)
  have hβ₁q : max 0 ((cardC : ℚ) * b₁q) = (cardC : ℚ) * b₁q :=
    max_eq_right (mul_nonneg hc.le hb₁q)
  have hβ₂c : max 0 ((cardC : ℚ) * b₂c) = (cardC : ℚ) * b₂c :=
    max_eq_right (mul_nonneg hc.le hb₂c)
  have hβ₂q : max 0 ((cardC : ℚ) * b₂q) = (cardC : ℚ) * b₂q :=
    max_eq_right (mul_nonneg hc.le hb₂q)
  rw [hβ₁c, hβ₁q, hβ₂c, hβ₂q]
  unfold twoFieldPotentialTotalBudget
  rw [div_le_iff₀ hc]
  nlinarith [hk, hfield₁, hfield₂]

def twoFieldPotentialMaxBudget (R₁ R₂ : Lfzk.CertifiedV1.Row)
    (logv₁ logv₂ cardC : ℕ)
    (keyBudget βchallenge₁ βquery₁ βchallenge₂ βquery₂ : ℚ) : ℚ :=
  max keyBudget
    (max (max (sideFieldMaxBudget R₁ logv₁ cardC : ℚ)
        (max βchallenge₁ βquery₁))
      (max (sideFieldMaxBudget R₂ logv₂ cardC : ℚ)
        (max βchallenge₂ βquery₂)))

/-- The worst-slot count also admits an alphabet-independent density bound.
The graded terminal costs must fit under the row's registered per-query
coefficient; the slot sum itself may be substantially sharper. -/
theorem twoFieldPotentialMaxBudget_le_density
    (R₁ R₂ : Lfzk.CertifiedV1.Row)
    (logv₁ logv₂ cardC cardFmac B₁ B₂ kmac : ℕ)
    (hC : 0 < cardC) (hFmac : 0 < cardFmac)
    (hF₁ : 0 < R₁.params.row.fieldSize)
    (hF₂ : 0 < R₂.params.row.fieldSize)
    (hmac : kmac * cardFmac ≤ cardC)
    (b₁c b₁q b₂c b₂q : ℚ)
    (hb₁c : 0 ≤ b₁c) (hb₁q : 0 ≤ b₁q)
    (hb₂c : 0 ≤ b₂c) (hb₂q : 0 ≤ b₂q)
    (h₁c : b₁c ≤ R₁.zkCoefficient logv₁)
    (h₁q : b₁q ≤ R₁.zkCoefficient logv₁)
    (h₂c : b₂c ≤ R₂.zkCoefficient logv₂)
    (h₂q : b₂q ≤ R₂.zkCoefficient logv₂) :
    twoFieldPotentialMaxBudget R₁ R₂ logv₁ logv₂ cardC
        (B₁ * B₂ * kmac : ℚ)
        (max 0 ((cardC : ℚ) * b₁c))
        (max 0 ((cardC : ℚ) * b₁q))
        (max 0 ((cardC : ℚ) * b₂c))
        (max 0 ((cardC : ℚ) * b₂q)) ≤
      (cardC : ℚ) *
        max (max (R₁.zkCoefficient logv₁)
          (R₂.zkCoefficient logv₂))
          ((B₁ * B₂ : ℚ) / cardFmac) := by
  have hc : (0 : ℚ) ≤ cardC := Nat.cast_nonneg _
  have hf : (0 : ℚ) < cardFmac := by exact_mod_cast hFmac
  let K : ℚ := max (max (R₁.zkCoefficient logv₁)
    (R₂.zkCoefficient logv₂)) ((B₁ * B₂ : ℚ) / cardFmac)
  have hk : (B₁ * B₂ * kmac : ℚ) ≤
      (cardC : ℚ) * K := by
    have hh : (B₁ * B₂ * kmac) * cardFmac ≤
        (B₁ * B₂) * cardC := by
      calc
        (B₁ * B₂ * kmac) * cardFmac =
            (B₁ * B₂) * (kmac * cardFmac) := by ring
        _ ≤ (B₁ * B₂) * cardC := Nat.mul_le_mul_left _ hmac
    have hhq : ((B₁ * B₂ * kmac) * cardFmac : ℚ) ≤
        ((B₁ * B₂) * cardC : ℕ) := by exact_mod_cast hh
    have hkey : (B₁ * B₂ * kmac : ℚ) ≤
        (cardC : ℚ) * ((B₁ * B₂ : ℚ) / cardFmac) := by
      calc
        (B₁ * B₂ * kmac : ℚ) =
            ((B₁ * B₂ * kmac) * cardFmac : ℚ) / cardFmac := by
              field_simp
        _ ≤ ((B₁ * B₂) * cardC : ℕ) / (cardFmac : ℚ) :=
          div_le_div_of_nonneg_right hhq hf.le
        _ = (cardC : ℚ) * ((B₁ * B₂ : ℚ) / cardFmac) := by
          push_cast
          ring
    exact hkey.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hc)
  have hfield₁ : (sideFieldMaxBudget R₁ logv₁ cardC : ℚ) ≤
      (cardC : ℚ) * K :=
    (sideFieldMaxBudget_le_density R₁ logv₁ cardC hC hF₁).trans
      (mul_le_mul_of_nonneg_left
        ((le_max_left _ _).trans (le_max_left _ _)) hc)
  have hfield₂ : (sideFieldMaxBudget R₂ logv₂ cardC : ℚ) ≤
      (cardC : ℚ) * K :=
    (sideFieldMaxBudget_le_density R₂ logv₂ cardC hC hF₂).trans
      (mul_le_mul_of_nonneg_left
        ((le_max_right _ _).trans (le_max_left _ _)) hc)
  have hβ₁c : max 0 ((cardC : ℚ) * b₁c) ≤ (cardC : ℚ) * K := by
    rw [max_eq_right (mul_nonneg hc hb₁c)]
    exact mul_le_mul_of_nonneg_left
      (h₁c.trans ((le_max_left _ _).trans (le_max_left _ _))) hc
  have hβ₁q : max 0 ((cardC : ℚ) * b₁q) ≤ (cardC : ℚ) * K := by
    rw [max_eq_right (mul_nonneg hc hb₁q)]
    exact mul_le_mul_of_nonneg_left
      (h₁q.trans ((le_max_left _ _).trans (le_max_left _ _))) hc
  have hβ₂c : max 0 ((cardC : ℚ) * b₂c) ≤ (cardC : ℚ) * K := by
    rw [max_eq_right (mul_nonneg hc hb₂c)]
    exact mul_le_mul_of_nonneg_left
      (h₂c.trans ((le_max_right _ _).trans (le_max_left _ _))) hc
  have hβ₂q : max 0 ((cardC : ℚ) * b₂q) ≤ (cardC : ℚ) * K := by
    rw [max_eq_right (mul_nonneg hc hb₂q)]
    exact mul_le_mul_of_nonneg_left
      (h₂q.trans ((le_max_right _ _).trans (le_max_left _ _))) hc
  unfold twoFieldPotentialMaxBudget
  exact max_le hk (max_le (max_le hfield₁ (max_le hβ₁c hβ₁q))
    (max_le hfield₂ (max_le hβ₂c hβ₂q)))

/-- The complete rational hash-answer contribution of the extraction
compiler, including its unchanged factor of `N`, in density form. -/
theorem twoFieldPotentialCombinedBudget_le_density
    (R₁ R₂ : Lfzk.CertifiedV1.Row)
    (logv₁ logv₂ cardC cardFmac B₁ B₂ kmac N : ℕ)
    (hC : 0 < cardC) (hFmac : 0 < cardFmac)
    (hF₁ : 0 < R₁.params.row.fieldSize)
    (hF₂ : 0 < R₂.params.row.fieldSize)
    (hmac : kmac * cardFmac ≤ cardC)
    (b₁c b₁q b₂c b₂q : ℚ)
    (hb₁c : 0 ≤ b₁c) (hb₁q : 0 ≤ b₁q)
    (hb₂c : 0 ≤ b₂c) (hb₂q : 0 ≤ b₂q)
    (h₁c : b₁c ≤ R₁.zkCoefficient logv₁)
    (h₁q : b₁q ≤ R₁.zkCoefficient logv₁)
    (h₂c : b₂c ≤ R₂.zkCoefficient logv₂)
    (h₂q : b₂q ≤ R₂.zkCoefficient logv₂) :
    ((N : ℚ) *
        twoFieldPotentialMaxBudget R₁ R₂ logv₁ logv₂ cardC
          (B₁ * B₂ * kmac : ℚ)
          (max 0 ((cardC : ℚ) * b₁c))
          (max 0 ((cardC : ℚ) * b₁q))
          (max 0 ((cardC : ℚ) * b₂c))
          (max 0 ((cardC : ℚ) * b₂q)) +
      twoFieldPotentialTotalBudget R₁ R₂ logv₁ logv₂ cardC
        (B₁ * B₂ * kmac : ℚ)
        (max 0 ((cardC : ℚ) * b₁c))
        (max 0 ((cardC : ℚ) * b₁q))
        (max 0 ((cardC : ℚ) * b₂c))
        (max 0 ((cardC : ℚ) * b₂q))) / cardC ≤
      (B₁ * B₂ : ℚ) / cardFmac +
        (R₁.cardCand : ℚ) * zkFieldDensity R₁ logv₁ + b₁c + b₁q +
        (R₂.cardCand : ℚ) * zkFieldDensity R₂ logv₂ + b₂c + b₂q +
        N * max (max (R₁.zkCoefficient logv₁)
          (R₂.zkCoefficient logv₂))
          ((B₁ * B₂ : ℚ) / cardFmac) := by
  have hc : (0 : ℚ) < cardC := by exact_mod_cast hC
  have hmax := twoFieldPotentialMaxBudget_le_density R₁ R₂
    logv₁ logv₂ cardC cardFmac B₁ B₂ kmac hC hFmac hF₁ hF₂ hmac
    b₁c b₁q b₂c b₂q hb₁c hb₁q hb₂c hb₂q h₁c h₁q h₂c h₂q
  have htotal := twoFieldPotentialTotalBudget_le_density R₁ R₂
    logv₁ logv₂ cardC cardFmac B₁ B₂ kmac hC hFmac hF₁ hF₂ hmac
    b₁c b₁q b₂c b₂q hb₁c hb₁q hb₂c hb₂q
  rw [div_le_iff₀ hc] at htotal ⊢
  have hN := mul_le_mul_of_nonneg_left hmax
    (Nat.cast_nonneg N : (0 : ℚ) ≤ N)
  nlinarith [hN, htotal]

/-- Compact public form of the hash-answer part of the compiled extraction
bound.  The arguments are per-answer densities, and the function handles
conversion to exact rational answer counts. -/
def gradedCombinedBudget (R₁ R₂ : Lfzk.CertifiedV1.Row)
    (logv₁ logv₂ cardC N : ℕ)
    (keyBudget b₁c b₁q b₂c b₂q : ℚ) : ℚ :=
  let β₁c := max 0 ((cardC : ℚ) * b₁c)
  let β₁q := max 0 ((cardC : ℚ) * b₁q)
  let β₂c := max 0 ((cardC : ℚ) * b₂c)
  let β₂q := max 0 ((cardC : ℚ) * b₂q)
  ((N : ℚ) * twoFieldPotentialMaxBudget R₁ R₂ logv₁ logv₂ cardC
      keyBudget β₁c β₁q β₂c β₂q +
    twoFieldPotentialTotalBudget R₁ R₂ logv₁ logv₂ cardC
      keyBudget β₁c β₁q β₂c β₂q) / cardC

/-- The compact budget inherits the alphabet-independent bound. -/
theorem gradedCombinedBudget_le_density
    (R₁ R₂ : Lfzk.CertifiedV1.Row)
    (logv₁ logv₂ cardC cardFmac B₁ B₂ kmac N : ℕ)
    (hC : 0 < cardC) (hFmac : 0 < cardFmac)
    (hF₁ : 0 < R₁.params.row.fieldSize)
    (hF₂ : 0 < R₂.params.row.fieldSize)
    (hmac : kmac * cardFmac ≤ cardC)
    (b₁c b₁q b₂c b₂q : ℚ)
    (hb₁c : 0 ≤ b₁c) (hb₁q : 0 ≤ b₁q)
    (hb₂c : 0 ≤ b₂c) (hb₂q : 0 ≤ b₂q)
    (h₁c : b₁c ≤ R₁.zkCoefficient logv₁)
    (h₁q : b₁q ≤ R₁.zkCoefficient logv₁)
    (h₂c : b₂c ≤ R₂.zkCoefficient logv₂)
    (h₂q : b₂q ≤ R₂.zkCoefficient logv₂) :
    gradedCombinedBudget R₁ R₂ logv₁ logv₂ cardC N
      (B₁ * B₂ * kmac : ℚ) b₁c b₁q b₂c b₂q ≤
      (B₁ * B₂ : ℚ) / cardFmac +
        (R₁.cardCand : ℚ) * zkFieldDensity R₁ logv₁ + b₁c + b₁q +
        (R₂.cardCand : ℚ) * zkFieldDensity R₂ logv₂ + b₂c + b₂q +
        N * max (max (R₁.zkCoefficient logv₁)
          (R₂.zkCoefficient logv₂))
          ((B₁ * B₂ : ℚ) / cardFmac) := by
  simpa only [gradedCombinedBudget] using
    twoFieldPotentialCombinedBudget_le_density R₁ R₂ logv₁ logv₂
      cardC cardFmac B₁ B₂ kmac N hC hFmac hF₁ hF₂ hmac
      b₁c b₁q b₂c b₂q hb₁c hb₁q hb₂c hb₂q h₁c h₁q h₂c h₂q

/-- Role-based graded budget at an integer slot of the merged schedule. -/
noncomputable def twoFieldPotentialSlotBudgetAt
    (keyBudget βchallenge₁ βquery₁ βchallenge₂ βquery₂ : ℚ)
    (k : ℕ) : ℚ :=
  if k = 0 then keyBudget
  else if k < 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds then
    sideUniformRoleBudget (R := R₁) (logv := logv₁) (C := C)
      βchallenge₁ βquery₁ (roleAt (k - 1))
  else
    sideUniformRoleBudget (R := R₂) (logv := logv₂) (C := C)
      βchallenge₂ βquery₂
      (roleAt (k - 1 - Rounds.Role.length R₁.params.nl R₁.params.rounds))

omit [DecidableEq C] in
/-- The role-based slot budget agrees with the budget of the deployed hash
input, independently of the prover's message prefixes. -/
theorem twoFieldPotentialSlotBudgetAt_hash2
    {Out : Type} (rootOf₁ rootOf₂ : Out → D)
    (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (keyBudget βchallenge₁ βquery₁ βchallenge₂ βquery₂ : ℚ)
    (out : Out)
    (i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
      Rounds.Role.length R₂.params.nl R₂.params.rounds)) :
    twoFieldPotentialBudget keyBudget
      (sideUniformPotentialBudget (R := R₁) (logv := logv₁)
        (C := C) βchallenge₁ βquery₁)
      (sideUniformPotentialBudget (R := R₂) (logv := logv₂)
        (C := C) βchallenge₂ βquery₂)
      (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) =
    twoFieldPotentialSlotBudgetAt (R₁ := R₁) (R₂ := R₂)
      (logv₁ := logv₁) (logv₂ := logv₂) (C := C)
      keyBudget βchallenge₁ βquery₁ βchallenge₂ βquery₂ i.val := by
  unfold hash2 twoFieldPotentialSlotBudgetAt
  split_ifs <;>
    simp only [twoFieldPotentialBudget, sideUniformPotentialBudget_eq_role,
      msgPoint]

omit [DecidableEq C] [Inhabited Msg₁] [Inhabited Msg₂] in
/-- Exact sum of the key, field, challenge, and query budgets over the
merged hash schedule. -/
theorem twoFieldPotentialSlotBudgetAt_sum
    (keyBudget βchallenge₁ βquery₁ βchallenge₂ βquery₂ : ℚ) :
    ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
      Rounds.Role.length R₂.params.nl R₂.params.rounds),
      twoFieldPotentialSlotBudgetAt (R₁ := R₁) (R₂ := R₂)
        (logv₁ := logv₁) (logv₂ := logv₂) (C := C)
        keyBudget βchallenge₁ βquery₁ βchallenge₂ βquery₂ i.val =
    twoFieldPotentialTotalBudget R₁ R₂ logv₁ logv₂
      (Fintype.card C) keyBudget βchallenge₁ βquery₁
        βchallenge₂ βquery₂ := by
  let L₁ := Rounds.Role.length R₁.params.nl R₁.params.rounds
  let L₂ := Rounds.Role.length R₂.params.nl R₂.params.rounds
  let g := twoFieldPotentialSlotBudgetAt (R₁ := R₁) (R₂ := R₂)
    (logv₁ := logv₁) (logv₂ := logv₂) (C := C)
    keyBudget βchallenge₁ βquery₁ βchallenge₂ βquery₂
  change (∑ i : Fin (1 + L₁ + L₂), g i.val) = _
  rw [Fin.sum_univ_eq_sum_range g, Finset.sum_range_add,
    Finset.sum_range_add, Finset.sum_range_one]
  have e0 : g 0 = keyBudget := by
    simp [g, twoFieldPotentialSlotBudgetAt]
  have e1 : ∑ x ∈ range L₁, g (1 + x) =
      ∑ x ∈ range L₁,
        sideUniformRoleBudget (R := R₁) (logv := logv₁) (C := C)
          βchallenge₁ βquery₁ (roleAt x) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_range.mp hx
    simp only [g, twoFieldPotentialSlotBudgetAt]
    rw [if_neg (by omega), if_pos (by omega),
      show 1 + x - 1 = x by omega]
  have e2 : ∑ x ∈ range L₂, g (1 + L₁ + x) =
      ∑ x ∈ range L₂,
        sideUniformRoleBudget (R := R₂) (logv := logv₂) (C := C)
          βchallenge₂ βquery₂ (roleAt x) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [g, twoFieldPotentialSlotBudgetAt]
    rw [if_neg (by omega), if_neg (by omega),
      show 1 + L₁ + x - 1 - L₁ = x by omega]
  rw [e0, e1, e2,
    Lfzk.NizkAdaptiveTwoField.sum_roleAt_rat,
    Lfzk.NizkAdaptiveTwoField.sum_roleAt_rat,
    sideUniformRoleBudget_sum, sideUniformRoleBudget_sum]
  rfl

omit [DecidableEq C] [Inhabited Msg₁] [Inhabited Msg₂] in
/-- A single worst-slot count for the two-field potential compiler. -/
theorem twoFieldPotentialBudget_le_max
    (keyBudget βchallenge₁ βquery₁ βchallenge₂ βquery₂ : ℚ)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds) :
    twoFieldPotentialBudget keyBudget
      (sideUniformPotentialBudget (R := R₁) (logv := logv₁)
        (C := C) βchallenge₁ βquery₁)
      (sideUniformPotentialBudget (R := R₂) (logv := logv₂)
        (C := C) βchallenge₂ βquery₂) p ≤
    twoFieldPotentialMaxBudget R₁ R₂ logv₁ logv₂
      (Fintype.card C) keyBudget βchallenge₁ βquery₁
        βchallenge₂ βquery₂ := by
  rcases p with p | p | p
  · exact le_max_left _ _
  · rw [twoFieldPotentialBudget, sideUniformPotentialBudget_eq_role]
    exact (sideUniformRoleBudget_le_max
      (R := R₁) (logv := logv₁) (C := C)
      βchallenge₁ βquery₁ p.role).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · rw [twoFieldPotentialBudget, sideUniformPotentialBudget_eq_role]
    exact (sideUniformRoleBudget_le_max
      (R := R₂) (logv := logv₂) (C := C)
      βchallenge₂ βquery₂ p.role).trans
      ((le_max_right _ _).trans (le_max_right _ _))

omit [DecidableEq C] in
/-- The merged local answer count follows from the key collision count and
the two side potential counts.  The side budgets are uniform in the cut
trace and public context, as required by the adaptive oracle compiler. -/
theorem twoFieldPotentialCharge_local
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
    (keyBudget : ℚ)
    (hkey : ∀ κ : PKey D Enc,
      (∑ c : C, if keyBad κ c then (1 : ℚ) else 0) ≤ keyBudget)
    (budget₁ : MPoint (SideCtx D C X) Msg₁ R₁.params.nl R₁.params.rounds → ℚ)
    (hbudget₁ : ∀ p, 0 ≤ budget₁ p)
    (hlocal₁ : ∀ (σ : PSig D C X Enc)
      (p : MPoint (SideCtx D C X) Msg₁ R₁.params.nl R₁.params.rounds)
      (pref : Fin p.role.slot → C),
      (∑ c : C, sidePointCharge (H := S₁.H σ) (Sat := S₁.Sat σ)
        (S₁.LD σ) (P₁ σ) p pref c) ≤ budget₁ p)
    (budget₂ : MPoint (SideCtx D C X ×
      (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → Msg₁))
      Msg₂ R₂.params.nl R₂.params.rounds → ℚ)
    (hbudget₂ : ∀ p, 0 ≤ budget₂ p)
    (hlocal₂ : ∀ (σ : PSig D C X Enc)
      (p : MPoint (SideCtx D C X ×
        (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → Msg₁))
        Msg₂ R₂.params.nl R₂.params.rounds)
      (pref : Fin p.role.slot → C),
      (∑ c : C, sidePointCharge (H := S₂.H σ) (Sat := S₂.Sat σ)
        (S₂.LD σ) (P₂ σ) p pref c) ≤ budget₂ p)
    (κ : PKey D Enc)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds)
    (pref : Fin (pts2.slot p) → C) :
    (∑ c : C, twoFieldPotentialCharge S₁ S₂ P₁ P₂
      keyBad dflt κ p pref c) ≤
      twoFieldPotentialBudget keyBudget budget₁ budget₂ p := by
  rcases p with p | p | p
  · simpa only [twoFieldPotentialCharge, twoFieldPotentialBudget] using hkey κ
  · let σ : PSig D C X Enc := (κ, p.ctx.2.1, p.ctx.2.2)
    by_cases hf : ZkFails S₁.Sat σ
    · change (∑ c : C, if ZkFails S₁.Sat σ then
          sidePointCharge (H := S₁.H σ) (Sat := S₁.Sat σ)
            (S₁.LD σ) (P₁ σ) p
            (fun j => pget dflt pref (1 + j.val)) c else 0) ≤ budget₁ p
      simp only [if_pos hf]
      exact hlocal₁ σ p (fun j => pget dflt pref (1 + j.val))
    · change (∑ c : C, if ZkFails S₁.Sat σ then
          sidePointCharge (H := S₁.H σ) (Sat := S₁.Sat σ)
            (S₁.LD σ) (P₁ σ) p
            (fun j => pget dflt pref (1 + j.val)) c else 0) ≤ budget₁ p
      simp only [if_neg hf, Finset.sum_const_zero]
      exact hbudget₁ p
  · let σ : PSig D C X Enc := (κ, p.ctx.1.2.1, p.ctx.1.2.2)
    by_cases hf : ZkFails S₂.Sat σ
    · change (∑ c : C, if ZkFails S₂.Sat σ then
          sidePointCharge (H := S₂.H σ) (Sat := S₂.Sat σ)
            (S₂.LD σ) (P₂ σ) p
            (fun j => pget dflt pref
              (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + j.val)) c else 0) ≤
          budget₂ p
      simp only [if_pos hf]
      exact hlocal₂ σ p (fun j => pget dflt pref
        (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + j.val))
    · change (∑ c : C, if ZkFails S₂.Sat σ then
          sidePointCharge (H := S₂.H σ) (Sat := S₂.Sat σ)
            (S₂.LD σ) (P₂ σ) p
            (fun j => pget dflt pref
              (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + j.val)) c else 0) ≤
          budget₂ p
      simp only [if_neg hf, Finset.sum_const_zero]
      exact hbudget₂ p

omit [DecidableEq C] in
/-- The field data and terminal potential of each `ZkSide` discharge the
merged charge's local obligations.  The four rational terminal bounds are
uniform in the cut trace; field roles keep their exact role-specific budgets. -/
theorem twoFieldPotentialCharge_local_of_sides
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
    (keyBudget : ℚ)
    (hkey : ∀ κ : PKey D Enc,
      (∑ c : C, if keyBad κ c then (1 : ℚ) else 0) ≤ keyBudget)
    (βchallenge₁ βquery₁ βchallenge₂ βquery₂ : ℚ)
    (hc₁ : 0 ≤ βchallenge₁) (hq₁ : 0 ≤ βquery₁)
    (hc₂ : 0 ≤ βchallenge₂) (hq₂ : 0 ≤ βquery₂)
    (hP₁c : ∀ σ, (P₁ σ).challengeBudget ≤ βchallenge₁)
    (hP₁q : ∀ σ, (P₁ σ).queryBudget ≤ βquery₁)
    (hP₂c : ∀ σ, (P₂ σ).challengeBudget ≤ βchallenge₂)
    (hP₂q : ∀ σ, (P₂ σ).queryBudget ≤ βquery₂)
    (κ : PKey D Enc)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds)
    (pref : Fin (pts2.slot p) → C) :
    (∑ c : C, twoFieldPotentialCharge S₁ S₂ P₁ P₂
      keyBad dflt κ p pref c) ≤
      twoFieldPotentialBudget keyBudget
        (sideUniformPotentialBudget (R := R₁) (logv := logv₁)
          (C := C) βchallenge₁ βquery₁)
        (sideUniformPotentialBudget (R := R₂) (logv := logv₂)
          (C := C) βchallenge₂ βquery₂) p := by
  apply twoFieldPotentialCharge_local S₁ S₂ P₁ P₂ keyBad dflt
    keyBudget hkey
    (sideUniformPotentialBudget (R := R₁) (logv := logv₁)
      (C := C) βchallenge₁ βquery₁)
    (sideUniformPotentialBudget_nonneg (R := R₁) (logv := logv₁)
      (C := C) βchallenge₁ βquery₁ hc₁ hq₁)
    (fun σ p pref =>
      sidePointCharge_uniform_local S₁ hF₁ P₁ βchallenge₁ βquery₁
        hP₁c hP₁q σ p pref)
    (sideUniformPotentialBudget (R := R₂) (logv := logv₂)
      (C := C) βchallenge₂ βquery₂)
    (sideUniformPotentialBudget_nonneg (R := R₂) (logv := logv₂)
      (C := C) βchallenge₂ βquery₂ hc₂ hq₂)
    (fun σ p pref =>
      sidePointCharge_uniform_local S₂ hF₂ P₂ βchallenge₂ βquery₂
        hP₂c hP₂q σ p pref) κ p pref

omit [DecidableEq C] in
/-- At a side-1 verifier point, the merged charge is exactly the side's
graded charge on its own ancestor answers. -/
theorem twoFieldPotentialCharge_side1_at
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
    (κ : PKey D Enc)
    (p : MPoint (SideCtx D C X) Msg₁ R₁.params.nl R₁.params.rounds)
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hfail : ZkFails S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2)) :
    twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt κ
      (Sum.inr (Sum.inl p)) (pts2.chal ro (Sum.inr (Sum.inl p)))
      (ro (Sum.inr (Sum.inl p))) =
      sidePointCharge (H := S₁.H (κ, p.ctx.2.1, p.ctx.2.2))
        (Sat := S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2))
        (S₁.LD (κ, p.ctx.2.1, p.ctx.2.2))
        (P₁ (κ, p.ctx.2.1, p.ctx.2.2)) p
        (mpoints.chal (fun q => ro (Sum.inr (Sum.inl q))) p)
        (ro (Sum.inr (Sum.inl p))) := by
  simp only [twoFieldPotentialCharge, if_pos hfail]
  exact congrArg (fun pref : Fin p.role.slot → C =>
    sidePointCharge (H := S₁.H (κ, p.ctx.2.1, p.ctx.2.2))
      (Sat := S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2))
      (S₁.LD (κ, p.ctx.2.1, p.ctx.2.2))
      (P₁ (κ, p.ctx.2.1, p.ctx.2.2)) p pref
      (ro (Sum.inr (Sum.inl p)))) (pget_side1_prefix dflt ro p)

omit [DecidableEq C] in
/-- The corresponding exact identity for side 2. -/
theorem twoFieldPotentialCharge_side2_at
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
    (κ : PKey D Enc)
    (p : MPoint (SideCtx D C X ×
      (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → Msg₁))
      Msg₂ R₂.params.nl R₂.params.rounds)
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hfail : ZkFails S₂.Sat (κ, p.ctx.1.2.1, p.ctx.1.2.2)) :
    twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt κ
      (Sum.inr (Sum.inr p)) (pts2.chal ro (Sum.inr (Sum.inr p)))
      (ro (Sum.inr (Sum.inr p))) =
      sidePointCharge (H := S₂.H (κ, p.ctx.1.2.1, p.ctx.1.2.2))
        (Sat := S₂.Sat (κ, p.ctx.1.2.1, p.ctx.1.2.2))
        (S₂.LD (κ, p.ctx.1.2.1, p.ctx.1.2.2))
        (P₂ (κ, p.ctx.1.2.1, p.ctx.1.2.2)) p
        (mpoints.chal (fun q => ro (Sum.inr (Sum.inr q))) p)
        (ro (Sum.inr (Sum.inr p))) := by
  simp only [twoFieldPotentialCharge, if_pos hfail]
  exact congrArg (fun pref : Fin p.role.slot → C =>
    sidePointCharge (H := S₂.H (κ, p.ctx.1.2.1, p.ctx.1.2.2))
      (Sat := S₂.Sat (κ, p.ctx.1.2.1, p.ctx.1.2.2))
      (S₂.LD (κ, p.ctx.1.2.1, p.ctx.1.2.2))
      (P₂ (κ, p.ctx.1.2.1, p.ctx.1.2.2)) p pref
      (ro (Sum.inr (Sum.inr p)))) (pget_side2_prefix dflt ro p)

omit [DecidableEq C] in
/-- The merged verifier path pays whenever either side's extraction path
pays, or the two fixed candidate sets collide at the key answer.  This is
the exact three-way composition before adaptive-oracle counting. -/
theorem twoFieldPotentialCharge_verifier_path
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
    {Out : Type} (rootOf₁ rootOf₂ : Out → D)
    (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out) (cut : List (Enc × D))
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hkey : ¬ ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      ¬ ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      keyBad ((rootOf₁ out, rootOf₂ out), cut)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))))
    (hside₁ : ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      1 ≤ ∑ i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds),
        sideTraceCharge
          (H := S₁.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (Sat := S₁.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (P₁ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out
          (fun p => ro (Sum.inr (Sum.inl p))) i)
    (hside₂ : ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      1 ≤ ∑ i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds),
        sideTraceCharge
          (H := S₂.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (Sat := S₂.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (P₂ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
            fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
              msgOf₁ out i.val) msgOf₂ out
          (fun p => ro (Sum.inr (Sum.inr p))) i) :
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt
        ((rootOf₁ out, rootOf₂ out), cut)
        (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)
        (pts2.chal ro
          (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)) := by
  let κ : PKey D Enc := ((rootOf₁ out, rootOf₂ out), cut)
  let σ : PSig D C X Enc := (κ, avOf out, pubOf out)
  let f : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → ℚ :=
    fun p => twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt κ p
      (pts2.chal ro p) (ro p)
  rw [show (∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
      Rounds.Role.length R₂.params.nl R₂.params.rounds),
        twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt κ
          (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)
          (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val))
          (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val))) =
      ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
        f (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) from rfl]
  rw [sum_hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out f]
  have hk : 0 ≤ f (Sum.inl (rootOf₁ out, rootOf₂ out)) :=
    twoFieldPotentialCharge_nonneg S₁ S₂ P₁ P₂ keyBad dflt κ _ _ _
  have hs₁ : 0 ≤ ∑ i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds),
      f (Sum.inr (Sum.inl (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val))) :=
    Finset.sum_nonneg fun i _ =>
      twoFieldPotentialCharge_nonneg S₁ S₂ P₁ P₂ keyBad dflt κ _ _ _
  have hs₂ : 0 ≤ ∑ i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds),
      f (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
            msgOf₁ out j.val) msgOf₂ out i.val))) :=
    Finset.sum_nonneg fun i _ =>
      twoFieldPotentialCharge_nonneg S₁ S₂ P₁ P₂ keyBad dflt κ _ _ _
  by_cases hf₁ : ZkFails S₁.Sat σ
  · have hp := hside₁ hf₁
    have heq : (∑ i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds),
        f (Sum.inr (Sum.inl (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))) =
        ∑ i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds),
          sideTraceCharge (H := S₁.H σ) (Sat := S₁.Sat σ)
            (S₁.LD σ) (P₁ σ)
            (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out
            (fun p => ro (Sum.inr (Sum.inl p))) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact twoFieldPotentialCharge_side1_at S₁ S₂ P₁ P₂ keyBad dflt κ _ ro hf₁
    rw [heq] at hs₁ ⊢
    linarith
  by_cases hf₂ : ZkFails S₂.Sat σ
  · have hp := hside₂ hf₂
    have heq : (∑ i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds),
        f (Sum.inr (Sum.inr (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
            fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
              msgOf₁ out j.val) msgOf₂ out i.val)))) =
        ∑ i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          sideTraceCharge (H := S₂.H σ) (Sat := S₂.Sat σ)
            (S₂.LD σ) (P₂ σ)
            (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
              fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
                msgOf₁ out j.val) msgOf₂ out
            (fun p => ro (Sum.inr (Sum.inr p))) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact twoFieldPotentialCharge_side2_at S₁ S₂ P₁ P₂ keyBad dflt κ _ ro hf₂
    rw [heq] at hs₂ ⊢
    linarith
  have hkb := hkey hf₁ hf₂
  have hkp : f (Sum.inl (rootOf₁ out, rootOf₂ out)) = 1 := by
    simp [f, twoFieldPotentialCharge, κ, hkb]
  rw [hkp]
  linarith

omit [DecidableEq C] in
/-- The three-way verifier path theorem with each side's accepted
LayerStep transcript as the premise.  Thus the side payments follow from
extraction failure, rather than being additional protocol assumptions. -/
theorem twoFieldPotentialCharge_accepted_path
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
    {Out : Type} (rootOf₁ rootOf₂ : Out → D)
    (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out) (cut : List (Enc × D))
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hkey : ¬ ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      ¬ ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      keyBad ((rootOf₁ out, rootOf₂ out), cut)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))))
    (hacc₁ : ZkLayerStepAccepts .accepted .start
      (steps (nl := R₁.params.nl) (w := R₁.params.rounds)
        (S₁.V (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₁ out))
      (fun i => ro (Sum.inr (Sum.inl
        (msgPoint (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))))
    (hacc₂ : ZkLayerStepAccepts .accepted .start
      (steps (nl := R₂.params.nl) (w := R₂.params.rounds)
        (S₂.V (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₂ out))
      (fun i => ro (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
            msgOf₁ out j.val) msgOf₂ out i.val))))) :
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt
        ((rootOf₁ out, rootOf₂ out), cut)
        (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)
        (pts2.chal ro
          (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)) := by
  apply twoFieldPotentialCharge_verifier_path S₁ S₂ P₁ P₂ keyBad dflt
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out cut ro hkey
  · intro hf
    exact accepted_noSat_sideTrace_pays
      (H := S₁.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (Sat := S₁.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (P₁ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out
      (fun p => ro (Sum.inr (Sum.inl p))) hf hacc₁
  · intro hf
    exact accepted_noSat_sideTrace_pays
      (H := S₂.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (Sat := S₂.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (P₂ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
        fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
          msgOf₁ out i.val) msgOf₂ out
      (fun p => ro (Sum.inr (Sum.inr p))) hf hacc₂
end Lfzk.NizkZkDeployedHash
