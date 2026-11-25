import LfzkV1.CompiledLongfellowZkV7Joint
import LfzkV1.V7ColumnUniqueness
import LfzkV1.MerkleWork125V7
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The four registered v7 Ligero geometries

The numerical endpoint uses the exact degree cuts, including for the two
response masks. Its support conditions apply only to core padding. The
three dedicated masks remain independent full-field draws.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LfzkV1.V7ZkProfile

open Merkle.MH LigeroFamily LigeroFamily.ReedSolomon
open LfzkV1.MacSep LfzkV1.CompiledLongfellowZk LfzkV1.CompiledLongfellowZkTwoField
  LfzkV1.CompiledLongfellowZkV7Joint LfzkV1.ZkAdaptiveV1 LfzkV1.ZkGhostSubfield
  LfzkV1.ZkGhostTwoField LfzkV1.ZkGhostSampled LfzkV1.ZkGhostSimulator
  LfzkV1.MerkleWork125 LfzkV1.CertifiedV1 LfzkV1.LigeroV1Rows

/-- The exact deployed Reed–Solomon code at this side's evaluation points. -/
structure CodeInstance {F : Type} [Field F] {r w n : ℕ} (C : MultiplicativeCode F r w n) where
  domain : Domain F r w n
  width_le : r + w ≤ n
  width_ge : 3 ≤ r + w
  exactCode : C = V7ColumnUniqueness.deployedCode domain width_le (by omega)

abbrev CorePadding (F : Type) (r nw nq : ℕ) :=
  (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F

abbrev SupportedTape {F : Type} [Field F] {r w n nw nq : ℕ}
    (C : MultiplicativeCode F r w n) (keep : CorePadding F r nw nq → Prop) :=
  {ρ : Tape C nw nq 1 // keep ρ.corePadding}

/-- Private input prefix of the frozen hash circuit, in attribute-count order.
The v1 prover subtracts the public-input count before appending sumcheck pads. -/
def hashPrivateSubfieldBoundary (attr : Fin 4) : ℕ := ![84160, 88280, 92400, 96520] attr

/-- Only complete witness rows within the private prefix use the small field.
Quadratic-copy rows and all three dedicated masks use the ambient field. -/
def hashSubfieldRow (attr : Fin 4) (w : ℕ) {nw nq : ℕ}
    (block : CoreBlock) (j : Fin (block.rowCount nw nq)) : Prop :=
  block = .linear ∧ (j.val + 1) * w ≤ hashPrivateSubfieldBoundary attr

theorem deployed_hash_subfield_rows (attr : Fin 4) :
    hashPrivateSubfieldBoundary attr / ((v7HashProfile attr).params.row.k - 132) =
      (![255, 258, 267, 269] : Fin 4 → ℕ) attr := by
  fin_cases attr <;> decide +kernel

def hashPadding {K F : Type} [Field K] [Field F] (emb : K →+* F)
    (attr : Fin 4) (w : ℕ) {r nw nq : ℕ} (pad : CorePadding F r nw nq) : Prop :=
  ∀ block j, hashSubfieldRow attr w block j → ∀ i, pad block j i ∈ Set.range emb

private theorem duplicate_on_supported_tape {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {r w n nw nq : ℕ} {C : MultiplicativeCode F r w n} (code : CodeInstance C)
    (messages : CoreMessages F nw nq w) (keep : CorePadding F r nw nq → Prop)
    [Fintype (SupportedTape C keep)] :
    probOf id (fun ρ : {ρ : Tape C nw nq 1 // keep ρ.corePadding} =>
      ¬ Function.Injective (v1Oracle messages ρ.val).column) ≤
      (n.choose 2 : ℚ) / (Fintype.card F : ℚ)^3 := by
  rcases code with ⟨domain, hw, hlarge, he⟩
  subst C
  letI : Fintype (Subtype keep) := Fintype.ofFinite _
  exact V7ColumnUniqueness.duplicate_columns_tape_restricted domain hw hlarge messages keep

/-- The distinction between the two query-budget endpoints is exact. -/
theorem v7_bound_lt_128 {Q : ℕ} (hQ : Q < 2 ^ 128) :
    (Q : ℚ) / 2 ^ 256 + 1 / 2 ^ 360 < 1 / 2 ^ 128 := by
  have h : (Q : ℚ) ≤ ((2 : ℕ) ^ 128 - 1 : ℕ) := by exact_mod_cast Nat.le_pred_of_lt hQ
  calc
    _ ≤ ((2 : ℕ) ^ 128 - 1 : ℕ) / (2 : ℚ) ^ 256 + 1 / 2 ^ 360 := by gcongr
    _ < _ := by decide +kernel

theorem v7_bound_at_128 :
    (((2 : ℕ) ^ 128 : ℕ) : ℚ) / 2 ^ 256 + 1 / 2 ^ 360 = 1 / 2 ^ 128 + 1 / 2 ^ 360 := by
  decide +kernel

section Profiles


/-- The four registered hash profiles have the required degree room. -/
theorem hash_degree_room (i : Fin 4) :
    3 ≤ (v7HashProfile i).params.row.k ∧ (v7HashProfile i).params.row.k ≤ (v7HashProfile i).params.row.n := by
  fin_cases i <;> decide +kernel

theorem signature_degree_room :
    3 ≤ v7Sig.params.row.k ∧ v7Sig.params.row.k ≤ v7Sig.params.row.n := by
  decide +kernel

/-- Exact union-bound numerators, in order of attribute count. -/
theorem hash_pair_counts (i : Fin 4) :
    (v7HashProfile i).params.row.n.choose 2 = (![5214835, 5502903, 5616276, 5901330] : Fin 4 → ℕ) i := by
  rw [Nat.choose_two_right]
  fin_cases i <;> decide +kernel

theorem sig_pair_count : v7Sig.params.row.n.choose 2 = 5076891 := by
  rw [Nat.choose_two_right]
  decide +kernel

theorem hash_duplicate_budget (i : Fin 4) :
    ((v7HashProfile i).params.row.n.choose 2 : ℚ) / 2^384 < 1 / 2^361 := by
  rw [hash_pair_counts]
  fin_cases i <;> decide +kernel

theorem signature_duplicate_budget :
    (v7Sig.params.row.n.choose 2 : ℚ) / (p256Order : ℚ)^3 < 1 / 2^745 := by
  rw [sig_pair_count]
  decide +kernel

end Profiles

section Main

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ r₂ w₂ n₂ nw₂ nq₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ : Type}
variable [Fintype Salt] [Nonempty Salt] [Fintype D] [DecidableEq D] [Inhabited D]
  [DecidableEq Enc₁] [DecidableEq Enc₂] [Fintype Enc₁] [Fintype Enc₂] [DecidableEq LQ₁] [DecidableEq LQ₂]
  [Fintype LQ₁] [Fintype LQ₂] [Fintype Coin₁] [Fintype Coin₂]
  [Nonempty Coin₁] [Nonempty Coin₂] [Fintype RO₁] [Fintype RO₂]
  [Fintype B₁] [Fintype B₂] [Fintype Tr₁] [Fintype Tr₂]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk Q : ℕ} {V : Type}

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ 1 E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ 1 E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ 1 Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ 1 F₂ r₂ w₂ n₂ nw₂ nq₂ 1
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V Q)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
section Profiles

open LfzkV1.V7ColumnUniqueness LfzkV1.CertifiedV1
  LfzkV1.LigeroV1Rows

/-- The total duplicate-payload budget, using one profile index for all four
registered hash geometries. The signature geometry is common to all four. -/
theorem profile_duplicate_lt (attr : Fin 4)
    (hashN : n₁ = (v7HashProfile attr).params.row.n) (sigN : n₂ = v7Sig.params.row.n)
    (hashField : Fintype.card F₁ = 2 ^ 128) (sigField : Fintype.card F₂ = p256Order) :
    (n₁.choose 2 : ℚ) / (Fintype.card F₁ : ℚ)^3 +
      (n₂.choose 2 : ℚ) / (Fintype.card F₂ : ℚ)^3 < 1 / 2^360 := by
  rw [hashN, sigN, hashField, sigField, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  have h := add_lt_add (hash_duplicate_budget attr) signature_duplicate_budget
  exact h.trans (by decide +kernel)

variable {R₁ R₂ : Type} [Fintype R₁] [Fintype R₂] [Nonempty R₁] [Nonempty R₂]
variable (draw₁ : R₁ → Tape P₁.C nw₁ nq₁ 1) (draw₂ : R₂ → Tape P₂.C nw₂ nq₂ 1)

private def drawBoth (x : Tag Fmac nblk × (B₁ × R₁) × (B₂ × R₂)) :
    HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk) :=
  (x.1, (x.2.1.1, draw₁ x.2.1.2), (x.2.2.1, draw₂ x.2.2.2))

open LfzkV1.ZkAdaptiveV1 LigeroFamily.ZeroKnowledge

private theorem profile_duplicate_probability (attr : Fin 4)
    (hashN : n₁ = (v7HashProfile attr).params.row.n) (sigN : n₂ = v7Sig.params.row.n)
    (hashField : Fintype.card F₁ = 2 ^ 128) (sigField : Fintype.card F₂ = p256Order)
    (h₁ : ∀ a b, probOf id (fun ρ : R₁ =>
      ¬ Function.Injective (v1Oracle (P₁.FE.msgs (wit₁ a) b) (draw₁ ρ)).column)
        ≤ (n₁.choose 2 : ℚ) / (Fintype.card F₁ : ℚ)^3)
    (h₂ : ∀ a b, probOf id (fun ρ : R₂ =>
      ¬ Function.Injective (v1Oracle (P₂.FE.msgs (wit₂ a) b) (draw₂ ρ)).column)
        ≤ (n₂.choose 2 : ℚ) / (Fintype.card F₂ : ℚ)^3) :
    probOf (drawBoth P₁ P₂ draw₁ draw₂) (fun x => ¬ separateColumns P₁ P₂ wit₁ wit₂ x) < 1 / 2^360 := by
  classical
  have hu := probOf_two_side_bad_le _ _ (by positivity) (by positivity) h₁ h₂
  refine lt_of_le_of_lt ?_ (profile_duplicate_lt (F₁ := F₁) (F₂ := F₂) attr hashN sigN hashField sigField)
  refine le_trans ?_ hu
  unfold probOf
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hh : ¬ (Function.Injective (v1Oracle (P₁.FE.msgs (wit₁ x.1) x.2.1.1) (draw₁ x.2.1.2)).column ∧
        Function.Injective (v1Oracle (P₂.FE.msgs (wit₂ x.1) x.2.2.1) (draw₂ x.2.2.2)).column) := hx
    exact not_and_or.mp hh)

end Profiles

variable (keep₁ : CorePadding F₁ r₁ nw₁ nq₁ → Prop) (keep₂ : CorePadding F₂ r₂ nw₂ nq₂ → Prop)

local notation "R₁" => SupportedTape P₁.C keep₁
local notation "R₂" => SupportedTape P₂.C keep₂
local notation "Real" => Tag Fmac nblk × (B₁ × R₁) × (B₂ × R₂)
local notation "Sim" => Tag Fmac nblk × (Tr₁ × R₁) × (Tr₂ × R₂)
local notation "Outer" => OuterCoins n₁ n₂ Salt D Enc₁ Enc₂ Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂

/-- Code and field evidence for the profile indexed by its attribute count.
The proof only needs the number of columns for its numerical budget. -/
structure RegisteredGeometry (attr : Fin 4) where
  hashCode : CodeInstance P₁.C
  sigCode : CodeInstance P₂.C
  hashN : n₁ = (v7HashProfile attr).params.row.n
  sigN : n₂ = v7Sig.params.row.n
  hashK : r₁ + w₁ = (v7HashProfile attr).params.row.k
  sigK : r₂ + w₂ = v7Sig.params.row.k
  hashOpenings : r₁ = 132
  sigOpenings : r₂ = 132
  hashField : Fintype.card F₁ = 2 ^ 128
  sigField : Fintype.card F₂ = p256Order

/-- Supply the hash-side support premise using the registered interpolation
points and the v7 core witness prefix. The signature support is unrestricted. -/
theorem hash_padding_stable {K : Type} [Field K] (emb : K →+* F₁) (attr : Fin 4)
    (code : CodeInstance P₁.C)
    (points : ∀ i, code.domain.point i ∈ Set.range emb)
    (witness : ∀ ap b block j, hashSubfieldRow attr w₁ block j → ∀ k,
      P₁.FE.msgs (wit₁ ap) b block j k ∈ Set.range emb)
    (side : FixedSide n₁ Salt D Coin₁ LQ₁ RO₁) :
    Stable P₁ side wit₁ (fun ρ => hashPadding emb attr w₁ ρ.corePadding) := by
  have baseEq : P₁.C.base = evaluationSpace code.domain (r₁ + w₁) := by
    exact congrArg MultiplicativeCode.base code.exactCode
  exact stable_of_points_supported P₁ side wit₁ emb (hashSubfieldRow attr w₁) code.domain points baseEq witness

/-- One v7 result for each of the four registered profiles. It takes
exactly one total Merkle-query budget, and preserves the v7 zero pattern. -/
theorem v7mac_twofield_zk {T₁ T₂ : ℕ}
    [Fintype R₁] [Fintype R₂] [Nonempty R₁] [Nonempty R₂]
    (attr : Fin 4) (profile : RegisteredGeometry P₁ P₂ attr)
    (saltCard : Fintype.card Salt = 2 ^ 256)
    (hT₁ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₁)
    (hT₂ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₂)
    (leaf₁ : Function.Injective P₁.Cod.leafEnc) (leaf₂ : Function.Injective P₂.Cod.leafEnc)
    (node₁ : ∀ children sm, P₁.Cod.nodeEnc children ≠ P₁.Cod.leafEnc sm)
    (node₂ : ∀ children sm, P₂.Cod.nodeEnc children ≠ P₂.Cod.leafEnc sm)
    (hp : ∀ side, Stable P₁ side wit₁ (fun ρ => keep₁ ρ.corePadding))
    (hq : ∀ side, Stable P₂ side wit₂ (fun ρ => keep₂ ρ.corePadding))
    (hvalid₁ : ∀ ap rt₁ rt₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ rt₁ rt₂ av (shiftTag av ap msg)))
    (hvalid₂ : ∀ ap rt₁ rt₂ av p₁, P₂.FE.Valid (wit₂ ap) (ctx₂ rt₁ rt₂ av (shiftTag av ap msg) p₁)) :
    StatClose ((Q : ℚ) / 2^256 + 1 / 2^360)
      (realSampledV7 P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂)
        (forgetSupport : Real → HonestTape P₁ P₂))
      (fun ω : Sim × Outer => ghostSimExpLeak P₁ P₂ ctx₁ ctx₂ dist (zeroPat msg) (forgetSupport ω.1, ω.2)) := by
  have hc := profile_duplicate_probability P₁ P₂ wit₁ wit₂
    (fun r : R₁ => r.val) (fun r : R₂ => r.val) attr profile.hashN profile.sigN profile.hashField profile.sigField
    (fun a b => duplicate_on_supported_tape profile.hashCode (P₁.FE.msgs (wit₁ a) b) keep₁)
    (fun a b => duplicate_on_supported_tape profile.sigCode (P₂.FE.msgs (wit₂ a) b) keep₂)
  apply (v7_zk_joint_restricted P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg
    (fun ρ => keep₁ ρ.corePadding) (fun ρ => keep₂ ρ.corePadding)
    hT₁ hT₂ leaf₁ leaf₂ node₁ node₂ hp hq hvalid₁ hvalid₂).mono
  rw [saltCard, Nat.cast_pow, Nat.cast_ofNat]
  exact add_le_add_right hc.le _

/-- If every common block is nonzero, the same bound uses the simulator
with no private zero-pattern input. -/
theorem v7mac_twofield_zk_nonzero {T₁ T₂ : ℕ}
    [Fintype R₁] [Fintype R₂] [Nonempty R₁] [Nonempty R₂]
    (attr : Fin 4) (profile : RegisteredGeometry P₁ P₂ attr)
    (saltCard : Fintype.card Salt = 2 ^ 256)
    (hT₁ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₁)
    (hT₂ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₂)
    (leaf₁ : Function.Injective P₁.Cod.leafEnc) (leaf₂ : Function.Injective P₂.Cod.leafEnc)
    (node₁ : ∀ children sm, P₁.Cod.nodeEnc children ≠ P₁.Cod.leafEnc sm)
    (node₂ : ∀ children sm, P₂.Cod.nodeEnc children ≠ P₂.Cod.leafEnc sm)
    (hp : ∀ side, Stable P₁ side wit₁ (fun ρ => keep₁ ρ.corePadding))
    (hq : ∀ side, Stable P₂ side wit₂ (fun ρ => keep₂ ρ.corePadding))
    (hvalid₁ : ∀ ap rt₁ rt₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ rt₁ rt₂ av (shiftTag av ap msg)))
    (hvalid₂ : ∀ ap rt₁ rt₂ av p₁, P₂.FE.Valid (wit₂ ap) (ctx₂ rt₁ rt₂ av (shiftTag av ap msg) p₁))
    (hmsg : ∀ j, msg j ≠ 0) :
    StatClose ((Q : ℚ) / 2^256 + 1 / 2^360)
      (realSampledV7 P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂)
        (forgetSupport : Real → HonestTape P₁ P₂))
      (fun ω : Sim × Outer => ghostSimExp P₁ P₂ ctx₁ ctx₂ dist (forgetSupport ω.1, ω.2)) := by
  rw [← ghostSimExpLeak_of_ne_zero P₁ P₂ ctx₁ ctx₂ dist msg hmsg]
  exact v7mac_twofield_zk P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg keep₁ keep₂ attr profile saltCard hT₁ hT₂
    leaf₁ leaf₂ node₁ node₂ hp hq hvalid₁ hvalid₂

section DeployedPadding

variable (emb : GaloisField 2 16 →+* F₁) (attr : Fin 4)

local notation "HashPadding" => (hashPadding emb attr w₁ (r := r₁) (nw := nw₁) (nq := nq₁))
local notation "SigPadding" => (fun _ : CorePadding F₂ r₂ nw₂ nq₂ => True)
local notation "HashTape" => SupportedTape P₁.C HashPadding
local notation "SigTape" => SupportedTape P₂.C SigPadding
local notation "RealV7" => Tag Fmac nblk × (B₁ × HashTape) × (B₂ × SigTape)
local notation "SimV7" => Tag Fmac nblk × (Tr₁ × HashTape) × (Tr₂ × SigTape)

/-- All four v7 profiles with the specific hash subfield prefix and full-field
signature padding. The supplied domain and witness rows identify the
mathematical frontend with this interpolation and layout contract. -/
theorem v7mac_twofield_zk_deployed_padding {T₁ T₂ : ℕ}
    [Fintype HashTape] [Fintype SigTape] [Nonempty HashTape] [Nonempty SigTape]
    (profile : RegisteredGeometry P₁ P₂ attr)
    (saltCard : Fintype.card Salt = 2 ^ 256)
    (hT₁ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₁)
    (hT₂ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₂)
    (leaf₁ : Function.Injective P₁.Cod.leafEnc) (leaf₂ : Function.Injective P₂.Cod.leafEnc)
    (node₁ : ∀ children sm, P₁.Cod.nodeEnc children ≠ P₁.Cod.leafEnc sm)
    (node₂ : ∀ children sm, P₂.Cod.nodeEnc children ≠ P₂.Cod.leafEnc sm)
    (points : ∀ i, profile.hashCode.domain.point i ∈ Set.range emb)
    (witness : ∀ ap b block j, hashSubfieldRow attr w₁ block j → ∀ k,
      P₁.FE.msgs (wit₁ ap) b block j k ∈ Set.range emb)
    (hvalid₁ : ∀ ap rt₁ rt₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ rt₁ rt₂ av (shiftTag av ap msg)))
    (hvalid₂ : ∀ ap rt₁ rt₂ av p₁, P₂.FE.Valid (wit₂ ap) (ctx₂ rt₁ rt₂ av (shiftTag av ap msg) p₁)) :
    StatClose ((Q : ℚ) / 2^256 + 1 / 2^360)
      (realSampledV7 P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂)
        (forgetSupport : RealV7 → HonestTape P₁ P₂))
      (fun ω : SimV7 × Outer =>
        ghostSimExpLeak P₁ P₂ ctx₁ ctx₂ dist (zeroPat msg) (forgetSupport ω.1, ω.2)) :=
  v7mac_twofield_zk P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg HashPadding SigPadding
    attr profile saltCard hT₁ hT₂ leaf₁ leaf₂ node₁ node₂
    (hash_padding_stable P₁ wit₁ emb attr profile.hashCode points witness)
    (fun side => stable_unrestricted P₂ side wit₂) hvalid₁ hvalid₂

end DeployedPadding

end Main

/-- The two salted leaves have different input lengths, and neither matches a
64-byte internal node, at all four profiles. -/
theorem deployed_leaf_lengths (attr : Fin 4) :
    let hash := MerkleWork125.leafInputBytes (MerkleWork125.v7HashTableauRows attr) 16
    let sig := MerkleWork125.leafInputBytes 19 32
    hash ≠ sig ∧ hash ≠ 64 ∧ sig ≠ 64 := by
  exact ⟨(MerkleWork125.v7Hash_leaf_input_disjoint attr).1,
    (MerkleWork125.v7Hash_leaf_input_disjoint attr).2, by decide +kernel⟩

end LfzkV1.V7ZkProfile
