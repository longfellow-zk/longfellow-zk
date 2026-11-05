import LfzkV2.Linear.Runtime.TwoFieldCommitmentFS
import LfzkV1.TSec

/-! The annotated authenticated extraction experiment for the native packed
sides. Raw replay below derives the MAC-answer annotation from the oracle. -/

namespace LfzkV2.Linear.Runtime.TwoFieldCommitmentFS

open Finset RecursivePolygero Merkle Merkle.MH Merkle.RandomOracle TwoFieldReplay
open LfzkV2.TwoFieldCommitmentFS (cutOracle check)
open scoped Classical

variable {F₁ F₂ Key C Public Out Enc D Salt₁ Salt₂ Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂]
variable [Fintype C] [Fintype Key] [Fintype Public] [Fintype D]
variable [DecidableEq Key] [DecidableEq D] [DecidableEq Enc] [Inhabited D]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {out₁ input₁ out₂ input₂ blocks tA N TM : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C S₁.Selected circuit₂ I₂)
variable [Inhabited Salt₁] [Inhabited Salt₂]
variable [Inhabited (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq)]
variable [Inhabited (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq)]
variable [Fintype S₁.Data] [Fintype S₂.Data]
variable [DecidableEq (Domain S₁ S₂)]
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)
variable (codec₁ : Codec Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D Enc)
variable (codec₂ : Codec Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D Enc)
variable (claimOf₁ : Out → OpeningClaim I₁.n Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D)
variable (claimOf₂ : Out → OpeningClaim I₂.n Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D)
variable (ht₁ : 0 < I₁.t) (ht₂ : 0 < I₂.t)
variable (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
variable (proofOf : Out → Proof S₁ S₂)
variable (dec₁ : RoleDecoders codec₁) (dec₂ : RoleDecoders codec₂) (rootOf₁ rootOf₂ : Key → D)

noncomputable def failureProbability : ℚ :=
  let K := setup S₁ S₂ body proofOf S₁.dflt
  let ck := check I₁ I₂ codec₁ codec₂ claimOf₁ claimOf₂
  let context := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) key =>
    (cutOracle I₁ K dec₁ rootOf₁ mt H key,cutOracle I₂ K dec₂ rootOf₂ mt H key)
  let acceptedAt := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) (result : Out) =>
    let proof := proofOf result
    (TwoFieldReplay.context S₁ S₂ proof).2.1 = H (.inl (TwoFieldReplay.context S₁ S₂ proof).1) ∧
    S₁.CompiledAccepts ht₁ (codec₁.withOracle (K.merkleOracle ck mt H))
      (fun x => H (.inr (.inl x))) (selectedOne S₁ S₂ proof)
      (rootOf₁ (TwoFieldReplay.context S₁ S₂ proof).1) (claimOf₁ result) ∧
    S₂.CompiledAccepts ht₂ (codec₂.withOracle (K.merkleOracle ck mt H))
      (fun x => H (.inr (.inr x))) proof
      (rootOf₂ (TwoFieldReplay.context S₁ S₂ proof).1) (claimOf₂ result)
  let badAt := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) (result : Out) =>
    let proof := proofOf result
    let W := context mt H (TwoFieldReplay.context S₁ S₂ proof).1
    TwoFieldPotential.extract S₁ S₂ M W proof = none
  let accepts := fun mt H => acceptedAt mt H (K.proof mt H)
  let fails := fun mt H => badAt mt H (K.proof mt H)
  ((univ.filter fun ω : (Fin TM → D) × (Domain S₁ S₂ → C) =>
      accepts ω.1 ω.2 ∧ fails ω.1 ω.2).card : ℚ) /
    ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂))

theorem failureProbability_le_one :
    failureProbability (TM := TM) S₁ S₂ M codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂
      body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤ 1 := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  unfold failureProbability
  exact LfzkV1.TSec.ratio_le_one _

/-- The named probability is the event in the checked annotated two-opening
reduction. Its MAC-row hypotheses concern the actual V2 affine MAC. -/
theorem failureProbability_le (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : Context Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : S₁.Selected) W g,
      S₂.Good ctx W g → M.macTwo g (M.decode (S₁.context ctx).2.1) = tag (S₁.context ctx).2.2)
    (hspace : 2*I₂.n+2*I₁.n+tA ≤ TM) :
    failureProbability (TM := TM) S₁ S₂ M codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂
      body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (N*TwoFieldFS.maxBudget S₁ S₂ M +
        ∑ i, TwoFieldFS.slotBudget S₁ S₂ M i)/Fintype.card C +
      2*(Bcs.AdaptiveCommit.adaptiveNumerator (2*I₂.n+2*I₁.n) tA
        (1+S₁.slots+S₂.slots+N) : ℚ)/Fintype.card D := by
  have h := extraction_le S₁ S₂ codec₁ codec₂ claimOf₁ claimOf₂ M
    ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ tag hrowOne hrowTwo hspace
  exact h

end LfzkV2.Linear.Runtime.TwoFieldCommitmentFS
