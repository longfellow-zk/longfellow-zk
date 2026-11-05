import LfzkV2.Packed.AuthenticatedProbability
import LfzkV2.Packed.TwoFieldKeyReplay
import Bcs.SmallMerkle

/-! Authenticated extraction after the verifier recomputes the MAC answer.
The event contains no supplied-key coherence condition. The generic bound
uses the native packed side interfaces and retains both Merkle errors. -/

namespace LfzkV2.Packed.RawExtraction

open Finset RecursivePolygero Merkle Merkle.MH Merkle.RandomOracle TwoFieldReplay
open scoped Classical

variable {F₁ F₂ Key C Public Out Enc D Salt₁ Salt₂ Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂]
variable [Fintype C] [DecidableEq Enc] [Inhabited D]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {out₁ input₁ out₂ input₂ blocks tA N TM : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C S₁.Selected circuit₂ I₂)
variable [Inhabited Salt₁] [Inhabited Salt₂]
variable [DecidableEq (Domain S₁ S₂)]
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)
variable (codec₁ : Codec Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D Enc)
variable (codec₂ : Codec Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D Enc)
variable (claimOf₁ : Out → OpeningClaim I₁.n Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D)
variable (claimOf₂ : Out → OpeningClaim I₂.n Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D)
variable (ht₁ : 0 < I₁.t) (ht₂ : 0 < I₂.t)
variable (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
variable (proofOf : Out → RawProof S₁ S₂)
variable (dec₁ : RoleDecoders codec₁) (dec₂ : RoleDecoders codec₂) (rootOf₁ rootOf₂ : Key → D)

/-- The replayed answer is coherent for every oracle pair, even if the
original prover never queried the key. -/
theorem key_coherent (mt : Fin TM → D)
    (H : Domain S₁ S₂ → C) :
    let K := TwoFieldCommitmentFS.setup S₁ S₂
      (prepareBody S₁ S₂ body proofOf)
      (preparedProof S₁ S₂ proofOf) S₁.dflt
    let proof := preparedProof S₁ S₂ proofOf (K.proof mt H)
    (TwoFieldReplay.context S₁ S₂ proof).2.1 = H (.inl (TwoFieldReplay.context S₁ S₂ proof).1) := by
  dsimp only
  rw [Bcs.TotalOracleCommit.Setup.proof_eq]
  simpa only [Bcs.TotalOracleCommit.Setup.search,TwoFieldCommitmentFS.setup,prepareBody_fixLeft] using
    preparedProof_coherent S₁ S₂
      (TwoOracleTree.fixLeft mt default body []) proofOf H

variable [Fintype Key] [Fintype Public] [Fintype D] [DecidableEq Key] [DecidableEq D]
variable [Inhabited (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq)]
variable [Inhabited (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq)]
variable [Fintype S₁.Data] [Fintype S₂.Data]

/-- Acceptance and paired-extraction failure after the verifier recomputes
the key. This event has no supplied-key coherence condition. -/
noncomputable def probability : ℚ :=
  let K := TwoFieldCommitmentFS.setup S₁ S₂
    (prepareBody S₁ S₂ body proofOf)
    (preparedProof S₁ S₂ proofOf) S₁.dflt
  let ck := LfzkV2.TwoFieldCommitmentFS.check I₁ I₂ codec₁ codec₂
    (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
  let fails := fun ω : (Fin TM → D) × (Domain S₁ S₂ → C) =>
    let result := K.proof ω.1 ω.2
    let proof := preparedProof S₁ S₂ proofOf result
    let W := (LfzkV2.TwoFieldCommitmentFS.cutOracle I₁ K dec₁ rootOf₁ ω.1 ω.2 (TwoFieldReplay.context S₁ S₂ proof).1,
      LfzkV2.TwoFieldCommitmentFS.cutOracle I₂ K dec₂ rootOf₂ ω.1 ω.2 (TwoFieldReplay.context S₁ S₂ proof).1)
    S₁.CompiledAccepts ht₁ (codec₁.withOracle (K.merkleOracle ck ω.1 ω.2))
      (fun x => ω.2 (.inr (.inl x))) (selectedOne S₁ S₂ proof)
      (rootOf₁ (TwoFieldReplay.context S₁ S₂ proof).1) (claimOf₁ result.1) ∧
    S₂.CompiledAccepts ht₂ (codec₂.withOracle (K.merkleOracle ck ω.1 ω.2))
      (fun x => ω.2 (.inr (.inr x))) proof
      (rootOf₂ (TwoFieldReplay.context S₁ S₂ proof).1) (claimOf₂ result.1) ∧
    TwoFieldPotential.extract S₁ S₂ M W proof = none
  ((univ.filter fails).card : ℚ) /
    ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂))

/-- Derived key coherence removes the extra conjunct in the annotated
experiment. Both experiments use the same authenticated execution. -/
theorem probability_eq_annotated :
    probability (TM := TM) S₁ S₂ M
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ =
    TwoFieldCommitmentFS.failureProbability (TM := TM) S₁ S₂ M codec₁ codec₂
      (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
      ht₁ ht₂ (prepareBody S₁ S₂ body proofOf)
      (preparedProof S₁ S₂ proofOf) dec₁ dec₂ rootOf₁ rootOf₂ := by
  unfold probability TwoFieldCommitmentFS.failureProbability
  apply congrArg (fun s : Finset ((Fin TM → D) ×
      (Domain S₁ S₂ → C)) =>
    (s.card : ℚ) / ((Fintype.card D : ℚ)^TM *
      (Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂)))
  ext ω
  have hc := key_coherent S₁ S₂ body proofOf ω.1 ω.2
  dsimp only at hc
  simp only [mem_filter,and_assoc]
  tauto

theorem probability_le_one :
    probability (TM := TM) S₁ S₂ M
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤ 1 := by
  rw [probability_eq_annotated]
  exact TwoFieldCommitmentFS.failureProbability_le_one S₁ S₂ M codec₁ codec₂
    (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
    ht₁ ht₂ (prepareBody S₁ S₂ body proofOf)
    (preparedProof S₁ S₂ proofOf) dec₁ dec₂ rootOf₁ rootOf₂

/-- With fewer than eight Merkle queries, authenticated acceptance already
requires a predictable digest hit. This bound is independent of the number
of transcript queries and does not assume distinct leaf encodings. -/
theorem probability_small_merkle (hn : 128 ≤ I₁.n) (hsmall : tA < 8)
    (hspace : 2*I₂.n+2*I₁.n+tA ≤ TM) :
    probability (TM := TM) S₁ S₂ M
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (2*tA*tA+(2*I₂.n+2*I₁.n+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ) := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  let K := TwoFieldCommitmentFS.setup S₁ S₂
    (prepareBody S₁ S₂ body proofOf)
    (preparedProof S₁ S₂ proofOf) S₁.dflt
  let ck := LfzkV2.TwoFieldCommitmentFS.check I₁ I₂ codec₁ codec₂
    (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
  have hTM : 1 ≤ TM := by omega
  have h := K.merkle_small_ratio_le codec₁ dec₁ ck rootOf₁
    (fun result : Out × C => claimOf₁ result.1)
    (LfzkV2.TwoFieldCommitmentFS.check_contains_one I₁ I₂ codec₁ codec₂
      (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1))
    hsmall hn (by omega) hspace hTM
  refine le_trans ?_ h
  unfold probability
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (Nat.cast_le (α := ℚ)).mpr
  apply card_le_card
  intro ω hω
  simp only [mem_filter] at hω ⊢
  exact ⟨hω.1,hω.2.1.2.2.1⟩

/-- The complete native/packing/MAC/Merkle bound for raw proof messages. -/
theorem probability_le (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : Context Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : S₁.Selected) W g, S₂.Good ctx W g →
      M.macTwo g (M.decode (S₁.context ctx).2.1) = tag (S₁.context ctx).2.2)
    (hspace : 2*I₂.n+2*I₁.n+tA ≤ TM) :
    probability (TM := TM) S₁ S₂ M codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂
      body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      ((1+N)*TwoFieldFS.maxBudget S₁ S₂ M + ∑ i, TwoFieldFS.slotBudget S₁ S₂ M i)/Fintype.card C +
      2*(Bcs.AdaptiveCommit.adaptiveNumerator (2*I₂.n+2*I₁.n) tA
        (1+S₁.slots+S₂.slots+(1+N)) : ℚ)/Fintype.card D := by
  rw [probability_eq_annotated]
  simpa only [Nat.cast_add, Nat.cast_one] using
    TwoFieldCommitmentFS.failureProbability_le S₁ S₂ M codec₁ codec₂
    (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
    ht₁ ht₂ (prepareBody S₁ S₂ body proofOf) (preparedProof S₁ S₂ proofOf)
    dec₁ dec₂ rootOf₁ rootOf₂ tag hrowOne hrowTwo hspace

end LfzkV2.Packed.RawExtraction
