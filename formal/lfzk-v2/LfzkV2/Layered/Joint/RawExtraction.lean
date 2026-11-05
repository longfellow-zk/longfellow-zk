import LfzkV2.Layered.Joint.Commitment
import LfzkV2.Layered.Joint.RawReplay
import LfzkV1.TSec
import Bcs.SmallMerkle

/-! Authenticated raw-verifier extraction. Coherence of the MAC annotation
is derived from the verifier's extra query; it is not an acceptance premise. -/

namespace LfzkV2.Layered.Joint.RawExtraction

open Finset RecursivePolygero LigeroFamily Merkle Merkle.MH Merkle.RandomOracle Replay
open LfzkV2.Joint (Participant Family)
open scoped Classical

variable {k s n t out₁ input₁ out₂ input₂ tA N TM blocks : ℕ}
variable (P₁ P₂ : Participant k s n t)
variable {Key C Public Out Enc D Salt Fmac : Type}
variable [Fintype C] [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {circuit₁ : Layered.Circuit P₁.Carrier out₁ input₁}
variable {circuit₂ : Layered.Circuit P₂.Carrier out₂ input₂}
variable (S₁ : Layered.Runtime.CompiledSide P₁.Carrier C (Context Key C Public) circuit₁ P₁.backend)
variable (S₂ : Layered.Runtime.CompiledSide P₂.Carrier C (Side.Frontend S₁) circuit₂ P₂.backend)
variable (M : MacData C Fmac (Counting.tupleCounts P₁.backend).Index
  (Counting.tupleCounts P₂.backend).Index blocks)
variable (decodeQuery : C → QuerySet n t)
variable [DecidableEq Enc] [Inhabited D] [Inhabited Salt]
variable [Fintype Key] [Fintype Public] [Fintype D] [DecidableEq Key] [DecidableEq D]
variable [Inhabited (Pair.family P₁ P₂).Leaf] [Fintype S₁.Data] [Fintype S₂.Data]
variable [DecidableEq (Domain S₁ S₂)]
variable (codec : Codec Salt (Pair.family P₁ P₂).Leaf D Enc)
variable (claimOf : Out → OpeningClaim n Salt (Pair.family P₁ P₂).Leaf D)
variable (ht : 0 < t) (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
variable (proofOf : Out → RawProof S₁ S₂) (dec : RoleDecoders codec) (rootOf : Key → D)

omit [Fintype Key] [Fintype Public] [Fintype D] [DecidableEq Key] [DecidableEq D]
  [Inhabited (Pair.family P₁ P₂).Leaf] [Fintype S₁.Data] [Fintype S₂.Data] in
theorem key_coherent (mt : Fin TM → D) (H : Domain S₁ S₂ → C) :
    let K := Commitment.setup S₁ S₂ (prepareBody S₁ S₂ body proofOf)
      (preparedProof S₁ S₂ proofOf) S₁.dflt
    let proof := preparedProof S₁ S₂ proofOf (K.proof mt H)
    (Replay.context S₁ S₂ proof).2.1 = H (hashInput S₁ S₂ proof 0) := by
  dsimp only
  rw [Bcs.TotalOracleCommit.Setup.proof_eq]
  simpa only [Bcs.TotalOracleCommit.Setup.search, Commitment.setup, prepareBody_fixLeft] using
    preparedProof_coherent S₁ S₂ (TwoOracleTree.fixLeft mt default body []) proofOf H

noncomputable def probability : ℚ :=
  let K := Commitment.setup S₁ S₂ (prepareBody S₁ S₂ body proofOf)
    (preparedProof S₁ S₂ proofOf) S₁.dflt
  let ck := Commitment.check codec (fun result : Out × C => claimOf result.1)
  let fails := fun ω : (Fin TM → D) × (Domain S₁ S₂ → C) =>
    let result := K.proof ω.1 ω.2
    let proof := preparedProof S₁ S₂ proofOf result
    let W := Pair.oracleEquiv P₁ P₂
      (Commitment.cutOracle (Pair.family P₁ P₂) K dec rootOf ω.1 ω.2 (Replay.context S₁ S₂ proof).1)
    Pair.CompiledAccepts P₁ P₂ S₁ S₂ decodeQuery ht
      (codec.withOracle (K.merkleOracle ck ω.1 ω.2)) ω.2 proof
      (rootOf (Replay.context S₁ S₂ proof).1) (claimOf result.1) ∧
    Extraction.extract S₁ S₂ M W proof = none
  ((univ.filter fails).card : ℚ) /
    ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂))

theorem probability_eq_annotated :
    probability (TM := TM) P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht body proofOf dec rootOf =
    Commitment.failureProbability (TM := TM) P₁ P₂ S₁ S₂ M decodeQuery codec
      (fun result : Out × C => claimOf result.1) ht (prepareBody S₁ S₂ body proofOf)
      (preparedProof S₁ S₂ proofOf) dec rootOf := by
  unfold probability Commitment.failureProbability
  apply congrArg (fun s : Finset ((Fin TM → D) × (Domain S₁ S₂ → C)) =>
    (s.card : ℚ) / ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂)))
  ext ω
  have hc := key_coherent P₁ P₂ S₁ S₂ body proofOf ω.1 ω.2
  dsimp only at hc
  simp only [mem_filter]
  tauto

theorem probability_le_one :
    probability (TM := TM) P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht body proofOf dec rootOf ≤ 1 := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  unfold probability
  exact LfzkV1.TSec.ratio_le_one _

/-- A short Merkle trace must guess a digest before it can authenticate the
large joint tree. No assumption about independence of the fields enters. -/
theorem probability_small_merkle (hn : 128 ≤ n) (hsmall : tA < 8) (hspace : 2*n+tA ≤ TM) :
    probability (TM := TM) P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht body proofOf dec rootOf ≤
      (2*tA*tA+(2*n+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ) := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  let K := Commitment.setup S₁ S₂ (prepareBody S₁ S₂ body proofOf)
    (preparedProof S₁ S₂ proofOf) S₁.dflt
  let ck := Commitment.check codec (fun result : Out × C => claimOf result.1)
  have h := K.merkle_small_ratio_le codec dec ck rootOf (fun result : Out × C => claimOf result.1)
    (Commitment.check_contains codec (fun result : Out × C => claimOf result.1))
    hsmall hn (by omega) hspace (by omega)
  refine le_trans ?_ h
  unfold probability
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (Nat.cast_le (α := ℚ)).mpr
  apply card_le_card
  intro ω hω
  simp only [mem_filter] at hω ⊢
  exact ⟨hω.1,hω.2.1.2.2.2.1⟩

/-- Exact finite authenticated extraction with a single shared opening and
the verifier's additional MAC lookup. -/
theorem probability_le
    (hqueryOne : ∀ c, S₁.decodeQuery c = P₁.localQuery (decodeQuery c))
    (hqueryTwo : ∀ c, S₂.decodeQuery c = P₂.localQuery (decodeQuery c))
    (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : Context Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : Side.Frontend S₁) W g, S₂.Good ctx W g →
      M.macTwo g (M.decode ctx.1.1.2.1) = tag ctx.1.1.2.2)
    (hspace : 2*n+tA ≤ TM) :
    probability (TM := TM) P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht body proofOf dec rootOf ≤
      ((1+N)*Cost.maxBudget S₁ S₂ M + ∑ i, Cost.slotBudget S₁ S₂ M i)/Fintype.card C +
      (Bcs.AdaptiveCommit.adaptiveNumerator (2*n) tA (slots S₁ S₂+(1+N)) : ℚ)/Fintype.card D := by
  rw [probability_eq_annotated]
  simpa only [Nat.cast_add, Nat.cast_one] using
    Commitment.extraction_le P₁ P₂ S₁ S₂ M decodeQuery codec
      (fun result : Out × C => claimOf result.1) ht (prepareBody S₁ S₂ body proofOf)
      (preparedProof S₁ S₂ proofOf) dec rootOf hqueryOne hqueryTwo tag hrowOne hrowTwo hspace

end LfzkV2.Layered.Joint.RawExtraction
