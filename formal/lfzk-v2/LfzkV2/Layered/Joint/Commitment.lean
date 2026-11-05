import LfzkV2.Joint.Commitment
import LfzkV2.Layered.Joint.FiatShamir
import LfzkV2.Layered.Joint.Pair
import Bcs.PotentialCommit

/-!
# One authenticated commitment for the mdoc tuple

This checkpoint uses the quad-fragment layered frontend. A single cut trace extracts the whole
typed column tuple before the MAC challenge. The generic Merkle reduction
therefore contributes one explanation error and one checker of size `2*n`.
-/

namespace LfzkV2.Layered.Joint.Commitment

open RecursivePolygero LigeroFamily Merkle Merkle.MH Bcs.TotalOracle Finset
  Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree Replay
open LfzkV2.Joint (Participant Family)
open scoped Classical

section Setup
variable {F₁ F₂ Key C Public Out Enc D : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable {out₁ input₁ out₂ input₂ tA N : ℕ}
variable {circuit₁ : Layered.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Layered.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : Layered.Runtime.CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : Layered.Runtime.CompiledSide F₂ C (Side.Frontend S₁) circuit₂ I₂)

def setup [DecidableEq (Domain S₁ S₂)]
    (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
    (proofOf : Out → Proof S₁ S₂) (dflt : C) :
    Bcs.TotalOracleCommit.Setup Enc D (Domain S₁ S₂) C Out Key tA N (slots S₁ S₂) where
  body := body
  hashInput out := hashInput S₁ S₂ (proofOf out)
  dflt := dflt
  key := key S₁ S₂
  keyOut out := (Replay.context S₁ S₂ (proofOf out)).1
  hkey out j := hashInput_key S₁ S₂ (proofOf out) j
end Setup

export LfzkV2.Joint.Commitment (cutOracle cutOracle_off check check_contains)

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
variable (proofOf : Out → Proof S₁ S₂) (dec : RoleDecoders codec) (rootOf : Key → D)

noncomputable def failureProbability : ℚ :=
  let K := setup S₁ S₂ body proofOf S₁.dflt
  let ck := check codec claimOf
  let fails := fun ω : (Fin TM → D) × (Domain S₁ S₂ → C) =>
    let result := K.proof ω.1 ω.2
    let proof := proofOf result
    let W := Pair.oracleEquiv P₁ P₂
      (cutOracle (Pair.family P₁ P₂) K dec rootOf ω.1 ω.2 (Replay.context S₁ S₂ proof).1)
    (Replay.context S₁ S₂ proof).2.1 = ω.2 (hashInput S₁ S₂ proof 0) ∧
    Pair.CompiledAccepts P₁ P₂ S₁ S₂ decodeQuery ht
      (codec.withOracle (K.merkleOracle ck ω.1 ω.2)) ω.2 proof
      (rootOf (Replay.context S₁ S₂ proof).1) (claimOf result) ∧
    Extraction.extract S₁ S₂ M W proof = none
  ((univ.filter fails).card : ℚ) /
    ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂))

/-- All component soundness and the commitment-context invariance are proved
reductions. The remaining premises identify the runtime's shared sampler and
the two circuits' MAC row equations. -/
theorem extraction_le
    (hqueryOne : ∀ c, S₁.decodeQuery c = P₁.localQuery (decodeQuery c))
    (hqueryTwo : ∀ c, S₂.decodeQuery c = P₂.localQuery (decodeQuery c))
    (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : Context Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : Side.Frontend S₁) W g, S₂.Good ctx W g →
      M.macTwo g (M.decode ctx.1.1.2.1) = tag ctx.1.1.2.2)
    (hspace : 2*n+tA ≤ TM) :
    failureProbability (TM := TM) P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht body proofOf dec rootOf ≤
      (N * Cost.maxBudget S₁ S₂ M + ∑ i, Cost.slotBudget S₁ S₂ M i)/Fintype.card C +
      (Bcs.AdaptiveCommit.adaptiveNumerator (2*n) tA (slots S₁ S₂+N) : ℚ)/Fintype.card D := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  let K := setup S₁ S₂ body proofOf S₁.dflt
  let ck := check codec claimOf
  let context := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) key =>
    Pair.oracleEquiv P₁ P₂ (cutOracle (Pair.family P₁ P₂) K dec rootOf mt H key)
  let accepts := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) =>
    let proof := proofOf (K.proof mt H)
    (Replay.context S₁ S₂ proof).2.1 = H (hashInput S₁ S₂ proof 0) ∧
    Pair.CompiledAccepts P₁ P₂ S₁ S₂ decodeQuery ht (codec.withOracle (K.merkleOracle ck mt H))
      H proof (rootOf (Replay.context S₁ S₂ proof).1) (claimOf (K.proof mt H))
  let fails := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) =>
    let proof := proofOf (K.proof mt H)
    Extraction.extract S₁ S₂ M (context mt H (Replay.context S₁ S₂ proof).1) proof = none
  let ideal := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) =>
    let proof := proofOf (K.proof mt H)
    let W := context mt H (Replay.context S₁ S₂ proof).1
    (Replay.context S₁ S₂ proof).2.1 = H (hashInput S₁ S₂ proof 0) ∧
    S₁.Accepts W.1 (firstOracle S₁ S₂ H proof) (selectedOne S₁ S₂ proof) ∧
    S₂.Accepts W.2 (secondOracle S₁ S₂ H proof) (selectedTwo S₁ S₂ proof) ∧ fails mt H
  let fsError : ℚ := (N * Cost.maxBudget S₁ S₂ M + ∑ i, Cost.slotBudget S₁ S₂ M i)/Fintype.card C
  have hfs mt : ((univ.filter (ideal mt)).card : ℚ)/
      (Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂) ≤ fsError := by
    have h := FiatShamir.extraction_le S₁ S₂ M (K.search mt) proofOf (context mt)
      (by
        intro H H' x hoff
        exact congrArg (Pair.oracleEquiv P₁ P₂)
          (cutOracle_off (Pair.family P₁ P₂) K dec rootOf mt H H' x hoff)) tag hrowOne hrowTwo
    convert! h using 1
    congr 3
    ext H
    simp only [mem_filter]
    dsimp only [ideal, fails]
    rw [K.proof_eq]
  have hbridge mt H (ha : accepts mt H) (he : K.Explains dec rootOf claimOf mt H)
      (hb : fails mt H) : ideal mt H := by
    obtain ⟨e,hext,hagree,-⟩ := he
    let proof := proofOf (K.proof mt H)
    have hv := Pair.accepts_of_extraction P₁ P₂ S₁ S₂ decodeQuery ht dec
      (codec.withOracle (K.merkleOracle ck mt H)) H proof
      (rootOf (Replay.context S₁ S₂ proof).1)
      ((K.atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape (Replay.context S₁ S₂ proof).1)
      (claimOf (K.proof mt H)) e hext hagree hqueryOne hqueryTwo ha.2
    exact ⟨ha.1,hv.1,hv.2,hb⟩
  have hn : t ≤ n := by simpa only [P₁.openings, P₁.columns] using P₁.backend.query_le
  have h := K.ratio_le_from_potential codec dec ck rootOf claimOf (check_contains codec claimOf)
    (by unfold slots; omega) (by omega) hspace (by omega) accepts fails
    (fun _ _ h => h.2.2.2.2.1) fsError (by
      intro mt
      apply le_trans _ (hfs mt)
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (Nat.cast_le (α := ℚ)).mpr
      exact card_le_card (by
        intro H hH
        simp only [mem_filter] at hH
        exact mem_filter.mpr ⟨mem_univ _,hbridge mt H hH.2.1 hH.2.2.1 hH.2.2.2⟩))
  simpa only [failureProbability, accepts, fails, context, K, ck, fsError, and_assoc] using h

end LfzkV2.Layered.Joint.Commitment
