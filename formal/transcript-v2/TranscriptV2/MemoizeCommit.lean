import TranscriptV2.MemoizeCut
import Bcs.PotentialCommit

/-! Merkle composition with a distinct transcript-query budget. The program
may contain arbitrarily many repeated calls within its finite execution fuel.
Normalization preserves the original verifier and its actual cut extractor. -/
noncomputable section
namespace TranscriptV2.Memoize
open Finset Merkle Merkle.MH Merkle.RandomOracle
open Merkle.RandomOracle.TwoOracleTree Bcs.AdaptiveCommit Bcs.TotalOracle
open scoped Classical

variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA calls rounds TM Q : ℕ}
variable (S : Bcs.TotalOracleCommit.Setup Enc D Pt C Out Key tA calls rounds)
variable [DecidableEq Key] [DecidableEq D] {Salt M : Type}
  [Inhabited Salt] [Inhabited M] {n fc : ℕ}

/-- A distinct-query budget for the complete analysis program suffices for
Merkle composition. `Explains` is the original first-context-cut extractor,
whose identity under caching is proved by `normalizeSetup_Explains`. -/
theorem ratio_le_from_potential_support
    [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    (fallback : Out)
    (hsupport : ∀ (mt : Fin TM → D) (H : Pt → C),
      (TranscriptV2.seen (fixLeft mt default S.body []) H).card ≤ Q)
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2*n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hrounds : 0 < rounds) (ht : tA ≤ TM) (hF : fc+tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc Fails : (Fin TM → D) → (Pt → C) → Prop)
    (hacc : ∀ mt H, Acc mt H → S.MerkleAccepts codec check rootOf claimOf mt H)
    (fsBound : ℚ)
    (hfs : ∀ mt : Fin TM → D,
      ((univ.filter fun H : Pt → C =>
        Acc mt H ∧ S.Explains dec rootOf claimOf mt H ∧ Fails mt H).card : ℚ) /
        (Fintype.card C : ℚ)^Fintype.card Pt ≤ fsBound) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card Pt) ≤
      fsBound + (adaptiveNumerator fc tA (rounds+Q) : ℚ) / Fintype.card D := by
  apply (normalizeSetup S fallback Q).ratio_le_from_potential
    codec dec check rootOf claimOf hcheck hrounds ht hF hTM Acc Fails
    (fun mt H accepted => (normalizeSetup_MerkleAccepts S fallback mt H
      (hsupport mt H) codec check rootOf claimOf).mpr (hacc mt H accepted)) fsBound
  intro mt
  have he : (univ.filter fun H : Pt → C =>
      Acc mt H ∧ (normalizeSetup S fallback Q).Explains dec rootOf claimOf mt H ∧ Fails mt H) =
      (univ.filter fun H : Pt → C =>
        Acc mt H ∧ S.Explains dec rootOf claimOf mt H ∧ Fails mt H) := by
    ext H
    simp only [mem_filter,mem_univ,true_and,
      normalizeSetup_Explains S fallback mt H (hsupport mt H) dec rootOf claimOf]
  rw [he]
  exact hfs mt

end TranscriptV2.Memoize
