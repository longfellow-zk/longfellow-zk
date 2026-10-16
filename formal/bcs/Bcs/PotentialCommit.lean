import Bcs.TotalOracleCommit
import Bcs.PotentialGrinding

/-!
# Merkle composition for an exact graded Fiat--Shamir bound

The challenge-oracle side is supplied as a probability bound at each fixed
Merkle tape.  This separates the potential argument from the unchanged
cut-trace/Merkle error.  A client may obtain that premise from
`CtxGrinding.potential_ratio_le_rat`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracleCommit.Setup

open Finset Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree Bcs.AdaptiveCommit Bcs.TotalOracle
open scoped Classical

variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N L TM : ℕ}
variable (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N L)
variable [DecidableEq Key] [DecidableEq D] {Salt M : Type}
  [Inhabited Salt] [Inhabited M] {n fc : ℕ}

/-- Combine a potential-based challenge-oracle estimate with the original
Merkle extraction error.  This statement does not assume any particular
shape for the potential or the Ligero agreement profile. -/
theorem ratio_le_from_potential
    [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2 * n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc : (Fin TM → D) → (Pt → C) → Prop)
    (Fails : (Fin TM → D) → (Pt → C) → Prop)
    (hacc : ∀ mt H, Acc mt H → S.MerkleAccepts codec check rootOf claimOf mt H)
    (fsBound : ℚ)
    (hfs : ∀ mt : Fin TM → D,
      ((univ.filter fun H : Pt → C =>
        Acc mt H ∧ S.Explains dec rootOf claimOf mt H ∧
          Fails mt H).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Pt ≤ fsBound) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      fsBound + (adaptiveNumerator fc tA (L + N) : ℚ) /
        Fintype.card D := by
  classical
  let A := adaptiveNumerator fc tA (L + N)
  let good : Finset ((Fin TM → D) × (Pt → C)) :=
    univ.filter fun ω => Acc ω.1 ω.2 ∧
      S.Explains dec rootOf claimOf ω.1 ω.2 ∧ Fails ω.1 ω.2
  let badMerkle : Finset ((Fin TM → D) × (Pt → C)) :=
    univ.filter fun ω => S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
      ¬ S.Explains dec rootOf claimOf ω.1 ω.2
  have hsplit : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card ≤
        good.card + badMerkle.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_cases hex : S.Explains dec rootOf claimOf ω.1 ω.2
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω.1, hex, hω.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc _ _ hω.1, hex⟩)
  have hc : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℚ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hfsSum : (good.card : ℚ) ≤
      fsBound * (Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt := by
    have hcount : good.card = ∑ mt : Fin TM → D,
        (univ.filter fun H : Pt → C => Acc mt H ∧
          S.Explains dec rootOf claimOf mt H ∧
          Fails mt H).card := by
      unfold good
      rw [card_filter_prod_fst]
    rw [hcount]
    push_cast
    have hden : 0 < (Fintype.card C : ℚ) ^ Fintype.card Pt := pow_pos hc _
    have hsum : (∑ mt : Fin TM → D,
        ((univ.filter fun H : Pt → C => Acc mt H ∧
          S.Explains dec rootOf claimOf mt H ∧
          Fails mt H).card : ℚ)) ≤
        ∑ _mt : Fin TM → D,
          fsBound * (Fintype.card C : ℚ) ^ Fintype.card Pt := by
      apply Finset.sum_le_sum
      intro mt _
      exact (div_le_iff₀ hden).mp (hfs mt)
    calc
      (∑ mt : Fin TM → D,
        ((univ.filter fun H : Pt → C => Acc mt H ∧
          S.Explains dec rootOf claimOf mt H ∧
          Fails mt H).card : ℚ)) ≤
          ∑ _mt : Fin TM → D,
            fsBound * (Fintype.card C : ℚ) ^ Fintype.card Pt := hsum
      _ = fsBound * (Fintype.card D : ℚ) ^ TM *
          (Fintype.card C : ℚ) ^ Fintype.card Pt := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
  have hmkNat : badMerkle.card ≤
      Fintype.card C ^ Fintype.card Pt * (A * Fintype.card D ^ (TM - 1)) := by
    rw [card_filter_prod_snd]
    calc
      ∑ H : Pt → C, (univ.filter fun mt : Fin TM → D =>
          S.MerkleAccepts codec check rootOf claimOf mt H ∧
          ¬ S.Explains dec rootOf claimOf mt H).card ≤
        ∑ _H : Pt → C, A * Fintype.card D ^ (TM - 1) :=
          Finset.sum_le_sum fun H _ =>
            (S.atOracle H).merkle_card_le codec dec check rootOf claimOf
              hcheck hL ht hF emptyTape
      _ = Fintype.card C ^ Fintype.card Pt *
          (A * Fintype.card D ^ (TM - 1)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul]
  have hpowD : (Fintype.card D : ℚ) ^ TM =
      (Fintype.card D : ℚ) ^ (TM - 1) * Fintype.card D := by
    rw [← pow_succ]
    congr 1
    omega
  have hmk : (badMerkle.card : ℚ) ≤
      ((adaptiveNumerator fc tA (L + N) : ℚ) / Fintype.card D) *
        ((Fintype.card D : ℚ) ^ TM *
          (Fintype.card C : ℚ) ^ Fintype.card Pt) := by
    have h := (Nat.cast_le (α := ℚ)).mpr hmkNat
    push_cast at h
    rw [hpowD]
    calc
      (badMerkle.card : ℚ) ≤
          (Fintype.card C : ℚ) ^ Fintype.card Pt *
            ((A : ℚ) * (Fintype.card D : ℚ) ^ (TM - 1)) := h
      _ = _ := by field_simp; ring
  have htotal : (0 : ℚ) <
      (Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt :=
    mul_pos (pow_pos hd _) (pow_pos hc _)
  rw [div_le_iff₀ htotal]
  have hs : ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) ≤
        (good.card : ℚ) + (badMerkle.card : ℚ) := by exact_mod_cast hsplit
  have hsum := add_le_add hfsSum hmk
  nlinarith [hsum]

/-- The existing cut-trace/Merkle failure estimate, isolated so a second
commitment can be added to a potential-based challenge-oracle estimate. -/
theorem merkle_error_ratio_le
    [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2 * n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
        ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      (adaptiveNumerator fc tA (L + N) : ℚ) / Fintype.card D := by
  classical
  let A := adaptiveNumerator fc tA (L + N)
  have hmk : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
        ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card ≤
      Fintype.card C ^ Fintype.card Pt *
        (A * Fintype.card D ^ (TM - 1)) := by
    rw [card_filter_prod_snd]
    calc
      ∑ H : Pt → C, (univ.filter fun mt : Fin TM → D =>
          S.MerkleAccepts codec check rootOf claimOf mt H ∧
          ¬ S.Explains dec rootOf claimOf mt H).card ≤
        ∑ _H : Pt → C, A * Fintype.card D ^ (TM - 1) :=
          Finset.sum_le_sum fun H _ =>
            (S.atOracle H).merkle_card_le codec dec check rootOf claimOf
              hcheck hL ht hF emptyTape
      _ = Fintype.card C ^ Fintype.card Pt *
          (A * Fintype.card D ^ (TM - 1)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul]
  have hd : (0 : ℚ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hc : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hpowD : (Fintype.card D : ℚ) ^ TM =
      (Fintype.card D : ℚ) ^ (TM - 1) * Fintype.card D := by
    rw [← pow_succ]
    congr 1
    omega
  rw [div_le_iff₀ (mul_pos (pow_pos hd _) (pow_pos hc _))]
  have hq := (Nat.cast_le (α := ℚ)).mpr hmk
  push_cast at hq
  rw [hpowD]
  calc
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
        ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card : ℚ) ≤
      (Fintype.card C : ℚ) ^ Fintype.card Pt *
        ((A : ℚ) * (Fintype.card D : ℚ) ^ (TM - 1)) := hq
    _ = (A : ℚ) / Fintype.card D *
        ((Fintype.card D : ℚ) ^ (TM - 1) * Fintype.card D *
          (Fintype.card C : ℚ) ^ Fintype.card Pt) := by
          field_simp

/-- Two Merkle explanations can be composed with one potential estimate.  The
challenge-oracle estimate is made only on tapes for which both committed
objects have been explained; each opening contributes the original cut-trace
error. -/
theorem ratio_le_two_from_potential
    [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    (codec₁ : Codec Salt M D Enc) (dec₁ : RoleDecoders codec₁)
    (check₁ : Out → Tree Enc D Unit fc) (rootOf₁ : Key → D)
    (claimOf₁ : Out → OpeningClaim n Salt M D)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n (claimOf₁ out).I (claimOf₁ out).a
          (claimOf₁ out).pf (2 * n) fun _ => default).run H).2,
        qa ∈ ((check₁ out).run H).2)
    {Salt₂ M₂ : Type} [Inhabited Salt₂] [Inhabited M₂] {n₂ : ℕ}
    (codec₂ : Codec Salt₂ M₂ D Enc) (dec₂ : RoleDecoders codec₂)
    (check₂ : Out → Tree Enc D Unit fc) (rootOf₂ : Key → D)
    (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a
          (claimOf₂ out).pf (2 * n₂) fun _ => default).run H).2,
        qa ∈ ((check₂ out).run H).2)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc Fails : (Fin TM → D) → (Pt → C) → Prop)
    (hacc₁ : ∀ mt H, Acc mt H →
      S.MerkleAccepts codec₁ check₁ rootOf₁ claimOf₁ mt H)
    (hacc₂ : ∀ mt H, Acc mt H →
      S.MerkleAccepts codec₂ check₂ rootOf₂ claimOf₂ mt H)
    (fsBound : ℚ)
    (hfs : ∀ mt : Fin TM → D,
      ((univ.filter fun H : Pt → C =>
        Acc mt H ∧ S.Explains dec₂ rootOf₂ claimOf₂ mt H ∧
          S.Explains dec₁ rootOf₁ claimOf₁ mt H ∧ Fails mt H).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Pt ≤ fsBound) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      fsBound + 2 * (adaptiveNumerator fc tA (L + N) : ℚ) /
        Fintype.card D := by
  classical
  let den : ℚ := (Fintype.card D : ℚ) ^ TM *
    (Fintype.card C : ℚ) ^ Fintype.card Pt
  have hd : 0 < den := by
    dsimp [den]
    exact mul_pos (pow_pos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)) _)
      (pow_pos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card C)) _)
  let good : Finset ((Fin TM → D) × (Pt → C)) :=
    univ.filter fun ω => Acc ω.1 ω.2 ∧
      S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2 ∧ Fails ω.1 ω.2
  let bad : Finset ((Fin TM → D) × (Pt → C)) :=
    univ.filter fun ω => S.MerkleAccepts codec₂ check₂ rootOf₂ claimOf₂ ω.1 ω.2 ∧
      ¬ S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2
  have hsplit : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card ≤ good.card + bad.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_cases hex : S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω.1, hex, hω.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc₂ _ _ hω.1, hex⟩)
  have hgood : (good.card : ℚ) / den ≤
      fsBound + (adaptiveNumerator fc tA (L + N) : ℚ) /
        Fintype.card D := by
    simpa only [good, den, and_assoc] using
      (S.ratio_le_from_potential codec₁ dec₁ check₁ rootOf₁ claimOf₁
        hcheck₁ hL ht hF hTM
        (fun mt H => Acc mt H ∧ S.Explains dec₂ rootOf₂ claimOf₂ mt H)
        Fails (fun mt H h => hacc₁ mt H h.1) fsBound (by
          intro mt
          simpa only [and_assoc] using hfs mt))
  have hbad : (bad.card : ℚ) / den ≤
      (adaptiveNumerator fc tA (L + N) : ℚ) / Fintype.card D := by
    simpa only [bad, den] using
      (S.merkle_error_ratio_le codec₂ dec₂ check₂ rootOf₂ claimOf₂
        hcheck₂ hL ht hF hTM)
  have hs : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card ≤ good.card + bad.card := hsplit
  have hsQ : (((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) / den) ≤
      (good.card : ℚ) / den + (bad.card : ℚ) / den := by
    have h : (((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ)) ≤
        (good.card : ℚ) + (bad.card : ℚ) := by exact_mod_cast hs
    calc
      _ ≤ ((good.card : ℚ) + (bad.card : ℚ)) / den :=
        div_le_div_of_nonneg_right h (le_of_lt hd)
      _ = _ := by ring
  dsimp [den] at hsQ
  calc
    _ ≤ (good.card : ℚ) / ((Fintype.card D : ℚ) ^ TM *
          (Fintype.card C : ℚ) ^ Fintype.card Pt) +
        (bad.card : ℚ) / ((Fintype.card D : ℚ) ^ TM *
          (Fintype.card C : ℚ) ^ Fintype.card Pt) := hsQ
    _ ≤ (fsBound + (adaptiveNumerator fc tA (L + N) : ℚ) /
          Fintype.card D) +
        (adaptiveNumerator fc tA (L + N) : ℚ) / Fintype.card D :=
      add_le_add hgood hbad
    _ = _ := by ring

/-- The context and prefix structure of the deployed compiler, without a
Boolean bad-answer classifier.  The rational charge is supplied separately. -/
def potentialCarrier [Fintype C] (mt : Fin TM → D)
    (pts : PrefixPoints Pt) :
    TotalOracle.CtxGrinding C Pt Out Key (Key × List (Enc × D)) N L :=
  S.grinding mt pts (fun _ _ _ _ => False) (fun _ => 0) (by simp)

omit [DecidableEq D] in
/-- Every verifier slot contributes to the charged-point sum when the hash
inputs record their slots injectively.  This is the bridge from an
extraction telescope along the verifier's transcript to the adaptive
random-oracle potential compiler. -/
theorem verifier_potential_charge_le
    [Fintype Pt] [Fintype C]
    (pts : PrefixPoints Pt)
    (hinputs : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (charge : (Key × List (Enc × D)) → (x : Pt) →
      (Fin (pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (mt : Fin TM → D) (H : Pt → C) :
    let G := S.potentialCarrier mt pts
    (∑ i : Fin L,
      charge (G.ctxAt H (G.key (G.point H i.val)))
        (G.point H i.val) (pts.chal H (G.point H i.val))
        (H (G.point H i.val))) ≤
      ∑ x : Pt, if G.Charged x H then
        charge (G.ctxAt H (G.key x)) x (pts.chal H x) (H x) else 0 := by
  let G := S.potentialCarrier mt pts
  exact G.verifier_charge_le_total (by
      intro out i j hij
      exact hinputs out hij)
    (fun x => charge (G.ctxAt H (G.key x)) x (pts.chal H x) (H x))
    (fun x => hnonneg _ _ _ _) H

omit [DecidableEq D] in
/-- A verifier-transcript extraction telescope is enough for the adaptive
compiler when the verifier's hash inputs are injective.  No separate event
partition or selected escape slot is required. -/
theorem charged_chain_of_verifier_chain
    [Fintype Pt] [Fintype C]
    (pts : PrefixPoints Pt)
    (hinputs : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (charge : (Key × List (Enc × D)) → (x : Pt) →
      (Fin (pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (E : (Fin TM → D) → (Pt → C) → Prop)
    (hpath : ∀ mt H, E mt H →
      let G := S.potentialCarrier mt pts
      1 ≤ ∑ i : Fin L,
        charge (G.ctxAt H (G.key (G.point H i.val)))
          (G.point H i.val) (pts.chal H (G.point H i.val))
          (H (G.point H i.val))) :
    ∀ mt H, E mt H →
      let G := S.potentialCarrier mt pts
      1 ≤ ∑ x : Pt, if G.Charged x H then
        charge (G.ctxAt H (G.key x)) x (pts.chal H x) (H x) else 0 := by
  intro mt H hE
  exact (hpath mt H hE).trans
    (S.verifier_potential_charge_le pts hinputs charge hnonneg mt H)

/-- Extraction-first potential compiler for a re-committing prover.  The
extractor may read the full transcript.  `hchain` is the
protocol proof that an accepted execution with no extracted witness has
accumulated potential at least one.  A client's local graded transition
theorems discharge `hlocal` and `hchain`; the Merkle loss is unchanged. -/
theorem extraction_failure_ratio_le_potential
    [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    {Witness : Type}
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2 * n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (pts : PrefixPoints Pt)
    (charge : (Key × List (Enc × D)) → (x : Pt) →
      (Fin (pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (budget : Pt → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (hlocal : ∀ κ x pref, ∑ c : C, charge κ x pref c ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ x, budget x ≤ betaMax)
    (slotBeta : Fin L → ℚ)
    (hslot : ∀ out i, budget (S.hashInput out i.val) ≤ slotBeta i)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc : (Fin TM → D) → (Pt → C) → Prop)
    (extract : (Fin TM → D) → (Pt → C) → Option Witness)
    (hacc : ∀ mt H, Acc mt H → S.MerkleAccepts codec check rootOf claimOf mt H)
    (hchain : ∀ mt H, Acc mt H → S.Explains dec rootOf claimOf mt H →
      extract mt H = none →
      1 ≤ ∑ x : Pt, if (S.potentialCarrier mt pts).Charged x H then
        charge ((S.potentialCarrier mt pts).ctxAt H
          ((S.potentialCarrier mt pts).key x)) x
          (pts.chal H x) (H x) else 0) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ extract ω.1 ω.2 = none).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C +
        (adaptiveNumerator fc tA (L + N) : ℚ) / Fintype.card D := by
  classical
  convert S.ratio_le_from_potential codec dec check rootOf claimOf hcheck
    hL ht hF hTM Acc (fun mt H => extract mt H = none) hacc
    ((N * betaMax + ∑ i, slotBeta i) / Fintype.card C) ?_ using 1
  · congr 1
    apply congrArg (fun z : ℕ => (z : ℚ))
    apply congrArg Finset.card
    ext ω
    simp
  intro mt
  let G := S.potentialCarrier mt pts
  convert G.potential_ratio_le_rat charge hnonneg budget hbudget hlocal
    betaMax hbetaMax hmax slotBeta hslot
    (fun H => Acc mt H ∧ S.Explains dec rootOf claimOf mt H ∧
      extract mt H = none)
    (fun H hH => hchain mt H hH.1 hH.2.1 hH.2.2) using 1
  congr 1
  apply congrArg (fun z : ℕ => (z : ℚ))
  apply congrArg Finset.card
  ext H
  simp

/-- Extraction-first two-opening compiler.  The witness is read from the
explained commitments and the full challenge transcript.  Both Merkle errors
are charged once, while the graded challenge oracle is charged only once. -/
theorem extraction_failure_ratio_le_two_potential
    [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    {Witness : Type}
    (codec₁ : Codec Salt M D Enc) (dec₁ : RoleDecoders codec₁)
    (check : Out → Tree Enc D Unit fc) (rootOf₁ : Key → D)
    (claimOf₁ : Out → OpeningClaim n Salt M D)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n (claimOf₁ out).I (claimOf₁ out).a
          (claimOf₁ out).pf (2 * n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    {Salt₂ M₂ : Type} [Inhabited Salt₂] [Inhabited M₂] {n₂ : ℕ}
    (codec₂ : Codec Salt₂ M₂ D Enc) (dec₂ : RoleDecoders codec₂)
    (rootOf₂ : Key → D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a
          (claimOf₂ out).pf (2 * n₂) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (pts : PrefixPoints Pt)
    (charge : (Key × List (Enc × D)) → (x : Pt) →
      (Fin (pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (budget : Pt → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (hlocal : ∀ κ x pref, ∑ c : C, charge κ x pref c ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ x, budget x ≤ betaMax)
    (slotBeta : Fin L → ℚ)
    (hslot : ∀ out i, budget (S.hashInput out i.val) ≤ slotBeta i)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc : (Fin TM → D) → (Pt → C) → Prop)
    (extract : (Fin TM → D) → (Pt → C) → Option Witness)
    (hacc₁ : ∀ mt H, Acc mt H →
      S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ mt H)
    (hacc₂ : ∀ mt H, Acc mt H →
      S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ mt H)
    (hchain : ∀ mt H, Acc mt H →
      S.Explains dec₁ rootOf₁ claimOf₁ mt H →
      S.Explains dec₂ rootOf₂ claimOf₂ mt H →
      extract mt H = none →
      1 ≤ ∑ x : Pt, if (S.potentialCarrier mt pts).Charged x H then
        charge ((S.potentialCarrier mt pts).ctxAt H
          ((S.potentialCarrier mt pts).key x)) x
          (pts.chal H x) (H x) else 0) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ extract ω.1 ω.2 = none).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C +
        2 * (adaptiveNumerator fc tA (L + N) : ℚ) /
          Fintype.card D := by
  classical
  have hfs : ∀ mt : Fin TM → D,
      ((univ.filter fun H : Pt → C => Acc mt H ∧
        S.Explains dec₂ rootOf₂ claimOf₂ mt H ∧
        S.Explains dec₁ rootOf₁ claimOf₁ mt H ∧
        extract mt H = none).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Pt ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C := by
    intro mt
    let G := S.potentialCarrier mt pts
    convert G.potential_ratio_le_rat charge hnonneg budget hbudget hlocal
      betaMax hbetaMax hmax slotBeta hslot
      (fun H => Acc mt H ∧ S.Explains dec₂ rootOf₂ claimOf₂ mt H ∧
        S.Explains dec₁ rootOf₁ claimOf₁ mt H ∧ extract mt H = none)
      (fun H hH => hchain mt H hH.1 hH.2.2.1 hH.2.1 hH.2.2.2) using 1
  convert S.ratio_le_two_from_potential codec₁ dec₁ check rootOf₁ claimOf₁
    hcheck₁ codec₂ dec₂ check rootOf₂ claimOf₂ hcheck₂ hL ht hF hTM
    Acc (fun mt H => extract mt H = none) hacc₁ hacc₂
    ((N * betaMax + ∑ i, slotBeta i) / Fintype.card C) (by
      intro mt
      convert hfs mt using 1
      congr 1
      apply congrArg (fun z : ℕ => (z : ℚ))
      apply congrArg Finset.card
      ext H
      simp) using 1
  congr 1
  apply congrArg (fun z : ℕ => (z : ℚ))
  apply congrArg Finset.card
  ext ω
  simp

/-- The two-opening extraction compiler in verifier-path form.  Clients
prove one unit of charge on the actual deployed transcript; injectivity
then promotes that path sum to the adaptive oracle's charged-point sum. -/
theorem extraction_failure_ratio_le_two_verifier_potential
    [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    {Witness : Type}
    (codec₁ : Codec Salt M D Enc) (dec₁ : RoleDecoders codec₁)
    (check : Out → Tree Enc D Unit fc) (rootOf₁ : Key → D)
    (claimOf₁ : Out → OpeningClaim n Salt M D)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n (claimOf₁ out).I (claimOf₁ out).a
          (claimOf₁ out).pf (2 * n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    {Salt₂ M₂ : Type} [Inhabited Salt₂] [Inhabited M₂] {n₂ : ℕ}
    (codec₂ : Codec Salt₂ M₂ D Enc) (dec₂ : RoleDecoders codec₂)
    (rootOf₂ : Key → D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a
          (claimOf₂ out).pf (2 * n₂) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (pts : PrefixPoints Pt)
    (hinputs : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (charge : (Key × List (Enc × D)) → (x : Pt) →
      (Fin (pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (budget : Pt → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (hlocal : ∀ κ x pref, ∑ c : C, charge κ x pref c ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ x, budget x ≤ betaMax)
    (slotBeta : Fin L → ℚ)
    (hslot : ∀ out i, budget (S.hashInput out i.val) ≤ slotBeta i)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc : (Fin TM → D) → (Pt → C) → Prop)
    (extract : (Fin TM → D) → (Pt → C) → Option Witness)
    (hacc₁ : ∀ mt H, Acc mt H →
      S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ mt H)
    (hacc₂ : ∀ mt H, Acc mt H →
      S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ mt H)
    (hpath : ∀ mt H, Acc mt H →
      S.Explains dec₁ rootOf₁ claimOf₁ mt H →
      S.Explains dec₂ rootOf₂ claimOf₂ mt H →
      extract mt H = none →
      let G := S.potentialCarrier mt pts
      1 ≤ ∑ i : Fin L,
        charge (G.ctxAt H (G.key (G.point H i.val)))
          (G.point H i.val) (pts.chal H (G.point H i.val))
          (H (G.point H i.val))) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ extract ω.1 ω.2 = none).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C +
        2 * (adaptiveNumerator fc tA (L + N) : ℚ) /
          Fintype.card D := by
  apply S.extraction_failure_ratio_le_two_potential codec₁ dec₁ check
    rootOf₁ claimOf₁ hcheck₁ codec₂ dec₂ rootOf₂ claimOf₂ hcheck₂
    pts charge hnonneg budget hbudget hlocal betaMax hbetaMax hmax
    slotBeta hslot hL ht hF hTM Acc extract hacc₁ hacc₂
  intro mt H ha he₁ he₂ hx
  exact S.charged_chain_of_verifier_chain pts hinputs charge hnonneg
    (fun mt H => Acc mt H ∧ S.Explains dec₁ rootOf₁ claimOf₁ mt H ∧
      S.Explains dec₂ rootOf₂ claimOf₂ mt H ∧ extract mt H = none)
    (fun mt H h => hpath mt H h.1 h.2.1 h.2.2.1 h.2.2.2)
    mt H ⟨ha, he₁, he₂, hx⟩

/-- Soundness follows from the extraction-failure theorem when every
extracted witness is valid.  The random-oracle and Merkle accounting is
entirely inherited from the extraction result. -/
theorem soundness_ratio_le_potential
    [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    {Witness : Type}
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2 * n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (pts : PrefixPoints Pt)
    (charge : (Key × List (Enc × D)) → (x : Pt) →
      (Fin (pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (budget : Pt → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (hlocal : ∀ κ x pref, ∑ c : C, charge κ x pref c ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ x, budget x ≤ betaMax)
    (slotBeta : Fin L → ℚ)
    (hslot : ∀ out i, budget (S.hashInput out i.val) ≤ slotBeta i)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc : (Fin TM → D) → (Pt → C) → Prop)
    (extract : (Fin TM → D) → (Pt → C) → Option Witness)
    (Good : (Fin TM → D) → (Pt → C) → Witness → Prop)
    (hvalid : ∀ mt H w, extract mt H = some w → Good mt H w)
    (Fails : (Fin TM → D) → (Pt → C) → Prop)
    (hfalse : ∀ mt H, Fails mt H → ∀ w, ¬ Good mt H w)
    (hacc : ∀ mt H, Acc mt H → S.MerkleAccepts codec check rootOf claimOf mt H)
    (hchain : ∀ mt H, Acc mt H → S.Explains dec rootOf claimOf mt H →
      extract mt H = none →
      1 ≤ ∑ x : Pt, if (S.potentialCarrier mt pts).Charged x H then
        charge ((S.potentialCarrier mt pts).ctxAt H
          ((S.potentialCarrier mt pts).key x)) x
          (pts.chal H x) (H x) else 0) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C +
        (adaptiveNumerator fc tA (L + N) : ℚ) / Fintype.card D := by
  classical
  have hsub : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2) ⊆
      (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ extract ω.1 ω.2 = none) := by
    intro ω hω
    obtain ⟨hacc', hf⟩ := (Finset.mem_filter.mp hω).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc', ?_⟩
    cases hx : extract ω.1 ω.2 with
    | none => rfl
    | some w => exact False.elim ((hfalse _ _ hf w) (hvalid _ _ w hx))
  have hden : 0 ≤ (Fintype.card D : ℚ) ^ TM *
      (Fintype.card C : ℚ) ^ Fintype.card Pt := by positivity
  have hcard :
      ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) ≤
      ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ extract ω.1 ω.2 = none).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine le_trans (div_le_div_of_nonneg_right hcard hden) ?_
  exact S.extraction_failure_ratio_le_potential codec dec check rootOf claimOf
    hcheck pts charge hnonneg budget hbudget hlocal betaMax hbetaMax hmax
    slotBeta hslot hL ht hF hTM Acc extract hacc hchain

/-- Two-opening soundness is a corollary of the extraction-failure theorem.
This is the interface for the two-field Longfellow protocol. -/
theorem soundness_ratio_le_two_potential
    [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    {Witness : Type}
    (codec₁ : Codec Salt M D Enc) (dec₁ : RoleDecoders codec₁)
    (check : Out → Tree Enc D Unit fc) (rootOf₁ : Key → D)
    (claimOf₁ : Out → OpeningClaim n Salt M D)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n (claimOf₁ out).I (claimOf₁ out).a
          (claimOf₁ out).pf (2 * n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    {Salt₂ M₂ : Type} [Inhabited Salt₂] [Inhabited M₂] {n₂ : ℕ}
    (codec₂ : Codec Salt₂ M₂ D Enc) (dec₂ : RoleDecoders codec₂)
    (rootOf₂ : Key → D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a
          (claimOf₂ out).pf (2 * n₂) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (pts : PrefixPoints Pt)
    (charge : (Key × List (Enc × D)) → (x : Pt) →
      (Fin (pts.slot x) → C) → C → ℚ)
    (hnonneg : ∀ κ x pref c, 0 ≤ charge κ x pref c)
    (budget : Pt → ℚ) (hbudget : ∀ x, 0 ≤ budget x)
    (hlocal : ∀ κ x pref, ∑ c : C, charge κ x pref c ≤ budget x)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ x, budget x ≤ betaMax)
    (slotBeta : Fin L → ℚ)
    (hslot : ∀ out i, budget (S.hashInput out i.val) ≤ slotBeta i)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc : (Fin TM → D) → (Pt → C) → Prop)
    (extract : (Fin TM → D) → (Pt → C) → Option Witness)
    (Good : (Fin TM → D) → (Pt → C) → Witness → Prop)
    (hvalid : ∀ mt H w, extract mt H = some w → Good mt H w)
    (Fails : (Fin TM → D) → (Pt → C) → Prop)
    (hfalse : ∀ mt H, Fails mt H → ∀ w, ¬ Good mt H w)
    (hacc₁ : ∀ mt H, Acc mt H →
      S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ mt H)
    (hacc₂ : ∀ mt H, Acc mt H →
      S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ mt H)
    (hchain : ∀ mt H, Acc mt H →
      S.Explains dec₁ rootOf₁ claimOf₁ mt H →
      S.Explains dec₂ rootOf₂ claimOf₂ mt H →
      extract mt H = none →
      1 ≤ ∑ x : Pt, if (S.potentialCarrier mt pts).Charged x H then
        charge ((S.potentialCarrier mt pts).ctxAt H
          ((S.potentialCarrier mt pts).key x)) x
          (pts.chal H x) (H x) else 0) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C +
        2 * (adaptiveNumerator fc tA (L + N) : ℚ) /
          Fintype.card D := by
  classical
  have hsub : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ Fails ω.1 ω.2) ⊆
      (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      Acc ω.1 ω.2 ∧ extract ω.1 ω.2 = none) := by
    intro ω hω
    obtain ⟨hacc', hf⟩ := (Finset.mem_filter.mp hω).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc', ?_⟩
    cases hx : extract ω.1 ω.2 with
    | none => rfl
    | some w => exact False.elim ((hfalse _ _ hf w) (hvalid _ _ w hx))
  have hden : 0 ≤ (Fintype.card D : ℚ) ^ TM *
      (Fintype.card C : ℚ) ^ Fintype.card Pt := by positivity
  have hcard :
      ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) ≤
      ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ extract ω.1 ω.2 = none).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine le_trans (div_le_div_of_nonneg_right hcard hden) ?_
  exact S.extraction_failure_ratio_le_two_potential codec₁ dec₁ check rootOf₁ claimOf₁
    hcheck₁ codec₂ dec₂ rootOf₂ claimOf₂ hcheck₂ pts charge hnonneg
    budget hbudget hlocal betaMax hbetaMax hmax slotBeta hslot
    hL ht hF hTM Acc extract hacc₁ hacc₂ hchain

end Bcs.TotalOracleCommit.Setup
