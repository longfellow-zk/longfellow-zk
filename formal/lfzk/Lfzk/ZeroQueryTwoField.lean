import Bcs.FixedPathCommit
import Bcs.Counting
import Lfzk.NizkDeployedHashTwoField

/-!
# The deployed two-field verifier at zero transcript-oracle queries

Once the Merkle tape is fixed, a prover making no transcript-oracle query has
a fixed proof. The actual key, first-side, and second-side hash inputs are
pairwise distinct, so their answers have exactly the distribution of a fresh
interactive verifier tape. The identity below is independent of the event
chosen on that tape and is the sampling bridge for flat extraction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkDeployedHashTwoField

open Finset Bcs.TotalOracleCommit Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable {D C X Msg₁ Msg₂ Out Enc : Type}
  [Fintype D] [DecidableEq D] [Inhabited D]
  [Fintype C] [Nonempty C]
  [Fintype X]
  [Fintype Msg₁] [Inhabited Msg₁]
  [Fintype Msg₂] [Inhabited Msg₂]
  [DecidableEq Enc]
  {nl₁ nl₂ tA TM : ℕ} {w₁ w₂ : ℕ → ℕ}

/-- Exact reduction from the zero-query deployed FS experiment, conditional
on one Merkle tape, to an interactive uniform verifier tape. -/
theorem setup2_zeroQuery_challenges_ratio_eq
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out tA 0)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (mt : Fin TM → D)
    (dummy : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C)
    (E : Out →
      (Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C) → Prop) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    ((univ.filter fun H : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C =>
        E (S.proof mt H) (S.challenges mt H)).card : ℚ) /
        (Fintype.card C : ℚ) ^
          Fintype.card (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) =
      ((univ.filter fun tape : Fin
          (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C =>
        E (S.proof mt dummy) tape).card : ℚ) /
        (Fintype.card C : ℚ) ^
          (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) := by
  exact (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).zeroQuery_challenges_ratio_eq
    mt dummy (setup2_hashInput_injective body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂) E

/-- The fixed-path identity for the full deployed verifier event.  The event
may inspect the extracted commitment context and Merkle oracle as well as the
proof and all challenge answers; these objects are fixed by the Merkle tape
when the prover has made no transcript-oracle query. -/
theorem setup2_zeroQuery_verifierEvent_ratio_eq
    {fc : ℕ}
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out tA 0)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (check : Out → Tree Enc D Unit fc)
    (mt : Fin TM → D)
    (dummy : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C)
    (E : ((D × D) × List (Enc × D)) → (Enc → D) → Out →
      (Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C) → Prop) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    ((univ.filter fun H : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C =>
        E (S.context mt H) (S.merkleOracle check mt H)
          (S.proof mt H) (S.challenges mt H)).card : ℚ) /
        (Fintype.card C : ℚ) ^
          Fintype.card (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) =
      ((univ.filter fun tape : Fin
          (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C =>
        E (S.context mt dummy) (S.merkleOracle check mt dummy)
          (S.proof mt dummy) tape).card : ℚ) /
        (Fintype.card C : ℚ) ^
          (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) := by
  exact (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).zeroQuery_verifierEvent_ratio_eq
    check mt dummy (setup2_hashInput_injective body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂) E

/-- A bound proved for every fixed Merkle tape and a fresh interactive
key-and-two-side verifier tape holds for the deployed zero-query FS
experiment with exactly the same error. -/
theorem setup2_zeroQuery_verifierEvent_ratio_le
    {fc : ℕ}
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out tA 0)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (check : Out → Tree Enc D Unit fc)
    (dummy : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C)
    (E : ((D × D) × List (Enc × D)) → (Enc → D) → Out →
      (Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C) → Prop)
    (epsilon : ℚ)
    (hinteractive : ∀ mt : Fin TM → D,
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      ((univ.filter fun tape : Fin
          (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C =>
        E (S.context mt dummy) (S.merkleOracle check mt dummy)
          (S.proof mt dummy) tape).card : ℚ) /
        (Fintype.card C : ℚ) ^
          (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) ≤
        epsilon) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C) =>
        E (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
          (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^
          Fintype.card (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂)) ≤ epsilon := by
  have h := (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).zeroQuery_verifierEvent_ratio_le
    check dummy (setup2_hashInput_injective body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂) E epsilon hinteractive
  simpa only [Fintype.card_prod, Fintype.card_fun, Nat.cast_mul, Nat.cast_pow,
    Fintype.card_fin] using h

/-- At zero transcript-oracle queries the deployed verifier admits three
independent answer blocks: the shared key, side one, and side two.  A
deterministic extraction-failure cover by these three events transfers to
the full Fiat--Shamir experiment with exactly their summed error. -/
theorem setup2_zeroQuery_threeBlock_verifierEvent_ratio_le
    {fc : ℕ}
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out tA 0)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (check : Out → Tree Enc D Unit fc)
    (dummy : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C)
    (E : ((D × D) × List (Enc × D)) → (Enc → D) → Out →
      (Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C) → Prop)
    (keyBad : (Fin TM → D) → C → Prop)
    (side₁Bad : (Fin TM → D) → C →
      (Fin (Rounds.Role.length nl₁ w₁) → C) → Prop)
    (side₂Bad : (Fin TM → D) → C →
      (Fin (Rounds.Role.length nl₂ w₂) → C) → Prop)
    (keyBound side₁Bound side₂Bound : ℚ)
    (hcover : ∀ (mt : Fin TM → D)
      (tape : Fin (1 + Rounds.Role.length nl₁ w₁ +
        Rounds.Role.length nl₂ w₂) → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      E (S.context mt dummy) (S.merkleOracle check mt dummy)
        (S.proof mt dummy) tape →
      let p := Bcs.threeBlockTapeEquiv C
        (Rounds.Role.length nl₁ w₁) (Rounds.Role.length nl₂ w₂) tape
      keyBad mt p.1 ∨ side₁Bad mt p.1 p.2.1 ∨ side₂Bad mt p.1 p.2.2)
    (hkey : ∀ mt, ((univ.filter (keyBad mt)).card : ℚ) /
      Fintype.card C ≤ keyBound)
    (hside₁ : ∀ mt key, ((univ.filter (side₁Bad mt key)).card : ℚ) /
      Fintype.card (Fin (Rounds.Role.length nl₁ w₁) → C) ≤ side₁Bound)
    (hside₂ : ∀ mt key, ((univ.filter (side₂Bad mt key)).card : ℚ) /
      Fintype.card (Fin (Rounds.Role.length nl₂ w₂) → C) ≤ side₂Bound) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C) =>
        E (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
          (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^
          Fintype.card (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂)) ≤
      keyBound + side₁Bound + side₂Bound := by
  classical
  apply setup2_zeroQuery_verifierEvent_ratio_le body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ check dummy E (keyBound + side₁Bound + side₂Bound)
  intro mt
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    (Bcs.three_block_tape_ratio_le
    (fun tape =>
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      E (S.context mt dummy) (S.merkleOracle check mt dummy)
        (S.proof mt dummy) tape)
    (keyBad mt) (side₁Bad mt) (side₂Bad mt)
    keyBound side₁Bound side₂Bound (hcover mt) (hkey mt)
    (hside₁ mt) (hside₂ mt))

/-- A fixed-tape extraction bound on the two explained Merkle paths transfers
to the actual zero-query two-field FS verifier.  The only additional charge
is the two ordinary Merkle explanation failures; no challenge-counting term
is introduced by this transfer. -/
theorem setup2_zeroQuery_good_plus_merkle_ratio_le
    {Salt₁ M₁ Salt₂ M₂ : Type}
    [Inhabited Salt₁] [Inhabited M₁]
    [Inhabited Salt₂] [Inhabited M₂]
    {n₁ n₂ fc : ℕ}
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out tA 0)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (codec₁ : Codec Salt₁ M₁ D Enc) (dec₁ : RoleDecoders codec₁)
    (codec₂ : Codec Salt₂ M₂ D Enc) (dec₂ : RoleDecoders codec₂)
    (check : Out → Tree Enc D Unit fc)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D)
    (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I
          (claimOf₁ out).a (claimOf₁ out).pf (2 * n₁)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I
          (claimOf₂ out).a (claimOf₂ out).pf (2 * n₂)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hL : 0 < 1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂)
    (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (dummy : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C)
    (E : ((D × D) × List (Enc × D)) → (Enc → D) → Out →
      (Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C) → Prop)
    (productEvent : (Fin TM → D) → C ×
      ((Fin (Rounds.Role.length nl₁ w₁) → C) ×
       (Fin (Rounds.Role.length nl₂ w₂) → C)) → Prop)
    (epsilon : ℚ)
    (haccept₁ : ∀ (mt : Fin TM → D)
      (H : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      E (S.context mt H) (S.merkleOracle check mt H)
        (S.proof mt H) (S.challenges mt H) →
      S.MerkleAccepts codec₁ check Prod.fst claimOf₁ mt H)
    (haccept₂ : ∀ (mt : Fin TM → D)
      (H : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      E (S.context mt H) (S.merkleOracle check mt H)
        (S.proof mt H) (S.challenges mt H) →
      S.MerkleAccepts codec₂ check Prod.snd claimOf₂ mt H)
    (hcover : ∀ (mt : Fin TM → D)
      (ro : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      E (S.context mt ro) (S.merkleOracle check mt ro)
        (S.proof mt ro) (S.challenges mt ro) ∧
      S.Explains dec₁ Prod.fst claimOf₁ mt ro ∧
      S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      productEvent mt (Bcs.threeBlockTapeEquiv C
        (Rounds.Role.length nl₁ w₁) (Rounds.Role.length nl₂ w₂)
          (S.challenges mt ro)))
    (hproduct : ∀ mt : Fin TM → D,
      ((univ.filter (productEvent mt)).card : ℚ) /
        Fintype.card (C ×
          ((Fin (Rounds.Role.length nl₁ w₁) → C) ×
           (Fin (Rounds.Role.length nl₂ w₂) → C))) ≤ epsilon) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C) =>
        E (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
          (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^
          Fintype.card (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂)) ≤
      epsilon + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA
        (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) : ℚ) /
          Fintype.card D) := by
  have hgood : ∀ mt : Fin TM → D,
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      ((univ.filter fun tape : Fin
          (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C =>
        E (S.context mt dummy) (S.merkleOracle check mt dummy)
          (S.proof mt dummy) tape ∧
        S.Explains dec₁ Prod.fst claimOf₁ mt dummy ∧
        S.Explains dec₂ Prod.snd claimOf₂ mt dummy).card : ℚ) /
        (Fintype.card C : ℚ) ^
          (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) ≤
        epsilon := by
    intro mt
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    have hfixed (tape : Fin
        (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C)
        (he : E (S.context mt dummy) (S.merkleOracle check mt dummy)
          (S.proof mt dummy) tape ∧
          S.Explains dec₁ Prod.fst claimOf₁ mt dummy ∧
          S.Explains dec₂ Prod.snd claimOf₂ mt dummy) :
        productEvent mt (Bcs.threeBlockTapeEquiv C
          (Rounds.Role.length nl₁ w₁) (Rounds.Role.length nl₂ w₂) tape) := by
      let ro := S.oracleWithTape mt dummy
        (setup2_hashInput_injective body rootOf₁ rootOf₂ avOf pubOf
          msgOf₁ msgOf₂) tape
      have hevent := (S.zeroQuery_event_oracleWithTape_iff check mt dummy
        (setup2_hashInput_injective body rootOf₁ rootOf₂ avOf pubOf
          msgOf₁ msgOf₂) tape E).mpr he.1
      have hexp₁ := (S.zeroQuery_explains_iff dec₁ Prod.fst claimOf₁
        mt ro dummy).mpr he.2.1
      have hexp₂ := (S.zeroQuery_explains_iff dec₂ Prod.snd claimOf₂
        mt ro dummy).mpr he.2.2
      have hp := hcover mt ro ⟨hevent, hexp₁, hexp₂⟩
      change productEvent mt (Bcs.threeBlockTapeEquiv C
        (Rounds.Role.length nl₁ w₁) (Rounds.Role.length nl₂ w₂)
          (S.challenges mt ro)) at hp
      rw [S.oracleWithTape_challenges_eq mt dummy
        (setup2_hashInput_injective body rootOf₁ rootOf₂ avOf pubOf
          msgOf₁ msgOf₂) tape] at hp
      exact hp
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
      (Bcs.three_block_tape_ratio_le_of_product_bound
        (fun tape =>
          let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
          E (S.context mt dummy) (S.merkleOracle check mt dummy)
            (S.proof mt dummy) tape ∧
          S.Explains dec₁ Prod.fst claimOf₁ mt dummy ∧
          S.Explains dec₂ Prod.snd claimOf₂ mt dummy)
        (productEvent mt) epsilon hfixed (hproduct mt))
  have h := (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).zeroQuery_ratio_le_good_plus_merkle_two
    codec₁ dec₁ codec₂ dec₂ check Prod.fst Prod.snd claimOf₁ claimOf₂
    hcheck₁ hcheck₂ hL ht hF hTM dummy
    (setup2_hashInput_injective body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
    E epsilon haccept₁ haccept₂ (by
      intro mt
      convert hgood mt using 1)
  simpa only [Nat.add_zero] using h

end Lfzk.NizkDeployedHashTwoField
