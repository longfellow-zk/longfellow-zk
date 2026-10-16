import Lfzk.FlatV7Deployed
import Lfzk.SoundnessAudit
import Lfzk.CompiledZkProfileSepMac
import Lfzk.GradedCircuitV7

/-!
# V7 hash1 Fiat–Shamir extraction at 116 bits

The zero-query branch uses the enlarged-radius flat extractor from
`FlatV7Deployed`.  The positive-query branch uses the existing graded
compiler on the deployed radius.  Both branches bound the same enlarged-
radius extraction-failure event, with circuit MAC rows supplied at every
satisfying assignment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.CompiledZk.FlatV7Headline

open Lfzk.CertifiedV1 Lfzk.NizkZk Lfzk.RbrZkSplit

theorem v7Hash1_zeroQuery_rhs_le_116
    {D : Type} [Fintype D]
    (hD : Fintype.card D = 2 ^ 256)
    (tA : ℕ) (htA : tA ≤ 2 ^ 116) :
    (4 : ℚ) / 2 ^ 128 +
      ((v7Hash1.cardCand : ℚ) * zkFieldDensity v7Hash1 3 +
        (1 : ℚ) / 2 ^ 125) +
      zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
      2 * ((Bcs.AdaptiveCommit.adaptiveNumerator
        (2 * v7SigHahn.params.row.n + 2 * v7Hash1.params.row.n) tA
        (1 + Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds +
          Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds) : ℚ) /
        Fintype.card D) ≤
      (1 + tA : ℚ) / 2 ^ 116 := by
  have h := Lfzk.SoundnessAudit.flat125_twofield_116_zero_query
    ⟨0, by decide⟩ tA htA
  change (v7Hash1.cardCand : ℚ) * zkFieldDensity v7Hash1 3 +
      (1 : ℚ) / 2 ^ 125 + zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
      (4 : ℚ) / 2 ^ 128 +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator
        (2 * v7Hash1.params.row.n + 2 * v7SigHahn.params.row.n) tA
        (1 + Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds +
          Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds) : ℚ) /
        2 ^ 256 ≤ (1 + tA : ℚ) / 2 ^ 116 at h
  rw [hD]
  rw [Nat.add_comm (2 * v7SigHahn.params.row.n)
    (2 * v7Hash1.params.row.n)]
  convert h using 1
  ring

/-- The earlier per-round positive-query compiler also meets the 116-bit
target for the hash1/signature pair. The circuit headline below uses the
graded extraction-first compiler. -/
theorem v7Hash1_positiveQuery_rhs_le_116
    (N tA : ℕ) (hN : 0 < N) (htA : tA ≤ 2 ^ 116) :
    zkCoreAt v7Hash1 3 v7Hash1.cardCand +
      zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
      (4 : ℚ) / 2 ^ 128 +
      N * max (max (v7Hash1.zkCoefficient 3)
        (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) +
      2 * ((Bcs.AdaptiveCommit.adaptiveNumerator
        (2 * v7Hash1.params.row.n + 2 * v7SigHahn.params.row.n) tA
        (Lfzk.NizkAdaptiveTwoField.len2 v7Hash1 v7SigHahn + N) : ℚ) /
        2 ^ 256) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  have h := Lfzk.SoundnessAudit.hahn_twofield_116_of_pos_queries_extended
    ⟨0, by decide⟩ N tA hN htA
  change zkCoreAt v7Hash1 3 v7Hash1.cardCand +
      zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
      (4 : ℚ) / 2 ^ 128 +
      N * max (max (v7Hash1.zkCoefficient 3)
        (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator
        (2 * v7Hash1.params.row.n + 2 * v7SigHahn.params.row.n) tA
        (Lfzk.NizkAdaptiveTwoField.len2 v7Hash1 v7SigHahn + N) : ℚ) /
        2 ^ 256 ≤
      (1 + N + tA : ℚ) / 2 ^ 116 at h
  convert h using 1
  ring

end Lfzk.CompiledZk.FlatV7Headline

namespace Lfzk.CompiledZk.FlatV7Headline

open Finset Merkle.MH Lfzk.CompiledZk Lfzk.CertifiedV1
  Lfzk.NizkDeployedHashTwoField Lfzk.CompiledZk.FlatV7Deployed
open Lfzk.CompiledLongfellow (Col)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2)
open Lfzk.NizkAdaptiveTwoField (check2)
open scoped Classical

variable {C D Enc X Out Salt₁ Salt₂ : Type}
  [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype D] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
  [Fintype X] [Inhabited Salt₁] [Inhabited Salt₂]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {F₁ Msg₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁]
  [SumcheckInterp F₁] [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁]
variable {M₁ nt₁ nlin₁ : ℕ}
variable {codec₁ : Codec Salt₁ (Col F₁ v7Hash1.params.nw v7Hash1.params.nq) D Enc}
  {dec₁ : RoleDecoders codec₁}
variable {F₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂]
  [DecidableEq F₂] [SumcheckInterp F₂] [DecidableEq Msg₂]
  [Inhabited Msg₂] [Fintype Msg₂]
variable {M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ : ℕ}
variable {codec₂ : Codec Salt₂ (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
  {dec₂ : RoleDecoders codec₂}

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- The earlier positive-query two-field compiler bounds the deployed
flat extraction-failure event at 116 bits.  The flat event is included in
the old-radius event, so this retains the compiler's existing query factor. -/
theorem v7Hash1_positiveQuery_deployed_extraction_116
    {nblk tA N TM : ℕ}
    (hN : 0 < N) (htA : tA ≤ 2 ^ 116)
    (hD : Fintype.card D = 2 ^ 256)
    (hC : Fintype.card C = 2 ^ 256)
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    (H : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F₁ v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin H.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : (Fin H.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : C => decode c = x).card ≤ 2 ^ 128)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (cands₂ : (D × D) × List (Enc × D) → Finset Witness₂)
    (hcard₂ : ∀ κ, (cands₂ κ).card ≤ v7SigHahn.cardCand)
    (hcands₂ : ∀ σ a, L₂.Good σ a → a ∈ cands₂ σ.1)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : Fin H.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      H.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₁ msgOf₁ claimOf₁ avOf pubOf (slice1 v7Hash1 v7SigHahn) mt ro →
      H.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₂ msgOf₂ claimOf₂ avOf pubOf (slice2 v7Hash1 v7SigHahn) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (htape : 2 * v7SigHahn.params.row.n +
      2 * v7Hash1.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    ((univ.filter fun ω : (Fin TM → D) ×
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds → C) =>
      v7Hash1_flatEvent H L₂ rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
        (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card
          (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
            v7Hash1.params.rounds v7SigHahn.params.rounds)) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
  have hmac : 2 ^ 128 * Fintype.card Fmac ≤ Fintype.card C := by
    rw [hFmac, hC]
    norm_num [← pow_add]
  have hcore := Lfzk.CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT_sep
    v7Hash1_valid v7SigHahn_valid
    v7Hash1_openings_pos v7SigHahn_openings_pos
    H.toSide L₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂
    (by simpa only [show v7Hash1.params.digestBits = 256 from rfl]
      using hD)
    (by simpa only [show v7SigHahn.params.digestBits = 256 from rfl]
      using hD)
    aP decode (2 ^ 128) hbal hmac tagOf common₁ common₂
    mac₁ mac₂ hcoll H.cands cands₂ H.cands_card_le hcard₂
    H.good_mem_cands hcands₂ hrow₁ hrow₂ htape hTM
  have hsubset := v7Hash1_flatEvent_ratio_le_old (TM := TM) H L₂ S
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    common₁ common₂ check
  have hnum := v7Hash1_positiveQuery_rhs_le_116 N tA hN htA
  calc
    _ ≤ _ := hsubset
    _ ≤ _ := by
      convert hcore using 1
      apply congrArg (fun s : Finset ((Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)) =>
          (s.card : ℚ) /
            ((Fintype.card D : ℚ) ^ TM *
              (Fintype.card C : ℚ) ^ Fintype.card
                (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
                  v7Hash1.params.rounds v7SigHahn.params.rounds)))
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [v7Hash1_oldEvent]
      rw [← H.toSide.acceptsDH_iff_tape S check rootOf₁ msgOf₁
        claimOf₁ avOf pubOf (slice1 v7Hash1 v7SigHahn) ω.1 ω.2,
        ← L₂.acceptsDH_iff_tape S check rootOf₂ msgOf₂
          claimOf₂ avOf pubOf (slice2 v7Hash1 v7SigHahn) ω.1 ω.2]
      rfl
    _ ≤ _ := by
      have hpair : v7Hash1.cardCand * v7SigHahn.cardCand = 4 := by decide
      have hpairQ : (v7Hash1.cardCand : ℚ) *
          (v7SigHahn.cardCand : ℚ) = 4 := by exact_mod_cast hpair
      rw [hFmac, hpairQ,
        show v7Hash1.params.digestBits = 256 from rfl,
        Nat.add_comm (2 * v7SigHahn.params.row.n)
          (2 * v7Hash1.params.row.n)]
      convert hnum using 1
      ring_nf

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- A single 116-bit extraction bound for every transcript-query budget.
The MAC rows are required for all satisfying candidates at the actual
public input; this is the circuit fact that supports both the zero-query
flat extractor and the positive-query deployed compiler. -/
theorem v7Hash1_deployed_fs_extraction_116
    [Nonempty X] {nblk tA N TM : ℕ}
    (htA : tA ≤ 2 ^ 116)
    (hD : Fintype.card D = 2 ^ 256)
    (hC : Fintype.card C = 2 ^ 256)
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    (H : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F₁ v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin H.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : (Fin H.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : C => decode c = x).card ≤ 2 ^ 128)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (cands₂ : (D × D) × List (Enc × D) → Finset Witness₂)
    (hcard₂ : ∀ κ, (cands₂ κ).card ≤ v7SigHahn.cardCand)
    (hcands₂ : ∀ σ a, L₂.Good σ a → a ∈ cands₂ σ.1)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : Fin H.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide H).Good
        (S.context mt ro, avOf out, pubOf out) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      L₂.Good (S.context mt ro, avOf out, pubOf out) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (htape : 2 * v7SigHahn.params.row.n +
      2 * v7Hash1.params.row.n + tA ≤ TM)
    (hTM : 0 < TM)
    (dummy : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
      v7Hash1.params.rounds v7SigHahn.params.rounds → C) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    ((univ.filter fun ω : (Fin TM → D) ×
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds → C) =>
      v7Hash1_flatEvent H L₂ rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
        (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card
          (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
            v7Hash1.params.rounds v7SigHahn.params.rounds)) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  by_cases hN : N = 0
  · subst N
    have hz := v7Hash1_zeroQuery_deployed_extraction_ratio_le
      H L₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      claimOf₁ claimOf₂ common₁ common₂ mac₁ mac₂ aP decode tagOf
      cands₂ hcard₂ hcands₂ hcoll hbal hC htape (by omega) dummy
      (by intro mt a; exact hrow₁ mt dummy a)
      (by intro mt a; exact hrow₂ mt dummy a)
    have hn := v7Hash1_zeroQuery_rhs_le_116 hD tA htA
    exact hz.trans (by simpa using hn)
  · have hp : 0 < N := Nat.pos_of_ne_zero hN
    apply v7Hash1_positiveQuery_deployed_extraction_116
      hp htA hD hC hFmac H L₂ body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ aP decode tagOf common₁ common₂
      mac₁ mac₂ hbal hcoll cands₂ hcard₂ hcands₂
    · intro mt ro a S hacc hg
      exact hrow₁ mt ro a
        (H.toZkSideAt_good_of_deployed
          (Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.v7Hash1_v1.certificate.e +
            Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.v7Hash1_v1.certificate.g)
          (by decide)
          (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flat_lift_card H)
          _ a hg)
    · intro mt ro a S hacc hg
      exact hrow₂ mt ro a hg
    · exact htape
    · exact hTM


omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- The 116-bit bound with MAC rows stated directly for every satisfying
circuit assignment.  Both analysis radii use the same circuit facts. -/
theorem v7Hash1_deployed_fs_extraction_116_circuit_bounded
    [Nonempty X] {nblk tA N TM : ℕ}
    (htA : tA ≤ 2 ^ 116)
    (hD : Fintype.card D = 2 ^ 256)
    (hC : Fintype.card C = 2 ^ 256)
    (_hFmac : Fintype.card Fmac = 2 ^ 128)
    (H : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F₁ v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin H.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (mac₁ : (Fin H.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin S₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : C => decode c = x).card ≤ 2 ^ 128)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (hrowSat₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : Fin H.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      H.c.Satisfied (H.pubIn (avOf out) (pubOf out)) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (hrowSat₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : (Fin S₂.c.ninp → F₂)),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      S₂.c.Satisfied (S₂.pubIn (avOf out) (pubOf out)) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (htape : 2 * v7SigHahn.params.row.n +
      2 * v7Hash1.params.row.n + tA ≤ TM)
    (hTM : 0 < TM)
    (dummy : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
      v7Hash1.params.rounds v7SigHahn.params.rounds → C) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    ((univ.filter fun ω : (Fin TM → D) ×
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds → C) =>
      v7Hash1_flatEvent H S₂.toSide rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
        (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card
          (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
            v7Hash1.params.rounds v7SigHahn.params.rounds)) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  by_cases hN : N = 0
  · subst N
    have hz := v7Hash1_zeroQuery_deployed_extraction_ratio_le
      H S₂.toSide body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      claimOf₁ claimOf₂ common₁ common₂ mac₁ mac₂ aP decode tagOf
      S₂.cands S₂.cands_card_le S₂.good_mem_cands hcoll hbal hC
      htape (by omega) dummy
      (by
        intro mt a S out σ hgood
        apply hrowSat₁ mt dummy a
        exact H.toZkSideAt_good_property
          (Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.v7Hash1_v1.certificate.e +
            Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.v7Hash1_v1.certificate.g)
          (by decide)
          (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flat_lift_card H)
          (fun σ a => H.c.Satisfied (H.pubIn σ.2.1 σ.2.2) a)
          (by intro σ a hs; exact hs) _ a hgood)
      (by
        intro mt a S out σ hgood
        apply hrowSat₂ mt dummy a
        exact S₂.toSide_good_property
          (fun σ a => S₂.c.Satisfied (S₂.pubIn σ.2.1 σ.2.2) a)
          (by intro σ a hs; exact hs) _ a hgood)
    have hn := v7Hash1_zeroQuery_rhs_le_116 hD tA htA
    exact hz.trans (by simpa using hn)
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    have hmac : 2 ^ 128 * 2 ^ 128 ≤ Fintype.card C := by
      rw [hC]
      norm_num [← pow_add]
    have hgraded := Lfzk.CompiledZkProfileRows.v7_circuit_potential_extraction_116_of_pos_queries
      (0 : Fin 4) hD hNpos H S₂ body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      aP decode (2 ^ 128) hbal hmac tagOf common₁ common₂
      mac₁ mac₂ hcoll
      (by
        intro mt ro a S hacc hgood
        apply hrowSat₁ mt ro a
        exact H.toSide_good_property
          (fun σ a => H.c.Satisfied (H.pubIn σ.2.1 σ.2.2) a)
          (by intro σ a hs; exact hs) _ a hgood)
      (by
        intro mt ro a S hacc hgood
        apply hrowSat₂ mt ro a
        exact S₂.toSide_good_property
          (fun σ a => S₂.c.Satisfied (S₂.pubIn σ.2.1 σ.2.2) a)
          (by intro σ a hs; exact hs) _ a hgood)
      htape hTM
    have hsubset := v7Hash1_flatEvent_ratio_le_old (TM := TM) H S₂.toSide S
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      common₁ common₂ check
    have hOldLe :
        ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
            v7Hash1.params.rounds v7SigHahn.params.rounds → C) =>
          v7Hash1_oldEvent H S₂.toSide rootOf₁ rootOf₂ avOf pubOf
            msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
            (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
            (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
          ((Fintype.card D : ℚ) ^ TM *
            (Fintype.card C : ℚ) ^ Fintype.card
              (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
                v7Hash1.params.rounds v7SigHahn.params.rounds)) ≤
        Lfzk.CompiledZkProfileRows.circuitExtractionFailureRatio (TM := TM) H S₂ body
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
          common₁ common₂ := by
      unfold Lfzk.CompiledZkProfileRows.circuitExtractionFailureRatio
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        dsimp only [v7Hash1_oldEvent] at hω
        rcases hω with ⟨ha, hb, hk, he⟩
        have ha' := (H.toSide.acceptsDH_iff_tape S check rootOf₁ msgOf₁
          claimOf₁ avOf pubOf (slice1 v7Hash1 v7SigHahn) ω.1 ω.2).2 ha
        have hb' := (S₂.toSide.acceptsDH_iff_tape S check rootOf₂ msgOf₂
          claimOf₂ avOf pubOf (slice2 v7Hash1 v7SigHahn) ω.1 ω.2).2 hb
        have hzero :
            S.challenges ω.1 ω.2 ⟨0, by omega⟩ =
              ω.2 (Sum.inl
                (rootOf₁ (S.proof ω.1 ω.2), rootOf₂ (S.proof ω.1 ω.2))) := by
          change ω.2 (Lfzk.NizkDeployedHashTwoField.hash2
            (C := C) (nl₁ := v7Hash1.params.nl)
            (nl₂ := v7SigHahn.params.nl)
            (w₁ := v7Hash1.params.rounds)
            (w₂ := v7SigHahn.params.rounds)
            rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
            (S.proof ω.1 ω.2) 0) = _
          rw [Lfzk.NizkDeployedHashTwoField.hash2_zero]
        have hex := (Lfzk.NizkZkDeployedHash.twoFieldExtract_none_iff
          H.toSide.toZkSide S₂.toSide.toZkSide common₁ common₂
          (sideCtx S avOf pubOf ω.1 ω.2)).2 he
        exact ⟨⟨ha', hb', hzero.symm.trans hk⟩, hex⟩)
    calc
      _ ≤ _ := hsubset
      _ ≤ _ := hOldLe
      _ ≤ _ := hgraded


omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- The uncapped 116-bit FS extraction theorem for the modeled v7 hash1
and Hahn signature circuit pair.  Above the useful Merkle-query range the
right-hand side is at least one. -/
theorem v7Hash1_deployed_fs_extraction_116_circuit
    [Nonempty X] {nblk tA N TM : ℕ}
    (hD : Fintype.card D = 2 ^ 256)
    (hC : Fintype.card C = 2 ^ 256)
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    (H : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F₁ v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin H.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (mac₁ : (Fin H.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin S₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : C => decode c = x).card ≤ 2 ^ 128)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (hrowSat₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : Fin H.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      H.c.Satisfied (H.pubIn (avOf out) (pubOf out)) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (hrowSat₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : (Fin S₂.c.ninp → F₂)),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      S₂.c.Satisfied (S₂.pubIn (avOf out) (pubOf out)) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (htape : 2 * v7SigHahn.params.row.n +
      2 * v7Hash1.params.row.n + tA ≤ TM)
    (hTM : 0 < TM)
    (dummy : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
      v7Hash1.params.rounds v7SigHahn.params.rounds → C) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    ((univ.filter fun ω : (Fin TM → D) ×
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds → C) =>
      v7Hash1_flatEvent H S₂.toSide rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
        (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card
          (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
            v7Hash1.params.rounds v7SigHahn.params.rounds)) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  by_cases hcut : tA ≤ 2 ^ 116
  · exact v7Hash1_deployed_fs_extraction_116_circuit_bounded
      hcut hD hC hFmac H S₂ body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ aP decode tagOf common₁ common₂
      mac₁ mac₂ hbal hcoll hrowSat₁ hrowSat₂ htape hTM dummy
  · calc
      _ ≤ (1 : ℚ) := Lfzk.TSec.ratio_le_one _
      _ ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
        have hn : 2 ^ 116 ≤ tA := by omega
        have hq : (2 ^ 116 : ℚ) ≤ (tA : ℚ) := by exact_mod_cast hn
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [show (0 : ℚ) ≤ N by positivity]


omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- False-statement soundness follows from the response-assisted extractor:
acceptance is charged only when no satisfying pair of circuit witnesses
has the same common value. -/
theorem v7Hash1_deployed_fs_false_statement_116
    [Nonempty X] {nblk tA N TM : ℕ}
    (hD : Fintype.card D = 2 ^ 256)
    (hC : Fintype.card C = 2 ^ 256)
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    (H : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F₁ v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin H.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (mac₁ : (Fin H.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin S₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : C => decode c = x).card ≤ 2 ^ 128)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (hrowSat₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : Fin H.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      H.c.Satisfied (H.pubIn (avOf out) (pubOf out)) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (hrowSat₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : (Fin S₂.c.ninp → F₂)),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      S₂.c.Satisfied (S₂.pubIn (avOf out) (pubOf out)) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (htape : 2 * v7SigHahn.params.row.n +
      2 * v7Hash1.params.row.n + tA ≤ TM)
    (hTM : 0 < TM)
    (dummy : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
      v7Hash1.params.rounds v7SigHahn.params.rounds → C) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    ((univ.filter fun ω : (Fin TM → D) ×
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds → C) =>
      H.toSide.acceptsTape rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 v7Hash1 v7SigHahn) (S.merkleOracle check ω.1 ω.2)
        (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2) ∧
      S₂.toSide.acceptsTape rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 v7Hash1 v7SigHahn) (S.merkleOracle check ω.1 ω.2)
        (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2) ∧
      S.challenges ω.1 ω.2 ⟨0, by omega⟩ = avOf (S.proof ω.1 ω.2) ∧
      ¬ ∃ a₁ a₂,
        H.c.Satisfied (H.pubIn (avOf (S.proof ω.1 ω.2))
          (pubOf (S.proof ω.1 ω.2))) a₁ ∧
        S₂.c.Satisfied (S₂.pubIn (avOf (S.proof ω.1 ω.2))
          (pubOf (S.proof ω.1 ω.2))) a₂ ∧
        common₁ a₁ = common₂ a₂).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card
          (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
            v7Hash1.params.rounds v7SigHahn.params.rounds)) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
  have hcore := v7Hash1_deployed_fs_extraction_116_circuit
    hD hC hFmac H S₂ body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ claimOf₁ claimOf₂ aP decode tagOf common₁ common₂
    mac₁ mac₂ hbal hcoll hrowSat₁ hrowSat₂ htape hTM dummy
  let P : (Fin TM → D) ×
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds → C) → Prop := fun ω =>
    H.toSide.acceptsTape rootOf₁ msgOf₁ claimOf₁ avOf pubOf
      (slice1 v7Hash1 v7SigHahn) (S.merkleOracle check ω.1 ω.2)
      (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2) ∧
    S₂.toSide.acceptsTape rootOf₂ msgOf₂ claimOf₂ avOf pubOf
      (slice2 v7Hash1 v7SigHahn) (S.merkleOracle check ω.1 ω.2)
      (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2) ∧
    S.challenges ω.1 ω.2 ⟨0, by omega⟩ = avOf (S.proof ω.1 ω.2) ∧
    ¬ ∃ a₁ a₂,
      H.c.Satisfied (H.pubIn (avOf (S.proof ω.1 ω.2))
        (pubOf (S.proof ω.1 ω.2))) a₁ ∧
      S₂.c.Satisfied (S₂.pubIn (avOf (S.proof ω.1 ω.2))
        (pubOf (S.proof ω.1 ω.2))) a₂ ∧
      common₁ a₁ = common₂ a₂
  let Q : (Fin TM → D) ×
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds → C) → Prop := fun ω =>
    v7Hash1_flatEvent H S₂.toSide rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
      (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
      (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)
  have hsub : univ.filter P ⊆ univ.filter Q := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    dsimp only [P] at hω
    dsimp only [Q, v7Hash1_flatEvent]
    rcases hω with ⟨hacc₁, hacc₂, hkey, hfalse⟩
    refine ⟨hacc₁, hacc₂, hkey, ?_⟩
    intro ⟨a₁, a₂, hg₁, hg₂, heq⟩
    apply hfalse
    refine ⟨a₁, a₂, ?_, ?_, heq⟩
    · exact H.toZkSideAt_good_property
        (Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.v7Hash1_v1.certificate.e +
          Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.v7Hash1_v1.certificate.g)
        (by decide) (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flat_lift_card H)
        (fun σ a => H.c.Satisfied (H.pubIn σ.2.1 σ.2.2) a)
        (by intro σ a hs; exact hs) _ a₁ hg₁
    · exact S₂.toSide_good_property
        (fun σ a => S₂.c.Satisfied (S₂.pubIn σ.2.1 σ.2.2) a)
        (by intro σ a hs; exact hs) _ a₂ hg₂
  have hcard : ((univ.filter P).card : ℚ) ≤ ((univ.filter Q).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  apply le_trans ?_ hcore
  exact div_le_div_of_nonneg_right hcard (by positivity)


end Lfzk.CompiledZk.FlatV7Headline
