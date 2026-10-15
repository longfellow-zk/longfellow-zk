import Lfzk.CertifiedHahn
import Lfzk.TSec

/-!
# The v7 signature circuit: 127-bit T-security with the Hahn/Delsarte mask row

This has the same protocol geometry, verifier, and circuit hypotheses as the original signature
headline. Only the analysis row (and therefore the extractor's radius) changes. The decoder and
transliteration assumptions remain explicit. The two-field proof is still limited by its hash side.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZkProfileRows

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
  RbrLongfellow Lfzk.NizkDeployedHash Lfzk.NizkDeployedHashAdaptive Lfzk.RbrZkLongfellow
  Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1 Lfzk.CompiledZk Lfzk.CertifiedV1
  Lfzk.CompiledZkDeployedHash Lfzk.Arith Lfzk.ZkArithProfile Lfzk.ZkArithInit
  Lfzk.NizkZkDeployedHash
open Lfzk.CompiledLongfellow (Col v1K)
open scoped Classical

open Lfzk.TSec

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/-- **The v7 signature circuit is 127-bit T-secure in the stated oracle model.**
The Hahn/Delsarte mask certificate is connected through the RBR classifier to the compiled
verifier and the concrete circuit arithmetization; the Merkle-query budget is unrestricted. -/
theorem v7SigHahn_zk_circuit_tsec (c : QuadCircuit F) (hnl : c.nl = v7SigHahn.params.nl) {L TM : ℕ}
    (hwf : WellFormedP c 8 v7SigHahn.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7SigHahn.params.q v7SigHahn.params.nw v7SigHahn.params.nq nt)
    {codec : Codec Salt (Col F v7SigHahn.params.nw v7SigHahn.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7SigHahn.params.nw v7SigHahn.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7SigHahn.params.row) Msg (Fin 8 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7SigHahn.params.row.openings v7SigHahn.params.q
      v7SigHahn.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7SigHahn.params.row.openings v7SigHahn.params.q
      v7SigHahn.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7SigHahn.params.nl v7SigHahn.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7SigHahn.params.row.n Salt (Col F v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (hF : Fintype.card F = v7SigHahn.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 8 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7SigHahn.params.nw v7SigHahn.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7SigHahn.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (8 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7SigHahn.params.nw v7SigHahn.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7SigHahn.params.row) ≤ Fintype.card C)
    (htape : 2 * v7SigHahn.params.row.n + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2 ^ v7SigHahn.params.digestBits) :
    ((univ.filter fun ω : (Fin TM → D) × (MPoint D Msg v7SigHahn.params.nl v7SigHahn.params.rounds → C) =>
        AcceptsZkDH (nl := v7SigHahn.params.nl) (w := v7SigHahn.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7SigHahn_valid) dom
              (Row.hkrow v7SigHahn_valid) v7SigHahn_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7SigHahn_valid) dom (Row.hkrow v7SigHahn_valid)
              (extOracle nlin nt (Row.rowValid v7SigHahn_valid) dom (Row.hkrow v7SigHahn_valid)
                v7SigHahn_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7SigHahn.params.nl v7SigHahn.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 127 := by
  have hp := row_zk_deployed_circuit_ratio_leT v7SigHahn_valid v7SigHahn_openings_pos 8
    c hnl hwf hiso hde pub pl dec V hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF
    kinit kpair k kchal kq hbalInit hbalPair hbalF hbalChal hbalQuery
    hkinit hkpair hk hkchal hkq htape hTM hD
  obtain ⟨hA, hK, hT⟩ := v7SigHahn_tsec_slack
  have h := Lfzk.TSec.tsec_of_linear_slack
    (k := 1) (δ := 1 / 2 ^ 256) (ε := 1 / 2 ^ 127) (G := 2 ^ 127)
    (A := zkCoreAt v7SigHahn 8 v7SigHahn.cardCand) (K := v7SigHahn.zkCoefficient 8)
    (fc := 2 * v7SigHahn.params.row.n)
    (L := Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds) (N := N) (tA := tA)
    (ratio_le_one _) (hp.trans_eq (by rw [show v7SigHahn.params.digestBits = 256 from rfl]; ring))
    (by positivity) (by norm_num) (by positivity)
    (by simpa only [one_mul, mul_one_div] using hA)
    (by simpa only [one_mul, mul_one_div] using hK)
    (by simpa only [one_mul, mul_one_div] using hT)
    (by norm_num)
  exact h.trans_eq (by ring)

end Lfzk.CompiledZkProfileRows
