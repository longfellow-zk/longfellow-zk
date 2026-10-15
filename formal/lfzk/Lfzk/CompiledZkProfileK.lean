import Lfzk.ZkVirtualCard
import Lfzk.CompiledZkProfileRows

/-!
# The deployed v7 pairs with decoders balanced up to a virtual card

`Lfzk.CompiledZkProfileRows`'s two-field headline takes each side as a `CircuitSide`, whose decoder
fields `hbal…`, `hk…` say the coin decoders are **exactly** balanced over the raw alphabet `C`.  On
the deployed alphabet — streams of AES blocks — that cannot hold
(`Lfzk.StreamDecoders.no_exact_decoder_odd`).  This file restates the chain with each side a
`CircuitSideK`: the same data, with the decoders balanced up to a virtual card `K`
(`kinit · |F|^(logv+2) ≤ K`, …), and proves

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  (K / |C|) · ( zkCore₁ + zkCore₂ + 1/|Fmac|
                      + N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|) )
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^digestBits
```

(`twofield_zk_deployed_ratio_leTK`), and its T-security form `twofield_tsecK`: when
`K / |C| ≤ 1 + 2^-40` the certified slack of every v7 pair still gives `(1 + tA + N) · 2^-115`
(`v7P256Sha{1,2,3,4}_slackK_bound`, `_slackK_coeff`, by `native_decide` on closed numerals).

The deployed verifier's event is the same as in `CompiledZkProfileRows` (`CircuitSideK.acceptsDH`
unfolds to the same `AcceptsZkAtDH` at the side's code, placement, domain and response reader).

## What is still a hypothesis

Those of `CompiledZkProfileRows.v7P256Sha{1..4}_zk_circuit_tsec` with the exact-balance fields
replaced by balance up to `K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZkProfileK

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk
  Lfzk.ZkLigeroV1 Lfzk.CompiledZk Lfzk.CertifiedV1 Lfzk.Arith Lfzk.ZkArithProfile
  Lfzk.ZkArithInit Lfzk.ZkVirtualCard Lfzk.CompiledZkDeployedHash Lfzk.NizkZkDeployedHash Lfzk.Mac
open Lfzk.CompiledLongfellow (Col guarded v1K)
open Lfzk.CompiledLongfellowAdaptive (Sig accepts_guarded responseOfAt mem_acceptingR_of_accepts
  slice1 slice2)
open Lfzk.NizkDeployedHashAdaptive (JointAccepts)
open Lfzk.NizkAdaptiveTwoField (check2 len2)
open Lfzk.NizkDeployedHashTwoField (Pt2 setup2 sideCtx)
open scoped Classical

/-! ## 1. A circuit side, decoders balanced up to `K` -/

/--
**A deployed zero-knowledge side from a circuit, its decoders balanced up to `K`**: the data of
`CompiledZk.CircuitSide`, with `hkinit … hkq` stated against `K` instead of `|C|`.
-/
structure CircuitSideK (R : Row) (hR : R.Valid) (hr : 0 < R.params.row.openings) (logv : ℕ)
    (C : Type) [Fintype C] (F Msg : Type) [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    (M nt nlin : ℕ) {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] (X : Type) {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
    (dec : RoleDecoders codec) (rootOfKey : D × D → D) (K : ℕ) where
  /-- The circuit, in the deployed format. -/
  c : QuadCircuit F
  hnl : c.nl = R.params.nl
  /-- The container dimension. -/
  L : ℕ
  hwf : WellFormedP c logv R.params.logw L
  hiso : c.Isolated
  hde : c.DeadEnd
  /-- The public input at the MAC-key share and the public data. -/
  pubIn : C → X → Fin c.ninp → F
  /-- The placement of the built system into the tableau. -/
  pl : Encode.Placement c.ninp M R.params.q R.params.nw R.params.nq nt
  /-- The code's evaluation domain. -/
  dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n
  /-- The verifier's code at the MAC-key share and the public data. -/
  Vc : C → X → ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
    (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M c.ninp L 0
  hnlin : ∀ a x, (Vc a x).nlin = nlin
  hnt : ∀ a x, (Vc a x).nt = nt
  hV : ∀ a x, CodeAgreesP c (pubIn a x) L (Vc a x)
  hst0 : ∀ a x G, ((Vc a x).st0 G).g0 = padG L G ∧ ((Vc a x).st0 G).g1 = padG L G
  /-- How a message carries the side's Ligero response. -/
  respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1
  /-- The decoders' preimage bounds. -/
  kinit : ℕ
  kpair : ℕ
  k : ℕ
  kchal : ℕ
  kq : ℕ
  hbalInit : ∀ a x (y : (Fin logv → F) × F × F),
    (univ.filter fun c' : C => (Vc a x).decodeInit c' = y).card ≤ kinit
  hbalPair : ∀ a x (y : F × F), (univ.filter fun c' : C => (Vc a x).decodePair c' = y).card ≤ kpair
  hbalF : ∀ a x (y : F), (univ.filter fun c' : C => (Vc a x).decodeF c' = y).card ≤ k
  hbalChal : ∀ a x (y : ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt),
    (univ.filter fun c' : C => (Vc a x).decodeChal c' = y).card ≤ kchal
  hbalQuery : ∀ a x (y : LigeroV1LayerStep.Qry R.params.row),
    (univ.filter fun c' : C => (Vc a x).decodeQuery c' = y).card ≤ kq
  /-- **Balance up to the virtual card `K`.** -/
  hkinit : kinit * Fintype.card F ^ (logv + 2) ≤ K
  hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ K
  hk : k * Fintype.card F ≤ K
  hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt) ≤ K
  hkq : kq * Fintype.card (LigeroV1LayerStep.Qry R.params.row) ≤ K
  hF : Fintype.card F = R.params.row.fieldSize

namespace CircuitSideK

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {X : Type} {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D} {K : ℕ}
variable (S : CircuitSideK R hR hr logv C F Msg M nt nlin X dec rootOfKey K)

/-- The honest values at a side context. -/
noncomputable def H (σ : Sig D C X Enc) :
    ZkHonest F (sideLift hR hr nlin nt S.dom dec rootOfKey σ) S.L 0 :=
  zkHonestP S.hwf (S.pubIn σ.2.1 σ.2.2) (fun ℓ => (asgOf S.pl ℓ).1)
    (cPendP S.c (S.pubIn σ.2.1 σ.2.2) S.L R.params.logw (fun ℓ => (asgOf S.pl ℓ).1))

/-- The field half at a side context (`ZkArithProfile.zkFieldDataP`). -/
noncomputable def FD (σ : Sig D C X Enc) :=
  zkFieldDataP S.hwf (S.pubIn σ.2.1 σ.2.2) S.hiso S.hde (S.Vc σ.2.1 σ.2.2) (S.hV _ _)
    (S.hst0 _ _) (fun ℓ : sideLift hR hr nlin nt S.dom dec rootOfKey σ => (asgOf S.pl ℓ).1)
    (asgOf S.pl) (fun _ _ _ => rfl) S.kinit S.kpair S.k S.kchal S.kq (S.hbalInit _ _)
    (S.hbalPair _ _) (S.hbalF _ _) (S.hbalChal _ _) (S.hbalQuery _ _) S.hnl

theorem FD_exactAtK (σ : Sig D C X Enc) : (S.FD σ).ExactAtK K :=
  ⟨le_rfl, S.hkinit, S.hkpair, S.hk, S.hkchal, S.hkq⟩

/-- The Ligero half at a side context, from `ZkLigeroV1.exists_zkLigeroData`. -/
theorem exists_LD (σ : Sig D C X Enc) :
    ∃ LD : ZkLigeroData C (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
        (LigeroV1LayerStep.Qry R.params.row) Msg (S.Vc σ.2.1 σ.2.2)
        (asgOf S.pl (h := CertifiedV1.Row.rowValid hR) (D := S.dom)
          (hkrow := CertifiedV1.Row.hkrow hR)
          (O := extOracle nlin nt (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR) hr
            dec (rootOfKey σ.1.1, σ.1.2))),
      LD.accepting = accZ (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR) S.pl nlin
        (extOracle nlin nt (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR) hr dec
          (rootOfKey σ.1.1, σ.1.2)) S.respOf ∧
      (∀ sys, Fits (S.Vc σ.2.1 σ.2.2) sys →
        NoSat (asgOf S.pl (h := CertifiedV1.Row.rowValid hR) (D := S.dom)
          (hkrow := CertifiedV1.Row.hkrow hR)
          (O := extOracle nlin nt (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR) hr
            dec (rootOfKey σ.1.1, σ.1.2))) sys →
        ((LD.escaping sys).card : ℚ) ≤ (R.params.row.fail + R.params.row.arith)
          * Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)) ∧
      LD.bq = LigeroV1LayerStep.queryCount R.params.row :=
  exists_zkLigeroData (S.Vc σ.2.1 σ.2.2) (S.hnlin _ _) (S.hnt _ _) S.pl
    (CertifiedV1.Row.rowValid hR) (CertifiedV1.Row.coreRows hR) S.hF S.dom
    (CertifiedV1.Row.hkrow hR) _ S.respOf

/-- The chosen Ligero half. -/
noncomputable def LD (σ : Sig D C X Enc) := Classical.choose (S.exists_LD σ)

theorem LD_acc (σ : Sig D C X Enc) :
    (S.LD σ).accepting = accZ (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR) S.pl
      nlin (extOracle nlin nt (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR) hr dec
        (rootOfKey σ.1.1, σ.1.2)) S.respOf :=
  (Classical.choose_spec (S.exists_LD σ)).1

theorem LD_esc (σ : Sig D C X Enc) :
    ∀ sys, Fits (S.Vc σ.2.1 σ.2.2) sys →
      NoSat (asgOf S.pl (h := CertifiedV1.Row.rowValid hR) (D := S.dom)
        (hkrow := CertifiedV1.Row.hkrow hR)
        (O := extOracle nlin nt (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR) hr
          dec (rootOfKey σ.1.1, σ.1.2))) sys →
      (((S.LD σ).escaping sys).card : ℚ) ≤ (R.params.row.fail + R.params.row.arith)
        * Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt) :=
  (Classical.choose_spec (S.exists_LD σ)).2.1

theorem LD_bq (σ : Sig D C X Enc) : (S.LD σ).bq = LigeroV1LayerStep.queryCount R.params.row :=
  (Classical.choose_spec (S.exists_LD σ)).2.2

/-- **The `ZkSideK` a circuit side is.** -/
noncomputable def toZkSideK :
    ZkSideK R logv (Sig D C X Enc) C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin S.c.ninp → F) M S.c.ninp S.L 0 K where
  V σ := S.Vc σ.2.1 σ.2.2
  Lift σ := sideLift hR hr nlin nt S.dom dec rootOfKey σ
  fin _ := inferInstance
  hcand _ := (lift_card_le (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR) _).trans_eq
    (CertifiedV1.Row.cand_eq hR).symm
  H := S.H
  asg _ := asgOf S.pl
  wit _ ℓ := (asgOf S.pl ℓ).1
  Sat σ ℓ := S.c.Satisfied (S.pubIn σ.2.1 σ.2.2) (asgOf S.pl ℓ).1
  FD := S.FD
  hexactK := S.FD_exactAtK
  LD := S.LD
  hesc := S.LD_esc
  hbq σ := (S.LD_bq σ).le
  hQ := by simp [LigeroV1LayerStep.Qry]

/-- **A good witness**: the committed witness of a lift-list member that satisfies the circuit at
the side's public input. -/
def Good (σ : Sig D C X Enc) (a : Fin S.c.ninp → F) : Prop :=
  ∃ ℓ : sideLift hR hr nlin nt S.dom dec rootOfKey σ,
    S.c.Satisfied (S.pubIn σ.2.1 σ.2.2) (asgOf S.pl ℓ).1 ∧ (asgOf S.pl ℓ).1 = a

theorem toZkSideK_good (σ : Sig D C X Enc) (a : Fin S.c.ninp → F) :
    S.toZkSideK.Good σ a ↔ S.Good σ a := Iff.rfl

variable {Out : Type} {Pt : Type} [DecidableEq Pt] {tA N Lsch fc TM : ℕ}

/-- The side's code on `(mt, ro)`: at the MAC-key share the proof carries and the public data. -/
def VofDH (avOf : Out → C) (pubOf : Out → X) (out : Out) (_chals : Fin Lsch → C) :
    ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M S.c.ninp S.L 0 :=
  S.Vc (avOf out) (pubOf out)

/-- **The side's deployed verifier on `(mt, ro)`**, at its slice `sl` of the verifier's challenges
(`CompiledZkSide.acceptsDH` at this side's data). -/
def acceptsDH (S' : TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N Lsch)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ro : Pt → C) : Prop :=
  AcceptsZkAtDH (nl := R.params.nl) (w := R.params.rounds)
    (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (CertifiedV1.Row.rowValid hR) S.dom
      (CertifiedV1.Row.hkrow hR) hr)
    (S.VofDH avOf pubOf) codec S' check rootOf msgOf claimOf (stmtOf S.pl nlin) S.respOf sl mt ro

/-- **`hright` for a circuit side against a prefix-only prover** (`CompiledZkSide.hrightDH`). -/
theorem hrightDH (S' : TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N Lsch)
    (check : Out → Tree Enc D Unit fc)
    (rootOf : Out → D) (hroot : ∀ out, rootOfKey (S'.keyOut out) = rootOf out)
    (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ro : Pt → C)
    (hacc : JointAccepts (guarded (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR) hr)) codec S' check
      rootOf claimOf
      (zkStatementOfAt (nl := R.params.nl) (w := R.params.rounds) (S.VofDH avOf pubOf) msgOf
        (stmtOf S.pl nlin) sl)
      (responseOfAt R.params.nl R.params.rounds S.respOf msgOf)
      (zkChallengeOfAt (nl := R.params.nl) (w := R.params.rounds) (S.VofDH avOf pubOf) sl)
      (zkQueryOfAt (nl := R.params.nl) (w := R.params.rounds) (S.VofDH avOf pubOf) sl) mt ro)
    (hexp : S'.Explains dec rootOfKey claimOf mt ro) :
    ZkLayerStepAccepts .accepted .start
      (steps (nl := R.params.nl) (w := R.params.rounds)
        (S.toZkSideK.V (sideCtx S' avOf pubOf mt ro)) (S.toZkSideK.LD (sideCtx S' avOf pubOf mt ro))
        (msgOf (S'.proof mt ro)))
      (sl (S'.challenges mt ro)) := by
  rw [← acceptsZkAtDH_iff_joint] at hacc
  obtain ⟨sys, hsys, hv1⟩ := hacc
  obtain ⟨e, hext, hagree, -⟩ := hexp
  show ZkLayerStepAccepts .accepted .start (zkSteps _ _ _ _ _) _
  rw [zkAccepts_iff]
  refine ⟨sys, hsys, ?_⟩
  show _ ∈ (S.LD (sideCtx S' avOf pubOf mt ro)).accepting _ _ _ _ _
  rw [S.LD_acc]
  rw [← hroot (S'.proof mt ro)] at hv1
  exact mem_acceptingR_of_accepts (CertifiedV1.Row.rowValid hR) S.dom (CertifiedV1.Row.hkrow hR)
    hr dec _ _ _ _ _ _ _ _ e hext hagree hv1

end CircuitSideK

/-! ## 2. Two circuit sides at the virtual card -/

section Compose

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ nt₁ nlin₁ : ℕ}
variable {F₂ Msg₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ nt₂ nlin₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at the deployed zero-knowledge verifiers, both sides from circuits, decoders
balanced up to a virtual card `K`**, against one re-committing prefix-only Fiat–Shamir prover, with
no bound on the prover's Merkle queries:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  (K / |C|) · ( zkCore₁ + zkCore₂ + 1/|Fmac|
                      + N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|) )
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^digestBits
```

`CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT`'s proof on `ZkVirtualCard`'s chain.
-/
theorem twofield_zk_deployed_ratio_leTK {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N TM : ℕ} (K : ℕ) (hKpos : 0 < K)
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (L₁ : CircuitSideK R₁ h₁ hr₁ logv₁ C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (L₂ : CircuitSideK R₂ h₂ hr₂ logv₂ C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin L₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin L₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Fin L₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 R₁ R₂) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Fin L₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 R₁ R₂) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 R₁ R₂) ω.1 ω.2 ∧
          L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 R₁ R₂) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ (K : ℚ) / (Fintype.card C : ℚ) * (zkCoreAt R₁ logv₁ R₁.cardCand
          + zkCoreAt R₂ logv₂ R₂.cardCand + 1 / (Fintype.card Fmac : ℚ)
          + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            (1 / (Fintype.card Fmac : ℚ)))
        + 2 * ((AdaptiveCommit.adaptiveNumerator (2 * R₂.params.row.n + 2 * R₁.params.row.n) tA
            (len2 R₁ R₂ + N) : ℚ) / 2 ^ R₁.params.digestBits) := by
  have hroot₁ : ∀ out, Prod.fst ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, Prod.snd ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₂ out := fun _ => rfl
  have key₁ : ∀ ω : (Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
          (slice1 R₁ R₂) ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin₁ ⊕ (Fin nt₁ × Encode.QSide))
            (Row.rowValid h₁) L₁.dom (Row.hkrow h₁) hr₁)) codec₁
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
          (zkStatementOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.VofDH avOf pubOf) msgOf₁ (stmtOf L₁.pl nlin₁) (slice1 R₁ R₂))
          (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
          (zkChallengeOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.VofDH avOf pubOf) (slice1 R₁ R₂))
          (zkQueryOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.VofDH avOf pubOf) (slice1 R₁ R₂)) ω.1 ω.2 :=
    fun ω => acceptsZkAtDH_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _
  have key₂ : ∀ ω : (Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
          (slice2 R₁ R₂) ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin₂ ⊕ (Fin nt₂ × Encode.QSide))
            (Row.rowValid h₂) L₂.dom (Row.hkrow h₂) hr₂)) codec₂
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
          (zkStatementOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.VofDH avOf pubOf) msgOf₂ (stmtOf L₂.pl nlin₂) (slice2 R₁ R₂))
          (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
          (zkChallengeOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.VofDH avOf pubOf) (slice2 R₁ R₂))
          (zkQueryOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.VofDH avOf pubOf) (slice2 R₁ R₂)) ω.1 ω.2 :=
    fun ω => acceptsZkAtDH_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _
  refine le_trans (le_of_eq ?_)
    (twofield_zk_deployed_adaptive_ratio_leTK h₁ K hKpos dec₁ dec₂
      (guarded (v1K (Equations := Fin nlin₁ ⊕ (Fin nt₁ × Encode.QSide))
        (Row.rowValid h₁) L₁.dom (Row.hkrow h₁) hr₁))
      (guarded (v1K (Equations := Fin nlin₂ ⊕ (Fin nt₂ × Encode.QSide))
        (Row.rowValid h₂) L₂.dom (Row.hkrow h₂) hr₂))
      body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      (zkStatementOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.VofDH avOf pubOf) msgOf₁ (stmtOf L₁.pl nlin₁) (slice1 R₁ R₂))
      (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
      (zkChallengeOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.VofDH avOf pubOf) (slice1 R₁ R₂))
      (zkQueryOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.VofDH avOf pubOf) (slice1 R₁ R₂))
      (zkStatementOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.VofDH avOf pubOf) msgOf₂ (stmtOf L₂.pl nlin₂) (slice2 R₁ R₂))
      (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
      (zkChallengeOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.VofDH avOf pubOf) (slice2 R₁ R₂))
      (zkQueryOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.VofDH avOf pubOf) (slice2 R₁ R₂))
      L₁.toZkSideK L₂.toZkSideK L₁.hF L₂.hF hD₁ hD₂ aP decode kmac hbal hmac keyB tagOf
      common₁ common₂
      (fun mt ro hacc hexp => L₁.hrightDH _ _ rootOf₁ hroot₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 R₁ R₂) mt ro hacc hexp)
      (fun mt ro hacc hexp => L₂.hrightDH _ _ rootOf₂ hroot₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 R₁ R₂) mt ro hacc hexp)
      (fun mt ro a hacc hgood => hrow₁ mt ro a ((key₁ (mt, ro)).mpr hacc) hgood)
      (fun mt ro a hacc hgood => hrow₂ mt ro a ((key₂ (mt, ro)).mpr hacc) hgood)
      htape hTM)
  congr 3
  ext ω
  simp only [mem_filter, mem_univ, true_and]
  exact and_congr (key₁ ω) (and_congr_left' (key₂ ω))

end Compose

/-! ## 3. T-security at the virtual card -/

section TSec

open Lfzk.TSec

/-- **T-security for two fields at a virtual card**: `twofield_tsec` with the field and Ligero
terms inflated by `lam = K / |C| ≤ lam₀`, from slack numerals that carry `lam₀`. -/
theorem twofield_tsecK {R₁ R₂ : Row} {l₁ l₂ a b fc tA N : ℕ} {p m lam lam₀ : ℚ} (hp1 : p ≤ 1)
    (hp : p ≤ lam * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m
        + N * max (max (R₁.zkCoefficient l₁) (R₂.zkCoefficient l₂)) m)
      + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA (len2 R₁ R₂ + N) : ℚ)
        / 2 ^ R₁.params.digestBits))
    (hm0 : 0 ≤ m) (hlam0 : 0 ≤ lam) (hlam : lam ≤ lam₀)
    (hsb : lam₀ * (R₂.zkBound l₂ + R₁.zkBound l₁ + m)
        + 2 * (((R₂.tape * len2 R₂ R₁ : ℕ) : ℚ) / 2 ^ R₂.params.digestBits) ≤ 1 / 2 ^ a)
    (hsc : lam₀ * max (max (R₂.zkCoefficient l₂) (R₁.zkCoefficient l₁)) m
        + 2 * ((R₂.tape : ℚ) / 2 ^ R₂.params.digestBits) ≤ 1 / 2 ^ b)
    (hab : a + 1 ≤ b) (hdg : R₁.params.digestBits = R₂.params.digestBits)
    (hT0 : 32 ≤ R₂.tape) (hfc : 2 * fc ≤ R₂.tape) (hd : 2 * a + 4 ≤ R₁.params.digestBits) :
    p ≤ (1 + N + tA) / 2 ^ a := by
  obtain ⟨hG, hGe⟩ := pow_facts hd
  have hδ : (0 : ℚ) ≤ 1 / 2 ^ R₁.params.digestBits := by positivity
  have hl : len2 R₂ R₁ = len2 R₁ R₂ := by unfold len2; omega
  rw [hl, ← hdg] at hsb
  rw [← hdg] at hsc
  have hb : (1 : ℚ) / 2 ^ b ≤ 1 / 2 ^ a / 2 := by
    rw [div_div, ← pow_succ]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hab)
  have hc₁ := zkCoreAt_le_zkBound R₁ l₁
  have hc₂ := zkCoreAt_le_zkBound R₂ l₂
  have hn₁ := zkCoreAt_nonneg R₁ l₁ R₁.cardCand
  have hn₂ := zkCoreAt_nonneg R₂ l₂ R₂.cardCand
  set MM := max (max (R₁.zkCoefficient l₁) (R₂.zkCoefficient l₂)) m with hMM
  have hMM0 : 0 ≤ MM := le_trans hm0 (le_max_right _ _)
  have hmax : max (max (R₂.zkCoefficient l₂) (R₁.zkCoefficient l₁)) m = MM := by
    rw [hMM, max_comm (R₁.zkCoefficient l₁)]
  rw [hmax] at hsc
  have hX0 : 0 ≤ zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m := by linarith
  have hA' : lam * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m)
      ≤ lam₀ * (R₂.zkBound l₂ + R₁.zkBound l₁ + m) := by
    calc lam * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m)
        ≤ lam₀ * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m) :=
          mul_le_mul_of_nonneg_right hlam hX0
      _ ≤ lam₀ * (R₂.zkBound l₂ + R₁.zkBound l₁ + m) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_trans hlam0 hlam)
  have hK' : lam * MM ≤ lam₀ * MM := mul_le_mul_of_nonneg_right hlam hMM0
  have key := tsec_of_uncapped (k := 2)
    (A := lam * (zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m))
    (K := lam * MM) (ε := 1 / 2 ^ a)
    (δ := 1 / 2 ^ R₁.params.digestBits) (fc := fc) (T0 := R₂.tape) (L := len2 R₁ R₂)
    (N := N) (tA := tA) (G := 2 ^ (R₁.params.digestBits - a - 4)) hp1
    (hp.trans_eq (by ring)) (mul_nonneg hlam0 hX0) (mul_nonneg hlam0 hMM0) hδ (by norm_num)
    (by norm_num)
    (by
      have : (2 : ℚ) * ((R₂.tape * len2 R₁ R₂ : ℕ) : ℚ) * (1 / 2 ^ R₁.params.digestBits)
          = 2 * (((R₂.tape * len2 R₁ R₂ : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by ring
      rw [this]; linarith)
    (by
      have : (2 : ℚ) * (R₂.tape : ℚ) * (1 / 2 ^ R₁.params.digestBits)
          = 2 * ((R₂.tape : ℚ) / 2 ^ R₁.params.digestBits) := by ring
      rw [this]; linarith)
    hG hGe hT0 hfc (by unfold len2; omega)
  exact key.trans_eq (by ring)

/-- The inflation every v7 numeral below carries: `lam₀ = 1 + 2^-40`. -/
def lam₀ : ℚ := 1 + 1 / 2 ^ 40

end TSec

open Lfzk.TwoFieldV1Rows

/-- `v7P256Sha1` at the zero-knowledge accounting (`logv = 8, 3`), inflated by `lam₀ = 1 + 2^-40`, at
`N = 0`: at most `2^-115`. -/
theorem v7P256Sha1_slackK_bound :
    lam₀ * (v7P256Sha1.ecdsa.zkBound 8 + v7P256Sha1.sha.zkBound 3 + 1 / (v7P256Sha1.macFieldSize : ℚ))
        + 2 * (((v7P256Sha1.ecdsa.tape * len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha1`'s worst zero-knowledge coefficient inflated by `lam₀`, plus the per-query term: at most
`2^-116`. -/
theorem v7P256Sha1_slackK_coeff :
    lam₀ * max (max (v7P256Sha1.ecdsa.zkCoefficient 8) (v7P256Sha1.sha.zkCoefficient 3))
        (1 / (v7P256Sha1.macFieldSize : ℚ))
      + 2 * ((v7P256Sha1.ecdsa.tape : ℚ) / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha2` at the zero-knowledge accounting (`logv = 8, 4`), inflated by `lam₀ = 1 + 2^-40`, at
`N = 0`: at most `2^-115`. -/
theorem v7P256Sha2_slackK_bound :
    lam₀ * (v7P256Sha2.ecdsa.zkBound 8 + v7P256Sha2.sha.zkBound 4 + 1 / (v7P256Sha2.macFieldSize : ℚ))
        + 2 * (((v7P256Sha2.ecdsa.tape * len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha2`'s worst zero-knowledge coefficient inflated by `lam₀`, plus the per-query term: at most
`2^-116`. -/
theorem v7P256Sha2_slackK_coeff :
    lam₀ * max (max (v7P256Sha2.ecdsa.zkCoefficient 8) (v7P256Sha2.sha.zkCoefficient 4))
        (1 / (v7P256Sha2.macFieldSize : ℚ))
      + 2 * ((v7P256Sha2.ecdsa.tape : ℚ) / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha3` at the zero-knowledge accounting (`logv = 8, 4`), inflated by `lam₀ = 1 + 2^-40`, at
`N = 0`: at most `2^-115`. -/
theorem v7P256Sha3_slackK_bound :
    lam₀ * (v7P256Sha3.ecdsa.zkBound 8 + v7P256Sha3.sha.zkBound 4 + 1 / (v7P256Sha3.macFieldSize : ℚ))
        + 2 * (((v7P256Sha3.ecdsa.tape * len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha3`'s worst zero-knowledge coefficient inflated by `lam₀`, plus the per-query term: at most
`2^-116`. -/
theorem v7P256Sha3_slackK_coeff :
    lam₀ * max (max (v7P256Sha3.ecdsa.zkCoefficient 8) (v7P256Sha3.sha.zkCoefficient 4))
        (1 / (v7P256Sha3.macFieldSize : ℚ))
      + 2 * ((v7P256Sha3.ecdsa.tape : ℚ) / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha4` at the zero-knowledge accounting (`logv = 8, 5`), inflated by `lam₀ = 1 + 2^-40`, at
`N = 0`: at most `2^-115`. -/
theorem v7P256Sha4_slackK_bound :
    lam₀ * (v7P256Sha4.ecdsa.zkBound 8 + v7P256Sha4.sha.zkBound 5 + 1 / (v7P256Sha4.macFieldSize : ℚ))
        + 2 * (((v7P256Sha4.ecdsa.tape * len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  unfold lam₀
  native_decide

/-- `v7P256Sha4`'s worst zero-knowledge coefficient inflated by `lam₀`, plus the per-query term: at most
`2^-116`. -/
theorem v7P256Sha4_slackK_coeff :
    lam₀ * max (max (v7P256Sha4.ecdsa.zkCoefficient 8) (v7P256Sha4.sha.zkCoefficient 5))
        (1 / (v7P256Sha4.macFieldSize : ℚ))
      + 2 * ((v7P256Sha4.ecdsa.tape : ℚ) / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  unfold lam₀
  native_decide

section V7PairsTSecK

open Lfzk.TSec

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ nt₁ nlin₁ : ℕ}
variable {F₂ Msg₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ nt₂ nlin₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha1`, decoders balanced up to a virtual card `K` with
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  `CompiledZkProfileRows.v7P256Sha1_zk_circuit_tsec`
with each side a `CircuitSideK` and the MAC decoder balanced up to `K`:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_zk_deployed_ratio_leTK` with `twofield_tsecK` and the slack numerals
`v7P256Sha1_slackK_bound`, `_slackK_coeff`.
-/
theorem v7P256Sha1_zk_circuit_tsecK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha1_valid
  have key := twofield_zk_deployed_ratio_leTK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha1_sha_openings_pos v7P256Sha1_ecdsa_openings_pos K hKpos S₁
    S₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM
  have hm : (1 : ℚ) / (v7P256Sha1.macFieldSize : ℚ) = 1 / (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha1_slackK_bound
  have hsc := v7P256Sha1_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha2`, decoders balanced up to a virtual card `K` with
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  `CompiledZkProfileRows.v7P256Sha2_zk_circuit_tsec`
with each side a `CircuitSideK` and the MAC decoder balanced up to `K`:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_zk_deployed_ratio_leTK` with `twofield_tsecK` and the slack numerals
`v7P256Sha2_slackK_bound`, `_slackK_coeff`.
-/
theorem v7P256Sha2_zk_circuit_tsecK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha2.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha2.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha2_valid
  have key := twofield_zk_deployed_ratio_leTK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha2_sha_openings_pos v7P256Sha2_ecdsa_openings_pos K hKpos S₁
    S₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM
  have hm : (1 : ℚ) / (v7P256Sha2.macFieldSize : ℚ) = 1 / (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha2_slackK_bound
  have hsc := v7P256Sha2_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha3`, decoders balanced up to a virtual card `K` with
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  `CompiledZkProfileRows.v7P256Sha3_zk_circuit_tsec`
with each side a `CircuitSideK` and the MAC decoder balanced up to `K`:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_zk_deployed_ratio_leTK` with `twofield_tsecK` and the slack numerals
`v7P256Sha3_slackK_bound`, `_slackK_coeff`.
-/
theorem v7P256Sha3_zk_circuit_tsecK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha3.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha3.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha3_valid
  have key := twofield_zk_deployed_ratio_leTK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha3_sha_openings_pos v7P256Sha3_ecdsa_openings_pos K hKpos S₁
    S₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM
  have hm : (1 : ℚ) / (v7P256Sha3.macFieldSize : ℚ) = 1 / (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha3_slackK_bound
  have hsc := v7P256Sha3_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha4`, decoders balanced up to a virtual card `K` with
`K / |C| ≤ 1 + 2^-40`, T-secure at `λ = 115`.**  `CompiledZkProfileRows.v7P256Sha4_zk_circuit_tsec`
with each side a `CircuitSideK` and the MAC decoder balanced up to `K`:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`twofield_zk_deployed_ratio_leTK` with `twofield_tsecK` and the slack numerals
`v7P256Sha4_slackK_bound`, `_slackK_coeff`.
-/
theorem v7P256Sha4_zk_circuit_tsecK {tA N TM K : ℕ} (hKpos : 0 < K)
    (hlam : (K : ℚ) / (Fintype.card C : ℚ) ≤ lam₀) (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSideK v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst K)
    (S₂ : CircuitSideK v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd K)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha4.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha4.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ K)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        S₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          S₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha4_valid
  have key := twofield_zk_deployed_ratio_leTK (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha4_sha_openings_pos v7P256Sha4_ecdsa_openings_pos K hKpos S₁
    S₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM
  have hm : (1 : ℚ) / (v7P256Sha4.macFieldSize : ℚ) = 1 / (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha4_slackK_bound
  have hsc := v7P256Sha4_slackK_coeff
  rw [hm] at hsb hsc
  exact twofield_tsecK (ratio_le_one _) (by convert key using 6) (by positivity) (by positivity)
    hlam hsb hsc (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide)
    (by decide)

end V7PairsTSecK

end Lfzk.CompiledZkProfileK
