import Lfzk.NizkZkTwoField
import Lfzk.CompiledZkRows
import Lfzk.TwoFieldV7Rows

/-!
# Two-field Longfellow at the deployed zero-knowledge verifiers

`Lfzk.NizkZkTwoField.twofield_zk_adaptive_ratio_le` at two **deployed** zero-knowledge sides: each
side's acceptance is `CompiledZkSide.accepts` — its transcript, at its slice of the merged tape,
builds a system with the side's code at the hashed MAC key and the public data (the code's public
binding reads them), and its Merkle-compiled V1 check accepts on the encoded system — and its
`hright` is a theorem (`CompiledZkSide.hright`, the two-field twin of `CompiledZk.hright_zk`).  The
Ligero halves are built from Ligero V1 at the extracted matrices (`ZkLigeroV1.exists_zkLigeroData`):
no `hfalse`.

```text
Pr[ both deployed verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · tape · (1 + L₁ + L₂ + N) / 2^digestBits        twofield_zk_compiled_ratio_le
```

`Lfzk.CompiledZkTwoFieldRows` instantiates it at the deployed v7 pairs (`v7Sig` with `logv = 8` and
`v7HashK`) and at `p256sha` (v8):

| pair | headline |
|---|---|
| `v7P256Sha1` … `v7P256Sha4` | `2^-115 + N · 2^-117` |
| `p256sha` (v8) | `2^-115 + N · 2^-116` |

## What is still a hypothesis

Per side, the `CompiledZkSide` data: the code, a placement, the analysis data (honest values and
pending-assertion predicate, the boundary facts, the layer-0 count — `CompiledZk`'s docstring) with
exactly balanced decoders; the MAC data
and the MAC rows `hrow₁`, `hrow₂` (a good witness of an accepting side satisfies the MAC at the
hashed multiplier, the same private `keyB`, and the proof's tag). The shared private blind is
stronger than Rust's two separate private `mac_ap` witnesses (v8 blinds; v7 multiplier shares);
see `Lfzk.TwoField` for the unresolved
composition obligation. Other premises are `|D|`, `|Fmac|`, the Merkle
budget.  The transliteration debt is `CompiledZk`'s.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZk

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1
  Lfzk.CompiledLongfellow Lfzk.CompiledLongfellowAdaptive Lfzk.NizkAdaptiveTwoField
  Lfzk.NizkZkTwoField Lfzk.CertifiedV1 Lfzk.Mac
open scoped Classical

/-! ## 1. A side's acceptance at its slice of the merged tape -/

section SideAccept

variable {C F X Q Msg Gpt : Type} [Field F] [SumcheckInterp F] [DecidableEq Q]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable {Out Statement Resp : Type}
variable {Enc D Salt Pt Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N L TM TC fc : ℕ}
variable {Oracle Mc : Type} {Opening : Q → Type} {n : ℕ}

/-- **The deployed zero-knowledge verifier of one side, at its slice `sl` of the merged tape**,
with the code read from the proof and the recomputed answers (`Vof`). -/
def AcceptsZkAt (K : Compiler Statement Oracle X Resp Q Opening Mc n)
    (Vof : Out → (Fin L → C) → ZkCode C F X Q Msg Gpt M ninp logw logc)
    (codec : Codec Salt Mc D Enc) (S : Setup Enc D Pt C Out Key tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D) (stmtOf : LigeroSystem ninp M F → Statement)
    (respOf : Msg → Resp) (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C)
    (mt : Fin TM → D) (ct : Fin TC → C) : Prop :=
  ∃ sys, zkBuilt (nl := nl) (w := w) (Vof (S.proof mt ct) (S.challenges mt ct))
      (msgOf (S.proof mt ct)) (sl (S.challenges mt ct)) = some sys ∧
    K.Accepts (codec.withOracle (S.merkleOracle check mt ct)) (stmtOf sys) (rootOf (S.proof mt ct))
      ((Vof (S.proof mt ct) (S.challenges mt ct)).decodeChal (sl (S.challenges mt ct) ligIdx))
      (respOf (msgOf (S.proof mt ct) (Rounds.Role.layerBase w nl + 2)))
      ((Vof (S.proof mt ct) (S.challenges mt ct)).decodeQuery (sl (S.challenges mt ct) qryIdx))
      (claimOf (S.proof mt ct))

/-- The statement for `guarded K` at a slice. -/
noncomputable def zkStatementOfAt (Vof : Out → (Fin L → C) → ZkCode C F X Q Msg Gpt M ninp logw logc)
    (msgOf : Out → ℕ → Msg) (stmtOf : LigeroSystem ninp M F → Statement)
    (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C) (out : Out) (chals : Fin L → C) :
    Statement × Bool :=
  (stmtOf ((zkBuilt (nl := nl) (w := w) (Vof out chals) (msgOf out) (sl chals)).getD emptySys),
    (zkBuilt (nl := nl) (w := w) (Vof out chals) (msgOf out) (sl chals)).isSome)

/-- The verifier's Ligero challenge at a slice. -/
def zkChallengeOfAt (Vof : Out → (Fin L → C) → ZkCode C F X Q Msg Gpt M ninp logw logc)
    (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C) (out : Out) (chals : Fin L → C) : X :=
  (Vof out chals).decodeChal (sl chals ligIdx)

/-- The verifier's Ligero query at a slice. -/
def zkQueryOfAt (Vof : Out → (Fin L → C) → ZkCode C F X Q Msg Gpt M ninp logw logc)
    (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C) (out : Out) (chals : Fin L → C) : Q :=
  (Vof out chals).decodeQuery (sl chals qryIdx)

omit [DecidableEq Q] in
/-- **`AcceptsZkAt` is `guarded K`'s joint acceptance** at the side's maps. -/
theorem acceptsZkAt_iff_joint (K : Compiler Statement Oracle X Resp Q Opening Mc n)
    (Vof : Out → (Fin L → C) → ZkCode C F X Q Msg Gpt M ninp logw logc)
    (codec : Codec Salt Mc D Enc) (S : Setup Enc D Pt C Out Key tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D) (stmtOf : LigeroSystem ninp M F → Statement)
    (respOf : Msg → Resp) (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C)
    (mt : Fin TM → D) (ct : Fin TC → C) :
    AcceptsZkAt (nl := nl) (w := w) K Vof codec S check rootOf msgOf claimOf stmtOf respOf sl
        mt ct ↔
      JointAccepts (guarded K) codec S check rootOf claimOf
        (zkStatementOfAt (nl := nl) (w := w) Vof msgOf stmtOf sl) (responseOfAt nl w respOf msgOf)
        (zkChallengeOfAt (nl := nl) (w := w) Vof sl) (zkQueryOfAt (nl := nl) (w := w) Vof sl)
        mt ct := by
  unfold JointAccepts AcceptsZkAt zkStatementOfAt
  rw [accepts_guarded]
  constructor
  · rintro ⟨sys, hs, hacc⟩
    rw [hs]
    exact ⟨rfl, hacc⟩
  · rintro ⟨hb, hacc⟩
    rcases hs : zkBuilt (nl := nl) (w := w) (Vof (S.proof mt ct) (S.challenges mt ct))
      (msgOf (S.proof mt ct)) (sl (S.challenges mt ct)) with _ | sys
    · rw [hs] at hb; exact absurd hb (by simp)
    · rw [hs] at hacc
      exact ⟨sys, rfl, hacc⟩

end SideAccept

/-! ## 2. A deployed zero-knowledge side -/

section Side

/-- The lift list of a side's extracted matrix, at a side context. -/
abbrev sideLift {R : Lfzk.CertifiedV1.Row} (hR : R.Valid) (hr : 0 < R.params.row.openings) (nlin nt : ℕ)
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {C X Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (rootOfKey : D × D → D) (σ : Sig D C X Enc) : Type :=
  ZkLigeroV1.Lift (CertifiedV1.Row.rowValid hR) dom (CertifiedV1.Row.hkrow hR)
    (extOracle nlin nt (CertifiedV1.Row.rowValid hR) dom (CertifiedV1.Row.hkrow hR) hr dec
      (rootOfKey σ.1.1, σ.1.2))

/--
**One side at the deployed zero-knowledge verifier**: the verifier's data (a placement, the
domain, the code at each MAC-key answer and public datum `Vc c₀ pub`, the response reader) and the
analysis data per side context (honest values, candidates' witnesses, satisfaction, field data with
exactly balanced decoders).  The candidates are the side's extracted matrix's lift list.
-/
structure CompiledZkSide (R : Lfzk.CertifiedV1.Row) (hR : R.Valid) (hr : 0 < R.params.row.openings) (logv : ℕ)
    (C : Type) [Fintype C] (F Msg Witness : Type) [Field F] [Fintype F] [DecidableEq F]
    [SumcheckInterp F] (M ninp nt nlin logw logc : ℕ) {Enc D Salt : Type} [Inhabited D]
    [DecidableEq D] [DecidableEq Enc] [Inhabited Salt] (X : Type)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (rootOfKey : D × D → D) where
  /-- The placement of the built system into the tableau. -/
  pl : Encode.Placement ninp M R.params.q R.params.nw R.params.nq nt
  /-- The code's evaluation domain. -/
  dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n
  /-- The verifier's zero-knowledge code at the MAC-key answer and the public data. -/
  Vc : C → X → ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
    (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M ninp logw logc
  hnlin : ∀ c x, (Vc c x).nlin = nlin
  hnt : ∀ c x, (Vc c x).nt = nt
  /-- How a message carries the side's Ligero response. -/
  respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1
  /-- The honest values. -/
  H : ∀ σ : Sig D C X Enc, ZkHonest F (sideLift hR hr nlin nt dom dec rootOfKey σ) logw logc
  /-- The candidates' witnesses. -/
  wit : ∀ σ : Sig D C X Enc, sideLift hR hr nlin nt dom dec rootOfKey σ → Witness
  /-- Which candidates satisfy the side's circuit. -/
  Sat : ∀ σ : Sig D C X Enc, sideLift hR hr nlin nt dom dec rootOfKey σ → Prop
  /-- The field half. -/
  FD : ∀ σ : Sig D C X Enc, ZkFieldData C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
    (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F)
    (sideLift hR hr nlin nt dom dec rootOfKey σ) M ninp logw logc R.params.nl R.params.rounds
    (Vc σ.2.1 σ.2.2) (H σ) (asgOf pl) (Sat σ)
  hexact : ∀ σ, (FD σ).ExactAt
  hF : Fintype.card F = R.params.row.fieldSize

namespace CompiledZkSide

variable {R : Lfzk.CertifiedV1.Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C] {F Msg Witness : Type} [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [DecidableEq Msg] [Inhabited Msg]
variable {M ninp nt nlin logw logc : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {X : Type} {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}
variable (L : CompiledZkSide R hR hr logv C F Msg Witness M ninp nt nlin logw logc X dec rootOfKey)

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- The Ligero half at a side context, from `ZkLigeroV1.exists_zkLigeroData`. -/
theorem exists_LD (σ : Sig D C X Enc) :
    ∃ LD : ZkLigeroData C (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
        (LigeroV1LayerStep.Qry R.params.row) Msg (L.Vc σ.2.1 σ.2.2)
        (asgOf L.pl (h := CertifiedV1.Row.rowValid hR) (D := L.dom) (hkrow := CertifiedV1.Row.hkrow hR)
          (O := extOracle nlin nt (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) hr dec
            (rootOfKey σ.1.1, σ.1.2))),
      LD.accepting = accZ (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) L.pl nlin
        (extOracle nlin nt (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) hr dec
          (rootOfKey σ.1.1, σ.1.2)) L.respOf ∧
      (∀ sys, Fits (L.Vc σ.2.1 σ.2.2) sys →
        NoSat (asgOf L.pl (h := CertifiedV1.Row.rowValid hR) (D := L.dom)
          (hkrow := CertifiedV1.Row.hkrow hR)
          (O := extOracle nlin nt (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) hr dec
            (rootOfKey σ.1.1, σ.1.2))) sys →
        ((LD.escaping sys).card : ℚ) ≤ (R.params.row.fail + R.params.row.arith)
          * Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)) ∧
      LD.bq = LigeroV1LayerStep.queryCount R.params.row :=
  exists_zkLigeroData (L.Vc σ.2.1 σ.2.2) (L.hnlin _ _) (L.hnt _ _) L.pl
    (CertifiedV1.Row.rowValid hR) (CertifiedV1.Row.coreRows hR) L.hF L.dom
    (CertifiedV1.Row.hkrow hR) _ L.respOf

/-- The chosen Ligero half. -/
noncomputable def LD (σ : Sig D C X Enc) :=
  Classical.choose (L.exists_LD σ)

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
theorem LD_acc (σ : Sig D C X Enc) :
    (L.LD σ).accepting = accZ (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) L.pl nlin
      (extOracle nlin nt (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) hr dec
        (rootOfKey σ.1.1, σ.1.2)) L.respOf :=
  (Classical.choose_spec (L.exists_LD σ)).1

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
theorem LD_esc (σ : Sig D C X Enc) :
    ∀ sys, Fits (L.Vc σ.2.1 σ.2.2) sys →
      NoSat (asgOf L.pl (h := CertifiedV1.Row.rowValid hR) (D := L.dom)
        (hkrow := CertifiedV1.Row.hkrow hR)
        (O := extOracle nlin nt (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) hr dec
          (rootOfKey σ.1.1, σ.1.2))) sys →
      (((L.LD σ).escaping sys).card : ℚ) ≤ (R.params.row.fail + R.params.row.arith)
        * Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt) :=
  (Classical.choose_spec (L.exists_LD σ)).2.1

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
theorem LD_bq (σ : Sig D C X Enc) : (L.LD σ).bq = LigeroV1LayerStep.queryCount R.params.row :=
  (Classical.choose_spec (L.exists_LD σ)).2.2

/-- **The `ZkSide` the deployed side is.** -/
noncomputable def toZkSide :
    ZkSide R logv (Sig D C X Enc) C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg Witness M ninp logw logc where
  V σ := L.Vc σ.2.1 σ.2.2
  Lift σ := sideLift hR hr nlin nt L.dom dec rootOfKey σ
  fin _ := inferInstance
  hcand _ := (lift_card_le (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) _).trans_eq
    (CertifiedV1.Row.cand_eq hR).symm
  H := L.H
  asg _ := asgOf L.pl
  wit := L.wit
  Sat := L.Sat
  FD := L.FD
  hexact := L.hexact
  LD := L.LD
  hesc := L.LD_esc
  hbq σ := (L.LD_bq σ).le
  hQ := by simp [LigeroV1LayerStep.Qry]

/-- A good witness of the side. -/
def Good (σ : Sig D C X Enc) (a : Witness) : Prop :=
  ∃ ℓ : sideLift hR hr nlin nt L.dom dec rootOfKey σ, L.Sat σ ℓ ∧ L.wit σ ℓ = a

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
theorem toZkSide_good (σ : Sig D C X Enc) (a : Witness) :
    L.toZkSide.Good σ a ↔ L.Good σ a := Iff.rfl

variable {Out : Type} {Pt : Type} [DecidableEq Pt] {tA N Lsch fc TM TC : ℕ}

/-- The side's code on a joint execution: at the raw key answer (slot `0`) and the public data. -/
def Vof (pubOf : Out → X) (hL : 0 < Lsch) (out : Out) (chals : Fin Lsch → C) :
    ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M ninp logw logc :=
  L.Vc (chals ⟨0, hL⟩) (pubOf out)

/-- **The side's deployed verifier on the joint execution**, at its slice `sl`. -/
def accepts (S : Setup Enc D Pt C Out (D × D) tA N Lsch) (check : Out → Tree Enc D Unit fc)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (pubOf : Out → X) (hL : 0 < Lsch)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ct : Fin TC → C) : Prop :=
  AcceptsZkAt (nl := R.params.nl) (w := R.params.rounds)
    (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (CertifiedV1.Row.rowValid hR) L.dom
      (CertifiedV1.Row.hkrow hR) hr)
    (L.Vof pubOf hL) codec S check rootOf msgOf claimOf (stmtOf L.pl nlin) L.respOf sl mt ct

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/--
**`hright`, proved for one deployed zero-knowledge side**: from the guarded joint acceptance at the
side's maps and the cut-trace extraction at the side's root, the side's zero-knowledge LayerStep
accepts at its slice of the recomputed answers.
-/
theorem hright (S : Setup Enc D Pt C Out (D × D) tA N Lsch) (check : Out → Tree Enc D Unit fc)
    (rootOf : Out → D) (hroot : ∀ out, rootOfKey (S.keyOut out) = rootOf out)
    (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (pubOf : Out → X) (hL : 0 < Lsch)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ct : Fin TC → C)
    (hacc : JointAccepts (guarded (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) hr)) codec S check
      rootOf claimOf
      (zkStatementOfAt (nl := R.params.nl) (w := R.params.rounds) (L.Vof pubOf hL) msgOf
        (stmtOf L.pl nlin) sl)
      (responseOfAt R.params.nl R.params.rounds L.respOf msgOf)
      (zkChallengeOfAt (nl := R.params.nl) (w := R.params.rounds) (L.Vof pubOf hL) sl)
      (zkQueryOfAt (nl := R.params.nl) (w := R.params.rounds) (L.Vof pubOf hL) sl) mt ct)
    (hexp : S.Explains dec rootOfKey claimOf mt ct) :
    ZkLayerStepAccepts .accepted .start
      (steps (nl := R.params.nl) (w := R.params.rounds)
        (L.toZkSide.V (sideCtx S pubOf hL mt ct)) (L.toZkSide.LD (sideCtx S pubOf hL mt ct))
        (msgOf (S.proof mt ct)))
      (sl (S.challenges mt ct)) := by
  rw [← acceptsZkAt_iff_joint] at hacc
  obtain ⟨sys, hsys, hv1⟩ := hacc
  obtain ⟨e, hext, hagree, -⟩ := hexp
  show ZkLayerStepAccepts .accepted .start (zkSteps _ _ _ _ _) _
  rw [zkAccepts_iff]
  refine ⟨sys, hsys, ?_⟩
  show _ ∈ (L.LD (sideCtx S pubOf hL mt ct)).accepting _ _ _ _ _
  rw [L.LD_acc]
  rw [← hroot (S.proof mt ct)] at hv1
  exact mem_acceptingR_of_accepts (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR)
    hr dec _ _ _ _ _ _ _ _ e hext hagree hv1

end CompiledZkSide

end Side

/-! ## 3. Two deployed zero-knowledge sides -/

section Compose

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] {M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ : ℕ}
variable {F₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] {M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at the deployed zero-knowledge verifiers, against one re-committing
Fiat–Shamir prover with a hashed MAC key.**

`NizkZkTwoField.twofield_zk_adaptive_ratio_le` at two `CompiledZkSide`s, `hright` discharged by
`CompiledZkSide.hright` and the Ligero halves built from V1 (no `hfalse`, no `hlig`).  Each side's
acceptance is `CompiledZkSide.accepts`: its transcript, at its slice of the recomputed answers,
builds a system, and its Merkle-compiled V1 check accepts the proof's response on the encoded
system.

```text
Pr[ both deployed verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · tape · (len2 + N) / 2^digestBits
```

**Every premise:** per side a `CompiledZkSide` (the code, placement, domain, response reader, the
analysis data with exactly balanced decoders, `|F|`), `|D|`, the MAC data `aP`, `decode`, `hbal`,
`hmac`, the MAC rows `hrow₁`, `hrow₂` (`assert_mac`), and the instance's numbers.
-/
theorem twofield_zk_compiled_ratio_le {R₁ R₂ : Lfzk.CertifiedV1.Row} (h₁ : R₁.Valid)
    (h₂ : R₂.Valid) (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ Witness₁ M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledZkSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ Witness₂ M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos R₁ R₂) (slice1 R₁ R₂) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos R₁ R₂) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos R₁ R₂⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos R₁ R₂) (slice2 R₁ R₂) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos R₁ R₂) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos R₁ R₂⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel)
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ R₁.tape)
    (htape₂ : R₁.tape = R₂.tape) :
    ((univ.filter fun ω : (Fin R₁.tape → D) × (Fin (len2 R₁ R₂ + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
            (len2_pos R₁ R₂) (slice1 R₁ R₂) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
            (len2_pos R₁ R₂) (slice2 R₁ R₂) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos R₁ R₂) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos R₁ R₂) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ (len2 R₁ R₂ + N))
      ≤ R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  have hroot₁ : ∀ out, Prod.fst ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, Prod.snd ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₂ out := fun _ => rfl
  have key₁ : ∀ ω : (Fin R₁.tape → D) × (Fin (len2 R₁ R₂ + N) → C),
      L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
          (len2_pos R₁ R₂) (slice1 R₁ R₂) ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin₁ ⊕ (Fin nt₁ × Encode.QSide))
            (CertifiedV1.Row.rowValid h₁) L₁.dom (CertifiedV1.Row.hkrow h₁) hr₁)) codec₁
          (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
          (zkStatementOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.Vof pubOf (len2_pos R₁ R₂)) msgOf₁ (stmtOf L₁.pl nlin₁) (slice1 R₁ R₂))
          (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
          (zkChallengeOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.Vof pubOf (len2_pos R₁ R₂)) (slice1 R₁ R₂))
          (zkQueryOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.Vof pubOf (len2_pos R₁ R₂)) (slice1 R₁ R₂)) ω.1 ω.2 :=
    fun ω => acceptsZkAt_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _
  have key₂ : ∀ ω : (Fin R₁.tape → D) × (Fin (len2 R₁ R₂ + N) → C),
      L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
          (len2_pos R₁ R₂) (slice2 R₁ R₂) ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin₂ ⊕ (Fin nt₂ × Encode.QSide))
            (CertifiedV1.Row.rowValid h₂) L₂.dom (CertifiedV1.Row.hkrow h₂) hr₂)) codec₂
          (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
          (zkStatementOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.Vof pubOf (len2_pos R₁ R₂)) msgOf₂ (stmtOf L₂.pl nlin₂) (slice2 R₁ R₂))
          (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
          (zkChallengeOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.Vof pubOf (len2_pos R₁ R₂)) (slice2 R₁ R₂))
          (zkQueryOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.Vof pubOf (len2_pos R₁ R₂)) (slice2 R₁ R₂)) ω.1 ω.2 :=
    fun ω => acceptsZkAt_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _
  refine le_trans (le_of_eq ?_)
    (twofield_zk_adaptive_ratio_le h₁ dec₁ dec₂
      (guarded (v1K (Equations := Fin nlin₁ ⊕ (Fin nt₁ × Encode.QSide))
        (CertifiedV1.Row.rowValid h₁) L₁.dom (CertifiedV1.Row.hkrow h₁) hr₁))
      (guarded (v1K (Equations := Fin nlin₂ ⊕ (Fin nt₂ × Encode.QSide))
        (CertifiedV1.Row.rowValid h₂) L₂.dom (CertifiedV1.Row.hkrow h₂) hr₂))
      body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      (zkStatementOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.Vof pubOf (len2_pos R₁ R₂)) msgOf₁ (stmtOf L₁.pl nlin₁) (slice1 R₁ R₂))
      (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
      (zkChallengeOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.Vof pubOf (len2_pos R₁ R₂)) (slice1 R₁ R₂))
      (zkQueryOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.Vof pubOf (len2_pos R₁ R₂)) (slice1 R₁ R₂))
      (zkStatementOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.Vof pubOf (len2_pos R₁ R₂)) msgOf₂ (stmtOf L₂.pl nlin₂) (slice2 R₁ R₂))
      (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
      (zkChallengeOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.Vof pubOf (len2_pos R₁ R₂)) (slice2 R₁ R₂))
      (zkQueryOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.Vof pubOf (len2_pos R₁ R₂)) (slice2 R₁ R₂))
      L₁.toZkSide L₂.toZkSide L₁.hF L₂.hF hD₁ hD₂ aP decode kmac hbal hmac keyB tagOf
      common₁ common₂
      (fun mt ct hacc hexp => L₁.hright _ _ rootOf₁ hroot₁ msgOf₁ claimOf₁ pubOf
        (len2_pos R₁ R₂) (slice1 R₁ R₂) mt ct hacc hexp)
      (fun mt ct hacc hexp => L₂.hright _ _ rootOf₂ hroot₂ msgOf₂ claimOf₂ pubOf
        (len2_pos R₁ R₂) (slice2 R₁ R₂) mt ct hacc hexp)
      (fun mt ct a hacc hgood => hrow₁ mt ct a ((key₁ (mt, ct)).mpr hacc) hgood)
      (fun mt ct a hacc hgood => hrow₂ mt ct a ((key₂ (mt, ct)).mpr hacc) hgood)
      htA₁ htA₂ htape htape₂)
  exact congrArg (fun t : Finset ((Fin R₁.tape → D) × (Fin (len2 R₁ R₂ + N) → C)) =>
      ((t.card : ℕ) : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ (len2 R₁ R₂ + N)))
    (Finset.filter_congr fun ω _ => and_congr (key₁ ω) (and_congr_left' (key₂ ω)))

end Compose

end Lfzk.CompiledZk
