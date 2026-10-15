import Lfzk.ZkArithProfile
import Lfzk.CompiledZkDeployedHashRows

/-!
# Longfellow at the deployed v7 rows, with the arithmetization constructed

The headlines of `Lfzk.CompiledZkDeployedHash` and `Lfzk.CompiledZkDeployedHashRows` — the deployed
zero-knowledge verifier, against a re-committing prefix-only Fiat–Shamir prover, at the deployed hash
inputs — take the field half of the analysis (`RbrZkSplit.ZkFieldData`, per context) as a premise.
This file discharges that premise from a **circuit in the deployed format at the row's width profile**
(`Lfzk.ZkArithProfile.zkFieldDataP`): the honest values, the boundary facts, the pending predicate
and the layer-0 count are all constructed, and the extraction event reads

```text
no lift-list member's committed witness satisfies the circuit c with the public input
```

(`QuadCircuit.Satisfied`: every assert-zero term's hand product vanishes and every output wire is
zero, on the witness the member's committed columns hold at the placement).

* `row_zk_deployed_circuit_ratio_le` — at any certified V1 row and output dimension `logv`, for a
  circuit `c` with `c.nl = R.params.nl` that fits the row's width profile `R.params.logw`;
* `v7Hash{1,2,3,4}_zk_circuit_ratio_le`, `v7Sig_zk_circuit_ratio_le` — at the registered v7 rows:
  `2^-115 + N · 2^-117` (hash), `2^-123 + N · 2^-123` (signature);
* `CompiledZkSide.ofCircuit` — a two-field side from a circuit, its public input a function of the
  MAC-key share and the public data;
* `v7P256Sha{1,2,3,4}_zk_circuit_ratio_le` — **two-field Longfellow at the deployed v7 pairs**, hash
  side first, both sides from circuits: `2^-115 + N · 2^-117` at a fixed Merkle budget;
* `…_leT` and §5 — the same with **no bound on the prover's Merkle queries**, and the headlines in
  T-security form: `v7P256Sha{1,2,3,4}_zk_circuit_tsec`, `v7Hash{1,2,3,4}_zk_circuit_tsec` at
  `(1 + tA + N) · 2^-115`, `v7Sig_zk_circuit_tsec` at `(1 + tA + N) · 2^-122`.

## What is still a hypothesis

* About each circuit: `WellFormedP` at the row's profile (decidable), `Isolated`, `DeadEnd`
  (decidable; `inspect_v7_assertions.py` checks the registered v7 circuits), and that `QuadCircuit`
  is the artifact's bytes (transliteration).
* About each verifier's code: `CodeAgreesP` (its next points are the bound list's interleaved even
  and odd coordinates, its layer coefficient is `bind_gh_all` at the layer's own `beta`, its input row
  is the `alpha_in`-combination of the two points' `EQ` vectors), `begin_circuit` puts both points at
  the output point, `nlin`/`nt` fit, exactly balanced decoders (`hkinit`, …), `|F|`.
* About the commitment: the placement `pl` (where the witness sits in the tableau), `|D|`, the
  Merkle budget; for two fields the MAC data and the MAC rows `hrow₁`, `hrow₂` (each circuit
  enforces the MAC on its bit-packed common value with the same private blind `keyB` on both
  sides). Sharing the public tags and multiplier in Rust does not establish this shared-blind
  premise; the separate-blind composition is an unresolved obligation described in the README.
* The random-oracle idealisation of SHA-256 on (context, role, message prefix) and transliteration
  debt R1, R2, R6 (README).
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

/-! ## 1. One field, at a certified row -/

section Row

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**A certified V1 row at the deployed zero-knowledge verifier with deployed hash inputs, the field
half constructed from a circuit, with no bound on the prover's Merkle queries.**
`row_zk_deployed_circuit_ratio_le` over a Merkle tape of any length `TM` with room for the run:

```text
Pr[ AcceptsZkDH  ∧  no lift-list member's committed witness satisfies c ]
    ≤  zkCore  +  N · R.zkCoefficient logv  +  adaptiveNumerator (2n) tA (L + N) / 2^digestBits
```
-/
theorem row_zk_deployed_circuit_ratio_leT {R : Row} (h : R.Valid) (hr : 0 < R.params.row.openings)
    (logv : ℕ) (c : QuadCircuit F) (hnl : c.nl = R.params.nl) {L TM : ℕ}
    (hwf : WellFormedP c logv R.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M R.params.q R.params.nw R.params.nq nt)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg R.params.nl R.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin logv → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry R.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (logv + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry R.params.row) ≤ Fintype.card C)
    (htape : 2 * R.params.row.n + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin TM → D) × (MPoint D Msg R.params.nl R.params.rounds → C) =>
        AcceptsZkDH (nl := R.params.nl) (w := R.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid h) dom
              (Row.hkrow h) hr) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
              (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ)) =>
              c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg R.params.nl R.params.rounds))
      ≤ zkCoreAt R logv R.cardCand + N * R.zkCoefficient logv
        + (AdaptiveCommit.adaptiveNumerator (2 * R.params.row.n) tA
            (Rounds.Role.length R.params.nl R.params.rounds + N) : ℚ)
          / 2 ^ R.params.digestBits :=
  row_zk_deployed_ratio_leT h hr logv pl dec V hnlin hnt dom respOf body rootOf msgOf claimOf hF
    (fun _ => zkHonestP hwf pub (fun ℓ => (asgOf pl ℓ).1)
      (cPendP c pub L R.params.logw (fun ℓ => (asgOf pl ℓ).1)))
    (fun _ ℓ => c.Satisfied pub (asgOf pl ℓ).1)
    (fun _ => zkFieldDataP hwf pub hiso hde V hV hst0 (fun ℓ => (asgOf pl ℓ).1) (asgOf pl)
      (fun _ _ _ => rfl) kinit kpair k kchal kq hbalInit hbalPair hbalF hbalChal hbalQuery hnl)
    (fun _ => zkFieldDataP_exactAt hwf pub hiso hde V hV hst0 (fun ℓ => (asgOf pl ℓ).1)
      (asgOf pl) (fun _ _ _ => rfl) kinit kpair k kchal kq hbalInit hbalPair hbalF hbalChal
      hbalQuery hnl hkinit hkpair hk hkchal hkq)
    htape hTM hD

/--
**A certified V1 row at the deployed zero-knowledge verifier with deployed hash inputs, the field
half constructed from a circuit.**

`CompiledZkDeployedHash.row_zk_deployed_ratio_le` with `H`, `Sat`, `FD` and `hexact` built by
`ZkArithProfile.zkFieldDataP` from a circuit `c` that has the row's layer count and fits the row's
width profile, at the honest satisfaction of the witness each lift-list member's committed columns
hold:

```text
Pr[ AcceptsZkDH  ∧  no lift-list member's committed witness satisfies c ]
    ≤  R.zkBound logv  +  N · R.zkCoefficient logv  +  R.tape · (L + N) / 2^digestBits
```
-/
theorem row_zk_deployed_circuit_ratio_le {R : Row} (h : R.Valid) (hr : 0 < R.params.row.openings)
    (logv : ℕ) (c : QuadCircuit F) (hnl : c.nl = R.params.nl) {L : ℕ}
    (hwf : WellFormedP c logv R.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M R.params.q R.params.nw R.params.nq nt)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg R.params.nl R.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin logv → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry R.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (logv + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry R.params.row) ≤ Fintype.card C)
    (htA : tA ≤ R.commitFuel) (htape : 2 * R.params.row.n + tA ≤ R.tape)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (MPoint D Msg R.params.nl R.params.rounds → C) =>
        AcceptsZkDH (nl := R.params.nl) (w := R.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid h) dom
              (Row.hkrow h) hr) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
              (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ)) =>
              c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg R.params.nl R.params.rounds))
      ≤ R.zkBound logv + N * R.zkCoefficient logv
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits :=
  le_trans (row_zk_deployed_circuit_ratio_leT h hr logv c hnl hwf hiso hde pub pl dec V hnlin hnt hV
      hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit hbalPair hbalF
      hbalChal hbalQuery hkinit hkpair hk hkchal hkq htape (by have := Row.fuel_room h; omega) hD)
    (row_cap h logv htA htape)

end Row

end Lfzk.CompiledZkProfileRows

/-! ## 2. A two-field side from a circuit -/

namespace Lfzk.CompiledZk

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle Lfzk.RbrZkLongfellow
  Lfzk.RbrZkSplit Lfzk.ZkLigeroV1 Lfzk.CertifiedV1 Lfzk.Arith Lfzk.ZkArithProfile Lfzk.ZkArithInit
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

/--
**A deployed zero-knowledge side, from a circuit at the row's width profile.**  The circuit `c` has
the row's layer count and fits its profile (`WellFormedP` at `R.params.logw`, output width `logv`),
its assertions are isolated dead ends, and its public input is `pubIn av x` at the MAC-key share `av`
and the public data `x`.  The verifier's code `Vc av x` agrees with the construction at that public
input, and its decoders are exactly balanced.  `toSide` is the `CompiledZkSide` whose candidates'
witnesses are their committed columns and whose `Sat` is `c.Satisfied (pubIn av x)`.
-/
structure CircuitSide (R : Row) (hR : R.Valid) (hr : 0 < R.params.row.openings) (logv : ℕ)
    (C : Type) [Fintype C] (F Msg : Type) [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    (M nt nlin : ℕ) {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] (X : Type) {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
    (dec : RoleDecoders codec) (rootOfKey : D × D → D) where
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
  /-- The decoders' balances, exact. -/
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
  hkinit : kinit * Fintype.card F ^ (logv + 2) ≤ Fintype.card C
  hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C
  hk : k * Fintype.card F ≤ Fintype.card C
  hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
    ≤ Fintype.card C
  hkq : kq * Fintype.card (LigeroV1LayerStep.Qry R.params.row) ≤ Fintype.card C
  hF : Fintype.card F = R.params.row.fieldSize

namespace CircuitSide

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {X : Type} {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}

/-- **The `CompiledZkSide` a circuit side is**: the field half from `ZkArithProfile.zkFieldDataP`
at every side context. -/
noncomputable def toSide
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey) :
    CompiledZkSide R hR hr logv C F Msg (Fin S.c.ninp → F) M S.c.ninp nt nlin S.L 0 X dec
      rootOfKey where
  pl := S.pl
  dom := S.dom
  Vc := S.Vc
  hnlin := S.hnlin
  hnt := S.hnt
  respOf := S.respOf
  H σ := zkHonestP S.hwf (S.pubIn σ.2.1 σ.2.2) (fun ℓ => (asgOf S.pl ℓ).1)
    (cPendP S.c (S.pubIn σ.2.1 σ.2.2) S.L R.params.logw (fun ℓ => (asgOf S.pl ℓ).1))
  wit _ ℓ := (asgOf S.pl ℓ).1
  Sat σ ℓ := S.c.Satisfied (S.pubIn σ.2.1 σ.2.2) (asgOf S.pl ℓ).1
  FD σ := zkFieldDataP S.hwf (S.pubIn σ.2.1 σ.2.2) S.hiso S.hde (S.Vc σ.2.1 σ.2.2) (S.hV _ _)
    (S.hst0 _ _) (fun ℓ => (asgOf S.pl ℓ).1) (asgOf S.pl) (fun _ _ _ => rfl) S.kinit S.kpair S.k
    S.kchal S.kq (S.hbalInit _ _) (S.hbalPair _ _) (S.hbalF _ _) (S.hbalChal _ _)
    (S.hbalQuery _ _) S.hnl
  hexact σ := zkFieldDataP_exactAt S.hwf (S.pubIn σ.2.1 σ.2.2) S.hiso S.hde (S.Vc σ.2.1 σ.2.2)
    (S.hV _ _) (S.hst0 _ _) (fun ℓ => (asgOf S.pl ℓ).1) (asgOf S.pl) (fun _ _ _ => rfl) S.kinit
    S.kpair S.k S.kchal S.kq (S.hbalInit _ _) (S.hbalPair _ _) (S.hbalF _ _) (S.hbalChal _ _)
    (S.hbalQuery _ _) S.hnl S.hkinit S.hkpair S.hk S.hkchal S.hkq
  hF := S.hF

/-- A circuit side's good witnesses are the committed witnesses of lift-list members that satisfy
the circuit at the side's public input. -/
theorem toSide_good (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) (a : Fin S.c.ninp → F) :
    S.toSide.Good σ a ↔ ∃ ℓ : sideLift hR hr nlin nt S.dom dec rootOfKey σ,
      S.c.Satisfied (S.pubIn σ.2.1 σ.2.2) (asgOf S.pl ℓ).1 ∧ (asgOf S.pl ℓ).1 = a := Iff.rfl

end CircuitSide

end Lfzk.CompiledZk

/-! ## 3. The v7 rows, one field -/

namespace Lfzk.CompiledZkProfileRows

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
  RbrLongfellow Lfzk.NizkDeployedHash Lfzk.NizkDeployedHashAdaptive Lfzk.RbrZkLongfellow
  Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1 Lfzk.CompiledZk Lfzk.CertifiedV1
  Lfzk.CompiledZkDeployedHash Lfzk.Arith Lfzk.ZkArithProfile Lfzk.ZkArithInit
open Lfzk.CompiledLongfellow (Col v1K)
open scoped Classical

section V7

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**`v7Hash1`, the deployed v7 1-attribute hash row, at the deployed zero-knowledge verifier with deployed hash
inputs, the field half constructed from a circuit: `2^-115 + N · 2^-117`.**
`row_zk_deployed_circuit_ratio_le` at `CertifiedV1.v7Hash1` (output dimension `logv = 3`, width profile
`v7Hash1.params.logw`) with the numerals `CompiledZk.v7Hash1_zk_rhs_le`.
-/
theorem v7Hash1_zk_circuit_ratio_le (c : QuadCircuit F) (hnl : c.nl = v7Hash1.params.nl) {L : ℕ}
    (hwf : WellFormedP c 3 v7Hash1.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Hash1.params.q v7Hash1.params.nw v7Hash1.params.nq nt)
    {codec : Codec Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash1.params.row) Msg (Fin 3 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash1.params.row.n Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 3 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Hash1.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (3 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Hash1.params.row) ≤ Fintype.card C)
    (htA : tA ≤ v7Hash1.commitFuel) (htape : 2 * v7Hash1.params.row.n + tA ≤ v7Hash1.tape)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash1.tape → D) × (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash1_valid) dom
              (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
              (extOracle nlin nt (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
                v7Hash1_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash1.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_deployed_circuit_ratio_le v7Hash1_valid v7Hash1_openings_pos 3 c hnl hwf hiso hde pub pl dec V
      hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htA htape hD)
    (v7Hash1_zk_rhs_le N)

/--
**`v7Hash2`, the deployed v7 2-attribute hash row, at the deployed zero-knowledge verifier with deployed hash
inputs, the field half constructed from a circuit: `2^-115 + N · 2^-117`.**
`row_zk_deployed_circuit_ratio_le` at `CertifiedV1.v7Hash2` (output dimension `logv = 4`, width profile
`v7Hash2.params.logw`) with the numerals `CompiledZk.v7Hash2_zk_rhs_le`.
-/
theorem v7Hash2_zk_circuit_ratio_le (c : QuadCircuit F) (hnl : c.nl = v7Hash2.params.nl) {L : ℕ}
    (hwf : WellFormedP c 4 v7Hash2.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Hash2.params.q v7Hash2.params.nw v7Hash2.params.nq nt)
    {codec : Codec Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash2.params.row) Msg (Fin 4 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash2.params.row.n Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D)
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 4 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Hash2.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (4 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Hash2.params.row) ≤ Fintype.card C)
    (htA : tA ≤ v7Hash2.commitFuel) (htape : 2 * v7Hash2.params.row.n + tA ≤ v7Hash2.tape)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash2.tape → D) × (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash2_valid) dom
              (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
              (extOracle nlin nt (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
                v7Hash2_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash2.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_deployed_circuit_ratio_le v7Hash2_valid v7Hash2_openings_pos 4 c hnl hwf hiso hde pub pl dec V
      hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htA htape hD)
    (v7Hash2_zk_rhs_le N)

/--
**`v7Hash3`, the deployed v7 3-attribute hash row, at the deployed zero-knowledge verifier with deployed hash
inputs, the field half constructed from a circuit: `2^-115 + N · 2^-117`.**
`row_zk_deployed_circuit_ratio_le` at `CertifiedV1.v7Hash3` (output dimension `logv = 4`, width profile
`v7Hash3.params.logw`) with the numerals `CompiledZk.v7Hash3_zk_rhs_le`.
-/
theorem v7Hash3_zk_circuit_ratio_le (c : QuadCircuit F) (hnl : c.nl = v7Hash3.params.nl) {L : ℕ}
    (hwf : WellFormedP c 4 v7Hash3.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Hash3.params.q v7Hash3.params.nw v7Hash3.params.nq nt)
    {codec : Codec Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash3.params.row) Msg (Fin 4 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash3.params.row.n Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D)
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 4 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Hash3.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (4 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Hash3.params.row) ≤ Fintype.card C)
    (htA : tA ≤ v7Hash3.commitFuel) (htape : 2 * v7Hash3.params.row.n + tA ≤ v7Hash3.tape)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash3.tape → D) × (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash3_valid) dom
              (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
              (extOracle nlin nt (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
                v7Hash3_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash3.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_deployed_circuit_ratio_le v7Hash3_valid v7Hash3_openings_pos 4 c hnl hwf hiso hde pub pl dec V
      hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htA htape hD)
    (v7Hash3_zk_rhs_le N)

/--
**`v7Hash4`, the deployed v7 4-attribute hash row, at the deployed zero-knowledge verifier with deployed hash
inputs, the field half constructed from a circuit: `2^-115 + N · 2^-117`.**
`row_zk_deployed_circuit_ratio_le` at `CertifiedV1.v7Hash4` (output dimension `logv = 5`, width profile
`v7Hash4.params.logw`) with the numerals `CompiledZk.v7Hash4_zk_rhs_le`.
-/
theorem v7Hash4_zk_circuit_ratio_le (c : QuadCircuit F) (hnl : c.nl = v7Hash4.params.nl) {L : ℕ}
    (hwf : WellFormedP c 5 v7Hash4.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Hash4.params.q v7Hash4.params.nw v7Hash4.params.nq nt)
    {codec : Codec Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash4.params.row) Msg (Fin 5 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash4.params.row.n Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D)
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 5 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Hash4.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (5 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Hash4.params.row) ≤ Fintype.card C)
    (htA : tA ≤ v7Hash4.commitFuel) (htape : 2 * v7Hash4.params.row.n + tA ≤ v7Hash4.tape)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash4.tape → D) × (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash4_valid) dom
              (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
              (extOracle nlin nt (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
                v7Hash4_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash4.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_deployed_circuit_ratio_le v7Hash4_valid v7Hash4_openings_pos 5 c hnl hwf hiso hde pub pl dec V
      hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htA htape hD)
    (v7Hash4_zk_rhs_le N)

/--
**`v7Sig`, the deployed v7 signature row, at the deployed zero-knowledge verifier with deployed hash
inputs, the field half constructed from a circuit: `2^-123 + N · 2^-123`.**
`row_zk_deployed_circuit_ratio_le` at `CertifiedV1.v7Sig` (output dimension `logv = 8`, width profile
`v7Sig.params.logw`) with the numerals `CompiledZk.v7Sig_zk_rhs_le`.
-/
theorem v7Sig_zk_circuit_ratio_le (c : QuadCircuit F) (hnl : c.nl = v7Sig.params.nl) {L : ℕ}
    (hwf : WellFormedP c 8 v7Sig.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Sig.params.q v7Sig.params.nw v7Sig.params.nq nt)
    {codec : Codec Salt (Col F v7Sig.params.nw v7Sig.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Sig.params.row) Msg (Fin 8 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Sig.params.row.n Salt (Col F v7Sig.params.nw v7Sig.params.nq) D)
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 8 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Sig.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (8 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Sig.params.row) ≤ Fintype.card C)
    (htA : tA ≤ v7Sig.commitFuel) (htape : 2 * v7Sig.params.row.n + tA ≤ v7Sig.tape)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Sig.tape → D) × (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds → C) =>
        AcceptsZkDH (nl := v7Sig.params.nl) (w := v7Sig.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Sig_valid) dom
              (Row.hkrow v7Sig_valid) v7Sig_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
              (extOracle nlin nt (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
                v7Sig_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Sig.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 123 + N * ((1 : ℚ) / 2 ^ 123) :=
  le_trans
    (row_zk_deployed_circuit_ratio_le v7Sig_valid v7Sig_openings_pos 8 c hnl hwf hiso hde pub pl dec V
      hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htA htape hD)
    (v7Sig_zk_rhs_le N)

end V7

/-! ## 4. The v7 pairs, two fields, hash side first, both sides from circuits -/

open Lfzk.NizkAdaptiveTwoField (check2 len2)
open Lfzk.NizkDeployedHashTwoField (Pt2 setup2 sideCtx)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2)
open Lfzk.TwoFieldV1Rows Lfzk.Mac

section V7Pairs

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
**Two-field Longfellow at `v7P256Sha1`, as deployed: the v7 `1`-attribute hash circuit over `GF(2^128)`
proved first, then the v7 signature circuit over `P-256`'s base field, on one Fiat–Shamir transcript
with deployed hash inputs, both field halves constructed from the circuits: `2^-115 + N · 2^-117`.**

`CompiledZkDeployedHash.v7P256Sha1_zk_deployed_ratio_le` at `S₁.toSide`, `S₂.toSide`.  A good witness of a
side is the committed witness of a lift-list member that satisfies that side's circuit at its public
input (`CircuitSide.toSide_good`):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  2^-115  +  N · 2^-117
```

against one adaptive program making at most `tA ≤ 2^60` Merkle-oracle queries and `N` deployed hash
queries.
-/
theorem v7P256Sha1_zk_circuit_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
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
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha1.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha1.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha1.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha1.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) := by
  have key := v7P256Sha1_zk_deployed_ratio_le hFmac S₁.toSide S₂.toSide body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁
    hrow₂ htA htape
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  convert key using 6

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha2`, as deployed: the v7 `2`-attribute hash circuit over `GF(2^128)`
proved first, then the v7 signature circuit over `P-256`'s base field, on one Fiat–Shamir transcript
with deployed hash inputs, both field halves constructed from the circuits: `2^-115 + N · 2^-117`.**

`CompiledZkDeployedHash.v7P256Sha2_zk_deployed_ratio_le` at `S₁.toSide`, `S₂.toSide`.  A good witness of a
side is the committed witness of a lift-list member that satisfies that side's circuit at its public
input (`CircuitSide.toSide_good`):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  2^-115  +  N · 2^-117
```

against one adaptive program making at most `tA ≤ 2^60` Merkle-oracle queries and `N` deployed hash
queries.
-/
theorem v7P256Sha2_zk_circuit_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
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
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha2.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha2.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha2.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha2.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) := by
  have key := v7P256Sha2_zk_deployed_ratio_le hFmac S₁.toSide S₂.toSide body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁
    hrow₂ htA htape
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  convert key using 6

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha3`, as deployed: the v7 `3`-attribute hash circuit over `GF(2^128)`
proved first, then the v7 signature circuit over `P-256`'s base field, on one Fiat–Shamir transcript
with deployed hash inputs, both field halves constructed from the circuits: `2^-115 + N · 2^-117`.**

`CompiledZkDeployedHash.v7P256Sha3_zk_deployed_ratio_le` at `S₁.toSide`, `S₂.toSide`.  A good witness of a
side is the committed witness of a lift-list member that satisfies that side's circuit at its public
input (`CircuitSide.toSide_good`):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  2^-115  +  N · 2^-117
```

against one adaptive program making at most `tA ≤ 2^60` Merkle-oracle queries and `N` deployed hash
queries.
-/
theorem v7P256Sha3_zk_circuit_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
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
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha3.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha3.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha3.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha3.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) := by
  have key := v7P256Sha3_zk_deployed_ratio_le hFmac S₁.toSide S₂.toSide body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁
    hrow₂ htA htape
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  convert key using 6

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha4`, as deployed: the v7 `4`-attribute hash circuit over `GF(2^128)`
proved first, then the v7 signature circuit over `P-256`'s base field, on one Fiat–Shamir transcript
with deployed hash inputs, both field halves constructed from the circuits: `2^-115 + N · 2^-117`.**

`CompiledZkDeployedHash.v7P256Sha4_zk_deployed_ratio_le` at `S₁.toSide`, `S₂.toSide`.  A good witness of a
side is the committed witness of a lift-list member that satisfies that side's circuit at its public
input (`CircuitSide.toSide_good`):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  2^-115  +  N · 2^-117
```

against one adaptive program making at most `tA ≤ 2^60` Merkle-oracle queries and `N` deployed hash
queries.
-/
theorem v7P256Sha4_zk_circuit_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
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
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha4.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha4.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha4.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha4.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) := by
  have key := v7P256Sha4_zk_deployed_ratio_le hFmac S₁.toSide S₂.toSide body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁
    hrow₂ htA htape
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  convert key using 6

end V7Pairs

end Lfzk.CompiledZkProfileRows

/-! ## 5. T-security

The headlines above close the Merkle extraction term at the rows' fixed budget (`tA ≤ 2^60` Merkle
queries, a `2^62`-slot tape) so that each is one number.  Nothing in the proof needs that budget:
`…_leT` is the same chain over a Merkle tape of any length, with the Merkle term the exact count
`adaptiveNumerator (2n) tA (L + N)`, quadratic in `tA` (the birthday term of a 256-bit hash).  This
section turns that into **T-security**: an adversary making `tA` Merkle-oracle and `N` hash queries
succeeds with probability at most `(1 + tA + N) · 2^-λ`.

* `tsec_real`, `tsec_of_uncapped` — the arithmetic: below `N, tA ≤ G = 2^(d − λ − 4)` the quadratic
  term is at most `tA · 2^-λ`; above it `(1 + N + tA) · 2^-λ ≥ 1`;
* `row_tsec`, `twofield_tsec` — at a row or a pair, from its certified slack numerals;
* `v7Hash{1..4}_zk_circuit_tsec` (`λ = 115`), `v7Sig_zk_circuit_tsec` (`λ = 122`),
  `v7P256Sha{1..4}_zk_circuit_tsec` (`λ = 115`).
-/

namespace Lfzk.TSec
open Finset

/-- The adaptive Merkle count, opened up. -/
theorem adaptiveNumerator_le_poly (fc tA m : ℕ) :
    Bcs.AdaptiveCommit.adaptiveNumerator fc tA m
      ≤ 3 * (tA * tA) + tA * (2 * fc + 1) + fc + (fc + tA) * m := by
  unfold Bcs.AdaptiveCommit.adaptiveNumerator
  have h1 : tA * (tA - 1) / 2 ≤ tA * tA :=
    le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  nlinarith [h1]

/-- The arithmetic of T-security, over `ℚ`. -/
theorem tsec_real {A K ε δ k n t f T l g AN : ℚ}
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hδ : 0 ≤ δ) (hk0 : 0 ≤ k) (hk : k ≤ 2)
    (hn : 0 ≤ n) (ht : 0 ≤ t) (hf : 0 ≤ f) (hl : 1 ≤ l) (hT : 32 ≤ T)
    (hnG : n ≤ g) (htG : t ≤ g) (hfT : 2 * f ≤ T)
    (hA : A + k * (T * l) * δ ≤ ε) (hK : K + k * T * δ ≤ ε / 2) (hG : 16 * g * δ ≤ ε)
    (hAN : AN ≤ 3 * (t * t) + t * (2 * f + 1) + f + (f + t) * (l + n)) :
    A + n * K + k * AN * δ ≤ (1 + n + t) * ε := by
  have hQ : 0 ≤ k * δ := mul_nonneg hk0 hδ
  have hg0 : 0 ≤ g := le_trans hn hnG
  have hε : 0 ≤ ε := le_trans (mul_nonneg (mul_nonneg (by norm_num) hg0) hδ) hG
  have hP2 : k * δ ≤ 2 * δ := mul_le_mul_of_nonneg_right hk hδ
  have hkT : k * T * δ ≤ ε / 2 := by linarith
  have hkTl : k * (T * l) * δ ≤ ε - A := by linarith
  have hgδ : g * δ ≤ ε / 16 := by linarith
  have hkl : k * l * δ * 32 ≤ ε := by
    have h1 : k * l * δ * 32 ≤ k * l * δ * T :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    have h2 : k * l * δ * T = k * (T * l) * δ := by ring
    linarith
  -- (1) the birthday term
  have a1 : k * δ * t ≤ 2 * δ * g := mul_le_mul hP2 htG ht (by positivity)
  have e1 : k * (3 * (t * t)) * δ ≤ t * (6 / 16 * ε) := by
    have h1 : t * (k * δ * t) ≤ t * (2 * δ * g) := mul_le_mul_of_nonneg_left a1 ht
    have h2 : t * (g * δ) ≤ t * (ε / 16) := mul_le_mul_of_nonneg_left hgδ ht
    have h3 : k * (3 * (t * t)) * δ = 3 * (t * (k * δ * t)) := by ring
    have h4 : t * (2 * δ * g) = 2 * (t * (g * δ)) := by ring
    nlinarith
  -- (2) the opening check's queries times the adversary's
  have e2 : k * (t * (2 * f)) * δ ≤ t * (ε / 2) := by
    have h1 : 2 * f * (k * δ) ≤ T * (k * δ) := mul_le_mul_of_nonneg_right hfT hQ
    have h2 : t * (2 * f * (k * δ)) ≤ t * (T * (k * δ)) := mul_le_mul_of_nonneg_left h1 ht
    have h3 : t * (T * (k * δ)) ≤ t * (ε / 2) := by
      have : T * (k * δ) = k * T * δ := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hkT ht
    have h4 : k * (t * (2 * f)) * δ = t * (2 * f * (k * δ)) := by ring
    linarith
  -- (3) one root target per verifier slot and per adversary query
  have e3 : k * (t * (1 + l)) * δ ≤ t * (ε / 16) := by
    have h1 : (1 + l) * (k * δ) ≤ (2 * l) * (k * δ) := mul_le_mul_of_nonneg_right (by linarith) hQ
    have h2 : (2 * l) * (k * δ) ≤ ε / 16 := by
      have : (2 * l) * (k * δ) = 2 * (k * l * δ) := by ring
      rw [this]; linarith
    have h3 : t * ((1 + l) * (k * δ)) ≤ t * (ε / 16) :=
      mul_le_mul_of_nonneg_left (le_trans h1 h2) ht
    have h4 : k * (t * (1 + l)) * δ = t * ((1 + l) * (k * δ)) := by ring
    linarith
  -- (4) the constant
  have e4 : k * (f * (1 + l)) * δ ≤ ε - A := by
    have h0 : f ≤ f * l := le_mul_of_one_le_right hf hl
    have h1 : f * (1 + l) ≤ T * l := by nlinarith
    have h2 : (f * (1 + l)) * (k * δ) ≤ (T * l) * (k * δ) := mul_le_mul_of_nonneg_right h1 hQ
    have h3 : k * (f * (1 + l)) * δ = (f * (1 + l)) * (k * δ) := by ring
    have h4 : (T * l) * (k * δ) = k * (T * l) * δ := by ring
    linarith
  -- (5) the opening check's queries times the hash queries
  have e5 : k * (f * n) * δ ≤ n * (ε / 2 - K) := by
    have h1 : f * (k * δ) ≤ T * (k * δ) := mul_le_mul_of_nonneg_right (by linarith) hQ
    have h2 : T * (k * δ) ≤ ε / 2 - K := by
      have : T * (k * δ) = k * T * δ := by ring
      rw [this]; linarith
    have h3 : n * (f * (k * δ)) ≤ n * (ε / 2 - K) :=
      mul_le_mul_of_nonneg_left (le_trans h1 h2) hn
    have h4 : k * (f * n) * δ = n * (f * (k * δ)) := by ring
    linarith
  -- (6) the adversary's Merkle queries times its hash queries
  have e6 : k * (t * n) * δ ≤ n * (ε / 8) := by
    have h1 : n * (k * δ * t) ≤ n * (2 * δ * g) := mul_le_mul_of_nonneg_left a1 hn
    have h2 : n * (g * δ) ≤ n * (ε / 16) := mul_le_mul_of_nonneg_left hgδ hn
    have h3 : k * (t * n) * δ = n * (k * δ * t) := by ring
    have h4 : n * (2 * δ * g) = 2 * (n * (g * δ)) := by ring
    linarith
  have hmono : k * AN * δ ≤ k * (3 * (t * t) + t * (2 * f + 1) + f + (f + t) * (l + n)) * δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAN hk0) hδ
  have hexp : k * (3 * (t * t) + t * (2 * f + 1) + f + (f + t) * (l + n)) * δ
      = k * (3 * (t * t)) * δ + k * (t * (2 * f)) * δ + k * (t * (1 + l)) * δ
        + k * (f * (1 + l)) * δ + k * (f * n) * δ + k * (t * n) * δ := by ring
  have hnK : n * (ε / 2 - K) + n * K = n * (ε / 2) := by ring
  nlinarith

/-- **T-security from an uncapped bound.**  Any `p ≤ 1` below the uncapped right-hand side is at most
`(1 + N + tA) · ε`: inside `N, tA ≤ G` by `tsec_real`, and outside it the right-hand side is at least
`G · ε ≥ 1`. -/
theorem tsec_of_uncapped {p A K ε δ k : ℚ} {fc T0 L N tA G : ℕ} (hp1 : p ≤ 1)
    (hp : p ≤ A + N * K + k * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) * δ)
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hδ : 0 ≤ δ) (hk0 : 0 ≤ k) (hk : k ≤ 2)
    (hA : A + k * ((T0 * L : ℕ) : ℚ) * δ ≤ ε) (hK : K + k * (T0 : ℚ) * δ ≤ ε / 2)
    (hG : 16 * (G : ℚ) * δ ≤ ε) (hGe : 1 ≤ (G : ℚ) * ε) (hT0 : 32 ≤ T0) (hfc : 2 * fc ≤ T0)
    (hL : 1 ≤ L) :
    p ≤ (1 + N + tA) * ε := by
  have hε : 0 ≤ ε := le_trans (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ) hG
  by_cases hs : N ≤ G ∧ tA ≤ G
  · refine hp.trans (tsec_real (n := (N : ℚ)) (t := (tA : ℚ)) (f := (fc : ℚ)) (T := (T0 : ℚ))
      (l := (L : ℚ)) (g := (G : ℚ))
      (AN := (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ))
      hA0 hK0 hδ hk0 hk (Nat.cast_nonneg N) (Nat.cast_nonneg tA)
      (Nat.cast_nonneg fc) (by exact_mod_cast hL) (by exact_mod_cast hT0)
      (by exact_mod_cast hs.1) (by exact_mod_cast hs.2) (by exact_mod_cast hfc)
      (by push_cast at hA; exact hA) hK hG ?_)
    have := adaptiveNumerator_le_poly fc tA (L + N)
    exact_mod_cast this
  · have hGN : (G : ℚ) ≤ N + tA := by
      have : G ≤ N + tA := by
        by_contra hc
        exact hs ⟨by omega, by omega⟩
      exact_mod_cast this
    calc p ≤ 1 := hp1
      _ ≤ (G : ℚ) * ε := hGe
      _ ≤ (1 + N + tA) * ε := mul_le_mul_of_nonneg_right (by linarith) hε

open Lfzk.CertifiedV1 Lfzk.NizkZk Lfzk.NizkAdaptiveTwoField

/-- **A probability is at most one**: the event over the Merkle tape and the total oracle. -/
theorem ratio_le_one {D C Pt : Type} [Fintype D] [Fintype C] [Fintype Pt] [DecidableEq Pt]
    [Nonempty D] [Nonempty C] {TM : ℕ} (P : (Fin TM → D) × (Pt → C) → Prop)
    {inst : DecidablePred P} :
    ((@Finset.filter _ P inst univ).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤ 1 := by
  have hcard : Fintype.card ((Fin TM → D) × (Pt → C))
      = Fintype.card D ^ TM * Fintype.card C ^ Fintype.card Pt := by
    simp [Fintype.card_prod]
  rw [div_le_one (by positivity)]
  have h := Finset.card_le_univ (@Finset.filter _ P inst univ)
  rw [hcard] at h
  exact_mod_cast h

/-- The exponent bookkeeping: `G = 2^(d - a - 4)` against `δ = 2^-d` and `ε = 2^-a`. -/
theorem pow_facts {a d : ℕ} (hd : 2 * a + 4 ≤ d) :
    16 * ((2 ^ (d - a - 4) : ℕ) : ℚ) * (1 / 2 ^ d) ≤ 1 / 2 ^ a
      ∧ 1 ≤ ((2 ^ (d - a - 4) : ℕ) : ℚ) * (1 / 2 ^ a) := by
  have hsplit : (2 : ℚ) ^ d = 2 ^ (d - a - 4) * 2 ^ 4 * 2 ^ a := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  push_cast
  constructor
  · rw [hsplit]
    field_simp
    norm_num
  · rw [mul_one_div, one_le_div (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- **T-security at one certified row**, from its certified slack numerals. -/
theorem row_tsec {R : Row} {logv a n tA N : ℕ} {p : ℚ} (hp1 : p ≤ 1)
    (hp : p ≤ zkCoreAt R logv R.cardCand + N * R.zkCoefficient logv
      + (Bcs.AdaptiveCommit.adaptiveNumerator (2 * n) tA
          (Rounds.Role.length R.params.nl R.params.rounds + N) : ℚ) / 2 ^ R.params.digestBits)
    {a₀ b : ℕ}
    (hsb : R.zkBound logv
        + ((R.tape * Rounds.Role.length R.params.nl R.params.rounds : ℕ) : ℚ)
          / 2 ^ R.params.digestBits ≤ 1 / 2 ^ a₀) (ha : a ≤ a₀)
    (hsc : R.zkCoefficient logv + (R.tape : ℚ) / 2 ^ R.params.digestBits ≤ 1 / 2 ^ b)
    (hab : a + 1 ≤ b)
    (hT0 : 32 ≤ R.tape) (hfc : 4 * n ≤ R.tape) (hd : 2 * a + 4 ≤ R.params.digestBits) :
    p ≤ (1 + N + tA) / 2 ^ a := by
  obtain ⟨hG, hGe⟩ := pow_facts hd
  have hδ : (0 : ℚ) ≤ 1 / 2 ^ R.params.digestBits := by positivity
  have ha' : (1 : ℚ) / 2 ^ a₀ ≤ 1 / 2 ^ a :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) ha)
  have hb' : (1 : ℚ) / 2 ^ b ≤ 1 / 2 ^ (a + 1) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hab)
  have h2 : (1 : ℚ) / 2 ^ (a + 1) = 1 / 2 ^ a / 2 := by rw [pow_succ]; field_simp
  have hcore := zkCoreAt_le_zkBound R logv
  have key := tsec_of_uncapped (k := 1) (A := zkCoreAt R logv R.cardCand)
    (K := R.zkCoefficient logv) (ε := 1 / 2 ^ a) (δ := 1 / 2 ^ R.params.digestBits)
    (fc := 2 * n) (T0 := R.tape) (L := Rounds.Role.length R.params.nl R.params.rounds)
    (N := N) (tA := tA) (G := 2 ^ (R.params.digestBits - a - 4)) hp1
    (hp.trans_eq (by ring)) (zkCoreAt_nonneg R logv R.cardCand) (zkCoefficient_nonneg R logv) hδ
    (by norm_num) (by norm_num)
    (by
      have : (1 : ℚ) * ((R.tape * Rounds.Role.length R.params.nl R.params.rounds : ℕ) : ℚ)
          * (1 / 2 ^ R.params.digestBits)
          = ((R.tape * Rounds.Role.length R.params.nl R.params.rounds : ℕ) : ℚ)
            / 2 ^ R.params.digestBits := by ring
      rw [this]; linarith)
    (by
      have : (1 : ℚ) * (R.tape : ℚ) * (1 / 2 ^ R.params.digestBits)
          = (R.tape : ℚ) / 2 ^ R.params.digestBits := by ring
      rw [this, ← h2]; linarith)
    hG hGe hT0 (by omega) (length_pos R)
  exact key.trans_eq (by ring)

/-- **T-security for two fields** (hash side `R₁` first), from the pair's certified slack numerals,
which are stated signature side first. -/
theorem twofield_tsec {R₁ R₂ : Row} {l₁ l₂ a b fc tA N : ℕ} {p m : ℚ} (hp1 : p ≤ 1)
    (hp : p ≤ zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m
      + N * max (max (R₁.zkCoefficient l₁) (R₂.zkCoefficient l₂)) m
      + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA (len2 R₁ R₂ + N) : ℚ)
        / 2 ^ R₁.params.digestBits))
    (hm0 : 0 ≤ m)
    (hsb : R₂.zkBound l₂ + R₁.zkBound l₁ + m
        + 2 * (((R₂.tape * len2 R₂ R₁ : ℕ) : ℚ) / 2 ^ R₂.params.digestBits) ≤ 1 / 2 ^ a)
    (hsc : max (max (R₂.zkCoefficient l₂) (R₁.zkCoefficient l₁)) m
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
  have hmax : max (max (R₁.zkCoefficient l₁) (R₂.zkCoefficient l₂)) m
      = max (max (R₂.zkCoefficient l₂) (R₁.zkCoefficient l₁)) m := by rw [max_comm (R₁.zkCoefficient l₁)]
  have key := tsec_of_uncapped (k := 2)
    (A := zkCoreAt R₁ l₁ R₁.cardCand + zkCoreAt R₂ l₂ R₂.cardCand + m)
    (K := max (max (R₁.zkCoefficient l₁) (R₂.zkCoefficient l₂)) m) (ε := 1 / 2 ^ a)
    (δ := 1 / 2 ^ R₁.params.digestBits) (fc := fc) (T0 := R₂.tape) (L := len2 R₁ R₂)
    (N := N) (tA := tA) (G := 2 ^ (R₁.params.digestBits - a - 4)) hp1
    (hp.trans_eq (by ring))
    (by have := zkCoreAt_nonneg R₁ l₁ R₁.cardCand; have := zkCoreAt_nonneg R₂ l₂ R₂.cardCand
        linarith)
    (le_trans hm0 (le_max_right _ _)) hδ (by norm_num) (by norm_num)
    (by
      have : (2 : ℚ) * ((R₂.tape * len2 R₁ R₂ : ℕ) : ℚ) * (1 / 2 ^ R₁.params.digestBits)
          = 2 * (((R₂.tape * len2 R₁ R₂ : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by ring
      rw [this]; linarith)
    (by
      have : (2 : ℚ) * (R₂.tape : ℚ) * (1 / 2 ^ R₁.params.digestBits)
          = 2 * ((R₂.tape : ℚ) / 2 ^ R₁.params.digestBits) := by ring
      rw [this, hmax]; linarith)
    hG hGe hT0 hfc (by unfold len2; omega)
  exact key.trans_eq (by ring)

end Lfzk.TSec

/-! ### The v7 rows and pairs, T-secure -/

namespace Lfzk.CompiledZkProfileRows

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
  RbrLongfellow Lfzk.NizkDeployedHash Lfzk.NizkDeployedHashAdaptive Lfzk.RbrZkLongfellow
  Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1 Lfzk.CompiledZk Lfzk.CertifiedV1
  Lfzk.CompiledZkDeployedHash Lfzk.Arith Lfzk.ZkArithProfile Lfzk.ZkArithInit Lfzk.TSec
open Lfzk.CompiledLongfellow (Col v1K)
open scoped Classical

section V7TSec

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**`v7Hash1`, the deployed v7 1-attribute hash row, T-secure at `λ = 115`.**  Against one adaptive program making
`tA` Merkle-oracle and `N` deployed hash queries, **with no bound on either**, over a Merkle tape of
any length `TM` with room for the run:

```text
Pr[ AcceptsZkDH  ∧  no lift-list member's committed witness satisfies c ]  ≤  (1 + tA + N) · 2^-115
```

`row_zk_deployed_circuit_ratio_leT` at `CertifiedV1.v7Hash1`, with `row_tsec` and the certified slack
numerals `CompiledZk.v7Hash1_zk_slack_bound`, `_slack_coeff`.  The premises are
`v7Hash1_zk_circuit_ratio_le`'s without `tA ≤ 2^60`.
-/
theorem v7Hash1_zk_circuit_tsec (c : QuadCircuit F) (hnl : c.nl = v7Hash1.params.nl) {L TM : ℕ}
    (hwf : WellFormedP c 3 v7Hash1.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Hash1.params.q v7Hash1.params.nw v7Hash1.params.nq nt)
    {codec : Codec Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash1.params.row) Msg (Fin 3 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash1.params.row.n Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 3 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Hash1.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (3 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Hash1.params.row) ≤ Fintype.card C)
    (htape : 2 * v7Hash1.params.row.n + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun ω : (Fin TM → D) × (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash1_valid) dom
              (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
              (extOracle nlin nt (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
                v7Hash1_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 :=
  row_tsec (ratio_le_one _)
    (row_zk_deployed_circuit_ratio_leT v7Hash1_valid v7Hash1_openings_pos 3 c hnl hwf hiso hde pub pl dec
      V hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htape hTM hD)
    v7Hash1_zk_slack_bound (by norm_num) v7Hash1_zk_slack_coeff (by norm_num) (by decide) (by decide)
    (by decide)

/--
**`v7Hash2`, the deployed v7 2-attribute hash row, T-secure at `λ = 115`.**  Against one adaptive program making
`tA` Merkle-oracle and `N` deployed hash queries, **with no bound on either**, over a Merkle tape of
any length `TM` with room for the run:

```text
Pr[ AcceptsZkDH  ∧  no lift-list member's committed witness satisfies c ]  ≤  (1 + tA + N) · 2^-115
```

`row_zk_deployed_circuit_ratio_leT` at `CertifiedV1.v7Hash2`, with `row_tsec` and the certified slack
numerals `CompiledZk.v7Hash2_zk_slack_bound`, `_slack_coeff`.  The premises are
`v7Hash2_zk_circuit_ratio_le`'s without `tA ≤ 2^60`.
-/
theorem v7Hash2_zk_circuit_tsec (c : QuadCircuit F) (hnl : c.nl = v7Hash2.params.nl) {L TM : ℕ}
    (hwf : WellFormedP c 4 v7Hash2.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Hash2.params.q v7Hash2.params.nw v7Hash2.params.nq nt)
    {codec : Codec Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash2.params.row) Msg (Fin 4 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash2.params.row.n Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D)
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 4 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Hash2.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (4 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Hash2.params.row) ≤ Fintype.card C)
    (htape : 2 * v7Hash2.params.row.n + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun ω : (Fin TM → D) × (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash2_valid) dom
              (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
              (extOracle nlin nt (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
                v7Hash2_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 :=
  row_tsec (ratio_le_one _)
    (row_zk_deployed_circuit_ratio_leT v7Hash2_valid v7Hash2_openings_pos 4 c hnl hwf hiso hde pub pl dec
      V hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htape hTM hD)
    v7Hash2_zk_slack_bound (by norm_num) v7Hash2_zk_slack_coeff (by norm_num) (by decide) (by decide)
    (by decide)

/--
**`v7Hash3`, the deployed v7 3-attribute hash row, T-secure at `λ = 115`.**  Against one adaptive program making
`tA` Merkle-oracle and `N` deployed hash queries, **with no bound on either**, over a Merkle tape of
any length `TM` with room for the run:

```text
Pr[ AcceptsZkDH  ∧  no lift-list member's committed witness satisfies c ]  ≤  (1 + tA + N) · 2^-115
```

`row_zk_deployed_circuit_ratio_leT` at `CertifiedV1.v7Hash3`, with `row_tsec` and the certified slack
numerals `CompiledZk.v7Hash3_zk_slack_bound`, `_slack_coeff`.  The premises are
`v7Hash3_zk_circuit_ratio_le`'s without `tA ≤ 2^60`.
-/
theorem v7Hash3_zk_circuit_tsec (c : QuadCircuit F) (hnl : c.nl = v7Hash3.params.nl) {L TM : ℕ}
    (hwf : WellFormedP c 4 v7Hash3.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Hash3.params.q v7Hash3.params.nw v7Hash3.params.nq nt)
    {codec : Codec Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash3.params.row) Msg (Fin 4 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash3.params.row.n Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D)
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 4 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Hash3.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (4 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Hash3.params.row) ≤ Fintype.card C)
    (htape : 2 * v7Hash3.params.row.n + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun ω : (Fin TM → D) × (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash3_valid) dom
              (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
              (extOracle nlin nt (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
                v7Hash3_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 :=
  row_tsec (ratio_le_one _)
    (row_zk_deployed_circuit_ratio_leT v7Hash3_valid v7Hash3_openings_pos 4 c hnl hwf hiso hde pub pl dec
      V hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htape hTM hD)
    v7Hash3_zk_slack_bound (by norm_num) v7Hash3_zk_slack_coeff (by norm_num) (by decide) (by decide)
    (by decide)

/--
**`v7Hash4`, the deployed v7 4-attribute hash row, T-secure at `λ = 115`.**  Against one adaptive program making
`tA` Merkle-oracle and `N` deployed hash queries, **with no bound on either**, over a Merkle tape of
any length `TM` with room for the run:

```text
Pr[ AcceptsZkDH  ∧  no lift-list member's committed witness satisfies c ]  ≤  (1 + tA + N) · 2^-115
```

`row_zk_deployed_circuit_ratio_leT` at `CertifiedV1.v7Hash4`, with `row_tsec` and the certified slack
numerals `CompiledZk.v7Hash4_zk_slack_bound`, `_slack_coeff`.  The premises are
`v7Hash4_zk_circuit_ratio_le`'s without `tA ≤ 2^60`.
-/
theorem v7Hash4_zk_circuit_tsec (c : QuadCircuit F) (hnl : c.nl = v7Hash4.params.nl) {L TM : ℕ}
    (hwf : WellFormedP c 5 v7Hash4.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Hash4.params.q v7Hash4.params.nw v7Hash4.params.nq nt)
    {codec : Codec Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash4.params.row) Msg (Fin 5 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash4.params.row.n Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D)
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 5 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Hash4.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (5 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Hash4.params.row) ≤ Fintype.card C)
    (htape : 2 * v7Hash4.params.row.n + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun ω : (Fin TM → D) × (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash4_valid) dom
              (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
              (extOracle nlin nt (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
                v7Hash4_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 :=
  row_tsec (ratio_le_one _)
    (row_zk_deployed_circuit_ratio_leT v7Hash4_valid v7Hash4_openings_pos 5 c hnl hwf hiso hde pub pl dec
      V hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htape hTM hD)
    v7Hash4_zk_slack_bound (by norm_num) v7Hash4_zk_slack_coeff (by norm_num) (by decide) (by decide)
    (by decide)

/--
**`v7Sig`, the deployed v7 signature row, T-secure at `λ = 122`.**  Against one adaptive program making
`tA` Merkle-oracle and `N` deployed hash queries, **with no bound on either**, over a Merkle tape of
any length `TM` with room for the run:

```text
Pr[ AcceptsZkDH  ∧  no lift-list member's committed witness satisfies c ]  ≤  (1 + tA + N) · 2^-122
```

`row_zk_deployed_circuit_ratio_leT` at `CertifiedV1.v7Sig`, with `row_tsec` and the certified slack
numerals `CompiledZk.v7Sig_zk_slack_bound`, `_slack_coeff`.  The premises are
`v7Sig_zk_circuit_ratio_le`'s without `tA ≤ 2^60`.
-/
theorem v7Sig_zk_circuit_tsec (c : QuadCircuit F) (hnl : c.nl = v7Sig.params.nl) {L TM : ℕ}
    (hwf : WellFormedP c 8 v7Sig.params.logw L) (hiso : c.Isolated) (hde : c.DeadEnd)
    (pub : Fin c.ninp → F)
    (pl : Encode.Placement c.ninp M v7Sig.params.q v7Sig.params.nw v7Sig.params.nq nt)
    {codec : Codec Salt (Col F v7Sig.params.nw v7Sig.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Sig.params.row) Msg (Fin 8 → F) M c.ninp L 0)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Sig.params.row.n Salt (Col F v7Sig.params.nw v7Sig.params.nq) D)
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin 8 → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt,
      (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : LigeroV1LayerStep.Qry v7Sig.params.row,
      (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    (hkinit : kinit * Fintype.card F ^ (8 + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C)
    (hkchal : kchal * Fintype.card (ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt)
      ≤ Fintype.card C)
    (hkq : kq * Fintype.card (LigeroV1LayerStep.Qry v7Sig.params.row) ≤ Fintype.card C)
    (htape : 2 * v7Sig.params.row.n + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun ω : (Fin TM → D) × (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds → C) =>
        AcceptsZkDH (nl := v7Sig.params.nl) (w := v7Sig.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Sig_valid) dom
              (Row.hkrow v7Sig_valid) v7Sig_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails (fun κ (ℓ : ZkLigeroV1.Lift (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
              (extOracle nlin nt (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
                v7Sig_openings_pos dec κ)) => c.Satisfied pub (asgOf pl ℓ).1)
            ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 122 :=
  row_tsec (ratio_le_one _)
    (row_zk_deployed_circuit_ratio_leT v7Sig_valid v7Sig_openings_pos 8 c hnl hwf hiso hde pub pl dec
      V hnlin hnt hV hst0 dom respOf body rootOf msgOf claimOf hF kinit kpair k kchal kq hbalInit
      hbalPair hbalF hbalChal hbalQuery hkinit hkpair hk hkchal hkq htape hTM hD)
    v7Sig_zk_slack_bound (by norm_num) v7Sig_zk_slack_coeff (by norm_num) (by decide) (by decide)
    (by decide)

end V7TSec

open Lfzk.NizkAdaptiveTwoField (check2 len2)
open Lfzk.NizkDeployedHashTwoField (Pt2 setup2 sideCtx)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2)
open Lfzk.TwoFieldV1Rows Lfzk.Mac

section V7PairsTSec

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
**Two-field Longfellow at `v7P256Sha1`, as deployed, T-secure at `λ = 115`.**  The v7 `1`-attribute hash
circuit over `GF(2^128)` proved first, then the v7 signature circuit over `P-256`'s base field, on
one Fiat–Shamir transcript with deployed hash inputs, both field halves constructed from the
circuits.  Against one adaptive program making `tA` Merkle-oracle and `N` deployed hash queries,
**with no bound on either**, over a Merkle tape of any length `TM` with room for the run:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT` at `S₁.toSide`, `S₂.toSide`, with
`twofield_tsec` and the pair's certified slack numerals `TwoFieldV1Rows.v7P256Sha1_zk_slack_bound`,
`_slack_coeff`.  The premises are `v7P256Sha1_zk_circuit_ratio_le`'s without `tA ≤ 2^60`.
-/
theorem v7P256Sha1_zk_circuit_tsec {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
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
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha1_valid
  have key := twofield_zk_deployed_ratio_leT (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha1_sha_openings_pos v7P256Sha1_ecdsa_openings_pos S₁.toSide
    S₂.toSide body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM
  have hm : (1 : ℚ) / (v7P256Sha1.macFieldSize : ℚ) = 1 / (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha1_zk_slack_bound
  have hsc := v7P256Sha1_zk_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha2`, as deployed, T-secure at `λ = 115`.**  The v7 `2`-attribute hash
circuit over `GF(2^128)` proved first, then the v7 signature circuit over `P-256`'s base field, on
one Fiat–Shamir transcript with deployed hash inputs, both field halves constructed from the
circuits.  Against one adaptive program making `tA` Merkle-oracle and `N` deployed hash queries,
**with no bound on either**, over a Merkle tape of any length `TM` with room for the run:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT` at `S₁.toSide`, `S₂.toSide`, with
`twofield_tsec` and the pair's certified slack numerals `TwoFieldV1Rows.v7P256Sha2_zk_slack_bound`,
`_slack_coeff`.  The premises are `v7P256Sha2_zk_circuit_ratio_le`'s without `tA ≤ 2^60`.
-/
theorem v7P256Sha2_zk_circuit_tsec {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
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
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha2_valid
  have key := twofield_zk_deployed_ratio_leT (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha2_sha_openings_pos v7P256Sha2_ecdsa_openings_pos S₁.toSide
    S₂.toSide body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM
  have hm : (1 : ℚ) / (v7P256Sha2.macFieldSize : ℚ) = 1 / (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha2_zk_slack_bound
  have hsc := v7P256Sha2_zk_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha3`, as deployed, T-secure at `λ = 115`.**  The v7 `3`-attribute hash
circuit over `GF(2^128)` proved first, then the v7 signature circuit over `P-256`'s base field, on
one Fiat–Shamir transcript with deployed hash inputs, both field halves constructed from the
circuits.  Against one adaptive program making `tA` Merkle-oracle and `N` deployed hash queries,
**with no bound on either**, over a Merkle tape of any length `TM` with room for the run:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT` at `S₁.toSide`, `S₂.toSide`, with
`twofield_tsec` and the pair's certified slack numerals `TwoFieldV1Rows.v7P256Sha3_zk_slack_bound`,
`_slack_coeff`.  The premises are `v7P256Sha3_zk_circuit_ratio_le`'s without `tA ≤ 2^60`.
-/
theorem v7P256Sha3_zk_circuit_tsec {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
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
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha3_valid
  have key := twofield_zk_deployed_ratio_leT (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha3_sha_openings_pos v7P256Sha3_ecdsa_openings_pos S₁.toSide
    S₂.toSide body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM
  have hm : (1 : ℚ) / (v7P256Sha3.macFieldSize : ℚ) = 1 / (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha3_zk_slack_bound
  have hsc := v7P256Sha3_zk_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha4`, as deployed, T-secure at `λ = 115`.**  The v7 `4`-attribute hash
circuit over `GF(2^128)` proved first, then the v7 signature circuit over `P-256`'s base field, on
one Fiat–Shamir transcript with deployed hash inputs, both field halves constructed from the
circuits.  Against one adaptive program making `tA` Merkle-oracle and `N` deployed hash queries,
**with no bound on either**, over a Merkle tape of any length `TM` with room for the run:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

`CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT` at `S₁.toSide`, `S₂.toSide`, with
`twofield_tsec` and the pair's certified slack numerals `TwoFieldV1Rows.v7P256Sha4_zk_slack_bound`,
`_slack_coeff`.  The premises are `v7P256Sha4_zk_circuit_ratio_le`'s without `tA ≤ 2^60`.
-/
theorem v7P256Sha4_zk_circuit_tsec {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
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
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  have hv := v7P256Sha4_valid
  have key := twofield_zk_deployed_ratio_leT (TwoFieldRowV1.sha_valid hv)
    (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha4_sha_openings_pos v7P256Sha4_ecdsa_openings_pos S₁.toSide
    S₂.toSide body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM
  have hm : (1 : ℚ) / (v7P256Sha4.macFieldSize : ℚ) = 1 / (Fintype.card Fmac : ℚ) := by
    rw [hFmac]; rfl
  have hsb := v7P256Sha4_zk_slack_bound
  have hsc := v7P256Sha4_zk_slack_coeff
  rw [hm] at hsb hsc
  -- the event's `¬ ∃ a₁ a₂` is decided by enumeration here (the witnesses are a `Fintype`) and
  -- classically in `key`; `Decidable` is a subsingleton
  exact twofield_tsec (ratio_le_one _) (by convert key using 6) (by positivity) hsb hsc
    (by norm_num) (TwoFieldRowV1.digest_eq hv).symm (by decide) (by decide) (by decide)

end V7PairsTSec

end Lfzk.CompiledZkProfileRows
