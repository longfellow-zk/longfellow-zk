import Lfzk.CertifiedV1

/-!
# A certified V1 row covers every narrower profile

`Lfzk.ProfileMono` for `Lfzk.CertifiedV1.Row`.  `CertifiedV1.Row.nizk_ratio_le_family` is stated
at the row's own width profile: LayerStep's schedule is `Rounds.Role.length nl (fun ly => 2·logw ly)`
and the Ligero witness has `nw` rows.  A circuit whose layers are narrower runs a shorter schedule
over a smaller witness, so the row does not, as stated, say anything about it.  This file proves
that it does: a row certified at `logw` certifies every profile that is pointwise at most `logw` on
the layers `0 … nl-1`, and every smaller input layer, with the same `lam` and no new
`native_decide`.

The headline is `v8Hash_covers`: **every** depth-16 schedule with at most `2^18` wires per layer
and at most `2^18` inputs gets `CertifiedV1.v8Hash`'s `2^-114`.

## Why it holds

`CertifiedV1.Row.Valid` has eight conjuncts.

* Five read only fields `ProfileLe` holds fixed: the Ligero row's validity, `r + q = k`,
  `cardCand = listBound`, the tape room `2n + commitFuel < tape`, and `logc = 0`;
* `CoreRowsNonempty nw nq` reads `nw`, which **does** shrink with the profile.  It survives because
  `nq = ⌈nl/q⌉` does not change and is positive at any row with a layer (`coreRows_of_profile_le`):
  the V3 port had no such conjunct;
* `bound ≤ 2^-lam`: the bound is `|Cand|·((2nl + 2T + 1)/|F| + ligero) + merkle` with
  `T = ∑_{ly < nl} 2·logw ly`.  Only the field density reads the profile, through `T`
  (`nizkBound_le`); the Ligero density is the row's;
* `proofBytes ≤ sizeBound`: `CostV1.Params.proofBytes` is `Cost.Params.proofBytes` at `q := w`, and
  the same monotonicity argument goes through (`proofBytes_le`).

## What "covers" means

As in `ProfileMono`: the soundness theorem quantifies over LayerStep data at schedule `P'.rounds` and a
Ligero instance with `P'.nw` witness rows.  It does not mention gate counts; `profileLe_countParams`
connects them — a circuit whose layer `i` has at most `2 ^ logw i` gates fits the profile
`i ↦ ⌈log₂ x i⌉`, which is `ProfileLe` the row's.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ProfileMonoV1

open Finset Lfzk.CostV1 Lfzk.CertifiedV1

/-! ## The order on parameters -/

/--
**`P'` is `P` at a narrower profile.**  Every field equal except two: the profile may shrink on the
layers the schedule uses (`ly < nl`), and the input-layer column count `ninp` may shrink.  The same
order as `Lfzk.ProfileMono.ProfileLe`, on `CostV1.Params`.
-/
structure ProfileLe (P' P : Params) : Prop where
  row : P'.row = P.row
  q : P'.q = P.q
  nl : P'.nl = P.nl
  logw : ∀ ly < P.nl, P'.logw ly ≤ P.logw ly
  logc : P'.logc = P.logc
  digestBits : P'.digestBits = P.digestBits
  ninp : P'.ninp ≤ P.ninp
  colBytes : P'.colBytes = P.colBytes
  nfullWit : P'.nfullWit = P.nfullWit

namespace ProfileLe

theorem refl (P : Params) : ProfileLe P P :=
  ⟨rfl, rfl, rfl, fun _ _ => le_rfl, rfl, rfl, le_rfl, rfl, rfl⟩

theorem trans {P'' P' P : Params} (h₁ : ProfileLe P'' P') (h₂ : ProfileLe P' P) :
    ProfileLe P'' P :=
  ⟨h₁.row.trans h₂.row, h₁.q.trans h₂.q, h₁.nl.trans h₂.nl,
    fun ly hly => (h₁.logw ly (h₂.nl ▸ hly)).trans (h₂.logw ly hly),
    h₁.logc.trans h₂.logc, h₁.digestBits.trans h₂.digestBits, h₁.ninp.trans h₂.ninp,
    h₁.colBytes.trans h₂.colBytes, h₁.nfullWit.trans h₂.nfullWit⟩

/-- **The usual way in:** replace the profile, pointwise narrower on the schedule's layers. -/
theorem withProfile (P : Params) {logw' : ℕ → ℕ} (h : ∀ ly < P.nl, logw' ly ≤ P.logw ly) :
    ProfileLe { P with logw := logw' } P :=
  ⟨rfl, rfl, rfl, h, rfl, rfl, le_rfl, rfl, rfl⟩

/-- Replace the profile and shrink `ninp`. -/
theorem withProfileInputs (P : Params) {logw' : ℕ → ℕ} {ninp' : ℕ}
    (h : ∀ ly < P.nl, logw' ly ≤ P.logw ly) (hn : ninp' ≤ P.ninp) :
    ProfileLe { P with logw := logw', ninp := ninp' } P :=
  ⟨rfl, rfl, rfl, h, rfl, rfl, hn, rfl, rfl⟩

end ProfileLe

/-! ## What the bound does not read -/

theorem nizkBound_ninp (P : Params) (ninp' cardCand commitFuel T : ℕ) :
    ({ P with ninp := ninp' } : Params).nizkBound cardCand commitFuel T
      = P.nizkBound cardCand commitFuel T := rfl

theorem nizkBound_logc (P : Params) (logc' cardCand commitFuel T : ℕ) :
    ({ P with logc := logc' } : Params).nizkBound cardCand commitFuel T
      = P.nizkBound cardCand commitFuel T := rfl

theorem proofBytes_logc (P : Params) (logc' : ℕ) :
    ({ P with logc := logc' } : Params).proofBytes = P.proofBytes := rfl

/-! ## Monotonicity -/

section Mono

variable {P' P : Params}

theorem sum_range_le {nl : ℕ} {f g : ℕ → ℕ} (h : ∀ ly < nl, f ly ≤ g ly) :
    ∑ ly ∈ range nl, f ly ≤ ∑ ly ∈ range nl, g ly :=
  Finset.sum_le_sum fun ly hly => h ly (mem_range.mp hly)

theorem totalRounds_le (h : ProfileLe P' P) : P'.totalRounds ≤ P.totalRounds := by
  unfold Params.totalRounds Params.rounds
  rw [h.nl]
  exact sum_range_le fun ly hly => Nat.mul_le_mul_left 2 (h.logw ly hly)

theorem fieldDensity_le (h : ProfileLe P' P) : P'.fieldDensity ≤ P.fieldDensity := by
  unfold Params.fieldDensity
  rw [h.nl, h.row]
  have hT := totalRounds_le h
  have hnum : ((P.nl * 2 + P'.totalRounds * 2 + 1 : ℕ) : ℚ)
      ≤ ((P.nl * 2 + P.totalRounds * 2 + 1 : ℕ) : ℚ) := by
    exact_mod_cast (by omega)
  exact div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)

theorem ligeroDensity_eq (h : ProfileLe P' P) : P'.ligeroDensity = P.ligeroDensity := by
  unfold Params.ligeroDensity
  rw [h.row]

theorem merkleTerm_eq (h : ProfileLe P' P) (commitFuel T : ℕ) :
    P'.merkleTerm commitFuel T = P.merkleTerm commitFuel T := by
  unfold Params.merkleTerm
  rw [h.digestBits]

/-- **The composed bound is monotone in the profile.**  Only the field density reads it. -/
theorem nizkBound_le (h : ProfileLe P' P) (cardCand commitFuel T : ℕ) :
    P'.nizkBound cardCand commitFuel T ≤ P.nizkBound cardCand commitFuel T := by
  unfold Params.nizkBound
  rw [merkleTerm_eq h, ligeroDensity_eq h]
  have := fieldDensity_le h
  have hc : (0 : ℚ) ≤ (cardCand : ℚ) := Nat.cast_nonneg _
  nlinarith

theorem padSize_le (h : ProfileLe P' P) : P'.padSize ≤ P.padSize := by
  unfold Params.padSize
  rw [h.nl]
  exact sum_range_le fun ly hly => Nat.add_le_add_right (Nat.mul_le_mul_left 4 (h.logw ly hly)) 3

theorem sumcheckElems_le (h : ProfileLe P' P) : P'.sumcheckElems ≤ P.sumcheckElems := by
  unfold Params.sumcheckElems Params.rounds
  rw [h.nl]
  exact sum_range_le fun ly hly =>
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 (h.logw ly hly))) 2

theorem nw_le (h : ProfileLe P' P) : P'.nw ≤ P.nw := by
  unfold Params.nw
  rw [h.q]
  exact Nat.div_le_div_right (Nat.sub_le_sub_right
    (Nat.add_le_add_right (Nat.add_le_add h.ninp (padSize_le h)) _) 1)

theorem nq_eq (h : ProfileLe P' P) : P'.nq = P.nq := by
  unfold Params.nq
  rw [h.nl, h.q]

theorem nfull_eq (h : ProfileLe P' P) : P'.nfull = P.nfull := by
  unfold Params.nfull
  rw [nq_eq h, h.nfullWit]

theorem colRows_le (h : ProfileLe P' P) : P'.colRows ≤ P.colRows := by
  unfold Params.colRows Lfzk.CostV1.columnFieldCount
  rw [nq_eq h]
  exact Nat.add_le_add_right (Nat.add_le_add_right (nw_le h) _) 5

theorem columnBytes_le (h : ProfileLe P' P) : P'.columnBytes ≤ P.columnBytes := by
  unfold Params.columnBytes
  rw [h.row, nfull_eq h, h.colBytes]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (colRows_le h) _)) _)

/-- **The size model is monotone in the profile and in `ninp`.** -/
theorem proofBytes_le (h : ProfileLe P' P) : P'.proofBytes ≤ P.proofBytes := by
  have hclear : P'.cleartextElems = P.cleartextElems := by
    unfold Params.cleartextElems; rw [h.row]
  have helems : P'.proofElems ≤ P.proofElems := by
    unfold Params.proofElems
    rw [hclear]
    exact Nat.add_le_add_right (sumcheckElems_le h) _
  have hpath : Params.pathDigests P' = Params.pathDigests P := by
    unfold Params.pathDigests; rw [h.row]
  have hnonce : P'.nonceBytes = P.nonceBytes := by
    unfold Params.nonceBytes; rw [h.row]
  unfold Params.proofBytes
  rw [hpath, hnonce]
  have := Nat.mul_le_mul_right Lfzk.CostV1.bytesF helems
  have := columnBytes_le h
  omega

/-- `nq = ⌈nl / q⌉` is positive at a profile with a layer and a positive payload width. -/
theorem nq_pos {P : Params} (hnl : 0 < P.nl) (hq : 0 < P.q) : 0 < P.nq := by
  unfold Params.nq
  exact Nat.div_pos (by omega) hq

/--
**`CoreRowsNonempty` survives the narrowing**, at a profile with a layer.  `nw` may shrink, but
`nq` does not change; and if `nw > 0` then `q > 0` (`nw` is a quotient by `q`), so `nq > 0`.
-/
theorem coreRows_of_profile_le (h : ProfileLe P' P) (hnl : 0 < P.nl)
    (hc : LigeroFamily.CoreRowsNonempty P.nw P.nq) :
    LigeroFamily.CoreRowsNonempty P'.nw P'.nq := by
  unfold LigeroFamily.CoreRowsNonempty at hc ⊢
  rw [nq_eq h]
  rcases hc with hw | hq'
  · right
    refine nq_pos hnl (Nat.pos_of_ne_zero fun hq0 => ?_)
    unfold Params.nw at hw
    rw [hq0, Nat.div_zero] at hw
    exact absurd hw (lt_irrefl 0)
  · exact Or.inr hq'

end Mono

/-! ## Rows -/

namespace Row

variable {R : Row} {P' : Params}

/-- The bound of the row at the narrower profile is at most the row's own. -/
theorem bound_le (hle : ProfileLe P' R.params) :
    ({ R with params := P' } : Row).bound ≤ R.bound :=
  nizkBound_le hle R.cardCand R.commitFuel R.tape

/--
**Validity is inherited by every narrower profile with a layer.**  Five conjuncts read only fields
`ProfileLe` holds fixed; `CoreRowsNonempty` is `coreRows_of_profile_le`; the target is `bound_le`;
the size is `proofBytes_le`.
-/
theorem valid_of_profile_le (h : R.Valid) (hle : ProfileLe P' R.params) (hnl : 0 < R.params.nl) :
    ({ R with params := P' } : Row).Valid := by
  obtain ⟨hrow, hdim, hcand, hcore, hbound, hsize, hroom, hlogc⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show P'.row.Valid
    rw [hle.row]; exact hrow
  · show P'.row.openings + P'.q = P'.row.k
    rw [hle.row, hle.q]; exact hdim
  · show R.cardCand = P'.row.listBound
    rw [hle.row]; exact hcand
  · exact coreRows_of_profile_le hle hnl hcore
  · exact (bound_le hle).trans hbound
  · exact (proofBytes_le hle).trans hsize
  · show 2 * P'.row.n + R.commitFuel < R.tape
    rw [hle.row]; exact hroom
  · show P'.logc = 0
    rw [hle.logc]; exact hlogc

end Row

section Compose

open Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

/--
**`CertifiedV1.Row.nizk_ratio_le_family` at any narrower profile.**  The schedule is `P'`'s — the tape
has `∑ ly, 2·P'.logw ly` sumcheck slots — and the Ligero instance has `P'.nw` witness rows.  The
premises are the family theorem's at the narrowed row `{R with params := P'}`, whose validity is
`Row.valid_of_profile_le`; nothing is re-checked numerically.
-/
theorem Row.nizk_ratio_le_family_of_profile_le {R : Row} (h : R.Valid) {P' : Params}
    (hle : ProfileLe P' R.params) (hnl : 0 < R.params.nl)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n R.commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length P'.nl P'.rounds) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length P'.nl P'.rounds) → C) → Query)
    (statement : (Fin R.tape → D) × (Fin (Rounds.Role.length P'.nl P'.rounds) → C) → Statement)
    {Fails : (Fin R.tape → D) → Prop}
    (hF : Fintype.card F = P'.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F P'.row.openings P'.q P'.row.n)
    (lig : ∀ _pre : Fin R.tape → D,
      LigeroV1LayerStep.Instance P'.row F Equations P'.nw P'.nq P'.q)
    (hfalse : ∀ pre : Fin R.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    (H : ∀ _pre : Fin R.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin R.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin R.tape → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations P'.nw P'.nq)
        (LigeroV1LayerStep.Qry P'.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin R.tape → D, (Ffam pre).Exact)
    (hfail : ∀ pre : Fin R.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin R.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length P'.nl P'.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := P'.nl) (w := P'.rounds) (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting
              (CertifiedV1.Row.rowValid (Row.valid_of_profile_le h hle hnl)) dom
              (CertifiedV1.Row.hkrow (Row.valid_of_profile_le h hle hnl)) (lig pre)))
          tape)
    (ht₁ : R.commitFuel ≤ R.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ R.tape) (hT1 : 1 ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ P'.digestBits) :
    ((univ.filter fun omega : (Fin R.tape → D) × (Fin (Rounds.Role.length P'.nl P'.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin R.tape → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length P'.nl P'.rounds)
      ≤ (1 : ℚ) / 2 ^ R.lam :=
  CertifiedV1.Row.nizk_ratio_le_family (R := { R with params := P' })
    (Row.valid_of_profile_le h hle hnl) dec K A challengeOf queryOf statement hF dom lig hfalse
    H Sat Ffam hexact hfail hright ht₁ hT hT1 hcand hD

/-- **`CertifiedV1.Row.nizk_ratio_le` at any narrower profile**: the constant-`H`, constant-`Sat`
case of `Row.nizk_ratio_le_family_of_profile_le`. -/
theorem Row.nizk_ratio_le_of_profile_le {R : Row} (h : R.Valid) {P' : Params}
    (hle : ProfileLe P' R.params) (hnl : 0 < R.params.nl)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n R.commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length P'.nl P'.rounds) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length P'.nl P'.rounds) → C) → Query)
    (statement : (Fin R.tape → D) × (Fin (Rounds.Role.length P'.nl P'.rounds) → C) → Statement)
    {Fails : (Fin R.tape → D) → Prop}
    (hF : Fintype.card F = P'.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F P'.row.openings P'.q P'.row.n)
    (lig : ∀ _pre : Fin R.tape → D,
      LigeroV1LayerStep.Instance P'.row F Equations P'.nw P'.nq P'.q)
    (hfalse : ∀ pre : Fin R.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    (Ffam : ∀ _pre : Fin R.tape → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations P'.nw P'.nq)
        (LigeroV1LayerStep.Qry P'.row) Cand Witness nc nv logw logc H Sat)
    (hexact : ∀ pre : Fin R.tape → D, (Ffam pre).Exact)
    (hfail : ∀ pre : Fin R.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Fin R.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length P'.nl P'.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := P'.nl) (w := P'.rounds) (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting
              (CertifiedV1.Row.rowValid (Row.valid_of_profile_le h hle hnl)) dom
              (CertifiedV1.Row.hkrow (Row.valid_of_profile_le h hle hnl)) (lig pre)))
          tape)
    (ht₁ : R.commitFuel ≤ R.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ R.tape) (hT1 : 1 ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ P'.digestBits) :
    ((univ.filter fun omega : (Fin R.tape → D) × (Fin (Rounds.Role.length P'.nl P'.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin R.tape → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length P'.nl P'.rounds)
      ≤ (1 : ℚ) / 2 ^ R.lam :=
  Row.nizk_ratio_le_family_of_profile_le h hle hnl dec K A challengeOf queryOf statement hF dom
    lig hfalse (fun _ => H) (fun _ => Sat) Ffam hexact hfail hright ht₁ hT hT1 hcand hD

end Compose

/-! ## From gate counts to a profile

`Lfzk.Cost.Params.Fits` at `CostV1.Params`: layer `i` has at most `2 ^ logw i` gates, and the
Ligero payload holds the padded witness and the per-layer triples. -/

/-- A gate-count vector fits a V1 parameter set. -/
def Fits (P : Params) {d : ℕ} (x : Fin (d + 1) → ℕ) : Prop :=
  d = P.nl ∧ (∀ i : Fin (d + 1), x i ≤ 2 ^ P.logw i.val) ∧
    P.ninp + P.padSize ≤ P.nw * P.q ∧ P.nl ≤ P.nq * P.q

/-- The profile a gate-count vector determines: `⌈log₂ x i⌉` on layers `0 … d`. -/
def countProfile {d : ℕ} (x : Fin (d + 1) → ℕ) : ℕ → ℕ :=
  fun ly => if h : ly < d + 1 then Nat.clog 2 (x ⟨ly, h⟩) else 0

/-- `P` with the profile of the gate counts `x`. -/
def countParams (P : Params) {d : ℕ} (x : Fin (d + 1) → ℕ) : Params :=
  { P with logw := countProfile x }

/-- The ceiling quotient covers its numerator: `a ≤ ⌈a/q⌉·q` for `0 < q`. -/
theorem le_ceilDiv_mul (a : ℕ) {q : ℕ} (hq : 0 < q) : a ≤ (a + q - 1) / q * q := by
  have hdm := Nat.div_add_mod (a + q - 1) q
  have hmod := Nat.mod_lt (a + q - 1) hq
  rw [Nat.mul_comm] at hdm
  generalize (a + q - 1) / q * q = D at hdm ⊢
  generalize (a + q - 1) % q = M at hdm hmod
  omega

/--
**Every circuit under the row's widths gets its own profile.**  If layer `i` has at most
`2 ^ P.logw i` gates (and `d = P.nl`, `0 < P.q`), then `countParams P x` is `ProfileLe P` and fits
`x`.
-/
theorem profileLe_countParams (P : Params) {d : ℕ} (x : Fin (d + 1) → ℕ) (hd : d = P.nl)
    (hq : 0 < P.q) (hx : ∀ i : Fin (d + 1), x i ≤ 2 ^ P.logw i.val) :
    ProfileLe (countParams P x) P ∧ Fits (countParams P x) x := by
  refine ⟨ProfileLe.withProfile P fun ly hly => ?_, hd, fun i => ?_, ?_, ?_⟩
  · have hly' : ly < d + 1 := by omega
    simp only [countProfile, dif_pos hly']
    exact Nat.clog_le_of_le_pow (hx ⟨ly, hly'⟩)
  · show x i ≤ 2 ^ countProfile x i.val
    simp only [countProfile, dif_pos i.isLt]
    exact Nat.le_pow_clog (by norm_num) _
  · exact le_ceilDiv_mul _ hq
  · exact le_ceilDiv_mul _ hq

/-! ## The v8 hash row covers every narrower schedule -/

section V8Hash

open Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

/-- `v8Hash`'s order: `ProfileLe P' v8Hash.params` is exactly "the same Ligero row and
payload, twenty layers, each no wider than the deployed hash circuit's, at most `85733` inputs". -/
theorem v8Hash_profileLe {logw' : ℕ → ℕ} {ninp' : ℕ}
    (hw : ∀ ly < 20, logw' ly ≤ v8Hash.params.logw ly) (hn : ninp' ≤ 85733) :
    ProfileLe { v8Hash.params with logw := logw', ninp := ninp' } v8Hash.params :=
  ProfileLe.withProfileInputs _ hw hn

/-- **Every narrower row is valid at `2^-114`**, with no new `native_decide`. -/
theorem v8Hash_valid_of_profile_le {P' : Params} (hle : ProfileLe P' v8Hash.params) :
    ({ v8Hash with params := P' } : Row).Valid ∧ v8Hash.lam = 114 :=
  ⟨Row.valid_of_profile_le v8Hash_valid hle (by decide), rfl⟩

/--
**`v8Hash` covers every 20-layer circuit no wider than the deployed hash circuit.**

`CertifiedV1.v8Hash_nizk_ratio_le` at the schedule of any profile `P'` that is `ProfileLe`
`v8Hash.params` — twenty layers, each no wider than the deployed 4-attribute hash circuit's, at
most `85733` inputs, same Ligero row (132 openings over `GF(2^128)`), same payload width.  The
1-, 2- and 3-attribute hash circuits are such profiles.  The bound is the row's `2^-114`; the
premises are `Row.nizk_ratio_le_of_profile_le`'s, i.e. `CertifiedV1.Row.nizk_ratio_le`'s at `P'`.
-/
theorem v8Hash_covers {P' : Params} (hle : ProfileLe P' v8Hash.params)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n v8Hash.commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length P'.nl P'.rounds) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length P'.nl P'.rounds) → C) → Query)
    (statement : (Fin v8Hash.tape → D) × (Fin (Rounds.Role.length P'.nl P'.rounds) → C) →
      Statement)
    {Fails : (Fin v8Hash.tape → D) → Prop}
    (hF : Fintype.card F = P'.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F P'.row.openings P'.q P'.row.n)
    (lig : ∀ _pre : Fin v8Hash.tape → D,
      LigeroV1LayerStep.Instance P'.row F Equations P'.nw P'.nq P'.q)
    (hfalse : ∀ pre : Fin v8Hash.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    (Ffam : ∀ _pre : Fin v8Hash.tape → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations P'.nw P'.nq)
        (LigeroV1LayerStep.Qry P'.row) Cand Witness nc nv logw logc H Sat)
    (hexact : ∀ pre : Fin v8Hash.tape → D, (Ffam pre).Exact)
    (hfail : ∀ pre : Fin v8Hash.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Fin v8Hash.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length P'.nl P'.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n v8Hash.commitFuel (revealFuel + respondFuel)
            v8Hash.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := P'.nl) (w := P'.rounds) (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting
              (CertifiedV1.Row.rowValid (Row.valid_of_profile_le v8Hash_valid hle (by decide)))
              dom
              (CertifiedV1.Row.hkrow (Row.valid_of_profile_le v8Hash_valid hle (by decide)))
              (lig pre)))
          tape)
    (ht₁ : v8Hash.commitFuel ≤ v8Hash.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v8Hash.commitFuel ≤ v8Hash.tape)
    (hT1 : 1 ≤ v8Hash.tape)
    (hcand : Fintype.card Cand = v8Hash.cardCand)
    (hD : Fintype.card D = 2 ^ P'.digestBits) :
    ((univ.filter fun omega : (Fin v8Hash.tape → D) ×
          (Fin (Rounds.Role.length P'.nl P'.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v8Hash.tape → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length P'.nl P'.rounds)
      ≤ (1 : ℚ) / 2 ^ 114 :=
  Row.nizk_ratio_le_of_profile_le v8Hash_valid hle (by decide) dec K A challengeOf queryOf
    statement hF dom lig hfalse Ffam hexact hfail hright ht₁ hT hT1 hcand hD

/-- **Gate counts in.**  A 20-layer circuit whose twenty-one layers (`Fits`' `d + 1 = 21`) each
fit the deployed hash circuit's widths fits its own profile, which is `ProfileLe v8Hash.params`; so
`v8Hash_covers` applies at that profile. -/
theorem v8Hash_countParams (x : Fin 21 → ℕ) (hx : ∀ i, x i ≤ 2 ^ v8Hash.params.logw i.val) :
    ProfileLe (countParams v8Hash.params x) v8Hash.params ∧
      Fits (countParams v8Hash.params x) x :=
  profileLe_countParams v8Hash.params x rfl (by decide) hx

end V8Hash

/-! ## Non-vacuity of the order at the row

A strictly narrower profile: every layer at half its width exponent and the input layer at `2^12`.
`ProfileLe` holds with strict narrowing, and `v8Hash_valid_of_profile_le` gives its validity with
no new `native_decide`. -/

/-- The narrowed profile. -/
def v8HashNarrow : Params :=
  { v8Hash.params with logw := fun ly => v8Hash.params.logw ly / 2, ninp := 2 ^ 12 }

theorem v8HashNarrow_le : ProfileLe v8HashNarrow v8Hash.params :=
  v8Hash_profileLe (fun ly _ => Nat.div_le_self _ _) (by norm_num)

/-- The narrowing is strict on a layer the schedule uses. -/
theorem v8HashNarrow_strict :
    ∃ ly < v8Hash.params.nl, v8HashNarrow.logw ly < v8Hash.params.logw ly :=
  ⟨4, by decide, by decide⟩

theorem v8HashNarrow_valid : ({ v8Hash with params := v8HashNarrow } : Row).Valid :=
  (v8Hash_valid_of_profile_le v8HashNarrow_le).1

/-- The narrowed schedule is shorter: `294` sumcheck slots against the row's `610`. -/
theorem v8HashNarrow_totalRounds :
    v8HashNarrow.totalRounds = 294 ∧ v8Hash.params.totalRounds = 610 := by
  native_decide

end Lfzk.ProfileMonoV1
