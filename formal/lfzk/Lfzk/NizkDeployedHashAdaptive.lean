import Lfzk.NizkDeployedHash
import Lfzk.CompiledLongfellowAdaptive
import Bcs.TotalOracleCommit

/-!
# The re-committing Longfellow prover, with Fiat–Shamir hash inputs as deployed

`Lfzk.NizkAdaptive` and `Lfzk.CompiledLongfellowAdaptive` bound a prover that interleaves
Merkle-oracle and challenge-oracle queries and may re-commit any number of times, with hash inputs
`NizkGrinding.Point` that carry the raw earlier answers.  Here the hash inputs are the deployed ones,
`NizkDeployedHash.MPoint` (root, role, messages through the round — **no challenge**), and the
challenge oracle is the total random oracle on them (`Bcs.TotalOracleCommit`), so `N` counts deployed
hash queries.  The idealisation and the remaining transliteration debt are those of
`Lfzk.NizkDeployedHash`'s module docstring.

## What is proved

* `lfSetup` — the deployed reading: round `k` hashes `msgPoint (rootOf out) msgOf out k`, a point
  names its root.  `JointAccepts` — the compiled verifier on `(mt, ro)`: the Merkle opening under the
  run's Merkle oracle and the IPCP verifier at the challenges `ro (msgPoint … k)`.
* `row_adaptive_ratio_le` — at any certified V1 row:

```text
Pr[ JointAccepts ∧ Fails(context of the proof's root) ]
    ≤  R.bound  +  N · R.fsCoefficient  +  R.tape · (L + N) / 2^digestBits
```

  the right-hand side of `CertifiedV1.Row.adaptive_ratio_le`, with `N` the prover's deployed
  (message-prefix) challenge queries.  `adaptive_rhs_le_bits` turns certified slack at a row into
  `2^-a + N · 2^-b`; `v8Hash_adaptive_ratio_le`: `≤ 2^-114 + N · 2^-115`.
* `AcceptsAt`, `hright_v1`, `row_adaptive_ratio_le_v1`, `v8Hash_adaptive_compiled_ratio_le` — the same
  at the **compiled Longfellow verifier** of `Lfzk.CompiledLongfellowAdaptive` (Merkle opening, V1's
  policy on the opened columns at the decoded challenge and query, the proof's own response, the field
  rounds' `FieldPass`), with `hlig` and `hright` theorems: `≤ 2^-114 + N · 2^-115` at `v8Hash`.

## What is still a hypothesis

Those of `CompiledLongfellowAdaptive.row_adaptive_ratio_le_v1`: the protocol instance (field,
domain, fuels, `|D|`, `|Cand|`), `Matches`, `hfalse`, `hfail`; plus the finiteness of the message
type (`Fintype Msg`), which makes the oracle a finite sample space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkDeployedHashAdaptive

open Finset Bcs Bcs.TotalOracleCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkDeployedHash
open scoped Classical

/-! ## 1. The verifier's reading of a re-committing prover -/

section Reading

variable {Enc D Msg C Out : Type} {nl : ℕ} {w : ℕ → ℕ} {tA N : ℕ} [Inhabited Msg] [Nonempty C]

/-- **The deployed reading**: round `k` hashes the proof's root, the role and the proof's messages
through round `k` — no challenge; a point names its root. -/
noncomputable def lfSetup (body : TwoOracleTree Enc D (MPoint D Msg nl w) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg) :
    TotalOracleCommit.Setup Enc D (MPoint D Msg nl w) C Out D tA N (Rounds.Role.length nl w) where
  body := body
  hashInput out := msgPoint (rootOf out) msgOf out
  dflt := Classical.arbitrary C
  key := MPoint.ctx
  keyOut := rootOf
  hkey _ _ := rfl

end Reading

/-! ## 2. The compiled verifier on `(mt, ro)` -/

section Accepts

variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N L TM fc : ℕ}
variable {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
variable {Salt M : Type} {n : ℕ}

/-- **The compiled verifier on `(mt, ro)`**: the opened set is the queried one, the Merkle opening
reconstructs the proof's root under the run's Merkle oracle, and the IPCP verifier accepts the opened
leaves, at the challenge and query decoded from the verifier's challenges `S.challenges mt ro`. -/
def JointAccepts (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (codec : Codec Salt M D Enc) (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D)
    (claimOf : Out → OpeningClaim n Salt M D) (statementOf : Out → (Fin L → C) → Statement)
    (responseOf : Out → Response) (challengeOf : Out → (Fin L → C) → Challenge)
    (queryOf : Out → (Fin L → C) → Query) (mt : Fin TM → D) (ro : Pt → C) : Prop :=
  K.Accepts (codec.withOracle (S.merkleOracle check mt ro))
    (statementOf (S.proof mt ro) (S.challenges mt ro))
    (rootOf (S.proof mt ro)) (challengeOf (S.proof mt ro) (S.challenges mt ro))
    (responseOf (S.proof mt ro)) (queryOf (S.proof mt ro) (S.challenges mt ro))
    (claimOf (S.proof mt ro))

end Accepts

/-! ## 3. At a certified V1 row -/

section Row

open Lfzk.CertifiedV1

/--
**A certified V1 row against a re-committing prefix-only Fiat–Shamir prover.**

Over the Merkle tape (`R.tape` slots) and the random oracle on message prefixes, against a prover
`body` that interleaves at most `tA` Merkle-oracle and `N` challenge-oracle queries:

```text
Pr[ JointAccepts  ∧  Fails(context of the proof's root) ]
    ≤  R.bound  +  N · R.fsCoefficient  +  R.tape · (L + N) / 2^digestBits
```

`CertifiedV1.Row.adaptive_ratio_le`'s right-hand side, with `N` counting deployed hash queries.  The
premises are that theorem's, with the context, proof and challenges those of the deployed reading
`lfSetup` on `(mt, ro)`.
-/
theorem row_adaptive_ratio_le {R : Row} (h : R.Valid)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    -- the prover, and the verifier's reading of its proof
    (body : TwoOracleTree Enc D (MPoint D Msg R.params.nl R.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D)
    (statementOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    {Fails : D × List (Enc × D) → Prop}
    -- the Ligero half of LayerStep, per commitment context
    (hF : Fintype.card F = R.params.row.fieldSize)
    (accR : ∀ _κ : D × List (Enc × D), ∀ m : ℕ, (Fin m → C) → Msg →
      LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq →
        Finset (LigeroV1LayerStep.Qry R.params.row))
    (hlig : ∀ κ, Fails κ →
      ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq → Prop)
        (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
          (LigeroV1LayerStep.Qry R.params.row) Msg LigDoomed),
        ML.accepting = accR κ ∧
        (ML.escaping.card : ℚ) ≤ (R.params.row.fail + R.params.row.arith)
          * Fintype.card (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq) ∧
        ML.bq = LigeroV1LayerStep.queryCount R.params.row)
    -- the field half of LayerStep, per commitment context
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    -- extraction, and acceptance
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (hright : ∀ (mt : Fin R.tape → D) (ro : MPoint D Msg R.params.nl R.params.rounds → C),
      Fails ((lfSetup body rootOf msgOf).context mt ro) →
      JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
        claimOf statementOf responseOf challengeOf queryOf mt ro →
      (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds)
          (withMsgs (Ffam ((lfSetup body rootOf msgOf).context mt ro))
            (MD ((lfSetup body rootOf msgOf).context mt ro))
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
          (fun m pref => accR ((lfSetup body rootOf msgOf).context mt ro) m pref
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro) m)))
        ((lfSetup body rootOf msgOf).challenges mt ro))
    -- the prover's Merkle budget and the Merkle tape
    (htA : tA ≤ R.commitFuel) (htape : 2 * n + tA ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (MPoint D Msg R.params.nl R.params.rounds → C) =>
        JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg R.params.nl R.params.rounds))
      ≤ R.bound + N * R.fsCoefficient
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  set S := lfSetup body rootOf msgOf with hS
  -- the Ligero half, in each failing context
  choose LigD ML hacc hesc hbq using hlig
  have hFpos : 0 < R.params.row.fieldSize := by rw [← hF]; exact Fintype.card_pos
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have ep : 2 * Fintype.card C / Fintype.card F
      = pairBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]; rfl
  have ei : Fintype.card C / Fintype.card F
      = inBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]; rfl
  set bp := pairBudget (Fintype.card C) R.params.row.fieldSize
  set bi := inBudget (Fintype.card C) R.params.row.fieldSize
  set bl := ligBudget R.params.row (Fintype.card C)
  set bq := queryBudget R.params.row (Fintype.card C)
  have hB : ∀ (κ : D × List (Enc × D)) (hκ : Fails κ),
      MsgBudgets (Ffam κ) (ML κ hκ) bp bp bi bl bq := by
    intro κ hκ
    obtain ⟨hp0, hp1, hr, hi⟩ := (hexact κ).field_budgets
    obtain ⟨-, -, hchal, hqq⟩ := hexact κ
    refine ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
        (LigeroV1LayerStep.arith_nonneg _)) (hesc κ hκ) hchal, ?_⟩
    rw [hbq κ hκ]
    exact LigeroV1LayerStep.queryBudget_le hqq
  -- the bad event at a point, in a context, at its ancestors' answers
  obtain ⟨Bad, hBad⟩ : ∃ Bad : D × List (Enc × D) →
      (x : MPoint D Msg R.params.nl R.params.rounds) →
        (Fin ((mpoints (Ctx := D) (Msg := Msg)).slot x) → C) → C → Prop,
      Bad = fun κ x pref c => ∃ hκ : Fails κ,
        (layerStep (nl := R.params.nl) (w := R.params.rounds) (Ffam κ) (MD κ) (ML κ hκ)
            x.msgFn).doomed ((mpoints (Ctx := D) (Msg := Msg)).slot x) pref ∧
          ¬ (layerStep (nl := R.params.nl) (w := R.params.rounds) (Ffam κ) (MD κ) (ML κ hκ)
            x.msgFn).doomed ((mpoints (Ctx := D) (Msg := Msg)).slot x + 1) (Bcs.extend pref c) :=
    ⟨_, rfl⟩
  let beta : MPoint D Msg R.params.nl R.params.rounds → ℕ := fun q =>
    Fintype.card Cand * RbrLayerStep.classBudget (nl := R.params.nl) (w := R.params.rounds)
      bp bp bi bl bq q.role
  have hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x := by
    intro κ x pref
    by_cases hκ : Fails κ
    · by_cases hd : (layerStep (nl := R.params.nl) (w := R.params.rounds) (Ffam κ) (MD κ)
          (ML κ hκ) x.msgFn).doomed ((mpoints (Ctx := D) (Msg := Msg)).slot x) pref
      · have hpres := (layerStepRbr (nl := R.params.nl) (w := R.params.rounds) (Ffam κ) (MD κ)
          (ML κ hκ) (hB κ hκ) (Fails := False) False.elim x.msgFn).doom_preserved x.role.index
          pref hd
        rw [show (layerStepRbr (nl := R.params.nl) (w := R.params.rounds) (Ffam κ) (MD κ) (ML κ hκ)
            (hB κ hκ) (Fails := False) False.elim x.msgFn).beta x.role.index
            = Fintype.card Cand * RbrLayerStep.classBudget (nl := R.params.nl) (w := R.params.rounds)
                bp bp bi bl bq (Rounds.Role.indexEquiv.symm x.role.index) from rfl,
          indexEquiv_symm_index] at hpres
        refine le_trans (Finset.card_le_card ?_) hpres
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad] at hc ⊢
        obtain ⟨_, _, he⟩ := hc
        exact he
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad] at hc
        obtain ⟨_, hd', _⟩ := hc
        exact absurd hd' hd
    · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, hBad] at hc
      obtain ⟨hκ', _⟩ := hc
      exact absurd hκ' hκ
  set βmax := Fintype.card Cand * NizkGrinding.maxBudget bp bp bi bl bq with hβmax
  have hmax : ∀ q, beta q ≤ βmax := fun q => Nat.mul_le_mul_left _ (classBudget_le_max q.role)
  let slotBeta : Fin (Rounds.Role.length R.params.nl R.params.rounds) → ℕ := fun i =>
    Fintype.card Cand * RbrLayerStep.classBudget (nl := R.params.nl) (w := R.params.rounds)
      bp bp bi bl bq (Rounds.Role.indexEquiv.symm i)
  have hslot : ∀ (out : Out) (i : Fin (Rounds.Role.length R.params.nl R.params.rounds)),
      beta (S.hashInput out i.val) ≤ slotBeta i := by
    intro out i
    show Fintype.card Cand * RbrLayerStep.classBudget (nl := R.params.nl) (w := R.params.rounds)
        bp bp bi bl bq (roleAt i.val) ≤ _
    rw [roleAt_val]
  have hsum : ∑ i, slotBeta i
      = Fintype.card Cand * (R.params.nl * bp
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi + bl + bq) := by
    rw [← Finset.mul_sum, RbrLayerStep.layerStep_budget_sum]
  -- the chain, from LayerStep's sequential state function at the proof's messages
  have hchain : ∀ (mt : Fin R.tape → D) (ro : MPoint D Msg R.params.nl R.params.rounds → C),
      JointAccepts K codec S (NizkAdaptive.lfCheck codec claimOf) rootOf claimOf statementOf
        responseOf challengeOf queryOf mt ro →
      S.Explains dec id claimOf mt ro → Fails (S.context mt ro) →
      (S.grinding mt mpoints Bad beta hbad).RoundBad ro := by
    intro mt ro hacc' hexp hκ
    set κ := S.context mt ro with hκdef
    set out := S.proof mt ro with hout
    have hlayerStep := hright mt ro hκ hacc' hexp
    rw [← hacc κ hκ] at hlayerStep
    let hR := layerStepRbr (nl := R.params.nl) (w := R.params.rounds) (Ffam κ) (MD κ) (ML κ hκ)
      (hB κ hκ) (Fails := Fails κ) (hfail κ) (msgOf out)
    obtain ⟨k, hd, he⟩ := hR.exists_escape (S.challenges mt ro) (hR.doomed_start hκ _)
      (hR.accepts_undoomed _ hlayerStep)
    have hsh := shed_at_msgPoint (Ffam κ) (MD κ) (ML κ hκ) (rootOf out) msgOf out ro k hd he
    refine ⟨k, ?_⟩
    rw [S.grinding_ctx_point mt mpoints Bad beta hbad ro k.val,
      S.grinding_point mt mpoints Bad beta hbad ro k.val]
    subst hBad
    exact ⟨hκ, hsh⟩
  -- the generic count
  have hgen := S.ratio_le codec dec (NizkAdaptive.lfCheck codec claimOf) id claimOf
    (NizkAdaptive.lfCheck_trace codec claimOf) mpoints Bad beta hbad βmax hmax slotBeta hslot
    (length_pos R) (by omega) htape (by have := Row.fuel_room h; omega)
    (fun mt ro => JointAccepts K codec S (NizkAdaptive.lfCheck codec claimOf) rootOf claimOf
      statementOf responseOf challengeOf queryOf mt ro) Fails (fun mt ro hacc' => hacc'.2.1) hchain
  refine le_trans hgen ?_
  -- the densities
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hseq := budgets_le_bound R hCpos hFpos (cardCand := Fintype.card Cand) hD
  have hmaxd := maxBudget_le_density R hCpos hFpos
  have hnum := NizkAdaptive.adaptiveNumerator_le
    (Lfs := Rounds.Role.length R.params.nl R.params.rounds + N) htA htape
  have hDq : (Fintype.card D : ℚ) = 2 ^ R.params.digestBits := by rw [hD]; push_cast; rfl
  have hDpos : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast Fintype.card_pos
  have hnumq : (AdaptiveCommit.adaptiveNumerator (2 * n) tA
        (Rounds.Role.length R.params.nl R.params.rounds + N) : ℚ) / (Fintype.card D : ℚ)
      ≤ (merkleNumerator R.commitFuel R.tape : ℚ) / (Fintype.card D : ℚ)
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
    rw [← hDq, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum) hDpos.le
  rw [hsum]
  have hsplit : ((N * βmax + Fintype.card Cand * (R.params.nl * bp
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi + bl + bq) : ℕ) : ℚ)
        / (Fintype.card C : ℚ)
      = ((Fintype.card Cand * (R.params.nl * bp
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi + bl + bq) : ℕ) : ℚ)
          / (Fintype.card C : ℚ)
        + (Fintype.card Cand : ℚ) * N
          * ((NizkGrinding.maxBudget bp bp bi bl bq : ℚ) / (Fintype.card C : ℚ)) := by
    rw [hβmax]
    push_cast
    field_simp
    ring
  have hβ : (NizkGrinding.maxBudget bp bp bi bl bq : ℚ) / (Fintype.card C : ℚ) ≤ R.maxDensity := by
    rw [div_le_iff₀ hc]
    linarith
  rw [hsplit]
  have hbound : R.bound = R.params.nizkBound (Fintype.card Cand) R.commitFuel R.tape := by
    rw [hcand]; rfl
  have hcoef : R.fsCoefficient = (Fintype.card Cand : ℚ) * R.maxDensity := by
    unfold Row.fsCoefficient; rw [hcand]
  rw [hbound, hcoef]
  have hNcand : (0 : ℚ) ≤ (Fintype.card Cand : ℚ) * N := by positivity
  have := mul_le_mul_of_nonneg_left hβ hNcand
  nlinarith [hseq, hnumq, this]

/-- **At certified bit levels.**  If a row's sequential bound plus the re-commitment term of the
`L` recomputed rounds is at most `2^-a`, and its coefficient plus one root target per query is at most
`2^-b`, the adaptive right-hand side is at most `2^-a + N · 2^-b`.  With `row_adaptive_ratio_le` and
`row_adaptive_ratio_le_v1` this instantiates a new row in one line. -/
theorem adaptive_rhs_le_bits (R : Row) {a b : ℕ}
    (ha : R.bound + ((R.tape * Rounds.Role.length R.params.nl R.params.rounds : ℕ) : ℚ)
        / 2 ^ R.params.digestBits ≤ (1 : ℚ) / 2 ^ a)
    (hb : R.fsCoefficient + (R.tape : ℚ) / 2 ^ R.params.digestBits ≤ (1 : ℚ) / 2 ^ b) (N : ℕ) :
    R.bound + N * R.fsCoefficient
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits
      ≤ (1 : ℚ) / 2 ^ a + N * ((1 : ℚ) / 2 ^ b) := by
  have hsplit : ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ R.params.digestBits
      = ((R.tape * Rounds.Role.length R.params.nl R.params.rounds : ℕ) : ℚ)
          / 2 ^ R.params.digestBits
        + N * ((R.tape : ℚ) / 2 ^ R.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hb hN
  nlinarith

/--
**The v8 hash row against a re-committing prefix-only Fiat–Shamir prover.**

`row_adaptive_ratio_le` at `CertifiedV1.v8Hash`:

```text
Pr[ JointAccepts  ∧  Fails(context of the proof's root) ]  ≤  2^-114  +  N · 2^-115
```

with `N` the number of deployed hash queries; the numerals of `CertifiedV1.v8Hash_adaptive_ratio_le`.
-/
theorem v8Hash_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (MPoint D Msg v8Hash.params.nl v8Hash.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D)
    (statementOf : Out → (Fin (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds) → C)
      → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds)
      → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds)
      → C) → Query)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v8Hash.params.row.fieldSize)
    (accR : ∀ _κ : D × List (Enc × D), ∀ m : ℕ, (Fin m → C) → Msg →
      LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq →
        Finset (LigeroV1LayerStep.Qry v8Hash.params.row))
    (hlig : ∀ κ, Fails κ →
      ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq → Prop)
        (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
          (LigeroV1LayerStep.Qry v8Hash.params.row) Msg LigDoomed),
        ML.accepting = accR κ ∧
        (ML.escaping.card : ℚ) ≤ (v8Hash.params.row.fail + v8Hash.params.row.arith)
          * Fintype.card (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq) ∧
        ML.bq = LigeroV1LayerStep.queryCount v8Hash.params.row)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
        (LigeroV1LayerStep.Qry v8Hash.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (hright : ∀ (mt : Fin v8Hash.tape → D)
        (ro : MPoint D Msg v8Hash.params.nl v8Hash.params.rounds → C),
      Fails ((lfSetup body rootOf msgOf).context mt ro) →
      JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
        claimOf statementOf responseOf challengeOf queryOf mt ro →
      (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v8Hash.params.nl) (w := v8Hash.params.rounds)
          (withMsgs (Ffam ((lfSetup body rootOf msgOf).context mt ro))
            (MD ((lfSetup body rootOf msgOf).context mt ro))
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
          (fun m pref => accR ((lfSetup body rootOf msgOf).context mt ro) m pref
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro) m)))
        ((lfSetup body rootOf msgOf).challenges mt ro))
    (htA : tA ≤ v8Hash.commitFuel) (htape : 2 * n + tA ≤ v8Hash.tape)
    (hcand : Fintype.card Cand = v8Hash.cardCand)
    (hD : Fintype.card D = 2 ^ v8Hash.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v8Hash.tape → D) × (MPoint D Msg v8Hash.params.nl v8Hash.params.rounds → C) =>
        JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v8Hash.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v8Hash.params.nl v8Hash.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) :=
  le_trans (row_adaptive_ratio_le v8Hash_valid dec K body rootOf msgOf claimOf statementOf
      responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright htA htape hcand hD)
    (adaptive_rhs_le_bits v8Hash v8Hash_adaptive_slack_bound v8Hash_adaptive_slack_coeff N)

end Row

/-! ## 4. The compiled Longfellow verifier -/

section Verifier

open Lfzk.CompiledLongfellow (Code FieldPass ligIdx qryIdx guarded)
open Lfzk.CompiledLongfellowAdaptive (statementOfAt challengeOfAt queryOfAt responseOfAt
  accepts_guarded)

variable {C F X Q Msg : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {logw logc nl : ℕ} {w : ℕ → ℕ}
variable {Out Statement Resp : Type} {L : ℕ}
variable {Enc D Salt Pt Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N TM fc : ℕ}
variable {Oracle M : Type} {Opening : Q → Type} {n : ℕ}

/--
**The compiled Longfellow verifier on `(mt, ro)`**, as `CompiledLongfellowAdaptive.AcceptsAt` with
the verifier's challenges read at the deployed hash inputs: with the proof `out = S.proof mt ro` and
the challenges `chals = S.challenges mt ro` (round `k`'s is `ro` at round `k`'s message prefix),

* LayerStep's field rounds pass on `out`'s messages at the tape `sl chals` (`FieldPass`), and
* `K`'s compiled verifier accepts under the run's Merkle oracle on the statement `stmtOf out chals`,
  at the decoded Ligero challenge and query, with the proof's response read from its query-round
  message.
-/
def AcceptsAt (K : Compiler Statement Oracle X Resp Q Opening M n) (V : Code C F X Q Msg logw logc)
    (codec : Codec Salt M D Enc) (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D) (stmtOf : Out → (Fin L → C) → Statement)
    (respOf : Msg → Resp) (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C)
    (mt : Fin TM → D) (ro : Pt → C) : Prop :=
  FieldPass V (msgOf (S.proof mt ro)) (sl (S.challenges mt ro)) ∧
    K.Accepts (codec.withOracle (S.merkleOracle check mt ro))
      (stmtOf (S.proof mt ro) (S.challenges mt ro)) (rootOf (S.proof mt ro))
      (V.decodeChal (sl (S.challenges mt ro) ligIdx))
      (respOf (msgOf (S.proof mt ro) (Rounds.Role.layerBase w nl + 2)))
      (V.decodeQuery (sl (S.challenges mt ro) qryIdx)) (claimOf (S.proof mt ro))

omit [Fintype C] [Fintype F] [DecidableEq X] [Fintype Q] in
/-- **`AcceptsAt` is `guarded K`'s joint acceptance** at the verifier's statement, response,
challenge and query maps. -/
theorem acceptsAt_iff_joint (K : Compiler Statement Oracle X Resp Q Opening M n)
    (V : Code C F X Q Msg logw logc) (codec : Codec Salt M D Enc)
    (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N L) (check : Out → Tree Enc D Unit fc)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg) (claimOf : Out → OpeningClaim n Salt M D)
    (stmtOf : Out → (Fin L → C) → Statement) (respOf : Msg → Resp)
    (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C) (mt : Fin TM → D) (ro : Pt → C) :
    AcceptsAt (nl := nl) (w := w) K V codec S check rootOf msgOf claimOf stmtOf respOf sl mt ro ↔
      JointAccepts (guarded K) codec S check rootOf claimOf (statementOfAt V msgOf stmtOf sl)
        (responseOfAt nl w respOf msgOf) (challengeOfAt V sl) (queryOfAt V sl) mt ro := by
  unfold JointAccepts AcceptsAt statementOfAt
  rw [accepts_guarded, decide_eq_true_iff]
  rfl

end Verifier

section V1

open Lfzk.LigeroV1Rows
open Lfzk.CompiledLongfellow (Code Col guarded v1K Matches stepsOf_withMsgs_eq layerStepAccepts_iff)
open Lfzk.CompiledLongfellowAdaptive (statementOfAt challengeOfAt queryOfAt responseOfAt
  accepts_guarded mem_acceptingR_of_accepts rootStatement accR)

variable {C F Equations Msg : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
variable {logw logc nl : ℕ} {w : ℕ → ℕ} {row : Row} {nw nq qw : ℕ}
variable {Enc D Salt Out Cand Witness : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc]
  [Inhabited Salt] [DecidableEq Msg] [Inhabited Msg]
variable {nc nv tA N TM : ℕ}

omit [DecidableEq C] in
/--
**`hright`, proved for the compiled Longfellow verifier against a re-committing prefix-only prover.**

From the guarded joint acceptance, the guard is `FieldPass` and the V1 part puts the drawn query in
the extracted instance's test at the proof's response (`mem_acceptingR_of_accepts`); with LayerStep
data matching the verifier these are LayerStep's acceptance.  The proof of
`CompiledLongfellowAdaptive.hright_v1`, unchanged: nothing in it reads how challenges are hashed.
-/
theorem hright_v1 (h : row.Valid) (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (Col F nw nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations nw nq) (LigeroV1LayerStep.Qry row) Msg
      logw logc)
    (body : TwoOracleTree Enc D (MPoint D Msg nl w) C Out tA N) (rootOf : Out → D)
    (msgOf : Out → ℕ → Msg) (claimOf : Out → OpeningClaim row.n Salt (Col F nw nq) D)
    (stmt : D → LigeroFamily.ConstraintSystem F nw nq qw Equations)
    (respOf : Msg → LigeroFamily.Response F row.openings qw row.n 1)
    {H : Honest F Cand logw logc} {Sat : Cand → Prop}
    (FD : RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations nw nq)
      (LigeroV1LayerStep.Qry row) Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) (hm : Matches V FD MD) (mt : Fin TM → D)
    (ro : MPoint D Msg nl w → C)
    (hacc : JointAccepts (guarded (v1K (Equations := Equations) (nw := nw) (nq := nq) h dom hkrow hr))
      codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf claimOf
      (statementOfAt V msgOf (rootStatement rootOf stmt) id) (responseOfAt nl w respOf msgOf)
      (challengeOfAt V id) (queryOfAt V id) mt ro)
    (hexp : (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro) :
    RbrSplit.LayerStepAccepts
      (RbrSplit.stepsOf (nl := nl) (w := w)
        (withMsgs FD MD (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
        (fun m pref => accR h dom hkrow hr dec stmt respOf
          ((lfSetup body rootOf msgOf).context mt ro) m pref
          (msgOf ((lfSetup body rootOf msgOf).proof mt ro) m)))
      ((lfSetup body rootOf msgOf).challenges mt ro) := by
  unfold JointAccepts statementOfAt at hacc
  rw [accepts_guarded, decide_eq_true_iff] at hacc
  obtain ⟨hfield, hv1⟩ := hacc
  obtain ⟨e, hext, hagree, -⟩ := hexp
  rw [stepsOf_withMsgs_eq hm, layerStepAccepts_iff]
  exact ⟨hfield, mem_acceptingR_of_accepts h dom hkrow hr dec _ _ _ _ _ _ _ _ e hext hagree hv1⟩

end V1

section RowCompiled

open Lfzk.CertifiedV1
open Lfzk.CompiledLongfellow (Code Col guarded v1K Matches v8Hash_openings_pos)
open Lfzk.CompiledLongfellowAdaptive (statementOfAt challengeOfAt queryOfAt responseOfAt
  rootStatement accR exists_msgLigeroData extractedInstance)

variable {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
variable {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [Fintype Equations] [DecidableEq Equations]
variable {logw logc nc nv : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**A certified V1 row at the compiled Longfellow verifier, against a re-committing prefix-only
Fiat–Shamir prover.**

```text
Pr[ AcceptsAt (v1K …) V codec (lfSetup body rootOf msgOf) …  ∧  Fails(context) ]
    ≤  R.bound  +  N · R.fsCoefficient  +  R.tape · (L + N) / 2^digestBits
```

over the Merkle tape and the random oracle on message prefixes, `N` the prover's deployed hash
queries.  `row_adaptive_ratio_le` with `hlig` discharged by
`CompiledLongfellowAdaptive.exists_msgLigeroData` at the extracted instance and the proof's own
response, and `hright` by `hright_v1`.  **Every premise**: the protocol instance (`hr`, `hF`, `dom`,
`V`, `stmt`, `respOf`, `Ffam` with `hexact` and `RbrLongfellow`'s field premises inside it, `MD`,
`|Cand|`, `|D|`, `tA ≤ commitFuel`, `2n + tA ≤ tape`, `Fintype Msg`), `hmatch` (`Matches`),
`hfalse` (in a failing context the Ligero statement at the context's root is false), `hfail`.
-/
theorem row_adaptive_ratio_le_v1 {R : Row} (h : R.Valid) (hr : 0 < R.params.row.openings)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F R.params.nw R.params.nq R.params.q Equations)
    (respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg R.params.nl R.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = R.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ R.commitFuel) (htape : 2 * R.params.row.n + tA ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (MPoint D Msg R.params.nl R.params.rounds → C) =>
        AcceptsAt (v1K (Row.rowValid h) dom (Row.hkrow h) hr) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg R.params.nl R.params.rounds))
      ≤ R.bound + N * R.fsCoefficient
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  refine le_trans (le_of_eq ?_)
    (row_adaptive_ratio_le h dec (guarded (v1K (Row.rowValid h) dom (Row.hkrow h) hr)) body
      rootOf msgOf claimOf (statementOfAt V msgOf (rootStatement rootOf stmt) id)
      (responseOfAt R.params.nl R.params.rounds respOf msgOf) (challengeOfAt V id)
      (queryOfAt V id) hF (accR (Row.rowValid h) dom (Row.hkrow h) hr dec stmt respOf)
      (fun κ hκ => exists_msgLigeroData C Msg (Row.rowValid h) (Row.coreRows h) hF dom
        (Row.hkrow h)
        (extractedInstance (Row.rowValid h) dom (Row.hkrow h) hr dec (stmt κ.1) κ.1 κ.2)
        (hfalse κ hκ) respOf)
      H Sat Ffam hexact MD hfail
      (fun mt ro _ hacc hexp => hright_v1 (Row.rowValid h) dom (Row.hkrow h) hr dec V body
        rootOf msgOf claimOf stmt respOf (Ffam _) (MD _) (hmatch _) mt ro hacc hexp)
      htA htape hcand hD)
  congr 3
  refine Finset.filter_congr fun ω _ => ?_
  rw [acceptsAt_iff_joint]

/--
**The v8 hash row at the compiled Longfellow verifier, against a re-committing prefix-only
Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1` at `CertifiedV1.v8Hash` (the deployed hash profile, 20 layers and 610
sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 4088`, `k = 584`, 132 opened columns):

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-114  +  N · 2^-115
```

against one adaptive program making at most `tA ≤ 2^60` Merkle-oracle and `N` deployed
(message-prefix) hash queries, interleaved as it likes — the numerals of
`CompiledLongfellowAdaptive.v8Hash_adaptive_compiled_ratio_le`, where `N` counted raw-answer points.
-/
theorem v8Hash_adaptive_compiled_ratio_le
    {codec : Codec Salt (Col F v8Hash.params.nw v8Hash.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
      (LigeroV1LayerStep.Qry v8Hash.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v8Hash.params.row.openings v8Hash.params.q
      v8Hash.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F v8Hash.params.nw v8Hash.params.nq v8Hash.params.q
      Equations)
    (respOf : Msg → LigeroFamily.Response F v8Hash.params.row.openings v8Hash.params.q
      v8Hash.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v8Hash.params.nl v8Hash.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v8Hash.params.row.n Salt
      (Col F v8Hash.params.nw v8Hash.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v8Hash.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
        (LigeroV1LayerStep.Qry v8Hash.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ v8Hash.commitFuel) (htape : 2 * v8Hash.params.row.n + tA ≤ v8Hash.tape)
    (hcand : Fintype.card Cand = v8Hash.cardCand)
    (hD : Fintype.card D = 2 ^ v8Hash.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v8Hash.tape → D) × (MPoint D Msg v8Hash.params.nl v8Hash.params.rounds → C) =>
        AcceptsAt (v1K (Row.rowValid v8Hash_valid) dom (Row.hkrow v8Hash_valid) v8Hash_openings_pos)
            V codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf
            claimOf (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v8Hash.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v8Hash.params.nl v8Hash.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) :=
  le_trans
    (row_adaptive_ratio_le_v1 v8Hash_valid v8Hash_openings_pos dec V dom stmt respOf body
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (adaptive_rhs_le_bits v8Hash v8Hash_adaptive_slack_bound v8Hash_adaptive_slack_coeff N)

end RowCompiled

end Lfzk.NizkDeployedHashAdaptive
