import Lfzk.NizkGrinding
import Bcs.AdaptiveCommit

/-!
# The composed Longfellow bound against a re-committing Fiat–Shamir prover

`Lfzk.NizkGrinding` bounds a grinding Fiat–Shamir search run **after one fixed commitment**: the
search reads the commit stage's private state and makes no Merkle-oracle query.  This file removes
that restriction.  The prover is one adaptive program `body` that interleaves at most `tA`
Merkle-oracle queries with at most `N` challenge-oracle queries: it may build any number of Merkle
trees, hash each root for its challenges, and keep whichever root and transcript suit it.

## The verifier

* A hash input is a `NizkGrinding.Point D Msg C nl w` whose context **is the root**: the verifier
  hashes `hashPoint (rootOf out) msgOf out k cp` (`lfSetup`).  So a point names its commitment and a
  slot is charged once, at its point's role, whatever commitment it names.
* The compiled verifier (`JointAccepts`) recomputes the `L` rounds, checks the Merkle opening of
  `claimOf out` against `rootOf out` with the lazily sampled Merkle oracle of the whole run, and runs
  the IPCP verifier on the opened leaves at the statement, challenge and query it reads from the
  proof and the recomputed answers.

## The extractor, and where `N` and the commitment count enter

The commitment the proof's root refers to is fixed at the first challenge query naming that root
(`Bcs.AdaptiveCommit`).  The extractor reads the root from the Merkle queries made before that point;
its context `κ = (root, cut trace)` is what every per-commitment datum below is indexed by.

* **Merkle side** (`Bcs.AdaptiveCommit.Setup.merkle_card_le`).  A proof whose opening the cut-trace
  extraction does not explain costs `adaptiveNumerator (2n) tA (L + N) / |D|`: the single-commitment
  collision and child-label terms over the prover's `tA` Merkle queries, plus one root target per
  distinct challenge query.  At a row with `tA ≤ commitFuel` and `2n + tA ≤ tape` this is at most
  `merkleTerm + tape · (L + N) / |D|` (`adaptiveNumerator_le`).  **That is the whole price of
  re-committing**: the number of commitments never appears, only the number of challenge queries
  that could have fixed one.
* **Fiat–Shamir side** (`Bcs.CtxGrinding`).  LayerStep's bad event at a point is judged in the context
  of the root the point names, read off the challenge slots before it; each slot pays its point's
  role budget, the verifier's `L` recomputations their own role and the prover's `N` queries the worst
  role.

```text
Pr[ the compiled verifier accepts  ∧  Fails(κ) ]
    ≤  R.bound  +  N · R.fsCoefficient  +  tape · (L + N) / 2^digestBits        Row.adaptive_ratio_le
```

At `CertifiedV1.v8Hash` the extra term is `(633 + N) · 2^-194`, and both it and the `N`-term fit
inside the certified slack (`v8Hash_adaptive_slack_bound`, `v8Hash_adaptive_slack_coeff`), so

```text
Pr ≤ 2^-114 + N · 2^-115                                                  v8Hash_adaptive_ratio_le
```

— the same numbers as `NizkGrinding.v8Hash_fs_ratio_le`, now against a prover that may re-commit.

## What is still a hypothesis

`Row.adaptive_ratio_le`'s docstring lists every premise.  Beyond the protocol instance (field, fuels,
`|D|`, `|Cand|`), they are, per commitment context `κ`: `hlig` (the Ligero half: a query test read
from the proof's messages that is round-by-round sound at the row's densities where extraction
fails), `hfail` (extraction failure means no satisfying candidate), `Ffam`/`hexact` with
`RbrLongfellow`'s field premises inside `Ffam`, the message reading `MD`, and `hright`, the
Fiat–Shamir transliteration (README gap 1): an accepted, extraction-explained proof's LayerStep accepts
at the recomputed challenges, which carries that `challengeOf`/`queryOf` decode the recomputed Ligero
rounds.  `Lfzk.CompiledLongfellowAdaptive` discharges `hlig` and `hright` at the compiled Longfellow
verifier, with the Ligero test reading the proof's own response.

## Modelling choices, stated

* The Ligero half's doom predicate is fixed per commitment context; the query test may read the
  proof's messages (`MsgLigeroData`).
* Hash inputs carry the root and the raw earlier answers (`NizkGrinding.Point`).
* The Merkle check is the verifier's `checkPass` on `claimOf out`; the prover's own Merkle queries are
  bounded by `tA ≤ commitFuel`, and the Merkle tape must hold them and the check (`2n + tA ≤ tape`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkAdaptive

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding
open scoped Classical

/-! ## 1. The Longfellow verifier's reading of a re-committing prover -/

section Reading

variable {Enc D Msg C Out : Type} {nl : ℕ} {w : ℕ → ℕ} {tA N : ℕ}

/-- **The verifier's reading**: round `k` hashes the proof's root, the role, the messages through
round `k` and the raw earlier answers; a point names its root. -/
noncomputable def lfSetup (body : TwoOracleTree Enc D (Point D Msg C nl w) C Out tA N) (dflt : C)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg) :
    Setup Enc D (Point D Msg C nl w) C Out D tA N (Rounds.Role.length nl w) where
  body := body
  hashInput out := hashPoint (rootOf out) msgOf out
  dflt := dflt
  key := Point.ctx
  keyOut := rootOf
  hkey _ _ _ := rfl

variable {Salt M : Type} [Inhabited D] [DecidableEq Enc] {n : ℕ}

/-- The verifier's Merkle check on the proof's opening claim. -/
def lfCheck (codec : Codec Salt M D Enc) (claimOf : Out → OpeningClaim n Salt M D) :
    Out → Tree Enc D Unit (2 * n) := fun out =>
  (checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
    fun _ => default).map fun _ => ()

theorem lfCheck_trace (codec : Codec Salt M D Enc) (claimOf : Out → OpeningClaim n Salt M D)
    (H : Enc → D) (out : Out) :
    ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
        fun _ => default).run H).2, qa ∈ ((lfCheck codec claimOf out).run H).2 := by
  intro qa hqa
  rw [lfCheck, Tree.run_map]
  exact hqa

end Reading

/-! ## 2. The compiled verifier on the joint execution -/

section Accepts

variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N L TM TC fc : ℕ}
variable {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
variable {Salt M : Type} {n : ℕ}

/-- **The compiled verifier on the joint execution**: the opened set is the queried one, the Merkle
opening reconstructs the proof's root under the run's Merkle oracle, and the IPCP verifier accepts the
opened leaves, at the challenge and query decoded from the recomputed answers. -/
def JointAccepts (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (codec : Codec Salt M D Enc) (S : Setup Enc D Pt C Out Key tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D)
    (claimOf : Out → OpeningClaim n Salt M D) (statementOf : Out → (Fin L → C) → Statement)
    (responseOf : Out → Response) (challengeOf : Out → (Fin L → C) → Challenge)
    (queryOf : Out → (Fin L → C) → Query) (mt : Fin TM → D) (ct : Fin TC → C) : Prop :=
  K.Accepts (codec.withOracle (S.merkleOracle check mt ct))
    (statementOf (S.proof mt ct) (S.challenges mt ct))
    (rootOf (S.proof mt ct)) (challengeOf (S.proof mt ct) (S.challenges mt ct))
    (responseOf (S.proof mt ct)) (queryOf (S.proof mt ct) (S.challenges mt ct))
    (claimOf (S.proof mt ct))

end Accepts

/-! ## 3. Counting the Merkle term at a row -/

/-- **The adaptive Merkle numerator is the row's, plus one root target per challenge query per
tape slot.** -/
theorem adaptiveNumerator_le {fc tA cf tape Lfs : ℕ} (htA : tA ≤ cf) (htape : fc + tA ≤ tape) :
    adaptiveNumerator fc tA Lfs ≤ merkleNumerator cf tape + tape * Lfs := by
  unfold adaptiveNumerator merkleNumerator
  have h1 : tA * (tA - 1) / 2 ≤ cf * (cf - 1) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul htA (Nat.sub_le_sub_right htA 1))
  have h2 : (fc + tA) * (2 * tA + 1) ≤ tape * (2 * cf + 1) :=
    Nat.mul_le_mul htape (by omega)
  have h3 : (fc + tA) * Lfs ≤ tape * Lfs := Nat.mul_le_mul_right _ htape
  omega

end Lfzk.NizkAdaptive

/-! ## 4. At a certified V1 row -/

namespace Lfzk.CertifiedV1

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
open scoped Classical

/-- The schedule at a row has at least one round. -/
theorem length_pos (R : Row) : 0 < Rounds.Role.length R.params.nl R.params.rounds := by
  rw [length_eq]; omega

/--
**A certified V1 row against a re-committing Fiat–Shamir prover.**

Over the Merkle tape (`R.tape` slots) and a challenge tape of `L + N` slots, against a prover `body`
that interleaves at most `tA` Merkle-oracle and `N` challenge-oracle queries:

```text
Pr[ JointAccepts  ∧  Fails(context of the proof's root) ]
    ≤  R.bound  +  N · R.fsCoefficient  +  R.tape · (L + N) / 2^digestBits
```

`R.bound` is the sequential row's certified bound, `R.fsCoefficient` what each extra challenge query
can buy, and the last term what re-committing can buy (`Bcs.AdaptiveCommit.Setup.merkle_card_le`).

**Every premise**, and nothing else.  The context `κ = (root, cut trace)` is
`(lfSetup body dflt rootOf msgOf).context mt ct`: the proof's root and the Merkle queries made before
the first challenge query naming it.

* the protocol instance — `|F| = row.fieldSize` (`hF`), the field half of LayerStep per context
  `Ffam` with exactly balanced decoders (`hexact`) and `RbrLongfellow`'s field premises inside it,
  the message reading `MD`, `|Cand|` (`hcand`), `|D|` (`hD`), the prover's Merkle budget
  `tA ≤ commitFuel` (`htA`) and the Merkle tape's room `2n + tA ≤ tape` (`htape`);
* `hlig` — **the Ligero half**: in a failing context the query test `accR κ`, read from the prefix
  and the round's message, is round-by-round sound at the row's densities (an escaping set of
  density `fail + arith`, and `queryCount` accepting queries at a doomed challenge, whatever the
  response).  `LigeroV1LayerStep.exists_ligeroData` supplies it from a false Ligero statement at a
  fixed response strategy; `Lfzk.CompiledLongfellowAdaptive.exists_msgLigeroData` at the proof's own
  response;
* `hfail` — in a failing context no candidate satisfies the circuit;
* `hright` — **the Fiat–Shamir transliteration**: if the compiled verifier accepts and the cut-trace
  extraction explains the opening, then in a failing context LayerStep on the proof's messages accepts
  at the recomputed challenges, with the query test `accR κ` at the proof's messages.

`Ffam`'s `B` and `prover` fields are not read: `withMsgs` replaces them by `MD` at the proof's
messages.
-/
theorem Row.adaptive_ratio_le {R : Row} (h : R.Valid)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    -- the prover, and the verifier's reading of its proof
    (body : TwoOracleTree Enc D (Point D Msg C R.params.nl R.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D)
    (statementOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    {Fails : D × List (Enc × D) → Prop}
    -- the Ligero half of LayerStep, per commitment context: a query test read from the prefix
    -- and the round's message, round-by-round sound at the row's densities where extraction fails
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
    (hright : ∀ (mt : Fin R.tape → D) (ct : Fin (R.fsLen N) → C),
      Fails ((lfSetup body dflt rootOf msgOf).context mt ct) →
      JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
        statementOf responseOf challengeOf queryOf mt ct →
      (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds)
          (withMsgs (Ffam ((lfSetup body dflt rootOf msgOf).context mt ct))
            (MD ((lfSetup body dflt rootOf msgOf).context mt ct))
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
          (fun m pref => accR ((lfSetup body dflt rootOf msgOf).context mt ct) m pref
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct) m)))
        ((lfSetup body dflt rootOf msgOf).challenges mt ct))
    -- the prover's Merkle budget and the Merkle tape
    (htA : tA ≤ R.commitFuel) (htape : 2 * n + tA ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (Fin (R.fsLen N) → C) =>
        JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape * (Fintype.card C : ℚ) ^ R.fsLen N)
      ≤ R.bound + N * R.fsCoefficient
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  classical
  set S := lfSetup body dflt rootOf msgOf with hS
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
  -- the bad event at a point, in a context
  obtain ⟨Bad, hBad⟩ : ∃ Bad : D × List (Enc × D) → Point D Msg C R.params.nl R.params.rounds →
      C → Prop, Bad = fun κ q c => ∃ hκ : Fails κ, DoomedAt (Ffam κ) (MD κ) (ML κ hκ) dflt q ∧
        EscapesAt (Ffam κ) (MD κ) (ML κ hκ) dflt q c := ⟨_, rfl⟩
  let beta : Point D Msg C R.params.nl R.params.rounds → ℕ := fun q =>
    Fintype.card Cand * RbrLayerStep.classBudget (nl := R.params.nl) (w := R.params.rounds)
      bp bp bi bl bq q.role
  have hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q := by
    intro κ q
    by_cases hκ : Fails κ
    · by_cases hd : DoomedAt (Ffam κ) (MD κ) (ML κ hκ) dflt q
      · refine le_trans (Finset.card_le_card ?_)
          (escapesAt_card (Ffam κ) (MD κ) (ML κ hκ) (hB κ hκ) dflt q hd)
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
  let slotBeta : Fin (Rounds.Role.length R.params.nl R.params.rounds) → ℕ := fun i => Fintype.card Cand *
    RbrLayerStep.classBudget (nl := R.params.nl) (w := R.params.rounds) bp bp bi bl bq
      (Rounds.Role.indexEquiv.symm i)
  have hslot : ∀ (out : Out) (i : Fin (Rounds.Role.length R.params.nl R.params.rounds))
      (cp : Fin i.val → C),
      beta (S.hashInput out i.val cp) ≤ slotBeta i := by
    intro out i cp
    show Fintype.card Cand * RbrLayerStep.classBudget (nl := R.params.nl) (w := R.params.rounds)
        bp bp bi bl bq (roleAt i.val) ≤ _
    rw [roleAt_val]
  have hsum : ∑ i, slotBeta i
      = Fintype.card Cand * (R.params.nl * bp
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi + bl + bq) := by
    rw [← Finset.mul_sum, RbrLayerStep.layerStep_budget_sum]
  -- the chain, from LayerStep's sequential state function
  have hchain : ∀ (mt : Fin R.tape → D) (ct : Fin (R.fsLen N) → C),
      JointAccepts K codec S (lfCheck codec claimOf) rootOf claimOf statementOf responseOf
        challengeOf queryOf mt ct →
      S.Explains dec id claimOf mt ct → Fails (S.context mt ct) →
      (S.grinding mt Bad beta hbad).RoundBad ct := by
    intro mt ct hacc' hexp hκ
    set κ := S.context mt ct with hκdef
    set out := S.proof mt ct
    set ch := S.challenges mt ct
    have hlayerStep := hright mt ct hκ hacc' hexp
    rw [← hacc κ hκ] at hlayerStep
    let hR := layerStepRbr (nl := R.params.nl) (w := R.params.rounds) (Ffam κ) (MD κ) (ML κ hκ)
      (hB κ hκ) (Fails := Fails κ) (hfail κ) (msgOf out)
    obtain ⟨k, hd, he⟩ := hR.exists_escape ch (hR.doomed_start hκ _) (hR.accepts_undoomed ch hlayerStep)
    obtain ⟨hdq, hesq⟩ := link_at (Ffam κ) (MD κ) (ML κ hκ) dflt (rootOf out) msgOf out k.val
      (Sumcheck.extract_prefix ch k) (ch k) k.isLt hd he
    refine ⟨k, ?_⟩
    subst hBad
    exact ⟨hκ, hdq, hesq⟩
  -- the generic adaptive count
  have hgen := S.ratio_le codec dec (lfCheck codec claimOf) id claimOf (lfCheck_trace codec claimOf)
    Bad beta hbad βmax hmax slotBeta hslot (length_pos R) (by omega) htape
    (by have := Row.fuel_room h; omega) le_rfl
    (fun mt ct => JointAccepts K codec S (lfCheck codec claimOf) rootOf claimOf statementOf
      responseOf challengeOf queryOf mt ct) Fails (fun mt ct hacc' => hacc'.2.1) hchain
  refine le_trans hgen ?_
  -- the densities
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hseq := budgets_le_bound R hCpos hFpos (cardCand := Fintype.card Cand) hD
  have hmaxd := maxBudget_le_density R hCpos hFpos
  have hnum := adaptiveNumerator_le
    (Lfs := Rounds.Role.length R.params.nl R.params.rounds + N) htA htape
  have hDq : (Fintype.card D : ℚ) = 2 ^ R.params.digestBits := by rw [hD]; push_cast; rfl
  have hDpos : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast Fintype.card_pos
  have hnumq : (adaptiveNumerator (2 * n) tA
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

/-! ## 5. The v8 hash row -/

/-- **The re-commitment term at `N = 0` fits in the row's slack**: `R.bound + tape · 633 / 2^256`
is still at most `2^-114`.  Checked by evaluation, as `v8Hash_valid` is. -/
theorem v8Hash_adaptive_slack_bound :
    v8Hash.bound
        + ((v8Hash.tape * Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds
            : ℕ) : ℚ) / 2 ^ v8Hash.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 114 := by
  native_decide

/-- **The re-commitment term per challenge query fits in the coefficient's slack**:
`κ + tape / 2^256 ≤ 2^-115`. -/
theorem v8Hash_adaptive_slack_coeff :
    v8Hash.fsCoefficient + (v8Hash.tape : ℚ) / 2 ^ v8Hash.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- The re-commitment term at the row: `2^62 · (633 + N) / 2^256 = (633 + N) · 2^-194`. -/
theorem v8Hash_adaptive_term (N : ℕ) :
    ((v8Hash.tape * (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds + N)
        : ℕ) : ℚ) / 2 ^ v8Hash.params.digestBits
      = ((633 + N : ℕ) : ℚ) / 2 ^ 194 := by
  rw [v8Hash_length]
  have ht : v8Hash.tape = 2 ^ 62 := rfl
  have hd : v8Hash.params.digestBits = 256 := rfl
  rw [ht, hd]
  push_cast
  field_simp
  norm_num

/--
**The v8 hash row against a re-committing Fiat–Shamir prover.**

`Row.adaptive_ratio_le` at `v8Hash` (the deployed hash profile (20 layers, 610 sumcheck slots) over
`GF(2^128)`, Ligero V1 at the deployed geometry `n = 4088`, `k = 584` with 132 opened columns), against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes:

```text
Pr[ JointAccepts  ∧  Fails(context of the proof's root) ]  ≤  2^-114  +  N · 2^-115
```

over the Merkle tape (`2^62` slots) and a challenge tape of `633 + N` slots.  The re-commitment term
`(633 + N) · 2^-194` is absorbed: `633 · 2^-194` by the sequential bound's slack
(`v8Hash_adaptive_slack_bound`), `N · 2^-194` by the coefficient's (`v8Hash_adaptive_slack_coeff`).
The premises are `Row.adaptive_ratio_le`'s.
-/
theorem v8Hash_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (Point D Msg C v8Hash.params.nl v8Hash.params.rounds) C
      Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
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
    (hright : ∀ (mt : Fin v8Hash.tape → D) (ct : Fin (v8Hash.fsLen N) → C),
      Fails ((lfSetup body dflt rootOf msgOf).context mt ct) →
      JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
        statementOf responseOf challengeOf queryOf mt ct →
      (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v8Hash.params.nl) (w := v8Hash.params.rounds)
          (withMsgs (Ffam ((lfSetup body dflt rootOf msgOf).context mt ct))
            (MD ((lfSetup body dflt rootOf msgOf).context mt ct))
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
          (fun m pref => accR ((lfSetup body dflt rootOf msgOf).context mt ct) m pref
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct) m)))
        ((lfSetup body dflt rootOf msgOf).challenges mt ct))
    (htA : tA ≤ v8Hash.commitFuel) (htape : 2 * n + tA ≤ v8Hash.tape)
    (hcand : Fintype.card Cand = v8Hash.cardCand)
    (hD : Fintype.card D = 2 ^ v8Hash.params.digestBits) :
    ((univ.filter fun ω : (Fin v8Hash.tape → D) × (Fin (v8Hash.fsLen N) → C) =>
        JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v8Hash.tape * (Fintype.card C : ℚ) ^ v8Hash.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) := by
  refine le_trans (Row.adaptive_ratio_le v8Hash_valid dec K body dflt rootOf msgOf claimOf
    statementOf responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright
    htA htape hcand hD) ?_
  have hsb := v8Hash_adaptive_slack_bound
  have hsc := v8Hash_adaptive_slack_coeff
  have hsplit : ((v8Hash.tape
        * (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ v8Hash.params.digestBits
      = ((v8Hash.tape * Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds
          : ℕ) : ℚ) / 2 ^ v8Hash.params.digestBits
        + N * ((v8Hash.tape : ℚ) / 2 ^ v8Hash.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

end Lfzk.CertifiedV1
