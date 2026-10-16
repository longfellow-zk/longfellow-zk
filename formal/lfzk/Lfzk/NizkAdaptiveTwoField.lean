import Lfzk.NizkAdaptive
import Lfzk.TwoFieldV1Rows

/-!
# Two-field Longfellow against one re-committing Fiat–Shamir prover, with a hashed MAC key

`Lfzk.NizkGrindingTwoField` composes two grinding sides through the MAC, but each side keeps one
fixed commitment and the verifier's MAC-key share is a uniform coin of the merged tape.  Here both
restrictions are gone.  One prover program `body` interleaves Merkle-oracle queries (for both
sides' trees, under one hash) with challenge-oracle queries, and the verifier's MAC-key share is the
challenge oracle's answer at its own role.

## The transcript

A hash input is a `Pt2` (`hash2`):

* round `0`, **the MAC-key point** `H(root₁, root₂)` (`Sum.inl (root₁, root₂)`).  Its decoded answer
  is the verifier's share `a_v`, so the multiplier is `aP κ + decode c₀`;
* rounds `1, …, L₁`, side 1's points, and rounds `1 + L₁, …, L₁ + L₂`, side 2's.  A side point is a
  `NizkGrinding.Point` whose context `SideCtx` is both roots, the **raw key answer** `c₀`, and the
  public data `pubOf out` the prover sends with the key (the tag and blinds), followed by the side's
  own messages and raw answers.  Each side's sub-transcript is domain-separated by its role type.

Every point names the pair of roots (`key2`), so the commitment context `κ` of both sides is fixed at
the first challenge query naming the pair — typically the key point — and `Bcs.AdaptiveCommit`'s cut
applies to both roots at once.

## The bad events, one per slot

`Bad κ q c` reads the point's role:

* the key point: `aP κ + decode c = 0` — the MAC's one bad coin, budget `kmac` (`hbal`);
* a side point: the side's LayerStep, in the side context `(κ, c₀, pub)` the point carries, is doomed and
  `c` escapes — budget `|Candᵢ| · classBudget role`, as in the single-field theorem.

The chain is the three-way split of `Lfzk.TwoField.composed_fail_subset`, at the level of the
verifier's rounds: if no pair of good witnesses agrees on the common value, then side 1 has none (its
LayerStep sheds doom at some side-1 round), or side 2 has none, or both have one and they disagree, and
then the two MAC rows force `aP κ + decode c₀ = 0` at round `0`.

## The bound

```text
Pr[ both compiled verifiers accept  ∧  the composed extractor fails ]
    ≤  R₁.bound + R₂.bound + 1/|Fmac|
       +  N · max(κ₁, κ₂, 1/|Fmac|)
       +  2 · tape · (1 + L₁ + L₂ + N) / 2^digestBits                    twofield_adaptive_ratio_le
```

`N` is the prover's total challenge-oracle budget, over all three roles; each of its queries pays the
worst role, the verifier's `1 + L₁ + L₂` recomputations their own.  The last term is one cut-trace
extraction per root (`Bcs.AdaptiveCommit.Setup.ratio_le_two`).

At `TwoFieldV1Rows.p256sha` (`p256sha_adaptive_ratio_le`): `≤ 2^-114 + N · 2^-115`, the extra terms
absorbed into the certified slack (`p256sha_adaptive_slack_bound`, `p256sha_adaptive_slack_coeff`).

## What is still a hypothesis

Per side and per side context `σ` (the fields of `Side`): the Ligero half `hlig` (a query test read
from the proof's messages, round-by-round sound at the row's densities where no candidate satisfies
the circuit), LayerStep's field data `field` with `hexact` and `RbrLongfellow`'s field premises inside
it, the message reading `MD`; per side, `hright` (the Fiat–Shamir transliteration, as in
`CertifiedV1.Row.adaptive_ratio_le`) and **`hrow` (the MAC row: a good witness of an accepting side
satisfies the MAC equation at the hashed key and the proof's tag)**; the MAC data `aP`, `decode`,
`hbal`, `hmac`, `|Fmac|`; and the instance's numbers (`tA ≤ commitFuel`, `2n₁ + 2n₂ + tA ≤ tape`).
`aP` is a function of the commitment context: the prover's share is committed.
`Lfzk.CompiledLongfellowAdaptive` discharges `hlig` and `hright` at the compiled Longfellow verifiers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkAdaptiveTwoField

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.CertifiedV1 Lfzk.Mac
open scoped Classical

/-! ## 1. The two-field transcript -/

/-- A side point's context: both roots, the raw MAC-key answer, and the public data sent with the
key. -/
abbrev SideCtx (D C X : Type) := (D × D) × C × X

/-- **A two-field hash input**: the MAC-key point `H(root₁, root₂)`, or a point of side 1 or 2. -/
abbrev Pt2 (D C X Msg₁ Msg₂ : Type) (nl₁ nl₂ : ℕ) (w₁ w₂ : ℕ → ℕ) :=
  (D × D) ⊕ (Point (SideCtx D C X) Msg₁ C nl₁ w₁ ⊕ Point (SideCtx D C X) Msg₂ C nl₂ w₂)

section Transcript

variable {D C X Msg₁ Msg₂ Out : Type} {nl₁ nl₂ : ℕ} {w₁ w₂ : ℕ → ℕ}

/-- The pair of roots a point names. -/
def key2 : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → D × D :=
  Sum.elim id (Sum.elim (fun p => p.ctx.1) (fun p => p.ctx.1))

/-- **The verifier's round-`k` hash input.**  Round `0` is the MAC-key point; rounds `1 + k₁` are
side 1's, with the side's own raw answers; the rest are side 2's. -/
noncomputable def hash2 (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) (k : ℕ) (cp : Fin k → C) :
    Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ :=
  if h0 : k = 0 then Sum.inl (rootOf₁ out, rootOf₂ out)
  else if h1 : k < 1 + Rounds.Role.length nl₁ w₁ then
    Sum.inr (Sum.inl (hashPoint ((rootOf₁ out, rootOf₂ out), cp ⟨0, by omega⟩, pubOf out) msgOf₁
      out (k - 1) fun j => cp ⟨1 + j.val, by omega⟩))
  else
    Sum.inr (Sum.inr (hashPoint ((rootOf₁ out, rootOf₂ out), cp ⟨0, by omega⟩, pubOf out) msgOf₂
      out (k - 1 - Rounds.Role.length nl₁ w₁)
        fun j => cp ⟨1 + Rounds.Role.length nl₁ w₁ + j.val, by omega⟩))

theorem key2_hash2 (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) (k : ℕ) (cp : Fin k → C) :
    key2 (hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂) rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      out k cp) = (rootOf₁ out, rootOf₂ out) := by
  unfold hash2
  split_ifs <;> rfl

/-- Rewriting a hash point's round index. -/
theorem hashPoint_cast {Ctx Msg : Type} {nl : ℕ} {w : ℕ → ℕ} (ctx : Ctx) (msgOf : Out → ℕ → Msg)
    (out : Out) {m m' : ℕ} (h : m = m') (cp : Fin m → C) :
    hashPoint (nl := nl) (w := w) ctx msgOf out m cp
      = hashPoint ctx msgOf out m' fun j => cp ⟨j.val, h ▸ j.isLt⟩ := by
  subst h; rfl

/-- **The two-field reading of a re-committing prover.** -/
noncomputable def setup2 {Enc : Type} {tA N : ℕ}
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out tA N) (dflt : C)
    (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) :
    Setup Enc D (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out (D × D) tA N
      (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) where
  body := body
  hashInput := hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
  dflt := dflt
  key := key2
  keyOut out := (rootOf₁ out, rootOf₂ out)
  hkey := key2_hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂

/-- Round `0`: the MAC-key point. -/
theorem hash2_zero (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) (cp : Fin 0 → C) :
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂) rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      out 0 cp = Sum.inl (rootOf₁ out, rootOf₂ out) := by
  unfold hash2; rw [dif_pos rfl]

/-- Round `1 + k₁`: side 1's round `k₁`, at side 1's raw answers. -/
theorem hash2_side1 (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) {k₁ : ℕ}
    (hk : k₁ < Rounds.Role.length nl₁ w₁) (cp : Fin (1 + k₁) → C) :
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂) rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      out (1 + k₁) cp
      = Sum.inr (Sum.inl (hashPoint ((rootOf₁ out, rootOf₂ out), cp ⟨0, by omega⟩, pubOf out)
          msgOf₁ out k₁ fun j => cp ⟨1 + j.val, by omega⟩)) := by
  unfold hash2
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  exact hashPoint_cast _ msgOf₁ out (by omega) _

/-- Round `1 + L₁ + k₂`: side 2's round `k₂`, at side 2's raw answers. -/
theorem hash2_side2 (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) {k₂ : ℕ}
    (cp : Fin (1 + Rounds.Role.length nl₁ w₁ + k₂) → C) :
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂) rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      out (1 + Rounds.Role.length nl₁ w₁ + k₂) cp
      = Sum.inr (Sum.inr (hashPoint ((rootOf₁ out, rootOf₂ out), cp ⟨0, by omega⟩, pubOf out)
          msgOf₂ out k₂ fun j => cp ⟨1 + Rounds.Role.length nl₁ w₁ + j.val, by omega⟩)) := by
  unfold hash2
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr 2
  exact hashPoint_cast _ msgOf₂ out (by omega) _

end Transcript

/-! ## 2. One side's per-context data -/

/-- **One side's protocol data, per side context** `σ = (κ, c₀, pub)`: `CertifiedV1.Row.adaptive_ratio_le`'s
per-context premises other than `hright`, with failure meaning that no candidate satisfies the side's
circuit. -/
structure Side (R : Row) (Sig C Cand F Equations Witness Msg : Type) [Fintype C] [Field F]
    [Fintype F] [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
    (nc nv logw logc : ℕ) where
  /-- The side's Ligero query test, per side context, read from the prefix and the round's
  message. -/
  accR : Sig → ∀ m : ℕ, (Fin m → C) → Msg →
    LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq →
      Finset (LigeroV1LayerStep.Qry R.params.row)
  /-- LayerStep's honest values, per side context. -/
  H : Sig → RbrLongfellow.Honest F Cand logw logc
  /-- Which candidates satisfy the side's circuit, per side context. -/
  Sat : Sig → Cand → Prop
  /-- The field half of LayerStep, per side context. -/
  field : ∀ σ, RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
    (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H σ) (Sat σ)
  /-- Its decoders are exactly balanced. -/
  hexact : ∀ σ, (field σ).Exact
  /-- How a round's message fixes LayerStep's prover data at that round. -/
  MD : ∀ σ, MsgData C Msg (H σ)
  /-- **The Ligero half**: where no candidate satisfies the circuit, the query test is round-by-round
  sound at the row's densities (`CertifiedV1.Row.adaptive_ratio_le`'s `hlig`). -/
  hlig : ∀ σ, (∀ cand : Cand, ¬ Sat σ cand) →
    ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq → Prop)
      (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Msg LigDoomed),
      ML.accepting = accR σ ∧
      (ML.escaping.card : ℚ) ≤ (R.params.row.fail + R.params.row.arith)
        * Fintype.card (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq) ∧
      ML.bq = LigeroV1LayerStep.queryCount R.params.row

/-- A good witness of a side: the witness of a satisfying candidate. -/
def Side.Good {R : Row} {Sig C Cand F Equations Witness Msg : Type} [Fintype C] [Field F]
    [Fintype F] [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
    {nc nv logw logc : ℕ}
    (S : Side R Sig C Cand F Equations Witness Msg nc nv logw logc) (σ : Sig) (a : Witness) :
    Prop :=
  ∃ cand : Cand, S.Sat σ cand ∧ (S.field σ).wOf cand = a

/-- The verifier's two Merkle checks, one per side, against one Merkle oracle. -/
def check2 {Enc D Out Salt₁ M₁ Salt₂ M₂ : Type} [Inhabited D] [DecidableEq Enc] {n₁ n₂ : ℕ}
    (codec₁ : Codec Salt₁ M₁ D Enc) (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D)
    (codec₂ : Codec Salt₂ M₂ D Enc) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D) :
    Out → Tree Enc D Unit (2 * n₂ + 2 * n₁) := fun out =>
  (lfCheck codec₁ claimOf₁ out).bind fun _ => lfCheck codec₂ claimOf₂ out

/-- The sum of a role function over the schedule, as a sum over slots. -/
theorem sum_roleAt {nl : ℕ} {w : ℕ → ℕ} (f : Rounds.Role nl w → ℕ) :
    ∑ x ∈ range (Rounds.Role.length nl w), f (roleAt x)
      = ∑ i : Fin (Rounds.Role.length nl w), f (Rounds.Role.indexEquiv.symm i) := by
  rw [← Fin.sum_univ_eq_sum_range (fun x => f (roleAt x))]
  exact Finset.sum_congr rfl fun i _ => by rw [roleAt_val]

/-- Rational version for graded role budgets. -/
theorem sum_roleAt_rat {nl : ℕ} {w : ℕ → ℕ}
    (f : Rounds.Role nl w → ℚ) :
    ∑ x ∈ range (Rounds.Role.length nl w), f (roleAt x)
      = ∑ i : Fin (Rounds.Role.length nl w),
          f (Rounds.Role.indexEquiv.symm i) := by
  rw [← Fin.sum_univ_eq_sum_range (fun x => f (roleAt x))]
  exact Finset.sum_congr rfl fun i _ => by rw [roleAt_val]

/-! ## 3. Two sides, one prover, one hashed MAC key -/

section Compose

variable {R₁ R₂ : Row}
variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [Inhabited Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [Inhabited Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Salt₁ M₁ Salt₂ M₂ : Type} [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂]
  [Inhabited M₂] {n₁ n₂ : ℕ}

/-- The schedule length: the key round and the two sides' rounds. -/
abbrev len2 (R₁ R₂ : Row) : ℕ :=
  1 + Rounds.Role.length R₁.params.nl R₁.params.rounds
    + Rounds.Role.length R₂.params.nl R₂.params.rounds

/--
**Two-field Longfellow against one re-committing Fiat–Shamir prover, with a hashed MAC key.**

Over one Merkle tape (`R₁.tape` slots, shared by both sides' trees) and one challenge tape of
`1 + L₁ + L₂ + N` slots, against one program `body` with at most `tA` Merkle-oracle and `N`
challenge-oracle queries:

```text
Pr[ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  R₁.bound + R₂.bound + 1/|Fmac|  +  N · max(κ₁, κ₂, 1/|Fmac|)
       +  2 · R₁.tape · (1 + L₁ + L₂ + N) / 2^digestBits
```

The side context is `σ = (κ, c₀, pubOf out)`: the commitment context of the pair of roots (cut at
the first challenge query naming the pair), the raw MAC-key answer, and the public data.

**Every premise**: per side, a `Side` (field, domain, Ligero instance, LayerStep data with `hexact`,
`MD`, `hfalse`) and `hF`, `hcand`, `hD`; per side, `hright` (the Fiat–Shamir transliteration at the
side's recomputed rounds) and `hrow` (the MAC row: a good witness of an accepting side satisfies the
MAC equation at the hashed key `aP κ + decode c₀`, the blinds `keyB out` and the tag `tagOf out`);
the MAC data `aP`, `decode`, `hbal`, `hmac`; the Merkle budget `tA ≤ commitFuelᵢ` and room
`2n₂ + 2n₁ + tA ≤ R₁.tape = R₂.tape`.
-/
theorem twofield_adaptive_ratio_le (h₁ : R₁.Valid) {tA N : ℕ}
    {codec₁ : Codec Salt₁ M₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ M₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂)
    -- the prover, and the verifier's reading of its proof
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (statementOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Statement₁) (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Statement₂) (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Query₂)
    -- the two sides, per side context
    (S₁ : Side R₁ (((D × D) × List (Enc × D)) × C × X) C Cand₁ F₁ Equations₁ Witness₁ Msg₁
      nc₁ nv₁ logw₁ logc₁)
    (S₂ : Side R₂ (((D × D) × List (Enc × D)) × C × X) C Cand₂ F₂ Equations₂ Witness₂ Msg₂
      nc₂ nv₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (hcand₁ : Fintype.card Cand₁ = R₁.cardCand) (hcand₂ : Fintype.card Cand₂ = R₂.cardCand)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    -- the MAC
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    -- acceptance, transliteration, and the MAC rows
    (hright₁ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₁.Sat σ cand) →
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R₁.params.nl) (w := R₁.params.rounds)
          (withMsgs (S₁.field σ) (S₁.MD σ) (msgOf₁ (S.proof mt ct)))
          (fun m pref => S₁.accR σ m pref (msgOf₁ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₂.Sat σ cand) →
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R₂.params.nl) (w := R₂.params.rounds)
          (withMsgs (S₂.field σ) (S₂.MD σ) (msgOf₂ (S.proof mt ct)))
          (fun m pref => S₂.accR σ m pref (msgOf₂ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct
          ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩))
    (hrow₁ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    -- the prover's Merkle budget and the shared Merkle tape
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel)
    (htape : 2 * n₂ + 2 * n₁ + tA ≤ R₁.tape) (htape₂ : R₁.tape = R₂.tape) :
    ((univ.filter fun ω : (Fin R₁.tape → D) × (Fin (len2 R₁ R₂ + N) → C) =>
        JointAccepts K₁ codec₁ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ (len2 R₁ R₂ + N))
      ≤ R₁.bound + R₂.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max R₁.fsCoefficient R₂.fsCoefficient) (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  classical
  set S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ with hS
  -- the Ligero halves, in each failing side context
  choose LigD₁ ML₁ hacc₁ hesc₁ hbq₁ using S₁.hlig
  choose LigD₂ ML₂ hacc₂ hesc₂ hbq₂ using S₂.hlig
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have hFpos₁ : 0 < R₁.params.row.fieldSize := by rw [← hF₁]; exact Fintype.card_pos
  have hFpos₂ : 0 < R₂.params.row.fieldSize := by rw [← hF₂]; exact Fintype.card_pos
  set bp₁ := pairBudget (Fintype.card C) R₁.params.row.fieldSize
  set bi₁ := inBudget (Fintype.card C) R₁.params.row.fieldSize
  set bl₁ := ligBudget R₁.params.row (Fintype.card C)
  set bq₁ := queryBudget R₁.params.row (Fintype.card C)
  set bp₂ := pairBudget (Fintype.card C) R₂.params.row.fieldSize
  set bi₂ := inBudget (Fintype.card C) R₂.params.row.fieldSize
  set bl₂ := ligBudget R₂.params.row (Fintype.card C)
  set bq₂ := queryBudget R₂.params.row (Fintype.card C)
  have hB₁ : ∀ σ (hσ : ∀ cand, ¬ S₁.Sat σ cand),
      MsgBudgets (S₁.field σ) (ML₁ σ hσ) bp₁ bp₁ bi₁ bl₁ bq₁ := by
    intro σ hσ
    have ep : 2 * Fintype.card C / Fintype.card F₁ = bp₁ := by rw [hF₁]; rfl
    have ei : Fintype.card C / Fintype.card F₁ = bi₁ := by rw [hF₁]; rfl
    obtain ⟨hp0, hp1, hr, hi⟩ := (S₁.hexact σ).field_budgets
    obtain ⟨-, -, hchal, hqq⟩ := S₁.hexact σ
    refine ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
        (LigeroV1LayerStep.arith_nonneg _)) (hesc₁ σ hσ) hchal, ?_⟩
    rw [hbq₁ σ hσ]
    exact LigeroV1LayerStep.queryBudget_le hqq
  have hB₂ : ∀ σ (hσ : ∀ cand, ¬ S₂.Sat σ cand),
      MsgBudgets (S₂.field σ) (ML₂ σ hσ) bp₂ bp₂ bi₂ bl₂ bq₂ := by
    intro σ hσ
    have ep : 2 * Fintype.card C / Fintype.card F₂ = bp₂ := by rw [hF₂]; rfl
    have ei : Fintype.card C / Fintype.card F₂ = bi₂ := by rw [hF₂]; rfl
    obtain ⟨hp0, hp1, hr, hi⟩ := (S₂.hexact σ).field_budgets
    obtain ⟨-, -, hchal, hqq⟩ := S₂.hexact σ
    refine ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
        (LigeroV1LayerStep.arith_nonneg _)) (hesc₂ σ hσ) hchal, ?_⟩
    rw [hbq₂ σ hσ]
    exact LigeroV1LayerStep.queryBudget_le hqq
  -- the bad event at a point, by role
  obtain ⟨Bad, hBad⟩ : ∃ Bad : (D × D) × List (Enc × D) →
      Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C → Prop,
      Bad = fun κ q c => Sum.elim (fun _ => aP κ + decode c = 0)
        (Sum.elim
          (fun p => ∃ hσ : (∀ cand, ¬ S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2) cand),
            DoomedAt (S₁.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₁.MD (κ, p.ctx.2.1, p.ctx.2.2))
              (ML₁ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p ∧
            EscapesAt (S₁.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₁.MD (κ, p.ctx.2.1, p.ctx.2.2))
              (ML₁ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p c)
          (fun p => ∃ hσ : (∀ cand, ¬ S₂.Sat (κ, p.ctx.2.1, p.ctx.2.2) cand),
            DoomedAt (S₂.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₂.MD (κ, p.ctx.2.1, p.ctx.2.2))
              (ML₂ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p ∧
            EscapesAt (S₂.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₂.MD (κ, p.ctx.2.1, p.ctx.2.2))
              (ML₂ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p c)) q := ⟨_, rfl⟩
  let beta : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds →
      ℕ := Sum.elim (fun _ => kmac) (Sum.elim
    (fun p => Fintype.card Cand₁ * RbrLayerStep.classBudget (nl := R₁.params.nl) (w := R₁.params.rounds)
      bp₁ bp₁ bi₁ bl₁ bq₁ p.role)
    (fun p => Fintype.card Cand₂ * RbrLayerStep.classBudget (nl := R₂.params.nl) (w := R₂.params.rounds)
      bp₂ bp₂ bi₂ bl₂ bq₂ p.role))
  have hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q := by
    intro κ q
    rcases q with r | p | p
    · refine le_trans (Finset.card_le_card ?_) (hbal (-aP κ))
      intro c hc
      simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inl] at hc ⊢
      linear_combination hc
    · by_cases hσ : ∀ cand, ¬ S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2) cand
      · by_cases hd : DoomedAt (S₁.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₁.MD (κ, p.ctx.2.1, p.ctx.2.2))
            (ML₁ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p
        · refine le_trans (Finset.card_le_card ?_)
            (escapesAt_card (S₁.field _) (S₁.MD _) (ML₁ _ hσ) (hB₁ _ hσ) dflt p hd)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr, Sum.elim_inl] at hc ⊢
          obtain ⟨_, _, he⟩ := hc
          exact he
        · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr, Sum.elim_inl] at hc
          obtain ⟨_, hd', _⟩ := hc
          exact absurd hd' hd
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr, Sum.elim_inl] at hc
        obtain ⟨hσ', _⟩ := hc
        exact absurd hσ' hσ
    · by_cases hσ : ∀ cand, ¬ S₂.Sat (κ, p.ctx.2.1, p.ctx.2.2) cand
      · by_cases hd : DoomedAt (S₂.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₂.MD (κ, p.ctx.2.1, p.ctx.2.2))
            (ML₂ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p
        · refine le_trans (Finset.card_le_card ?_)
            (escapesAt_card (S₂.field _) (S₂.MD _) (ML₂ _ hσ) (hB₂ _ hσ) dflt p hd)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr] at hc ⊢
          obtain ⟨_, _, he⟩ := hc
          exact he
        · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr] at hc
          obtain ⟨_, hd', _⟩ := hc
          exact absurd hd' hd
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr] at hc
        obtain ⟨hσ', _⟩ := hc
        exact absurd hσ' hσ
  -- the worst point, and each verifier round's point
  set βmax := max kmac (max (Fintype.card Cand₁ * NizkGrinding.maxBudget bp₁ bp₁ bi₁ bl₁ bq₁)
    (Fintype.card Cand₂ * NizkGrinding.maxBudget bp₂ bp₂ bi₂ bl₂ bq₂)) with hβmax
  have hmax : ∀ q, beta q ≤ βmax := by
    intro q
    rcases q with r | p | p
    · exact le_max_left _ _
    · exact le_trans (Nat.mul_le_mul_left _ (classBudget_le_max p.role))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (Nat.mul_le_mul_left _ (classBudget_le_max p.role))
        (le_trans (le_max_right _ _) (le_max_right _ _))
  let g : ℕ → ℕ := fun k =>
    if k = 0 then kmac
    else if k < 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds then
      Fintype.card Cand₁ * RbrLayerStep.classBudget (nl := R₁.params.nl) (w := R₁.params.rounds)
        bp₁ bp₁ bi₁ bl₁ bq₁ (roleAt (k - 1))
    else
      Fintype.card Cand₂ * RbrLayerStep.classBudget (nl := R₂.params.nl) (w := R₂.params.rounds)
        bp₂ bp₂ bi₂ bl₂ bq₂ (roleAt (k - 1 - Rounds.Role.length R₁.params.nl R₁.params.rounds))
  let slotBeta : Fin (len2 R₁ R₂) → ℕ := fun i => g i.val
  have hslot : ∀ (out : Out) (i : Fin (len2 R₁ R₂)) (cp : Fin i.val → C),
      beta (S.hashInput out i.val cp) ≤ slotBeta i := by
    intro out i cp
    show beta (hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ out i.val cp) ≤ g i.val
    unfold hash2
    simp only [g]
    split_ifs <;> exact le_rfl
  have hsum : ∑ i, slotBeta i
      = kmac + Fintype.card Cand₁ * (R₁.params.nl * bp₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁ + bl₁ + bq₁)
        + Fintype.card Cand₂ * (R₂.params.nl * bp₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂ + bl₂ + bq₂) := by
    rw [show (∑ i, slotBeta i) = ∑ i : Fin (len2 R₁ R₂), g i.val from rfl,
      Fin.sum_univ_eq_sum_range g, len2, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_range_one]
    have e0 : g 0 = kmac := by simp only [g, if_pos rfl]
    have e1 : ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds), g (1 + x)
        = Fintype.card Cand₁ * ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds),
          RbrLayerStep.classBudget (nl := R₁.params.nl) (w := R₁.params.rounds)
            bp₁ bp₁ bi₁ bl₁ bq₁ (roleAt x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_range.mp hx
      simp only [g]
      rw [if_neg (by omega), if_pos (by omega), show 1 + x - 1 = x by omega]
    have e2 : ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          g (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x)
        = Fintype.card Cand₂ * ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          RbrLayerStep.classBudget (nl := R₂.params.nl) (w := R₂.params.rounds)
            bp₂ bp₂ bi₂ bl₂ bq₂ (roleAt x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [g]
      rw [if_neg (by omega), if_neg (by omega),
        show 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x - 1
          - Rounds.Role.length R₁.params.nl R₁.params.rounds = x by omega]
    rw [e0, e1, e2, sum_roleAt, sum_roleAt, RbrLayerStep.layerStep_budget_sum, RbrLayerStep.layerStep_budget_sum]
  -- the chain: the three-way split of the composed failure, at the verifier's rounds
  have hchain : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C),
      (JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
          statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct ∧
        JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
          statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct) →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct → S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      (¬ ∃ a₁ a₂,
        S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a₁ ∧
        S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a₂ ∧
        common₁ a₁ = common₂ a₂) →
      (S.grinding mt Bad beta hbad).RoundBad ct := by
    intro mt ct hacc hex₁ hex₂ hcomp
    set out := S.proof mt ct with hout
    set c₀ := S.challenges mt ct ⟨0, by omega⟩ with hc₀
    set σ := (S.context mt ct, c₀, pubOf out) with hσdef
    by_cases hσ₁ : ∀ cand, ¬ S₁.Sat σ cand
    · -- side 1 has no good witness: its LayerStep sheds doom at some side-1 round
      have hlayerStep := hright₁ mt ct hσ₁ hacc.1 hex₁
      rw [← hacc₁ σ hσ₁] at hlayerStep
      let ch₁ : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C :=
        fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩
      let hR := layerStepRbr (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.field σ) (S₁.MD σ)
        (ML₁ σ hσ₁) (hB₁ σ hσ₁) (Fails := ∀ cand, ¬ S₁.Sat σ cand) (fun h => h) (msgOf₁ out)
      obtain ⟨k₁, hd, he⟩ := hR.exists_escape ch₁ (hR.doomed_start hσ₁ _)
        (hR.accepts_undoomed ch₁ hlayerStep)
      obtain ⟨hdq, hesq⟩ := link_at (S₁.field σ) (S₁.MD σ) (ML₁ σ hσ₁) dflt
        ((rootOf₁ out, rootOf₂ out), c₀, pubOf out) msgOf₁ out k₁.val
        (Sumcheck.extract_prefix ch₁ k₁) (ch₁ k₁) k₁.isLt hd he
      refine ⟨⟨1 + k₁.val, by omega⟩, ?_⟩
      have hpt : (S.grinding mt Bad beta hbad).point ct ⟨1 + k₁.val, by omega⟩
          = Sum.inr (Sum.inl (hashPoint ((rootOf₁ out, rootOf₂ out), c₀, pubOf out) msgOf₁ out
              k₁.val (Sumcheck.extract_prefix ch₁ k₁))) := by
        show hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ (S.output mt ct).1 (1 + k₁.val)
          (fun j => (S.output mt ct).2 j.val) = _
        exact hash2_side1 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ _ k₁.isLt _
      rw [hpt]
      subst hBad
      exact ⟨hσ₁, hdq, hesq⟩
    by_cases hσ₂ : ∀ cand, ¬ S₂.Sat σ cand
    · -- side 2 has no good witness
      have hlayerStep := hright₂ mt ct hσ₂ hacc.2 hex₂
      rw [← hacc₂ σ hσ₂] at hlayerStep
      let ch₂ : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C :=
        fun i => S.challenges mt ct
          ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩
      let hR := layerStepRbr (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.field σ) (S₂.MD σ)
        (ML₂ σ hσ₂) (hB₂ σ hσ₂) (Fails := ∀ cand, ¬ S₂.Sat σ cand) (fun h => h) (msgOf₂ out)
      obtain ⟨k₂, hd, he⟩ := hR.exists_escape ch₂ (hR.doomed_start hσ₂ _)
        (hR.accepts_undoomed ch₂ hlayerStep)
      obtain ⟨hdq, hesq⟩ := link_at (S₂.field σ) (S₂.MD σ) (ML₂ σ hσ₂) dflt
        ((rootOf₁ out, rootOf₂ out), c₀, pubOf out) msgOf₂ out k₂.val
        (Sumcheck.extract_prefix ch₂ k₂) (ch₂ k₂) k₂.isLt hd he
      refine ⟨⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩, ?_⟩
      have hpt : (S.grinding mt Bad beta hbad).point ct
            ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩
          = Sum.inr (Sum.inr (hashPoint ((rootOf₁ out, rootOf₂ out), c₀, pubOf out) msgOf₂ out
              k₂.val (Sumcheck.extract_prefix ch₂ k₂))) := by
        show hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ (S.output mt ct).1
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val)
          (fun j => (S.output mt ct).2 j.val) = _
        exact hash2_side2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ _ _
      rw [hpt]
      subst hBad
      exact ⟨hσ₂, hdq, hesq⟩
    -- both sides have good witnesses, which disagree: the MAC rows kill the multiplier
    push Not at hσ₁ hσ₂
    obtain ⟨cand₁, hs₁⟩ := hσ₁
    obtain ⟨cand₂, hs₂⟩ := hσ₂
    have hne : common₁ ((S₁.field σ).wOf cand₁) ≠ common₂ ((S₂.field σ).wOf cand₂) :=
      fun heq => hcomp ⟨_, _, ⟨cand₁, hs₁, rfl⟩, ⟨cand₂, hs₂, rfl⟩, heq⟩
    have hm₁ := hrow₁ mt ct _ hacc.1 ⟨cand₁, hs₁, rfl⟩
    have hm₂ := hrow₂ mt ct _ hacc.2 ⟨cand₂, hs₂, rfl⟩
    have hzero := macTag_collision hne (hm₁.trans hm₂.symm)
    refine ⟨⟨0, by omega⟩, ?_⟩
    have hpt : (S.grinding mt Bad beta hbad).point ct ⟨0, by omega⟩
        = Sum.inl (rootOf₁ out, rootOf₂ out) := by
      show hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ (S.output mt ct).1 0
        (fun j => (S.output mt ct).2 j.val) = _
      exact hash2_zero rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ _ _
    rw [hpt]
    subst hBad
    exact hzero
  -- the generic two-root count
  have hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I (claimOf₁ out).a (claimOf₁ out).pf (2 * n₁)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_left _ (lfCheck_trace codec₁ claimOf₁ H out qa hqa)
  have hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a (claimOf₂ out).pf (2 * n₂)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_right _ (lfCheck_trace codec₂ claimOf₂ H out qa hqa)
  have hroom := Row.fuel_room h₁
  have hgen := S.ratio_le_two codec₁ dec₁ codec₂ dec₂ (check2 codec₁ claimOf₁ codec₂ claimOf₂)
    Prod.fst Prod.snd claimOf₁ claimOf₂ hcheck₁ hcheck₂ Bad beta hbad βmax hmax slotBeta hslot
    (by omega) (by omega) htape (by omega) le_rfl
    (fun mt ct => JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁
        claimOf₁ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct ∧
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct)
    (fun mt ct => ¬ ∃ a₁ a₂,
      S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a₁ ∧
      S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a₂ ∧
      common₁ a₁ = common₂ a₂)
    (fun mt ct h => h.1.2.1) (fun mt ct h => h.2.2.1) hchain
  refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card ?_))
    (by positivity)) (le_trans hgen ?_)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact ⟨⟨hω.1, hω.2.1⟩, hω.2.2⟩
  -- the densities
  rw [hsum]
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hDpos : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast Fintype.card_pos
  have hseq₁ := budgets_le_bound R₁ hCpos hFpos₁ (cardCand := Fintype.card Cand₁) hD₁
  have hseq₂ := budgets_le_bound R₂ hCpos hFpos₂ (cardCand := Fintype.card Cand₂) hD₂
  have hb₁ : R₁.bound = R₁.params.nizkBound (Fintype.card Cand₁) R₁.commitFuel R₁.tape := by
    rw [hcand₁]; rfl
  have hb₂ : R₂.bound = R₂.params.nizkBound (Fintype.card Cand₂) R₂.commitFuel R₂.tape := by
    rw [hcand₂]; rfl
  have hmacq := Lfzk.TwoFieldV1.mac_term_le (C := C) hmac
  set M := max (max R₁.fsCoefficient R₂.fsCoefficient) (1 / (Fintype.card Fmac : ℚ)) with hM
  have hβ : (βmax : ℚ) / (Fintype.card C : ℚ) ≤ M := by
    rw [div_le_iff₀ hc, hβmax]
    push_cast
    have hk : (kmac : ℚ) ≤ M * Fintype.card C := by
      have h := (div_le_iff₀ hc).mp hmacq
      have hle : 1 / (Fintype.card Fmac : ℚ) ≤ M := le_max_right _ _
      nlinarith
    have h1 : (Fintype.card Cand₁ : ℚ) * (NizkGrinding.maxBudget bp₁ bp₁ bi₁ bl₁ bq₁ : ℚ)
        ≤ M * Fintype.card C := by
      have hmd := maxBudget_le_density R₁ hCpos hFpos₁
      have hκ : R₁.fsCoefficient = (Fintype.card Cand₁ : ℚ) * R₁.maxDensity := by
        unfold Row.fsCoefficient; rw [hcand₁]
      have hle : R₁.fsCoefficient ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
      calc (Fintype.card Cand₁ : ℚ) * (NizkGrinding.maxBudget bp₁ bp₁ bi₁ bl₁ bq₁ : ℚ)
          ≤ (Fintype.card Cand₁ : ℚ) * ((Fintype.card C : ℚ) * R₁.maxDensity) :=
            mul_le_mul_of_nonneg_left hmd (by positivity)
        _ = R₁.fsCoefficient * Fintype.card C := by rw [hκ]; ring
        _ ≤ M * Fintype.card C := mul_le_mul_of_nonneg_right hle hc.le
    have h2 : (Fintype.card Cand₂ : ℚ) * (NizkGrinding.maxBudget bp₂ bp₂ bi₂ bl₂ bq₂ : ℚ)
        ≤ M * Fintype.card C := by
      have hmd := maxBudget_le_density R₂ hCpos hFpos₂
      have hκ : R₂.fsCoefficient = (Fintype.card Cand₂ : ℚ) * R₂.maxDensity := by
        unfold Row.fsCoefficient; rw [hcand₂]
      have hle : R₂.fsCoefficient ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
      calc (Fintype.card Cand₂ : ℚ) * (NizkGrinding.maxBudget bp₂ bp₂ bi₂ bl₂ bq₂ : ℚ)
          ≤ (Fintype.card Cand₂ : ℚ) * ((Fintype.card C : ℚ) * R₂.maxDensity) :=
            mul_le_mul_of_nonneg_left hmd (by positivity)
        _ = R₂.fsCoefficient * Fintype.card C := by rw [hκ]; ring
        _ ≤ M * Fintype.card C := mul_le_mul_of_nonneg_right hle hc.le
    exact max_le hk (max_le h1 h2)
  have hDq : (Fintype.card D : ℚ) = 2 ^ R₁.params.digestBits := by rw [hD₁]; push_cast; rfl
  have hnum₁ := adaptiveNumerator_le (Lfs := len2 R₁ R₂ + N) htA₁ htape
  have hnum₂ := adaptiveNumerator_le (Lfs := len2 R₁ R₂ + N) htA₂ (htape₂ ▸ htape)
  have hnumq₁ : (adaptiveNumerator (2 * n₂ + 2 * n₁) tA (len2 R₁ R₂ + N) : ℚ)
        / (Fintype.card D : ℚ)
      ≤ (merkleNumerator R₁.commitFuel R₁.tape : ℚ) / (Fintype.card D : ℚ)
        + ((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits := by
    rw [← hDq, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum₁) hDpos.le
  have hnumq₂ : (adaptiveNumerator (2 * n₂ + 2 * n₁) tA (len2 R₁ R₂ + N) : ℚ)
        / (Fintype.card D : ℚ)
      ≤ (merkleNumerator R₂.commitFuel R₂.tape : ℚ) / (Fintype.card D : ℚ)
        + ((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits := by
    rw [← hDq, ← add_div, htape₂]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum₂) hDpos.le
  have hsplit : ((N * βmax + (kmac + Fintype.card Cand₁ * (R₁.params.nl * bp₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁ + bl₁ + bq₁)
        + Fintype.card Cand₂ * (R₂.params.nl * bp₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂ + bl₂ + bq₂)) : ℕ)
          : ℚ) / (Fintype.card C : ℚ)
      = N * ((βmax : ℚ) / (Fintype.card C : ℚ)) + (kmac : ℚ) / (Fintype.card C : ℚ)
        + ((Fintype.card Cand₁ * (R₁.params.nl * bp₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁ + bl₁ + bq₁) : ℕ)
            : ℚ) / (Fintype.card C : ℚ)
        + ((Fintype.card Cand₂ * (R₂.params.nl * bp₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂ + bl₂ + bq₂) : ℕ)
            : ℚ) / (Fintype.card C : ℚ) := by
    push_cast
    ring
  rw [hsplit, hb₁, hb₂]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hβ hN
  linarith

end Compose

/-! ## 4. At `p256sha` -/

open Lfzk.TwoFieldV1Rows

/-- The two-field schedule at `p256sha`: the key round, then `544` and `633` slots for the two sides. -/
theorem p256sha_len2 : len2 p256sha.ecdsa p256sha.sha = 1178 := by
  native_decide

/-- The two cut-trace extractions' term at the row: `2 · 2^62 · (1178 + N) / 2^256
= (1178 + N) · 2^-193`. -/
theorem p256sha_adaptive_term (N : ℕ) :
    2 * (((p256sha.ecdsa.tape * (len2 p256sha.ecdsa p256sha.sha + N) : ℕ) : ℚ)
        / 2 ^ p256sha.ecdsa.params.digestBits)
      = ((1178 + N : ℕ) : ℚ) / 2 ^ 193 := by
  rw [p256sha_len2]
  have ht : p256sha.ecdsa.tape = 2 ^ 62 := rfl
  have hd : p256sha.ecdsa.params.digestBits = 256 := rfl
  rw [ht, hd]
  push_cast
  field_simp
  norm_num

/-- **The re-commitment terms at `N = 0` fit in the row's slack**: the composed bound plus two
cut-trace extractions' `tape · 1178 / 2^256` is still at most `2^-114`.  Checked by evaluation, as
`p256sha_valid` is. -/
theorem p256sha_adaptive_slack_bound :
    p256sha.ecdsa.bound + p256sha.sha.bound + 1 / (p256sha.macFieldSize : ℚ)
        + 2 * (((p256sha.ecdsa.tape * len2 p256sha.ecdsa p256sha.sha : ℕ) : ℚ)
          / 2 ^ p256sha.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 114 := by
  native_decide

/-- **The per-query coefficient fits too**: the worst role's coefficient — the `GF(2^128)` side's
`κ₂`, above `κ₁ ≤ 2^-121` and the key slot's `1/|Fmac| = 2^-128` — plus `2 · tape / 2^256` is at most
`2^-115`. -/
theorem p256sha_adaptive_slack_coeff :
    max (max p256sha.ecdsa.fsCoefficient p256sha.sha.fsCoefficient)
        (1 / (p256sha.macFieldSize : ℚ))
      + 2 * ((p256sha.ecdsa.tape : ℚ) / 2 ^ p256sha.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

section Headline

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [Inhabited Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [Inhabited Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Salt₁ M₁ Salt₂ M₂ : Type} [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂]
  [Inhabited M₂] {n₁ n₂ : ℕ}

/--
**Two-field Longfellow at `p256sha` against one re-committing Fiat–Shamir prover, with a hashed
MAC key.**

ECDSA over `P-256`'s base field and SHA-256 over `GF(2^128)`, each at its deployed v8 circuit profile
proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128` elements;
the MAC-key share is the challenge oracle's answer at `H(root₁, root₂)`; one prover program makes at
most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles, interleaved as it
likes:

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-114  +  N · 2^-115
```

over one Merkle tape of `2^62` slots and one challenge tape of `1178 + N` slots.  The extra
re-commitment terms `2 · 2^62 · (1178 + N) / 2^256` are absorbed by the certified slack
(`p256sha_adaptive_slack_bound`, `p256sha_adaptive_slack_coeff`).  The premises are
`twofield_adaptive_ratio_le`'s.
-/
theorem p256sha_adaptive_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ M₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ M₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ p256sha.ecdsa.params.nl
      p256sha.sha.params.nl p256sha.ecdsa.params.rounds p256sha.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (statementOf₁ : Out → (Fin (len2 p256sha.ecdsa p256sha.sha) → C) → Statement₁)
    (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 p256sha.ecdsa p256sha.sha) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 p256sha.ecdsa p256sha.sha) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 p256sha.ecdsa p256sha.sha) → C) → Statement₂)
    (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 p256sha.ecdsa p256sha.sha) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 p256sha.ecdsa p256sha.sha) → C) → Query₂)
    (S₁ : Side p256sha.ecdsa (((D × D) × List (Enc × D)) × C × X) C Cand₁ F₁ Equations₁ Witness₁
      Msg₁ nc₁ nv₁ logw₁ logc₁)
    (S₂ : Side p256sha.sha (((D × D) × List (Enc × D)) × C × X) C Cand₂ F₂ Equations₂ Witness₂
      Msg₂ nc₂ nv₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = p256sha.ecdsa.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = p256sha.sha.params.row.fieldSize)
    (hcand₁ : Fintype.card Cand₁ = p256sha.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = p256sha.sha.cardCand)
    (hD : Fintype.card D = 2 ^ p256sha.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hright₁ : ∀ (mt : Fin p256sha.ecdsa.tape → D)
      (ct : Fin (len2 p256sha.ecdsa p256sha.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₁.Sat σ cand) →
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := p256sha.ecdsa.params.nl) (w := p256sha.ecdsa.params.rounds)
          (withMsgs (S₁.field σ) (S₁.MD σ) (msgOf₁ (S.proof mt ct)))
          (fun m pref => S₁.accR σ m pref (msgOf₁ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin p256sha.ecdsa.tape → D)
      (ct : Fin (len2 p256sha.ecdsa p256sha.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₂.Sat σ cand) →
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := p256sha.sha.params.nl) (w := p256sha.sha.params.rounds)
          (withMsgs (S₂.field σ) (S₂.MD σ) (msgOf₂ (S.proof mt ct)))
          (fun m pref => S₂.accR σ m pref (msgOf₂ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct
          ⟨1 + Rounds.Role.length p256sha.ecdsa.params.nl p256sha.ecdsa.params.rounds + i.val,
            by omega⟩))
    (hrow₁ : ∀ (mt : Fin p256sha.ecdsa.tape → D)
      (ct : Fin (len2 p256sha.ecdsa p256sha.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin p256sha.ecdsa.tape → D)
      (ct : Fin (len2 p256sha.ecdsa p256sha.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60) (htape : 2 * n₂ + 2 * n₁ + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin p256sha.ecdsa.tape → D) ×
          (Fin (len2 p256sha.ecdsa p256sha.sha + N) → C) =>
        JointAccepts K₁ codec₁ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ p256sha.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 p256sha.ecdsa p256sha.sha + N))
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) := by
  have hv := p256sha_valid
  refine le_trans (twofield_adaptive_ratio_le (TwoFieldRowV1.ecdsa_valid hv)
    dec₁ dec₂ K₁ K₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ statementOf₂ responseOf₂
    challengeOf₂ queryOf₂ S₁ S₂ hF₁ hF₂ hcand₁ hcand₂ hD hD aP decode kmac hbal hmac keyB tagOf
    common₁ common₂ hright₁ hright₂ hrow₁ hrow₂ htA htA htape rfl) ?_
  have hsb := p256sha_adaptive_slack_bound
  have hsc := p256sha_adaptive_slack_coeff
  have hmf : (Fintype.card Fmac : ℚ) = (p256sha.macFieldSize : ℚ) := by
    rw [hFmac]; rfl
  rw [hmf]
  have hsplit : 2 * (((p256sha.ecdsa.tape * (len2 p256sha.ecdsa p256sha.sha + N) : ℕ) : ℚ)
        / 2 ^ p256sha.ecdsa.params.digestBits)
      = 2 * (((p256sha.ecdsa.tape * len2 p256sha.ecdsa p256sha.sha : ℕ) : ℚ)
          / 2 ^ p256sha.ecdsa.params.digestBits)
        + N * (2 * ((p256sha.ecdsa.tape : ℚ) / 2 ^ p256sha.ecdsa.params.digestBits)) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

end Headline

end Lfzk.NizkAdaptiveTwoField
