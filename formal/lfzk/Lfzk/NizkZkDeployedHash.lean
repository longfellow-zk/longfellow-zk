import Lfzk.NizkZkTwoField
import Lfzk.NizkDeployedHashTwoField

/-!
# The zero-knowledge LayerStep, with Fiat–Shamir hash inputs as deployed

`Lfzk.NizkZk.Row.zk_adaptive_ratio_le` and `Lfzk.NizkZkTwoField.twofield_zk_adaptive_ratio_le`
bound a re-committing prover against the **zero-knowledge** LayerStep (`Lfzk.RbrZkSplit`) at hash
inputs `NizkGrinding.Point` that carry the raw earlier answers (README "R4").  A deployed adversary
that asks one message prefix asks one point; translated into the raw-answer model it must first ask
every earlier round, so its `N` there is multiplied by the number of rounds (~600).  This file
restates both bounds over the total random oracle on the deployed hash inputs (`Bcs.TotalOracle`,
`Bcs.TotalOracleCommit`, `Lfzk.NizkDeployedHash`), so `N` counts **deployed** (message-prefix)
hash queries.  The numerals are unchanged.

## The congruence the conversion needs (`zkChain_doomed_congr`)

`NizkDeployedHash.shed_at_msgPoint_of` applies to any family of state functions indexed by the
message sequence whose state at length `j` reads only messages `< j` (`hcongr`).  The
zero-knowledge chain is `MsgLocal` (`NizkZk.zkChain_msgLocal`): its start and its doom predicate
`ZkWrong` are message-blind, and slot `i`'s transition reads message `i` only — the round
polynomial at a sumcheck slot, the previous layer's close at a pair slot and at the input binding,
the Ligero response at the query slot.  `doomed_congr_of_msgLocal` turns that into `hcongr`.  The
statement the verifier builds is part of the state (`ZkState.built sys` after the input binding),
so at the two Ligero slots it is a function of the messages hashed before them; in particular the
doom at the Ligero challenge slot, "every candidate violates the built system", reads no message
after the input binding (`Lfzk.CompiledZkDeployedHash.zkBuilt_congr` states it for the verifier's
`zkBuilt`).

## Point layout

No new point layout is needed.  The zero-knowledge verifier runs on the same `Rounds` schedule as
the clear one, and round `k` reads message `k`; so round `k`'s hash input is
`NizkDeployedHash.msgPoint ctx msgOf out k` (context, role `roleAt k`, messages `0, …, k`):

* layer 0's pair slot (role `layerPair 0`) is where `begin_circuit` draws the output point `G` and
  `begin_layer` layer 0's `(beta, alpha)` — one oracle answer decoded by `ZkCode.decodeInit`, the
  model's reading of successive PRF outputs of one digest that are not re-absorbed.  Its point
  carries message `0` only (the public statement absorbed before `G`); the transition reads none;
* layer `ly > 0`'s pair slot reads layer `ly − 1`'s close (`closeOf (ms m)` at its own slot `m`),
  which its point carries as its last message;
* the two Ligero slots carry, as their last messages, the input binding's close and the Ligero
  response.

The two-field transcript is `NizkDeployedHashTwoField`'s exactly: the key point is the pair of
roots, the hash side is proved first, its points carry the context `(roots, av, pub)` with `av` the
MAC-key share the proof carries in its public inputs, the signature side's points carry all of the
hash side's messages, and `av` is checked against the oracle's answer at the key point (that
equation is part of the acceptance event).  Each side's zero-knowledge code is read at the proof's
`av` (its public binding reads the key and the public data).

## What is proved

* `doomed_congr_of_msgLocal`, `zkChain_doomed_congr` — `hcongr` for the zero-knowledge chain;
* `row_zk_deployed_adaptive_ratio_le` — at any certified V1 row and output dimension `logv`, for an
  abstract compiled verifier `K` with `hright`:

```text
Pr[ JointAccepts  ∧  no lift-list member's witness satisfies the circuit ]
    ≤  R.zkBound logv  +  N · R.zkCoefficient logv  +  R.tape · (L + N) / 2^digestBits
```

  `NizkZk.Row.zk_adaptive_ratio_le`'s right-hand side, `N` the prover's deployed hash queries;
* `twofield_zk_deployed_adaptive_ratio_le` — two zero-knowledge sides, hash side first:

```text
Pr[ both accept ∧ av = ro(key point) ∧ no two good witnesses agree on the common value ]
    ≤  R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · tape · (1 + L₁ + L₂ + N) / 2^digestBits
```

  `NizkZkTwoField.twofield_zk_adaptive_ratio_le`'s right-hand side.

`Lfzk.CompiledZkDeployedHash` discharges `hright` at the deployed verifiers, and
`Lfzk.CompiledZkDeployedHashRows` instantiates the v7 rows and pairs.

## What is still a hypothesis

Those of `NizkZk.Row.zk_adaptive_ratio_le` and `NizkZkTwoField.twofield_zk_adaptive_ratio_le`
(per context the field data with exactly balanced decoders, the Ligero half's numerals,
`|Lift| ≤ cardCand`, `hright`; per side `hrow`; the MAC data; `|F|`, `|D|`, the Merkle budget), with
the MAC rows at the `av` the proof carries; plus finiteness of the message types and of the public
data, which makes the oracle a finite sample space.  The idealisation of the SHA-256 transcript as
one random oracle on (context, role, message prefix) is `Lfzk.NizkDeployedHash`'s.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkZkDeployedHash

open Finset Bcs Bcs.TotalOracleCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkDeployedHash
  Lfzk.NizkDeployedHashAdaptive Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit
  Lfzk.NizkZk Lfzk.CertifiedV1
open scoped Classical

/-! ## 1. `hcongr` for the zero-knowledge chain -/

section Congr

variable {C S Cand Msg : Type} {nl : ℕ} {w : ℕ → ℕ}

/-- **A message-local chain family reads messages causally**: its doom at a prefix of length `j`
reads only messages `< j` — the `hcongr` of `NizkDeployedHash.shed_at_msgPoint_of`. -/
theorem doomed_congr_of_msgLocal
    {chainOf : (ℕ → Msg) → Bcs.ClaimChain C (Rounds.Role.length nl w) S Cand}
    (hloc : MsgLocal chainOf) (ms ms' : ℕ → Msg) (j : ℕ) (h : ∀ i, i < j → ms i = ms' i)
    (p : Fin j → C) : (chainOf ms).doomed j p ↔ (chainOf ms').doomed j p := by
  unfold Bcs.ClaimChain.doomed
  rw [state_congrG hloc j h p, hloc.wrong ms ms']

end Congr

section ZkCongr

variable {C F X Q Msg Gpt Lift : Type} [Field F] [SumcheckInterp F]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}

/-- **The zero-knowledge chain's `hcongr`**: each step reads only its own message, and start and
doom read none, so the doom at a prefix of length `j` reads only messages `< j`. -/
theorem zkChain_doomed_congr (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (H : ZkHonest F Lift logw logc) (asg : Lift → LigeroAssignment ninp M F) (Sat : Lift → Prop)
    (LD : ZkLigeroData C X Q Msg V asg) (ms ms' : ℕ → Msg) (j : ℕ)
    (h : ∀ i, i < j → ms i = ms' i) (p : Fin j → C) :
    (chain (nl := nl) (w := w) V H asg Sat LD ms).doomed j p ↔
      (chain (nl := nl) (w := w) V H asg Sat LD ms').doomed j p :=
  doomed_congr_of_msgLocal (zkChain_msgLocal V H asg Sat LD) ms ms' j h p

end ZkCongr

/-! ## 2. One field, a re-committing prefix-only prover -/

section Adaptive

/--
**The zero-knowledge LayerStep against a re-committing prefix-only Fiat–Shamir prover, at a
certified V1 row, with no bound on the prover's Merkle queries.**

Over a Merkle tape of any length `TM` with room for the run (`2n + tA ≤ TM`) and the total random
oracle on the deployed hash inputs `MPoint D Msg nl w`, against one program making `tA`
Merkle-oracle and `N` challenge-oracle queries:

```text
Pr[ JointAccepts  ∧  no lift-list member's witness satisfies the circuit ]
    ≤  zkCore  +  N · R.zkCoefficient logv  +  adaptiveNumerator (2n) tA (L + N) / 2^digestBits
```

`zkCore` is the field densities with the list factor and the Ligero densities (`zkCoreAt`); the last
term is the exact Merkle extraction count, quadratic in `tA` (the birthday term of the Merkle hash).
`row_zk_deployed_adaptive_ratio_le` is this at `TM = R.tape`, `tA ≤ R.commitFuel`.
-/
theorem row_zk_deployed_adaptive_ratio_leT {R : Row} (_h : R.Valid) (logv : ℕ)
    {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    {F X Q : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    {M ninp logw logc : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt Mc : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited Mc]
    {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N TM : ℕ}
    {codec : Codec Salt Mc D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening Mc n)
    (body : TwoOracleTree Enc D (MPoint D Msg R.params.nl R.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D)
    (statementOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (V : ZkCode C F X Q Msg (Fin logv → F) M ninp logw logc)
    (Lift : D × List (Enc × D) → Type) [∀ κ, Fintype (Lift κ)]
    (hcand : ∀ κ, Fintype.card (Lift κ) ≤ R.cardCand)
    (H : ∀ κ, ZkHonest F (Lift κ) logw logc)
    (asg : ∀ κ, Lift κ → LigeroAssignment ninp M F)
    (Sat : ∀ κ, Lift κ → Prop)
    (FD : ∀ κ, ZkFieldData C F X Q Msg (Fin logv → F) (Lift κ) M ninp logw logc R.params.nl
      R.params.rounds V (H κ) (asg κ) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (LD : ∀ κ, ZkLigeroData C X Q Msg V (asg κ))
    (hesc : ∀ κ sys, Fits V sys → NoSat (asg κ) sys →
      (((LD κ).escaping sys).card : ℚ) ≤ (R.params.row.fail + R.params.row.arith)
        * Fintype.card X)
    (hbq : ∀ κ, (LD κ).bq ≤ LigeroV1LayerStep.queryCount R.params.row)
    (hQ : Fintype.card Q = R.params.row.n.choose R.params.row.openings)
    (hright : ∀ (mt : Fin TM → D) (ro : MPoint D Msg R.params.nl R.params.rounds → C),
      JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
        claimOf statementOf responseOf challengeOf queryOf mt ro →
      (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R.params.nl) (w := R.params.rounds) V
          (LD ((lfSetup body rootOf msgOf).context mt ro))
          (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
        ((lfSetup body rootOf msgOf).challenges mt ro))
    (htape : 2 * n + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin TM → D) × (MPoint D Msg R.params.nl R.params.rounds → C) =>
        JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf)
            rootOf claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg R.params.nl R.params.rounds))
      ≤ zkCoreAt R logv R.cardCand + N * R.zkCoefficient logv
        + (AdaptiveCommit.adaptiveNumerator (2 * n) tA
            (Rounds.Role.length R.params.nl R.params.rounds + N) : ℚ)
          / 2 ^ R.params.digestBits := by
  classical
  set S := lfSetup body rootOf msgOf with hS
  have hFpos : 0 < R.params.row.fieldSize := by rw [← hF]; exact Fintype.card_pos
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  set bz := zkPairBudget (Fintype.card C) R.params.row.fieldSize logv
  set bp := pairBudget (Fintype.card C) R.params.row.fieldSize
  set bi := inBudget (Fintype.card C) R.params.row.fieldSize
  set bl := ligBudget R.params.row (Fintype.card C)
  set bq := queryBudget R.params.row (Fintype.card C)
  have hB : ∀ κ, ZkBudgets (FD κ) (LD κ) bz bp bi bl bq := by
    intro κ
    obtain ⟨hbin, hini, hpr, hk, hch, hqq⟩ := hexact κ
    have hF' : 0 < Fintype.card F := Fintype.card_pos
    obtain ⟨e0, e1, e2, e3⟩ := zk_field_budgets (cardC := Fintype.card C) hF' hbin hini hpr hk
    have ez : zkPairBudget (Fintype.card C) (Fintype.card F) logv = bz := by rw [hF]
    have ep : pairBudget (Fintype.card C) (Fintype.card F) = bp := by rw [hF]
    have ei : inBudget (Fintype.card C) (Fintype.card F) = bi := by rw [hF]
    refine ⟨e0.trans_eq ez, e1.trans_eq ez, e2.trans_eq ep, e3.trans_eq ei,
      fun sys hf hn => ?_, ?_⟩
    · exact LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
        (LigeroV1LayerStep.arith_nonneg _)) (hesc κ sys hf hn) hch
    · refine le_trans (Nat.mul_le_mul_left _ (hbq κ)) ?_
      refine LigeroV1LayerStep.mul_le_floor (cardY := R.params.row.n.choose R.params.row.openings)
        (LigeroV1LayerStep.cover_nonneg _) ?_ (by rw [← hQ]; exact hqq)
      exact Nat.floor_le (mul_nonneg (LigeroV1LayerStep.cover_nonneg _) (Nat.cast_nonneg _))
  -- the chain per context, and its congruence in the messages
  let chainZ : ∀ κ, (ℕ → Msg) → Bcs.ClaimChain C (Rounds.Role.length R.params.nl R.params.rounds)
      (ZkState M ninp logw logc F X) (Option (Lift κ)) := fun κ ms =>
    chain (nl := R.params.nl) (w := R.params.rounds) V (H κ) (asg κ) (Sat κ) (LD κ) ms
  have hcongr : ∀ κ (ms ms' : ℕ → Msg) (j : ℕ), (∀ i, i < j → ms i = ms' i) →
      ∀ p : Fin j → C, (chainZ κ ms).doomed j p ↔ (chainZ κ ms').doomed j p :=
    fun κ => zkChain_doomed_congr V (H κ) (asg κ) (Sat κ) (LD κ)
  -- the bad event at a point, in a context, at its ancestors' answers
  obtain ⟨Bad, hBad⟩ : ∃ Bad : D × List (Enc × D) →
      (x : MPoint D Msg R.params.nl R.params.rounds) →
        (Fin ((mpoints (Ctx := D) (Msg := Msg)).slot x) → C) → C → Prop,
      Bad = fun κ x pref c => ZkFails Sat κ ∧
        (chainZ κ x.msgFn).doomed ((mpoints (Ctx := D) (Msg := Msg)).slot x) pref ∧
        ¬ (chainZ κ x.msgFn).doomed ((mpoints (Ctx := D) (Msg := Msg)).slot x + 1)
          (Bcs.extend pref c) := ⟨_, rfl⟩
  let beta : MPoint D Msg R.params.nl R.params.rounds → ℕ := fun q =>
    mixedBudget (nl := R.params.nl) (w := R.params.rounds) R.cardCand bz bp bi bl bq q.role
  have hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x := by
    intro κ x pref
    by_cases hκ : ZkFails Sat κ
    · by_cases hd : (chainZ κ x.msgFn).doomed ((mpoints (Ctx := D) (Msg := Msg)).slot x) pref
      · have hpres := (FD κ).doom_preserved_chain (LD κ) (hB κ) x.msgFn x.role.index pref hd
        rw [indexEquiv_symm_index] at hpres
        refine le_trans (Finset.card_le_card ?_)
          (le_trans hpres (mixedBudget_mono (hcand κ) bz bp bi bl bq x.role))
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad] at hc ⊢
        exact hc.2.2
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad] at hc
        exact absurd hc.2.1 hd
    · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, hBad] at hc
      exact absurd hc.1 hκ
  set βmax := NizkGrinding.maxBudget (R.cardCand * bz) (R.cardCand * bp)
    (R.cardCand * bi) bl bq with hβmax
  have hmax : ∀ q, beta q ≤ βmax := fun q => classBudget_le_max q.role
  let slotBeta : Fin (Rounds.Role.length R.params.nl R.params.rounds) → ℕ := fun i =>
    mixedBudget (nl := R.params.nl) (w := R.params.rounds) R.cardCand bz bp bi bl bq
      (Rounds.Role.indexEquiv.symm i)
  have hslot : ∀ (out : Out) (i : Fin (Rounds.Role.length R.params.nl R.params.rounds)),
      beta (S.hashInput out i.val) ≤ slotBeta i := by
    intro out i
    show mixedBudget (nl := R.params.nl) (w := R.params.rounds) R.cardCand bz bp bi bl bq
        (roleAt i.val) ≤ _
    rw [roleAt_val]
  have hsum : ∑ i, slotBeta i
      = R.cardCand * (R.params.nl * bz
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi) + bl + bq :=
    mixed_budget_sum (nl := R.params.nl) (w := R.params.rounds) _ _ _ _ _ _
  -- the chain: the sequential escape at the proof's messages, at the verifier's point
  have hchain : ∀ (mt : Fin TM → D) (ro : MPoint D Msg R.params.nl R.params.rounds → C),
      JointAccepts K codec S (NizkAdaptive.lfCheck codec claimOf) rootOf claimOf statementOf
        responseOf challengeOf queryOf mt ro →
      S.Explains dec id claimOf mt ro → ZkFails Sat (S.context mt ro) →
      (S.grinding mt mpoints Bad beta hbad).RoundBad ro := by
    intro mt ro hacc' hexp hκ
    set κ := S.context mt ro with hκdef
    set out := S.proof mt ro with hout
    have hz := hright mt ro hacc' hexp
    obtain ⟨k, hd, he⟩ := (FD κ).exists_escape_chain (LD κ) (hB κ) (msgOf out)
      (S.challenges mt ro) hκ hz
    have hsh := shed_at_msgPoint_of (fun ms => (chainZ κ ms).doomed) (hcongr κ) (rootOf out) msgOf
      out ro k hd he
    refine ⟨k, ?_⟩
    rw [S.grinding_ctx_point mt mpoints Bad beta hbad ro k.val,
      S.grinding_point mt mpoints Bad beta hbad ro k.val]
    subst hBad
    exact ⟨hκ, hsh⟩
  -- the generic count
  have hgen := S.ratio_le codec dec (NizkAdaptive.lfCheck codec claimOf) id claimOf
    (NizkAdaptive.lfCheck_trace codec claimOf) mpoints Bad beta hbad βmax hmax slotBeta hslot
    (length_pos R) (by omega) htape (by omega)
    (fun mt ro => JointAccepts K codec S (NizkAdaptive.lfCheck codec claimOf) rootOf claimOf
      statementOf responseOf challengeOf queryOf mt ro) (ZkFails Sat)
    (fun mt ro hacc' => hacc'.2.1) hchain
  refine le_trans hgen ?_
  -- the densities
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hseq := budgets_le_zkCore R logv hCpos hFpos (cardCand := R.cardCand)
  have hmaxd := maxBudget_le_zkDensity R logv hCpos hFpos (cardCand := R.cardCand)
  have hDq : (Fintype.card D : ℚ) = 2 ^ R.params.digestBits := by rw [hD]; push_cast; rfl
  rw [hsum, hDq]
  have hsplit : ((N * βmax + (R.cardCand * (R.params.nl * bz
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi) + bl + bq) : ℕ) : ℚ)
        / (Fintype.card C : ℚ)
      = ((R.cardCand * (R.params.nl * bz
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi) + bl + bq : ℕ) : ℚ)
          / (Fintype.card C : ℚ)
        + N * ((βmax : ℚ) / (Fintype.card C : ℚ)) := by
    push_cast
    field_simp
    ring
  have hβ : (βmax : ℚ) / (Fintype.card C : ℚ) ≤ zkMaxDensityAt R logv R.cardCand := by
    rw [div_le_iff₀ hc]
    linarith
  rw [hsplit]
  have hcoef : R.zkCoefficient logv = zkMaxDensityAt R logv R.cardCand := rfl
  rw [hcoef]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hβ hN
  linarith


/-- **Closing the Merkle term at the row's fuel.**  With `tA ≤ R.commitFuel` and the run inside the
row's tape, the uncapped right-hand side is at most the row's: `zkCore + merkleTerm = zkBound`, and
the rest of the count is `tape · (L + N)` (`NizkAdaptive.adaptiveNumerator_le`). -/
theorem row_cap {R : Row} (_h : R.Valid) (logv : ℕ) {n tA N : ℕ} (htA : tA ≤ R.commitFuel)
    (htape : 2 * n + tA ≤ R.tape) :
    zkCoreAt R logv R.cardCand + N * R.zkCoefficient logv
        + (AdaptiveCommit.adaptiveNumerator (2 * n) tA
            (Rounds.Role.length R.params.nl R.params.rounds + N) : ℚ) / 2 ^ R.params.digestBits
      ≤ R.zkBound logv + N * R.zkCoefficient logv
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  have hnum := NizkAdaptive.adaptiveNumerator_le
    (Lfs := Rounds.Role.length R.params.nl R.params.rounds + N) htA htape
  have hb : R.zkBound logv = zkCoreAt R logv R.cardCand
      + (merkleNumerator R.commitFuel R.tape : ℚ) / 2 ^ R.params.digestBits := rfl
  have hq : (AdaptiveCommit.adaptiveNumerator (2 * n) tA
        (Rounds.Role.length R.params.nl R.params.rounds + N) : ℚ) / 2 ^ R.params.digestBits
      ≤ (merkleNumerator R.commitFuel R.tape : ℚ) / 2 ^ R.params.digestBits
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum) (by positivity)
  rw [hb]
  linarith


/--
**The zero-knowledge LayerStep against a re-committing prefix-only Fiat–Shamir prover, at a
certified V1 row.**

Over the Merkle tape and the total random oracle on the deployed hash inputs
`MPoint D Msg nl w` (root, role, messages through the round — no challenge), against one program
`body` interleaving at most `tA` Merkle-oracle and `N` challenge-oracle queries:

```text
Pr[ JointAccepts  ∧  no lift-list member's witness satisfies the circuit ]
    ≤  R.zkBound logv  +  N · R.zkCoefficient logv  +  R.tape · (L + N) / 2^digestBits
```

The context `κ = (root, cut trace)` is `(lfSetup body rootOf msgOf).context mt ro`.  The premises are
`NizkZk.Row.zk_adaptive_ratio_le`'s, with the proof, context and challenges those of the deployed
reading `NizkDeployedHashAdaptive.lfSetup` on `(mt, ro)`, plus `Fintype Msg`.
-/
theorem row_zk_deployed_adaptive_ratio_le {R : Row} (h : R.Valid) (logv : ℕ)
    {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    {F X Q : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    {M ninp logw logc : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt Mc : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited Mc]
    {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt Mc D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening Mc n)
    (body : TwoOracleTree Enc D (MPoint D Msg R.params.nl R.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D)
    (statementOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (V : ZkCode C F X Q Msg (Fin logv → F) M ninp logw logc)
    (Lift : D × List (Enc × D) → Type) [∀ κ, Fintype (Lift κ)]
    (hcand : ∀ κ, Fintype.card (Lift κ) ≤ R.cardCand)
    (H : ∀ κ, ZkHonest F (Lift κ) logw logc)
    (asg : ∀ κ, Lift κ → LigeroAssignment ninp M F)
    (Sat : ∀ κ, Lift κ → Prop)
    (FD : ∀ κ, ZkFieldData C F X Q Msg (Fin logv → F) (Lift κ) M ninp logw logc R.params.nl
      R.params.rounds V (H κ) (asg κ) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (LD : ∀ κ, ZkLigeroData C X Q Msg V (asg κ))
    (hesc : ∀ κ sys, Fits V sys → NoSat (asg κ) sys →
      (((LD κ).escaping sys).card : ℚ) ≤ (R.params.row.fail + R.params.row.arith)
        * Fintype.card X)
    (hbq : ∀ κ, (LD κ).bq ≤ LigeroV1LayerStep.queryCount R.params.row)
    (hQ : Fintype.card Q = R.params.row.n.choose R.params.row.openings)
    (hright : ∀ (mt : Fin R.tape → D) (ro : MPoint D Msg R.params.nl R.params.rounds → C),
      JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
        claimOf statementOf responseOf challengeOf queryOf mt ro →
      (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R.params.nl) (w := R.params.rounds) V
          (LD ((lfSetup body rootOf msgOf).context mt ro))
          (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
        ((lfSetup body rootOf msgOf).challenges mt ro))
    (htA : tA ≤ R.commitFuel) (htape : 2 * n + tA ≤ R.tape)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (MPoint D Msg R.params.nl R.params.rounds → C) =>
        JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf)
            rootOf claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg R.params.nl R.params.rounds))
      ≤ R.zkBound logv + N * R.zkCoefficient logv
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  refine le_trans (row_zk_deployed_adaptive_ratio_leT h logv dec K body rootOf msgOf claimOf
    statementOf responseOf challengeOf queryOf hF V Lift hcand H asg Sat FD hexact LD hesc hbq hQ
    hright htape (by have := Row.fuel_room h; omega) hD) ?_
  exact row_cap h logv htA htape

end Adaptive

/-! ## 3. Two fields, one prefix-only prover, hash side first -/

section Compose

open Lfzk.NizkZkTwoField (ZkSide)
open Lfzk.NizkAdaptiveTwoField (SideCtx check2 len2 sum_roleAt)
open Lfzk.NizkDeployedHashTwoField (Pt2 ctxOf hash2 hash2_zero hash2_side1 hash2_side2 pts2 pget
  pget_side1 pget_side2 setup2)
open Lfzk.Mac

variable {R₁ R₂ : Row} {logv₁ logv₂ : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ X₁ Q₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁]
  [SumcheckInterp F₁] [Fintype X₁] [DecidableEq X₁] [Fintype Q₁] [DecidableEq Q₁]
  [Inhabited Msg₁] [DecidableEq Msg₁] [Fintype Msg₁] {M₁ ninp₁ logw₁ logc₁ : ℕ}
variable {F₂ X₂ Q₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂]
  [SumcheckInterp F₂] [Fintype X₂] [DecidableEq X₂] [Fintype Q₂] [DecidableEq Q₂]
  [Inhabited Msg₂] [DecidableEq Msg₂] [Fintype Msg₂] {M₂ ninp₂ logw₂ logc₂ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Salt₁ Mc₁ Salt₂ Mc₂ : Type} [Inhabited Salt₁] [Inhabited Mc₁] [Inhabited Salt₂]
  [Inhabited Mc₂] {n₁ n₂ : ℕ}

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at the zero-knowledge LayerStep, against one re-committing prefix-only
Fiat–Shamir prover with a hashed MAC key, with no bound on the prover's Merkle queries.**

Over one Merkle tape of any length `TM` with room for the run (`2n₂ + 2n₁ + tA ≤ TM`, shared by both
sides' trees) and the total random oracle on the deployed hash inputs, against one program with
`tA` Merkle-oracle and `N` challenge-oracle queries:

```text
Pr[ both verifiers accept ∧ av = ro(key point) ∧ no two good witnesses agree on the common value ]
    ≤  zkCore₁ + zkCore₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^digestBits
```

`twofield_zk_deployed_adaptive_ratio_le` is this at `TM = R₁.tape`, `tA ≤ commitFuel`.
-/
theorem twofield_zk_deployed_adaptive_ratio_leT (_h₁ : R₁.Valid) {tA N TM : ℕ}
    {codec₁ : Codec Salt₁ Mc₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ Mc₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ Mc₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ Mc₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ Mc₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ Mc₂ D)
    (statementOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Statement₁) (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Statement₂) (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Query₂)
    (S₁ : ZkSide R₁ logv₁ (((D × D) × List (Enc × D)) × C × X) C F₁ X₁ Q₁ Msg₁ Witness₁
      M₁ ninp₁ logw₁ logc₁)
    (S₂ : ZkSide R₂ logv₂ (((D × D) × List (Enc × D)) × C × X) C F₂ X₂ Q₂ Msg₂ Witness₂
      M₂ ninp₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (_hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hright₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro))
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro →
      S.Explains dec₁ Prod.fst claimOf₁ mt ro →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.V σ) (S₁.LD σ)
          (msgOf₁ (S.proof mt ro)))
        (fun i => S.challenges mt ro ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro))
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro →
      S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.V σ) (S₂.LD σ)
          (msgOf₂ (S.proof mt ro)))
        (fun i => S.challenges mt ro
          ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩))
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro →
      S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro →
      S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * n₂ + 2 * n₁ + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        JointAccepts K₁ codec₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2 ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
              pubOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
              pubOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ zkCoreAt R₁ logv₁ R₁.cardCand + zkCoreAt R₂ logv₂ R₂.cardCand
        + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * ((AdaptiveCommit.adaptiveNumerator (2 * n₂ + 2 * n₁) tA (len2 R₁ R₂ + N) : ℚ)
          / 2 ^ R₁.params.digestBits) := by
  set S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ with hS
  set dflt : C := Classical.arbitrary C with hdflt
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have hFpos₁ : 0 < R₁.params.row.fieldSize := by rw [← hF₁]; exact Fintype.card_pos
  have hFpos₂ : 0 < R₂.params.row.fieldSize := by rw [← hF₂]; exact Fintype.card_pos
  set bz₁ := zkPairBudget (Fintype.card C) R₁.params.row.fieldSize logv₁
  set bp₁ := pairBudget (Fintype.card C) R₁.params.row.fieldSize
  set bi₁ := inBudget (Fintype.card C) R₁.params.row.fieldSize
  set bl₁ := ligBudget R₁.params.row (Fintype.card C)
  set bq₁ := queryBudget R₁.params.row (Fintype.card C)
  set bz₂ := zkPairBudget (Fintype.card C) R₂.params.row.fieldSize logv₂
  set bp₂ := pairBudget (Fintype.card C) R₂.params.row.fieldSize
  set bi₂ := inBudget (Fintype.card C) R₂.params.row.fieldSize
  set bl₂ := ligBudget R₂.params.row (Fintype.card C)
  set bq₂ := queryBudget R₂.params.row (Fintype.card C)
  have hB₁ := S₁.budgets hF₁
  have hB₂ := S₂.budgets hF₂
  have hcongr₁ : ∀ σ (ms ms' : ℕ → Msg₁) (j : ℕ), (∀ i, i < j → ms i = ms' i) →
      ∀ p : Fin j → C, (S₁.chainAt σ ms).doomed j p ↔ (S₁.chainAt σ ms').doomed j p :=
    fun σ => zkChain_doomed_congr (S₁.V σ) (S₁.H σ) (S₁.asg σ) (S₁.Sat σ) (S₁.LD σ)
  have hcongr₂ : ∀ σ (ms ms' : ℕ → Msg₂) (j : ℕ), (∀ i, i < j → ms i = ms' i) →
      ∀ p : Fin j → C, (S₂.chainAt σ ms).doomed j p ↔ (S₂.chainAt σ ms').doomed j p :=
    fun σ => zkChain_doomed_congr (S₂.V σ) (S₂.H σ) (S₂.asg σ) (S₂.Sat σ) (S₂.LD σ)
  -- the bad event at a point, by role, reading the ancestors' answers as a total function
  let L₁ := Rounds.Role.length R₁.params.nl R₁.params.rounds
  obtain ⟨Bad', hBad'⟩ : ∃ Bad' : (D × D) × List (Enc × D) →
      Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds →
        (ℕ → C) → C → Prop,
      Bad' = fun κ q g c => Sum.elim (fun _ => aP κ + decode c = 0)
        (Sum.elim
          (fun p => ZkFails S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2) ∧
            (S₁.chainAt (κ, p.ctx.2.1, p.ctx.2.2) p.msgFn).doomed p.role.slot
              (fun j => g (1 + j.val)) ∧
            ¬ (S₁.chainAt (κ, p.ctx.2.1, p.ctx.2.2) p.msgFn).doomed (p.role.slot + 1)
              (Bcs.extend (fun j => g (1 + j.val)) c))
          (fun p => ZkFails S₂.Sat (κ, p.ctx.1.2.1, p.ctx.1.2.2) ∧
            (S₂.chainAt (κ, p.ctx.1.2.1, p.ctx.1.2.2) p.msgFn).doomed p.role.slot
              (fun j => g (1 + L₁ + j.val)) ∧
            ¬ (S₂.chainAt (κ, p.ctx.1.2.1, p.ctx.1.2.2) p.msgFn).doomed (p.role.slot + 1)
              (Bcs.extend (fun j => g (1 + L₁ + j.val)) c))) q := ⟨_, rfl⟩
  let Bad : (D × D) × List (Enc × D) →
      (x : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds) →
        (Fin (pts2.slot x) → C) → C → Prop :=
    fun κ x pref c => Bad' κ x (pget dflt pref) c
  let beta : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds →
      ℕ := Sum.elim (fun _ => kmac) (Sum.elim
    (fun p => mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) R₁.cardCand
      bz₁ bp₁ bi₁ bl₁ bq₁ p.role)
    (fun p => mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) R₂.cardCand
      bz₂ bp₂ bi₂ bl₂ bq₂ p.role))
  have hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x := by
    intro κ x pref
    rcases x with r | p | p
    · refine le_trans (Finset.card_le_card ?_) (hbal (-aP κ))
      intro c hc
      simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inl] at hc ⊢
      linear_combination hc
    · set σ := (κ, p.ctx.2.1, p.ctx.2.2) with hσdef
      set g := pget dflt pref
      by_cases hd : (S₁.chainAt σ p.msgFn).doomed p.role.slot (fun j => g (1 + j.val))
      · have hpres := (S₁.FD σ).doom_preserved_chain (S₁.LD σ) (hB₁ σ) p.msgFn p.role.index
          (fun j => g (1 + j.val)) hd
        rw [indexEquiv_symm_index] at hpres
        refine le_trans (Finset.card_le_card ?_)
          (le_trans hpres (mixedBudget_mono (S₁.hcand σ) bz₁ bp₁ bi₁ bl₁ bq₁ p.role))
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr, Sum.elim_inl]
          at hc ⊢
        exact hc.2.2
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr, Sum.elim_inl] at hc
        exact absurd hc.2.1 hd
    · set σ := (κ, p.ctx.1.2.1, p.ctx.1.2.2) with hσdef
      set g := pget dflt pref
      by_cases hd : (S₂.chainAt σ p.msgFn).doomed p.role.slot (fun j => g (1 + L₁ + j.val))
      · have hpres := (S₂.FD σ).doom_preserved_chain (S₂.LD σ) (hB₂ σ) p.msgFn p.role.index
          (fun j => g (1 + L₁ + j.val)) hd
        rw [indexEquiv_symm_index] at hpres
        refine le_trans (Finset.card_le_card ?_)
          (le_trans hpres (mixedBudget_mono (S₂.hcand σ) bz₂ bp₂ bi₂ bl₂ bq₂ p.role))
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr] at hc ⊢
        exact hc.2.2
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr] at hc
        exact absurd hc.2.1 hd
  -- the worst point, and each verifier round's point
  set βmax := max kmac (max
    (NizkGrinding.maxBudget (R₁.cardCand * bz₁) (R₁.cardCand * bp₁) (R₁.cardCand * bi₁) bl₁ bq₁)
    (NizkGrinding.maxBudget (R₂.cardCand * bz₂) (R₂.cardCand * bp₂) (R₂.cardCand * bi₂) bl₂ bq₂))
    with hβmax
  have hmax : ∀ q, beta q ≤ βmax := by
    intro q
    rcases q with r | p | p
    · exact le_max_left _ _
    · exact le_trans (classBudget_le_max p.role) (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (classBudget_le_max p.role) (le_trans (le_max_right _ _) (le_max_right _ _))
  let g : ℕ → ℕ := fun k =>
    if k = 0 then kmac
    else if k < 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds then
      mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) R₁.cardCand
        bz₁ bp₁ bi₁ bl₁ bq₁ (roleAt (k - 1))
    else
      mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) R₂.cardCand
        bz₂ bp₂ bi₂ bl₂ bq₂ (roleAt (k - 1 - Rounds.Role.length R₁.params.nl R₁.params.rounds))
  let slotBeta : Fin (len2 R₁ R₂) → ℕ := fun i => g i.val
  have hslot : ∀ (out : Out) (i : Fin (len2 R₁ R₂)), beta (S.hashInput out i.val) ≤ slotBeta i := by
    intro out i
    show beta (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) ≤ g i.val
    unfold hash2
    simp only [g]
    split_ifs <;> exact le_rfl
  have hsum : ∑ i, slotBeta i
      = kmac + (R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁)
        + (R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂) := by
    rw [show (∑ i, slotBeta i) = ∑ i : Fin (len2 R₁ R₂), g i.val from rfl,
      Fin.sum_univ_eq_sum_range g, len2, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_range_one]
    have e0 : g 0 = kmac := by simp only [g, if_pos rfl]
    have e1 : ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds), g (1 + x)
        = ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds),
          mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) R₁.cardCand
            bz₁ bp₁ bi₁ bl₁ bq₁ (roleAt x) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_range.mp hx
      simp only [g]
      rw [if_neg (by omega), if_pos (by omega), show 1 + x - 1 = x by omega]
    have e2 : ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          g (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x)
        = ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) R₂.cardCand
            bz₂ bp₂ bi₂ bl₂ bq₂ (roleAt x) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [g]
      rw [if_neg (by omega), if_neg (by omega),
        show 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x - 1
          - Rounds.Role.length R₁.params.nl R₁.params.rounds = x by omega]
    rw [e0, e1, e2, sum_roleAt, sum_roleAt, mixed_budget_sum, mixed_budget_sum]
  -- the chain: the three-way split of the composed failure, at the verifier's rounds
  have hchain : ∀ (mt : Fin TM → D)
      (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      (JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
          statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro ∧
        JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
          statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro ∧
        S.challenges mt ro ⟨0, by omega⟩ = avOf (S.proof mt ro)) →
      S.Explains dec₁ Prod.fst claimOf₁ mt ro → S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      (¬ ∃ a₁ a₂,
        S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₁ ∧
        S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₂ ∧
        common₁ a₁ = common₂ a₂) →
      (S.grinding mt pts2 Bad beta hbad).RoundBad ro := by
    intro mt ro hacc hex₁ hex₂ hcomp
    set out := S.proof mt ro with hout
    set σ := (S.context mt ro, avOf out, pubOf out) with hσdef
    set ctx₁ := ctxOf rootOf₁ rootOf₂ avOf pubOf out with hctx₁
    by_cases hσ₁ : ZkFails S₁.Sat σ
    · -- side 1 has no good witness: its zero-knowledge LayerStep sheds doom at a side-1 round
      have hz := hright₁ mt ro hacc.1 hex₁
      let ro₁ : MPoint (SideCtx D C X) Msg₁ R₁.params.nl R₁.params.rounds → C :=
        fun p => ro (Sum.inr (Sum.inl p))
      have hch : (fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
          S.challenges mt ro ⟨1 + i.val, by omega⟩)
          = fun i => ro₁ (msgPoint ctx₁ msgOf₁ out i.val) := by
        funext i
        show ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + i.val)) = _
        rw [hash2_side1 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.isLt]
      rw [hch] at hz
      obtain ⟨k₁, hd, he⟩ := (S₁.FD σ).exists_escape_chain (S₁.LD σ) (hB₁ σ) (msgOf₁ out) _
        hσ₁ hz
      have hsh := shed_at_msgPoint_of (fun ms => (S₁.chainAt σ ms).doomed) (hcongr₁ σ) ctx₁
        msgOf₁ out ro₁ k₁ hd he
      refine ⟨⟨1 + k₁.val, by omega⟩, ?_⟩
      rw [S.grinding_ctx_point mt pts2 Bad beta hbad ro _,
        S.grinding_point mt pts2 Bad beta hbad ro _]
      show Bad' (S.context mt ro) (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k₁.val))
        (pget dflt (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k₁.val))))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k₁.val)))
      rw [hash2_side1 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out k₁.isLt, hBad']
      simp only [Sum.elim_inr, Sum.elim_inl]
      refine ⟨hσ₁, ?_⟩
      have hpre : (fun j : Fin (msgPoint (nl := R₁.params.nl) (w := R₁.params.rounds) ctx₁ msgOf₁
            out k₁.val).role.slot =>
          pget dflt (pts2.chal ro (Sum.inr (Sum.inl (msgPoint ctx₁ msgOf₁ out k₁.val))))
            (1 + j.val))
          = mpoints.chal ro₁ (msgPoint ctx₁ msgOf₁ out k₁.val) := by
        funext j
        rw [pget_side1]
        rfl
      rw [hpre]
      exact hsh
    by_cases hσ₂ : ZkFails S₂.Sat σ
    · -- side 2 has no good witness
      have hz := hright₂ mt ro hacc.2.1 hex₂
      set ctx₂ := (ctx₁, fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
        msgOf₁ out i.val) with hctx₂
      let ro₂ : MPoint (SideCtx D C X × (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds)
          → Msg₁)) Msg₂ R₂.params.nl R₂.params.rounds → C :=
        fun p => ro (Sum.inr (Sum.inr p))
      have hch : (fun i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) =>
          S.challenges mt ro
            ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩)
          = fun i => ro₂ (msgPoint ctx₂ msgOf₂ out i.val) := by
        funext i
        show ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val)) = _
        rw [hash2_side2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val]
      rw [hch] at hz
      obtain ⟨k₂, hd, he⟩ := (S₂.FD σ).exists_escape_chain (S₂.LD σ) (hB₂ σ) (msgOf₂ out) _
        hσ₂ hz
      have hsh := shed_at_msgPoint_of (fun ms => (S₂.chainAt σ ms).doomed) (hcongr₂ σ) ctx₂
        msgOf₂ out ro₂ k₂ hd he
      refine ⟨⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩, ?_⟩
      rw [S.grinding_ctx_point mt pts2 Bad beta hbad ro _,
        S.grinding_point mt pts2 Bad beta hbad ro _]
      show Bad' (S.context mt ro) (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val))
        (pget dflt (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val))))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val)))
      rw [hash2_side2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out k₂.val, hBad']
      simp only [Sum.elim_inr]
      refine ⟨hσ₂, ?_⟩
      have hpre : (fun j : Fin (msgPoint (nl := R₂.params.nl) (w := R₂.params.rounds) ctx₂ msgOf₂
            out k₂.val).role.slot =>
          pget dflt (pts2.chal ro (Sum.inr (Sum.inr (msgPoint ctx₂ msgOf₂ out k₂.val))))
            (1 + L₁ + j.val))
          = mpoints.chal ro₂ (msgPoint ctx₂ msgOf₂ out k₂.val) := by
        funext j
        rw [pget_side2]
        rfl
      rw [hpre]
      exact hsh
    -- both sides have good witnesses, which disagree: the MAC rows kill the multiplier
    simp only [ZkFails, not_forall, not_not] at hσ₁ hσ₂
    obtain ⟨ℓ₁, hs₁⟩ := hσ₁
    obtain ⟨ℓ₂, hs₂⟩ := hσ₂
    have hne : common₁ (S₁.wit _ ℓ₁) ≠ common₂ (S₂.wit _ ℓ₂) :=
      fun heq => hcomp ⟨_, _, ⟨ℓ₁, hs₁, rfl⟩, ⟨ℓ₂, hs₂, rfl⟩, heq⟩
    have hm₁ := hrow₁ mt ro _ hacc.1 ⟨ℓ₁, hs₁, rfl⟩
    have hm₂ := hrow₂ mt ro _ hacc.2.1 ⟨ℓ₂, hs₂, rfl⟩
    have hzero := macTag_collision hne (hm₁.trans hm₂.symm)
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [S.grinding_ctx_point mt pts2 Bad beta hbad ro _,
      S.grinding_point mt pts2 Bad beta hbad ro _]
    show Bad' (S.context mt ro) (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0)
      (pget dflt (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0)))
      (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0))
    have hav : ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0) = avOf out := hacc.2.2
    rw [hav, hash2_zero rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out, hBad']
    simp only [Sum.elim_inl]
    exact hzero
  -- the generic two-root count
  have hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I (claimOf₁ out).a (claimOf₁ out).pf (2 * n₁)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_left _ (NizkAdaptive.lfCheck_trace codec₁ claimOf₁ H out qa hqa)
  have hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a (claimOf₂ out).pf (2 * n₂)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_right _ (NizkAdaptive.lfCheck_trace codec₂ claimOf₂ H out qa hqa)
  have hgen := S.ratio_le_two codec₁ dec₁ codec₂ dec₂ (check2 codec₁ claimOf₁ codec₂ claimOf₂)
    Prod.fst Prod.snd claimOf₁ claimOf₂ hcheck₁ hcheck₂ pts2 Bad beta hbad βmax hmax slotBeta hslot
    (by omega) (by omega) htape (by omega)
    (fun mt ro => JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁
        claimOf₁ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro ∧
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro ∧
      S.challenges mt ro ⟨0, by omega⟩ = avOf (S.proof mt ro))
    (fun mt ro => ¬ ∃ a₁ a₂,
      S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₁ ∧
      S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₂ ∧
      common₁ a₁ = common₂ a₂)
    (fun mt ro h => h.1.2.1) (fun mt ro h => h.2.1.2.1) hchain
  refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card ?_))
    (by positivity)) (le_trans hgen ?_)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact ⟨⟨hω.1, hω.2.1, hω.2.2.1⟩, hω.2.2.2⟩
  -- the densities
  rw [hsum]
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hseq₁ := budgets_le_zkCore R₁ logv₁ hCpos hFpos₁ (cardCand := R₁.cardCand)
  have hseq₂ := budgets_le_zkCore R₂ logv₂ hCpos hFpos₂ (cardCand := R₂.cardCand)
  have hmacq := Lfzk.TwoFieldV1.mac_term_le (C := C) hmac
  set MM := max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
    (1 / (Fintype.card Fmac : ℚ)) with hMM
  have hβ : (βmax : ℚ) / (Fintype.card C : ℚ) ≤ MM := by
    rw [div_le_iff₀ hc, hβmax]
    push_cast
    have hk : (kmac : ℚ) ≤ MM * Fintype.card C := by
      have h := (div_le_iff₀ hc).mp hmacq
      have hle : 1 / (Fintype.card Fmac : ℚ) ≤ MM := le_max_right _ _
      nlinarith
    have h1 : ((NizkGrinding.maxBudget (R₁.cardCand * bz₁) (R₁.cardCand * bp₁)
          (R₁.cardCand * bi₁) bl₁ bq₁ : ℕ) : ℚ) ≤ MM * Fintype.card C := by
      have hmd := maxBudget_le_zkDensity R₁ logv₁ hCpos hFpos₁ (cardCand := R₁.cardCand)
      have hle : R₁.zkCoefficient logv₁ ≤ MM := le_trans (le_max_left _ _) (le_max_left _ _)
      have hκ : R₁.zkCoefficient logv₁ = zkMaxDensityAt R₁ logv₁ R₁.cardCand := rfl
      rw [← hκ] at hmd
      nlinarith
    have h2 : ((NizkGrinding.maxBudget (R₂.cardCand * bz₂) (R₂.cardCand * bp₂)
          (R₂.cardCand * bi₂) bl₂ bq₂ : ℕ) : ℚ) ≤ MM * Fintype.card C := by
      have hmd := maxBudget_le_zkDensity R₂ logv₂ hCpos hFpos₂ (cardCand := R₂.cardCand)
      have hle : R₂.zkCoefficient logv₂ ≤ MM := le_trans (le_max_right _ _) (le_max_left _ _)
      have hκ : R₂.zkCoefficient logv₂ = zkMaxDensityAt R₂ logv₂ R₂.cardCand := rfl
      rw [← hκ] at hmd
      nlinarith
    exact max_le hk (max_le h1 h2)
  have hDq : (Fintype.card D : ℚ) = 2 ^ R₁.params.digestBits := by rw [hD₁]; push_cast; rfl
  have hsplit : ((N * βmax + (kmac + (R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁)
        + (R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂)) : ℕ)
          : ℚ) / (Fintype.card C : ℚ)
      = N * ((βmax : ℚ) / (Fintype.card C : ℚ)) + (kmac : ℚ) / (Fintype.card C : ℚ)
        + ((R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁ : ℕ)
            : ℚ) / (Fintype.card C : ℚ)
        + ((R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂ : ℕ)
            : ℚ) / (Fintype.card C : ℚ) := by
    push_cast
    ring
  rw [hsplit, hDq]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hβ hN
  linarith


/-- **Closing both Merkle terms at the rows' fuel** (two-field): `zkCoreᵢ + merkleTermᵢ = zkBoundᵢ`
and the rest of each count is `tape · (len2 + N)`. -/
theorem twofield_cap {R₁ R₂ : Row} {logv₁ logv₂ : ℕ} {cardD fc tA N : ℕ} {m : ℚ} {K : ℚ}
    (hD₁ : cardD = 2 ^ R₁.params.digestBits) (hD₂ : cardD = 2 ^ R₂.params.digestBits)
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel) (htape : fc + tA ≤ R₁.tape)
    (htape₂ : R₁.tape = R₂.tape) :
    zkCoreAt R₁ logv₁ R₁.cardCand + zkCoreAt R₂ logv₂ R₂.cardCand + m + N * K
        + 2 * ((AdaptiveCommit.adaptiveNumerator fc tA (len2 R₁ R₂ + N) : ℚ)
          / 2 ^ R₁.params.digestBits)
      ≤ R₁.zkBound logv₁ + R₂.zkBound logv₂ + m + N * K
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  have hnum₁ := NizkAdaptive.adaptiveNumerator_le (Lfs := len2 R₁ R₂ + N) htA₁ htape
  have hnum₂ := NizkAdaptive.adaptiveNumerator_le (Lfs := len2 R₁ R₂ + N) htA₂ (htape₂ ▸ htape)
  have hdd : (2 : ℚ) ^ R₂.params.digestBits = 2 ^ R₁.params.digestBits := by
    have := hD₂.symm.trans hD₁
    exact_mod_cast this
  have hb₁ : R₁.zkBound logv₁ = zkCoreAt R₁ logv₁ R₁.cardCand
      + (merkleNumerator R₁.commitFuel R₁.tape : ℚ) / 2 ^ R₁.params.digestBits := rfl
  have hb₂ : R₂.zkBound logv₂ = zkCoreAt R₂ logv₂ R₂.cardCand
      + (merkleNumerator R₂.commitFuel R₂.tape : ℚ) / 2 ^ R₂.params.digestBits := rfl
  rw [hb₁, hb₂, hdd]
  have hpos : (0 : ℚ) < 2 ^ R₁.params.digestBits := by positivity
  have hq₁ : (AdaptiveCommit.adaptiveNumerator fc tA (len2 R₁ R₂ + N) : ℚ)
        / 2 ^ R₁.params.digestBits
      ≤ (merkleNumerator R₁.commitFuel R₁.tape : ℚ) / 2 ^ R₁.params.digestBits
        + ((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum₁) hpos.le
  have hq₂ : (AdaptiveCommit.adaptiveNumerator fc tA (len2 R₁ R₂ + N) : ℚ)
        / 2 ^ R₁.params.digestBits
      ≤ (merkleNumerator R₂.commitFuel R₂.tape : ℚ) / 2 ^ R₁.params.digestBits
        + ((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits := by
    rw [← add_div, htape₂]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum₂) hpos.le
  linarith

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at the zero-knowledge LayerStep, against one re-committing prefix-only
Fiat–Shamir prover with a hashed MAC key, in the deployed transcript order.**

Over one Merkle tape (`R₁.tape` slots, shared by both sides' trees) and the total random oracle on
the deployed hash inputs `NizkDeployedHashTwoField.Pt2`, against one program `body` with at most
`tA` Merkle-oracle and `N` challenge-oracle queries over all three roles (key point, side 1, side
2):

```text
Pr[ both verifiers accept ∧ av = ro(key point) ∧ no two good witnesses agree on the common value ]
    ≤  R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · R₁.tape · (1 + L₁ + L₂ + N) / 2^digestBits
```

The side context is `σ = (κ, avOf out, pubOf out)`: the commitment context of the pair of roots and
the public inputs the proof carries.  **Every premise**: per side a `NizkZkTwoField.ZkSide` and
`|F| = row.fieldSize`; per side `hright` (the side's acceptance, with its cut-trace extraction
explaining it, makes its zero-knowledge LayerStep accept at its slice of the verifier's challenges)
and `hrow` (the MAC row at the proof's `av`); the MAC data `aP`, `decode`, `hbal`, `hmac`; `|D|`;
the Merkle budget.
-/
theorem twofield_zk_deployed_adaptive_ratio_le (h₁ : R₁.Valid) {tA N : ℕ}
    {codec₁ : Codec Salt₁ Mc₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ Mc₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ Mc₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ Mc₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ Mc₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ Mc₂ D)
    (statementOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Statement₁) (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Statement₂) (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Query₂)
    (S₁ : ZkSide R₁ logv₁ (((D × D) × List (Enc × D)) × C × X) C F₁ X₁ Q₁ Msg₁ Witness₁
      M₁ ninp₁ logw₁ logc₁)
    (S₂ : ZkSide R₂ logv₂ (((D × D) × List (Enc × D)) × C × X) C F₂ X₂ Q₂ Msg₂ Witness₂
      M₂ ninp₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hright₁ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro))
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro →
      S.Explains dec₁ Prod.fst claimOf₁ mt ro →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.V σ) (S₁.LD σ)
          (msgOf₁ (S.proof mt ro)))
        (fun i => S.challenges mt ro ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro))
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro →
      S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.V σ) (S₂.LD σ)
          (msgOf₂ (S.proof mt ro)))
        (fun i => S.challenges mt ro
          ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩))
    (hrow₁ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro →
      S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro →
      S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel)
    (htape : 2 * n₂ + 2 * n₁ + tA ≤ R₁.tape) (htape₂ : R₁.tape = R₂.tape) :
    ((univ.filter fun ω : (Fin R₁.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        JointAccepts K₁ codec₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2 ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
              pubOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
              pubOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  refine le_trans (twofield_zk_deployed_adaptive_ratio_leT h₁ dec₁ dec₂ K₁ K₂ body rootOf₁ rootOf₂
    avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ statementOf₁ responseOf₁ challengeOf₁ queryOf₁
    statementOf₂ responseOf₂ challengeOf₂ queryOf₂ S₁ S₂ hF₁ hF₂ hD₁ hD₂ aP decode kmac hbal hmac
    keyB tagOf common₁ common₂ hright₁ hright₂ hrow₁ hrow₂ htape
    (by have := Row.fuel_room h₁; omega)) ?_
  exact twofield_cap (logv₁ := logv₁) (logv₂ := logv₂) hD₁ hD₂ htA₁ htA₂ htape htape₂

end Compose

end Lfzk.NizkZkDeployedHash
