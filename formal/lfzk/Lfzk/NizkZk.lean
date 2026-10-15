import Lfzk.ZkLigeroV1

/-!
# The zero-knowledge LayerStep against a re-committing Fiat–Shamir prover

`Lfzk.NizkGrinding` §3 and `Lfzk.NizkAdaptive` turn the clear verifier's round-by-round LayerStep
into a bound against an adaptive prover that interleaves Merkle-oracle and challenge-oracle queries.
This file does the same for the **zero-knowledge** LayerStep of `Lfzk.RbrZkSplit`, at the mixed
accounting (list factor at the field slots only).

## 1. The query points, for any message-indexed chain

`DoomedAtG`, `EscapesAtG`, `link_atG`, `escapesAt_cardG` are `NizkGrinding.DoomedAt`, `EscapesAt`,
`link_at`, `escapesAt_card` for an arbitrary family of claim chains indexed by the proof's
messages, under `MsgLocal` (start and doom do not read the messages; slot `i` reads message `i`
only).  The zero-knowledge chain is such a family (`zkChain_msgLocal`).  The query points and the
schedule are `NizkGrinding`'s and `NizkAdaptive`'s (`Point`, `hashPoint`, `lfSetup`): the
zero-knowledge verifier has the same `Rounds` schedule, with `begin_circuit`'s output point drawn in
layer 0's pair slot (`Lfzk.ZkMultilinear`).

## 2. The bound

```text
zkFieldDensity logv  =  (nl·(logv + 2) + 2·totalRounds + 1) / |F|
zkBound logv         =  cardCand · zkFieldDensity logv  +  (fail + arith)  +  cover  +  merkleTerm
zkCoefficient logv   =  max(cardCand · (logv + 2)/|F|, fail + arith, cover)
```

`logv + 2` per layer pair: layer 0's slot pays the output point's Schwartz–Zippel `logv/|F|` and
the pair's `2/|F|`, and the pair class is charged at its worst member.

## 3. The theorem (`Row.zk_adaptive_ratio_le`)

At a certified V1 row, against one adaptive program making at most `tA` Merkle-oracle and `N`
challenge-oracle queries, for an abstract compiled verifier `K` whose acceptance (with the
cut-trace extraction explaining it) implies that the zero-knowledge LayerStep on the proof's messages
accepts at the recomputed challenges (`hright`):

```text
Pr[ JointAccepts  ∧  no lift-list member's witness satisfies the circuit ]
    ≤  R.zkBound logv  +  N · R.zkCoefficient logv  +  R.tape · (L + N) / 2^digestBits
```

The candidates are a per-context type `Lift κ` of at most `R.cardCand` members; the Ligero half is
any `ZkLigeroData` with the row's densities (`Lfzk.ZkLigeroV1.exists_zkLigeroData` supplies it at
the extracted oracle).  **No falsity premise**: the Ligero doom is the state function's.
`Lfzk.CompiledZk` fixes `K` to the deployed verifier and proves `hright`.

## What is still a hypothesis here

Per context: the field data `FD κ` (the boundary facts and the layer-0 count, with exactly balanced
decoders, `ZkFieldData.ExactAt`), the Ligero half's two numerals (`hesc`, `hbq`), `|Lift κ| ≤
cardCand`, and `hright`.  Globally: `|F| = row.fieldSize`, `|D| = 2^digestBits`, the Merkle budget.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1. Query points for a message-indexed chain -/

namespace Lfzk.NizkZk

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit
open scoped Classical

section Generic

variable {C S Cand Msg Ctx Out : Type} [Fintype C] [Inhabited Msg] {nl : ℕ} {w : ℕ → ℕ}
variable (chainOf : (ℕ → Msg) → Bcs.ClaimChain C (Rounds.Role.length nl w) S Cand)

/-- **The chain family reads the messages round by round**: start and doom are message-blind, and
slot `i`'s transition reads message `i` only. -/
structure MsgLocal : Prop where
  init : ∀ ms ms' : ℕ → Msg, (chainOf ms).init = (chainOf ms').init
  wrong : ∀ ms ms' : ℕ → Msg, (chainOf ms).Wrong = (chainOf ms').Wrong
  step : ∀ (ms ms' : ℕ → Msg) (i : Fin (Rounds.Role.length nl w)), ms i.val = ms' i.val →
    (chainOf ms).step i = (chainOf ms').step i

/-- **Doom at a point**: the chain at the point's messages is doomed at the point's raw answers. -/
def DoomedAtG (dflt : C) (p : Point Ctx Msg C nl w) : Prop :=
  (chainOf (listMsgs p.msgs)).doomed p.role.slot (listPrefix dflt p.chals p.role.slot)

/-- **Escape at a point.** -/
def EscapesAtG (dflt : C) (p : Point Ctx Msg C nl w) (c : C) : Prop :=
  ¬ (chainOf (listMsgs p.msgs)).doomed (p.role.slot + 1)
    (Bcs.extend (listPrefix dflt p.chals p.role.slot) c)

variable {chainOf}

omit [Fintype C] [Inhabited Msg] in
/-- The state at a prefix of length `j` reads only the first `j` messages. -/
theorem state_congrG (hloc : MsgLocal chainOf) {ms ms' : ℕ → Msg} (j : ℕ)
    (h : ∀ i, i < j → ms i = ms' i) (p : Fin j → C) :
    (chainOf ms).state j p = (chainOf ms').state j p :=
  state_congr_below (chainOf ms) (chainOf ms') (hloc.init ms ms') j
    (fun i hi => hloc.step ms ms' i (h i.val hi)) j le_rfl p

omit [Fintype C] in
/-- **The link**: at round `k`'s hash input, the sequential escape at the proof's messages is the
point's bad event. -/
theorem link_atG (hloc : MsgLocal chainOf) (dflt : C) (ctx : Ctx) (msgOf : Out → ℕ → Msg)
    (out : Out) (k : ℕ) (cp : Fin k → C) (c : C) (hk : k < Rounds.Role.length nl w)
    (hd : (chainOf (msgOf out)).doomed k cp)
    (he : ¬ (chainOf (msgOf out)).doomed (k + 1) (Bcs.extend cp c)) :
    DoomedAtG chainOf dflt (hashPoint (nl := nl) (w := w) ctx msgOf out k cp) ∧
      EscapesAtG chainOf dflt (hashPoint (nl := nl) (w := w) ctx msgOf out k cp) c := by
  have hdoom : ∀ j, j ≤ k + 1 → ∀ q : Fin j → C,
      (chainOf (listMsgs (List.ofFn fun i : Fin (k + 1) => msgOf out i.val))).doomed j q ↔
        (chainOf (msgOf out)).doomed j q := by
    intro j hj q
    unfold Bcs.ClaimChain.doomed
    rw [state_congrG hloc j (fun i hi => listMsgs_ofFn (msgOf out) (by omega)) q,
      hloc.wrong (listMsgs (List.ofFn fun i : Fin (k + 1) => msgOf out i.val)) (msgOf out)]
  simp only [DoomedAtG, EscapesAtG, hashPoint]
  rw [slot_roleAt hk, listPrefix_ofFn]
  exact ⟨(hdoom k (by omega) cp).mpr hd, fun h => he ((hdoom (k + 1) le_rfl _).mp h)⟩

/-- **A point's escape budget**, from the chain family's slot-wise doom preservation at a role
budget. -/
theorem escapesAt_cardG (budget : Rounds.Role nl w → ℕ)
    (hpres : ∀ (ms : ℕ → Msg) (i : Fin (Rounds.Role.length nl w)) (pref : Fin i.val → C),
      (chainOf ms).doomed i.val pref →
      (univ.filter fun c : C => ¬ (chainOf ms).doomed (i.val + 1) (Bcs.extend pref c)).card
        ≤ budget (Rounds.Role.indexEquiv.symm i))
    (dflt : C) (p : Point Ctx Msg C nl w) (hp : DoomedAtG chainOf dflt p) :
    (univ.filter fun c : C => EscapesAtG chainOf dflt p c).card ≤ budget p.role := by
  have h := hpres (listMsgs p.msgs) p.role.index (listPrefix dflt p.chals p.role.slot) hp
  rw [indexEquiv_symm_index] at h
  refine le_trans (Finset.card_le_card ?_) h
  intro c hc
  simp only [mem_filter, mem_univ, true_and] at hc ⊢
  exact hc

end Generic

/-! ### The zero-knowledge chain is message-local -/

section ZkLocal

variable {C F X Q Msg Gpt Lift : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}

omit [Fintype C] [Fintype F] [DecidableEq F] in
/-- **The zero-knowledge chain reads message `i` at slot `i` only.** -/
theorem zkChain_msgLocal (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (H : ZkHonest F Lift logw logc) (asg : Lift → LigeroAssignment ninp M F) (Sat : Lift → Prop)
    (LD : ZkLigeroData C X Q Msg V asg) :
    MsgLocal (nl := nl) (w := w) (fun ms => chain (nl := nl) (w := w) V H asg Sat LD ms) where
  init _ _ := rfl
  wrong _ _ := rfl
  step ms ms' i h := by
    funext pref c s
    simp only [chain, layerStepChainS, stepAtS, steps, zkSteps]
    cases Rounds.Role.indexEquiv.symm i <;> simp only [h]

end ZkLocal

/-! ## 2. The bound functions and the budgets in densities -/

section Bound

open Lfzk.CertifiedV1

/-- The pair class's budget, `⌊(logv + 2)·|C|/|F|⌋`: layer 0's output point and pair, the worst
member of the class. -/
def zkPairBudget (cardC cardF logv : ℕ) : ℕ := (logv + 2) * cardC / cardF

/-- **The zero-knowledge field density** at an output-point dimension `logv`. -/
def zkFieldDensity (R : Row) (logv : ℕ) : ℚ :=
  ((R.params.nl * (logv + 2) + R.params.totalRounds * 2 + 1 : ℕ) : ℚ)
    / (R.params.row.fieldSize : ℚ)

/-- **The zero-knowledge bound at a list size**: the list factor on the field densities only. -/
def zkBoundAt (R : Row) (logv cardCand : ℕ) : ℚ :=
  (cardCand : ℚ) * zkFieldDensity R logv + R.params.ligeroDensity
    + R.params.merkleTerm R.commitFuel R.tape

/-- **The zero-knowledge bound** at the row's list size. -/
def _root_.Lfzk.CertifiedV1.Row.zkBound (R : Row) (logv : ℕ) : ℚ := zkBoundAt R logv R.cardCand

/-- The worst slot's density at a list size. -/
def zkMaxDensityAt (R : Row) (logv cardCand : ℕ) : ℚ :=
  max (max ((cardCand : ℚ) * (((logv + 2 : ℕ) : ℚ) / (R.params.row.fieldSize : ℚ)))
    (R.params.row.fail + R.params.row.arith)) R.params.row.cover

/-- **The zero-knowledge per-query coefficient.** -/
def _root_.Lfzk.CertifiedV1.Row.zkCoefficient (R : Row) (logv : ℕ) : ℚ := zkMaxDensityAt R logv R.cardCand

/-- **The field slots' budgets from exactly balanced decoders.** -/
theorem zk_field_budgets {cardC cardF logv kinit kpair k binit : ℕ} (hF : 0 < cardF)
    (hbinit : binit ≤ (logv + 2) * cardF ^ (logv + 1))
    (hinit : kinit * cardF ^ (logv + 2) ≤ cardC) (hpair : kpair * (cardF * cardF) ≤ cardC)
    (hk : k * cardF ≤ cardC) :
    kinit * binit ≤ zkPairBudget cardC cardF logv ∧
      kpair * (2 * cardF) ≤ zkPairBudget cardC cardF logv ∧
      k * 2 ≤ pairBudget cardC cardF ∧ k * 1 ≤ inBudget cardC cardF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold zkPairBudget
    rw [Nat.le_div_iff_mul_le hF]
    calc kinit * binit * cardF ≤ kinit * ((logv + 2) * cardF ^ (logv + 1)) * cardF :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hbinit)
      _ = (logv + 2) * (kinit * cardF ^ (logv + 2)) := by ring
      _ ≤ (logv + 2) * cardC := Nat.mul_le_mul_left _ hinit
  · unfold zkPairBudget
    rw [Nat.le_div_iff_mul_le hF]
    calc kpair * (2 * cardF) * cardF = 2 * (kpair * (cardF * cardF)) := by ring
      _ ≤ 2 * cardC := Nat.mul_le_mul_left _ hpair
      _ ≤ (logv + 2) * cardC := Nat.mul_le_mul_right _ (by omega)
  · unfold pairBudget
    rw [Nat.le_div_iff_mul_le hF]
    calc k * 2 * cardF = 2 * (k * cardF) := by ring
      _ ≤ 2 * cardC := Nat.mul_le_mul_left _ hk
  · unfold inBudget
    rw [Nat.le_div_iff_mul_le hF]
    calc k * 1 * cardF = k * cardF := by ring
      _ ≤ cardC := hk

/-- **The budgets, in densities.** -/
theorem budgets_le_zkBound (R : Row) (logv : ℕ) {cardC cardCand cardD : ℕ} (hC : 0 < cardC)
    (hF : 0 < R.params.row.fieldSize) (hD : cardD = 2 ^ R.params.digestBits) :
    ((cardCand * (R.params.nl * zkPairBudget cardC R.params.row.fieldSize logv
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
            * pairBudget cardC R.params.row.fieldSize
          + inBudget cardC R.params.row.fieldSize) + ligBudget R.params.row cardC
          + queryBudget R.params.row cardC : ℕ) : ℚ) / (cardC : ℚ)
        + (merkleNumerator R.commitFuel R.tape : ℚ) / (cardD : ℚ)
      ≤ zkBoundAt R logv cardCand := by
  have hc : (0 : ℚ) < (cardC : ℚ) := by exact_mod_cast hC
  have hf : (0 : ℚ) < (R.params.row.fieldSize : ℚ) := by exact_mod_cast hF
  set f : ℚ := (R.params.row.fieldSize : ℚ)
  set c : ℚ := (cardC : ℚ)
  have hfa := add_nonneg (LigeroV1LayerStep.fail_nonneg R.params.row)
    (LigeroV1LayerStep.arith_nonneg R.params.row)
  have hcv := LigeroV1LayerStep.cover_nonneg R.params.row
  have hbz : (zkPairBudget cardC R.params.row.fieldSize logv : ℚ)
      ≤ c * (((logv + 2 : ℕ) : ℚ) / f) := by
    unfold zkPairBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    push_cast
    ring
  have hbp : (pairBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (2 / f) := by
    unfold pairBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    push_cast
    ring
  have hbi : (inBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (1 / f) := by
    unfold inBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    ring
  have hbl : (ligBudget R.params.row cardC : ℚ) ≤ c * (R.params.row.fail + R.params.row.arith) := by
    unfold ligBudget
    refine le_trans (Nat.floor_le (mul_nonneg hfa (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have hbq : (queryBudget R.params.row cardC : ℚ) ≤ c * R.params.row.cover := by
    unfold queryBudget
    refine le_trans (Nat.floor_le (mul_nonneg hcv (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have hS : (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) = R.params.totalRounds := rfl
  have hfield :
      ((R.params.nl * zkPairBudget cardC R.params.row.fieldSize logv
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
            * pairBudget cardC R.params.row.fieldSize
          + inBudget cardC R.params.row.fieldSize : ℕ) : ℚ)
        ≤ c * zkFieldDensity R logv := by
    rw [hS]
    push_cast
    have h1 : (R.params.nl : ℚ) * (zkPairBudget cardC R.params.row.fieldSize logv : ℚ)
        ≤ (R.params.nl : ℚ) * (c * (((logv + 2 : ℕ) : ℚ) / f)) :=
      mul_le_mul_of_nonneg_left hbz (Nat.cast_nonneg _)
    have h2 : (R.params.totalRounds : ℚ) * (pairBudget cardC R.params.row.fieldSize : ℚ)
        ≤ (R.params.totalRounds : ℚ) * (c * (2 / f)) :=
      mul_le_mul_of_nonneg_left hbp (Nat.cast_nonneg _)
    have hrhs : c * zkFieldDensity R logv
        = (R.params.nl : ℚ) * (c * (((logv + 2 : ℕ) : ℚ) / f))
          + (R.params.totalRounds : ℚ) * (c * (2 / f)) + c * (1 / f) := by
      unfold zkFieldDensity
      push_cast
      field_simp
      ring
    rw [hrhs]
    push_cast at h1 ⊢
    linarith
  have hmerkle : (merkleNumerator R.commitFuel R.tape : ℚ) / (cardD : ℚ)
      = R.params.merkleTerm R.commitFuel R.tape := by
    unfold Lfzk.CostV1.Params.merkleTerm
    rw [hD]
    push_cast
    rfl
  unfold zkBoundAt
  rw [hmerkle]
  refine add_le_add ?_ le_rfl
  rw [div_le_iff₀ hc]
  have hk := mul_le_mul_of_nonneg_left hfield (Nat.cast_nonneg cardCand : (0 : ℚ) ≤ cardCand)
  have hlig : R.params.ligeroDensity = (R.params.row.fail + R.params.row.arith)
      + R.params.row.cover := rfl
  push_cast
  push_cast at hk
  rw [hlig]
  nlinarith [hk, hbl, hbq]

/-- **Every slot's budget is at most `|C|` times the worst density.** -/
theorem maxBudget_le_zkDensity (R : Row) (logv : ℕ) {cardC cardCand : ℕ} (hC : 0 < cardC)
    (hF : 0 < R.params.row.fieldSize) :
    (maxBudget (cardCand * zkPairBudget cardC R.params.row.fieldSize logv)
        (cardCand * pairBudget cardC R.params.row.fieldSize)
        (cardCand * inBudget cardC R.params.row.fieldSize) (ligBudget R.params.row cardC)
        (queryBudget R.params.row cardC) : ℚ)
      ≤ (cardC : ℚ) * zkMaxDensityAt R logv cardCand := by
  have hc : (0 : ℚ) < (cardC : ℚ) := by exact_mod_cast hC
  have hf : (0 : ℚ) < (R.params.row.fieldSize : ℚ) := by exact_mod_cast hF
  set f : ℚ := (R.params.row.fieldSize : ℚ)
  set c : ℚ := (cardC : ℚ)
  set k : ℚ := (cardCand : ℚ)
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg _
  have hv2 : (2 : ℚ) / f ≤ ((logv + 2 : ℕ) : ℚ) / f := by
    refine div_le_div_of_nonneg_right ?_ hf.le
    push_cast
    have : (0 : ℚ) ≤ (logv : ℚ) := Nat.cast_nonneg _
    linarith
  have hv1 : (1 : ℚ) / f ≤ ((logv + 2 : ℕ) : ℚ) / f := by
    refine div_le_div_of_nonneg_right ?_ hf.le
    push_cast
    have : (0 : ℚ) ≤ (logv : ℚ) := Nat.cast_nonneg _
    linarith
  have hfa := add_nonneg (LigeroV1LayerStep.fail_nonneg R.params.row)
    (LigeroV1LayerStep.arith_nonneg R.params.row)
  have hcv := LigeroV1LayerStep.cover_nonneg R.params.row
  have hbz : (zkPairBudget cardC R.params.row.fieldSize logv : ℚ)
      ≤ c * (((logv + 2 : ℕ) : ℚ) / f) := by
    unfold zkPairBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    push_cast
    ring
  have hbp : (pairBudget cardC R.params.row.fieldSize : ℚ)
      ≤ c * (((logv + 2 : ℕ) : ℚ) / f) := by
    have h0 : (pairBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (2 / f) := by
      unfold pairBudget
      refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
      push_cast
      ring
    exact le_trans h0 (mul_le_mul_of_nonneg_left hv2 hc.le)
  have hbi : (inBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (((logv + 2 : ℕ) : ℚ) / f) := by
    have h0 : (inBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (1 / f) := by
      unfold inBudget
      refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
      ring
    exact le_trans h0 (mul_le_mul_of_nonneg_left hv1 hc.le)
  have hbl : (ligBudget R.params.row cardC : ℚ) ≤ c * (R.params.row.fail + R.params.row.arith) := by
    unfold ligBudget
    refine le_trans (Nat.floor_le (mul_nonneg hfa (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have hbq : (queryBudget R.params.row cardC : ℚ) ≤ c * R.params.row.cover := by
    unfold queryBudget
    refine le_trans (Nat.floor_le (mul_nonneg hcv (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have h1 : c * (k * (((logv + 2 : ℕ) : ℚ) / f)) ≤ c * zkMaxDensityAt R logv cardCand :=
    mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_left _ _)) hc.le
  have h2 : c * (R.params.row.fail + R.params.row.arith) ≤ c * zkMaxDensityAt R logv cardCand :=
    mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) (le_max_left _ _)) hc.le
  have h3 : c * R.params.row.cover ≤ c * zkMaxDensityAt R logv cardCand :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le
  have hkz : k * (zkPairBudget cardC R.params.row.fieldSize logv : ℚ)
      ≤ c * (k * (((logv + 2 : ℕ) : ℚ) / f)) := by
    have := mul_le_mul_of_nonneg_left hbz hk
    linarith
  have hkp : k * (pairBudget cardC R.params.row.fieldSize : ℚ)
      ≤ c * (k * (((logv + 2 : ℕ) : ℚ) / f)) := by
    have := mul_le_mul_of_nonneg_left hbp hk
    linarith
  have hki : k * (inBudget cardC R.params.row.fieldSize : ℚ)
      ≤ c * (k * (((logv + 2 : ℕ) : ℚ) / f)) := by
    have := mul_le_mul_of_nonneg_left hbi hk
    linarith
  unfold maxBudget
  push_cast
  refine max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_ <;> linarith

/-- `mixedBudget` is monotone in the list factor. -/
theorem mixedBudget_mono {nl : ℕ} {w : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
    (bpair bround bin blig bquery : ℕ) (rl : Rounds.Role nl w) :
    mixedBudget (nl := nl) (w := w) a bpair bround bin blig bquery rl
      ≤ mixedBudget (nl := nl) (w := w) b bpair bround bin blig bquery rl := by
  cases rl <;> simp only [mixedBudget, RbrLayerStep.classBudget] <;>
    first | exact Nat.mul_le_mul_right _ hab | exact le_rfl

/-! ### The bound without its Merkle constant

`zkBoundAt` closes the Merkle extraction term at the row's fixed `commitFuel` and `tape`, so that a
headline is one number.  `zkCoreAt` is the rest, the part every adversary pays whatever its Merkle
budget; the Merkle term then stays the exact `adaptiveNumerator` count, a function of the
adversary's Merkle queries (`NizkZkDeployedHash.row_zk_deployed_adaptive_ratio_leT`). -/

/-- **The zero-knowledge bound without the Merkle term**: the field densities with the list factor,
and the Ligero densities. -/
def zkCoreAt (R : Row) (logv cardCand : ℕ) : ℚ :=
  (cardCand : ℚ) * zkFieldDensity R logv + R.params.ligeroDensity

theorem zkBoundAt_eq_core (R : Row) (logv cardCand : ℕ) :
    zkBoundAt R logv cardCand
      = zkCoreAt R logv cardCand + R.params.merkleTerm R.commitFuel R.tape := rfl

theorem zkCoreAt_nonneg (R : Row) (logv cardCand : ℕ) : 0 ≤ zkCoreAt R logv cardCand := by
  unfold zkCoreAt zkFieldDensity
  have hlig : R.params.ligeroDensity = (R.params.row.fail + R.params.row.arith)
      + R.params.row.cover := rfl
  rw [hlig]
  have := LigeroV1LayerStep.fail_nonneg R.params.row
  have := LigeroV1LayerStep.arith_nonneg R.params.row
  have := LigeroV1LayerStep.cover_nonneg R.params.row
  positivity

theorem zkCoreAt_le_zkBound (R : Row) (logv : ℕ) :
    zkCoreAt R logv R.cardCand ≤ R.zkBound logv := by
  show zkCoreAt R logv R.cardCand ≤ zkBoundAt R logv R.cardCand
  rw [zkBoundAt_eq_core]
  have : 0 ≤ R.params.merkleTerm R.commitFuel R.tape := by
    unfold Lfzk.CostV1.Params.merkleTerm
    positivity
  linarith

theorem zkCoefficient_nonneg (R : Row) (logv : ℕ) : 0 ≤ R.zkCoefficient logv :=
  le_trans (LigeroV1LayerStep.cover_nonneg R.params.row) (le_max_right _ _)

/-- **The budgets, in densities, without the Merkle term.** -/
theorem budgets_le_zkCore (R : Row) (logv : ℕ) {cardC cardCand : ℕ} (hC : 0 < cardC)
    (hF : 0 < R.params.row.fieldSize) :
    ((cardCand * (R.params.nl * zkPairBudget cardC R.params.row.fieldSize logv
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
            * pairBudget cardC R.params.row.fieldSize
          + inBudget cardC R.params.row.fieldSize) + ligBudget R.params.row cardC
          + queryBudget R.params.row cardC : ℕ) : ℚ) / (cardC : ℚ)
      ≤ zkCoreAt R logv cardCand := by
  have h := budgets_le_zkBound R logv hC hF (cardCand := cardCand)
    (cardD := 2 ^ R.params.digestBits) rfl
  rw [zkBoundAt_eq_core] at h
  have hmerkle : (merkleNumerator R.commitFuel R.tape : ℚ) / ((2 ^ R.params.digestBits : ℕ) : ℚ)
      = R.params.merkleTerm R.commitFuel R.tape := by
    unfold Lfzk.CostV1.Params.merkleTerm
    push_cast
    rfl
  rw [hmerkle] at h
  linarith

end Bound

/-! ## 3. Exactly balanced decoders for the zero-knowledge field half -/

section Exact

variable {C F X Q Msg Lift : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [DecidableEq X] [Fintype Q] [DecidableEq Q] [Fintype X]
variable {M ninp logw logc nl logv : ℕ} {w : ℕ → ℕ}
variable {V : ZkCode C F X Q Msg (Fin logv → F) M ninp logw logc} {H : ZkHonest F Lift logw logc}
  {asg : Lift → LigeroAssignment ninp M F} {Sat : Lift → Prop}

/-- **Exactly balanced decoders, and layer 0's count at its Schwartz–Zippel value.** -/
def _root_.Lfzk.RbrZkSplit.ZkFieldData.ExactAt
    (FD : ZkFieldData C F X Q Msg (Fin logv → F) Lift M ninp logw logc nl w V H asg Sat) : Prop :=
  FD.binit ≤ (logv + 2) * Fintype.card F ^ (logv + 1) ∧
    FD.kinit * Fintype.card F ^ (logv + 2) ≤ Fintype.card C ∧
    FD.kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C ∧
    FD.k * Fintype.card F ≤ Fintype.card C ∧
    FD.kchal * Fintype.card X ≤ Fintype.card C ∧
    FD.kq * Fintype.card Q ≤ Fintype.card C

end Exact

/-! ## 4. One field, a re-committing prover -/

/-- **Extraction fails at a context**: no lift-list member's witness satisfies the circuit.  A
definition (rather than the bare `∀`) so that every event mentioning it is decided the same way. -/
def ZkFails {K : Type} {Lift : K → Type} (Sat : ∀ κ, Lift κ → Prop) (κ : K) : Prop :=
  ∀ ℓ : Lift κ, ¬ Sat κ ℓ


section Adaptive

open Lfzk.CertifiedV1

/--
**The zero-knowledge LayerStep against a re-committing Fiat–Shamir prover, at a certified V1 row.**

```text
Pr[ JointAccepts  ∧  no lift-list member's witness satisfies the circuit ]
    ≤  R.zkBound logv  +  N · R.zkCoefficient logv  +  R.tape · (L + N) / 2^digestBits
```

The context `κ = (root, cut trace)` is `(lfSetup body dflt rootOf msgOf).context mt ct`.
**Every premise**:

* the verifier's code `V` (one, public), with exactly balanced decoders (`hexact`);
* per context: the candidates `Lift κ` (at most `cardCand`, `hcand`), the honest values `H κ`, the
  candidates' assignments `asg κ`, the satisfaction predicate `Sat κ`, the field data `FD κ`, and the
  Ligero half `LD κ` with the row's densities (`hesc`, `hbq`);
* `hright` — the compiled verifier's acceptance, with the cut-trace extraction explaining it,
  implies that the zero-knowledge LayerStep on the proof's messages accepts at the recomputed
  challenges with the query test of `LD κ`;
* `|F| = row.fieldSize`, `|D| = 2^digestBits`, the Merkle budget `tA ≤ commitFuel`, `2n + tA ≤ tape`.
-/
theorem _root_.Lfzk.CertifiedV1.Row.zk_adaptive_ratio_le {R : Row} (h : R.Valid) (logv : ℕ)
    {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    {F X Q : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    {M ninp logw logc : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt Mc : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited Mc]
    {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt Mc D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening Mc n)
    (body : TwoOracleTree Enc D (Point D Msg C R.params.nl R.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
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
    (hright : ∀ (mt : Fin R.tape → D) (ct : Fin (R.fsLen N) → C),
      JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
        statementOf responseOf challengeOf queryOf mt ct →
      (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R.params.nl) (w := R.params.rounds) V
          (LD ((lfSetup body dflt rootOf msgOf).context mt ct))
          (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
        ((lfSetup body dflt rootOf msgOf).challenges mt ct))
    (htA : tA ≤ R.commitFuel) (htape : 2 * n + tA ≤ R.tape)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (Fin (R.fsLen N) → C) =>
        JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape * (Fintype.card C : ℚ) ^ R.fsLen N)
      ≤ R.zkBound logv + N * R.zkCoefficient logv
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  classical
  set S := lfSetup body dflt rootOf msgOf with hS
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
  -- the chain per context
  let chainZ : ∀ κ, (ℕ → Msg) → Bcs.ClaimChain C (Rounds.Role.length R.params.nl R.params.rounds)
      (ZkState M ninp logw logc F X) (Option (Lift κ)) := fun κ ms =>
    chain (nl := R.params.nl) (w := R.params.rounds) V (H κ) (asg κ) (Sat κ) (LD κ) ms
  have hloc : ∀ κ, MsgLocal (chainZ κ) := fun κ => zkChain_msgLocal V (H κ) (asg κ) (Sat κ) (LD κ)
  obtain ⟨Bad, hBad⟩ : ∃ Bad : D × List (Enc × D) → Point D Msg C R.params.nl R.params.rounds →
      C → Prop, Bad = fun κ q c => ZkFails Sat κ ∧ DoomedAtG (chainZ κ) dflt q ∧
        EscapesAtG (chainZ κ) dflt q c := ⟨_, rfl⟩
  let beta : Point D Msg C R.params.nl R.params.rounds → ℕ := fun q =>
    mixedBudget (nl := R.params.nl) (w := R.params.rounds) R.cardCand bz bp bi bl bq q.role
  have hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q := by
    intro κ q
    by_cases hκ : ZkFails Sat κ
    · by_cases hd : DoomedAtG (chainZ κ) dflt q
      · refine le_trans (Finset.card_le_card ?_) (le_trans (escapesAt_cardG
          (mixedBudget (nl := R.params.nl) (w := R.params.rounds) (Fintype.card (Lift κ))
            bz bp bi bl bq)
          (fun ms i pref hd' => (FD κ).doom_preserved_chain (LD κ) (hB κ) ms i pref hd') dflt q hd)
          (mixedBudget_mono (hcand κ) _ _ _ _ _ _))
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
  have hslot : ∀ (out : Out) (i : Fin (Rounds.Role.length R.params.nl R.params.rounds))
      (cp : Fin i.val → C), beta (S.hashInput out i.val cp) ≤ slotBeta i := by
    intro out i cp
    show mixedBudget (nl := R.params.nl) (w := R.params.rounds) R.cardCand bz bp bi bl bq
        (roleAt i.val) ≤ _
    rw [roleAt_val]
  have hsum : ∑ i, slotBeta i
      = R.cardCand * (R.params.nl * bz
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi) + bl + bq :=
    mixed_budget_sum (nl := R.params.nl) (w := R.params.rounds) _ _ _ _ _ _
  -- the chain: the sequential escape of the zero-knowledge LayerStep, at a hash input
  have hchain : ∀ (mt : Fin R.tape → D) (ct : Fin (R.fsLen N) → C),
      JointAccepts K codec S (lfCheck codec claimOf) rootOf claimOf statementOf responseOf
        challengeOf queryOf mt ct →
      S.Explains dec id claimOf mt ct → ZkFails Sat (S.context mt ct) →
      (S.grinding mt Bad beta hbad).RoundBad ct := by
    intro mt ct hacc' hexp hκ
    have hz := hright mt ct hacc' hexp
    obtain ⟨k, hd, he⟩ := (FD (S.context mt ct)).exists_escape_chain (LD (S.context mt ct))
      (hB (S.context mt ct)) (msgOf (S.proof mt ct)) (S.challenges mt ct) hκ hz
    obtain ⟨hdq, hesq⟩ := link_atG (hloc (S.context mt ct)) dflt (rootOf (S.proof mt ct)) msgOf
      (S.proof mt ct) k.val (Sumcheck.extract_prefix (S.challenges mt ct) k)
      (S.challenges mt ct k) k.isLt hd he
    refine ⟨k, ?_⟩
    subst hBad
    exact ⟨hκ, hdq, hesq⟩
  have hgen := S.ratio_le codec dec (lfCheck codec claimOf) id claimOf (lfCheck_trace codec claimOf)
    Bad beta hbad βmax hmax slotBeta hslot (length_pos R) (by omega) htape
    (by have := Row.fuel_room h; omega) le_rfl
    (fun mt ct => JointAccepts K codec S (lfCheck codec claimOf) rootOf claimOf statementOf
      responseOf challengeOf queryOf mt ct) (ZkFails Sat)
    (fun mt ct hacc' => hacc'.2.1) hchain
  refine le_trans hgen ?_
  -- the densities
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hseq := budgets_le_zkBound R logv hCpos hFpos (cardCand := R.cardCand) hD
  have hmaxd := maxBudget_le_zkDensity R logv hCpos hFpos (cardCand := R.cardCand)
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
  have hbound : R.zkBound logv = zkBoundAt R logv R.cardCand := rfl
  have hcoef : R.zkCoefficient logv = zkMaxDensityAt R logv R.cardCand := rfl
  rw [hbound, hcoef]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hβ hN
  linarith

end Adaptive

end Lfzk.NizkZk
