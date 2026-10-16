import Bcs.AdaptiveCommit
import Bcs.TotalOracle

/-!
# A re-committing prover against a total random oracle on message prefixes

`Bcs.AdaptiveCommit` handles a prover that interleaves Merkle-oracle and challenge-oracle queries and
may re-commit, with the challenge oracle **lazily sampled** and hash inputs carrying the raw earlier
answers.  This file is the same composition with the challenge oracle a **total** random oracle
`H : Pt → C` on prefix-only hash inputs (`Bcs.TotalOracle`), so that `N` counts deployed hash
queries.

## How the lazy machinery is reused

Fix the oracle `H`.  `answerRight H body` is the prover with every challenge answer replaced by
`H`'s, whatever the challenge tape says; so at the **empty** challenge tape `emptyTape`,
`Bcs.AdaptiveCommit.Setup` of `answerRight H body` (`atOracle H`) runs exactly the prover against
`H`.  Its proof is `((search mt).run H).1` (`proof_eq`), its cut-trace context is the commitment the
proof names, and `Bcs.AdaptiveCommit.Setup.merkle_card_le` applies to it **verbatim**, for every
`H`: the Merkle count is a statement about Merkle tapes at a fixed challenge side.

The one new fact is on the challenge side: **the context of the key a point names does not read
that point's answer** (`ctxAt_off`).  The cut of key `k` is at its first naming challenge query, so
when `x` names `k` the cut is at or before `x`'s first query, and the cut run answers only challenge
queries strictly before it — none of them `x`.  `stop_chal_congr` / `stop_merkle_congr` are that,
by induction on the prover; `List.findIdx_take` pins the cut index.

## What is proved

* `answerRight`, `answerWith`, `fixLeft_answerRight`, `lazyRun_answerWith_fst` — answering from `H`;
* `stop_chal_congr`, `stop_merkle_congr` — a truncated run that has not answered `x` is the same
  under two oracles that agree off `x`, on both sides;
* `Setup.ctxAt_off` — the context is fixed off the point; `Setup.grinding` — the Fiat–Shamir side at
  a Merkle tape as a `Bcs.TotalOracle.CtxGrinding`;
* `Setup.ratio_le`:

```text
Pr_{mt, H}[ Acc  ∧  Fails(context of the proof's key) ]
    ≤  (N · βmax + ∑ k, slotBeta k) / |C|  +  adaptiveNumerator fc tA (L + N) / |D|
```

— `Bcs.AdaptiveCommit.Setup.ratio_le`'s right-hand side, with `N` the prover's prefix-only queries.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracleCommit

open Finset Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
  Bcs.AdaptiveCommit Bcs.TotalOracle
open scoped Classical

/-! ## 1. Answering from a total oracle -/

section Answer

variable {QL DL QR DR A : Type}

/-- **The prover with its challenge answers taken from `H`**: every right query is still made (so
the cut structure is unchanged), but its continuation reads `H q`, not the right oracle's answer. -/
def answerRight (H : QR → DR) :
    {l r : ℕ} → TwoOracleTree QL DL QR DR A l r → TwoOracleTree QL DL QR DR A l r
  | _, _, .done a => .done a
  | _, _, .queryLeft q next => .queryLeft q fun y => answerRight H (next y)
  | _, _, .queryRight q next => .queryRight q fun _ => answerRight H (next (H q))

/-- A one-oracle program with its answers taken from `H`. -/
def answerWith (H : QR → DR) : {n : ℕ} → Tree QR DR A n → Tree QR DR A n
  | _, .done a => .done a
  | _, .query q next => .query q fun _ => answerWith H (next (H q))

theorem fixLeft_answerRight [DecidableEq QL] {TL : ℕ} (mt : Fin TL → DL) (dL : DL)
    (H : QR → DR) :
    ∀ {l r : ℕ} (τ : TwoOracleTree QL DL QR DR A l r) (sL : List QL),
      fixLeft mt dL (answerRight H τ) sL = answerWith H (fixLeft mt dL τ sL) := by
  intro l r τ
  induction τ with
  | done a => intro sL; rfl
  | queryLeft q next ih =>
      intro sL
      simp only [answerRight, fixLeft]
      exact ih _ _
  | queryRight q next ih =>
      intro sL
      simp only [answerRight, fixLeft, answerWith]
      exact congrArg (Tree.query q) (funext fun _ => ih (H q) sL)

/-- **A lazily-sampled run of a program answered from `H` outputs what the run against `H`
does.** -/
theorem lazyRun_answerWith_fst [DecidableEq QR] {T : ℕ} (tape : Fin T → DR) (d : DR)
    (H : QR → DR) :
    ∀ {n : ℕ} (t : Tree QR DR A n) (seen : List QR),
      (lazyRun tape d (answerWith H t) seen).1 = (t.run H).1 := by
  intro n t
  induction t with
  | done a => intro seen; rfl
  | query q next ih =>
      intro seen
      rw [answerWith, lazyRun_query]
      exact ih (H q) _

end Answer

/-! ## 2. A truncated run that has not answered `x` does not read `H x` -/

section Congr

variable {QL DL QR DR A B : Type} [DecidableEq QL] [DecidableEq QR] {TL TR r₂ : ℕ}
variable (mt : Fin TL → DL) (dL : DL) (ct : Fin TR → DR) (dR : DR) (i : ℕ)
  (rec : A → Tree QR DR B r₂)

/-- **Challenge side.**  If the run truncated at the `i`-th distinct challenge query never asks `x`
under `H`, it is the same under any `H'` agreeing with `H` off `x`. -/
theorem stop_chal_congr (x : QR) {H H' : QR → DR} (hHH : AgreeOff x H H') :
    ∀ {l r : ℕ} (τ : TwoOracleTree QL DL QR DR A l r) (sR : List QR) (sL : List QL)
      (sRf : List QR),
      x ∉ (lazyRun ct dR (fixLeft mt dL (stopAt i ((answerRight H τ).bindRight rec) sR) sL)
        sRf).2.1 →
      lazyRun ct dR (fixLeft mt dL (stopAt i ((answerRight H' τ).bindRight rec) sR) sL) sRf
        = lazyRun ct dR (fixLeft mt dL (stopAt i ((answerRight H τ).bindRight rec) sR) sL) sRf := by
  intro l r τ
  induction τ with
  | done a => intro _ _ _ _; rfl
  | queryLeft q next ih =>
      intro sR sL sRf hx
      simp only [answerRight, bindRight, stopAt, fixLeft] at hx ⊢
      exact ih _ _ _ _ hx
  | queryRight q next ih =>
      intro sR sL sRf hx
      simp only [answerRight, bindRight, stopAt] at hx ⊢
      by_cases hstop : q ∉ sR ∧ sR.length = i
      · simp only [if_pos hstop]
      · simp only [if_neg hstop, fixLeft, lazyRun_query] at hx ⊢
        set sRf' := if q ∈ sRf then sRf else sRf ++ [q] with hsRf'
        set sR' := if q ∈ sR then sR else sR ++ [q] with hsR'
        have hq : q ∈ (lazyRun ct dR (fixLeft mt dL
            (stopAt i ((answerRight H (next (H q))).bindRight rec) sR') sL) sRf').2.1 := by
          refine (lazyRun_seen_prefix ct dR _ sRf').subset ?_
          by_cases h : q ∈ sRf
          · simp only [hsRf', if_pos h]; exact h
          · simp [hsRf', h]
        have hne : q ≠ x := fun he => hx (he ▸ hq)
        rw [← hHH q hne]
        rw [ih (H q) sR' sL sRf' hx]

/-- **Merkle side.**  Under the same hypothesis, the truncated run's Merkle-oracle program, run on
the Merkle tape, is the same under `H` and `H'`. -/
theorem stop_merkle_congr (x : QR) {H H' : QR → DR} (hHH : AgreeOff x H H') :
    ∀ {l r : ℕ} (τ : TwoOracleTree QL DL QR DR A l r) (sR : List QR) (sL : List QL)
      (sRf : List QR),
      x ∉ (lazyRun ct dR (fixLeft mt dL (stopAt i ((answerRight H τ).bindRight rec) sR) sL)
        sRf).2.1 →
      lazyRun mt dL (fixRight ct dR (stopAt i ((answerRight H' τ).bindRight rec) sR) sRf) sL
        = lazyRun mt dL (fixRight ct dR (stopAt i ((answerRight H τ).bindRight rec) sR) sRf) sL := by
  intro l r τ
  induction τ with
  | done a => intro _ _ _ _; rfl
  | queryLeft q next ih =>
      intro sR sL sRf hx
      simp only [answerRight, bindRight, stopAt, fixLeft, fixRight, lazyRun_query] at hx ⊢
      rw [ih _ _ _ _ hx]
  | queryRight q next ih =>
      intro sR sL sRf hx
      simp only [answerRight, bindRight, stopAt] at hx ⊢
      by_cases hstop : q ∉ sR ∧ sR.length = i
      · simp only [if_pos hstop]
      · simp only [if_neg hstop, fixLeft, fixRight, lazyRun_query] at hx ⊢
        set sRf' := if q ∈ sRf then sRf else sRf ++ [q] with hsRf'
        set sR' := if q ∈ sR then sR else sR ++ [q] with hsR'
        have hq : q ∈ (lazyRun ct dR (fixLeft mt dL
            (stopAt i ((answerRight H (next (H q))).bindRight rec) sR') sL) sRf').2.1 := by
          refine (lazyRun_seen_prefix ct dR _ sRf').subset ?_
          by_cases h : q ∈ sRf
          · simp only [hsRf', if_pos h]; exact h
          · simp [hsRf', h]
        have hne : q ≠ x := fun he => hx (he ▸ hq)
        rw [← hHH q hne]
        exact ih (H q) sR' sL sRf' hx

end Congr

/-! ## 3. The setup -/

/--
**A re-committing prover with prefix-only hash inputs.**  `Bcs.AdaptiveCommit.Setup` with the
verifier's round-`k` hash input read from the proof alone.
-/
structure Setup (Enc D Pt C Out Key : Type) (tA N L : ℕ) where
  /-- The prover's program. -/
  body : TwoOracleTree Enc D Pt C Out tA N
  /-- Round `k`'s hash input, from the proof alone. -/
  hashInput : Out → ℕ → Pt
  /-- The challenge answer the lazy machinery's empty tape gives; never read. -/
  dflt : C
  /-- The commitment a point names. -/
  key : Pt → Key
  /-- The commitment a proof names. -/
  keyOut : Out → Key
  /-- The verifier's points name the proof's commitment. -/
  hkey : ∀ (out : Out) (k : ℕ), key (hashInput out k) = keyOut out

namespace Setup

variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N L TM : ℕ}
variable (S : Setup Enc D Pt C Out Key tA N L)

/-- **The prover against `H`, as a lazy `Bcs.AdaptiveCommit.Setup`**: its challenge answers are
`H`'s, so the challenge tape it is run on does not matter. -/
def atOracle (H : Pt → C) : AdaptiveCommit.Setup Enc D Pt C Out Key tA N L where
  body := answerRight H S.body
  hashInput out k _ := S.hashInput out k
  dflt := S.dflt
  key := S.key
  keyOut := S.keyOut
  hkey out k _ := S.hkey out k

/-- The empty challenge tape. -/
def emptyTape : Fin 0 → C := Fin.elim0

/-- The verifier's recomputation, as a continuation: it does not depend on the oracle. -/
def recompute (out : Out) : Tree Pt C (Out × (ℕ → C)) L :=
  (Bcs.Recompute.rounds (fun k (_ : Fin k → C) => S.hashInput out k) L 0 fun _ => S.dflt).map
    fun acc => (out, acc)

omit [DecidableEq Enc] [Inhabited D] [DecidableEq Pt] in
theorem joint_atOracle (H : Pt → C) :
    (S.atOracle H).joint = (answerRight H S.body).bindRight S.recompute := rfl

/-- The prover's search at a fixed Merkle tape. -/
def search (mt : Fin TM → D) : Tree Pt C Out N := fixLeft mt default S.body []

/-- The proof on `(mt, H)`. -/
def proof (mt : Fin TM → D) (H : Pt → C) : Out := (S.atOracle H).proof mt emptyTape

/-- **The verifier's challenges**: round `k`'s is `H` at round `k`'s hash input. -/
def challenges (mt : Fin TM → D) (H : Pt → C) : Fin L → C :=
  fun k => H (S.hashInput (S.proof mt H) k.val)

/-- The context of the proof's key: the key and the Merkle queries made before the first challenge
query naming it. -/
def context [DecidableEq Key] (mt : Fin TM → D) (H : Pt → C) : Key × List (Enc × D) :=
  (S.atOracle H).context mt emptyTape

/-- The verifier's Merkle oracle on `(mt, H)`. -/
def merkleOracle {fc : ℕ} (check : Out → Tree Enc D Unit fc) (mt : Fin TM → D) (H : Pt → C) :
    Enc → D :=
  (S.atOracle H).merkleOracle check mt emptyTape

/-- **The proof is the search's output against `H`.** -/
theorem proof_eq (mt : Fin TM → D) (H : Pt → C) : S.proof mt H = ((S.search mt).run H).1 := by
  show ((lazyRun emptyTape S.dflt (execution ((S.atOracle H).search mt)
      (S.atOracle H).hashInput S.dflt L) []).1).1 = _
  rw [lazyRun_execution]
  show (lazyRun emptyTape S.dflt (fixLeft mt default (answerRight H S.body) []) []).1 = _
  rw [fixLeft_answerRight, lazyRun_answerWith_fst]
  rfl

/--
**The context is fixed off the point.**  The context of the key `x` names, under two oracles that
agree off `x`, is the same: the cut of that key is at or before `x`'s first query, and the cut run
answers only the challenge queries before the cut.
-/
theorem ctxAt_off [DecidableEq Key] (mt : Fin TM → D) (H H' : Pt → C) (x : Pt)
    (hHH : AgreeOff x H H') :
    (S.atOracle H').ctxAt mt emptyTape (S.key x) = (S.atOracle H).ctxAt mt emptyTape (S.key x) := by
  have hseen : ∀ G : Pt → C, (S.atOracle G).fsSeen mt emptyTape
      = (lazyRun emptyTape S.dflt (fixLeft mt default (S.atOracle G).joint []) []).2.1 := by
    intro G
    unfold AdaptiveCommit.Setup.fsSeen AdaptiveCommit.Setup.fsExec
    rw [(S.atOracle G).fixLeft_joint]
    rfl
  obtain ⟨lH, hlH⟩ : ∃ l, l = (S.atOracle H).fsSeen mt emptyTape := ⟨_, rfl⟩
  obtain ⟨lH', hlH'⟩ : ∃ l, l = (S.atOracle H').fsSeen mt emptyTape := ⟨_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, i = lH.findIdx fun q => decide (S.key q = S.key x) := ⟨_, rfl⟩
  have hcutH : (S.atOracle H).cutIdx mt emptyTape (S.key x) = i := by
    rw [hi, hlH]; rfl
  -- the run truncated at the cut, on each oracle
  obtain ⟨hsH, hoH⟩ := lazyRun_fixLeft_stopAt mt default emptyTape S.dflt i
    (S.atOracle H).joint [] [] (Nat.zero_le _)
  obtain ⟨hsH', hoH'⟩ := lazyRun_fixLeft_stopAt mt default emptyTape S.dflt i
    (S.atOracle H').joint [] [] (Nat.zero_le _)
  rw [← hseen H, ← hlH] at hsH hoH
  rw [← hseen H', ← hlH'] at hsH' hoH'
  -- before the cut, `x` is not asked: its key is the cut's
  have hxi : x ∉ lH.take i := by
    intro hmem
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hmem
    have hji : j < lH.findIdx fun q => decide (S.key q = S.key x) := by
      rw [List.length_take] at hj
      omega
    have hnot := List.not_of_lt_findIdx hji
    have hk : S.key (lH[j]'(lt_of_lt_of_le hji List.findIdx_le_length)) = S.key x := by
      have h := congrArg S.key hjx
      rwa [List.getElem_take] at h
    simp only [decide_eq_false_iff_not] at hnot
    exact hnot hk
  have hx : x ∉ (lazyRun emptyTape S.dflt (fixLeft mt default
      (stopAt i ((answerRight H S.body).bindRight S.recompute) []) []) []).2.1 := by
    rw [← S.joint_atOracle H, hsH]
    exact hxi
  have hrun := stop_chal_congr mt default emptyTape S.dflt i S.recompute x hHH S.body [] [] [] hx
  rw [← S.joint_atOracle H, ← S.joint_atOracle H'] at hrun
  -- so the first `i + 1` distinct queries agree, and the cut index is the same
  have htake : lH'.take i = lH.take i := by rw [← hsH', ← hsH, hrun]
  have hget : lH'[i]? = lH[i]? := by rw [← hoH', ← hoH, hrun]
  have htake1 : lH'.take (i + 1) = lH.take (i + 1) := by
    rw [List.take_add_one, List.take_add_one, htake, hget]
  have hcutH' : (S.atOracle H').cutIdx mt emptyTape (S.key x) = i := by
    have h1 : (lH.take (i + 1)).findIdx (fun q => decide (S.key q = S.key x)) = i := by
      rw [List.findIdx_take, ← hi]
      omega
    rw [← htake1, List.findIdx_take] at h1
    show ((S.atOracle H').fsSeen mt emptyTape).findIdx (fun q => decide (S.key q = S.key x)) = i
    rw [← hlH']
    omega
  -- and the cut runs' Merkle traces agree
  have hm := stop_merkle_congr mt default emptyTape S.dflt i S.recompute x hHH S.body [] [] [] hx
  unfold AdaptiveCommit.Setup.ctxAt AdaptiveCommit.Setup.cutTrace AdaptiveCommit.Setup.cutRun
  rw [hcutH, hcutH', S.joint_atOracle H, S.joint_atOracle H']
  show (S.key x, (lazyRun mt default (fixRight emptyTape S.dflt
      (stopAt i ((answerRight H' S.body).bindRight S.recompute) []) []) []).2.2)
    = (S.key x, (lazyRun mt default (fixRight emptyTape S.dflt
      (stopAt i ((answerRight H S.body).bindRight S.recompute) []) []) []).2.2)
  rw [hm]

/-- **The Fiat–Shamir side at a Merkle tape**, as a `Bcs.TotalOracle.CtxGrinding` whose context is
the cut-trace context. -/
def grinding [Fintype C] [DecidableEq Key] (mt : Fin TM → D) (pts : PrefixPoints Pt)
    (Bad : Key × List (Enc × D) → (x : Pt) → (Fin (pts.slot x) → C) → C → Prop) (beta : Pt → ℕ)
    (hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x) :
    TotalOracle.CtxGrinding C Pt Out Key (Key × List (Enc × D)) N L where
  adversary := S.search mt
  hashInput := S.hashInput
  pts := pts
  key := S.key
  ctxAt H k := (S.atOracle H).ctxAt mt emptyTape k
  ctxAt_off H H' x h := S.ctxAt_off mt H H' x h
  Bad := Bad
  beta := beta
  bad_bound := hbad

theorem grinding_proof [Fintype C] [DecidableEq Key] (mt : Fin TM → D) (pts : PrefixPoints Pt)
    (Bad : Key × List (Enc × D) → (x : Pt) → (Fin (pts.slot x) → C) → C → Prop) (beta : Pt → ℕ)
    (hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x)
    (H : Pt → C) : (S.grinding mt pts Bad beta hbad).proof H = S.proof mt H :=
  (S.proof_eq mt H).symm

/-- The context the grinding count reads at a verifier point is the proof's context. -/
theorem grinding_ctx_point [Fintype C] [DecidableEq Key] (mt : Fin TM → D) (pts : PrefixPoints Pt)
    (Bad : Key × List (Enc × D) → (x : Pt) → (Fin (pts.slot x) → C) → C → Prop) (beta : Pt → ℕ)
    (hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x)
    (H : Pt → C) (k : ℕ) :
    (S.grinding mt pts Bad beta hbad).ctxAt H
        ((S.grinding mt pts Bad beta hbad).key ((S.grinding mt pts Bad beta hbad).point H k))
      = S.context mt H := by
  show (S.atOracle H).ctxAt mt emptyTape
      (S.key (S.hashInput ((S.grinding mt pts Bad beta hbad).proof H) k)) = _
  rw [S.grinding_proof mt pts Bad beta hbad H, S.hkey]
  rfl

theorem grinding_point [Fintype C] [DecidableEq Key] (mt : Fin TM → D) (pts : PrefixPoints Pt)
    (Bad : Key × List (Enc × D) → (x : Pt) → (Fin (pts.slot x) → C) → C → Prop) (beta : Pt → ℕ)
    (hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x)
    (H : Pt → C) (k : ℕ) :
    (S.grinding mt pts Bad beta hbad).point H k = S.hashInput (S.proof mt H) k := by
  show S.hashInput ((S.grinding mt pts Bad beta hbad).proof H) k = _
  rw [S.grinding_proof mt pts Bad beta hbad H]

/-! ## 4. The Merkle side and the composed count -/

section Composed

variable [DecidableEq Key] [DecidableEq D] {Salt M : Type} [Inhabited Salt] [Inhabited M] {n fc : ℕ}

/-- The verifier's Merkle check accepts the proof's opening at the root its key names. -/
def MerkleAccepts (codec : Codec Salt M D Enc) (check : Out → Tree Enc D Unit fc)
    (rootOf : Key → D) (claimOf : Out → OpeningClaim n Salt M D)
    (mt : Fin TM → D) (H : Pt → C) : Prop :=
  (S.atOracle H).MerkleAccepts codec check rootOf claimOf mt emptyTape

/-- The cut-trace extraction explains the opening. -/
def Explains {codec : Codec Salt M D Enc} (dec : RoleDecoders codec) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D) (mt : Fin TM → D) (H : Pt → C) : Prop :=
  (S.atOracle H).Explains dec rootOf claimOf mt emptyTape

/-- A failed Merkle explanation has the same adaptive count used by the
full compiler, independently of the challenge-side soundness argument. -/
theorem merkle_bad_ratio_le [Fintype Pt] [Fintype C] [Nonempty C] [Fintype D]
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2 * n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
        ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      (adaptiveNumerator fc tA (L + N) : ℚ) / Fintype.card D := by
  classical
  let A := adaptiveNumerator fc tA (L + N)
  have hmk : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
          ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card
      ≤ Fintype.card C ^ Fintype.card Pt * (A * Fintype.card D ^ (TM - 1)) := by
    rw [card_filter_prod_snd]
    calc
      (∑ H : Pt → C, (univ.filter fun mt : Fin TM → D =>
        S.MerkleAccepts codec check rootOf claimOf mt H ∧
          ¬ S.Explains dec rootOf claimOf mt H).card)
          ≤ ∑ _H : Pt → C, A * Fintype.card D ^ (TM - 1) :=
        Finset.sum_le_sum fun H _ =>
          (S.atOracle H).merkle_card_le codec dec check rootOf claimOf
            hcheck hL ht hF emptyTape
      _ = Fintype.card C ^ Fintype.card Pt *
          (A * Fintype.card D ^ (TM - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul]
  have hmkq :
      ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
          ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card : ℚ) ≤
        (Fintype.card C : ℚ) ^ Fintype.card Pt *
          ((A : ℚ) * (Fintype.card D : ℚ) ^ (TM - 1)) := by
    exact_mod_cast hmk
  have hd : (0 : ℚ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hc : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hpowD : (Fintype.card D : ℚ) ^ TM =
      (Fintype.card D : ℚ) ^ (TM - 1) * (Fintype.card D : ℚ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [div_le_iff₀ (mul_pos (pow_pos hd TM) (pow_pos hc _))]
  calc
    _ ≤ (Fintype.card C : ℚ) ^ Fintype.card Pt *
        ((A : ℚ) * (Fintype.card D : ℚ) ^ (TM - 1)) := hmkq
    _ = ((A : ℚ) / Fintype.card D) *
        ((Fintype.card D : ℚ) ^ TM *
          (Fintype.card C : ℚ) ^ Fintype.card Pt) := by
      rw [hpowD]
      field_simp

/-- The two independent Merkle-opening explanations in the deployed
two-field verifier cost two copies of the same adaptive Merkle term. -/
theorem merkle_bad_ratio_le_two [Fintype Pt] [Fintype C] [Nonempty C]
    [Fintype D]
    {Salt₁ M₁ Salt₂ M₂ : Type}
    [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂] [Inhabited M₂]
    {n₁ n₂ : ℕ}
    (codec₁ : Codec Salt₁ M₁ D Enc) (dec₁ : RoleDecoders codec₁)
    (codec₂ : Codec Salt₂ M₂ D Enc) (dec₂ : RoleDecoders codec₂)
    (check : Out → Tree Enc D Unit fc) (rootOf₁ rootOf₂ : Key → D)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D)
    (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I
          (claimOf₁ out).a (claimOf₁ out).pf (2 * n₁)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I
          (claimOf₂ out).a (claimOf₂ out).pf (2 * n₂)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      (S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ ω.1 ω.2 ∧
        ¬ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2) ∨
      (S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ ω.1 ω.2 ∧
        ¬ S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2)).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      2 * ((adaptiveNumerator fc tA (L + N) : ℚ) / Fintype.card D) := by
  classical
  let E₁ : Finset ((Fin TM → D) × (Pt → C)) :=
    univ.filter fun ω => S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ ω.1 ω.2 ∧
      ¬ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2
  let E₂ : Finset ((Fin TM → D) × (Pt → C)) :=
    univ.filter fun ω => S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ ω.1 ω.2 ∧
      ¬ S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2
  have hsub : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        (S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ ω.1 ω.2 ∧
          ¬ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2) ∨
        (S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ ω.1 ω.2 ∧
          ¬ S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2)) ⊆ E₁ ∪ E₂ := by
    intro ω hw
    obtain ⟨_, hw⟩ := mem_filter.mp hw
    rcases hw with h₁ | h₂
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h₁⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h₂⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le E₁ E₂)
  have hDpos : (0 : ℚ) < Fintype.card D := by
    exact_mod_cast Fintype.card_pos
  have hCpos : (0 : ℚ) < Fintype.card C := by
    exact_mod_cast Fintype.card_pos
  have hden : (0 : ℚ) <
      (Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt :=
    mul_pos (pow_pos hDpos _) (pow_pos hCpos _)
  have h₁ := S.merkle_bad_ratio_le codec₁ dec₁ check rootOf₁ claimOf₁
    hcheck₁ hL ht hF hTM
  have h₂ := S.merkle_bad_ratio_le codec₂ dec₂ check rootOf₂ claimOf₂
    hcheck₂ hL ht hF hTM
  calc
    _ ≤ ((E₁.card : ℚ) + E₂.card) /
        ((Fintype.card D : ℚ) ^ TM *
          (Fintype.card C : ℚ) ^ Fintype.card Pt) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hden)
    _ = (E₁.card : ℚ) /
          ((Fintype.card D : ℚ) ^ TM *
            (Fintype.card C : ℚ) ^ Fintype.card Pt) +
        (E₂.card : ℚ) /
          ((Fintype.card D : ℚ) ^ TM *
            (Fintype.card C : ℚ) ^ Fintype.card Pt) := by ring
    _ ≤ 2 * ((adaptiveNumerator fc tA (L + N) : ℚ) /
          Fintype.card D) := by
      dsimp only [E₁, E₂] at h₁ h₂ ⊢
      linarith

/--
**A re-committing prefix-only Fiat–Shamir prover, counted.**  Over the Merkle tape and the total
oracle on prefix-only hash inputs, for any acceptance event `Acc` that includes the Merkle check and
any failure predicate on the commitment context:

```text
Pr[ Acc  ∧  Fails(context of the proof's key) ]
    ≤  (N · βmax + ∑ k, slotBeta k) / |C|  +  adaptiveNumerator fc tA (L + N) / |D|
```

provided `hchain`: an accepted proof whose opening the cut-trace extraction explains, in a failing
context, has a round-level bad event.  The first term is `Bcs.TotalOracle.CtxGrinding.card_mul_le`
at each Merkle tape, the second `Bcs.AdaptiveCommit.Setup.merkle_card_le` at each oracle.
-/
theorem ratio_le [Fintype Pt] [Fintype C] [DecidableEq C] [Nonempty C] [Fintype D]
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (pts : PrefixPoints Pt)
    (Bad : Key × List (Enc × D) → (x : Pt) → (Fin (pts.slot x) → C) → C → Prop) (beta : Pt → ℕ)
    (hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x)
    (betaMax : ℕ) (hmax : ∀ q : Pt, beta q ≤ betaMax) (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L), beta (S.hashInput out i.val) ≤ slotBeta i)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc : (Fin TM → D) → (Pt → C) → Prop) (Fails : Key × List (Enc × D) → Prop)
    (hacc : ∀ mt H, Acc mt H → S.MerkleAccepts codec check rootOf claimOf mt H)
    (hchain : ∀ mt H, Acc mt H → S.Explains dec rootOf claimOf mt H →
      Fails (S.context mt H) → (S.grinding mt pts Bad beta hbad).RoundBad H) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ Fails (S.context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card Pt)
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) / (Fintype.card C : ℚ)
        + (adaptiveNumerator fc tA (L + N) : ℚ) / (Fintype.card D : ℚ) := by
  set B := N * betaMax + ∑ i, slotBeta i with hB
  set A := adaptiveNumerator fc tA (L + N) with hA
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have hDpos : 0 < Fintype.card D := Fintype.card_pos
  -- split on whether the cut-trace extraction explains the opening
  have hsplit : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ Fails (S.context ω.1 ω.2)).card
      ≤ (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          Acc ω.1 ω.2 ∧ S.Explains dec rootOf claimOf ω.1 ω.2 ∧
            Fails (S.context ω.1 ω.2)).card
        + (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
            ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_cases hex : S.Explains dec rootOf claimOf ω.1 ω.2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω.1, hex, hω.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc _ _ hω.1, hex⟩)
  -- the Fiat–Shamir side, at each Merkle tape
  have hfs : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ S.Explains dec rootOf claimOf ω.1 ω.2 ∧
          Fails (S.context ω.1 ω.2)).card * Fintype.card C
      ≤ Fintype.card D ^ TM * (B * Fintype.card C ^ Fintype.card Pt) := by
    rw [card_filter_prod_fst, Finset.sum_mul]
    calc ∑ mt : Fin TM → D, (univ.filter fun H : Pt → C =>
            Acc mt H ∧ S.Explains dec rootOf claimOf mt H ∧
              Fails (S.context mt H)).card * Fintype.card C
        ≤ ∑ _mt : Fin TM → D, B * Fintype.card C ^ Fintype.card Pt := by
          refine Finset.sum_le_sum fun mt _ => ?_
          exact (S.grinding mt pts Bad beta hbad).card_mul_le betaMax hmax slotBeta
            (fun out i => hslot out i) _ fun H hH => hchain mt H hH.1 hH.2.1 hH.2.2
      _ = Fintype.card D ^ TM * (B * Fintype.card C ^ Fintype.card Pt) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            smul_eq_mul]
  -- the Merkle side, at each oracle
  have hmk : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
          ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card
      ≤ Fintype.card C ^ Fintype.card Pt * (A * Fintype.card D ^ (TM - 1)) := by
    rw [card_filter_prod_snd]
    calc ∑ H : Pt → C, (univ.filter fun mt : Fin TM → D =>
            S.MerkleAccepts codec check rootOf claimOf mt H ∧
              ¬ S.Explains dec rootOf claimOf mt H).card
        ≤ ∑ _H : Pt → C, A * Fintype.card D ^ (TM - 1) :=
          Finset.sum_le_sum fun H _ =>
            (S.atOracle H).merkle_card_le codec dec check rootOf claimOf hcheck hL ht hF emptyTape
      _ = Fintype.card C ^ Fintype.card Pt * (A * Fintype.card D ^ (TM - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul]
  -- assemble
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hd : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast hDpos
  have hpowD : (Fintype.card D : ℚ) ^ TM
      = (Fintype.card D : ℚ) ^ (TM - 1) * (Fintype.card D : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  have hsplitq := (Nat.cast_le (α := ℚ)).mpr hsplit
  have hfsq := (Nat.cast_le (α := ℚ)).mpr hfs
  have hmkq := (Nat.cast_le (α := ℚ)).mpr hmk
  push_cast at hsplitq hfsq hmkq
  rw [div_le_iff₀ (mul_pos (pow_pos hd TM) (pow_pos hc _))]
  have e1 : ((B : ℕ) : ℚ) / (Fintype.card C : ℚ)
      * ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card Pt)
      = (Fintype.card D : ℚ) ^ TM * ((B : ℚ) * (Fintype.card C : ℚ) ^ Fintype.card Pt)
        / (Fintype.card C : ℚ) := by ring
  have e2 : ((A : ℕ) : ℚ) / (Fintype.card D : ℚ)
      * ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card Pt)
      = (Fintype.card C : ℚ) ^ Fintype.card Pt * ((A : ℚ) * (Fintype.card D : ℚ) ^ (TM - 1)) := by
    rw [hpowD]; field_simp
  rw [add_mul, e1, e2]
  have hfs' : ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ S.Explains dec rootOf claimOf ω.1 ω.2 ∧
          Fails (S.context ω.1 ω.2)).card : ℚ)
      ≤ (Fintype.card D : ℚ) ^ TM * ((B : ℚ) * (Fintype.card C : ℚ) ^ Fintype.card Pt)
        / (Fintype.card C : ℚ) := by
    rw [le_div_iff₀ hc]; exact hfsq
  linarith

end Composed

section Two

variable [DecidableEq Key] [DecidableEq D] {fc : ℕ}

/--
**Two Merkle commitments under one key, counted.**  `ratio_le` with two root readers and two opening
claims checked against one Merkle oracle: a proof both of whose openings verify, and whose failure
predicate holds, costs

```text
(N · βmax + ∑ k, slotBeta k) / |C|  +  2 · adaptiveNumerator fc tA (L + N) / |D|.
```

`Bcs.AdaptiveCommit.Setup.ratio_le_two`'s right-hand side, over the total oracle on prefix-only hash
inputs.
-/
theorem ratio_le_two [Fintype Pt] [Fintype C] [DecidableEq C] [Nonempty C] [Fintype D]
    {Salt₁ M₁ Salt₂ M₂ : Type} [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂] [Inhabited M₂]
    {n₁ n₂ : ℕ}
    (codec₁ : Codec Salt₁ M₁ D Enc) (dec₁ : RoleDecoders codec₁)
    (codec₂ : Codec Salt₂ M₂ D Enc) (dec₂ : RoleDecoders codec₂)
    (check : Out → Tree Enc D Unit fc) (rootOf₁ rootOf₂ : Key → D)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I (claimOf₁ out).a (claimOf₁ out).pf (2 * n₁)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a (claimOf₂ out).pf (2 * n₂)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (pts : PrefixPoints Pt)
    (Bad : Key × List (Enc × D) → (x : Pt) → (Fin (pts.slot x) → C) → C → Prop) (beta : Pt → ℕ)
    (hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x)
    (betaMax : ℕ) (hmax : ∀ q : Pt, beta q ≤ betaMax) (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L), beta (S.hashInput out i.val) ≤ slotBeta i)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc : (Fin TM → D) → (Pt → C) → Prop) (Fails : (Fin TM → D) → (Pt → C) → Prop)
    (hacc₁ : ∀ mt H, Acc mt H → S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ mt H)
    (hacc₂ : ∀ mt H, Acc mt H → S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ mt H)
    (hchain : ∀ mt H, Acc mt H → S.Explains dec₁ rootOf₁ claimOf₁ mt H →
      S.Explains dec₂ rootOf₂ claimOf₂ mt H → Fails mt H →
      (S.grinding mt pts Bad beta hbad).RoundBad H) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) => Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card Pt)
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) / (Fintype.card C : ℚ)
        + 2 * ((adaptiveNumerator fc tA (L + N) : ℚ) / (Fintype.card D : ℚ)) := by
  set B := N * betaMax + ∑ i, slotBeta i with hB
  set A := adaptiveNumerator fc tA (L + N) with hA
  have hsplit : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card
      ≤ (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          Acc ω.1 ω.2 ∧ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2 ∧
            S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2 ∧ Fails ω.1 ω.2).card
        + (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ ω.1 ω.2 ∧
            ¬ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2).card
        + (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ ω.1 ω.2 ∧
            ¬ S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2).card := by
    refine le_trans (Finset.card_le_card ?_)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_cases hex₁ : S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2
    · by_cases hex₂ : S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω.1, hex₁, hex₂, hω.2⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc₂ _ _ hω.1, hex₂⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc₁ _ _ hω.1, hex₁⟩))
  -- the Fiat–Shamir side, at each Merkle tape
  have hfs : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2 ∧
          S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2 ∧ Fails ω.1 ω.2).card * Fintype.card C
      ≤ Fintype.card D ^ TM * (B * Fintype.card C ^ Fintype.card Pt) := by
    rw [card_filter_prod_fst, Finset.sum_mul]
    calc ∑ mt : Fin TM → D, (univ.filter fun H : Pt → C =>
            Acc mt H ∧ S.Explains dec₁ rootOf₁ claimOf₁ mt H ∧
              S.Explains dec₂ rootOf₂ claimOf₂ mt H ∧ Fails mt H).card * Fintype.card C
        ≤ ∑ _mt : Fin TM → D, B * Fintype.card C ^ Fintype.card Pt := by
          refine Finset.sum_le_sum fun mt _ => ?_
          exact (S.grinding mt pts Bad beta hbad).card_mul_le betaMax hmax slotBeta
            (fun out i => hslot out i) _
            fun H hH => hchain mt H hH.1 hH.2.1 hH.2.2.1 hH.2.2.2
      _ = Fintype.card D ^ TM * (B * Fintype.card C ^ Fintype.card Pt) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            smul_eq_mul]
  -- the Merkle side, at each oracle, once per root
  have hmk : ∀ {Salt M : Type} [Inhabited Salt] [Inhabited M] {n : ℕ}
      (codec : Codec Salt M D Enc) (dec : RoleDecoders codec) (rootOf : Key → D)
      (claimOf : Out → OpeningClaim n Salt M D)
      (_hcheck : ∀ (H : Enc → D) (out : Out),
        ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
            fun _ => default).run H).2, qa ∈ ((check out).run H).2),
      (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
            ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card
        ≤ Fintype.card C ^ Fintype.card Pt * (A * Fintype.card D ^ (TM - 1)) := by
    intro Salt M _ _ n codec dec rootOf claimOf hcheck
    rw [card_filter_prod_snd]
    calc ∑ H : Pt → C, (univ.filter fun mt : Fin TM → D =>
            S.MerkleAccepts codec check rootOf claimOf mt H ∧
              ¬ S.Explains dec rootOf claimOf mt H).card
        ≤ ∑ _H : Pt → C, A * Fintype.card D ^ (TM - 1) :=
          Finset.sum_le_sum fun H _ =>
            (S.atOracle H).merkle_card_le codec dec check rootOf claimOf hcheck hL ht hF emptyTape
      _ = Fintype.card C ^ Fintype.card Pt * (A * Fintype.card D ^ (TM - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul]
  have hm₁ := hmk codec₁ dec₁ rootOf₁ claimOf₁ hcheck₁
  have hm₂ := hmk codec₂ dec₂ rootOf₂ claimOf₂ hcheck₂
  -- assemble
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast Fintype.card_pos
  have hpowD : (Fintype.card D : ℚ) ^ TM
      = (Fintype.card D : ℚ) ^ (TM - 1) * (Fintype.card D : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  have hsplitq := (Nat.cast_le (α := ℚ)).mpr hsplit
  have hfsq := (Nat.cast_le (α := ℚ)).mpr hfs
  have hm₁q := (Nat.cast_le (α := ℚ)).mpr hm₁
  have hm₂q := (Nat.cast_le (α := ℚ)).mpr hm₂
  push_cast at hsplitq hfsq hm₁q hm₂q
  rw [div_le_iff₀ (mul_pos (pow_pos hd TM) (pow_pos hc _))]
  have e1 : ((B : ℕ) : ℚ) / (Fintype.card C : ℚ)
      * ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card Pt)
      = (Fintype.card D : ℚ) ^ TM * ((B : ℚ) * (Fintype.card C : ℚ) ^ Fintype.card Pt)
        / (Fintype.card C : ℚ) := by ring
  have e2 : 2 * (((A : ℕ) : ℚ) / (Fintype.card D : ℚ))
      * ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card Pt)
      = 2 * ((Fintype.card C : ℚ) ^ Fintype.card Pt
          * ((A : ℚ) * (Fintype.card D : ℚ) ^ (TM - 1))) := by
    rw [hpowD]; field_simp
  rw [add_mul, e1, e2]
  have hfs' : ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        Acc ω.1 ω.2 ∧ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2 ∧
          S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ)
      ≤ (Fintype.card D : ℚ) ^ TM * ((B : ℚ) * (Fintype.card C : ℚ) ^ Fintype.card Pt)
        / (Fintype.card C : ℚ) := by
    rw [le_div_iff₀ hc]; exact hfsq
  linarith

end Two

end Setup

end Bcs.TotalOracleCommit
