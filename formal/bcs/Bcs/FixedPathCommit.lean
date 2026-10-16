import Bcs.FixedPath
import Bcs.TotalOracleCommit

/-!
# The zero-query commitment setup has a uniform verifier challenge tape

The Merkle tape remains fixed in this lemma.  Merkle extraction can therefore
be counted separately, while every event of the proof and verifier challenges
has the exact interactive challenge-tape distribution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracleCommit

open Finset Bcs.TotalOracle Merkle.MH
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

/-- Answering transcript-oracle calls changes no zero-query program. -/
theorem answerRight_zero_eq {QL DL QR DR A : Type} {leftFuel : ℕ}
    (body : TwoOracleTree QL DL QR DR A leftFuel 0) (H : QR → DR) :
    answerRight H body = body := by
  have haux : ∀ {l r : ℕ} (tree : TwoOracleTree QL DL QR DR A l r),
      r = 0 → answerRight H tree = tree := by
    intro l r tree hr
    induction tree with
    | done _ => rfl
    | queryLeft q next ih =>
        simp only [answerRight]
        congr
        funext y
        exact ih y hr
    | queryRight q next ih => omega
  exact haux body rfl

variable {Enc D Pt C Out Key : Type} {tA L TM : ℕ}

/-- At zero transcript-oracle queries, even the complete Merkle-side setup
is independent of the transcript oracle. -/
theorem Setup.atOracle_zero_eq
    (S : Setup Enc D Pt C Out Key tA 0 L) (H H' : Pt → C) :
    S.atOracle H = S.atOracle H' := by
  unfold Setup.atOracle
  rw [answerRight_zero_eq S.body H, answerRight_zero_eq S.body H']

variable [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]

theorem Setup.zeroQuery_proof_eq
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (mt : Fin TM → D) (H H' : Pt → C) :
    S.proof mt H = S.proof mt H' := by
  unfold Setup.proof
  rw [S.atOracle_zero_eq H H']

theorem Setup.zeroQuery_context_eq [DecidableEq Key]
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (mt : Fin TM → D) (H H' : Pt → C) :
    S.context mt H = S.context mt H' := by
  unfold Setup.context
  rw [S.atOracle_zero_eq H H']

theorem Setup.zeroQuery_merkleOracle_eq {fc : ℕ}
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (check : Out → Tree Enc D Unit fc)
    (mt : Fin TM → D) (H H' : Pt → C) :
    S.merkleOracle check mt H = S.merkleOracle check mt H' := by
  unfold Setup.merkleOracle
  rw [S.atOracle_zero_eq H H']

/-- A zero-query prover's Merkle explanation depends on its fixed Merkle
path and output, not on any answer of the transcript oracle. -/
theorem Setup.zeroQuery_explains_iff [DecidableEq D] [DecidableEq Key]
    {Salt M : Type} [Inhabited Salt] [Inhabited M] {n : ℕ}
    {codec : Merkle.MH.Codec Salt M D Enc}
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (dec : Merkle.MH.RoleDecoders codec)
    (rootOf : Key → D)
    (claimOf : Out → Merkle.MH.OpeningClaim n Salt M D)
    (mt : Fin TM → D) (H H' : Pt → C) :
    S.Explains dec rootOf claimOf mt H ↔
      S.Explains dec rootOf claimOf mt H' := by
  unfold Setup.Explains
  rw [S.atOracle_zero_eq H H']

variable [Fintype Pt] [Fintype C] [Nonempty C]

/-- Extend any chosen verifier challenge tape to a total transcript oracle,
keeping the off-path answers of `dummy`. -/
noncomputable def Setup.oracleWithTape
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (mt : Fin TM → D) (dummy : Pt → C)
    (hinj : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (tape : Fin L → C) : Pt → C :=
  let point : Fin L → Pt := fun i => S.hashInput (S.proof mt dummy) i.val
  (Bcs.TotalOracle.splitFixedPath point (hinj (S.proof mt dummy))).symm
    (tape, fun p => dummy p.1)

omit [Fintype Pt] [Fintype C] [Nonempty C] in
theorem Setup.oracleWithTape_challenges_eq
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (mt : Fin TM → D) (dummy : Pt → C)
    (hinj : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (tape : Fin L → C) :
    S.challenges mt (S.oracleWithTape mt dummy hinj tape) = tape := by
  let point : Fin L → Pt := fun i => S.hashInput (S.proof mt dummy) i.val
  let off : Bcs.TotalOracle.AwayFromPath point → C := fun p => dummy p.1
  let e := Bcs.TotalOracle.splitFixedPath (C := C) point
    (hinj (S.proof mt dummy))
  have hpoint (i : Fin L) :
      (S.oracleWithTape mt dummy hinj tape) (point i) = tape i := by
    have h := congrArg (fun p : (Fin L → C) ×
        (Bcs.TotalOracle.AwayFromPath point → C) => p.1 i)
      (e.apply_symm_apply (tape, off))
    exact h
  funext i
  unfold Setup.challenges
  rw [S.zeroQuery_proof_eq mt (S.oracleWithTape mt dummy hinj tape) dummy]
  exact hpoint i

omit [Fintype Pt] [Fintype C] [Nonempty C] in
/-- Every virtual verifier tape can be realized by one total oracle while
preserving the fixed Merkle path, prover output, and commitment context. -/
theorem Setup.zeroQuery_event_oracleWithTape_iff
    [DecidableEq Key] {fc : ℕ}
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (check : Out → Tree Enc D Unit fc)
    (mt : Fin TM → D) (dummy : Pt → C)
    (hinj : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (tape : Fin L → C)
    (E : (Key × List (Enc × D)) → (Enc → D) → Out →
      (Fin L → C) → Prop) :
    E (S.context mt (S.oracleWithTape mt dummy hinj tape))
      (S.merkleOracle check mt (S.oracleWithTape mt dummy hinj tape))
      (S.proof mt (S.oracleWithTape mt dummy hinj tape))
      (S.challenges mt (S.oracleWithTape mt dummy hinj tape)) ↔
    E (S.context mt dummy) (S.merkleOracle check mt dummy)
      (S.proof mt dummy) tape := by
  rw [S.zeroQuery_context_eq mt (S.oracleWithTape mt dummy hinj tape) dummy,
    S.zeroQuery_merkleOracle_eq check mt (S.oracleWithTape mt dummy hinj tape) dummy,
    S.zeroQuery_proof_eq mt (S.oracleWithTape mt dummy hinj tape) dummy,
    S.oracleWithTape_challenges_eq mt dummy hinj tape]

/-- At zero transcript-oracle queries, a fixed Merkle tape fixes the proof.
The deployed verifier's distinct hash inputs then read an independent uniform
challenge tape from the total random oracle. -/
theorem Setup.zeroQuery_challenges_ratio_eq
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (mt : Fin TM → D) (dummy : Pt → C)
    (hinj : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (E : Out → (Fin L → C) → Prop) :
    ((univ.filter fun H : Pt → C =>
        E (S.proof mt H) (S.challenges mt H)).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Pt =
      ((univ.filter fun tape : Fin L → C =>
        E (S.proof mt dummy) tape).card : ℚ) /
        (Fintype.card C : ℚ) ^ L := by
  have h := Bcs.TotalOracle.zeroQuery_fixedPath_ratio_eq
    mt (default : D) S.body [] dummy
      (fun out (i : Fin L) => S.hashInput out i.val) hinj E
  unfold Setup.challenges
  simpa only [S.proof_eq, Setup.search] using h

/-- The same exact coupling for events that inspect the commitment context
and the verifier's Merkle oracle. Both are fixed by the Merkle tape when the
prover makes no transcript-oracle calls. -/
theorem Setup.zeroQuery_verifierEvent_ratio_eq [DecidableEq Key] {fc : ℕ}
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (check : Out → Tree Enc D Unit fc)
    (mt : Fin TM → D) (dummy : Pt → C)
    (hinj : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (E : (Key × List (Enc × D)) → (Enc → D) → Out →
      (Fin L → C) → Prop) :
    ((univ.filter fun H : Pt → C =>
        E (S.context mt H) (S.merkleOracle check mt H)
          (S.proof mt H) (S.challenges mt H)).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Pt =
      ((univ.filter fun tape : Fin L → C =>
        E (S.context mt dummy) (S.merkleOracle check mt dummy)
          (S.proof mt dummy) tape).card : ℚ) /
        (Fintype.card C : ℚ) ^ L := by
  have h := S.zeroQuery_challenges_ratio_eq mt dummy hinj
    (fun out tape =>
      E (S.context mt dummy) (S.merkleOracle check mt dummy) out tape)
  have hfilter :
      (univ.filter fun H : Pt → C =>
        E (S.context mt H) (S.merkleOracle check mt H)
          (S.proof mt H) (S.challenges mt H)).card =
      (univ.filter fun H : Pt → C =>
        E (S.context mt dummy) (S.merkleOracle check mt dummy)
          (S.proof mt H) (S.challenges mt H)).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro H _
    rw [S.zeroQuery_context_eq mt H dummy,
      S.zeroQuery_merkleOracle_eq check mt H dummy]
  rw [hfilter]
  exact h

/-- A uniform interactive bound for the complete verifier event, conditional
on each Merkle tape, transfers without loss to the zero-query Fiat--Shamir
experiment.  This is the averaging step after fixed-path coupling; any Merkle
bad event can be included in `E` or bounded separately. -/
theorem Setup.zeroQuery_verifierEvent_ratio_le
    [Fintype D] [DecidableEq Key] {fc : ℕ}
    (S : Setup Enc D Pt C Out Key tA 0 L)
    (check : Out → Tree Enc D Unit fc)
    (dummy : Pt → C)
    (hinj : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (E : (Key × List (Enc × D)) → (Enc → D) → Out →
      (Fin L → C) → Prop)
    (epsilon : ℚ)
    (hinteractive : ∀ mt : Fin TM → D,
      ((univ.filter fun tape : Fin L → C =>
        E (S.context mt dummy) (S.merkleOracle check mt dummy)
          (S.proof mt dummy) tape).card : ℚ) /
        (Fintype.card C : ℚ) ^ L ≤ epsilon) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        E (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
          (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
        Fintype.card ((Fin TM → D) × (Pt → C)) ≤ epsilon := by
  classical
  apply Bcs.product_ratio_le_of_fst_fiber
    (fun mt H =>
      E (S.context mt H) (S.merkleOracle check mt H)
        (S.proof mt H) (S.challenges mt H)) epsilon
  intro mt
  have heq := S.zeroQuery_verifierEvent_ratio_eq check mt dummy hinj E
  simpa only [Fintype.card_fun, Nat.cast_pow] using
    (heq.le.trans (hinteractive mt))

/-- At zero transcript-oracle queries, a fixed-path verifier bound and the
two ordinary Merkle explanation failures compose additively.  The challenge
bound is charged only on paths for which both Merkle openings are explained. -/
theorem Setup.zeroQuery_ratio_le_good_plus_merkle_two
    [Fintype D] [DecidableEq D] [DecidableEq Key]
    {Salt₁ M₁ Salt₂ M₂ : Type}
    [Inhabited Salt₁] [Inhabited M₁]
    [Inhabited Salt₂] [Inhabited M₂]
    {n₁ n₂ fc : ℕ}
    (S : Setup Enc D Pt C Out Key tA 0 L)
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
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (dummy : Pt → C)
    (hinj : ∀ out, Function.Injective
      (fun i : Fin L => S.hashInput out i.val))
    (E : (Key × List (Enc × D)) → (Enc → D) → Out →
      (Fin L → C) → Prop)
    (epsilon : ℚ)
    (haccept₁ : ∀ (mt : Fin TM → D) (H : Pt → C),
      E (S.context mt H) (S.merkleOracle check mt H)
        (S.proof mt H) (S.challenges mt H) →
      S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ mt H)
    (haccept₂ : ∀ (mt : Fin TM → D) (H : Pt → C),
      E (S.context mt H) (S.merkleOracle check mt H)
        (S.proof mt H) (S.challenges mt H) →
      S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ mt H)
    (hgood : ∀ mt : Fin TM → D,
      ((univ.filter fun tape : Fin L → C =>
        E (S.context mt dummy) (S.merkleOracle check mt dummy)
          (S.proof mt dummy) tape ∧
        S.Explains dec₁ rootOf₁ claimOf₁ mt dummy ∧
        S.Explains dec₂ rootOf₂ claimOf₂ mt dummy).card : ℚ) /
          (Fintype.card C : ℚ) ^ L ≤ epsilon) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      E (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
        (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2)).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      epsilon + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + 0) : ℚ) /
        Fintype.card D) := by
  let event (mt : Fin TM → D) (H : Pt → C) : Prop :=
    E (S.context mt H) (S.merkleOracle check mt H)
      (S.proof mt H) (S.challenges mt H)
  let explained₁ (mt : Fin TM → D) (H : Pt → C) : Prop :=
    S.Explains dec₁ rootOf₁ claimOf₁ mt H
  let explained₂ (mt : Fin TM → D) (H : Pt → C) : Prop :=
    S.Explains dec₂ rootOf₂ claimOf₂ mt H
  let bad₁ (mt : Fin TM → D) (H : Pt → C) : Prop :=
    S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ mt H ∧ ¬ explained₁ mt H
  let bad₂ (mt : Fin TM → D) (H : Pt → C) : Prop :=
    S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ mt H ∧ ¬ explained₂ mt H
  have hgoodFib : ∀ mt : Fin TM → D,
      ((univ.filter fun H : Pt → C =>
        event mt H ∧ explained₁ mt H ∧ explained₂ mt H).card : ℚ) /
          Fintype.card (Pt → C) ≤ epsilon := by
    intro mt
    let Emt : (Key × List (Enc × D)) → (Enc → D) → Out →
        (Fin L → C) → Prop := fun κ mo out tape =>
      E κ mo out tape ∧ explained₁ mt dummy ∧ explained₂ mt dummy
    have heq := S.zeroQuery_verifierEvent_ratio_eq check mt dummy hinj Emt
    have hfilter : (univ.filter fun H : Pt → C =>
        event mt H ∧ explained₁ mt H ∧ explained₂ mt H) =
      (univ.filter fun H : Pt → C =>
        Emt (S.context mt H) (S.merkleOracle check mt H)
          (S.proof mt H) (S.challenges mt H)) := by
      ext H
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, event, Emt,
        explained₁, explained₂]
      have he₁ := S.zeroQuery_explains_iff dec₁ rootOf₁ claimOf₁ mt H dummy
      have he₂ := S.zeroQuery_explains_iff dec₂ rootOf₂ claimOf₂ mt H dummy
      constructor
      · rintro ⟨he, hx, hy⟩
        exact ⟨he, he₁.mp hx, he₂.mp hy⟩
      · rintro ⟨he, hx, hy⟩
        exact ⟨he, he₁.mpr hx, he₂.mpr hy⟩
    rw [hfilter]
    have hbound :
        ((univ.filter fun H : Pt → C =>
          Emt (S.context mt H) (S.merkleOracle check mt H)
            (S.proof mt H) (S.challenges mt H)).card : ℚ) /
          (Fintype.card C : ℚ) ^ Fintype.card Pt ≤ epsilon := by
      have h := heq.le.trans (show _ ≤ epsilon by
        convert hgood mt using 1
        apply congrArg (fun s : Finset (Fin L → C) =>
          (s.card : ℚ) / (Fintype.card C : ℚ) ^ L)
        ext tape
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Emt, explained₁, explained₂])
      convert h using 1
      all_goals try rfl
      all_goals
        apply congrArg (fun s : Finset (Pt → C) => (s.card : ℚ) /
          (Fintype.card C : ℚ) ^ Fintype.card Pt)
        ext H
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [Fintype.card_fun, Nat.cast_pow] using hbound
  have hgoodAll := Bcs.product_ratio_le_of_fst_fiber
    (fun mt H => event mt H ∧ explained₁ mt H ∧ explained₂ mt H)
    epsilon hgoodFib
  have hgoodAll' :
      ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        event ω.1 ω.2 ∧ explained₁ ω.1 ω.2 ∧ explained₂ ω.1 ω.2).card : ℚ) /
        ((Fintype.card D : ℚ) ^ TM *
          (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤ epsilon := by
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_pow] using hgoodAll
  have hbad := S.merkle_bad_ratio_le_two codec₁ dec₁ codec₂ dec₂
    check rootOf₁ rootOf₂ claimOf₁ claimOf₂
    hcheck₁ hcheck₂ hL ht hF hTM
  have hsub : (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      event ω.1 ω.2) ⊆
      (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        event ω.1 ω.2 ∧ explained₁ ω.1 ω.2 ∧ explained₂ ω.1 ω.2) ∪
      (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        bad₁ ω.1 ω.2 ∨ bad₂ ω.1 ω.2) := by
    intro ω hw
    have he := (Finset.mem_filter.mp hw).2
    by_cases h₁ : explained₁ ω.1 ω.2
    · by_cases h₂ : explained₂ ω.1 ω.2
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, h₁, h₂⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr
            ⟨haccept₂ ω.1 ω.2 he, h₂⟩⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl
          ⟨haccept₁ ω.1 ω.2 he, h₁⟩⟩)
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _)
  have hDpos : (0 : ℚ) < Fintype.card D := by
    exact_mod_cast Fintype.card_pos
  have hCpos : (0 : ℚ) < Fintype.card C := by
    exact_mod_cast Fintype.card_pos
  have hden : (0 : ℚ) <
      (Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^ Fintype.card Pt :=
    mul_pos (pow_pos hDpos _) (pow_pos hCpos _)
  calc
    _ ≤ (((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          event ω.1 ω.2 ∧ explained₁ ω.1 ω.2 ∧ explained₂ ω.1 ω.2).card : ℚ) +
        ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          bad₁ ω.1 ω.2 ∨ bad₂ ω.1 ω.2).card : ℚ)) /
        ((Fintype.card D : ℚ) ^ TM *
          (Fintype.card C : ℚ) ^ Fintype.card Pt) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hden)
    _ = ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          event ω.1 ω.2 ∧ explained₁ ω.1 ω.2 ∧ explained₂ ω.1 ω.2).card : ℚ) /
          ((Fintype.card D : ℚ) ^ TM *
            (Fintype.card C : ℚ) ^ Fintype.card Pt) +
        ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
          bad₁ ω.1 ω.2 ∨ bad₂ ω.1 ω.2).card : ℚ) /
          ((Fintype.card D : ℚ) ^ TM *
            (Fintype.card C : ℚ) ^ Fintype.card Pt) := by ring
    _ ≤ epsilon + 2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + 0) : ℚ) /
          Fintype.card D) := by
      dsimp only [bad₁, bad₂, explained₁, explained₂] at hbad ⊢
      linarith

end Bcs.TotalOracleCommit
