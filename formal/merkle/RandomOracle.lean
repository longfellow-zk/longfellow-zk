import Mathlib

/-!
# Bounded adaptive random-oracle executions

An oracle adversary is an answer-branching query tree. Unlike a function of a
complete oracle, this syntax exposes the exact adaptive query bound. The
finite counting lemmas below are reusable by binding and hiding games.
-/

open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace RandomOracle

universe uQ uD uA

/-- An adaptive oracle program making at most `fuel` queries. `done` may stop
early; `query` chooses its continuation after seeing the answer. -/
inductive Tree (Q : Type uQ) (D : Type uD) (A : Type uA) : ℕ → Type _ where
  | done {fuel : ℕ} (a : A) : Tree Q D A fuel
  | query {fuel : ℕ} (q : Q) (next : D → Tree Q D A fuel) :
      Tree Q D A (fuel + 1)

/-- Execute an adaptive tree against a total oracle, recording queries and
answers in execution order. -/
def Tree.run {Q : Type uQ} {D : Type uD} {A : Type uA} {fuel : ℕ} :
    Tree Q D A fuel → (Q → D) → A × List (Q × D)
  | .done a, _ => (a, [])
  | .query q next, H =>
      let y := H q
      let out := (next y).run H
      (out.1, (q, y) :: out.2)

@[simp] theorem Tree.run_done {Q : Type uQ} {D : Type uD} {A : Type uA}
    {fuel : ℕ} (a : A) (H : Q → D) :
    (Tree.done (fuel := fuel) a : Tree Q D A fuel).run H = (a, []) := rfl

@[simp] theorem Tree.run_query {Q : Type uQ} {D : Type uD} {A : Type uA}
    {fuel : ℕ} (q : Q) (next : D → Tree Q D A fuel) (H : Q → D) :
    (Tree.query q next).run H =
      let out := (next (H q)).run H
      (out.1, (q, H q) :: out.2) := rfl

/-- Execution never exceeds the syntactic query budget. -/
theorem Tree.trace_length_le {Q : Type uQ} {D : Type uD} {A : Type uA}
    {fuel : ℕ} (c : Tree Q D A fuel) (H : Q → D) :
    (c.run H).2.length ≤ fuel := by
  induction c with
  | done a => simp
  | @query fuel q next ih =>
      simp only [Tree.run_query, List.length_cons]
      have htail := ih (H q)
      omega

/-- Every answer in an execution trace is the answer of the oracle used for
that execution. -/
theorem Tree.trace_sound {Q : Type uQ} {D : Type uD} {A : Type uA}
    {fuel : ℕ} (c : Tree Q D A fuel) (H : Q → D) :
    ∀ qa ∈ (c.run H).2, qa.2 = H qa.1 := by
  induction c with
  | done a => simp
  | @query fuel q next ih =>
      intro qa hqa
      simp only [Tree.run_query, List.mem_cons] at hqa
      rcases hqa with rfl | htail
      · rfl
      · exact ih (H q) qa htail

/-- Oracle extensionality only on the actually executed trace suffices to
replay the same adaptive execution. -/
theorem Tree.run_congr_on_trace {Q : Type uQ} {D : Type uD} {A : Type uA}
    {fuel : ℕ} (c : Tree Q D A fuel) (H H' : Q → D)
    (hagrees : ∀ qa ∈ (c.run H).2, H' qa.1 = qa.2) :
    c.run H' = c.run H := by
  induction c with
  | done a => rfl
  | @query fuel q next ih =>
      have hq : H' q = H q := by
        have := hagrees (q, H q) (by simp [Tree.run_query])
        exact this
      simp only [Tree.run_query, hq]
      have htail : ∀ qa ∈ ((next (H q)).run H).2, H' qa.1 = qa.2 := by
        intro qa hqa
        apply hagrees qa
        simp only [Tree.run_query, List.mem_cons]
        exact Or.inr hqa
      rw [ih (H q) htail]

/-- A trace collision uses two distinct queried inputs with the same recorded
answer. -/
def TraceCollision {Q : Type uQ} {D : Type uD} (tr : List (Q × D)) : Prop :=
  ∃ qa₀ ∈ tr, ∃ qa₁ ∈ tr, qa₀.1 ≠ qa₁.1 ∧ qa₀.2 = qa₁.2

/-- A collision in an adaptive execution trace is a non-injectivity witness
for the total oracle. -/
theorem Tree.not_injective_of_traceCollision
    {Q : Type uQ} {D : Type uD} {A : Type uA}
    {fuel : ℕ} (c : Tree Q D A fuel) (H : Q → D)
    (hcol : TraceCollision (c.run H).2) : ¬Function.Injective H := by
  rcases hcol with ⟨qa₀, h₀, qa₁, h₁, hne, hans⟩
  intro hinj
  apply hne
  apply hinj
  rw [← Tree.trace_sound c H qa₀ h₀, ← Tree.trace_sound c H qa₁ h₁]
  exact hans

/-- A regression example whose second query genuinely depends on the first
answer. -/
def adaptiveSecondQuery : Tree (Fin 3) Bool Bool 2 :=
  .query 0 (fun b => .query (if b then 1 else 2) (fun b' => .done b'))

example (H : Fin 3 → Bool) (h : H 0 = true) :
    ((adaptiveSecondQuery.run H).2.map Prod.fst) = [0, 1] := by
  simp [adaptiveSecondQuery, h]

example (H : Fin 3 → Bool) (h : H 0 = false) :
    ((adaptiveSecondQuery.run H).2.map Prod.fst) = [0, 2] := by
  simp [adaptiveSecondQuery, h]

/-! ## Finite oracle counting -/

variable {Q : Type uQ} {D : Type uD}

/-- Restrict an oracle away from one coordinate. -/
def eraseCoord (q₁ : Q) (H : Q → D) : {q : Q // q ≠ q₁} → D :=
  fun q => H q.val

/-- If answers at two distinct coordinates are constrained equal, erasing
one of those coordinates remains injective: the erased answer is determined
by the retained one. -/
theorem eraseCoord_injective_on_equal [DecidableEq Q]
    (q₀ q₁ : Q) (hne : q₀ ≠ q₁) :
    Function.Injective (fun H : {H : Q → D // H q₀ = H q₁} =>
      eraseCoord q₁ H.val) := by
  intro H G heq
  apply Subtype.ext
  funext q
  by_cases hq : q = q₁
  · subst q
    rw [← H.property, ← G.property]
    exact congrFun heq ⟨q₀, hne⟩
  · exact congrFun heq ⟨q, hq⟩

/-- A fixed pair of distinct oracle inputs agrees on at most a `1/|D|`
fraction of all finite oracles, stated as a cardinality inequality. -/
theorem fixed_pair_card_le [Fintype Q] [DecidableEq Q]
    [Fintype D] [DecidableEq D]
    (q₀ q₁ : Q) (hne : q₀ ≠ q₁) :
    (Finset.filter (fun H : Q → D => H q₀ = H q₁) Finset.univ).card ≤
      (Fintype.card D) ^ (Fintype.card Q - 1) := by
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {H : Q → D // H q₀ = H q₁}
        ≤ Fintype.card ({q : Q // q ≠ q₁} → D) :=
      Fintype.card_le_of_injective _ (eraseCoord_injective_on_equal q₀ q₁ hne)
    _ = (Fintype.card D) ^ Fintype.card {q : Q // q ≠ q₁} := by
      rw [Fintype.card_fun]
    _ = (Fintype.card D) ^ (Fintype.card Q - 1) := by
      congr 1
      simp

/-- Coarse birthday bound obtained by a union bound over ordered distinct
pairs. The sharper unordered-pair factor `1/2` can be layered on later; this
form is sufficient as a conservative adaptive answer-tape bound. -/
theorem noninjective_card_le_square [Fintype Q] [DecidableEq Q]
    [Fintype D] [DecidableEq D] :
    (Finset.filter (fun H : Q → D => ¬Function.Injective H)
      Finset.univ).card ≤
      Fintype.card Q * Fintype.card Q *
        (Fintype.card D) ^ (Fintype.card Q - 1) := by
  classical
  let pairs : Finset (Q × Q) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 ≠ p.2)
  let Bad : (Q × Q) → (Q → D) → Prop := fun p H => H p.1 = H p.2
  have hevent :
      Finset.filter (fun H : Q → D => ¬Function.Injective H) Finset.univ =
      Finset.filter (fun H : Q → D => ∃ p ∈ pairs, Bad p H) Finset.univ := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [Function.not_injective_iff] at h
      rcases h with ⟨q₀, q₁, heq, hne⟩
      exact ⟨(q₀, q₁), by simp [pairs, hne], heq⟩
    · rintro ⟨⟨q₀, q₁⟩, hp, heq⟩ hinj
      have hne : q₀ ≠ q₁ := by simpa [pairs] using hp
      exact hne (hinj heq)
  rw [hevent]
  calc
    (Finset.filter (fun H : Q → D => ∃ p ∈ pairs, Bad p H)
        Finset.univ).card
        ≤ ∑ p ∈ pairs,
            (Finset.filter (Bad p) Finset.univ).card :=
      by
        let pieces : Q × Q → Finset (Q → D) :=
          fun p => Finset.filter (Bad p) Finset.univ
        have hp : Finset.filter
              (fun H : Q → D => ∃ p ∈ pairs, Bad p H) Finset.univ =
            pairs.biUnion pieces := by
          ext H
          simp [pieces]
        rw [hp]
        exact Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairs,
          (Fintype.card D) ^ (Fintype.card Q - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      change (Finset.filter (fun H : Q → D => H p.1 = H p.2)
        Finset.univ).card ≤ (Fintype.card D) ^ (Fintype.card Q - 1)
      exact fixed_pair_card_le (D := D) p.1 p.2
        (by simpa [pairs] using hp)
    _ = pairs.card * (Fintype.card D) ^ (Fintype.card Q - 1) := by simp
    _ ≤ (Fintype.card Q * Fintype.card Q) *
          (Fintype.card D) ^ (Fintype.card Q - 1) := by
      apply Nat.mul_le_mul_right
      calc
        pairs.card ≤ (Finset.univ ×ˢ (Finset.univ : Finset Q)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = Fintype.card Q * Fintype.card Q := by simp
    _ = Fintype.card Q * Fintype.card Q *
          (Fintype.card D) ^ (Fintype.card Q - 1) := rfl

/-- Conservative `t`-answer-tape birthday bound used by lazy-sampling
executions. Adaptive query choices do not affect this count because the tape
coordinates are sampled independently before execution. -/
theorem answerTape_birthday_card_le_square [Fintype D] [DecidableEq D]
    (t : ℕ) :
    (Finset.filter (fun answers : Fin t → D =>
      ¬Function.Injective answers) Finset.univ).card ≤
      t * t * (Fintype.card D) ^ (t - 1) := by
  simpa using (noninjective_card_le_square (Q := Fin t) (D := D))

/-- Exact fresh-pair kernel on an answer tape. -/
theorem answerTape_fixed_pair_card_le [Fintype D] [DecidableEq D]
    (t : ℕ) (i j : Fin t) (hne : i ≠ j) :
    (Finset.filter (fun answers : Fin t → D => answers i = answers j)
      Finset.univ).card ≤
      (Fintype.card D) ^ (t - 1) := by
  simpa using fixed_pair_card_le (D := D) i j hne

/-- The event that one of a finite collection of distinct answer-tape
coordinate pairs receives equal answers.  The pairs themselves are fixed by
the experiment layout; which pair witnesses failure may depend on all earlier
adaptive answers. -/
def PairCollision (T : ℕ) (pairs : Finset (Fin T × Fin T))
    (answers : Fin T → D) : Prop :=
  ∃ p ∈ pairs, answers p.1 = answers p.2

instance pairCollisionDecidable [DecidableEq D]
    (T : ℕ) (pairs : Finset (Fin T × Fin T)) :
    DecidablePred (PairCollision (D := D) T pairs) := by
  intro answers
  unfold PairCollision
  infer_instance

/-- Union bound for an arbitrary fixed family of answer-tape pairs.  This is
the useful fresh-coordinate lemma: adaptivity affects the queries stored in
the slots, but not the fact that each pair of distinct fresh slots agrees on
only a `1/|D|` fraction of tapes. -/
theorem answerTape_pairCollision_card_le
    [Fintype D] [DecidableEq D]
    (T : ℕ) (pairs : Finset (Fin T × Fin T))
    (hne : ∀ p ∈ pairs, p.1 ≠ p.2) :
    (Finset.filter (PairCollision (D := D) T pairs) Finset.univ).card ≤
      pairs.card * (Fintype.card D) ^ (T - 1) := by
  classical
  calc
    (Finset.filter (PairCollision (D := D) T pairs) Finset.univ).card ≤
        ∑ p ∈ pairs,
          (Finset.filter (fun answers : Fin T → D =>
            answers p.1 = answers p.2) Finset.univ).card := by
      let pieces : (Fin T × Fin T) → Finset (Fin T → D) :=
        fun p => Finset.filter (fun answers =>
          answers p.1 = answers p.2) Finset.univ
      have heq : Finset.filter (PairCollision T pairs) Finset.univ =
          pairs.biUnion pieces := by
        ext answers
        simp [PairCollision, pieces]
      rw [heq]
      exact Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, (Fintype.card D) ^ (T - 1) := by
      exact Finset.sum_le_sum (fun p hp =>
        answerTape_fixed_pair_card_le T p.1 p.2 (hne p hp))
    _ = pairs.card * (Fintype.card D) ^ (T - 1) := by simp

/-- Generic union bound for a finite family of oracle bad events. -/
theorem card_iUnion_bad_le [Fintype Q] [DecidableEq Q]
    [Fintype D] [DecidableEq D]
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Bad : ι → (Q → D) → Prop)
    [∀ i, DecidablePred (Bad i)] :
    (Finset.filter (fun H => ∃ i ∈ s, Bad i H) Finset.univ).card ≤
      ∑ i ∈ s, (Finset.filter (Bad i) Finset.univ).card := by
  classical
  let pieces : ι → Finset (Q → D) :=
    fun i => Finset.filter (Bad i) Finset.univ
  have heq : Finset.filter (fun H => ∃ i ∈ s, Bad i H) Finset.univ =
      s.biUnion pieces := by
    ext H
    simp [pieces]
  rw [heq]
  exact Finset.card_biUnion_le

/-- A fixed set of guesses hits an injectively encoded uniform secret on at
most one secret per guess. This is the deterministic counting core of the
salt one-time lemma. -/
theorem injective_secret_hit_card_le
    {S : Type*} [Fintype S] [DecidableEq S]
    [Fintype Q] [DecidableEq Q]
    (encode : S → Q) (hinj : Function.Injective encode)
    (guesses : Finset Q) :
    (Finset.filter (fun s : S => encode s ∈ guesses) Finset.univ).card ≤
      guesses.card := by
  let f : {s : S // encode s ∈ guesses} → {q : Q // q ∈ guesses} :=
    fun s => ⟨encode s.val, s.property⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact hinj (congrArg Subtype.val h)
  rw [← Fintype.card_subtype]
  simpa using Fintype.card_le_of_injective f hf

/-! ## Finite coupling interface -/

/-- Under a common finite coupling, every distinguisher's real acceptance
count is at most its simulated acceptance count plus the number of samples on
which the coupled views differ. -/
theorem real_count_le_sim_add_disagreement
    {Ω : Type*} {V : Type*}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    (real sim : Ω → V) (P : V → Prop) [DecidablePred P] :
    (Finset.filter (fun ω => P (real ω)) Finset.univ).card ≤
      (Finset.filter (fun ω => P (sim ω)) Finset.univ).card +
      (Finset.filter (fun ω => real ω ≠ sim ω) Finset.univ).card := by
  let realEvent := Finset.filter (fun ω => P (real ω)) Finset.univ
  let simEvent := Finset.filter (fun ω => P (sim ω)) Finset.univ
  let bad := Finset.filter (fun ω => real ω ≠ sim ω) Finset.univ
  calc
    realEvent.card ≤ (simEvent ∪ bad).card := by
      apply Finset.card_le_card
      intro ω hω
      have hreal : P (real ω) := by simpa [realEvent] using hω
      by_cases hsim : P (sim ω)
      · exact Finset.mem_union_left _ (by simp [simEvent, hsim])
      · apply Finset.mem_union_right
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
        intro heq
        apply hsim
        rwa [← heq]
    _ ≤ simEvent.card + bad.card := Finset.card_union_le _ _

/-- Symmetric half of the finite coupling bound. Together with the preceding
theorem this bounds the absolute distinguishing-count gap. -/
theorem sim_count_le_real_add_disagreement
    {Ω : Type*} {V : Type*}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    (real sim : Ω → V) (P : V → Prop) [DecidablePred P] :
    (Finset.filter (fun ω => P (sim ω)) Finset.univ).card ≤
      (Finset.filter (fun ω => P (real ω)) Finset.univ).card +
      (Finset.filter (fun ω => real ω ≠ sim ω) Finset.univ).card := by
  simpa [ne_comm] using
    (real_count_le_sim_add_disagreement sim real P)

/-! ## Counting closeness and certified couplings -/

/-- Two views on a common finite uniform sample space are `eps`-close when
the chosen coupling disagrees on at most `eps` samples.  Its probability
interpretation is `eps / |Ω|`; keeping numerators avoids division and all
zero-denominator side conditions in the core lemmas. -/
def CountingClose {Ω : Type*} {V : Type*} [Fintype Ω]
    [DecidableEq Ω] [DecidableEq V]
    (eps : ℕ) (real sim : Ω → V) : Prop :=
  (Finset.filter (fun ω => real ω ≠ sim ω) Finset.univ).card ≤ eps

/-- A bad-event certificate is the form produced by lazy-sampling and hybrid
arguments: the coupled views agree off `bad`, whose size is bounded. -/
structure CouplingCertificate {Ω : Type*} {V : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (eps : ℕ) (real sim : Ω → V) where
  bad : Finset Ω
  bad_card : bad.card ≤ eps
  agrees : ∀ ω ∉ bad, real ω = sim ω

/-- A certified good-outside-bad coupling gives counting closeness. -/
theorem CountingClose.of_certificate
    {Ω : Type*} {V : Type*}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    {eps : ℕ} {real sim : Ω → V}
    (cert : CouplingCertificate eps real sim) :
    CountingClose eps real sim := by
  calc
    (Finset.filter (fun ω => real ω ≠ sim ω) Finset.univ).card ≤
        cert.bad.card := by
      apply Finset.card_le_card
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      by_contra hnot
      exact hω (cert.agrees ω hnot)
    _ ≤ eps := cert.bad_card

/-- Counting closeness bounds both directions of every distinguisher's
acceptance-count gap. -/
theorem CountingClose.distinguisher
    {Ω : Type*} {V : Type*}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    {eps : ℕ} {real sim : Ω → V}
    (hclose : CountingClose eps real sim)
    (P : V → Prop) [DecidablePred P] :
    (Finset.filter (fun ω => P (real ω)) Finset.univ).card ≤
        (Finset.filter (fun ω => P (sim ω)) Finset.univ).card + eps ∧
      (Finset.filter (fun ω => P (sim ω)) Finset.univ).card ≤
        (Finset.filter (fun ω => P (real ω)) Finset.univ).card + eps := by
  constructor
  · exact (real_count_le_sim_add_disagreement real sim P).trans
      (Nat.add_le_add_left hclose _)
  · exact (sim_count_le_real_add_disagreement real sim P).trans
      (Nat.add_le_add_left hclose _)

/-- Hybrid/triangle rule on a common coupling space. -/
theorem CountingClose.trans
    {Ω : Type*} {V : Type*}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    {e₀ e₁ : ℕ} {v₀ v₁ v₂ : Ω → V}
    (h₀ : CountingClose e₀ v₀ v₁)
    (h₁ : CountingClose e₁ v₁ v₂) :
    CountingClose (e₀ + e₁) v₀ v₂ := by
  let bad₀ := Finset.filter (fun ω => v₀ ω ≠ v₁ ω) Finset.univ
  let bad₁ := Finset.filter (fun ω => v₁ ω ≠ v₂ ω) Finset.univ
  calc
    (Finset.filter (fun ω => v₀ ω ≠ v₂ ω) Finset.univ).card ≤
        (bad₀ ∪ bad₁).card := by
      apply Finset.card_le_card
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      by_cases hmid : v₀ ω = v₁ ω
      · apply Finset.mem_union_right
        simp only [bad₁, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hlast
        exact hω (hmid.trans hlast)
      · exact Finset.mem_union_left _ (by simp [bad₀, hmid])
    _ ≤ bad₀.card + bad₁.card := Finset.card_union_le _ _
    _ ≤ e₀ + e₁ := Nat.add_le_add h₀ h₁

/-- Exact ratio form of finite statistical closeness.  It states that the
disagreement probability is at most `numer / denom` by cross multiplication,
and therefore remains meaningful when the sample space contains arbitrary
additional oracle, simulator, or adversary coins. -/
def CountingCloseRatio {Ω : Type*} {V : Type*} [Fintype Ω]
    [DecidableEq Ω] [DecidableEq V]
    (numer denom : ℕ) (real sim : Ω → V) : Prop :=
  (Finset.filter (fun ω => real ω ≠ sim ω) Finset.univ).card * denom ≤
    numer * Fintype.card Ω

/-- A good-outside-bad coupling plus a normalized bound on `bad` yields an
exact statistical-distance ratio. -/
theorem CountingCloseRatio.of_bad
    {Ω : Type*} {V : Type*}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    (numer denom : ℕ) (real sim : Ω → V) (bad : Finset Ω)
    (hbad : bad.card * denom ≤ numer * Fintype.card Ω)
    (hagrees : ∀ ω ∉ bad, real ω = sim ω) :
    CountingCloseRatio numer denom real sim := by
  have hsub : Finset.filter (fun ω => real ω ≠ sim ω) Finset.univ ⊆ bad := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_contra hnot
    exact hω (hagrees ω hnot)
  exact (Nat.mul_le_mul_right denom (Finset.card_le_card hsub)).trans hbad

/-- Ratio closeness bounds the cross-multiplied acceptance counts of every
distinguisher in both directions. -/
theorem CountingCloseRatio.distinguisher
    {Ω : Type*} {V : Type*}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    {numer denom : ℕ} {real sim : Ω → V}
    (hclose : CountingCloseRatio numer denom real sim)
    (P : V → Prop) [DecidablePred P] :
    (Finset.filter (fun ω => P (real ω)) Finset.univ).card * denom ≤
        (Finset.filter (fun ω => P (sim ω)) Finset.univ).card * denom +
          numer * Fintype.card Ω ∧
      (Finset.filter (fun ω => P (sim ω)) Finset.univ).card * denom ≤
        (Finset.filter (fun ω => P (real ω)) Finset.univ).card * denom +
          numer * Fintype.card Ω := by
  let disagree :=
    (Finset.filter (fun ω => real ω ≠ sim ω) Finset.univ).card
  have hr := real_count_le_sim_add_disagreement real sim P
  have hs := sim_count_le_real_add_disagreement real sim P
  constructor
  · calc
      (Finset.filter (fun ω => P (real ω)) Finset.univ).card * denom ≤
          ((Finset.filter (fun ω => P (sim ω)) Finset.univ).card +
            disagree) * denom := Nat.mul_le_mul_right denom hr
      _ = (Finset.filter (fun ω => P (sim ω)) Finset.univ).card * denom +
            disagree * denom := Nat.add_mul _ _ _
      _ ≤ (Finset.filter (fun ω => P (sim ω)) Finset.univ).card * denom +
            numer * Fintype.card Ω := Nat.add_le_add_left hclose _
  · calc
      (Finset.filter (fun ω => P (sim ω)) Finset.univ).card * denom ≤
          ((Finset.filter (fun ω => P (real ω)) Finset.univ).card +
            disagree) * denom := Nat.mul_le_mul_right denom hs
      _ = (Finset.filter (fun ω => P (real ω)) Finset.univ).card * denom +
            disagree * denom := Nat.add_mul _ _ _
      _ ≤ (Finset.filter (fun ω => P (real ω)) Finset.univ).card * denom +
            numer * Fintype.card Ω := Nat.add_le_add_left hclose _

/-! ## Lazy-sampled tape execution

The counting lemmas above are stated over an answer tape `Fin T → D`, while
`Tree.run` executes against a total oracle `Q → D`.  This section is the bridge:
it runs a bounded adaptive tree *against a tape*, sampling lazily, and exhibits
the total oracle that reproduces the same execution.
-/

section Tape

variable {A : Type uA} [DecidableEq Q]

/-- Record a query, if it is new. -/
def seenPush (seen : List Q) (q : Q) : List Q :=
  if q ∈ seen then seen else seen ++ [q]

theorem mem_seenPush (seen : List Q) (q : Q) : q ∈ seenPush seen q := by
  by_cases h : q ∈ seen <;> simp [seenPush, h]

theorem seenPush_prefix (seen : List Q) (q : Q) : seen <+: seenPush seen q := by
  by_cases h : q ∈ seen <;> simp [seenPush, h]

theorem seenPush_nodup {seen : List Q} (h : seen.Nodup) (q : Q) :
    (seenPush seen q).Nodup := by
  by_cases hq : q ∈ seen
  · simpa [seenPush, hq] using h
  · simp only [seenPush, if_neg hq, List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    rintro a ha b hb rfl
    exact hq (List.mem_singleton.mp hb ▸ ha)

theorem seenPush_length_le (seen : List Q) (q : Q) :
    (seenPush seen q).length ≤ seen.length + 1 := by
  by_cases h : q ∈ seen <;> simp [seenPush, h]

private theorem idxOf_append_singleton_self {l : List Q} {q : Q} (h : q ∉ l) :
    (l ++ [q]).idxOf q = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.mem_cons, not_or] at h
      simp [Ne.symm h.1, ih h.2]

theorem seenPush_idxOf (seen : List Q) (q : Q) :
    (seenPush seen q).idxOf q = seen.idxOf q := by
  by_cases h : q ∈ seen
  · simp [seenPush, h]
  · simp [seenPush, h, idxOf_append_singleton_self h]

theorem idxOf_of_prefix {l₁ l₂ : List Q} (hp : l₁ <+: l₂) {q : Q} (hq : q ∈ l₁) :
    l₂.idxOf q = l₁.idxOf q := by
  obtain ⟨r, rfl⟩ := hp
  exact List.idxOf_append_of_mem hq


/-! ### Lazy-sampled execution -/

/-- Lazy-sampling oracle induced by a tape and a seen-list: the `k`-th distinct
query recorded is answered by tape slot `k`.  Queries outside `seen` all fall to
slot `seen.length`; the games constrain the oracle only at queries that were
actually made. -/
def tapeOracle (tape : ℕ → D) (seen : List Q) : Q → D :=
  fun q => tape (seen.idxOf q)

/-- Execute a bounded adaptive tree against an answer tape, sampling lazily: a
fresh query consumes the next tape slot, a repeated query reuses its first
answer.  Returns the output together with the queries made, in order of first
occurrence — so the returned list *is* the slot assignment. -/
def Tree.runTape {fuel : ℕ} :
    Tree Q D A fuel → (ℕ → D) → List Q → A × List Q
  | .done a, _, seen => (a, seen)
  | .query q next, tape, seen =>
      (next (tape (seen.idxOf q))).runTape tape (seenPush seen q)

@[simp] theorem Tree.runTape_done {fuel : ℕ} (a : A) (tape : ℕ → D)
    (seen : List Q) :
    (Tree.done (fuel := fuel) a : Tree Q D A fuel).runTape tape seen =
      (a, seen) := rfl

@[simp] theorem Tree.runTape_query {fuel : ℕ} (q : Q)
    (next : D → Tree Q D A fuel) (tape : ℕ → D) (seen : List Q) :
    (Tree.query q next).runTape tape seen =
      (next (tape (seen.idxOf q))).runTape tape (seenPush seen q) := rfl

/-- The seen-list only grows, and grows on the right: slots already assigned
keep their index. -/
theorem Tree.runTape_prefix {fuel : ℕ} (c : Tree Q D A fuel) (tape : ℕ → D) :
    ∀ seen : List Q, seen <+: (c.runTape tape seen).2 := by
  induction c with
  | done a => intro seen; simp
  | @query fuel q next ih =>
      intro seen
      exact (seenPush_prefix seen q).trans (ih _ (seenPush seen q))

/-- Distinct queries get distinct slots. -/
theorem Tree.runTape_nodup {fuel : ℕ} (c : Tree Q D A fuel) (tape : ℕ → D) :
    ∀ {seen : List Q}, seen.Nodup → (c.runTape tape seen).2.Nodup := by
  induction c with
  | done a => intro seen h; simpa using h
  | @query fuel q next ih =>
      intro seen h
      simpa using ih _ (seenPush_nodup h q)

/-- A `fuel`-query execution consumes at most `fuel` fresh slots. -/
theorem Tree.runTape_length_le {fuel : ℕ} (c : Tree Q D A fuel) (tape : ℕ → D) :
    ∀ seen : List Q, (c.runTape tape seen).2.length ≤ seen.length + fuel := by
  induction c with
  | done a => intro seen; simp
  | @query fuel q next ih =>
      intro seen
      have h := ih (tape (seen.idxOf q)) (seenPush seen q)
      have h2 := seenPush_length_le seen q
      simp only [Tree.runTape_query]
      omega

/-- The answer a query receives is its own slot's tape entry, computed with
the seen-list as it stood at query time. -/
private theorem tapeOracle_head {fuel : ℕ} (q : Q) (next : D → Tree Q D A fuel)
    (tape : ℕ → D) (seen : List Q) :
    tapeOracle tape
        ((next (tape (seen.idxOf q))).runTape tape (seenPush seen q)).2 q =
      tape (seen.idxOf q) := by
  show tape (List.idxOf q _) = _
  rw [idxOf_of_prefix
    (Tree.runTape_prefix (next (tape (seen.idxOf q))) tape (seenPush seen q))
    (mem_seenPush seen q), seenPush_idxOf]

/-- **The bridge.**  Running against the tape and running against the induced
total oracle produce the same output.  This is what connects the adaptive
syntax of `Tree` to the answer-tape counting lemmas. -/
theorem Tree.run_tapeOracle {fuel : ℕ} (c : Tree Q D A fuel) (tape : ℕ → D) :
    ∀ seen : List Q,
      (c.run (tapeOracle tape (c.runTape tape seen).2)).1 =
        (c.runTape tape seen).1 := by
  induction c with
  | done a => intro seen; simp
  | @query fuel q next ih =>
      intro seen
      simp only [Tree.runTape_query, Tree.run_query, tapeOracle_head]
      exact ih (tape (seen.idxOf q)) (seenPush seen q)

/-- Every query the execution makes is recorded, hence occupies a slot. -/
theorem Tree.tapeOracle_trace_mem {fuel : ℕ} (c : Tree Q D A fuel)
    (tape : ℕ → D) :
    ∀ seen : List Q,
      ∀ qa ∈ (c.run (tapeOracle tape (c.runTape tape seen).2)).2,
        qa.1 ∈ (c.runTape tape seen).2 := by
  induction c with
  | done a => intro seen qa hqa; simp at hqa
  | @query fuel q next ih =>
      intro seen qa hqa
      simp only [Tree.runTape_query] at hqa ⊢
      rw [Tree.run_query] at hqa
      simp only [List.mem_cons, tapeOracle_head] at hqa
      rcases hqa with rfl | htail
      · exact (Tree.runTape_prefix _ tape _).subset (mem_seenPush seen q)
      · exact ih (tape (seen.idxOf q)) (seenPush seen q) qa htail

/-- Slot soundness: the query recorded in slot `i` is answered by tape slot
`i`.  This is the `answer_sound` field of a ROM game. -/
theorem tapeOracle_getElem {seen : List Q} (hnd : seen.Nodup) (tape : ℕ → D)
    (i : ℕ) (hi : i < seen.length) :
    tapeOracle tape seen seen[i] = tape i := by
  simp [tapeOracle, hnd.idxOf_getElem i hi]

/-- Only the first `seen.length + fuel` tape slots are ever read, so a finite
tape of that length determines the execution. -/
theorem Tree.runTape_congr {fuel : ℕ} (c : Tree Q D A fuel)
    (tape tape' : ℕ → D) :
    ∀ seen : List Q, (∀ k, k < seen.length + fuel → tape k = tape' k) →
      c.runTape tape seen = c.runTape tape' seen := by
  induction c with
  | done a => intro seen _; simp
  | @query fuel q next ih =>
      intro seen h
      have hhead : tape (seen.idxOf q) = tape' (seen.idxOf q) := by
        have : List.idxOf q seen ≤ seen.length := List.idxOf_le_length
        exact h _ (by omega)
      simp only [Tree.runTape_query, hhead]
      refine ih _ (seenPush seen q) (fun k hk => h k ?_)
      have := seenPush_length_le seen q
      omega

/-! ### Slot indexing -/

/-- The query occupying slot `j`, with an explicit fallback for slots the
execution never reached. -/
def slotQuery (seen : List Q) (dummy : Q) (j : ℕ) : Q :=
  seen.getD j dummy

/-- Slot soundness in the slot-indexed form a ROM game consumes. -/
theorem tapeOracle_slotQuery {seen : List Q} (hnd : seen.Nodup) (tape : ℕ → D)
    (dummy : Q) (j : ℕ) (hj : j < seen.length) :
    tapeOracle tape seen (slotQuery seen dummy j) = tape j := by
  rw [slotQuery, List.getD_eq_getElem _ _ hj]
  exact tapeOracle_getElem hnd tape j hj

/-- Distinct recorded queries occupy distinct slots.  This is what turns a
located collision into a collision of two *distinct* tape coordinates, which is
exactly the hypothesis of `answerTape_pairCollision_card_le`. -/
theorem idxOf_ne_of_ne {seen : List Q} {x₀ x₁ : Q}
    (h₀ : x₀ ∈ seen) (h₁ : x₁ ∈ seen) (hne : x₀ ≠ x₁) :
    seen.idxOf x₀ ≠ seen.idxOf x₁ := by
  intro heq
  apply hne
  have e₀ := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr h₀)
  have e₁ := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr h₁)
  rw [← e₀, ← e₁]
  simp [heq]

/-! ### Finite tapes -/

/-- Read a finite answer tape as an infinite one by padding past its end.  With
`Tree.runTape_congr`, a tape of length `T ≥ fuel` already determines the whole
execution, so the counting lemmas over `Fin T → D` apply verbatim. -/
def finTape [Inhabited D] {T : ℕ} (tape : Fin T → D) : ℕ → D :=
  fun k => if h : k < T then tape ⟨k, h⟩ else default

@[simp] theorem finTape_val [Inhabited D] {T : ℕ} (tape : Fin T → D)
    (j : Fin T) : finTape tape j.val = tape j := by
  simp [finTape, j.isLt]

theorem finTape_of_lt [Inhabited D] {T : ℕ} (tape : Fin T → D) {k : ℕ}
    (h : k < T) : finTape tape k = tape ⟨k, h⟩ := by
  simp [finTape, h]

/-! ### Regression: lazy reuse -/

/-- Three queries, one of them repeated. -/
private def repeatQuery : Tree (Fin 2) Bool Unit 3 :=
  .query 0 (fun _ => .query 1 (fun _ => .query 0 (fun _ => .done ())))

/-- The repeated query reuses its first slot instead of consuming a fresh one:
three queries, two slots. -/
private example (tape : ℕ → Bool) : (repeatQuery.runTape tape []).2 = [0, 1] :=
  rfl

end Tape

end RandomOracle

end Merkle
