import Mathlib
import Collision
import RandomOracle

/-!
# Binding in the standard model and finite random-oracle counting

`mh_binding_of_collision` in `Collision.lean` is the primary standard-model
result. This file also gives two finite-ROM formulations: a loose bound for
full-oracle binders, and a sharp answer-tape theorem for a bounded combined
binder/check execution.  The latter records the fixed tape slots in which the
extractor's pair can occur, so adaptive query values cannot smuggle in a
full-oracle dependency.
-/

open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

universe uSalt uMsg uDigest uEnc

variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest}
variable {Enc : Type uEnc}

/-- Raw, oracle-independent binder output. Acceptance is evaluated by the
game against the sampled oracle. -/
structure BindingAttempt (n : ℕ) (Salt : Type uSalt) (M : Type uMsg)
    (D : Type uDigest) where
  rt : D
  I₀ : Finset (Fin n)
  I₁ : Finset (Fin n)
  a₀ : Fin n → M
  a₁ : Fin n → M
  pf₀ : Opening n I₀ Salt D
  pf₁ : Opening n I₁ Salt D

/-- Binding-game winning predicate for a raw attempt. -/
def IsBindingBreak [Inhabited D] (S : Scheme Salt M D Enc) (n : ℕ)
    (out : BindingAttempt n Salt M D) : Prop :=
  Accepts S n out.rt out.I₀ out.a₀ out.pf₀ ∧
  Accepts S n out.rt out.I₁ out.a₁ out.pf₁ ∧
  ∃ i : Fin n, i ∈ out.I₀ ∧ i ∈ out.I₁ ∧ out.a₀ i ≠ out.a₁ i

/-- The raw game predicate still constructively yields a collision. -/
theorem bindingAttempt_collision [Inhabited D] {S : Scheme Salt M D Enc}
    (hinj : S.Inj) (n : ℕ) (out : BindingAttempt n Salt M D)
    (hbreak : IsBindingBreak S n out) : Collision S.H := by
  rcases hbreak with ⟨hacc₀, hacc₁, i, hi₀, hi₁, hmsg⟩
  exact mh_collision S hinj n out.rt
    out.I₀ out.I₁ out.a₀ out.a₁ out.pf₀ out.pf₁ hacc₀ hacc₁
    i hi₀ hi₁ hmsg

/-- The two encoded inputs are a *located* collision for `out`: each is a
query of the selected-index trace of one of the two openings, and both receive
the same answer.  This is exactly the data `mh_collision_lemma` returns. -/
def LocatedCollision [Inhabited D] (S : Scheme Salt M D Enc) (n : ℕ)
    (out : BindingAttempt n Salt M D) (x₀ x₁ : Enc) : Prop :=
  ∃ (i : Fin n) (hi₀ : i ∈ out.I₀) (hi₁ : i ∈ out.I₁) (y : D),
    InIndexTrace S n out.I₀ out.a₀ out.pf₀ i hi₀ x₀ y ∧
    InIndexTrace S n out.I₁ out.a₁ out.pf₁ i hi₁ x₁ y

/-- A located collision really is a collision of `H`. -/
theorem LocatedCollision.hash_eq [Inhabited D] {S : Scheme Salt M D Enc}
    {n : ℕ} {out : BindingAttempt n Salt M D} {x₀ x₁ : Enc}
    (hloc : LocatedCollision S n out x₀ x₁) :
    S.H x₀ = S.H x₁ := by
  rcases hloc with ⟨i, hi₀, hi₁, y, ht₀, ht₁⟩
  rw [← indexTrace_sound S n out.I₀ out.a₀ out.pf₀ i hi₀ x₀ y ht₀,
    ← indexTrace_sound S n out.I₁ out.a₁ out.pf₁ i hi₁ x₁ y ht₁]

/-- Strengthening of `bindingAttempt_collision`: the extracted collision is
not merely some pair of inputs, it is a pair of queries the two accepting
checks actually make.  Only this located form can be covered by a fixed,
query-sized slot layout. -/
theorem bindingAttempt_locatedCollision [Inhabited D]
    {S : Scheme Salt M D Enc} (hinj : S.Inj)
    (n : ℕ) (out : BindingAttempt n Salt M D)
    (hbreak : IsBindingBreak S n out) :
    ∃ x₀ x₁, x₀ ≠ x₁ ∧ LocatedCollision S n out x₀ x₁ := by
  rcases hbreak with ⟨hacc₀, hacc₁, i, hi₀, hi₁, hmsg⟩
  rcases mh_collision_lemma S hinj n out.rt
      out.I₀ out.I₁ out.a₀ out.a₁ out.pf₀ out.pf₁ hacc₀ hacc₁
      i hi₀ hi₁ hmsg with ⟨x₀, x₁, y, ht₀, ht₁, hne⟩
  exact ⟨x₀, x₁, hne, i, hi₀, hi₁, y, ht₀, ht₁⟩

/-- Regression guard for the shape of `ROMBindingGame.covers_collision`.  For
any realistic hash-input type `Enc` is infinite while `D` is finite, so *every*
oracle collides.  A covering obligation phrased over `Collision (oracle
answers)` rather than over a located pair would therefore have to be discharged
on every answer tape; that forces `|D| ≤ ownPairs.card + freshPairs.card` and
makes the resulting bound vacuous.  Hence the located form below. -/
theorem collision_of_infinite_enc [Infinite Enc] [Finite D] (H : Enc → D) :
    Collision H := by
  obtain ⟨x₀, x₁, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite H
  exact ⟨x₀, x₁, hne, heq⟩

/-! ## Closed query-sized lazy-ROM game -/

/-- A finite lazy-sampling binding experiment.

`T` is the total answer-tape length of the combined binder and checker.  The
binder's own possible collision slots are `ownPairs`; `freshPairs` are the
two selected index traces used by `mh_collision_lemma`.  Query *values* may
depend on the entire preceding tape through `query`, but the slot layout is
fixed.  `covers_collision` is the trace-coverage obligation discharged when
compiling the binder and the two checks into this combined execution.

Unlike the old event-assembly theorem, the structure does not assume either
cardinality estimate: only the syntactic pair counts and oracle/answer-tape
consistency are fields, and the fixed-pair ROM lemma performs the counting.

`covers_collision` is deliberately stated over a `LocatedCollision`, i.e. over
the pair of queries the two accepting checks actually make, and asks only that
those two encodings occupy a fixed pair of tape slots.  Stating it over a bare
`Collision (oracle answers)` would be unsatisfiable at real parameters — see
`collision_of_infinite_enc`. -/
structure ROMBindingGame [Inhabited D] (C : Codec Salt M D Enc)
    (n T t dmax : ℕ) where
  oracle : (Fin T → D) → Enc → D
  /-- The binder is syntactically bounded by `t` adaptive oracle queries. -/
  binder : RandomOracle.Tree Enc D (BindingAttempt n Salt M D) t
  attempt : (Fin T → D) → BindingAttempt n Salt M D
  attempt_run : ∀ answers,
    attempt answers = (binder.run (oracle answers)).1
  query : (answers : Fin T → D) → Fin T → Enc
  ownPairs : Finset (Fin T × Fin T)
  freshPairs : Finset (Fin T × Fin T)
  own_card : ownPairs.card ≤ t * (t - 1) / 2
  fresh_card : freshPairs.card ≤ (dmax + 1) ^ 2
  pair_distinct : ∀ p ∈ ownPairs ∪ freshPairs, p.1 ≠ p.2
  answer_sound : ∀ answers j, oracle answers (query answers j) = answers j
  covers_collision : ∀ answers x₀ x₁,
    LocatedCollision (C.withOracle (oracle answers)) n (attempt answers)
      x₀ x₁ →
    x₀ ≠ x₁ →
    ∃ p ∈ ownPairs ∪ freshPairs,
      query answers p.1 = x₀ ∧ query answers p.2 = x₁

/-- Winning event of the bounded lazy-ROM binding game. -/
def ROMBindingGame.Bad [Inhabited D]
    {C : Codec Salt M D Enc} {n T t dmax : ℕ}
    (game : ROMBindingGame C n T t dmax)
    (answers : Fin T → D) : Prop :=
  IsBindingBreak (C.withOracle (game.oracle answers)) n
    (game.attempt answers)

/-- **Query-sized ROM binding theorem.**  A `t`-query binder whose extracted
collision is covered by two selected traces of length at most `dmax+1` wins
on at most

`(t(t-1)/2 + (dmax+1)^2) * |D|^(T-1)`

of the `|D|^T` uniform answer tapes.  This is exactly the cardinality form of
`t(t-1)/(2|D|) + (dmax+1)^2/|D|`. -/
theorem mh_binding_bound_rom [Inhabited D]
    [Fintype D] [DecidableEq D]
    {C : Codec Salt M D Enc} (hinj : C.Inj)
    (n T t dmax : ℕ)
    (game : ROMBindingGame C n T t dmax)
    [DecidablePred game.Bad] :
    (Finset.filter game.Bad Finset.univ).card ≤
      (t * (t - 1) / 2 + (dmax + 1) ^ 2) *
        (Fintype.card D) ^ (T - 1) := by
  let pairs := game.ownPairs ∪ game.freshPairs
  have hpairs : pairs.card ≤
      t * (t - 1) / 2 + (dmax + 1) ^ 2 := by
    calc
      pairs.card ≤ game.ownPairs.card + game.freshPairs.card :=
        Finset.card_union_le _ _
      _ ≤ t * (t - 1) / 2 + (dmax + 1) ^ 2 :=
        Nat.add_le_add game.own_card game.fresh_card
  calc
    (Finset.filter game.Bad Finset.univ).card ≤
        (Finset.filter
          (RandomOracle.PairCollision (D := D) T pairs)
          Finset.univ).card := by
      apply Finset.card_le_card
      intro answers hanswers
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hanswers ⊢
      rcases bindingAttempt_locatedCollision (S := C.withOracle
          (game.oracle answers)) hinj n (game.attempt answers) hanswers with
        ⟨x₀, x₁, hne, hloc⟩
      rcases game.covers_collision answers x₀ x₁ hloc hne with ⟨p, hp, h₀, h₁⟩
      refine ⟨p, hp, ?_⟩
      rw [← game.answer_sound answers p.1, ← game.answer_sound answers p.2,
        h₀, h₁]
      exact LocatedCollision.hash_eq hloc
    _ ≤ pairs.card * (Fintype.card D) ^ (T - 1) :=
      RandomOracle.answerTape_pairCollision_card_le T pairs
        (fun p hp => game.pair_distinct p hp)
    _ ≤ (t * (t - 1) / 2 + (dmax + 1) ^ 2) *
          (Fintype.card D) ^ (T - 1) :=
      Nat.mul_le_mul_right _ hpairs

/-- Cross-multiplied probability corollary.  For `T>0` and a nonempty digest
space this says `bad / |D|^T ≤ coefficient / |D|` without introducing a
particular rational-probability library. -/
theorem mh_binding_bound_rom_fraction [Inhabited D]
    [Fintype D] [DecidableEq D]
    {C : Codec Salt M D Enc} (hinj : C.Inj)
    (n T t dmax : ℕ) (hT : 0 < T)
    (game : ROMBindingGame C n T t dmax)
    [DecidablePred game.Bad] :
    (Finset.filter game.Bad Finset.univ).card *
        Fintype.card D ≤
      (t * (t - 1) / 2 + (dmax + 1) ^ 2) *
        (Fintype.card D) ^ T := by
  have h := mh_binding_bound_rom hinj n T t dmax game
  calc
    (Finset.filter game.Bad Finset.univ).card *
        Fintype.card D ≤
      ((t * (t - 1) / 2 + (dmax + 1) ^ 2) *
        (Fintype.card D) ^ (T - 1)) * Fintype.card D :=
      Nat.mul_le_mul_right _ h
    _ = (t * (t - 1) / 2 + (dmax + 1) ^ 2) *
        (Fintype.card D) ^ T := by
      rw [Nat.mul_assoc]
      rw [← Nat.pow_succ]
      congr 2
      omega

end MH

end Merkle
