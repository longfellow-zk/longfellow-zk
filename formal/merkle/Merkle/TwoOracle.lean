import Merkle.TreeCompose

/-!
# Bounded executions with two random oracles

The usual `RandomOracle.Tree` exposes adaptivity to one oracle.  Fiat--Shamir compilation needs
one more piece of syntax: the prover may interleave calls to the Merkle oracle and to the
challenge oracle.  Treating the challenge and query as arbitrary functions of a completed Merkle
tape loses that scheduling information and is too strong for the Merkle extraction count.

`TwoOracleTree` records both kinds of query, with a separate syntactic budget for each.  Fixing one
answer tape compiles it to an ordinary `Tree` over the other oracle.  Thus the same execution can be
sliced in the two ways used by the composition proof:

* fix the challenge tape and apply the Merkle extraction theorem to a Merkle-oracle `Tree`;
* fix the Merkle tape and apply the Fiat--Shamir count to a challenge-oracle `Tree`.

The output-coherence theorem says these are two views of one execution, not two independently
chosen families of programs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace RandomOracle

universe uQL uDL uQR uDR uA

/-- An adaptive program with at most `leftFuel` calls to the left oracle and `rightFuel` calls to
the right oracle. -/
inductive TwoOracleTree (QL : Type uQL) (DL : Type uDL) (QR : Type uQR) (DR : Type uDR)
    (A : Type uA) : ℕ → ℕ → Type _ where
  | done {leftFuel rightFuel : ℕ} (a : A) :
      TwoOracleTree QL DL QR DR A leftFuel rightFuel
  | queryLeft {leftFuel rightFuel : ℕ} (q : QL)
      (next : DL → TwoOracleTree QL DL QR DR A leftFuel rightFuel) :
      TwoOracleTree QL DL QR DR A (leftFuel + 1) rightFuel
  | queryRight {leftFuel rightFuel : ℕ} (q : QR)
      (next : DR → TwoOracleTree QL DL QR DR A leftFuel rightFuel) :
      TwoOracleTree QL DL QR DR A leftFuel (rightFuel + 1)

namespace TwoOracleTree

variable {QL : Type uQL} {DL : Type uDL} {QR : Type uQR} {DR : Type uDR} {A : Type uA}

/-! ## Right-oracle continuations -/

/-- Regard a one-oracle right program as a two-oracle program with an arbitrary unused left
budget.  Keeping that budget polymorphic makes it usable after an interleaved search. -/
def liftRightAt (leftFuel : ℕ) :
    {rightFuel : ℕ} → Tree QR DR A rightFuel →
      TwoOracleTree QL DL QR DR A leftFuel rightFuel
  | _, .done a => .done a
  | _, .query q next => .queryRight q fun y => liftRightAt leftFuel (next y)

/-- Increase only the right-oracle syntactic budget. -/
def weakenRight : {leftFuel rightFuel : ℕ} →
    TwoOracleTree QL DL QR DR A leftFuel rightFuel →
      TwoOracleTree QL DL QR DR A leftFuel (rightFuel + 1)
  | _, _, .done a => .done a
  | _, _, .queryLeft q next => .queryLeft q fun y => weakenRight (next y)
  | _, _, .queryRight q next => .queryRight q fun y => weakenRight (next y)

/-- Increase the right-oracle budget by a fixed amount. -/
def weakenRightAdd : {leftFuel rightFuel : ℕ} → (k : ℕ) →
    TwoOracleTree QL DL QR DR A leftFuel rightFuel →
      TwoOracleTree QL DL QR DR A leftFuel (rightFuel + k)
  | _, _, 0, tree => tree
  | _, _, k + 1, tree => weakenRight (weakenRightAdd k tree)

/-- Run an interleaved search and then a continuation which uses only the right oracle. -/
def bindRight {B : Type*} {rightFuel₂ : ℕ} :
    {leftFuel rightFuel₁ : ℕ} →
      TwoOracleTree QL DL QR DR A leftFuel rightFuel₁ →
      (A → Tree QR DR B rightFuel₂) →
      TwoOracleTree QL DL QR DR B leftFuel (rightFuel₂ + rightFuel₁)
  | leftFuel, rightFuel₁, .done a, next =>
      weakenRightAdd rightFuel₁ (liftRightAt leftFuel (next a))
  | _, _, .queryLeft q next, rest =>
      .queryLeft q fun y => bindRight (next y) rest
  | _, _, .queryRight q next, rest =>
      .queryRight q fun y => bindRight (next y) rest

/-- Fix the left answer tape.  Left queries are evaluated lazily and right queries remain as an
ordinary adaptive tree. -/
def fixLeft [DecidableEq QL] {TL : ℕ} (leftTape : Fin TL → DL) (leftDefault : DL) :
    {leftFuel rightFuel : ℕ} → TwoOracleTree QL DL QR DR A leftFuel rightFuel →
      List QL → Tree QR DR A rightFuel
  | _, _, .done a, _ => .done a
  | _, _, .queryLeft q next, seen =>
      let seen' := if q ∈ seen then seen else seen ++ [q]
      let y := tapeAt leftTape leftDefault (seen'.idxOf q)
      fixLeft leftTape leftDefault (next y) seen'
  | _, _, .queryRight q next, seen =>
      .query q fun y => fixLeft leftTape leftDefault (next y) seen

/-- With no right-oracle queries, fixing the left tape fixes the prover's
output. In particular, it cannot depend on the transcript random oracle. -/
theorem fixLeft_zero_run_eq [DecidableEq QL]
    {TL leftFuel : ℕ} (leftTape : Fin TL → DL) (leftDefault : DL)
    (tree : TwoOracleTree QL DL QR DR A leftFuel 0) (seen : List QL)
    (H H' : QR → DR) :
    (fixLeft leftTape leftDefault tree seen).run H =
      (fixLeft leftTape leftDefault tree seen).run H' := by
  cases fixLeft leftTape leftDefault tree seen with
  | done _ => rfl

/-- A zero-query prover has the same output and right-oracle slot list for
every right answer tape.  This is the lazy-tape form needed when comparing a
Fiat--Shamir experiment with an interactive verifier after the Merkle tape
has been fixed. -/
theorem fixLeft_zero_lazyRun_eq [DecidableEq QL] [DecidableEq QR]
    {TL TR TR' leftFuel : ℕ} (leftTape : Fin TL → DL) (leftDefault : DL)
    (tree : TwoOracleTree QL DL QR DR A leftFuel 0) (seenLeft : List QL)
    (rightTape : Fin TR → DR) (rightTape' : Fin TR' → DR)
    (rightDefault rightDefault' : DR) (seenRight : List QR) :
    lazyRun rightTape rightDefault
        (fixLeft leftTape leftDefault tree seenLeft) seenRight =
      lazyRun rightTape' rightDefault'
        (fixLeft leftTape leftDefault tree seenLeft) seenRight := by
  cases fixLeft leftTape leftDefault tree seenLeft with
  | done _ => rfl

@[simp] theorem fixLeft_liftRightAt [DecidableEq QL]
    {TL leftFuel rightFuel : ℕ} (leftTape : Fin TL → DL) (leftDefault : DL)
    (tree : Tree QR DR A rightFuel) (seen : List QL) :
    fixLeft leftTape leftDefault (liftRightAt (QL := QL) (DL := DL) leftFuel tree) seen = tree := by
  induction tree with
  | done a => rfl
  | query q next ih =>
      simp only [liftRightAt, fixLeft]
      congr
      funext y
      exact ih y

@[simp] theorem fixLeft_weakenRight [DecidableEq QL]
    {TL leftFuel rightFuel : ℕ} (leftTape : Fin TL → DL) (leftDefault : DL)
    (tree : TwoOracleTree QL DL QR DR A leftFuel rightFuel) (seen : List QL) :
    fixLeft leftTape leftDefault (weakenRight tree) seen =
      (fixLeft leftTape leftDefault tree seen).weaken := by
  induction tree generalizing seen with
  | done a => rfl
  | queryLeft q next ih =>
      simp only [weakenRight, fixLeft]
      exact ih _ _
  | queryRight q next ih =>
      simp only [weakenRight, fixLeft, Tree.weaken]
      congr
      funext y
      exact ih y seen

@[simp] theorem fixLeft_weakenRightAdd [DecidableEq QL]
    {TL leftFuel rightFuel : ℕ} (leftTape : Fin TL → DL) (leftDefault : DL)
    (k : ℕ) (tree : TwoOracleTree QL DL QR DR A leftFuel rightFuel) (seen : List QL) :
    fixLeft leftTape leftDefault (weakenRightAdd k tree) seen =
      (fixLeft leftTape leftDefault tree seen).weakenAdd k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [weakenRightAdd, fixLeft_weakenRight, ih, Tree.weakenAdd]

@[simp] theorem fixLeft_bindRight [DecidableEq QL]
    {B : Type*} {TL leftFuel rightFuel₁ rightFuel₂ : ℕ}
    (leftTape : Fin TL → DL) (leftDefault : DL)
    (tree : TwoOracleTree QL DL QR DR A leftFuel rightFuel₁)
    (next : A → Tree QR DR B rightFuel₂) (seen : List QL) :
    fixLeft leftTape leftDefault (bindRight tree next) seen =
      (fixLeft leftTape leftDefault tree seen).bind next := by
  induction tree generalizing seen with
  | done a =>
      simp only [bindRight, fixLeft_weakenRightAdd, fixLeft_liftRightAt, fixLeft, Tree.bind]
  | queryLeft q rest ih =>
      simp only [bindRight, fixLeft]
      exact ih _ _
  | queryRight q rest ih =>
      simp only [bindRight, fixLeft, Tree.bind]
      congr
      funext y
      exact ih y seen

/-- Fix the right answer tape.  Right queries are evaluated lazily and left queries remain as an
ordinary adaptive tree. -/
def fixRight [DecidableEq QR] {TR : ℕ} (rightTape : Fin TR → DR) (rightDefault : DR) :
    {leftFuel rightFuel : ℕ} → TwoOracleTree QL DL QR DR A leftFuel rightFuel →
      List QR → Tree QL DL A leftFuel
  | _, _, .done a, _ => .done a
  | _, _, .queryLeft q next, seen =>
      .query q fun y => fixRight rightTape rightDefault (next y) seen
  | _, _, .queryRight q next, seen =>
      let seen' := if q ∈ seen then seen else seen ++ [q]
      let y := tapeAt rightTape rightDefault (seen'.idxOf q)
      fixRight rightTape rightDefault (next y) seen'

/-- Fixing the left tape can also return the final left-oracle slot list.  This is useful when a
later one-oracle phase must resume the left oracle after the interleaved phase. -/
def fixLeftState [DecidableEq QL] {TL : ℕ} (leftTape : Fin TL → DL) (leftDefault : DL) :
    {leftFuel rightFuel : ℕ} → TwoOracleTree QL DL QR DR A leftFuel rightFuel →
      List QL → Tree QR DR (A × List QL) rightFuel
  | _, _, .done a, seen => .done (a, seen)
  | _, _, .queryLeft q next, seen =>
      let seen' := if q ∈ seen then seen else seen ++ [q]
      let y := tapeAt leftTape leftDefault (seen'.idxOf q)
      fixLeftState leftTape leftDefault (next y) seen'
  | _, _, .queryRight q next, seen =>
      .query q fun y => fixLeftState leftTape leftDefault (next y) seen

@[simp] theorem fixLeftState_fst [DecidableEq QL] [DecidableEq QR]
    {TL TR leftFuel rightFuel : ℕ} (leftTape : Fin TL → DL) (rightTape : Fin TR → DR)
    (leftDefault : DL) (rightDefault : DR)
    (tree : TwoOracleTree QL DL QR DR A leftFuel rightFuel) (seenLeft : List QL)
    (seenRight : List QR) :
    (lazyRun rightTape rightDefault
        (fixLeftState leftTape leftDefault tree seenLeft) seenRight).1.1 =
      (lazyRun rightTape rightDefault (fixLeft leftTape leftDefault tree seenLeft) seenRight).1 := by
  induction tree generalizing seenLeft seenRight with
  | done a => rfl
  | queryLeft q next ih =>
      simp only [fixLeftState, fixLeft]
      exact ih _ _ _
  | queryRight q next ih =>
      simp only [fixLeftState, fixLeft, lazyRun_query]
      exact ih _ _ _

/-- The two one-oracle compilations have the same output.  Both sides use lazy first-occurrence
semantics and may start from nonempty slot lists, so this also applies after a commitment prefix. -/
theorem fixLeft_fixRight_output [DecidableEq QL] [DecidableEq QR]
    {TL TR leftFuel rightFuel : ℕ} (leftTape : Fin TL → DL) (rightTape : Fin TR → DR)
    (leftDefault : DL) (rightDefault : DR)
    (tree : TwoOracleTree QL DL QR DR A leftFuel rightFuel) (seenLeft : List QL)
    (seenRight : List QR) :
    (lazyRun rightTape rightDefault (fixLeft leftTape leftDefault tree seenLeft) seenRight).1 =
      (lazyRun leftTape leftDefault (fixRight rightTape rightDefault tree seenRight) seenLeft).1 := by
  induction tree generalizing seenLeft seenRight with
  | done a => rfl
  | queryLeft q next ih =>
      simp only [fixLeft, fixRight, lazyRun_query]
      exact ih _ _ _
  | queryRight q next ih =>
      simp only [fixLeft, fixRight, lazyRun_query]
      exact ih _ _ _

end TwoOracleTree

end RandomOracle

end Merkle
