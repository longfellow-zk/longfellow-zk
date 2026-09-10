import Mathlib
import Merkle
import RandomOracle

/-!
# Hiding simulator

This file gives the exact simulator, finite counting kernels, and normalized
real/sim coupling theorems.  All oracle, commitment, simulator, and adversary
coins live in one explicit finite sample space `Ω`.  Bounds are stated by
cross multiplication, so adding unrelated coins to `Ω` cannot change the
claimed probability.
-/

open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

universe uSalt uMsg uDigest uEnc

variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest}
variable {Enc : Type uEnc}
variable (S : Scheme Salt M D Enc) [Inhabited D]

/-- Opening simulator coins: fresh nonces for opened leaves and simulated
roots for every frontier subtree. -/
structure SimulatorCoins (n : ℕ) (I : Finset (Fin n))
    (Salt : Type uSalt) (D : Type uDigest) where
  nonce : (i : {i : Fin n // i ∈ I}) → Salt
  frontierRoot : (v : {v : ℕ // v ∈ Heap.frontier n I}) → D

/-- The simulator's exact proof is just its sampled coordinates. -/
def simulateProof (n : ℕ) (I : Finset (Fin n))
    (coins : SimulatorCoins n I Salt D) : Opening n I Salt D where
  nonce := coins.nonce
  frontierValue := coins.frontierRoot

/-- The simulator derives the root by running the same deterministic
bottom-up recurrence as the verifier. -/
noncomputable def simulateRoot (n : ℕ) (I : Finset (Fin n))
    (a : Fin n → M) (coins : SimulatorCoins n I Salt D) : D :=
  checkValues S n I a (simulateProof n I coins) 1

/-- Every simulated nonempty opening verifies, for every oracle and every
choice of simulator coins. -/
theorem mh_simulated_opening_accepts (n : ℕ) (I : Finset (Fin n))
    (hI : I.Nonempty) (a : Fin n → M)
    (coins : SimulatorCoins n I Salt D) :
    Accepts S n
      (simulateRoot S n I a coins) I a
      (simulateProof n I coins) := by
  exact ⟨hI, rfl⟩

/-- The simulator depends only on the claims at `I`; total message functions
are merely an ergonomic representation of the dependent map `m[I]`. -/
theorem simulateRoot_congr_on_claims (n : ℕ) (I : Finset (Fin n))
    (a b : Fin n → M) (coins : SimulatorCoins n I Salt D)
    (hclaim : ∀ i, i ∈ I → a i = b i) :
    simulateRoot S n I a coins =
      simulateRoot S n I b coins := by
  exact checkValues_congr_on_claims S n I a b
    (simulateProof n I coins) hclaim 1

/-- Couple simulator coins to an honest commitment by using the honest opened
nonces and the actual roots of the frontier subtrees.  Lazy-sampling hybrids
replace these roots by independent uniform values; this definition is the
deterministic endpoint at which the two views agree. -/
noncomputable def coupledSimulatorCoins (n : ℕ) (I : Finset (Fin n))
    (nonce : Fin n → Salt) (m : Fin n → M) : SimulatorCoins n I Salt D where
  nonce i := nonce i.val
  frontierRoot v := commitLabels S n nonce m v.val

@[simp] theorem simulateProof_coupled (n : ℕ) (I : Finset (Fin n))
    (nonce : Fin n → Salt) (m : Fin n → M) :
    simulateProof n I (coupledSimulatorCoins S n I nonce m) =
      openCore S n I nonce m := by
  rfl

/-- At the coupled endpoint the simulator reconstructs exactly the honest
root. -/
theorem simulateRoot_coupled (n : ℕ) (I : Finset (Fin n))
    (hI : I.Nonempty) (nonce : Fin n → Salt) (m : Fin n → M) :
    simulateRoot S n I m
        (coupledSimulatorCoins S n I nonce m) =
      root S n nonce m := by
  exact (mh_core_completeness S n I hI nonce m).2

/-- The root together with the exact opening data is the view exposed by the
Merkle commitment/opening interface. -/
structure OpeningView (n : ℕ) (I : Finset (Fin n))
    (Salt : Type uSalt) (D : Type uDigest) where
  rt : D
  proof : Opening n I Salt D

/-- Honest commitment-and-opening view. -/
noncomputable def realOpeningView (n : ℕ) (I : Finset (Fin n))
    (nonce : Fin n → Salt) (m : Fin n → M) : OpeningView n I Salt D where
  rt := root S n nonce m
  proof := openCore S n I nonce m

/-- Simulator commitment-and-opening view. -/
noncomputable def simulatedOpeningView (n : ℕ) (I : Finset (Fin n))
    (m : Fin n → M) (coins : SimulatorCoins n I Salt D) :
    OpeningView n I Salt D where
  rt := simulateRoot S n I m coins
  proof := simulateProof n I coins

/-- The honest and simulator views coincide at the coupled endpoint. -/
theorem simulatedOpeningView_coupled (n : ℕ) (I : Finset (Fin n))
    (hI : I.Nonempty) (nonce : Fin n → Salt) (m : Fin n → M) :
    simulatedOpeningView S n I m
        (coupledSimulatorCoins S n I nonce m) =
      realOpeningView S n I nonce m := by
  unfold simulatedOpeningView realOpeningView
  rw [simulateRoot_coupled S n I hI nonce m,
    simulateProof_coupled S n I nonce m]

/-- The complete simulated opening view likewise ignores unopened message
coordinates. -/
theorem simulatedOpeningView_congr_on_claims (n : ℕ)
    (I : Finset (Fin n)) (a b : Fin n → M)
    (coins : SimulatorCoins n I Salt D)
    (hclaim : ∀ i, i ∈ I → a i = b i) :
    simulatedOpeningView S n I a coins =
      simulatedOpeningView S n I b coins := by
  unfold simulatedOpeningView
  rw [simulateRoot_congr_on_claims S n I a b coins hclaim]

/-! ## Basic salted-commitment counting -/

omit [Inhabited D] in
/-- For a fixed message, a fixed set of oracle guesses hits an injectively
encoded uniform salt on at most one salt per guess. -/
theorem salt_hit_card_le [Fintype Salt] [DecidableEq Salt]
    [Fintype Enc] [DecidableEq Enc]
    (C : Codec Salt M D Enc) (m : M)
    (hsalt : Function.Injective (fun s : Salt => C.leafEnc (s, m)))
    (guesses : Finset Enc) :
    (Finset.filter (fun s : Salt => C.leafEnc (s, m) ∈ guesses)
      Finset.univ).card ≤ guesses.card :=
  RandomOracle.injective_secret_hit_card_le
    (fun s : Salt => C.leafEnc (s, m)) hsalt guesses

omit [Inhabited D] in
/-- In particular, a list of at most `t` distinct guesses hits at most `t`
salts. -/
theorem salt_hit_card_le_queries [Fintype Salt] [DecidableEq Salt]
    [Fintype Enc] [DecidableEq Enc]
    (C : Codec Salt M D Enc) (m : M)
    (hsalt : Function.Injective (fun s : Salt => C.leafEnc (s, m)))
    (guesses : Finset Enc) (t : ℕ) (hcard : guesses.card ≤ t) :
    (Finset.filter (fun s : Salt => C.leafEnc (s, m) ∈ guesses)
      Finset.univ).card ≤ t :=
  (salt_hit_card_le C m hsalt guesses).trans hcard

/-! ## Tight frontier arithmetic -/

/-- Common-denominator numerator for the simplified basic hiding expression
`t/|Salt| + t²/|D|`: over denominator `|Salt|*|D|`, its numerator is
`t*|D| + t²*|Salt|`. -/
def basicHidingNumerator (saltCard digestCard t : ℕ) : ℕ :=
  t * digestCard + t ^ 2 * saltCard

/-- The sum of linear per-subtree hiding numerators is exactly the number of
unopened leaves times the basic numerator. -/
theorem frontier_hiding_numerator (n : ℕ) (I : Finset (Fin n))
    (hn : 0 < n) (hI : I.Nonempty)
    (saltCard digestCard t : ℕ) :
    ∑ v ∈ Heap.frontier n I,
        (Heap.subtreeLeaves n v).card *
          basicHidingNumerator saltCard digestCard t =
      (n - I.card) * basicHidingNumerator saltCard digestCard t := by
  rw [← Finset.sum_mul, Heap.frontier_leaf_sum n I hn hI]

/-- Event-bound assembly for the opening simulator: if each independent
frontier replacement costs at most its leaf count times the basic numerator,
their union-bound sum has the tight `(n-|I|)` coefficient. -/
theorem mh_opening_hiding_bound
    (n : ℕ) (I : Finset (Fin n)) (hn : 0 < n) (hI : I.Nonempty)
    (saltCard digestCard t : ℕ)
    (subtreeBad : ℕ → ℕ)
    (hsubtree : ∀ v ∈ Heap.frontier n I,
      subtreeBad v ≤ (Heap.subtreeLeaves n v).card *
        basicHidingNumerator saltCard digestCard t) :
    ∑ v ∈ Heap.frontier n I, subtreeBad v ≤
      (n - I.card) * basicHidingNumerator saltCard digestCard t := by
  calc
    ∑ v ∈ Heap.frontier n I, subtreeBad v ≤
        ∑ v ∈ Heap.frontier n I,
          (Heap.subtreeLeaves n v).card *
            basicHidingNumerator saltCard digestCard t := by
      exact Finset.sum_le_sum (fun v hv => hsubtree v hv)
    _ = _ := frontier_hiding_numerator n I hn hI saltCard digestCard t

/-- Root-hiding event assembly: `n` leaf replacements charged by
`t*|D|` and at most `n` internal replacements charged by `t²*|Salt|` give
`n` times the common basic numerator. -/
theorem mh_root_hiding_bound
    (n saltCard digestCard t : ℕ)
    (leafBad : Fin n → ℕ) (nodeBad : ℕ → ℕ)
    (hleaf : ∀ i, leafBad i ≤ t * digestCard)
    (hnode : ∀ v ∈ Heap.internals n, nodeBad v ≤ t ^ 2 * saltCard) :
    (∑ i : Fin n, leafBad i) +
        (∑ v ∈ Heap.internals n, nodeBad v) ≤
      n * basicHidingNumerator saltCard digestCard t := by
  have hleaves : (∑ i : Fin n, leafBad i) ≤ n * (t * digestCard) := by
    calc
      (∑ i : Fin n, leafBad i) ≤ ∑ _i : Fin n, t * digestCard := by
        exact Finset.sum_le_sum (fun i _ => hleaf i)
      _ = n * (t * digestCard) := by simp
  have hnodes : (∑ v ∈ Heap.internals n, nodeBad v) ≤
      n * (t ^ 2 * saltCard) := by
    calc
      (∑ v ∈ Heap.internals n, nodeBad v) ≤
          ∑ _v ∈ Heap.internals n, t ^ 2 * saltCard := by
        exact Finset.sum_le_sum (fun v hv => hnode v hv)
      _ = (Heap.internals n).card * (t ^ 2 * saltCard) := by simp
      _ ≤ n * (t ^ 2 * saltCard) := by
        apply Nat.mul_le_mul_right
        simp [Heap.internals]
  calc
    (∑ i : Fin n, leafBad i) + (∑ v ∈ Heap.internals n, nodeBad v)
        ≤ n * (t * digestCard) + n * (t ^ 2 * saltCard) :=
      Nat.add_le_add hleaves hnodes
    _ = n * basicHidingNumerator saltCard digestCard t := by
      simp [basicHidingNumerator, Nat.mul_add]

/-! ## Normalized real/sim ROM experiments -/

/-- A complete certified root-hiding experiment.  `Ω` contains every random
choice: the oracle, honest nonces, simulator coins, and distinguisher coins.
The leaf/node bad sets are the lazy-sampling failures.  Their normalized
bounds are precisely the basic salted-commitment and internal-input bounds;
`agrees` is the coupling invariant outside their union. -/
structure RootHidingGame (C : Codec Salt M D Enc) (Ω : Type*) (V : Type*)
    [Fintype Ω] [DecidableEq Ω]
    (n saltCard digestCard t : ℕ) where
  realOracle : Ω → Enc → D
  simulatedOracle : Ω → Enc → D
  nonce : Ω → Fin n → Salt
  message : Fin n → M
  simulatedRoot : Ω → D
  /-- The distinguisher's complete observed output.  It may execute a bounded
  adaptive oracle tree using the supplied oracle; its private coins are
  already a coordinate of `Ω`. -/
  observe : Ω → (Enc → D) → D → V
  leafBad : Fin n → Finset Ω
  nodeBad : ℕ → Finset Ω
  leaf_bound : ∀ i,
    (leafBad i).card * (saltCard * digestCard) ≤
      (t * digestCard) * Fintype.card Ω
  node_bound : ∀ v ∈ Heap.internals n,
    (nodeBad v).card * (saltCard * digestCard) ≤
      (t ^ 2 * saltCard) * Fintype.card Ω
  agrees : ∀ ω,
    ω ∉ (Finset.univ.biUnion leafBad) ∪
      ((Heap.internals n).biUnion nodeBad) →
    observe ω (realOracle ω)
        (root (C.withOracle (realOracle ω)) n (nonce ω) message) =
      observe ω (simulatedOracle ω) (simulatedRoot ω)

/-- Exact root-hiding theorem for the certified finite experiment:

`Δ(real root, simulated root) ≤ n * (t/|Salt| + t²/|D|)`.

The conclusion is cross-multiplied over the full sample space `Ω`. -/
theorem mh_root_hiding_rom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {V : Type*} [DecidableEq V]
    (C : Codec Salt M D Enc)
    (n saltCard digestCard t : ℕ)
    (game : RootHidingGame C Ω V n saltCard digestCard t) :
    RandomOracle.CountingCloseRatio
      (n * basicHidingNumerator saltCard digestCard t)
      (saltCard * digestCard)
      (fun ω => game.observe ω (game.realOracle ω)
        (root (C.withOracle (game.realOracle ω)) n
          (game.nonce ω) game.message))
      (fun ω => game.observe ω (game.simulatedOracle ω)
        (game.simulatedRoot ω)) := by
  let leafUnion : Finset Ω := Finset.univ.biUnion game.leafBad
  let nodeUnion : Finset Ω := (Heap.internals n).biUnion game.nodeBad
  let bad := leafUnion ∪ nodeUnion
  apply RandomOracle.CountingCloseRatio.of_bad
    (n * basicHidingNumerator saltCard digestCard t)
    (saltCard * digestCard) _ _ bad
  · have hleafUnion : leafUnion.card ≤
        ∑ i : Fin n, (game.leafBad i).card := by
      exact Finset.card_biUnion_le
    have hnodeUnion : nodeUnion.card ≤
        ∑ v ∈ Heap.internals n, (game.nodeBad v).card := by
      exact Finset.card_biUnion_le
    have hbad : bad.card ≤
        (∑ i : Fin n, (game.leafBad i).card) +
          (∑ v ∈ Heap.internals n, (game.nodeBad v).card) :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add hleafUnion hnodeUnion)
    have hscaled := mh_root_hiding_bound
      n (saltCard * Fintype.card Ω) (digestCard * Fintype.card Ω) t
      (fun i => (game.leafBad i).card * (saltCard * digestCard))
      (fun v => (game.nodeBad v).card * (saltCard * digestCard))
      (fun i => by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          game.leaf_bound i)
      (fun v hv => by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          game.node_bound v hv)
    calc
      bad.card * (saltCard * digestCard) ≤
          ((∑ i : Fin n, (game.leafBad i).card) +
            (∑ v ∈ Heap.internals n, (game.nodeBad v).card)) *
              (saltCard * digestCard) :=
        Nat.mul_le_mul_right _ hbad
      _ = (∑ i : Fin n,
            (game.leafBad i).card * (saltCard * digestCard)) +
          (∑ v ∈ Heap.internals n,
            (game.nodeBad v).card * (saltCard * digestCard)) := by
        simp only [Nat.add_mul, Finset.sum_mul]
      _ ≤ n * basicHidingNumerator
          (saltCard * Fintype.card Ω) (digestCard * Fintype.card Ω) t :=
        hscaled
      _ = (n * basicHidingNumerator saltCard digestCard t) *
          Fintype.card Ω := by
        simp [basicHidingNumerator]
        ring
  · intro ω hω
    exact game.agrees ω hω

/-- A complete certified opening-hiding experiment.  The simulator receives
only the opened claims (represented by the fixed `message`, whose unopened
coordinates are observationally unused) and its explicit coins. -/
structure OpeningHidingGame (C : Codec Salt M D Enc) (Ω : Type*) (V : Type*)
    [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (I : Finset (Fin n))
    (saltCard digestCard t : ℕ) where
  realOracle : Ω → Enc → D
  simulatedOracle : Ω → Enc → D
  nonce : Ω → Fin n → Salt
  message : Fin n → M
  simulatorCoins : (ω : Ω) → SimulatorCoins n I Salt D
  /-- Complete oracle-aware distinguisher view. -/
  observe : Ω → (Enc → D) → OpeningView n I Salt D → V
  subtreeBad : ℕ → Finset Ω
  subtree_bound : ∀ v ∈ Heap.frontier n I,
    (subtreeBad v).card * (saltCard * digestCard) ≤
      ((Heap.subtreeLeaves n v).card *
        basicHidingNumerator saltCard digestCard t) * Fintype.card Ω
  agrees : ∀ ω, ω ∉ (Heap.frontier n I).biUnion subtreeBad →
    observe ω (realOracle ω)
        (realOpeningView (C.withOracle (realOracle ω)) n I
          (nonce ω) message) =
      observe ω (simulatedOracle ω)
        (simulatedOpeningView (C.withOracle (simulatedOracle ω)) n I message
          (simulatorCoins ω))

/-- Exact real/sim opening-hiding theorem:

`Δ(real view, simulator view) ≤ (n-|I|) *
  (t/|Salt| + t²/|D|)`.

`frontier_leaf_sum` supplies the tight `n-|I|` coefficient. -/
theorem mh_opening_hiding_rom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {V : Type*} [DecidableEq V]
    (C : Codec Salt M D Enc)
    (n : ℕ) (I : Finset (Fin n)) (hn : 0 < n) (hI : I.Nonempty)
    (saltCard digestCard t : ℕ)
    (game : OpeningHidingGame C Ω V n I saltCard digestCard t) :
    RandomOracle.CountingCloseRatio
      ((n - I.card) * basicHidingNumerator saltCard digestCard t)
      (saltCard * digestCard)
      (fun ω => game.observe ω (game.realOracle ω)
        (realOpeningView (C.withOracle (game.realOracle ω)) n I
          (game.nonce ω) game.message))
      (fun ω => game.observe ω (game.simulatedOracle ω)
        (simulatedOpeningView (C.withOracle (game.simulatedOracle ω)) n I
          game.message (game.simulatorCoins ω))) := by
  let bad : Finset Ω := (Heap.frontier n I).biUnion game.subtreeBad
  apply RandomOracle.CountingCloseRatio.of_bad
    ((n - I.card) * basicHidingNumerator saltCard digestCard t)
    (saltCard * digestCard) _ _ bad
  · have hbad : bad.card ≤
        ∑ v ∈ Heap.frontier n I, (game.subtreeBad v).card := by
      exact Finset.card_biUnion_le
    have hscaled := mh_opening_hiding_bound n I hn hI
      (saltCard * Fintype.card Ω) (digestCard * Fintype.card Ω) t
      (fun v => (game.subtreeBad v).card * (saltCard * digestCard))
      (fun v hv => by
        calc
          (game.subtreeBad v).card * (saltCard * digestCard) ≤
              ((Heap.subtreeLeaves n v).card *
                basicHidingNumerator saltCard digestCard t) *
                  Fintype.card Ω := game.subtree_bound v hv
          _ = (Heap.subtreeLeaves n v).card *
              basicHidingNumerator
                (saltCard * Fintype.card Ω)
                (digestCard * Fintype.card Ω) t := by
            simp [basicHidingNumerator]
            ring)
    calc
      bad.card * (saltCard * digestCard) ≤
          (∑ v ∈ Heap.frontier n I, (game.subtreeBad v).card) *
            (saltCard * digestCard) := Nat.mul_le_mul_right _ hbad
      _ = ∑ v ∈ Heap.frontier n I,
          (game.subtreeBad v).card * (saltCard * digestCard) := by
        simp only [Finset.sum_mul]
      _ ≤ (n - I.card) * basicHidingNumerator
          (saltCard * Fintype.card Ω) (digestCard * Fintype.card Ω) t :=
        hscaled
      _ = ((n - I.card) * basicHidingNumerator
          saltCard digestCard t) * Fintype.card Ω := by
        simp [basicHidingNumerator]
        ring
  · intro ω hω
    exact game.agrees ω hω

end MH

end Merkle
