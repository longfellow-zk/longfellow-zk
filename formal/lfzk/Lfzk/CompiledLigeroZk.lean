import Lfzk.ZkMerkle
import Lfzk.FromLigeroZKV1
import Bcs.SchemeCompiler
import Lfzk.LigeroZk.V1ResponseAdaptive
import LigeroFamily.Protocol.FiniteResponse

/-!
# Zero knowledge of compiled Ligero, against a query-bounded distinguisher

`Lfzk.FromLigeroZK` proves Ligero's *oracle* protocol perfectly zero knowledge, and
`Lfzk.ZkMerkle` proves the Merkle commitment's opening view hiding.  Neither is a statement about
the deployed argument, in which the columns are Merkle-committed and both challenges are hashes:

```
c = H₁(root)              — decoded to the linear-combination challenge
i = H₂(root, c, response)  — decoded to the opened column set
```

This file is that statement, for a fixed true statement and witness ("version A": the
distinguisher queries the oracles only after seeing the proof).

Ported from `proofs/lfzk/Lfzk/CompiledLigeroZk.lean`: the generic part (`compiled_zk`,
`compiled_zk_bits256_q115`) and the V1 instance are verbatim; the V3 instance is dropped
(`formal/` carries no V3), `Bits256` is defined here rather than imported from
`Merkle.Instantiate` (not ported), and the V1 prover tape's `Nonempty` instance comes from
`Lfzk.FromLigeroZKV1`.  The Longfellow composition — the Ligero statement built *after* the
commitment from the sumcheck transcript — is `Lfzk.CompiledLongfellowZk`.

## The experiment

*Real.*  The honest IPCP prover commits; its columns are Merkle-committed with fresh nonces on a
lazily sampled oracle (`Merkle.MH.commitPass`, the commitment `Merkle.MH.openingHidingRun` runs);
the two challenges are the challenge oracle `G` at the two domain-separated points; the proof is
the root, the two raw challenges, the response, the query, the Merkle opening and the opened
columns.  The distinguisher then receives the proof, **the whole challenge oracle `G` as a
function**, and makes at most `f` further queries to the Merkle oracle.

*Simulated.*  Run the oracle-level simulator, which never sees the witness; Merkle-commit to its
opened columns and to `default` everywhere else; program `G` at the two points so that it agrees
with the simulated challenges.

## The bound

```
StatClose (openingEps |Salt| |D| n f T d |Ω|)  real  simulated
```

which is `(4n² + 2·d·f)/|Salt| + (2n−1)(2n−2)/|D|`, `d` bounding the number of unopened leaves.
At 32-byte salts and digests, `f = 2^115` and at most `2^13` leaves this is `≤ 2^-127`:
`v1_compiled_zk_bits256_q115`.
Three hybrids, and only the middle one costs anything:

| step | cost | why |
|---|---|---|
| program `G` at the two derived points | **0** | `progEquiv`: the root, the response and the points are fixed before `G` is read there, so programming is a relabelling of `G` |
| replace the unopened columns by `default` | `openingEps` | `ZkMerkle.openingHiding_statClose_of_agreeOnOpened`, at the fixed query |
| replace the response and opened columns by the simulator's | **0** | the oracle protocol's `SameDistribution` |

Challenge-oracle access is unbounded: the distinguisher gets `G` itself.  Only Merkle-oracle
queries are counted.

## Modelling premises

* The Merkle hash and the challenge hash are independent random oracles (domain separation).
* The statement and witness are fixed before the distinguisher makes any query.  An adversary that
  queries first and then chooses the statement is *not* covered (that is "version B").
* The decoders `dec₁ dec₂` are arbitrary: the oracle-level zero knowledge holds against every
  response-adaptive verifier, so no uniformity is needed.
* The simulator is the oracle-level one, which for V1 is not efficient (`referenceMessages` is
  chosen noncomputably), and the distinguisher is bounded by its Merkle queries.  The statement
  amounts to witness indistinguishability against query-bounded distinguishers, not zero
  knowledge with an efficient simulator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledLigeroZk

open Merkle Merkle.MH LigeroFamily LigeroFamily.ZeroKnowledge

/-! ## `StatClose` plumbing -/

section Plumbing

theorem statClose_of_probOf_eq {R S T : Type} [Fintype R] [Fintype S] {f : R → T} {g : S → T}
    (h : ∀ P, probOf f P = probOf g P) : StatClose 0 f g := by
  intro P
  rw [h P, sub_self, abs_zero]

/-- Reindexing the left sample space along a bijection changes nothing. -/
theorem statClose_comp_equiv_left {R R' S T : Type} [Fintype R] [Fintype R'] [Fintype S]
    {eps : ℚ} (f : R → T) (g : S → T) (e : R' ≃ R) :
    StatClose eps (fun r' => f (e r')) g ↔ StatClose eps f g := by
  constructor
  · intro h P
    rw [← probOf_equiv e f P]
    exact h P
  · intro h P
    rw [probOf_equiv e f P]
    exact h P

/-- Reindexing the right sample space along a bijection changes nothing. -/
theorem statClose_comp_equiv_right {R S S' T : Type} [Fintype R] [Fintype S] [Fintype S']
    {eps : ℚ} (f : R → T) (g : S → T) (e : S' ≃ S) :
    StatClose eps f (fun s' => g (e s')) ↔ StatClose eps f g := by
  constructor
  · intro h P
    rw [← probOf_equiv e g P]
    exact h P
  · intro h P
    rw [probOf_equiv e g P]
    exact h P

/-- Post-processing cannot increase the advantage. -/
theorem statClose_post {R S T U : Type} [Fintype R] [Fintype S] {eps : ℚ} {f : R → T}
    {g : S → T} (Ψ : T → U) (h : StatClose eps f g) :
    StatClose eps (fun r => Ψ (f r)) (fun s => Ψ (g s)) :=
  fun P => h (fun t => P (Ψ t))

/-- An unread independent coordinate does not change a probability. -/
theorem probOf_fst {A B T : Type} [Fintype A] [Fintype B] [Nonempty B] (g : A → T)
    (P : T → Prop) : probOf (fun x : A × B => g x.1) P = probOf g P := by
  rw [← probOf_equiv (Equiv.prodComm B A) (fun x : A × B => g x.1) P]
  have h := probOf_prod (fun (_ : B) (a : A) => g a) P
  simp only [Equiv.prodComm_apply, Prod.fst_swap] at h ⊢
  rw [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hB : (Fintype.card B : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := B)).ne'
  field_simp

end Plumbing

/-! ## Programming two adaptively chosen points is a relabelling

`p₁` is read first; `p₂` is a function of what was read there.  Replacing the oracle's values at
`p₁` and at `p₂ c` by fresh coins `c` and `i` gives a uniformly distributed oracle again, because
`(G₀, c, i) ↦ (prog G₀ c i, G₀ p₁, G₀ (p₂ c))` is a bijection.  So the programmed experiment and the
real one are *identically* distributed — the only cost of programming in the literature comes from
a distinguisher that has queried a programmed point beforehand, which this experiment does not
allow.
-/

section Programming

variable {Q Coin : Type} [DecidableEq Q]

/-- The oracle `G₀`, answering `c` at `p₁` and `i` at `p₂ c`. -/
def prog (p₁ : Q) (p₂ : Coin → Q) (G₀ : Q → Coin) (c i : Coin) : Q → Coin :=
  Function.update (Function.update G₀ p₁ c) (p₂ c) i

theorem prog_first {p₁ : Q} {p₂ : Coin → Q} (hne : ∀ c, p₂ c ≠ p₁) (G₀ : Q → Coin)
    (c i : Coin) : prog p₁ p₂ G₀ c i p₁ = c := by
  rw [prog, Function.update_of_ne (hne c).symm, Function.update_self]

theorem prog_second (p₁ : Q) (p₂ : Coin → Q) (G₀ : Q → Coin) (c i : Coin) :
    prog p₁ p₂ G₀ c i (p₂ c) = i := by
  rw [prog, Function.update_self]

/-- **Programming is a bijection on oracles-with-two-coins.** -/
def progEquiv (p₁ : Q) (p₂ : Coin → Q) (hne : ∀ c, p₂ c ≠ p₁) :
    (Q → Coin) × (Coin × Coin) ≃ (Q → Coin) × (Coin × Coin) where
  toFun x := (prog p₁ p₂ x.1 x.2.1 x.2.2, x.1 p₁, x.1 (p₂ x.2.1))
  invFun y := (Function.update (Function.update y.1 p₁ y.2.1) (p₂ (y.1 p₁)) y.2.2,
    y.1 p₁, y.1 (p₂ (y.1 p₁)))
  left_inv := by
    rintro ⟨G₀, c, i⟩
    have h1 : prog p₁ p₂ G₀ c i p₁ = c := prog_first hne G₀ c i
    simp only [h1, prog_second, Prod.mk.injEq, and_true]
    funext z
    by_cases hz2 : z = p₂ c
    · subst hz2
      simp
    · by_cases hz1 : z = p₁
      · subst hz1
        simp [Function.update_of_ne (hne c).symm]
      · simp [prog, Function.update_of_ne hz1, Function.update_of_ne hz2]
  right_inv := by
    rintro ⟨G, a, b⟩
    have hne' := (hne (G p₁)).symm
    have ha : Function.update (Function.update G p₁ a) (p₂ (G p₁)) b p₁ = a := by
      rw [Function.update_of_ne hne', Function.update_self]
    simp only [Prod.mk.injEq]
    refine ⟨?_, ha, by simp⟩
    funext z
    simp only [prog]
    by_cases hz2 : z = p₂ (G p₁)
    · subst hz2
      simp
    · by_cases hz1 : z = p₁
      · subst hz1
        simp [Function.update_of_ne hne']
      · simp [Function.update_of_ne hz1, Function.update_of_ne hz2]

@[simp] theorem progEquiv_apply_fst (p₁ : Q) (p₂ : Coin → Q) (hne : ∀ c, p₂ c ≠ p₁)
    (x : (Q → Coin) × (Coin × Coin)) :
    (progEquiv p₁ p₂ hne x).1 = prog p₁ p₂ x.1 x.2.1 x.2.2 := rfl

/--
**Programming is free.**  For every view `Φ` of a uniformly random oracle, programming it at `p₁`
and at `p₂ c` with fresh coins leaves the view's distribution unchanged.
-/
theorem statClose_prog [Fintype Q] [Fintype Coin] [Nonempty Coin] {V : Type}
    (p₁ : Q) (p₂ : Coin → Q) (hne : ∀ c, p₂ c ≠ p₁) (Φ : (Q → Coin) → V) :
    StatClose 0 Φ (fun x : (Q → Coin) × (Coin × Coin) => Φ (prog p₁ p₂ x.1 x.2.1 x.2.2)) := by
  refine statClose_of_probOf_eq fun P => ?_
  have h1 := probOf_equiv (progEquiv p₁ p₂ hne) (fun y : (Q → Coin) × (Coin × Coin) => Φ y.1) P
  simp only [progEquiv_apply_fst] at h1
  rw [h1, probOf_fst]

end Programming

/-! ## The compiled experiment -/

/-- The two domain-separated challenge-oracle inputs, `H₁(root)` and `H₂(root, c, response)`.  The
same shape as `Bcs.LigeroFSQuery`; restated here so this file does not depend on the staged
soundness files that define it. -/
inductive FSQuery (D Coin Response : Type) where
  | first (root : D)
  | second (root : D) (rawFirst : Coin) (response : Response)
  deriving DecidableEq, Fintype

/-- The challenge oracle. -/
abbrev ChalOracle (D Coin Response : Type) := FSQuery D Coin Response → Coin

/-- What the distinguisher receives: the root, the two raw challenges (which a verifier recomputes
from the oracle anyway), the response, the query, the Merkle opening and the opened columns. -/
structure CompiledProof (n : ℕ) (Salt D Coin Response Query : Type) (POpen : Query → Type)
    (I : Query → Finset (Fin n)) where
  root : D
  rawChallenge : Coin
  response : Response
  rawQuery : Coin
  query : Query
  merkleOpening : Merkle.MH.Opening n (I query) Salt D
  opening : POpen query

/-- The response-adaptive verifier the Fiat–Shamir transform realises: both challenges are decoded
oracle answers, and the query ignores the response because the response is already *in* the
second oracle input. -/
def fsVerifier {Coin Challenge Response Query : Type} (dec₁ : Coin → Challenge)
    (dec₂ : Coin → Query) : ResponseAdaptiveVerifier (Coin × Coin) Challenge Response Query where
  challenge vc := dec₁ vc.1
  query vc _ := dec₂ vc.2

theorem second_ne_first {D Coin Response : Type} (root root' : D) (c : Coin) (resp : Response) :
    (FSQuery.second root c resp : FSQuery D Coin Response) ≠ .first root' := by
  intro h
  cases h

section Experiment

variable {Statement Oracle Challenge Response Query : Type} {POpen : Query → Type}
variable {M : Type} {n : ℕ} {Wit ProverCoins SimCoins : Type}
variable {Salt D Enc Coin V : Type}
variable [DecidableEq D] [DecidableEq Coin] [DecidableEq Response] [Inhabited D] [DecidableEq Enc]

/-- A distinguisher: given the proof and the **whole** challenge oracle, it makes at most `f`
queries to the Merkle oracle. -/
abbrev Distinguisher (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (Salt D Enc Coin V : Type) (f : ℕ) :=
  CompiledProof n Salt D Coin Response Query POpen K.indices → ChalOracle D Coin Response →
    RandomOracle.Tree Enc D V f

/-- After the commitment: the proof at raw challenges `c` and `i`, handed to the distinguisher.
`c` and `i` are arguments rather than `let`s so that the programming step can rewrite them. -/
def realCont (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (dec₁ : Coin → Challenge) (dec₂ : Coin → Query)
    (prover : IPCPProver Statement Oracle Challenge Response) (s : Statement) {f : ℕ}
    (dist : Distinguisher K Salt D Enc Coin V f) (nonce : Fin n → Salt)
    (G : ChalOracle D Coin Response) (vals : ℕ → D) (c i : Coin) :
    RandomOracle.Tree Enc D V f :=
  dist ⟨vals 1, c, prover.respond s (prover.commit s) (dec₁ c), i, dec₂ i,
      { nonce := fun j => nonce j.val, frontierValue := fun v => vals v.val },
      K.protocol.openOracle (prover.commit s) (dec₂ i)⟩ G

/--
**The honest compiled prover, followed by the distinguisher.**

Merkle-commit to the prover's columns (`commitPass`, exactly the commitment
`Merkle.MH.openingHidingRun` runs); read `c := G(first root)`; respond to `dec₁ c`; read
`i := G(second root c response)`; open the columns at `dec₂ i`.
-/
def realRun (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (C : Codec Salt M D Enc) (dec₁ : Coin → Challenge) (dec₂ : Coin → Query)
    (prover : IPCPProver Statement Oracle Challenge Response) (s : Statement) {f : ℕ}
    (dist : Distinguisher K Salt D Enc Coin V f) (nonce : Fin n → Salt)
    (G : ChalOracle D Coin Response) : RandomOracle.Tree Enc D V (f + (2 * n - 1)) :=
  (commitPass C n nonce (K.columns (prover.commit s)) (2 * n - 1) fun _ => default).bind
    fun vals =>
      realCont K dec₁ dec₂ prover s dist nonce G vals (G (.first (vals 1)))
        (G (.second (vals 1) (G (.first (vals 1)))
          (prover.respond s (prover.commit s) (dec₁ (G (.first (vals 1)))))))

/-- **The real experiment.**  Coins: the prover's, the leaf nonces and the Merkle oracle's lazy
tape, and the challenge oracle. -/
noncomputable def realExp (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (C : Codec Salt M D Enc) (dec₁ : Coin → Challenge) (dec₂ : Coin → Query)
    (honestProver : Statement → Wit → ProverCoins →
      IPCPProver Statement Oracle Challenge Response)
    (s : Statement) (w : Wit) {T f : ℕ} (dist : Distinguisher K Salt D Enc Coin V f) :
    ProverCoins × HidingSample n T Salt D × ChalOracle D Coin Response → V :=
  fun ω => (RandomOracle.lazyRun ω.2.1.2 default
    (realRun K C dec₁ dec₂ (honestProver s w ω.1) s dist ω.2.1.1 ω.2.2) []).1

/-- The challenge oracle `G₀`, programmed at both derived points. -/
def progAt (G₀ : ChalOracle D Coin Response) (root : D) (c : Coin) (resp : Response) (i : Coin) :
    ChalOracle D Coin Response :=
  Function.update (Function.update G₀ (.first root) c) (.second root c resp) i

/-- The proof read off an oracle-level view and a Merkle opening view. -/
def proofOf (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (view : ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen)
    (ov : OpeningView n (K.indices view.query) Salt D) :
    CompiledProof n Salt D Coin Response Query POpen K.indices :=
  ⟨ov.rt, view.verifierCoins.1, view.response, view.verifierCoins.2, view.query, ov.proof,
    view.opening⟩

/-- Merkle-commit to `m`, then hand the distinguisher the proof read off `view`, with the challenge
oracle programmed to agree with `view`'s challenges. -/
noncomputable def viewExp (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (C : Codec Salt M D Enc) {T f : ℕ} (dist : Distinguisher K Salt D Enc Coin V f)
    (view : ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen)
    (m : Fin n → M) (G₀ : ChalOracle D Coin Response) (ω : HidingSample n T Salt D) : V :=
  openingHidingView C n (K.indices view.query) (fun _ => m)
    (fun _ ov => dist (proofOf K view ov)
      (progAt G₀ ov.rt view.verifierCoins.1 view.response view.verifierCoins.2)) ω

/-- The leaves a simulator commits to: the opened columns where opened, `default` elsewhere. -/
def leavesOf [Inhabited M] (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (openedLeaf : (q : Query) → POpen q → (i : Fin n) → i ∈ K.indices q → M)
    (view : ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen) :
    Fin n → M :=
  fun i => if h : i ∈ K.indices view.query then openedLeaf view.query view.opening i h
    else default

/-- **The simulated experiment.**  It never sees a witness: the oracle-level simulator, a
commitment to its opened columns and `default` elsewhere, and the challenge oracle programmed to
agree. -/
noncomputable def simExp [Inhabited M]
    (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (C : Codec Salt M D Enc)
    (openedLeaf : (q : Query) → POpen q → (i : Fin n) → i ∈ K.indices q → M)
    (simulator : Statement → SimCoins →
      ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen)
    (s : Statement) {T f : ℕ} (dist : Distinguisher K Salt D Enc Coin V f) :
    SimCoins × HidingSample n T Salt D × ChalOracle D Coin Response → V :=
  fun ω => viewExp K C dist (simulator s ω.1) (leavesOf K openedLeaf (simulator s ω.1)) ω.2.2 ω.2.1

/-- The honest oracle-level view at prover coins and the two raw challenges. -/
def realView (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (dec₁ : Coin → Challenge) (dec₂ : Coin → Query)
    (honestProver : Statement → Wit → ProverCoins →
      IPCPProver Statement Oracle Challenge Response)
    (s : Statement) (w : Wit) (x : ProverCoins × (Coin × Coin)) :
    ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen :=
  randomizedResponseAdaptiveView K.protocol honestProver s w (fsVerifier dec₁ dec₂) x

/-- The root the honest commitment produces at nonces `hs.1` and tape `hs.2`. -/
noncomputable def commitRoot (C : Codec Salt M D Enc) (m : Fin n → M) {T : ℕ}
    (hs : HidingSample n T Salt D) : D :=
  (RandomOracle.lazyRun hs.2 default (commitPass C n hs.1 m (2 * n - 1) fun _ => default) []).1 1

/-- The honest response to the raw challenge `c`. -/
def respOf (dec₁ : Coin → Challenge) (prover : IPCPProver Statement Oracle Challenge Response)
    (s : Statement) (c : Coin) : Response :=
  prover.respond s (prover.commit s) (dec₁ c)

/--
**The programming identity.**  The real experiment, run on the oracle `G₀` programmed at the two
points the honest prover will read, *is* the hybrid that commits to the real columns and reads its
challenges off the oracle-level view at `(c, i)`.
-/
theorem realExp_prog (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (C : Codec Salt M D Enc) (dec₁ : Coin → Challenge) (dec₂ : Coin → Query)
    (honestProver : Statement → Wit → ProverCoins →
      IPCPProver Statement Oracle Challenge Response)
    (s : Statement) (w : Wit) {T f : ℕ} (dist : Distinguisher K Salt D Enc Coin V f)
    (ρ : ProverCoins) (hs : HidingSample n T Salt D) (G₀ : ChalOracle D Coin Response)
    (c i : Coin) :
    realExp K C dec₁ dec₂ honestProver s w dist
        (ρ, hs, prog
          (FSQuery.first (commitRoot C (K.columns ((honestProver s w ρ).commit s)) hs))
          (fun c' => FSQuery.second
            (commitRoot C (K.columns ((honestProver s w ρ).commit s)) hs) c'
            (respOf dec₁ (honestProver s w ρ) s c'))
          G₀ c i)
      = viewExp K C dist (realView K dec₁ dec₂ honestProver s w (ρ, (c, i)))
          (K.columns ((honestProver s w ρ).commit s)) G₀ hs := by
  simp only [realExp, realRun, viewExp, openingHidingView, openingHidingRun, commitRoot,
    respOf]
  rw [RandomOracle.lazyRun_bind, RandomOracle.lazyRun_bind]
  rw [prog_first (fun c' => second_ne_first _ _ _ _), prog_second]
  rfl

end Experiment

/-! ## The bound -/

section Bound

theorem openingEps_nonneg (a b n f T d Ω : ℕ) : 0 ≤ ZkMerkle.openingEps a b n f T d Ω :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem openingEps_mono {a b n f T d d' Ω : ℕ} (h : d ≤ d') :
    ZkMerkle.openingEps a b n f T d Ω ≤ ZkMerkle.openingEps a b n f T d' Ω := by
  have hnum : openingHidingNumerator a b n f T d ≤ openingHidingNumerator a b n f T d' := by
    unfold openingHidingNumerator
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
  unfold ZkMerkle.openingEps
  exact div_le_div_of_nonneg_right (by exact_mod_cast hnum) (Nat.cast_nonneg _)

variable {Statement Oracle Challenge Response Query : Type} {POpen : Query → Type}
variable {M : Type} {n : ℕ} {Wit ProverCoins SimCoins : Type}
variable {Salt D Enc Coin V : Type}
variable [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D] [Inhabited D]
variable [DecidableEq Enc] [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
variable [Fintype Response] [DecidableEq Response] [DecidableEq V] [Inhabited M]
variable [Fintype ProverCoins] [Nonempty ProverCoins] [Fintype SimCoins] [Nonempty SimCoins]
variable [DecidableEq (ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen)]

/-- Sample-space bookkeeping between the hybrids. -/
def e12 (P H G X : Type) : (P × H) × (G × X) ≃ ((P × X) × G) × H where
  toFun x := (((x.1.1, x.2.2), x.2.1), x.1.2)
  invFun y := ((y.1.1.1, y.2), (y.1.2, y.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Sample-space bookkeeping between the hybrids. -/
def e23 (P H G X : Type) : ((P × X) × G) × H ≃ (H × G) × (P × X) where
  toFun y := ((y.2, y.1.2), y.1.1)
  invFun z := ((z.2, z.1.2), z.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/--
**Zero knowledge of the compiled argument, against an `f`-query distinguisher.**

For every true statement and witness, and every distinguisher that receives the compiled proof
and the whole challenge oracle and makes at most `f` Merkle-oracle queries, the real experiment and
the simulated one are `openingEps`-close.

Inputs, and what each one is:

* `hleaf` — the opening *is* the opened columns.  For the Ligero family this is `rfl`.
* `hzk` — the oracle protocol's perfect response-adaptive zero knowledge, against the verifier
  that decodes the two oracle answers.  For V1 this is
  `Ligero.V1.ZeroKnowledge.v1_unbounded_perfect_response_adaptive_zero_knowledge`.
* `hinjC` — same-role injectivity of the Merkle codec.
* `hd` — at most `d` leaves are unopened by any query.
* `hT` — the lazy tape covers the commitment and every distinguisher query, so the Merkle oracle
  is genuinely uniform throughout.
-/
theorem compiled_zk (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (C : Codec Salt M D Enc) (dec₁ : Coin → Challenge) (dec₂ : Coin → Query)
    (honestProver : Statement → Wit → ProverCoins →
      IPCPProver Statement Oracle Challenge Response)
    (relation : Statement → Wit → Prop)
    (simulator : Statement → SimCoins →
      ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen)
    (openedLeaf : (q : Query) → POpen q → (i : Fin n) → i ∈ K.indices q → M)
    (hleaf : ∀ (oracle : Oracle) (q : Query) (i : Fin n) (hi : i ∈ K.indices q),
      openedLeaf q (K.protocol.openOracle oracle q) i hi = K.columns oracle i)
    (hzk : UnboundedPerfectResponseAdaptiveZeroKnowledgeAgainst K.protocol relation honestProver
      (fsVerifier dec₁ dec₂) simulator)
    (hinjC : C.Inj) (d : ℕ) (hd : ∀ q : Query, (Finset.univ \ K.indices q).card ≤ d)
    (hn : 0 < n) (s : Statement) (w : Wit) (hrel : relation s w)
    {T f : ℕ} (hT : 2 * n - 1 + f ≤ T) (dist : Distinguisher K Salt D Enc Coin V f) :
    StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n f T d
        (Fintype.card (HidingSample n T Salt D)))
      (realExp (T := T) K C dec₁ dec₂ honestProver s w dist)
      (simExp (T := T) K C openedLeaf simulator s dist) := by
  classical
  have hT₁ : 2 * n - 2 < T := by omega
  have hT₂ : 2 * n - 1 ≤ T := by omega
  -- the oracle-level view, and the columns the honest prover commits to
  let rv := realView K dec₁ dec₂ honestProver s w
  let cols : ProverCoins → Fin n → M := fun ρ => K.columns ((honestProver s w ρ).commit s)
  let H1 : ((ProverCoins × (Coin × Coin)) × ChalOracle D Coin Response) ×
      HidingSample n T Salt D → V :=
    fun y => viewExp K C dist (rv y.1.1) (cols y.1.1.1) y.1.2 y.2
  let H2 : ((ProverCoins × (Coin × Coin)) × ChalOracle D Coin Response) ×
      HidingSample n T Salt D → V :=
    fun y => viewExp K C dist (rv y.1.1) (leavesOf K openedLeaf (rv y.1.1)) y.1.2 y.2
  let eA := Equiv.prodAssoc ProverCoins (HidingSample n T Salt D) (ChalOracle D Coin Response)
  let eB := e12 ProverCoins (HidingSample n T Salt D) (ChalOracle D Coin Response) (Coin × Coin)
  let real := realExp (T := T) K C dec₁ dec₂ honestProver s w dist
  -- Step 1: programming the challenge oracle is free
  have s1 : StatClose 0 real H1 := by
    have hm : StatClose 0
        (fun p : (ProverCoins × HidingSample n T Salt D) × ChalOracle D Coin Response =>
          real (eA (p.1, p.2)))
        (fun q : (ProverCoins × HidingSample n T Salt D) ×
            (ChalOracle D Coin Response × (Coin × Coin)) => H1 (eB (q.1, q.2))) := by
      refine statClose_mix (R₁ := ProverCoins × HidingSample n T Salt D)
        (R₂ := ChalOracle D Coin Response) (S₂ := ChalOracle D Coin Response × (Coin × Coin))
        le_rfl (fun r G => real (eA (r, G))) (fun r x => H1 (eB (r, x))) ?_
      intro r
      have hΦ : (fun G : ChalOracle D Coin Response => real (eA (r, G)))
          = fun G => real (r.1, r.2, G) := rfl
      have hH : (fun x : ChalOracle D Coin Response × (Coin × Coin) => H1 (eB (r, x)))
          = fun x => real (r.1, r.2, prog
              (FSQuery.first (commitRoot C (cols r.1) r.2))
              (fun c' => FSQuery.second (commitRoot C (cols r.1) r.2) c'
                (respOf dec₁ (honestProver s w r.1) s c'))
              x.1 x.2.1 x.2.2) :=
        funext fun x =>
          (realExp_prog K C dec₁ dec₂ honestProver s w dist r.1 r.2 x.1 x.2.1 x.2.2).symm
      rw [hΦ, hH]
      exact statClose_prog
        (FSQuery.first (commitRoot C (cols r.1) r.2))
        (fun c' => FSQuery.second (commitRoot C (cols r.1) r.2) c'
          (respOf dec₁ (honestProver s w r.1) s c'))
        (fun c' => second_ne_first _ _ _ _)
        (fun G => real (r.1, r.2, G))
    have hm' : StatClose 0 (fun p => real (eA p)) (fun q => H1 (eB q)) := hm
    exact (statClose_comp_equiv_right real H1 eB).mp
      ((statClose_comp_equiv_left real (fun q => H1 (eB q)) eA).mp hm')
  -- Step 2: the unopened columns are hidden by the Merkle commitment
  have s2 : StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n f T d
        (Fintype.card (HidingSample n T Salt D))) H1 H2 := by
    have hm := statClose_mix
      (R₁ := (ProverCoins × (Coin × Coin)) × ChalOracle D Coin Response)
      (R₂ := HidingSample n T Salt D) (S₂ := HidingSample n T Salt D)
      (openingEps_nonneg _ _ _ _ _ _ _)
      (fun r ω => viewExp K C dist (rv r.1) (cols r.1.1) r.2 ω)
      (fun r ω => viewExp K C dist (rv r.1) (leavesOf K openedLeaf (rv r.1)) r.2 ω)
      (fun r => by
        have hagree : ∀ (tape : Fin T → D) (j : Fin n), j ∈ K.indices (rv r.1).query →
            (fun _ => cols r.1.1) tape j = (fun _ => leavesOf K openedLeaf (rv r.1)) tape j := by
          intro tape j hj
          simp only [leavesOf, dif_pos hj]
          exact (hleaf ((honestProver s w r.1.1).commit s) _ j hj).symm
        have hsalt : ∀ (m : (Fin T → D) → Fin n → M) (tape : Fin T → D) (j : Fin n),
            Function.Injective fun salt : Salt => C.leafEnc (salt, m tape j) :=
          fun m tape j a b hab => congrArg Prod.fst (hinjC.leaf hab)
        have h := ZkMerkle.openingHiding_statClose_of_agreeOnOpened C n hn
          (K.indices (rv r.1).query) T (fun _ => cols r.1.1)
          (fun _ => leavesOf K openedLeaf (rv r.1))
          (fun _ ov => dist (proofOf K (rv r.1) ov)
            (progAt r.2 ov.rt (rv r.1).verifierCoins.1 (rv r.1).response
              (rv r.1).verifierCoins.2))
          hT₁ hT₂ hinjC hagree (hsalt _) (hsalt _)
        exact h.mono (openingEps_mono (hd _)))
    exact hm
  -- Step 3: the oracle-level view is the simulator's, exactly
  have s3 : StatClose 0 H2 (simExp (T := T) K C openedLeaf simulator s dist) := by
    let Ψ : (HidingSample n T Salt D × ChalOracle D Coin Response) →
        ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen → V :=
      fun z view => viewExp K C dist view (leavesOf K openedLeaf view) z.2 z.1
    have h0 : StatClose 0 rv (simulator s) :=
      FromLigeroZK.statClose_zero_of_sameDistribution (hzk s w hrel)
    have hmix := statClose_mix
      (R₁ := HidingSample n T Salt D × ChalOracle D Coin Response)
      (R₂ := ProverCoins × (Coin × Coin)) (S₂ := SimCoins) le_rfl
      (fun z x => Ψ z (rv x)) (fun z σ => Ψ z (simulator s σ))
      (fun z => statClose_post (Ψ z) h0)
    have ha := (statClose_comp_equiv_left _ _
      (e23 ProverCoins (HidingSample n T Salt D) (ChalOracle D Coin Response)
        (Coin × Coin))).mpr hmix
    have hb := (statClose_comp_equiv_right _ _
      (Equiv.prodComm SimCoins (HidingSample n T Salt D × ChalOracle D Coin Response))).mpr ha
    exact hb
  have h := s1.trans (s2.trans s3)
  rw [zero_add, add_zero] at h
  exact h

end Bound

/-! ## At 256-bit salts and digests, `2^115` queries -/

section Numeral

/-- 32 bytes: the deployed nonce (`MerkleNonce::kLength = kSHA256DigestSize`) and digest
(SHA-256) type.  Same definition as `Merkle.MH.Bits256` in `proofs/merkle/Merkle/Instantiate.lean`,
which is not ported. -/
abbrev Bits256 := Fin 32 → Fin 256

@[simp] theorem card_Bits256 : Fintype.card Bits256 = 2 ^ 256 := by
  simp [Bits256]

/-- The arithmetic: `2^127 · numerator ≤ |Ω|`, at `|Salt| = |D| = 2^256`, `f = 2^115`, at most
`2^13` leaves and at most `n - 1` of them unopened. -/
theorem numerator_le (n d T : ℕ) (hn : 0 < n) (hn' : n ≤ 2 ^ 13) (hd : d ≤ n - 1)
    (hT : 0 < T) :
    2 ^ 127 * openingHidingNumerator (2 ^ 256) (2 ^ 256) n (2 ^ 115) T d
      ≤ (2 ^ 256) ^ n * (2 ^ 256) ^ T := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  set S : ℕ := 2 ^ 256 with hS
  set C : ℕ := (2 * (k + 1) - 1) * (2 * (k + 1) - 2) / 2 with hC
  set X : ℕ := 4 * (k + 1) ^ 2 + 2 * C + d * 2 ^ 116 with hXdef
  have hfac : openingHidingNumerator S S (k + 1) (2 ^ 115) (t + 1) d
      = (S ^ k * S ^ t * S) * X := by
    rw [openingHidingNumerator, hXdef, hC]
    simp only [Nat.add_sub_cancel]
    ring
  have hrhs : S ^ (k + 1) * S ^ (t + 1) = (S ^ k * S ^ t * S) * S := by ring
  have hsq : (k + 1) ^ 2 ≤ (2 ^ 13) ^ 2 := Nat.pow_le_pow_left hn' 2
  have hC' : C ≤ 16383 * 16382 := by
    refine le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul ?_ ?_) <;> omega
  have hd' : d ≤ 8191 := by omega
  have hX : X ≤ 2 ^ 129 := by
    have h1 : 4 * (k + 1) ^ 2 ≤ 4 * (2 ^ 13) ^ 2 := Nat.mul_le_mul_left 4 hsq
    have h2 : 2 * C ≤ 2 * (16383 * 16382) := Nat.mul_le_mul_left 2 hC'
    have h3 : d * 2 ^ 116 ≤ 8191 * 2 ^ 116 := Nat.mul_le_mul_right _ hd'
    have hsum : 4 * (2 ^ 13) ^ 2 + 2 * (16383 * 16382) + 8191 * 2 ^ 116 ≤ 2 ^ 129 := by
      norm_num
    rw [hXdef]
    omega
  have hinner : 2 ^ 127 * X ≤ S := by
    rw [hS]
    calc 2 ^ 127 * X ≤ 2 ^ 127 * 2 ^ 129 := Nat.mul_le_mul_left _ hX
      _ = 2 ^ 256 := by norm_num
  rw [hfac, hrhs]
  calc 2 ^ 127 * ((S ^ k * S ^ t * S) * X)
      = (S ^ k * S ^ t * S) * (2 ^ 127 * X) := by ring
    _ ≤ (S ^ k * S ^ t * S) * S := Nat.mul_le_mul_left _ hinner

/-- The fraction form. -/
theorem openingEps_le (n d T : ℕ) (hn : 0 < n) (hn' : n ≤ 2 ^ 13) (hd : d ≤ n - 1)
    (hT : 0 < T) :
    ZkMerkle.openingEps (2 ^ 256) (2 ^ 256) n (2 ^ 115) T d
        (Fintype.card (HidingSample n T Bits256 Bits256)) ≤ 1 / 2 ^ 127 := by
  have hcard : Fintype.card (HidingSample n T Bits256 Bits256)
      = (2 ^ 256) ^ n * (2 ^ 256) ^ T := by
    simp [HidingSample, Fintype.card_prod]
  rw [ZkMerkle.openingEps, hcard]
  have hpos : (0 : ℚ) < ((2 ^ 256) ^ n * (2 ^ 256) ^ T : ℕ) := by positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  have h := numerator_le n d T hn hn' hd hT
  have h' : ((openingHidingNumerator (2 ^ 256) (2 ^ 256) n (2 ^ 115) T d : ℕ) : ℚ) * 2 ^ 127
      ≤ (((2 ^ 256) ^ n * (2 ^ 256) ^ T : ℕ) : ℚ) := by
    rw [mul_comm]
    exact_mod_cast h
  simpa using h'

variable {Statement Oracle Challenge Response Query : Type} {POpen : Query → Type}
variable {M : Type} {n : ℕ} {Wit ProverCoins SimCoins : Type}
variable {Enc Coin V : Type}
variable [DecidableEq Enc] [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
variable [Fintype Response] [DecidableEq Response] [DecidableEq V] [Inhabited M]
variable [Fintype ProverCoins] [Nonempty ProverCoins] [Fintype SimCoins] [Nonempty SimCoins]
variable [DecidableEq (ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen)]

omit [Fintype Response] [DecidableEq Response] [Inhabited M] in
/-- Every query opens at least one leaf, so at most `n - 1` are unopened. -/
theorem unopened_card_le (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (q : Query) : (Finset.univ \ K.indices q).card ≤ n - 1 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have := (K.indices_nonempty q).card_pos
  omega

/--
**Compiled zero knowledge at 256-bit salts and digests: `≤ 2^-127` against `2^115` queries.**

`compiled_zk` at `Salt = D = Bits256`, `f = 2^115` and at most `2^13` leaves.  The codec is any
same-role-injective one; the challenge decoders are arbitrary.
-/
theorem compiled_zk_bits256_q115
    (K : Bcs.Compiler Statement Oracle Challenge Response Query POpen M n)
    (C : Codec Bits256 M Bits256 Enc) (dec₁ : Coin → Challenge) (dec₂ : Coin → Query)
    (honestProver : Statement → Wit → ProverCoins →
      IPCPProver Statement Oracle Challenge Response)
    (relation : Statement → Wit → Prop)
    (simulator : Statement → SimCoins →
      ResponseAdaptiveVerifierView (Coin × Coin) Challenge Response Query POpen)
    (openedLeaf : (q : Query) → POpen q → (i : Fin n) → i ∈ K.indices q → M)
    (hleaf : ∀ (oracle : Oracle) (q : Query) (i : Fin n) (hi : i ∈ K.indices q),
      openedLeaf q (K.protocol.openOracle oracle q) i hi = K.columns oracle i)
    (hzk : UnboundedPerfectResponseAdaptiveZeroKnowledgeAgainst K.protocol relation honestProver
      (fsVerifier dec₁ dec₂) simulator)
    (hinjC : C.Inj) (hn' : n ≤ 2 ^ 13) (s : Statement) (w : Wit) (hrel : relation s w)
    {T : ℕ} (hT : 2 * n - 1 + 2 ^ 115 ≤ T)
    (dist : Distinguisher K Bits256 Bits256 Enc Coin V (2 ^ 115)) :
    StatClose (1 / 2 ^ 127)
      (realExp (T := T) K C dec₁ dec₂ honestProver s w dist)
      (simExp (T := T) K C openedLeaf simulator s dist) := by
  have hn : 0 < n := by
    obtain ⟨i, _⟩ := K.indices_nonempty (dec₂ (Classical.arbitrary Coin))
    exact i.pos
  have h := compiled_zk K C dec₁ dec₂ honestProver relation simulator openedLeaf hleaf hzk hinjC
    (n - 1) (unopened_card_le K) hn s w hrel hT dist
  rw [card_Bits256] at h
  exact h.mono (openingEps_le n (n - 1) T hn hn' le_rfl (by omega))

end Numeral

/-! ## Ligero V1 -/

section V1

open Ligero.V1.ZeroKnowledge

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq repetitions : ℕ}
variable {Enc Coin V : Type} [DecidableEq Enc] [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
variable [DecidableEq V]

noncomputable local instance v1ViewDecidableEq :
    DecidableEq (ResponseAdaptiveVerifierView (Coin × Coin)
      (Ligero.V1.Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r) (Ligero.V1.Opening F nw nq repetitions n r)) :=
  Classical.decEq _

/-- **The V1 compiler**: `Bcs.schemeVerifierCompiler` at V1's mask scheme.  A leaf is a committed
column; the opened set is the drawn query set. -/
noncomputable def v1Compiler (C : MultiplicativeCode F r w n) (hr : 0 < r) :=
  Bcs.schemeVerifierCompiler (Equations := Equations) (nw := nw) (nq := nq)
    (repetitions := repetitions) C Ligero.V1.scheme hr

/-- V1's opening *is* the opened columns. -/
def v1OpenedLeaf (C : MultiplicativeCode F r w n) (hr : 0 < r) :
    (query : QuerySet n r) → Ligero.V1.Opening F nw nq repetitions n r query →
      (i : Fin n) → i ∈ (v1Compiler (Equations := Equations) (nw := nw) (nq := nq)
        (repetitions := repetitions) C hr).indices query →
      SchemeColumn F NoMask Ligero.V1.Mask nw nq repetitions :=
  fun _ opening i hi => opening ⟨i, hi⟩

omit [DecidableEq Equations] in
/--
**Ligero V1, Merkle-compiled with Fiat–Shamir: zero knowledge `≤ 2^-127` against `2^115` queries.**

The honest V1 prover (`Ligero.V1.ZeroKnowledge.v1HonestProver`), at any number of repetitions,
committed with 32-byte salts and 32-byte digests under any same-role-injective codec, with
challenges `dec₁ (H₁ root)` and `dec₂ (H₂ root c response)`, on a tree of at most `2^13` leaves.  For
every satisfied statement and every distinguisher that receives the proof and the whole challenge
oracle and makes at most `2^115` Merkle-oracle queries, the real experiment is `2^-127`-close to the
simulation, which runs V1's own response-adaptive simulator and never sees the witness.
-/
theorem v1_compiled_zk_bits256_q115
    (C : MultiplicativeCode F r w n) (hr : 0 < r)
    (Cod : Codec Bits256 (SchemeColumn F NoMask Ligero.V1.Mask nw nq repetitions) Bits256 Enc)
    (hCod : Cod.Inj)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq repetitions Equations)
    (dec₂ : Coin → QuerySet n r) (hn' : n ≤ 2 ^ 13)
    (statement : ConstraintSystem F nw nq w Equations) (messages : CoreMessages F nw nq w)
    (hsat : statement.Satisfies messages)
    {T : ℕ} (hT : 2 * n - 1 + 2 ^ 115 ≤ T)
    (dist : Distinguisher (v1Compiler (Equations := Equations) (nw := nw) (nq := nq)
      (repetitions := repetitions) C hr) Bits256 Bits256 Enc Coin V (2 ^ 115)) :
    StatClose (1 / 2 ^ 127)
      (realExp (T := T) (v1Compiler C hr) Cod dec₁ dec₂ (v1HonestProver C) statement messages
        dist)
      (simExp (T := T) (v1Compiler C hr) Cod (v1OpenedLeaf C hr)
        (v1ResponseAdaptiveSimulator (C := C) (fsVerifier dec₁ dec₂)) statement dist) :=
  compiled_zk_bits256_q115 (v1Compiler C hr) Cod dec₁ dec₂ (v1HonestProver C)
    (fun st ms => st.Satisfies ms)
    (v1ResponseAdaptiveSimulator (C := C) (fsVerifier dec₁ dec₂))
    (v1OpenedLeaf C hr) (fun _ _ _ _ => rfl)
    (v1_unbounded_perfect_response_adaptive_zero_knowledge (C := C)
      (VerifierCoins := Coin × Coin) (fsVerifier dec₁ dec₂))
    hCod hn' statement messages hsat hT dist

end V1

end Lfzk.CompiledLigeroZk
