import Lfzk.ZkAdaptiveV1
import Lfzk.CompiledLigeroZk

/-!
# Zero knowledge of compiled Longfellow at Ligero V1, in one statement

`Lfzk.ZkFiatShamir` (the tape move), `Lfzk.ZkMerkle` (the Merkle hiding term),
`Lfzk.ZkProgram` (programming the challenge oracle) and `Lfzk.CompiledLigeroZk` (compiled Ligero
alone, for a fixed statement) compose only pairwise (`proofs/lfzk/README.md`, gap 4).  This file
is the single statement for the **compiled Longfellow argument** at Ligero V1, as `ZkProver`
runs it (`lib/zk/zk_prover.h`, `rust/runtime/zk`):

1. **commit** (`ZkProver::commit`): the witness and the random pad are laid out as the Ligero
   tableau and Merkle-committed column by column, each leaf salted with a fresh nonce
   (`MerkleCommitment::commit`: `SHA256(nonce ‖ column)`, 32-byte nonces and digests);
2. **sumcheck** (`ZkProver::prove`): the padded round polynomials and claim values are sent; every
   challenge is the hash of the transcript prefix, which begins with the root;
3. **Ligero** (`LigeroProver::prove`): the statement is built from the transcript
   (`verifier_constraints`); the Ligero challenge is the hash of the prefix, the response is
   sent, the column query is the hash of the prefix and the response, and the queried columns
   are opened with their nonces and Merkle paths.

`compiled_longfellow_zk` says: **for every witness valid for the statement, the real proof is
`openingEps`-close to a witness-free simulation, against every distinguisher that receives the
proof and both challenge oracles in full and makes at most `f` Merkle-oracle queries**, where

```
openingEps = (4n² + 2·d·f)/|Salt| + (2n−1)(2n−2)/|Digest|
```

(`openingEps_closed`), `n` the number of committed columns and `d` a bound on the unopened ones.
The tape move, the hiding term and the programming are all inside the one statement.

## The simulator (concrete; this discharges `ZkProgram.hview`)

`simExp` samples a V1 tape `ρ'`, a **transmission** `t` (uniform), Merkle coins, the round oracle,
a Ligero challenge oracle `G₀` and two raw challenges `c`, `i`; it then

* commits to the columns of the **all-zero** tableau on `ρ'` at the query `q = dec₂ i` and to
  `default` everywhere else;
* reads the sumcheck challenges off the round oracle at its own transcript `t` (it never programs
  the round oracle: the pad makes `t` uniform whatever the challenges are);
* builds the Ligero statement `s` from the transcript and answers with the honest V1 response of
  `s`'s **reference witness** on `ρ'` with its core paddings shifted to that witness
  (`Lfzk.ZkAdaptiveV1.simResp`);
* programs `G₀` at the two Ligero points so that they answer `c` and `i`.

It never reads *the* witness, but for Ligero's response it runs the honest prover on a reference
witness of the built statement, chosen noncomputably (`referenceMessages`).  So the simulator is not
efficient, and the theorem is not zero knowledge in the usual sense (an unbounded simulator could
always find a witness).  What it gives is **witness indistinguishability** against distinguishers
bounded by their Merkle queries: `compiled_longfellow_wi`.

## The four hybrids

| step | from → to | cost | lemma |
|---|---|---|---|
| program the Ligero points | real → `H1` | **0** | `CompiledLigeroZk.statClose_prog` (a bijection on oracles) |
| hide the unopened columns | `H1` → `H2` | `openingEps` | `ZkMerkle.openingHiding_statClose_of_agreeOnOpened` |
| adaptive V1 translation | `H2` → `H3` | **0** | `ZkAdaptiveV1.statClose_adaptive` |
| pad reparametrisation | `H3` → sim | **0** | `Frontend.transmit_bijective` (blinders ↔ transmission) |

The order matters and is forced.  The statement depends on the root, so the Ligero swap needs the
root to be a function of the opened columns alone — that is what the hiding step buys; and the
transmission depends on the root through the challenges, so the pad step needs the root to be
witness-free — that is what the Ligero swap buys.

## The model (stated plainly)

* **Query-bounded, hence computational.**  Every predicate on the distinguisher's output is
  allowed (`StatClose`), but the distinguisher makes at most `f` Merkle-oracle queries and the
  bound grows with `f` (`2·d·f/|Salt|`: guessing an unopened leaf's 256-bit nonce).  It is a
  statement about attackers bounded by their SHA-256 work, not a statistical one.
* **Inefficient simulator, so read it as witness indistinguishability** (`compiled_longfellow_wi`):
  the simulator uses a noncomputably chosen reference witness for Ligero's response.
* **Programmable random oracles, independent.**  The Merkle hash is a lazily sampled random
  oracle (`Merkle.RandomOracle.lazyRun` on a uniform tape); the round challenges and the two
  Ligero challenges are read from two further, independent, uniformly random functions `Gr` and
  `Gl`.  In the deployed code all three are SHA-256 (the Merkle tree on raw nonce‖column and
  digest‖digest strings, the transcript a running SHA-256 state expanded by a PRF); independence
  is the domain-separation idealisation, and the transcript ROM is the idealisation of the
  SHA-256 state + PRF expansion as a random function of the absorbed prefix.
* **Single session, statement fixed first ("version A").**  The witness and the public data are
  fixed before anything is sampled; the distinguisher queries the oracles only after receiving the
  proof (it gets `Gr` and `Gl` as whole functions and makes `f` Merkle-oracle queries).  An
  adversary that queries first and then chooses the statement is not covered.
* **Programming is free.**  Because the distinguisher has made no query before the proof, the
  two programmed Ligero points are a relabelling of a uniform oracle (`progEquiv`); the
  programming term of `ZkProgram.statClose_program` is `0` here.  The sumcheck challenges are not
  programmed at all.
* **The sumcheck stage is abstract** (`Frontend`): the committed tableau `msgs wit b`, the
  honest FS transmission `transmit wit Gr κ b` — a **bijection** in the blinders `b` for every
  oracle and context (`Lfzk.ZkFrontendOfSetup` builds it from `ZkSetup` and a causal transcript),
  and the Ligero statement `stmt Gr κ t` with `honest_sat`.  The context `κ = ctx root` carries
  the root (and, in the two-field protocol, everything else absorbed before this side's
  sumcheck).
* **The proof carries the raw challenges** `c` and `i` (the deployed proof does not; they are
  recomputable from it and the oracle, so this only strengthens the statement).

## What is *not* modelled

The byte encoding of columns and transcript prefixes (an injective codec is assumed, as in
`ZkMerkle`), the sumcheck arithmetic inside `Frontend` (see `Lfzk.ZkFrontendOfSetup`), multiple
sessions, and computational simulation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Lfzk.CompiledLongfellowZk

open Merkle Merkle.MH LigeroFamily LigeroFamily.ZeroKnowledge
open Lfzk.ZkAdaptiveV1 Lfzk.CompiledLigeroZk

/-! ## Plumbing -/

/-- `statClose_mix`, with both sides reindexed: if the two experiments, written over a shared
outer coordinate, are `eps`-close at every outer value, they are `eps`-close. -/
theorem statClose_mix_equiv {R S R₁ R₂ S₂ T : Type} [Fintype R] [Fintype S] [Fintype R₁]
    [Fintype R₂] [Fintype S₂] {eps : ℚ} (heps : 0 ≤ eps) (f : R → T) (g : S → T)
    (eR : R₁ × R₂ ≃ R) (eS : R₁ × S₂ ≃ S)
    (h : ∀ r₁, StatClose eps (fun r₂ => f (eR (r₁, r₂))) (fun s₂ => g (eS (r₁, s₂)))) :
    StatClose eps f g := by
  have hm := statClose_mix (R₁ := R₁) heps (fun r₁ r₂ => f (eR (r₁, r₂)))
    (fun r₁ s₂ => g (eS (r₁, s₂))) h
  have h1 : StatClose eps (fun p : R₁ × R₂ => f (eR p)) (fun q : R₁ × S₂ => g (eS q)) := hm
  exact (statClose_comp_equiv_right f g eS).mp
    ((statClose_comp_equiv_left f (fun q => g (eS q)) eR).mp h1)

/-- A pointwise identity along a bijection is a perfect closeness. -/
theorem statClose_of_equiv_pointwise {R S T : Type} [Fintype R] [Fintype S] (f : R → T)
    (g : S → T) (e : R ≃ S) (h : ∀ r, f r = g (e r)) : StatClose 0 f g := by
  intro P
  have hp := probOf_equiv e g P
  have hf : (fun r => g (e r)) = f := funext fun r => (h r).symm
  rw [hf] at hp
  rw [hp, sub_self, abs_zero]

/-- A continuation evaluated only at the value the first stage returns. -/
theorem lazyRun_bind_congr {Q D A B : Type} [DecidableEq Q] {T : ℕ} (tape : Fin T → D)
    (dflt : D) {f₁ f₂ : ℕ} (c : RandomOracle.Tree Q D A f₁) (k₁ k₂ : A → RandomOracle.Tree Q D B f₂)
    (seen : List Q) (h : k₁ (RandomOracle.lazyRun tape dflt c seen).1
      = k₂ (RandomOracle.lazyRun tape dflt c seen).1) :
    RandomOracle.lazyRun tape dflt (c.bind k₁) seen
      = RandomOracle.lazyRun tape dflt (c.bind k₂) seen := by
  rw [RandomOracle.lazyRun_bind, RandomOracle.lazyRun_bind, h]

/-! ## The protocol data -/

/--
**Longfellow's sumcheck stage, as the zero-knowledge argument sees it.**

* `msgs wit b` — the Ligero tableau `ZkProver::commit` commits: the witness and the pad, a
  function of the witness and the blinders **alone** (no challenge exists yet);
* `transmit wit Gr κ b` — what the honest Fiat–Shamir prover transmits during the sumcheck
  (padded round polynomials and claim values), at round oracle `Gr` and context `κ`;
* `transmit_bijective` — for every oracle and context, blinders ↦ transmission is a bijection.
  This is the pad's whole job, and with Fiat–Shamir it is a triangular bijection (round `k`'s
  blinded value is the honest value, a function of earlier transmissions through the challenges,
  plus a fresh blinder); `Lfzk.ZkFrontendOfSetup.frontendOfSetup` proves it from causality;
* `stmt Gr κ t` — the Ligero statement the verifier builds from the transcript;
* `honest_sat` — on valid inputs the honest tableau satisfies the statement built from the honest
  transcript.
-/
structure Frontend (F : Type) [Field F] (nw nq w : ℕ) (Equations : Type)
    (Ctx Wit Blind Tr RO : Type) where
  msgs : Wit → Blind → CoreMessages F nw nq w
  transmit : Wit → RO → Ctx → Blind → Tr
  transmit_bijective : ∀ (wit : Wit) (Gr : RO) (κ : Ctx), Function.Bijective (transmit wit Gr κ)
  stmt : RO → Ctx → Tr → ConstraintSystem F nw nq w Equations
  Valid : Wit → Ctx → Prop
  honest_sat : ∀ (wit : Wit) (Gr : RO) (κ : Ctx) (b : Blind), Valid wit κ →
    (stmt Gr κ (transmit wit Gr κ b)).Satisfies (msgs wit b)

/-- **The two Ligero hash inputs**: the prefix after the sumcheck transcript, and that prefix
followed by the raw challenge and the response.  They are distinct (domain separation by
length/role), which is all programming needs. -/
structure Points (Ctx Tr Coin Resp LQ : Type) where
  first : Ctx → Tr → LQ
  second : Ctx → Tr → Coin → Resp → LQ
  second_ne_first : ∀ κ t c resp, second κ t c resp ≠ first κ t

/-- **The proof, as the distinguisher receives it**: the root, the sumcheck transmission, the raw
Ligero challenge, the response, the raw query, the query, the Merkle opening (opened nonces and
frontier digests) and the opened columns. -/
structure ZkProof (n : ℕ) (Salt D Tr Coin Resp Query : Type) (POpen : Query → Type)
    (I : Query → Finset (Fin n)) where
  root : D
  transcript : Tr
  rawChallenge : Coin
  response : Resp
  rawQuery : Coin
  query : Query
  merkleOpening : MH.Opening n (I query) Salt D
  opening : POpen query

section Experiments

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq reps : ℕ}
variable {Salt D Enc Coin LQ Ctx Wit Blind Tr RO V : Type}
variable [DecidableEq Enc] [Inhabited D] [DecidableEq LQ]

/-- A committed column (a Merkle leaf). -/
abbrev Col (F : Type) (nw nq reps : ℕ) := SchemeColumn F NoMask Ligero.V1.Mask nw nq reps

/-- The V1 prover tape. -/
abbrev Tape {F : Type} [Field F] {r w n : ℕ} (C : MultiplicativeCode F r w n) (nw nq reps : ℕ) :=
  Ligero.V1.V1ProverRandomness C nw nq reps

/-- The compiled Longfellow proof at Ligero V1. -/
abbrev LProof (F : Type) [Field F] (r w n nw nq reps : ℕ) (Salt D Tr Coin : Type) :=
  ZkProof n Salt D Tr Coin (LigeroFamily.Response F r w n reps) (QuerySet n r)
    (Ligero.V1.Opening F nw nq reps n r) QuerySet.coordinates

/-- **A distinguisher**: given the proof, the round oracle and the Ligero challenge oracle (both
as whole functions), it makes at most `f` queries to the Merkle oracle. -/
abbrev Distinguisher (F : Type) [Field F] (r w n nw nq reps : ℕ)
    (Salt D Enc Tr Coin LQ RO V : Type) (f : ℕ) :=
  LProof F r w n nw nq reps Salt D Tr Coin → RO → (LQ → Coin) → RandomOracle.Tree Enc D V f

/-- The leaves of a commitment. -/
def colsOf (O : Ligero.V1.Oracle F nw nq n reps) : Fin n → Col F nw nq reps :=
  fun j => O.column j

/-- The opened leaves where opened, `default` elsewhere. -/
def leavesOfOpen {q : QuerySet n r} (o : Ligero.V1.Opening F nw nq reps n r q) :
    Fin n → Col F nw nq reps :=
  fun j => if h : j ∈ q.coordinates then o ⟨j, h⟩ else default

/-- The Ligero challenge oracle `G₀`, answering `c` at `x` and `i` at `y`. -/
def progAt (G₀ : LQ → Coin) (x : LQ) (c : Coin) (y : LQ) (i : Coin) : LQ → Coin :=
  Function.update (Function.update G₀ x c) y i

/-! ### The real experiment -/

/-- After the commitment, at commitment output `vals` and raw challenges `c` and `i`: the proof
the honest prover hands over. -/
noncomputable def realCont {C : MultiplicativeCode F r w n}
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : D → Ctx) (wit : Wit) {f : ℕ}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ : Tape C nw nq reps) (b : Blind) (nonce : Fin n → Salt) (Gr : RO) (Gl : LQ → Coin)
    (vals : ℕ → D) (c i : Coin) : RandomOracle.Tree Enc D V f :=
  dist ⟨vals 1, FE.transmit wit Gr (ctx (vals 1)) b, c,
      v1Resp (FE.stmt Gr (ctx (vals 1)) (FE.transmit wit Gr (ctx (vals 1)) b)) (FE.msgs wit b) ρ
        (dec₁ c),
      i, dec₂ i, { nonce := fun j => nonce j.val, frontierValue := fun v => vals v.val },
      openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i)⟩ Gr Gl

/--
**The honest compiled Longfellow prover, followed by the distinguisher.**

Merkle-commit the columns of `v1Oracle (msgs wit b) ρ` (`commitPass`); at root `vals 1` and
context `κ = ctx root`, run the honest sumcheck (`transmit`), read `c := Gl (first κ t)`, respond at
the statement built from the transcript, read `i := Gl (second κ t c resp)`, open the columns at
`dec₂ i`.
-/
noncomputable def realRun {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit) {f : ℕ}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ : Tape C nw nq reps) (b : Blind) (nonce : Fin n → Salt) (Gr : RO) (Gl : LQ → Coin) :
    RandomOracle.Tree Enc D V (f + (2 * n - 1)) :=
  (commitPass Cod n nonce (colsOf (v1Oracle (FE.msgs wit b) ρ)) (2 * n - 1)
      fun _ => default).bind fun vals =>
    realCont dec₁ dec₂ FE ctx wit dist ρ b nonce Gr Gl vals
      (Gl (pts.first (ctx (vals 1)) (FE.transmit wit Gr (ctx (vals 1)) b)))
      (Gl (pts.second (ctx (vals 1)) (FE.transmit wit Gr (ctx (vals 1)) b)
        (Gl (pts.first (ctx (vals 1)) (FE.transmit wit Gr (ctx (vals 1)) b)))
        (v1Resp (FE.stmt Gr (ctx (vals 1)) (FE.transmit wit Gr (ctx (vals 1)) b)) (FE.msgs wit b) ρ
          (dec₁ (Gl (pts.first (ctx (vals 1)) (FE.transmit wit Gr (ctx (vals 1)) b)))))))

/-- The real experiment at fixed coins. -/
noncomputable def realCore {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit) {T f : ℕ}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : HidingSample n T Salt D) (Gr : RO)
    (Gl : LQ → Coin) : V :=
  (RandomOracle.lazyRun hs.2 default (realRun Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs.1 Gr Gl)
    []).1

/--
**The real experiment.**  Coins: the V1 tape, the blinders, the Merkle nonces and lazy tape, the
round oracle and the Ligero challenge oracle — all uniform.
-/
noncomputable def realExp (C : MultiplicativeCode F r w n)
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit) {T f : ℕ}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f) :
    Tape C nw nq reps × Blind × HidingSample n T Salt D × RO × (LQ → Coin) → V :=
  fun ω => realCore Cod dec₁ dec₂ FE ctx pts wit dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2

/-! ### The hybrids' common shape -/

/-- Merkle-commit to `L`; at root `root` the transmission is `tOf root` and the response
`respOf root`; the raw challenges are the coins `c` and `i`; the Ligero challenge oracle is `G₀`
programmed at the two derived points; the opening is `o`. -/
noncomputable def hybExp (Cod : Codec Salt (Col F nw nq reps) D Enc) (dec₂ : Coin → QuerySet n r)
    (ctx : D → Ctx) (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) {T f : ℕ}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (L : Fin n → Col F nw nq reps) (i : Coin) (o : Ligero.V1.Opening F nw nq reps n r (dec₂ i))
    (tOf : D → Tr) (respOf : D → LigeroFamily.Response F r w n reps) (c : Coin) (Gr : RO)
    (G₀ : LQ → Coin) (hs : HidingSample n T Salt D) : V :=
  openingHidingView Cod n (dec₂ i).coordinates (fun _ => L)
    (fun _ ov => dist ⟨ov.rt, tOf ov.rt, c, respOf ov.rt, i, dec₂ i, ov.proof, o⟩ Gr
      (progAt G₀ (pts.first (ctx ov.rt) (tOf ov.rt)) c
        (pts.second (ctx ov.rt) (tOf ov.rt) c (respOf ov.rt)) i)) hs

omit [DecidableEq LQ] in
/-- The hybrid reads `tOf` and `respOf` only at the root the commitment produces. -/
theorem hybExp_congr (Cod : Codec Salt (Col F nw nq reps) D Enc) (dec₂ : Coin → QuerySet n r)
    (ctx : D → Ctx) (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) {T f : ℕ}
    [DecidableEq LQ]
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (L : Fin n → Col F nw nq reps) (i : Coin) (o : Ligero.V1.Opening F nw nq reps n r (dec₂ i))
    (tOf tOf' : D → Tr) (respOf respOf' : D → LigeroFamily.Response F r w n reps) (c : Coin)
    (Gr : RO) (G₀ : LQ → Coin) (hs : HidingSample n T Salt D)
    (ht : tOf (CompiledLigeroZk.commitRoot Cod L hs) = tOf' (CompiledLigeroZk.commitRoot Cod L hs))
    (hr : respOf (CompiledLigeroZk.commitRoot Cod L hs) = respOf' (CompiledLigeroZk.commitRoot Cod L hs)) :
    hybExp Cod dec₂ ctx pts dist L i o tOf respOf c Gr G₀ hs
      = hybExp Cod dec₂ ctx pts dist L i o tOf' respOf' c Gr G₀ hs := by
  unfold hybExp openingHidingView openingHidingRun
  rw [lazyRun_bind_congr]
  simp only [CompiledLigeroZk.commitRoot] at ht hr
  simp only [ht, hr]

/-! ### The simulator -/

/-- The simulator's response at root `root`: the reference witness of the statement built from
its own transmission `t`, on its tape with the core paddings shifted from the zero tableau. -/
noncomputable def simRespAt {C : MultiplicativeCode F r w n}
    (stmt : RO → Ctx → Tr → ConstraintSystem F nw nq w Equations) (ctx : D → Ctx)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (ρ' : Tape C nw nq reps) (t : Tr) (c i : Coin) (Gr : RO) (root : D) :
    LigeroFamily.Response F r w n reps :=
  v1Resp (stmt Gr (ctx root) t) (referenceMessages (stmt Gr (ctx root) t))
    (coreShift 0 (referenceMessages (stmt Gr (ctx root) t)) (dec₂ i) ρ') (dec₁ c)

/-- The simulated experiment at fixed coins. -/
noncomputable def simCore {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (stmt : RO → Ctx → Tr → ConstraintSystem F nw nq w Equations) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) {T f : ℕ}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ' : Tape C nw nq reps) (t : Tr) (hs : HidingSample n T Salt D) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) : V :=
  hybExp Cod dec₂ ctx pts dist (leavesOfOpen (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i))) i
    (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i)) (fun _ => t)
    (simRespAt stmt ctx dec₁ dec₂ ρ' t c i Gr) c Gr G₀ hs

/--
**The simulated experiment.**  It never sees a witness — its only inputs are public: the codec,
the decoders, the statement builder `stmt`, the context map, the Ligero points and the
distinguisher.  Coins: a V1 tape, a transmission, the Merkle coins, the round oracle, a Ligero
challenge oracle and two raw challenges.
-/
noncomputable def simExp (C : MultiplicativeCode F r w n)
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (stmt : RO → Ctx → Tr → ConstraintSystem F nw nq w Equations) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) {T f : ℕ}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f) :
    Tape C nw nq reps × Tr × HidingSample n T Salt D × RO × (LQ → Coin) × Coin × Coin → V :=
  fun ω => simCore Cod dec₁ dec₂ stmt ctx pts dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1
    ω.2.2.2.2.2.1 ω.2.2.2.2.2.2

end Experiments

/-! ## The hybrids and the bound -/

section Bound

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq reps : ℕ}
variable {Salt D Enc Coin LQ Ctx Wit Blind Tr RO V : Type}
variable [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D] [Inhabited D]
variable [DecidableEq Enc] [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
variable [Fintype LQ] [DecidableEq LQ] [Fintype Blind] [Fintype Tr] [Fintype RO] [DecidableEq V]

variable (C : MultiplicativeCode F r w n) (Cod : Codec Salt (Col F nw nq reps) D Enc)
  (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
  (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : D → Ctx)
  (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit)

/-- Hybrid 1 at fixed coins: the real columns are committed, the two raw Ligero challenges are
fresh coins and the challenge oracle is programmed to agree. -/
noncomputable def h1Core {T f : ℕ} (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : HidingSample n T Salt D) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) : V :=
  hybExp Cod dec₂ ctx pts dist (colsOf (v1Oracle (FE.msgs wit b) ρ)) i
    (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))
    (fun root => FE.transmit wit Gr (ctx root) b)
    (fun root => v1Resp (FE.stmt Gr (ctx root) (FE.transmit wit Gr (ctx root) b)) (FE.msgs wit b)
      ρ (dec₁ c)) c Gr G₀ hs

/-- Hybrid 2 at fixed coins: the unopened columns are replaced by `default`. -/
noncomputable def h2Core {T f : ℕ} (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : HidingSample n T Salt D) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) : V :=
  hybExp Cod dec₂ ctx pts dist
    (leavesOfOpen (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))) i
    (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))
    (fun root => FE.transmit wit Gr (ctx root) b)
    (fun root => v1Resp (FE.stmt Gr (ctx root) (FE.transmit wit Gr (ctx root) b)) (FE.msgs wit b)
      ρ (dec₁ c)) c Gr G₀ hs

/-- Hybrid 3 at fixed coins: the simulator's tableau and response, but still the honest
transmission. -/
noncomputable def h3Core {T f : ℕ} (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ' : Tape C nw nq reps) (b : Blind) (hs : HidingSample n T Salt D) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) : V :=
  hybExp Cod dec₂ ctx pts dist (leavesOfOpen (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i))) i
    (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i))
    (fun root => FE.transmit wit Gr (ctx root) b)
    (fun root => simRespAt FE.stmt ctx dec₁ dec₂ ρ' (FE.transmit wit Gr (ctx root) b) c i Gr root)
    c Gr G₀ hs

/-- The root of the honest commitment. -/
noncomputable def realRoot {T : ℕ} (ρ : Tape C nw nq reps) (b : Blind)
    (hs : HidingSample n T Salt D) : D :=
  CompiledLigeroZk.commitRoot Cod (colsOf (v1Oracle (FE.msgs wit b) ρ)) hs

/-! ### Step 1: programming the two Ligero points is free -/

/-- **The programming identity.**  The real experiment on `G₀` programmed at the two points the
honest prover reads *is* hybrid 1 at raw challenges `c` and `i`. -/
theorem realCore_prog {T f : ℕ} (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : HidingSample n T Salt D) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) :
    realCore Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr
        (prog (pts.first (ctx (realRoot C Cod FE wit ρ b hs))
            (FE.transmit wit Gr (ctx (realRoot C Cod FE wit ρ b hs)) b))
          (fun c' => pts.second (ctx (realRoot C Cod FE wit ρ b hs))
            (FE.transmit wit Gr (ctx (realRoot C Cod FE wit ρ b hs)) b) c'
            (v1Resp (FE.stmt Gr (ctx (realRoot C Cod FE wit ρ b hs))
                (FE.transmit wit Gr (ctx (realRoot C Cod FE wit ρ b hs)) b))
              (FE.msgs wit b) ρ (dec₁ c')))
          G₀ c i)
      = h1Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i := by
  simp only [realCore, realRun, realCont, h1Core, hybExp, openingHidingView, openingHidingRun,
    realRoot, CompiledLigeroZk.commitRoot]
  rw [RandomOracle.lazyRun_bind, RandomOracle.lazyRun_bind]
  rw [prog_first (fun c' => pts.second_ne_first _ _ _ _), prog_second]
  rfl

theorem step_prog {T f : ℕ} (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : HidingSample n T Salt D) (Gr : RO) :
    StatClose 0 (fun G : LQ → Coin => realCore Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G)
      (fun x : (LQ → Coin) × (Coin × Coin) =>
        h1Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr x.1 x.2.1 x.2.2) := by
  have h := statClose_prog
    (pts.first (ctx (realRoot C Cod FE wit ρ b hs))
      (FE.transmit wit Gr (ctx (realRoot C Cod FE wit ρ b hs)) b))
    (fun c' => pts.second (ctx (realRoot C Cod FE wit ρ b hs))
      (FE.transmit wit Gr (ctx (realRoot C Cod FE wit ρ b hs)) b) c'
      (v1Resp (FE.stmt Gr (ctx (realRoot C Cod FE wit ρ b hs))
          (FE.transmit wit Gr (ctx (realRoot C Cod FE wit ρ b hs)) b))
        (FE.msgs wit b) ρ (dec₁ c')))
    (fun c' => pts.second_ne_first _ _ _ _)
    (fun G => realCore Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G)
  have hfun : (fun x : (LQ → Coin) × (Coin × Coin) =>
      realCore Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr
        (prog (pts.first (ctx (realRoot C Cod FE wit ρ b hs))
            (FE.transmit wit Gr (ctx (realRoot C Cod FE wit ρ b hs)) b))
          (fun c' => pts.second (ctx (realRoot C Cod FE wit ρ b hs))
            (FE.transmit wit Gr (ctx (realRoot C Cod FE wit ρ b hs)) b) c'
            (v1Resp (FE.stmt Gr (ctx (realRoot C Cod FE wit ρ b hs))
                (FE.transmit wit Gr (ctx (realRoot C Cod FE wit ρ b hs)) b))
              (FE.msgs wit b) ρ (dec₁ c')))
          x.1 x.2.1 x.2.2))
      = fun x => h1Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr x.1 x.2.1 x.2.2 :=
    funext fun x => realCore_prog C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr x.1 x.2.1 x.2.2
  rw [hfun] at h
  exact h

/-! ### Step 2: the Merkle commitment hides the unopened columns -/

theorem step_hide (hinjC : Cod.Inj) (hn : 0 < n) (d : ℕ)
    (hd : ∀ q : QuerySet n r, (Finset.univ \ q.coordinates).card ≤ d) {T f : ℕ}
    (hT : 2 * n - 1 + f ≤ T)
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ : Tape C nw nq reps) (b : Blind) (Gr : RO) (G₀ : LQ → Coin) (c i : Coin) :
    StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n f T d
        (Fintype.card (HidingSample n T Salt D)))
      (fun hs : HidingSample n T Salt D => h1Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i)
      (fun hs : HidingSample n T Salt D => h2Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i) := by
  classical
  have hT₁ : 2 * n - 2 < T := by omega
  have hT₂ : 2 * n - 1 ≤ T := by omega
  have hagree : ∀ (tape : Fin T → D) (j : Fin n), j ∈ (dec₂ i).coordinates →
      (fun _ => colsOf (v1Oracle (FE.msgs wit b) ρ)) tape j
        = (fun _ => leavesOfOpen (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))) tape j := by
    intro tape j hj
    simp only [leavesOfOpen, dif_pos hj]
    rfl
  have hsalt : ∀ (m : (Fin T → D) → Fin n → Col F nw nq reps) (tape : Fin T → D) (j : Fin n),
      Function.Injective fun salt : Salt => Cod.leafEnc (salt, m tape j) :=
    fun m tape j a a' hab => congrArg Prod.fst (hinjC.leaf hab)
  have h := ZkMerkle.openingHiding_statClose_of_agreeOnOpened Cod n hn (dec₂ i).coordinates T
    (fun _ => colsOf (v1Oracle (FE.msgs wit b) ρ))
    (fun _ => leavesOfOpen (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i)))
    (fun _ ov => dist ⟨ov.rt, FE.transmit wit Gr (ctx ov.rt) b, c,
        v1Resp (FE.stmt Gr (ctx ov.rt) (FE.transmit wit Gr (ctx ov.rt) b)) (FE.msgs wit b) ρ (dec₁ c),
        i, dec₂ i, ov.proof, openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i)⟩ Gr
      (progAt G₀ (pts.first (ctx ov.rt) (FE.transmit wit Gr (ctx ov.rt) b)) c
        (pts.second (ctx ov.rt) (FE.transmit wit Gr (ctx ov.rt) b) c
          (v1Resp (FE.stmt Gr (ctx ov.rt) (FE.transmit wit Gr (ctx ov.rt) b)) (FE.msgs wit b) ρ
            (dec₁ c))) i))
    hT₁ hT₂ hinjC hagree (hsalt _) (hsalt _)
  exact h.mono (openingEps_mono (hd _))

/-! ### Step 3: the adaptive V1 translation -/

theorem step_adaptive (hvalid : ∀ root, FE.Valid wit (ctx root)) {T f : ℕ}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (b : Blind) (hs : HidingSample n T Salt D) (Gr : RO) (G₀ : LQ → Coin) (c i : Coin) :
    StatClose 0
      (fun ρ : Tape C nw nq reps => h2Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i)
      (fun ρ' : Tape C nw nq reps => h3Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ' b hs Gr G₀ c i) := by
  let rootOf : Ligero.V1.Opening F nw nq reps n r (dec₂ i) → D :=
    fun o => CompiledLigeroZk.commitRoot Cod (leavesOfOpen o) hs
  let S : Ligero.V1.Opening F nw nq reps n r (dec₂ i) → ConstraintSystem F nw nq w Equations :=
    fun o => FE.stmt Gr (ctx (rootOf o)) (FE.transmit wit Gr (ctx (rootOf o)) b)
  have hsat : ∀ o, (S o).Satisfies (FE.msgs wit b) :=
    fun o => FE.honest_sat wit Gr _ b (hvalid _)
  let Ψ : Ligero.V1.Opening F nw nq reps n r (dec₂ i) → LigeroFamily.Response F r w n reps → V :=
    fun o resp => hybExp Cod dec₂ ctx pts dist (leavesOfOpen o) i o
      (fun root => FE.transmit wit Gr (ctx root) b) (fun _ => resp) c Gr G₀ hs
  have h := statClose_adaptive (C := C) (FE.msgs wit b) (dec₂ i) (dec₁ c) S hsat Ψ
  have e1 : (fun ρ => h2Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i)
      = fun ρ : Tape C nw nq reps => Ψ (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))
          (v1Resp (S (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))) (FE.msgs wit b) ρ
            (dec₁ c)) :=
    funext fun ρ => hybExp_congr Cod dec₂ ctx pts dist _ i _ _ _ _ _ c Gr G₀ hs rfl rfl
  have e2 : (fun ρ' => h3Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ' b hs Gr G₀ c i)
      = fun ρ' : Tape C nw nq reps => Ψ (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i))
          (simResp S (dec₁ c) ρ') :=
    funext fun ρ' => hybExp_congr Cod dec₂ ctx pts dist _ i _ _ _ _ _ c Gr G₀ hs rfl rfl
  rw [e1, e2]
  exact h

/-! ### Step 4: the pad makes the transmission uniform -/

theorem step_pad {T f : ℕ}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ' : Tape C nw nq reps) (hs : HidingSample n T Salt D) (Gr : RO) (G₀ : LQ → Coin)
    (c i : Coin) :
    StatClose 0
      (fun b : Blind => h3Core C Cod dec₁ dec₂ FE ctx pts wit dist ρ' b hs Gr G₀ c i)
      (fun t : Tr => simCore Cod dec₁ dec₂ FE.stmt ctx pts dist ρ' t hs Gr G₀ c i) := by
  let root₀ := CompiledLigeroZk.commitRoot Cod
    (leavesOfOpen (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i))) hs
  let e := Equiv.ofBijective (FE.transmit wit Gr (ctx root₀)) (FE.transmit_bijective wit Gr (ctx root₀))
  refine statClose_of_equiv_pointwise _ _ e fun b => ?_
  exact hybExp_congr Cod dec₂ ctx pts dist _ i _ _ _ _ _ c Gr G₀ hs rfl rfl

/-! ### Sample-space bookkeeping -/

/-- Step 1's real side. -/
def e1R (A B H R G : Type) : (A × B × H × R) × G ≃ A × B × H × R × G where
  toFun p := (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2, p.2)
  invFun ω := ((ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1), ω.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Step 1's hybrid side. -/
def e1S (A B H R G X Y : Type) : (A × B × H × R) × (G × X × Y) ≃ A × B × H × R × G × X × Y where
  toFun p := (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2, p.2.1, p.2.2.1, p.2.2.2)
  invFun ω := ((ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1), (ω.2.2.2.2.1, ω.2.2.2.2.2.1, ω.2.2.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Step 2: the Merkle coins inside. -/
def e2 (A B H R G X Y : Type) : (A × B × R × G × X × Y) × H ≃ A × B × H × R × G × X × Y where
  toFun p := (p.1.1, p.1.2.1, p.2, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2)
  invFun ω := ((ω.1, ω.2.1, ω.2.2.2.1, ω.2.2.2.2.1, ω.2.2.2.2.2.1, ω.2.2.2.2.2.2), ω.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Step 3: the V1 tape inside. -/
def e3 (A B H R G X Y : Type) : (B × H × R × G × X × Y) × A ≃ A × B × H × R × G × X × Y where
  toFun p := (p.2, p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2)
  invFun ω := ((ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2.1, ω.2.2.2.2.2.1, ω.2.2.2.2.2.2), ω.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Step 4: the blinders (resp. the transmission) inside. -/
def e4 (A B H R G X Y : Type) : (A × H × R × G × X × Y) × B ≃ A × B × H × R × G × X × Y where
  toFun p := (p.1.1, p.2, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2)
  invFun ω := ((ω.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2.1, ω.2.2.2.2.2.1, ω.2.2.2.2.2.2), ω.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The theorem -/

/--
**Zero knowledge of compiled Longfellow at Ligero V1.**

For every witness valid at every root (`hvalid`: the public data is fixed and the witness is a
witness for it), and every distinguisher that receives the proof, the round oracle and the Ligero
challenge oracle and makes at most `f` Merkle-oracle queries, the real experiment is
`openingEps`-close to the witness-free simulation `simExp`.

Inputs:

* `hinjC` — same-role injectivity of the Merkle codec (fixed-width raw concatenation, as
  deployed, is injective);
* `hd` — at most `d` columns are unopened by any query (`d = n − r` at the deployed query size);
* `hT` — the Merkle lazy tape covers the commitment's `2n − 1` and the distinguisher's `f`
  queries, so the Merkle oracle is uniform throughout.
-/
theorem compiled_longfellow_zk (hinjC : Cod.Inj) (hvalid : ∀ root, FE.Valid wit (ctx root))
    (d : ℕ) (hd : ∀ q : QuerySet n r, (Finset.univ \ q.coordinates).card ≤ d) (hn : 0 < n)
    {T f : ℕ} (hT : 2 * n - 1 + f ≤ T)
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f) :
    StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n f T d
        (Fintype.card (HidingSample n T Salt D)))
      (realExp C Cod dec₁ dec₂ FE ctx pts wit (T := T) dist)
      (simExp C Cod dec₁ dec₂ FE.stmt ctx pts (T := T) dist) := by
  classical
  let H1 : Tape C nw nq reps × Blind × HidingSample n T Salt D × RO × (LQ → Coin) × Coin × Coin → V :=
    fun ω => h1Core C Cod dec₁ dec₂ FE ctx pts wit dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1
      ω.2.2.2.2.2.1 ω.2.2.2.2.2.2
  let H2 : Tape C nw nq reps × Blind × HidingSample n T Salt D × RO × (LQ → Coin) × Coin × Coin → V :=
    fun ω => h2Core C Cod dec₁ dec₂ FE ctx pts wit dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1
      ω.2.2.2.2.2.1 ω.2.2.2.2.2.2
  let H3 : Tape C nw nq reps × Blind × HidingSample n T Salt D × RO × (LQ → Coin) × Coin × Coin → V :=
    fun ω => h3Core C Cod dec₁ dec₂ FE ctx pts wit dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1
      ω.2.2.2.2.2.1 ω.2.2.2.2.2.2
  have s1 : StatClose 0 (realExp C Cod dec₁ dec₂ FE ctx pts wit (T := T) dist) H1 :=
    statClose_mix_equiv le_rfl _ _ (e1R _ _ _ _ _) (e1S _ _ _ _ _ _ _)
      fun r₁ => step_prog C Cod dec₁ dec₂ FE ctx pts wit dist r₁.1 r₁.2.1 r₁.2.2.1 r₁.2.2.2
  have s2 : StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n f T d
        (Fintype.card (HidingSample n T Salt D))) H1 H2 :=
    statClose_mix_equiv (openingEps_nonneg _ _ _ _ _ _ _) _ _ (e2 _ _ _ _ _ _ _)
      (e2 _ _ _ _ _ _ _)
      fun r₁ => step_hide C Cod dec₁ dec₂ FE ctx pts wit hinjC hn d hd hT dist r₁.1 r₁.2.1
        r₁.2.2.1 r₁.2.2.2.1 r₁.2.2.2.2.1 r₁.2.2.2.2.2
  have s3 : StatClose 0 H2 H3 :=
    statClose_mix_equiv le_rfl _ _ (e3 _ _ _ _ _ _ _) (e3 _ _ _ _ _ _ _)
      fun r₁ => step_adaptive C Cod dec₁ dec₂ FE ctx pts wit hvalid dist r₁.1 r₁.2.1 r₁.2.2.1
        r₁.2.2.2.1 r₁.2.2.2.2.1 r₁.2.2.2.2.2
  have s4 : StatClose 0 H3 (simExp C Cod dec₁ dec₂ FE.stmt ctx pts (T := T) dist) :=
    statClose_mix_equiv le_rfl _ _ (e4 _ _ _ _ _ _ _) (e4 _ _ _ _ _ _ _)
      fun r₁ => step_pad C Cod dec₁ dec₂ FE ctx pts wit dist r₁.1 r₁.2.1 r₁.2.2.1 r₁.2.2.2.1
        r₁.2.2.2.2.1 r₁.2.2.2.2.2
  have h := s1.trans (s2.trans (s3.trans s4))
  simpa using h

/--
**Witness indistinguishability against query-bounded distinguishers.**  For two witnesses valid for
the same statement, the two honest proofs are `2 · openingEps`-close, against every distinguisher
that sees the proof and both challenge oracles and makes at most `f` Merkle-oracle queries.

This is what `compiled_longfellow_zk` amounts to: its simulator answers Ligero's response with the
honest prover run on a reference witness chosen noncomputably (`referenceMessages`), so it is not
an efficient simulator, and the theorem is best read as this corollary.  The bound grows with `f`
(`2·d·f/|Salt|`, guessing an unopened leaf's nonce), so the guarantee is computational in the
number of Merkle-hash evaluations, not statistical.
-/
theorem compiled_longfellow_wi (hinjC : Cod.Inj) {wit₀ wit₁ : Wit}
    (hvalid₀ : ∀ root, FE.Valid wit₀ (ctx root)) (hvalid₁ : ∀ root, FE.Valid wit₁ (ctx root))
    (d : ℕ) (hd : ∀ q : QuerySet n r, (Finset.univ \ q.coordinates).card ≤ d) (hn : 0 < n)
    {T f : ℕ} (hT : 2 * n - 1 + f ≤ T)
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f) :
    StatClose
      (2 * ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n f T d
        (Fintype.card (HidingSample n T Salt D)))
      (realExp C Cod dec₁ dec₂ FE ctx pts wit₀ (T := T) dist)
      (realExp C Cod dec₁ dec₂ FE ctx pts wit₁ (T := T) dist) := by
  have h₀ := compiled_longfellow_zk C Cod dec₁ dec₂ FE ctx pts wit₀ hinjC hvalid₀ d hd hn hT dist
  have h₁ := compiled_longfellow_zk C Cod dec₁ dec₂ FE ctx pts wit₁ hinjC hvalid₁ d hd hn hT dist
  rw [two_mul]
  exact h₀.trans h₁.symm

end Bound

/-! ## The bound in closed form, and at the deployed geometries -/

section Numerals

/-- **`openingEps` in closed form**: `(4n² + 2·d·f)/|Salt| + (2n−1)(2n−2)/|Digest|`.

The three terms are the three bad events of `Merkle.MH.openingHidingBad`: a collision among the
honest commitment's leaf inputs (`4n²/|Salt|`, via nonce collisions in both experiments), among its
`2n−1` slot answers (`(2n−1)(2n−2)/|Digest|`), and the distinguisher hitting an unopened leaf's
salted input (`2·d·f/|Salt|`, `f` queries against `d` unopened nonces, in both experiments). -/
theorem openingEps_closed (S Dg n f T d : ℕ) (hS : 0 < S) (hD : 0 < Dg) (hn : 0 < n)
    (hT : 0 < T) :
    ZkMerkle.openingEps S Dg n f T d (S ^ n * Dg ^ T)
      = ((4 * n ^ 2 + 2 * d * f : ℕ) : ℚ) / S + (((2 * n - 1) * (2 * n - 2) : ℕ) : ℚ) / Dg := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have h2 : 2 * (k + 1) - 2 = 2 * k := by omega
  have hdiv : (2 * k + 1) * (2 * k) / 2 = (2 * k + 1) * k := by
    rw [show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  unfold ZkMerkle.openingEps openingHidingNumerator
  rw [h1, h2, hdiv]
  simp only [Nat.add_sub_cancel]
  have hS' : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  have hD' : (Dg : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  field_simp
  ring

theorem card_hidingSample_bits256 (n T : ℕ) :
    Fintype.card (HidingSample n T Bits256 Bits256) = (2 ^ 256) ^ n * (2 ^ 256) ^ T := by
  simp [HidingSample, Fintype.card_prod]

/-- At 32-byte nonces and digests. -/
theorem openingEps_bits256 (n f T d : ℕ) (hn : 0 < n) (hT : 0 < T) :
    ZkMerkle.openingEps (Fintype.card Bits256) (Fintype.card Bits256) n f T d
        (Fintype.card (HidingSample n T Bits256 Bits256))
      = ((4 * n ^ 2 + 2 * d * f + (2 * n - 1) * (2 * n - 2) : ℕ) : ℚ) / 2 ^ 256 := by
  rw [card_hidingSample_bits256, card_Bits256,
    openingEps_closed _ _ n f T d (by positivity) (by positivity) hn hT]
  push_cast
  ring

/-- **The deployed regime**: at most `2^12` committed columns, so the `f`-free terms are below
`2^27/2^256`. -/
theorem openingEps_bits256_le (n f T d : ℕ) (hn : 0 < n) (hn' : n ≤ 2 ^ 12) (hT : 0 < T) :
    ZkMerkle.openingEps (Fintype.card Bits256) (Fintype.card Bits256) n f T d
        (Fintype.card (HidingSample n T Bits256 Bits256))
      ≤ ((2 ^ 27 + 2 * d * f : ℕ) : ℚ) / 2 ^ 256 := by
  rw [openingEps_bits256 n f T d hn hT]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsq : n ^ 2 ≤ (2 ^ 12) ^ 2 := Nat.pow_le_pow_left hn' 2
  have hprod : (2 * n - 1) * (2 * n - 2) ≤ 4 * n ^ 2 := by
    calc (2 * n - 1) * (2 * n - 2) ≤ (2 * n) * (2 * n) :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = 4 * n ^ 2 := by ring
  have : 4 * n ^ 2 + (2 * n - 1) * (2 * n - 2) ≤ 2 ^ 27 := by
    have : 4 * n ^ 2 ≤ 4 * (2 ^ 12) ^ 2 := Nat.mul_le_mul_left 4 hsq
    norm_num at this ⊢
    omega
  exact_mod_cast (by omega : 4 * n ^ 2 + 2 * d * f + (2 * n - 1) * (2 * n - 2)
    ≤ 2 ^ 27 + 2 * d * f)

/-- A query set opens exactly `r` of the `n` columns, so exactly `n − r` are unopened. -/
theorem unopened_card {n r : ℕ} (q : QuerySet n r) :
    (Finset.univ \ q.coordinates).card = n - r := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    QuerySet.card_coordinates]

/-- At `f = 2^115` Merkle-oracle queries, any geometry with at most `2^12` columns and at least one
opened column: `≤ 2^-128`. -/
theorem openingEps_bits256_q115 (n r T : ℕ) (hn : 0 < n) (hn' : n ≤ 2 ^ 12) (hr : 0 < r)
    (hT : 0 < T) :
    ZkMerkle.openingEps (Fintype.card Bits256) (Fintype.card Bits256) n (2 ^ 115) T (n - r)
        (Fintype.card (HidingSample n T Bits256 Bits256)) ≤ 1 / 2 ^ 128 := by
  refine (openingEps_bits256_le n (2 ^ 115) T (n - r) hn hn' hT).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hd : 2 * (n - r) ≤ 8190 := by omega
  have : 2 ^ 27 + 2 * (n - r) * 2 ^ 115 ≤ 2 ^ 128 := by
    have h27 : (2 : ℕ) ^ 27 ≤ 2 * 2 ^ 115 := by norm_num
    calc 2 ^ 27 + 2 * (n - r) * 2 ^ 115 ≤ 2 * 2 ^ 115 + 8190 * 2 ^ 115 :=
          Nat.add_le_add h27 (Nat.mul_le_mul_right _ hd)
      _ = 2 ^ 128 := by norm_num
  have h' : ((2 ^ 27 + 2 * (n - r) * 2 ^ 115 : ℕ) : ℚ) ≤ 2 ^ 128 := by exact_mod_cast this
  nlinarith [h']

end Numerals

/-! ## The headline at 32-byte nonces and digests -/

section Bits256

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq reps : ℕ}
variable {Enc Coin LQ Ctx Wit Blind Tr RO V : Type}
variable [DecidableEq Enc] [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
variable [Fintype LQ] [DecidableEq LQ] [Fintype Blind] [Fintype Tr] [Fintype RO] [DecidableEq V]

/--
**Compiled Longfellow at Ligero V1 is zero knowledge, at the deployed hash sizes.**

32-byte nonces and SHA-256 digests (`MerkleNonce::kLength = kSHA256DigestSize`), any
same-role-injective codec, a V1 code with `r` opened columns out of `n`, any front end, any
decoders and any Ligero hash points.  For every witness valid at every root and every distinguisher
making at most `f` Merkle-oracle queries (and seeing both challenge oracles in full):

```
StatClose ((4n² + 2(n−r)f + (2n−1)(2n−2)) / 2^256)  real  simulated
```
-/
theorem compiled_longfellow_zk_bits256 (C : MultiplicativeCode F r w n)
    (Cod : Codec Bits256 (Col F nw nq reps) Bits256 Enc) (hinjC : Cod.Inj)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : Bits256 → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit)
    (hvalid : ∀ root, FE.Valid wit (ctx root)) (hn : 0 < n) {T f : ℕ} (hT : 2 * n - 1 + f ≤ T)
    (dist : Distinguisher F r w n nw nq reps Bits256 Bits256 Enc Tr Coin LQ RO V f) :
    StatClose (((4 * n ^ 2 + 2 * (n - r) * f + (2 * n - 1) * (2 * n - 2) : ℕ) : ℚ) / 2 ^ 256)
      (realExp C Cod dec₁ dec₂ FE ctx pts wit (T := T) dist)
      (simExp C Cod dec₁ dec₂ FE.stmt ctx pts (T := T) dist) := by
  have h := compiled_longfellow_zk C Cod dec₁ dec₂ FE ctx pts wit hinjC hvalid (n - r)
    (fun q => (unopened_card q).le) hn hT dist
  rwa [openingEps_bits256 n f T (n - r) hn (by omega)] at h

/--
**At `2^115` Merkle-oracle queries: `≤ 2^-128`**, for every deployed geometry (at most `2^12`
committed columns: v7 signature `n = 3187`, v7 hash `n = 3230 … 3436`, v8 hash `n = 4088`,
v8 signature `n = 3458`; `r = 132` opened columns).
-/
theorem compiled_longfellow_zk_bits256_q115 (C : MultiplicativeCode F r w n)
    (Cod : Codec Bits256 (Col F nw nq reps) Bits256 Enc) (hinjC : Cod.Inj)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : Bits256 → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit)
    (hvalid : ∀ root, FE.Valid wit (ctx root)) (hn : 0 < n) (hn' : n ≤ 2 ^ 12) (hr : 0 < r)
    {T : ℕ} (hT : 2 * n - 1 + 2 ^ 115 ≤ T)
    (dist : Distinguisher F r w n nw nq reps Bits256 Bits256 Enc Tr Coin LQ RO V (2 ^ 115)) :
    StatClose (1 / 2 ^ 128)
      (realExp C Cod dec₁ dec₂ FE ctx pts wit (T := T) dist)
      (simExp C Cod dec₁ dec₂ FE.stmt ctx pts (T := T) dist) := by
  have h := compiled_longfellow_zk C Cod dec₁ dec₂ FE ctx pts wit hinjC hvalid (n - r)
    (fun q => (unopened_card q).le) hn hT dist
  exact h.mono (by
    simpa using openingEps_bits256_q115 n r T hn hn' hr (by omega))

end Bits256

end Lfzk.CompiledLongfellowZk
