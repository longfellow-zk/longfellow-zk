import Lfzk.ZkSim
import Merkle.Hiding
import Bcs.Compiled

/-!
# Compiled zero knowledge: the Merkle hiding term

`Lfzk.FromLigeroZKV1` proves `IsLigeroZeroKnowledge` at `eps_hide = 0` — the *oracle* protocol is
perfectly zero knowledge, because `Ligero.V1`'s response-adaptive statement is an equality of
distributions and Longfellow's pad blinding is a bijection on blinders.

(Ported from `proofs/lfzk/Lfzk/ZkMerkle.lean`; the code is verbatim, the unused
`Lfzk.FromLigeroZK` import is dropped and the docstrings name the V1 instance, since `formal/`
carries no V3.)

`ZkSim.lean` says why the parameter survives anyway:

> compiling the oracle away with a Merkle commitment reintroduces a hiding term, and that is where a
> nonzero value would come from.

This file is that term.  It is the zero-knowledge mirror of Phase 3c: there, the compilation cost a
*soundness* term (`Bcs.drop_explains_ratio_le`, an extraction failure); here it costs a *hiding* term
(`Merkle.MH.openingHiding_countingClose_closed`, a distinguisher hit).

## The two notions of closeness, and the bridge

`Merkle` counts: `RandomOracle.CountingClose eps real sim` says the two views differ on at most `eps`
points of one shared sample space `Ω`.  `Lfzk` measures: `StatClose eps f g` says no predicate
separates `f` from `g` by more than `eps`, over sample spaces that need not even have the same size.

The bridge is `zkClose_statClose`, already in `ZkHiding`: a coupling on `eps` bad coins out of `|R|`
is indistinguishability at `eps/|R|`.  What was missing is that a *same-space* counting bound is such
a coupling — at the identity bijection, which is `zkClose_of_countingClose` below.  So

```text
CountingClose eps  →  ZkClose eps  →  StatClose (eps / |Ω|)
```

and the Merkle numerator becomes an `eps_hide`.

## What this does and does not close

`isLigeroZeroKnowledge_of_compile` is the composition: given the oracle-protocol interface at `eps₀`
and a compilation whose proof is `epsM`-close to the oracle one, the compiled protocol satisfies the
interface at `epsM + eps₀` — and at `eps₀ = 0`, which is what `FromLigeroZK` gives, simply at `epsM`.

`verifierView_statClose` discharges the protocol-specific step: the verifier's view — the
commitment's opening view together with the opened values — cannot tell the real column family from
the simulated one, provided they agree where they are *opened*, which is what oracle zero knowledge
supplies perfectly.  `openOracle_eq_of_agreeOnOpened` is why the response needs no separate
component: `Bcs.Compiler.open_congr` makes it a function of the opened values.

This needed one generalisation on the Merkle side — `openingHidingView`'s distinguisher is now
*tape-indexed* — and it cost nothing: `leafCatch_prod_card_le`'s hypothesis is that the execution is
a function of (the other nonces, the tape), which a tape-indexed distinguisher satisfies by
construction.  Every proof in `Merkle/Hiding.lean` went through unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkMerkle

open Merkle Merkle.MH

/-! ## The bridge -/

/--
**A same-space counting bound is a coupling.**

`ZkClose` asks for a bijection between the two coin spaces; when the two views already live on the
same `Ω`, the identity serves.  The `ne_comm` is the only content: `CountingClose` counts
`real ω ≠ sim ω` and `ZkClose` counts `sim ω ≠ real ω`.
-/
theorem zkClose_of_countingClose {Ω V : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    {eps : ℕ} {real sim : Ω → V} (h : RandomOracle.CountingClose eps real sim) :
    ZkClose eps real sim := by
  classical
  refine ⟨Equiv.refl Ω, ?_⟩
  simp only [Sumcheck.event_card, Equiv.refl_apply]
  rw [show (Finset.filter (fun ω => sim ω ≠ real ω) Finset.univ)
        = (Finset.filter (fun ω => real ω ≠ sim ω) Finset.univ) from by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ne_comm]
  exact h

/--
**The Merkle hiding bound, as an indistinguishability bound.**

`eps` bad coins out of `|Ω|` is advantage at most `eps/|Ω|`, for an unbounded non-uniform
distinguisher.  This is the form `IsLigeroZeroKnowledge` takes.
-/
theorem statClose_of_countingClose {Ω V : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    {eps : ℕ} {real sim : Ω → V} (h : RandomOracle.CountingClose eps real sim) :
    StatClose ((eps : ℚ) / Fintype.card Ω) real sim :=
  zkClose_statClose (zkClose_of_countingClose h)

/-! ## The term the Merkle compilation adds -/

/--
**The opening-hiding term.**  `Merkle.MH.openingHidingNumerator` over the size of the hiding sample
space — nonces for every leaf and a tape of `T` digests.
-/
noncomputable def openingEps (saltCard digestCard n f T d omegaCard : ℕ) : ℚ :=
  (MH.openingHidingNumerator saltCard digestCard n f T d : ℚ) / omegaCard

open scoped Classical in
/--
**Two message vectors differing only on unopened coordinates are indistinguishable.**

`Merkle.MH.openingHiding_countingClose_closed`, read through the bridge.  This is the statement that
makes the Merkle commitment *statistically* hiding: what the verifier sees of the unopened columns is
independent of them, up to `openingEps`.
-/
theorem openingHiding_statClose
    {Salt M D Enc V : Type} [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
    [DecidableEq Enc] [DecidableEq V] [Inhabited D]
    (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n) (I : Finset (Fin n)) (T : ℕ) {f : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M) (E : Finset (Fin n))
    (dist : (Fin T → D) → OpeningView n I Salt D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hTn : 2 * n - 1 ≤ T) (hinjC : C.Inj)
    (hEI : ∀ i ∈ E, i ∉ I)
    (hE : ∀ (tape : Fin T → D) (i : Fin n), i ∉ E → m₀ tape i = m₁ tape i)
    (hsalt₀ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₀ tape i))
    (hsalt₁ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₁ tape i)) :
    StatClose
      (openingEps (Fintype.card Salt) (Fintype.card D) n f T E.card
        (Fintype.card (MH.HidingSample n T Salt D)))
      (MH.openingHidingView (T := T) C n I m₀ dist)
      (MH.openingHidingView (T := T) C n I m₁ dist) :=
  statClose_of_countingClose
    (MH.openingHiding_countingClose_closed C n hn I T m₀ m₁ E dist hT hTn hinjC hEI hE
      hsalt₀ hsalt₁)

/-! ## Composing with the oracle protocol -/

variable {ninp M' : ℕ} {F LigProof LigRand SimRand CompRand : Type} [Field F]
variable [Fintype LigRand] [Fintype SimRand] [Fintype CompRand]

/--
**Compiled zero knowledge.**

The oracle protocol satisfies the interface at `eps₀`; the compilation's proof is `epsM`-close to the
oracle one at every system and assignment.  Then the compiled protocol satisfies the interface at
`epsM + eps₀`.

This is `StatClose.trans`, and the point of stating it is the hypothesis list: `hcompile` is exactly
where a Merkle hiding term enters, and nothing else about the compilation is used.
-/
theorem isLigeroZeroKnowledge_of_compile {eps₀ epsM : ℚ}
    {realProof : LigeroSystem ninp M' F → (Fin ninp → F) → Pad M' F → LigRand → LigProof}
    {compiledProof : LigeroSystem ninp M' F → (Fin ninp → F) → Pad M' F → CompRand → LigProof}
    {sim : LigeroSystem ninp M' F → SimRand → LigProof}
    (lzk : IsLigeroZeroKnowledge eps₀ realProof sim)
    (hM : 0 ≤ epsM)
    (hcompile : ∀ (cs : LigeroSystem ninp M' F) (wcol : Fin ninp → F) (pad : Pad M' F),
      cs.Sat wcol pad →
        StatClose epsM (compiledProof cs wcol pad) (realProof cs wcol pad)) :
    IsLigeroZeroKnowledge (epsM + eps₀) compiledProof sim where
  nonneg := add_nonneg hM lzk.nonneg
  close cs wcol pad hsat :=
    StatClose.trans (hcompile cs wcol pad hsat) (lzk.close cs wcol pad hsat)

/--
**At perfect oracle zero knowledge, the compiled term is all there is.**

`Lfzk.FromLigeroZK.V1.isLigeroZeroKnowledge_v1` supplies `eps₀ = 0`, so the compiled protocol's
hiding error is exactly what the commitment costs.
-/
theorem isLigeroZeroKnowledge_of_compile_perfect {epsM : ℚ}
    {realProof : LigeroSystem ninp M' F → (Fin ninp → F) → Pad M' F → LigRand → LigProof}
    {compiledProof : LigeroSystem ninp M' F → (Fin ninp → F) → Pad M' F → CompRand → LigProof}
    {sim : LigeroSystem ninp M' F → SimRand → LigProof}
    (lzk : IsLigeroZeroKnowledge 0 realProof sim)
    (hM : 0 ≤ epsM)
    (hcompile : ∀ (cs : LigeroSystem ninp M' F) (wcol : Fin ninp → F) (pad : Pad M' F),
      cs.Sat wcol pad →
        StatClose epsM (compiledProof cs wcol pad) (realProof cs wcol pad)) :
    IsLigeroZeroKnowledge epsM compiledProof sim := by
  have h := isLigeroZeroKnowledge_of_compile lzk hM hcompile
  simpa using h

/-! ## The compiled statements

`longfellow_hvzk`, `longfellow_hvzk_statDist` and `longfellow_wi` are already parametric in
`eps_hide` — nothing in them assumes the commitment is perfect.  So the compiled statements are the
same theorems fed a different `IsLigeroZeroKnowledge`, and the only new input is `hcompile`.
-/

/--
**Compiled honest-verifier zero knowledge.**

`longfellow_hvzk` at the compiled interface: the transcript of the *compiled* prover is
`epsM`-indistinguishable from the simulator's, where `epsM` is what the commitment costs and the
oracle protocol contributes nothing.
-/
theorem longfellow_hvzk_compiled {nb : ℕ} {Witness Chal : Type} {epsM : ℚ}
    [Fintype F]
    (S : ZkSetup ninp M' nb F Witness Chal)
    {realProof : LigeroSystem ninp M' F → (Fin ninp → F) → Pad M' F → LigRand → LigProof}
    (compiledProof : LigeroSystem ninp M' F → (Fin ninp → F) → Pad M' F → CompRand → LigProof)
    (sim : LigeroSystem ninp M' F → SimRand → LigProof)
    (lzk : IsLigeroZeroKnowledge 0 realProof sim) (hM : 0 ≤ epsM)
    (hcompile : ∀ (cs : LigeroSystem ninp M' F) (wcol : Fin ninp → F) (pad : Pad M' F),
      cs.Sat wcol pad →
        StatClose epsM (compiledProof cs wcol pad) (realProof cs wcol pad))
    (w : Witness) (chal : Chal) :
    StatClose epsM (realTranscript S compiledProof w chal) (simulate S sim chal) :=
  longfellow_hvzk S compiledProof sim
    (isLigeroZeroKnowledge_of_compile_perfect lzk hM hcompile) w chal

/--
**Compiled witness indistinguishability.**  Two witnesses give transcripts `2·epsM`-close, with no
simulator in the statement.
-/
theorem longfellow_wi_compiled {nb : ℕ} {Witness Chal : Type} {epsM : ℚ}
    [Fintype F]
    (S : ZkSetup ninp M' nb F Witness Chal)
    {realProof : LigeroSystem ninp M' F → (Fin ninp → F) → Pad M' F → LigRand → LigProof}
    (compiledProof : LigeroSystem ninp M' F → (Fin ninp → F) → Pad M' F → CompRand → LigProof)
    (sim : LigeroSystem ninp M' F → SimRand → LigProof)
    (lzk : IsLigeroZeroKnowledge 0 realProof sim) (hM : 0 ≤ epsM)
    (hcompile : ∀ (cs : LigeroSystem ninp M' F) (wcol : Fin ninp → F) (pad : Pad M' F),
      cs.Sat wcol pad →
        StatClose epsM (compiledProof cs wcol pad) (realProof cs wcol pad))
    (w₁ w₂ : Witness) (chal : Chal) :
    StatClose (epsM + epsM)
      (realTranscript S compiledProof w₁ chal) (realTranscript S compiledProof w₂ chal) :=
  longfellow_wi (SimRand := SimRand) S compiledProof sim
    (isLigeroZeroKnowledge_of_compile_perfect lzk hM hcompile) w₁ w₂ chal

/-! ## Anchored at V1

`Lfzk.FromLigeroZK.V1.isLigeroZeroKnowledge_v1` is the `eps₀ = 0` instance:

```text
isLigeroZeroKnowledge_v1 C pl nlin verifier :
  IsLigeroZeroKnowledge 0 (realProofV1 C pl nlin verifier) (simV1 C pl nlin verifier)
```

so `isLigeroZeroKnowledge_of_compile_perfect` applies to it directly, and
`longfellow_hvzk_compiled` / `longfellow_wi_compiled` then read at `epsM`.  The composition is not
stated as a separate theorem here only because spelling out `simV1`'s codomain — a
`ResponseAdaptiveVerifierView` over four type arguments — buys nothing over applying the general
statement at the call site.
-/

/-! ## `hcompile`: agreement on the opened columns is enough

`openingHiding_statClose` asks for a set `E` containing every coordinate where the two message
vectors may differ, disjoint from the opened set `I`.  In the zero-knowledge application there is a
canonical such `E`: the *unopened* coordinates.  What oracle zero knowledge supplies is exactly that
the real and simulated column vectors agree on `I` — off `I` they are unrelated, and the point of the
commitment being hiding is that this cannot be seen.

So the hypothesis a compiled zero-knowledge statement has to discharge is not "the two vectors are
close" but "they agree where they are opened", which is a *pointwise equality* and much easier to
supply.
-/

open scoped Classical in
/--
**Agreement on the opened columns suffices.**

`openingHiding_statClose` at `E := univ \ I`: the two views differ by at most
`openingEps … (n - I.card)`, and the only hypothesis about the messages is that they agree on the
opened coordinates.
-/
theorem openingHiding_statClose_of_agreeOnOpened
    {Salt M D Enc V : Type} [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
    [DecidableEq Enc] [DecidableEq V] [Inhabited D]
    (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n) (I : Finset (Fin n)) (T : ℕ) {f : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M)
    (dist : (Fin T → D) → OpeningView n I Salt D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hTn : 2 * n - 1 ≤ T) (hinjC : C.Inj)
    (hagree : ∀ (tape : Fin T → D) (i : Fin n), i ∈ I → m₀ tape i = m₁ tape i)
    (hsalt₀ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₀ tape i))
    (hsalt₁ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₁ tape i)) :
    StatClose
      (openingEps (Fintype.card Salt) (Fintype.card D) n f T (Finset.univ \ I).card
        (Fintype.card (MH.HidingSample n T Salt D)))
      (MH.openingHidingView (T := T) C n I m₀ dist)
      (MH.openingHidingView (T := T) C n I m₁ dist) := by
  refine openingHiding_statClose C n hn I T m₀ m₁ (Finset.univ \ I) dist hT hTn hinjC
    ?_ ?_ hsalt₀ hsalt₁
  · intro i hi
    exact (Finset.mem_sdiff.mp hi).2
  · intro tape i hi
    -- off the *unopened* set means opened, where the two agree
    have : i ∈ I := by
      by_contra hc
      exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc⟩)
    exact hagree tape i this

/-! ## `hcompile`, in two halves

The compiled prover reveals the commitment — root plus the opening at the queried set — on top of
what the oracle prover reveals; the *response* is the oracle protocol's own, computed from the opened
columns.  So the obligation splits, and the two halves have different characters:

* the **response** half is an *equality*, not a bound.  `Bcs.Compiler.open_congr` is the locality
  axiom of the compiler: two commitments agreeing on the opened leaves are opened identically.  So
  the opened response is the same on the real and simulated sides, and contributes no term;
* the **commitment** half is `openingHiding_statClose_of_agreeOnOpened`, at `I := K.indices query`.

Both take the same hypothesis — the real and simulated column vectors agree on the *opened*
coordinates — which is what oracle zero knowledge supplies, perfectly.
-/

/--
**The response half, exactly.**

Two claimed column families agreeing on the queried set are opened identically.  This is
`Bcs.Compiler.open_congr` in the form the hiding argument uses: a *claim*-level statement rather than
an oracle-level one, so it composes with the Merkle view, which is indexed by column vectors.
-/
theorem openOracle_eq_of_agreeOnOpened
    {Statement Oracle Challenge Response Query : Type*} {Opening : Query → Type*}
    {M'' : Type*} {n : ℕ}
    (K : Bcs.Compiler Statement Oracle Challenge Response Query Opening M'' n)
    (query : Query) (a₀ a₁ : Fin n → M'')
    (h : ∀ i ∈ K.indices query, a₀ i = a₁ i) :
    K.protocol.openOracle (K.oracleOfClaim a₀) query
      = K.protocol.openOracle (K.oracleOfClaim a₁) query :=
  K.open_congr _ _ query (by
    intro i hi
    rw [Bcs.Compiler.columns_oracleOfClaim, Bcs.Compiler.columns_oracleOfClaim]
    exact h i hi)

open scoped Classical in
/--
**The commitment half, at a compiler's query.**

`openingHiding_statClose_of_agreeOnOpened` with `I := K.indices query`: the commitment's view of two
column families agreeing on the queried set is `openingEps`-close.

**Superseded for the verifier's view** by `verifierView_statClose` below.  This statement is about
`Merkle.MH.OpeningView`, which carries the root, the opened nonces and the frontier digests but not
the opened message values; `verifierView` adds those, which is what the verifier actually sees.
-/
theorem compiled_view_statClose
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Salt M'' D Enc V : Type} [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
    [DecidableEq Enc] [DecidableEq V] [Inhabited D] {n : ℕ}
    (K : Bcs.Compiler Statement Oracle Challenge Response Query Opening M'' n)
    (query : Query)
    (C : Codec Salt M'' D Enc) (hn : 0 < n) (T : ℕ) {f : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M'')
    (dist : (Fin T → D) → OpeningView n (K.indices query) Salt D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hTn : 2 * n - 1 ≤ T) (hinjC : C.Inj)
    (hagree : ∀ (tape : Fin T → D) (i : Fin n), i ∈ K.indices query → m₀ tape i = m₁ tape i)
    (hsalt₀ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₀ tape i))
    (hsalt₁ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₁ tape i)) :
    StatClose
      (openingEps (Fintype.card Salt) (Fintype.card D) n f T
        (Finset.univ \ K.indices query).card
        (Fintype.card (MH.HidingSample n T Salt D)))
      (MH.openingHidingView (T := T) C n (K.indices query) m₀ dist)
      (MH.openingHidingView (T := T) C n (K.indices query) m₁ dist) :=
  openingHiding_statClose_of_agreeOnOpened C n hn (K.indices query) T m₀ m₁ dist hT hTn hinjC
    hagree hsalt₀ hsalt₁

/-! ## The verifier's view

`Merkle.MH.openingHidingView` now takes a **tape-indexed** distinguisher,
`(Fin T → D) → OpeningView n I Salt D → Tree …`.  That generalisation cost nothing on the Merkle
side — the counting hypothesis of `leafCatch_prod_card_le` is that the execution is a function of
(the other nonces, the tape), and a tape-indexed distinguisher is exactly that — and it is what lets
the distinguisher receive the *opened values*, which depend on the tape.

With it the two halves of `hcompile` join: `verifierView` is the object the verifier actually sees —
the commitment's opening view **and** the opened values, from which `Bcs.Compiler.open_congr` says
the response is determined — and `verifierView_statClose` is that it cannot tell the real column
family from the simulated one.
-/

/-- The opened values, as the verifier receives them. -/
def openedValues {M'' : Type} {n : ℕ} (I : Finset (Fin n)) (m : Fin n → M'') :
    {i : Fin n // i ∈ I} → M'' := fun i => m i.val

/--
**The verifier's view.**  The commitment's opening view together with the opened values.  The
response is not a separate component: by `openOracle_eq_of_agreeOnOpened` it is a function of the
opened values, so a distinguisher that receives them can compute it.
-/
noncomputable def verifierView
    {Salt M'' D Enc V : Type} [DecidableEq Enc] [Inhabited D]
    (C : Codec Salt M'' D Enc) (n : ℕ) (I : Finset (Fin n)) {T f : ℕ}
    (m : (Fin T → D) → Fin n → M'')
    (dist : OpeningView n I Salt D → ({i : Fin n // i ∈ I} → M'') →
      RandomOracle.Tree Enc D V f) :
    MH.HidingSample n T Salt D → V :=
  MH.openingHidingView (T := T) C n I m (fun tp ov => dist ov (openedValues I (m tp)))

open scoped Classical in
/--
**`hcompile`, joined.**

The verifier's view of two column families that agree on the opened coordinates is
`openingEps`-close.  The opened values are *equal* on the two sides, so they contribute nothing; the
whole gap is the commitment's, and that is the Merkle opening-hiding term.

This is the statement `isLigeroZeroKnowledge_of_compile`'s `hcompile` asks for, at the level of the
view rather than of an abstract proof type.
-/
theorem verifierView_statClose
    {Salt M'' D Enc V : Type} [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
    [DecidableEq Enc] [DecidableEq V] [Inhabited D]
    (C : Codec Salt M'' D Enc) (n : ℕ) (hn : 0 < n) (I : Finset (Fin n)) (T : ℕ) {f : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M'')
    (dist : OpeningView n I Salt D → ({i : Fin n // i ∈ I} → M'') →
      RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hTn : 2 * n - 1 ≤ T) (hinjC : C.Inj)
    (hagree : ∀ (tape : Fin T → D) (i : Fin n), i ∈ I → m₀ tape i = m₁ tape i)
    (hsalt₀ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₀ tape i))
    (hsalt₁ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₁ tape i)) :
    StatClose
      (openingEps (Fintype.card Salt) (Fintype.card D) n f T (Finset.univ \ I).card
        (Fintype.card (MH.HidingSample n T Salt D)))
      (verifierView C n I m₀ dist) (verifierView C n I m₁ dist) := by
  -- the opened values agree, so both sides run the *same* tape-indexed distinguisher
  have hval : ∀ tp : Fin T → D, openedValues I (m₁ tp) = openedValues I (m₀ tp) := by
    intro tp
    funext i
    exact (hagree tp i.val i.property).symm
  have hrw : verifierView C n I m₁ dist
      = MH.openingHidingView (T := T) C n I m₁
          (fun tp ov => dist ov (openedValues I (m₀ tp))) := by
    unfold verifierView
    congr 1
    funext tp ov
    rw [hval tp]
  rw [verifierView, hrw]
  exact openingHiding_statClose_of_agreeOnOpened C n hn I T m₀ m₁
    (fun tp ov => dist ov (openedValues I (m₀ tp))) hT hTn hinjC hagree hsalt₀ hsalt₁

end Lfzk.ZkMerkle
