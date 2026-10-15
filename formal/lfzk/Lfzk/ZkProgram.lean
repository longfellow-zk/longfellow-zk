import Lfzk.ZkFiatShamir
import Lfzk.ZkMerkle

/-!
# Step 3: programming the oracle to force the challenge

`Lfzk.ZkFiatShamir` showed that putting the challenge on the hash tape is free, and isolated the
whole difficulty as the **adaptivity**: the real derivation is `chal = H(prefix)` with the prefix
containing the prover's own messages, so the simulator cannot evaluate it before producing messages
and cannot produce messages before knowing the challenge.

This file breaks that circle.  The simulator picks the challenge, runs the honest-verifier simulator
at it, and *then* programs the oracle at the one input the derivation reads so that the derivation
agrees.  Two facts do the work, and they have very different characters:

* **Programming forces the challenge** — `derive_programTo`, an *equality*, two lines.  This is the
  step the circularity blocked, and once the oracle is a value that can be patched there is nothing
  to it.
* **Programming is undetectable unless asked** — `Merkle.RandomOracle.run_congr_off_programQueried`,
  from step 2, over an arbitrary programmed set.

The detection event is the cheapest possible: the simulator programs a **single** input, so the bad
event is "the distinguisher queried the challenge input", one fresh hit.  Forcing `L` challenges
costs `L` such terms, which is the usual Fiat–Shamir simulator accounting.

## What is proved, and what is named

Proved: that programming forces the challenge; that the forced oracle differs from the real one only
at that input; and the composition — real is `(eps_hvzk + eps_prog/|Ω|)`-close to the programmed
simulator, from honest-verifier closeness plus a counting bound on detection.

Named, not proved: `hview`, that the *programmed* simulator's view is the honest-verifier simulator's
view at the forced challenge.  That is an identification of two protocol objects, in the same family
as `hcompile` was before `verifierView_statClose` — the content is that the simulator's messages are
the ones the honest-verifier simulator produces, which is true by construction of any concrete
simulator but is not a fact about `Derivation`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkProgram

open Merkle

/-! ## The adaptive derivation -/

/--
**How a Fiat–Shamir challenge is derived.**  The prover's messages determine a hash input; the
digest there, decoded, is the challenge.  `Pre` is whatever the prefix is — this file needs only that
the input is a function of it.
-/
structure Derivation (Enc D Chal Pre : Type) where
  /-- The hash input the challenge is read from — a function of the prover's own messages. -/
  input : Pre → Enc
  /-- How a digest becomes a challenge. -/
  decode : D → Chal

namespace Derivation

variable {Enc D Chal Pre : Type}

/-- The derived challenge. -/
def derive (d : Derivation Enc D Chal Pre) (H : Enc → D) (pre : Pre) : Chal :=
  d.decode (H (d.input pre))

end Derivation

/-! ## Forcing a challenge -/

/-- The oracle `H`, patched to answer `y` at the single input `x`. -/
def programTo {Enc D : Type} [DecidableEq Enc] (x : Enc) (y : D) (H : Enc → D) : Enc → D :=
  RandomOracle.reprogram {x} H (fun _ => y)

@[simp] theorem programTo_apply {Enc D : Type} [DecidableEq Enc] (x : Enc) (y : D) (H : Enc → D) :
    programTo x y H x = y := by
  simp [programTo, RandomOracle.reprogram]

@[simp] theorem programTo_of_ne {Enc D : Type} [DecidableEq Enc] (x : Enc) (y : D) (H : Enc → D)
    {z : Enc} (hz : z ≠ x) : programTo x y H z = H z := by
  simp [programTo, RandomOracle.reprogram, hz]

/--
**Programming forces the challenge.**

The simulator chooses a digest and patches the oracle at the derivation's input; the derived
challenge is then whatever that digest decodes to.  This is the whole content of "the simulator may
program the random oracle", and it is an equality — no probability appears.
-/
theorem derive_programTo {Enc D Chal Pre : Type} [DecidableEq Enc]
    (d : Derivation Enc D Chal Pre) (pre : Pre) (y : D) (H : Enc → D) :
    d.derive (programTo (d.input pre) y H) pre = d.decode y := by
  rw [Derivation.derive, programTo_apply]

/--
**A chosen challenge is reachable** whenever the decoding is onto — pick a digest above it.  For a
decoding that is a bijection (the usual case: the digest *is* the challenge sequence) this is
immediate.
-/
theorem derive_programTo_eq {Enc D Chal Pre : Type} [DecidableEq Enc]
    (d : Derivation Enc D Chal Pre) (pre : Pre) (H : Enc → D)
    {chal : Chal} {y : D} (hy : d.decode y = chal) :
    d.derive (programTo (d.input pre) y H) pre = chal := by
  rw [derive_programTo, hy]

/-! ## Undetectability, at the challenge input

Step 2's lemmas, at the singleton the simulator programs.  Nothing new is proved here; the point is
that the programmed set is a *single* input, so the detection event is one fresh hit.
-/

/-- The programmed oracle is step 2's `reprogram` at a singleton, so its lemmas apply verbatim. -/
theorem programTo_eq_reprogram {Enc D : Type} [DecidableEq Enc] (x : Enc) (y : D) (H : Enc → D) :
    programTo x y H = RandomOracle.reprogram {x} H (fun _ => y) := rfl

/-- **The distinguisher cannot tell, unless it queries the challenge input.** -/
theorem run_congr_off_challengeQueried {Enc D A : Type} [DecidableEq Enc] {fuel : ℕ}
    (x : Enc) (y : D) (H : Enc → D) (c : RandomOracle.Tree Enc D A fuel)
    (hmiss : ∀ qa ∈ (c.run H).2, qa.1 ≠ x) :
    c.run (programTo x y H) = c.run H := by
  refine RandomOracle.Tree.run_congr_off_programmed {x} H (fun _ => y) c ?_
  intro qa hqa
  simpa using hmiss qa hqa

/-! ## The composition -/

/--
**Programmed-simulator zero knowledge.**

Given honest-verifier closeness at the forced challenge (`hhvzk`) and a counting bound on detection
(`hview`, the programmed simulator agreeing with the honest-verifier one off `eps_prog` sample
points), the real transcript is `(eps_hvzk + eps_prog/|Ω|)`-close to the programmed simulator.

The two inputs are of different kinds on purpose.  `hhvzk` is a *distribution* statement, which
`Lfzk.ZkFiatShamir.nizk_zk_of_hvzk` supplies and which is *perfect* for Longfellow.  `hview` is a
*pointwise* statement off a bad set, which is what `run_congr_off_challengeQueried` produces and what
the fresh-hit counts bound.  So the whole Fiat–Shamir error is the detection term.
-/
theorem statClose_program {R Ω V : Type} [Fintype R] [Fintype Ω] [DecidableEq Ω] [DecidableEq V]
    {eps_hvzk : ℚ} {eps_prog : ℕ}
    {real : R → V} {hvzkSim progSim : Ω → V}
    (hhvzk : StatClose eps_hvzk real hvzkSim)
    (hview : RandomOracle.CountingClose eps_prog progSim hvzkSim) :
    StatClose (eps_hvzk + (eps_prog : ℚ) / Fintype.card Ω) real progSim :=
  hhvzk.trans (Lfzk.ZkMerkle.statClose_of_countingClose hview).symm

/--
**At perfect honest-verifier zero knowledge, the Fiat–Shamir error is exactly detection.**

`Lfzk.FromLigeroZK.V1.isLigeroZeroKnowledge_v1` gives `eps_hvzk = 0` and
`Lfzk.ZkFiatShamir.nizk_zk_of_perfect_hvzk` carries it onto the tape, so the simulator's only cost is
that the distinguisher might have queried the challenge input first.
-/
theorem statClose_program_perfect {R Ω V : Type} [Fintype R] [Fintype Ω] [DecidableEq Ω]
    [DecidableEq V] {eps_prog : ℕ}
    {real : R → V} {hvzkSim progSim : Ω → V}
    (hhvzk : StatClose 0 real hvzkSim)
    (hview : RandomOracle.CountingClose eps_prog progSim hvzkSim) :
    StatClose ((eps_prog : ℚ) / Fintype.card Ω) real progSim := by
  have h := statClose_program hhvzk hview
  simpa using h

/--
**Detection is the whole gap, and the bad set is a definition.**

When the two views are the distinguisher's *outputs* under the programmed and the real oracle, they
agree off `programQueried` — by step 2's lemma at the singleton.  So `statClose_program`'s `hview` is
not an assumption in this case: it is this theorem, with `eps_prog` the size of the detection event.

What remains construction-specific, and is *not* here, is that the simulator's messages are the ones
the honest-verifier simulator produces — that is what makes the real-oracle view the honest-verifier
view at the forced challenge, and it is a fact about a particular simulator rather than about
`Derivation`.
-/
theorem countingClose_program {Enc D A : Type} [DecidableEq Enc] [Fintype D] [DecidableEq D]
    [DecidableEq A] {fuel T : ℕ}
    (x : (Fin T → D) → Enc) (y : (Fin T → D) → D)
    (oracle : (Fin T → D) → Enc → D) (c : RandomOracle.Tree Enc D A fuel) :
    RandomOracle.CountingClose
      (RandomOracle.programQueried (fun ω => ({x ω} : Finset Enc)) oracle c).card
      (fun ω => (c.run (programTo (x ω) (y ω) (oracle ω))).1)
      (fun ω => (c.run (oracle ω)).1) :=
  RandomOracle.CountingClose.of_certificate
    { bad := RandomOracle.programQueried (fun ω => ({x ω} : Finset Enc)) oracle c
      bad_card := le_refl _
      agrees := fun ω hω => by
        have h := RandomOracle.run_congr_off_programQueried
          (fun ω => ({x ω} : Finset Enc)) oracle (fun ω _ => y ω) c ω hω
        rw [programTo_eq_reprogram, h] }

/-! ## The concrete Longfellow Fiat–Shamir simulator

Step 3's `statClose_program` named one obligation: that the simulator's messages are the ones the
honest-verifier simulator produces.  Exhibiting the simulator discharges it **definitionally** — the
simulated transcript *is* `Lfzk.simulate` at the challenge the simulator chose — and what that buys
is the property honest-verifier zero knowledge cannot give on its own:

> a verifier re-deriving the challenge from the simulated messages gets the challenge the simulated
> transcript contains.

That is `fsTranscript_consistent`.  Without programming it is false: the honest-verifier simulator
picks a challenge and messages for it, and nothing makes `H(messages)` equal that challenge.
-/

section Simulator

variable {ninp M nb : ℕ} {F Witness Chal LigProof SimRand : Type} [Field F]
variable {Enc D Pre : Type} [DecidableEq Enc]

/-- The simulator's coins: a digest to force the challenge to, the blinders, and Ligero's own. -/
structure SimCoins (D : Type) (nb : ℕ) (F : Type) (SimRand : Type) where
  /-- The digest the challenge input will be programmed to. -/
  chalDigest : D
  /-- The transmitted blinded values. -/
  blinders : Fin nb → F
  /-- Ligero's simulator randomness. -/
  ligero : SimRand

/--
**The simulated transcript.**  `Lfzk.simulate` at the challenge the simulator chose — so it never
sees a witness, and it is *literally* the honest-verifier simulator's output.
-/
noncomputable def fsTranscript
    (S : ZkSetup ninp M nb F Witness Chal)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (d : Derivation Enc D Chal Pre) (c : SimCoins D nb F SimRand) :
    ((Chal × (Fin nb → F)) × LigProof) :=
  simulate S sim (d.decode c.chalDigest) (c.blinders, c.ligero)

omit [DecidableEq Enc] in
/-- Discharging step 3's obligation: the simulated transcript is the honest-verifier simulator's
output, by definition.  Nothing is assumed about the simulator's messages because they *are* its
messages. -/
theorem fsTranscript_eq_simulate
    (S : ZkSetup ninp M nb F Witness Chal)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (d : Derivation Enc D Chal Pre) (c : SimCoins D nb F SimRand) :
    fsTranscript S sim d c
      = simulate S sim (d.decode c.chalDigest) (c.blinders, c.ligero) := rfl

omit [DecidableEq Enc] in
/-- The challenge the simulated transcript carries. -/
@[simp] theorem fsTranscript_chal
    (S : ZkSetup ninp M nb F Witness Chal)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (d : Derivation Enc D Chal Pre) (c : SimCoins D nb F SimRand) :
    (fsTranscript S sim d c).1.1 = d.decode c.chalDigest := rfl

/--
**The oracle the simulator hands over.**  The real one, patched at the single input the derivation
reads off the simulated messages.
-/
noncomputable def fsOracle
    (S : ZkSetup ninp M nb F Witness Chal)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (d : Derivation Enc D Chal Pre)
    (prefixOf : ((Chal × (Fin nb → F)) × LigProof) → Pre)
    (H : Enc → D) (c : SimCoins D nb F SimRand) : Enc → D :=
  programTo (d.input (prefixOf (fsTranscript S sim d c))) c.chalDigest H

/--
**The simulated transcript is consistent.**

Re-deriving the challenge from the simulated messages, under the oracle the simulator hands over,
returns the challenge the simulated transcript contains.  This is what makes it a *Fiat–Shamir*
simulator rather than an honest-verifier one, and it is exactly `derive_programTo`.
-/
theorem fsTranscript_consistent
    (S : ZkSetup ninp M nb F Witness Chal)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (d : Derivation Enc D Chal Pre)
    (prefixOf : ((Chal × (Fin nb → F)) × LigProof) → Pre)
    (H : Enc → D) (c : SimCoins D nb F SimRand) :
    d.derive (fsOracle S sim d prefixOf H c) (prefixOf (fsTranscript S sim d c))
      = (fsTranscript S sim d c).1.1 := by
  rw [fsTranscript_chal, fsOracle]
  exact derive_programTo d _ c.chalDigest H

/--
**The programmed oracle differs from the real one only at the challenge input.**  So a distinguisher
that never queries it sees the real oracle, which is what
`run_congr_off_challengeQueried` turns into an equality of views.
-/
theorem fsOracle_of_ne
    (S : ZkSetup ninp M nb F Witness Chal)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (d : Derivation Enc D Chal Pre)
    (prefixOf : ((Chal × (Fin nb → F)) × LigProof) → Pre)
    (H : Enc → D) (c : SimCoins D nb F SimRand) {z : Enc}
    (hz : z ≠ d.input (prefixOf (fsTranscript S sim d c))) :
    fsOracle S sim d prefixOf H c z = H z := by
  rw [fsOracle]
  exact programTo_of_ne _ _ _ hz

end Simulator

/-! ## Freshness: the real challenge is a uniform coin

The last piece is on the *honest prover's* side, not the simulator's.  For the simulator's chosen
challenge to match the real one in distribution, the real derivation must be **fresh** — the honest
prover's challenge input not queried earlier — so that the oracle answer there is a uniform coin.

Two forms, and the second is the one that composes.

* `Merkle.RandomOracle.answerTape_slot_eq_card` is the counting form: the tapes on which a slot takes
  a given value number exactly `|D|^(T-1)`, the same for every value.
* `statClose_tapeSplit` is the reindexing form: splitting the tape *at* the challenge slot exhibits
  the challenge digest as an independent coordinate.  Freshness is then not a probability estimate at
  all — it is the statement that the challenge is a coordinate, and reading it off the tape is the
  same experiment as sampling it.  That is the same move `blindEquiv` makes for the pad, and it costs
  `StatClose 0`.
-/

section Freshness

variable {D V : Type} [Fintype D] [DecidableEq D]

/-- Splitting the tape at one slot.  The first component is that slot; the second is the rest. -/
def tapeSplit (T : ℕ) (j : Fin T) : (Fin T → D) ≃ D × ({i : Fin T // i ≠ j} → D) :=
  Equiv.funSplitAt j D

omit [Fintype D] [DecidableEq D] in
@[simp] theorem tapeSplit_fst (T : ℕ) (j : Fin T) (tape : Fin T → D) :
    (tapeSplit T j tape).1 = tape j := rfl

omit [DecidableEq D] in
/--
**Reading a fresh challenge off the tape is the same experiment as sampling it.**

For any view that reads the tape only through (the challenge slot, the rest), the real experiment —
challenge read from the tape — and the sampled experiment — challenge drawn independently — are
*identical*, not merely close.  This is what freshness buys, and it is why the simulator may choose
the challenge.
-/
theorem statClose_tapeSplit (T : ℕ) (j : Fin T)
    (f : D → ({i : Fin T // i ≠ j} → D) → V) :
    StatClose 0
      (fun tape : Fin T → D => f (tape j) (tapeSplit T j tape).2)
      (fun p : D × ({i : Fin T // i ≠ j} → D) => f p.1 p.2) := by
  have h : ZkClose 0
      (fun tape : Fin T → D => f (tape j) (tapeSplit T j tape).2)
      (fun p : D × ({i : Fin T // i ≠ j} → D) => f p.1 p.2) :=
    zkClose_zero (tapeSplit T j) _ _ fun _ => rfl
  simpa using zkClose_statClose h

end Freshness

end Lfzk.ZkProgram
