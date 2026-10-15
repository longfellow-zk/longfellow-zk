import Lfzk.Rounds
import Merkle.LazyTape
import Lfzk.ZkFiatShamir
import Lfzk.ZkProgram

/-!
# The end-to-end identification: Longfellow's own challenge schedule

`Lfzk.ZkFiatShamir` proved that deriving the challenge from a tape is free, for an *arbitrary*
`chalOf`.  This file instantiates it at Longfellow's actual derivation and schedule, so the
zero-knowledge statement is about the protocol rather than about a placeholder.

## The identification

Longfellow's challenges are the coin tape read at the schedule's slots: `Rounds.Role.readAt tape rl`
is `tape rl.index`.  And `Rounds.Role.indexEquiv` is a **bijection** — `index_inj` says no two rounds
share a slot, `card_role` says there are exactly as many rounds as slots.  So

> the challenge sequence *is* the tape, up to reindexing.

`roundChalEquiv` is that reindexing.  Two things follow, and they are the two halves of what the
previous files left open.

* **Freshness is structural, not probabilistic.**  `Lfzk.ZkProgram.statClose_tapeSplit` had to split a
  tape to exhibit *one* challenge as an independent coordinate.  Here every challenge is a coordinate
  already, and there is no remainder to split off — `Rounds.Role.slot_inj`, proved for the soundness
  argument, is exactly the freshness the zero-knowledge argument needs.  Distinct rounds read distinct
  slots, so no round's challenge is a function of another's.
* **The derivation is a bijection, so it is free.**  `longfellow_nizk_zk` is
  `ZkFiatShamir.nizk_zk_of_hvzk` at `chalOf := roundChal`, and no term is paid for the reindexing.

## What this is, and what it is not

This is Fiat–Shamir zero knowledge **in the coin-tape model** — the model `Bcs.Rbr` and
`Lfzk.Nizk.nizk_ratio_le_merkle` also live in, where a round's challenge is a tape coordinate.  It is
the same model the certified soundness statement uses, so the two halves of the top theorem are now
stated over the same object.

It is *not* the hash-oracle model, where a challenge is `H(prefix)` and the coin tape has to be shown
to be realized by hashing.  That bridge is `Merkle.RandomOracle.slotQuery_eq` — the query at slot `j`
is a function of the slots below it — and `Bcs.FiatShamir` already uses it for the grinding
*soundness* argument.  It is shared between soundness and zero knowledge and specific to neither, so
it is recorded here as the one remaining step rather than duplicated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkLongfellow

open Finset

variable {C : Type} [Fintype C] [DecidableEq C] {nl : ℕ} {w : ℕ → ℕ}
variable {ninp M nb : ℕ} {F Witness LigProof LigRand SimRand : Type}
variable [Field F] [Fintype F] [Fintype LigRand] [Fintype SimRand]

/-- Longfellow's challenge sequence: the coin tape, read at the schedule's slots. -/
def roundChal (tape : Fin (Rounds.Role.length nl w) → C) : Rounds.Role nl w → C :=
  fun rl => Rounds.Role.readAt tape rl

/--
**The challenge sequence is the tape.**

Reindexing along `Rounds.Role.indexEquiv`.  That this is an `Equiv` rather than merely an injection is
the content: `index_inj` gives distinctness — no two rounds share a slot — and `card_role` gives
surjectivity — no slot is unused.  So the schedule spends the tape exactly, and the challenge sequence
carries the same information.
-/
noncomputable def roundChalEquiv :
    (Fin (Rounds.Role.length nl w) → C) ≃ (Rounds.Role nl w → C) :=
  Equiv.arrowCongr (Rounds.Role.indexEquiv (nl := nl) (w := w)).symm (Equiv.refl C)

omit [Fintype C] [DecidableEq C] in
/-- The reindexing is the reading. -/
theorem roundChalEquiv_apply (tape : Fin (Rounds.Role.length nl w) → C) :
    roundChalEquiv (C := C) tape = roundChal tape := by
  funext rl
  simp [roundChalEquiv, roundChal, Rounds.Role.readAt, Rounds.Role.indexEquiv,
    Equiv.arrowCongr]

omit [DecidableEq C] in
/--
**Longfellow Fiat–Shamir zero knowledge, over the coin tape.**

`ZkFiatShamir.nizk_zk_of_hvzk` at Longfellow's own derivation: the real transcript, with every
challenge read off the tape at its scheduled slot, is `eps_hide`-close to a simulation that never sees
a witness.  No term is paid for putting the challenges on the tape — the derivation is a bijection.
-/
theorem longfellow_nizk_zk {eps_hide : ℚ}
    (S : ZkSetup ninp M nb F Witness (Rounds.Role nl w → C))
    (realProof : LigeroSystem ninp M F → (Fin ninp → F) → Pad M F → LigRand → LigProof)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (lzk : IsLigeroZeroKnowledge eps_hide realProof sim) (wit : Witness) :
    StatClose eps_hide
      (ZkFiatShamir.nizkTranscript (T := Rounds.Role.length nl w) S realProof roundChal wit)
      (ZkFiatShamir.nizkSimulate (T := Rounds.Role.length nl w) S sim roundChal) :=
  ZkFiatShamir.nizk_zk_of_hvzk S realProof sim lzk roundChal wit

omit [DecidableEq C] in
/--
**At perfect oracle hiding it is exact.**

`Lfzk.FromLigeroZK.V1.isLigeroZeroKnowledge_v1` gives `eps_hide = 0`, so in the coin-tape model
Longfellow's Fiat–Shamir transcript is *perfectly* simulatable.  Every cost of the compilation is
elsewhere: the Merkle commitment's hiding term (`Lfzk.ZkMerkle.verifierView_statClose`) and, in the
hash-oracle model, the programming-detection term (`Lfzk.ZkProgram.countingClose_program`).
-/
theorem longfellow_nizk_zk_perfect
    (S : ZkSetup ninp M nb F Witness (Rounds.Role nl w → C))
    (realProof : LigeroSystem ninp M F → (Fin ninp → F) → Pad M F → LigRand → LigProof)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (lzk : IsLigeroZeroKnowledge 0 realProof sim) (wit : Witness) :
    StatClose 0
      (ZkFiatShamir.nizkTranscript (T := Rounds.Role.length nl w) S realProof roundChal wit)
      (ZkFiatShamir.nizkSimulate (T := Rounds.Role.length nl w) S sim roundChal) :=
  longfellow_nizk_zk S realProof sim lzk wit

omit [DecidableEq C] in
/--
**Witness indistinguishability, at the same schedule.**
-/
theorem longfellow_nizk_wi {eps_hide : ℚ}
    (S : ZkSetup ninp M nb F Witness (Rounds.Role nl w → C))
    (realProof : LigeroSystem ninp M F → (Fin ninp → F) → Pad M F → LigRand → LigProof)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (lzk : IsLigeroZeroKnowledge eps_hide realProof sim) (w₁ w₂ : Witness) :
    StatClose (eps_hide + eps_hide)
      (ZkFiatShamir.nizkTranscript (T := Rounds.Role.length nl w) S realProof roundChal w₁)
      (ZkFiatShamir.nizkTranscript (T := Rounds.Role.length nl w) S realProof roundChal w₂) :=
  ZkFiatShamir.nizk_wi_of_hvzk (SimRand := SimRand) S realProof sim lzk roundChal w₁ w₂

/-! ## The bridge: the hashed challenges *are* the coin tape

Everything above is the coin-tape model.  This section closes the gap to the hash-oracle model, where
a challenge is the oracle's answer at a transcript prefix.

The content is `Merkle.RandomOracle.lazyRun_answer_eq_tape`: an execution's answers sit at their
queries' permanent slots, and for **distinct** queries in a known order those slots are `0, 1, 2, …`.
The honest Fiat–Shamir prover's queries are distinct — each round hashes a longer prefix — so its
answer sequence is the tape, coordinate for coordinate.

So the coin-tape model is *realised*, not assumed, and the realisation costs nothing: it is an
equality of answers, with no bad event and no term.  What the schedule contributes is the indexing —
`Rounds.Role.indexEquiv` says which slot each round reads, and `index_inj` that they are distinct.
-/

section Bridge

variable {Q A : Type} [DecidableEq Q]

omit [Fintype C] [DecidableEq C] in
/--
**Longfellow's hashed challenges are `roundChal` of the tape.**

Given the honest prover's prefix at each round (`qs`, injective — distinct prefixes) and that its
execution's distinct queries are exactly those prefixes in schedule order, the answer it receives at
round `rl` is `roundChal tape rl`.

This is the identification the coin-tape statements were waiting on: `longfellow_nizk_zk` is about
`roundChal`, and `roundChal` is what hashing produces.
-/
theorem roundChal_realized
    (tape : Fin (Rounds.Role.length nl w) → C) (dflt : C) {fuel : ℕ}
    (c : Merkle.RandomOracle.Tree Q C A fuel)
    (qs : Rounds.Role nl w → Q) (hinj : Function.Injective qs)
    (hseen : (Merkle.RandomOracle.lazyRun tape dflt c []).2.1
        = List.ofFn fun j => qs (Rounds.Role.indexEquiv.symm j))
    (rl : Rounds.Role nl w)
    {qa : Q × C} (hqa : qa ∈ (Merkle.RandomOracle.lazyRun tape dflt c []).2.2)
    (hq : qa.1 = qs rl) :
    qa.2 = roundChal tape rl := by
  have hinj' : Function.Injective fun j => qs (Rounds.Role.indexEquiv.symm j) :=
    hinj.comp (Rounds.Role.indexEquiv (nl := nl) (w := w)).symm.injective
  have hrl : Rounds.Role.indexEquiv.symm (Rounds.Role.index rl) = rl := by
    simp [Rounds.Role.indexEquiv]
  have hq' : qa.1 = (fun j => qs (Rounds.Role.indexEquiv.symm j)) (Rounds.Role.index rl) := by
    simp only [hrl]
    exact hq
  have h := Merkle.RandomOracle.lazyRun_answer_eq_tape tape dflt c _ hinj' hseen
    (k := Rounds.Role.index rl) (Rounds.Role.index rl).isLt hqa hq'
  rw [h, roundChal, Rounds.Role.readAt]

/--
**The honest prover's query program.**  One hash per round, at the round's prefix, in slot order.
`Merkle.RandomOracle.askFin` is the program; its fuel is exactly the tape length, which is the
schedule's own `Rounds.Role.length`.
-/
noncomputable def honestProgram (qs : Rounds.Role nl w → Q) :
    Merkle.RandomOracle.Tree Q C Unit (Rounds.Role.length nl w) :=
  Merkle.RandomOracle.askFin _ fun j => qs (Rounds.Role.indexEquiv.symm j)

omit [Fintype C] [DecidableEq C] in
/--
**The bridge, unconditionally.**

`roundChal_realized` with its `hseen` discharged: `Merkle.RandomOracle.lazyRun_seen_askFin` computes
the honest program's distinct queries to be exactly the schedule's prefixes in slot order.  So for a
prover that hashes one fresh prefix per round, the challenge it receives at round `rl` **is**
`roundChal tape rl` — no hypothesis, no bad event, no term.

With this the coin-tape statements (`longfellow_nizk_zk`, and `Lfzk.Nizk.nizk_ratio_le_merkle` on the
soundness side) are statements about the hashing protocol.
-/
theorem roundChal_realized_honest
    (tape : Fin (Rounds.Role.length nl w) → C) (dflt : C)
    (qs : Rounds.Role nl w → Q) (hinj : Function.Injective qs)
    (rl : Rounds.Role nl w) {qa : Q × C}
    (hqa : qa ∈ (Merkle.RandomOracle.lazyRun tape dflt (honestProgram qs) []).2.2)
    (hq : qa.1 = qs rl) :
    qa.2 = roundChal tape rl := by
  have hinj' : Function.Injective fun j => qs (Rounds.Role.indexEquiv.symm j) :=
    hinj.comp (Rounds.Role.indexEquiv (nl := nl) (w := w)).symm.injective
  refine roundChal_realized tape dflt (honestProgram qs) qs hinj ?_ rl hqa hq
  simpa [honestProgram] using
    Merkle.RandomOracle.lazyRun_seen_askFin tape dflt _
      (fun j => qs (Rounds.Role.indexEquiv.symm j)) [] (by simp) hinj'

end Bridge

end Lfzk.ZkLongfellow
