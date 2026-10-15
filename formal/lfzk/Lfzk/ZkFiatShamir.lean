import Lfzk.ZkSim

/-!
# Step 1: the challenge as a function of the hash tape

`Lfzk.ZkSim`'s statements are honest-verifier: `realTranscript S realProof w chal` and
`simulate S sim chal` take the challenge sequence as an **argument**, identical on both sides, and
the theorems quantify over it.  A Fiat–Shamir NIZK derives the challenge from the transcript through
the hash, so the statement has to be about the *tape* instead.

This file makes that move and measures what it costs: **nothing.**

```text
nizkTranscript S realProof chalOf w  ω  =  realTranscript S realProof w (chalOf ω.1) ω.2
nizkSimulate   S sim      chalOf     ω  =  simulate      S sim      (chalOf ω.1) ω.2
```

over the joint space `(Fin T → D) × coins`, and `nizk_zk_of_hvzk` says these are `eps_hide`-close —
the same `eps_hide`, with no factor for the tape.  The reason is `statClose_mix`: the tape is *shared*
public randomness that both parties read, so a bound holding at every tape holds at the mixture.

## What this settles, and what it leaves

It settles that the sample-space move is free.  Whatever the difficulty of Fiat–Shamir zero
knowledge is, it is **not** that the challenge lives on a tape.

What it leaves is the *adaptivity*.  `chalOf : (Fin T → D) → Chal` is a **non-adaptive** derivation:
the challenge depends on the tape alone.  Longfellow's actual derivation is `chal = H(prefix)` where
the prefix contains the prover's own earlier messages, so it is really

```text
chalOf : (Fin T → D) → Prefix → Chal
```

and there the simulator is stuck: it cannot evaluate the derivation until it has produced the
messages, and it cannot produce the messages until it knows the challenge.  Breaking that circle is
what programming the oracle is for — the simulator picks the challenge, produces messages for it, and
*then* sets the oracle so the derivation agrees.

The tools are in place: `Merkle.RandomOracle.reprogram` programs an arbitrary input set, and
`Merkle.RandomOracle.run_congr_off_programQueried` says it is undetectable off a bad set that the
existing fresh-hit counts (`Merkle.MH.salt_hit_card_le`,
`Merkle.MH.leafCatch_prod_card_le`) already know how to bound.  Composing them with
`nizk_zk_of_hvzk` through `StatClose.trans` is the remaining step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkFiatShamir

variable {ninp M nb T : ℕ} {F Witness Chal LigProof LigRand SimRand D : Type}
variable [Field F] [Fintype F] [Fintype LigRand] [Fintype SimRand] [Fintype D]

/--
**The real Fiat–Shamir transcript.**  The challenge sequence is `chalOf` of the hash tape; the
remaining coins are the blinders and Ligero's prover randomness.
-/
noncomputable def nizkTranscript
    (S : ZkSetup ninp M nb F Witness Chal)
    (realProof : LigeroSystem ninp M F → (Fin ninp → F) → Pad M F → LigRand → LigProof)
    (chalOf : (Fin T → D) → Chal) (w : Witness) :
    ((Fin T → D) × ((Fin nb → F) × LigRand)) → ((Chal × (Fin nb → F)) × LigProof) :=
  fun ω => realTranscript S realProof w (chalOf ω.1) ω.2

/--
**The simulator, at the same derivation.**  It reads the tape exactly as the verifier does; it does
*not* program it.  That is the whole restriction this file operates under, and the reason the result
below is about a non-adaptive derivation.
-/
noncomputable def nizkSimulate
    (S : ZkSetup ninp M nb F Witness Chal)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (chalOf : (Fin T → D) → Chal) :
    ((Fin T → D) × ((Fin nb → F) × SimRand)) → ((Chal × (Fin nb → F)) × LigProof) :=
  fun ω => simulate S sim (chalOf ω.1) ω.2

set_option maxHeartbeats 1000000 in
/--
**Deriving the challenge from the tape is free.**

`longfellow_hvzk` holds at every challenge, so it holds at `chalOf tape` for every tape, so by
`statClose_mix` it holds jointly.  The bound is the *same* `eps_hide` — no factor for the tape, no
loss from the mixture.
-/
theorem nizk_zk_of_hvzk {eps_hide : ℚ}
    (S : ZkSetup ninp M nb F Witness Chal)
    (realProof : LigeroSystem ninp M F → (Fin ninp → F) → Pad M F → LigRand → LigProof)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (lzk : IsLigeroZeroKnowledge eps_hide realProof sim)
    (chalOf : (Fin T → D) → Chal) (w : Witness) :
    StatClose eps_hide
      (nizkTranscript (T := T) S realProof chalOf w)
      (nizkSimulate (T := T) S sim chalOf) :=
  statClose_mix (R₁ := Fin T → D) lzk.nonneg
    (fun tape p => realTranscript S realProof w (chalOf tape) p)
    (fun tape q => simulate S sim (chalOf tape) q)
    fun tape => longfellow_hvzk S realProof sim lzk w (chalOf tape)

set_option maxHeartbeats 1000000 in
/--
**Witness indistinguishability, on the tape.**  Two witnesses give transcripts `2·eps_hide`-close,
with no simulator in the statement — again with no loss from the mixture.
-/
theorem nizk_wi_of_hvzk {eps_hide : ℚ}
    (S : ZkSetup ninp M nb F Witness Chal)
    (realProof : LigeroSystem ninp M F → (Fin ninp → F) → Pad M F → LigRand → LigProof)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (lzk : IsLigeroZeroKnowledge eps_hide realProof sim)
    (chalOf : (Fin T → D) → Chal) (w₁ w₂ : Witness) :
    StatClose (eps_hide + eps_hide)
      (nizkTranscript (T := T) S realProof chalOf w₁)
      (nizkTranscript (T := T) S realProof chalOf w₂) :=
  statClose_mix (R₁ := Fin T → D) (add_nonneg lzk.nonneg lzk.nonneg)
    (fun tape p => realTranscript S realProof w₁ (chalOf tape) p)
    (fun tape q => realTranscript S realProof w₂ (chalOf tape) q)
    fun tape => longfellow_wi (SimRand := SimRand) S realProof sim lzk w₁ w₂ (chalOf tape)

set_option maxHeartbeats 1000000 in
/--
**At perfect oracle hiding, Fiat–Shamir on a tape is perfect too.**

`Lfzk.FromLigeroZK.V1.isLigeroZeroKnowledge_v1` gives `eps_hide = 0`, so the non-adaptive Fiat–Shamir
transcript is *exactly* simulatable.  This isolates the difficulty precisely: every bit of the
Fiat–Shamir zero-knowledge problem is the prefix-dependence of the real derivation, and none of it is
the tape.
-/
theorem nizk_zk_of_perfect_hvzk
    (S : ZkSetup ninp M nb F Witness Chal)
    (realProof : LigeroSystem ninp M F → (Fin ninp → F) → Pad M F → LigRand → LigProof)
    (sim : LigeroSystem ninp M F → SimRand → LigProof)
    (lzk : IsLigeroZeroKnowledge 0 realProof sim)
    (chalOf : (Fin T → D) → Chal) (w : Witness) :
    StatClose 0
      (nizkTranscript (T := T) S realProof chalOf w)
      (nizkSimulate (T := T) S sim chalOf) :=
  nizk_zk_of_hvzk S realProof sim lzk chalOf w

end Lfzk.ZkFiatShamir
