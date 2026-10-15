import Lfzk.Mac
import Lfzk.ZkSim

/-!
# Two-field consistency: zero knowledge

Theorem 9 of the paper, zero-knowledge half.  Two Longfellow arguments over two *different* fields,
sharing a witness and a MAC tag on it, are jointly simulatable:

```
StatClose (eps₁ + eps₂)  (the real two-field transcript)  (a simulation that never sees a witness)
```

and at Ligero V1's `eps_hide = 0` (`Lfzk.FromLigeroZK.V1.isLigeroZeroKnowledge_v1`) that is
`StatClose 0` — perfect.  (Ported verbatim from `proofs/lfzk/Lfzk/TwoFieldZk.lean`; docstrings
name the V1 instance.)

**The MAC contributes nothing.**  The paper's last hybrid is "the mac value `m` is randomly sampled
instead of computed using `w`… statistically close by the hiding property of the MAC".  It is a
*bijection*: `Lfzk.Mac.macBlindEquiv` says the tag is a translate of the prover's blind, so
`hybrid_tag` below is `StatClose 0`.  This is the same phenomenon as `blindEquiv` at the pad stage,
and it is why the two-field composition is free on the zero-knowledge side.

## How the paper's proof maps onto this file

| paper | here | cost |
|---|---|---|
| "the simulator for `Ĉ₁` is invoked using the same `k_v` and correct mac value `m`" | `statClose_parallel`, first `statClose_mix` | `eps₁` |
| "in the next hybrid, the same is done for `Ĉ₂`" | `statClose_parallel`, second `statClose_mix` | `eps₂` |
| "the mac value `m` is randomly sampled instead of computed using `w`" | `hybrid_tag`, via `macBlindEquiv` | **`0`** |
| the theorem | `twofield_hvzk` | `eps₁ + eps₂` |

`statClose_mix` is the right lemma for the two side hybrids rather than an approximation of one: the
verifier's key share `k_v` and the tag `m` are public randomness *both* parties read, which is the
case that lemma exists for.

## The tag rides in `Chal`

`ZkSetup.sys : Chal → (Fin nb → F) → LigeroSystem` takes its public data as `Chal`, and `m` is public
data both parties hold — Protocol 3.8 sends it in step 3b and then uses it as a public input to both
circuits.  So each side is instantiated at `Chal := Chalᵢ × (Fin nblk → Fmac)` and
`longfellow_hvzk` applies unchanged.  Nothing in `ZkSim.lean` needs to change.

## Where the general lemmas live

`statClose_map`, `statClose_reindex`, `statClose_zero_of_equiv` and `statClose_parallel` are about
`StatClose` and nothing else, so they live next to `statClose_mix` in `ZkHiding.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Classical

namespace Lfzk.TwoFieldZk

open Lfzk.Mac

/-! ## The `StatClose` plumbing lives upstream

`statClose_map`, `statClose_reindex`, `statClose_zero_of_equiv`, `Equiv.prodPullSnd`,
`Equiv.prodPullFst` and `statClose_parallel` are about `StatClose` and nothing else, so they sit
next to `statClose_mix` in `ZkHiding.lean`.  `statClose_parallel` is the hybrid argument of a
two-instance composition, done once; `hybrid_sides` below is its instance. -/

/-! ## Protocol 3.8

The parameters of one run.  `ap` and `av` are the two shares of the MAC multiplier and `bv` the
verifier's share of the blind; the prover's share of the blind is a *coin*, which is what makes the
tag uniform.  `msg` is the common witness, packed into `Fin nblk → Fmac` — see
`Lfzk.Mac.packBits`. -/

variable {Fmac : Type} [Field Fmac] [Fintype Fmac] {nblk : ℕ}
variable {ninp₁ M₁ nb₁ ninp₂ M₂ nb₂ : ℕ}
variable {F₁ F₂ : Type} [Field F₁] [Fintype F₁] [Field F₂] [Fintype F₂]
variable {Witness₁ Witness₂ Chal₁ Chal₂ : Type}
variable {LigProof₁ LigProof₂ : Type}
variable {LigRand₁ LigRand₂ SimRand₁ SimRand₂ : Type}
variable [Fintype LigRand₁] [Fintype LigRand₂] [Fintype SimRand₁] [Fintype SimRand₂]

/-- The tag the honest prover computes and sends (step 3b of Protocol 3.8): the MAC of the common
value at the jointly sampled key. -/
def tagOf (ap av : Fmac) (bv msg bp : Fin nblk → Fmac) : Fin nblk → Fmac :=
  macTag (ap + av) (bp + bv) msg

/--
**The real two-field transcript.**

Coins: the prover's blind share `bp`, then each side's blinders and Ligero randomness.  The output is
what the verifier sees — the tag, then each side's transcript, each carrying the tag in its public
data.
-/
noncomputable def twoFieldTranscript
    (S₁ : ZkSetup ninp₁ M₁ nb₁ F₁ Witness₁ (Chal₁ × (Fin nblk → Fmac)))
    (S₂ : ZkSetup ninp₂ M₂ nb₂ F₂ Witness₂ (Chal₂ × (Fin nblk → Fmac)))
    (realProof₁ : LigeroSystem ninp₁ M₁ F₁ → (Fin ninp₁ → F₁) → Pad M₁ F₁ → LigRand₁ → LigProof₁)
    (realProof₂ : LigeroSystem ninp₂ M₂ F₂ → (Fin ninp₂ → F₂) → Pad M₂ F₂ → LigRand₂ → LigProof₂)
    (ap av : Fmac) (bv msg : Fin nblk → Fmac)
    (w₁ : Witness₁) (w₂ : Witness₂) (chal₁ : Chal₁) (chal₂ : Chal₂) :
    (Fin nblk → Fmac) × (((Fin nb₁ → F₁) × LigRand₁) × ((Fin nb₂ → F₂) × LigRand₂)) →
      (Fin nblk → Fmac)
        × ((((Chal₁ × (Fin nblk → Fmac)) × (Fin nb₁ → F₁)) × LigProof₁)
          × (((Chal₂ × (Fin nblk → Fmac)) × (Fin nb₂ → F₂)) × LigProof₂)) :=
  fun p =>
    (tagOf ap av bv msg p.1,
     realTranscript S₁ realProof₁ w₁ (chal₁, tagOf ap av bv msg p.1) p.2.1,
     realTranscript S₂ realProof₂ w₂ (chal₂, tagOf ap av bv msg p.1) p.2.2)

/--
**The simulator.**  Sample the tag uniformly — never computing it from a witness — then run each
side's Ligero simulator on the system that tag determines.
-/
noncomputable def twoFieldSimulate
    (S₁ : ZkSetup ninp₁ M₁ nb₁ F₁ Witness₁ (Chal₁ × (Fin nblk → Fmac)))
    (S₂ : ZkSetup ninp₂ M₂ nb₂ F₂ Witness₂ (Chal₂ × (Fin nblk → Fmac)))
    (sim₁ : LigeroSystem ninp₁ M₁ F₁ → SimRand₁ → LigProof₁)
    (sim₂ : LigeroSystem ninp₂ M₂ F₂ → SimRand₂ → LigProof₂)
    (chal₁ : Chal₁) (chal₂ : Chal₂) :
    (Fin nblk → Fmac) × (((Fin nb₁ → F₁) × SimRand₁) × ((Fin nb₂ → F₂) × SimRand₂)) →
      (Fin nblk → Fmac)
        × ((((Chal₁ × (Fin nblk → Fmac)) × (Fin nb₁ → F₁)) × LigProof₁)
          × (((Chal₂ × (Fin nblk → Fmac)) × (Fin nb₂ → F₂)) × LigProof₂)) :=
  fun q =>
    (q.1,
     simulate S₁ sim₁ (chal₁, q.1) q.2.1,
     simulate S₂ sim₂ (chal₂, q.1) q.2.2)

/--
**The two side hybrids.**  Both sides replaced by their simulators, at the *correct* tag.  This is
the paper's first two hybrid steps, and it is `statClose_parallel` at `A := Fin nblk → Fmac`, the
prover's blind, which is shared between the two sides because the tag is.
-/
theorem hybrid_sides {eps₁ eps₂ : ℚ}
    (S₁ : ZkSetup ninp₁ M₁ nb₁ F₁ Witness₁ (Chal₁ × (Fin nblk → Fmac)))
    (S₂ : ZkSetup ninp₂ M₂ nb₂ F₂ Witness₂ (Chal₂ × (Fin nblk → Fmac)))
    (realProof₁ : LigeroSystem ninp₁ M₁ F₁ → (Fin ninp₁ → F₁) → Pad M₁ F₁ → LigRand₁ → LigProof₁)
    (realProof₂ : LigeroSystem ninp₂ M₂ F₂ → (Fin ninp₂ → F₂) → Pad M₂ F₂ → LigRand₂ → LigProof₂)
    (sim₁ : LigeroSystem ninp₁ M₁ F₁ → SimRand₁ → LigProof₁)
    (sim₂ : LigeroSystem ninp₂ M₂ F₂ → SimRand₂ → LigProof₂)
    (lzk₁ : IsLigeroZeroKnowledge eps₁ realProof₁ sim₁)
    (lzk₂ : IsLigeroZeroKnowledge eps₂ realProof₂ sim₂)
    (ap av : Fmac) (bv msg : Fin nblk → Fmac)
    (w₁ : Witness₁) (w₂ : Witness₂) (chal₁ : Chal₁) (chal₂ : Chal₂) :
    StatClose (eps₁ + eps₂)
      (twoFieldTranscript S₁ S₂ realProof₁ realProof₂ ap av bv msg w₁ w₂ chal₁ chal₂)
      (fun q : (Fin nblk → Fmac) × (((Fin nb₁ → F₁) × SimRand₁) × ((Fin nb₂ → F₂) × SimRand₂)) =>
        (tagOf ap av bv msg q.1,
         simulate S₁ sim₁ (chal₁, tagOf ap av bv msg q.1) q.2.1,
         simulate S₂ sim₂ (chal₂, tagOf ap av bv msg q.1) q.2.2)) :=
  statClose_parallel lzk₁.nonneg lzk₂.nonneg
    (fun bp b₁ b₂ => (tagOf ap av bv msg bp, b₁, b₂))
    (fun bp => realTranscript S₁ realProof₁ w₁ (chal₁, tagOf ap av bv msg bp))
    (fun bp => simulate S₁ sim₁ (chal₁, tagOf ap av bv msg bp))
    (fun bp => realTranscript S₂ realProof₂ w₂ (chal₂, tagOf ap av bv msg bp))
    (fun bp => simulate S₂ sim₂ (chal₂, tagOf ap av bv msg bp))
    (fun bp => longfellow_hvzk S₁ realProof₁ sim₁ lzk₁ w₁ (chal₁, tagOf ap av bv msg bp))
    (fun bp => longfellow_hvzk S₂ realProof₂ sim₂ lzk₂ w₂ (chal₂, tagOf ap av bv msg bp))

/--
**The tag hybrid, at cost `0`.**

Replacing the computed tag by a uniform one is a *relabelling of the prover's blind*, because
`bp ↦ macTag (ap + av) (bp + bv) msg` is `Lfzk.Mac.macBlindEquiv`, a bijection.  So this step is
exact, and the paper's "statistically close by the hiding property of the MAC" is in fact perfect.

Note where the blind is needed: `Lfzk.TwoFieldExample.noBlind_not_surjective` shows that with the
blind dropped — footnote 5's optimisation — this map is not surjective at `nblk ≥ 2` and the step
fails.
-/
theorem hybrid_tag
    (S₁ : ZkSetup ninp₁ M₁ nb₁ F₁ Witness₁ (Chal₁ × (Fin nblk → Fmac)))
    (S₂ : ZkSetup ninp₂ M₂ nb₂ F₂ Witness₂ (Chal₂ × (Fin nblk → Fmac)))
    (sim₁ : LigeroSystem ninp₁ M₁ F₁ → SimRand₁ → LigProof₁)
    (sim₂ : LigeroSystem ninp₂ M₂ F₂ → SimRand₂ → LigProof₂)
    (ap av : Fmac) (bv msg : Fin nblk → Fmac) (chal₁ : Chal₁) (chal₂ : Chal₂) :
    StatClose 0
      (fun q : (Fin nblk → Fmac) × (((Fin nb₁ → F₁) × SimRand₁) × ((Fin nb₂ → F₂) × SimRand₂)) =>
        (tagOf ap av bv msg q.1,
         simulate S₁ sim₁ (chal₁, tagOf ap av bv msg q.1) q.2.1,
         simulate S₂ sim₂ (chal₂, tagOf ap av bv msg q.1) q.2.2))
      (twoFieldSimulate S₁ S₂ sim₁ sim₂ chal₁ chal₂) :=
  statClose_zero_of_equiv
    ((macBlindEquiv (ap + av) bv msg).prodCongr (Equiv.refl _))
    (fun _ => rfl)

/--
**Theorem 9, zero-knowledge half.**

For every pair of witnesses, every common value, every key share and every challenge sequence, no
test distinguishes the real two-field transcript from a simulation that never sees a witness with
advantage more than `eps₁ + eps₂`.

The MAC adds **nothing**: the bound is the sum of the two instances' own zero-knowledge errors.
-/
theorem twofield_hvzk {eps₁ eps₂ : ℚ}
    (S₁ : ZkSetup ninp₁ M₁ nb₁ F₁ Witness₁ (Chal₁ × (Fin nblk → Fmac)))
    (S₂ : ZkSetup ninp₂ M₂ nb₂ F₂ Witness₂ (Chal₂ × (Fin nblk → Fmac)))
    (realProof₁ : LigeroSystem ninp₁ M₁ F₁ → (Fin ninp₁ → F₁) → Pad M₁ F₁ → LigRand₁ → LigProof₁)
    (realProof₂ : LigeroSystem ninp₂ M₂ F₂ → (Fin ninp₂ → F₂) → Pad M₂ F₂ → LigRand₂ → LigProof₂)
    (sim₁ : LigeroSystem ninp₁ M₁ F₁ → SimRand₁ → LigProof₁)
    (sim₂ : LigeroSystem ninp₂ M₂ F₂ → SimRand₂ → LigProof₂)
    (lzk₁ : IsLigeroZeroKnowledge eps₁ realProof₁ sim₁)
    (lzk₂ : IsLigeroZeroKnowledge eps₂ realProof₂ sim₂)
    (ap av : Fmac) (bv msg : Fin nblk → Fmac)
    (w₁ : Witness₁) (w₂ : Witness₂) (chal₁ : Chal₁) (chal₂ : Chal₂) :
    StatClose (eps₁ + eps₂)
      (twoFieldTranscript S₁ S₂ realProof₁ realProof₂ ap av bv msg w₁ w₂ chal₁ chal₂)
      (twoFieldSimulate S₁ S₂ sim₁ sim₂ chal₁ chal₂) := by
  have h := (hybrid_sides S₁ S₂ realProof₁ realProof₂ sim₁ sim₂ lzk₁ lzk₂
    ap av bv msg w₁ w₂ chal₁ chal₂).trans
      (hybrid_tag S₁ S₂ sim₁ sim₂ ap av bv msg chal₁ chal₂)
  simpa using h

/-- **At perfect oracle hiding it is exact.**  `Lfzk.FromLigeroZK.V1.isLigeroZeroKnowledge_v1` gives
`eps_hide = 0` on each side, so the two-field transcript is *perfectly* simulatable. -/
theorem twofield_hvzk_perfect
    (S₁ : ZkSetup ninp₁ M₁ nb₁ F₁ Witness₁ (Chal₁ × (Fin nblk → Fmac)))
    (S₂ : ZkSetup ninp₂ M₂ nb₂ F₂ Witness₂ (Chal₂ × (Fin nblk → Fmac)))
    (realProof₁ : LigeroSystem ninp₁ M₁ F₁ → (Fin ninp₁ → F₁) → Pad M₁ F₁ → LigRand₁ → LigProof₁)
    (realProof₂ : LigeroSystem ninp₂ M₂ F₂ → (Fin ninp₂ → F₂) → Pad M₂ F₂ → LigRand₂ → LigProof₂)
    (sim₁ : LigeroSystem ninp₁ M₁ F₁ → SimRand₁ → LigProof₁)
    (sim₂ : LigeroSystem ninp₂ M₂ F₂ → SimRand₂ → LigProof₂)
    (lzk₁ : IsLigeroZeroKnowledge 0 realProof₁ sim₁)
    (lzk₂ : IsLigeroZeroKnowledge 0 realProof₂ sim₂)
    (ap av : Fmac) (bv msg : Fin nblk → Fmac)
    (w₁ : Witness₁) (w₂ : Witness₂) (chal₁ : Chal₁) (chal₂ : Chal₂) :
    StatClose 0
      (twoFieldTranscript S₁ S₂ realProof₁ realProof₂ ap av bv msg w₁ w₂ chal₁ chal₂)
      (twoFieldSimulate S₁ S₂ sim₁ sim₂ chal₁ chal₂) := by
  have h := twofield_hvzk S₁ S₂ realProof₁ realProof₂ sim₁ sim₂ lzk₁ lzk₂
    ap av bv msg w₁ w₂ chal₁ chal₂
  simpa using h

/--
**Witness indistinguishability, with no simulator in the statement.**

Two pairs of witnesses *and two different common values* give transcripts
`2·(eps₁ + eps₂)`-indistinguishable — `0` at Ligero V1.  That the common value may differ is the point:
it is what says the MAC tag does not leak it.
-/
theorem twofield_wi {eps₁ eps₂ : ℚ}
    (S₁ : ZkSetup ninp₁ M₁ nb₁ F₁ Witness₁ (Chal₁ × (Fin nblk → Fmac)))
    (S₂ : ZkSetup ninp₂ M₂ nb₂ F₂ Witness₂ (Chal₂ × (Fin nblk → Fmac)))
    (realProof₁ : LigeroSystem ninp₁ M₁ F₁ → (Fin ninp₁ → F₁) → Pad M₁ F₁ → LigRand₁ → LigProof₁)
    (realProof₂ : LigeroSystem ninp₂ M₂ F₂ → (Fin ninp₂ → F₂) → Pad M₂ F₂ → LigRand₂ → LigProof₂)
    (sim₁ : LigeroSystem ninp₁ M₁ F₁ → SimRand₁ → LigProof₁)
    (sim₂ : LigeroSystem ninp₂ M₂ F₂ → SimRand₂ → LigProof₂)
    (lzk₁ : IsLigeroZeroKnowledge eps₁ realProof₁ sim₁)
    (lzk₂ : IsLigeroZeroKnowledge eps₂ realProof₂ sim₂)
    (ap av : Fmac) (bv msg msg' : Fin nblk → Fmac)
    (w₁ w₁' : Witness₁) (w₂ w₂' : Witness₂) (chal₁ : Chal₁) (chal₂ : Chal₂) :
    StatClose ((eps₁ + eps₂) + (eps₁ + eps₂))
      (twoFieldTranscript S₁ S₂ realProof₁ realProof₂ ap av bv msg w₁ w₂ chal₁ chal₂)
      (twoFieldTranscript S₁ S₂ realProof₁ realProof₂ ap av bv msg' w₁' w₂' chal₁ chal₂) :=
  (twofield_hvzk (SimRand₁ := SimRand₁) (SimRand₂ := SimRand₂)
      S₁ S₂ realProof₁ realProof₂ sim₁ sim₂ lzk₁ lzk₂ ap av bv msg w₁ w₂ chal₁ chal₂).trans
    (twofield_hvzk (SimRand₁ := SimRand₁) (SimRand₂ := SimRand₂)
      S₁ S₂ realProof₁ realProof₂ sim₁ sim₂ lzk₁ lzk₂ ap av bv msg' w₁' w₂' chal₁ chal₂).symm

end Lfzk.TwoFieldZk
