import Lfzk.Encode
import Lfzk.ZkSim
import Lfzk.LigeroZk.V1ResponseAdaptive
import LigeroFamily.Protocol.FiniteResponse

open Sumcheck

/-!
# `IsLigeroZeroKnowledge` is a theorem, at `eps_hide = 0` — Ligero V1

`ZkSim.lean` states `IsLigeroZeroKnowledge eps_hide realProof sim`: Ligero's real proof and its
simulation are `eps_hide`-indistinguishable.  `Ligero.V1.ZeroKnowledge`
(`Lfzk.LigeroZk.V1ResponseAdaptive`) **proves** the corresponding statement for the deployed
Ligero variant, V1, in the exact form `SameDistribution` — the two view distributions are *equal*,
not close.  So the hypothesis is discharged at `eps_hide = 0` and `longfellow_hvzk` becomes perfect
honest-verifier zero knowledge.

Ported from `proofs/lfzk/Lfzk/FromLigeroZK.lean`.  The first two sections (the
`SameDistribution → StatClose 0` translation and the protocol-agnostic bridge
`isLigeroZeroKnowledge_of_perfect`) are verbatim; the instantiation is re-done at **V1** (the
proofs file instantiates V3, which `formal/` does not carry).  V1, like V3, needs no masking-rate
side condition: its direct response-mask spaces contain every canonical-response difference.

## Scope

This is zero knowledge of the *oracle* protocol, with the statement fixed before the prover
commits.  The compiled argument (Merkle commitment, hashed challenges) and the Longfellow
schedule, in which the Ligero statement is built *after* the commitment, are
`Lfzk.CompiledLongfellowZk`.  The simulator is V1's response-adaptive one: the honest prover run
on a noncomputably chosen reference witness (`referenceMessages`).  That simulator is not
efficient, so the statement amounts to witness indistinguishability of the oracle protocol, not
zero knowledge with an efficient simulator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Classical
open LigeroFamily LigeroFamily.ZeroKnowledge

namespace Lfzk.FromLigeroZK

/-! ## Equal distributions are `0`-indistinguishable

`SameDistribution` counts tapes; `StatClose` compares probabilities of predicates.  At `eps = 0`
they say the same thing, and this is the translation.  It is stated without `Fintype` on the view
type — ligero's views carry a dependent `opening` field and no `Fintype` instance is declared for
them — so the fibrewise decomposition runs over the union of the two images instead of over all
of `T`.
-/

variable {R₁ R₂ T : Type} [Fintype R₁] [Fintype R₂] [DecidableEq T]

/-- The count of a predicate, decomposed over the fibres inside any finite set containing the
image. -/
private lemma card_eq_sum_viewCount (f : R₁ → T) (P : T → Prop) (A : Finset T)
    (hA : ∀ r, f r ∈ A) :
    (Finset.filter (fun r => P (f r)) Finset.univ).card
      = ∑ t ∈ A.filter P, viewCount f t := by
  have hmem : ∀ r ∈ Finset.filter (fun r => P (f r)) Finset.univ, f r ∈ A.filter P := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    exact Finset.mem_filter.mpr ⟨hA r, hr⟩
  refine (Finset.card_eq_sum_card_fiberwise hmem).trans (Finset.sum_congr rfl ?_)
  intro t ht
  simp only [Finset.mem_filter] at ht
  unfold viewCount
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ ht.2, h⟩⟩

/--
**Equal finite distributions are `0`-indistinguishable.**

`Nonempty` on both tapes is needed and not cosmetic: with an empty tape `probOf` is `0/0 = 0`
while `SameDistribution` degenerates to `0 = 0` and says nothing.
-/
theorem statClose_zero_of_sameDistribution [Nonempty R₁] [Nonempty R₂]
    {f : R₁ → T} {g : R₂ → T} (h : SameDistribution f g) : StatClose 0 f g := by
  have hc₁ : (0 : ℚ) < Fintype.card R₁ := by exact_mod_cast Fintype.card_pos (α := R₁)
  have hc₂ : (0 : ℚ) < Fintype.card R₂ := by exact_mod_cast Fintype.card_pos (α := R₂)
  -- the two normalised fibre counts agree at every outcome
  have hpt : ∀ t : T,
      (viewCount f t : ℚ) / Fintype.card R₁ = (viewCount g t : ℚ) / Fintype.card R₂ := by
    intro t
    have ht : (Fintype.card R₂ : ℚ) * viewCount f t = (Fintype.card R₁ : ℚ) * viewCount g t := by
      exact_mod_cast congrArg (Nat.cast (R := ℚ)) (h t)
    rw [div_eq_div_iff (ne_of_gt hc₁) (ne_of_gt hc₂)]
    linarith [ht]
  intro P
  have heq : probOf f P = probOf g P := by
    set A : Finset T := Finset.univ.image f ∪ Finset.univ.image g with hAdef
    have hAf : ∀ r, f r ∈ A := fun r =>
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))
    have hAg : ∀ r, g r ∈ A := fun r =>
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))
    rw [probOf, probOf, card_eq_sum_viewCount f P A hAf, card_eq_sum_viewCount g P A hAg]
    push_cast
    rw [Finset.sum_div, Finset.sum_div]
    exact Finset.sum_congr rfl (fun t _ => hpt t)
  rw [heq, sub_self, abs_zero]

end Lfzk.FromLigeroZK

/-! ## The bridge, protocol-agnostically

Nothing below mentions V3 until the last section.  `IsLigeroZeroKnowledge` asks for two families
indexed by an lfzk `LigeroSystem`; a perfect-zero-knowledge IPCP supplies them once the system and
the assignment are translated, and the translation is Phase 1's `satisfies_embed_of_sat`.
-/

namespace Lfzk.FromLigeroZK

open Lfzk.Encode

variable {ninp M : ℕ} {F : Type} [Field F]
variable {Statement Oracle Challenge Response Query Wit ProverCoins VerifierCoins
  SimulatorCoins : Type}
variable {Opening : Query → Type}

/--
**The generic bridge.**

Given a translation of lfzk systems into an IPCP's statements that carries satisfaction, perfect
zero knowledge of the IPCP is `IsLigeroZeroKnowledge` at `eps_hide = 0`.

`enc` and `asg` are abstract here: the only thing asked of them is `henc`, that an assignment
satisfying the lfzk system maps to a witness satisfying the encoded statement.  That is exactly
`Lfzk.Encode.satisfies_embed_of_sat`, and it is the whole content of the connection.
-/
theorem isLigeroZeroKnowledge_of_perfect
    [Fintype ProverCoins] [Fintype VerifierCoins] [Fintype SimulatorCoins]
    [Nonempty ProverCoins] [Nonempty VerifierCoins] [Nonempty SimulatorCoins]
    [DecidableEq (ResponseAdaptiveVerifierView VerifierCoins Challenge Response Query Opening)]
    (protocol : PublicCoinIPCP Statement Oracle Challenge Response Query Opening)
    (relation : Statement → Wit → Prop)
    (honestProver : Statement → Wit → ProverCoins → IPCPProver Statement Oracle Challenge Response)
    (verifier : ResponseAdaptiveVerifier VerifierCoins Challenge Response Query)
    (simulator : Statement → SimulatorCoins →
      ResponseAdaptiveVerifierView VerifierCoins Challenge Response Query Opening)
    (hzk : UnboundedPerfectResponseAdaptiveZeroKnowledgeAgainst protocol relation honestProver
      verifier simulator)
    (enc : LigeroSystem ninp M F → Statement)
    (asg : LigeroSystem ninp M F → (Fin ninp → F) → Pad M F → Wit)
    (henc : ∀ (cs : LigeroSystem ninp M F) (wcol : Fin ninp → F) (pad : Pad M F),
      cs.Sat wcol pad → relation (enc cs) (asg cs wcol pad)) :
    IsLigeroZeroKnowledge (ninp := ninp) (M := M) (F := F) 0
      (fun cs wcol pad =>
        randomizedResponseAdaptiveView protocol honestProver (enc cs) (asg cs wcol pad) verifier)
      (fun cs => simulator (enc cs)) where
  nonneg := le_refl 0
  close cs wcol pad hsat :=
    statClose_zero_of_sameDistribution (hzk (enc cs) (asg cs wcol pad) (henc cs wcol pad hsat))

end Lfzk.FromLigeroZK

/-! ## The V1 instantiation -/

namespace Lfzk.FromLigeroZK.V1

open Lfzk.Encode Ligero.V1 Ligero.V1.ZeroKnowledge

variable {ninp Mp nw nq nt nlin : ℕ}
variable {F : Type} [Field F] [Fintype F]
variable {VerifierCoins : Type} [Fintype VerifierCoins] [Nonempty VerifierCoins]
variable {r w n reps : ℕ}

/-- V1's prover tape is inhabited: every field is a function into a module.  `StatClose`
normalises by the tape size, so it is needed (on an empty tape `probOf` is `0/0`). -/
instance v1ProverRandomnessNonempty {C : MultiplicativeCode F r w n} :
    Nonempty (V1ProverRandomness C nw nq reps) :=
  ⟨{ corePadding := fun _ _ _ => 0
     linearMask := fun _ => 0
     quadraticMask := fun _ => 0
     proximityBlind := fun _ => 0 }⟩

noncomputable local instance v1ViewDecidableEq {Eqs : Type} :
    DecidableEq (ResponseAdaptiveVerifierView VerifierCoins
      (Challenge F nw nq reps Eqs) (LigeroFamily.Response F r w n reps)
      (QuerySet n r) (Opening F nw nq reps n r)) :=
  Classical.decEq _

/-- Ligero's real proof, as `IsLigeroZeroKnowledge` wants it: the response-adaptive view of an
honest V1 prover, run on the encoded system with the embedded assignment. -/
noncomputable def realProofV1 (C : MultiplicativeCode F r w n)
    (pl : Placement ninp Mp w nw nq nt) (nlin : ℕ)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq reps (Fin nlin ⊕ (Fin nt × QSide)))
      (LigeroFamily.Response F r w n reps) (QuerySet n r))
    (cs : LigeroSystem ninp Mp F) (wcol : Fin ninp → F) (pad : Pad Mp F) :
    (V1ProverRandomness C nw nq reps × VerifierCoins) →
      ResponseAdaptiveVerifierView VerifierCoins
        (Challenge F nw nq reps (Fin nlin ⊕ (Fin nt × QSide)))
        (LigeroFamily.Response F r w n reps) (QuerySet n r)
        (Opening F nw nq reps n r) :=
  randomizedResponseAdaptiveView
    (SchemeVerifier.protocol (Equations := Fin nlin ⊕ (Fin nt × QSide))
      (nw := nw) (nq := nq) (repetitions := reps) C scheme)
    (v1HonestProver C) (encodeLig pl nlin cs) (embedLig pl cs wcol pad) verifier

/-- Ligero V1's simulator, which never sees the assignment. -/
noncomputable def simV1 (C : MultiplicativeCode F r w n)
    (pl : Placement ninp Mp w nw nq nt) (nlin : ℕ)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq reps (Fin nlin ⊕ (Fin nt × QSide)))
      (LigeroFamily.Response F r w n reps) (QuerySet n r))
    (cs : LigeroSystem ninp Mp F) :
    (V1ProverRandomness C nw nq reps × VerifierCoins) →
      ResponseAdaptiveVerifierView VerifierCoins
        (Challenge F nw nq reps (Fin nlin ⊕ (Fin nt × QSide)))
        (LigeroFamily.Response F r w n reps) (QuerySet n r)
        (Opening F nw nq reps n r) :=
  v1ResponseAdaptiveSimulator (C := C) verifier (encodeLig pl nlin cs)

/--
**Ligero V1's hiding, discharged.**

`IsLigeroZeroKnowledge` at `eps_hide = 0`, for the V1 protocol at any multiplicative code, any
number of repetitions, any response-adaptive verifier and any placement.  There is no hypothesis:
V1's zero knowledge is unconditional, and the translation's side condition is
`satisfies_encodeLig`.
-/
theorem isLigeroZeroKnowledge_v1 (C : MultiplicativeCode F r w n)
    (pl : Placement ninp Mp w nw nq nt) (nlin : ℕ)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq reps (Fin nlin ⊕ (Fin nt × QSide)))
      (LigeroFamily.Response F r w n reps) (QuerySet n r)) :
    IsLigeroZeroKnowledge (ninp := ninp) (M := Mp) (F := F) 0
      (realProofV1 C pl nlin verifier) (simV1 C pl nlin verifier) :=
  isLigeroZeroKnowledge_of_perfect _ _ _ verifier _
    (v1_unbounded_perfect_response_adaptive_zero_knowledge (C := C)
      (nw := nw) (nq := nq) (repetitions := reps) verifier)
    (encodeLig pl nlin) (embedLig pl) (satisfies_encodeLig pl nlin)

/--
**Perfect honest-verifier zero knowledge for Longfellow at Ligero V1**, in the IPCP model.

`longfellow_hvzk` at `eps_hide = 0`: for every witness and every challenge sequence, no test
separates the real transcript from a simulation that never sees a witness.
-/
theorem longfellow_perfect_hvzk_v1 {nb : ℕ} {Witness Chal : Type}
    (C : MultiplicativeCode F r w n) (pl : Placement ninp Mp w nw nq nt) (nlin : ℕ)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq reps (Fin nlin ⊕ (Fin nt × QSide)))
      (LigeroFamily.Response F r w n reps) (QuerySet n r))
    (S : ZkSetup ninp Mp nb F Witness Chal) (wit : Witness) (chal : Chal) :
    StatClose 0
      (realTranscript S (realProofV1 C pl nlin verifier) wit chal)
      (simulate S (simV1 C pl nlin verifier) chal) :=
  longfellow_hvzk S _ _ (isLigeroZeroKnowledge_v1 C pl nlin verifier) wit chal

/-- **Perfect witness indistinguishability** at V1: two witnesses give *identically distributed*
transcripts. -/
theorem longfellow_perfect_wi_v1 {nb : ℕ} {Witness Chal : Type}
    (C : MultiplicativeCode F r w n) (pl : Placement ninp Mp w nw nq nt) (nlin : ℕ)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq reps (Fin nlin ⊕ (Fin nt × QSide)))
      (LigeroFamily.Response F r w n reps) (QuerySet n r))
    (S : ZkSetup ninp Mp nb F Witness Chal) (w₁ w₂ : Witness) (chal : Chal) :
    StatClose 0
      (realTranscript S (realProofV1 C pl nlin verifier) w₁ chal)
      (realTranscript S (realProofV1 C pl nlin verifier) w₂ chal) := by
  have h := longfellow_wi S (realProofV1 C pl nlin verifier) (simV1 C pl nlin verifier)
    (isLigeroZeroKnowledge_v1 C pl nlin verifier) w₁ w₂ chal
  simpa using h

end Lfzk.FromLigeroZK.V1
