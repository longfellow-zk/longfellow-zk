import Lfzk.CompiledLongfellowZk
import Lfzk.Encode
import Lfzk.ZkSim

/-!
# The sumcheck front end, built from `ZkSetup` and a causal Fiat–Shamir transcript

`Lfzk.CompiledLongfellowZk.compiled_longfellow_zk` is stated over an abstract `Frontend`: the
committed tableau, the honest Fiat–Shamir transmission (a bijection in the blinders), and the
Ligero statement built from the transcript.  This file builds that `Frontend` from the objects the
honest-verifier development already has (`ZkSim.lean`):

* a `ZkSetup` — the honest pre-blinding values `honest w chal`, the pad `padOf b`, the committed
  input columns `wcol`, the system `sys chal t` and `honest_sat`;
* a **causal** challenge derivation `chalOf Gr κ t` — the challenges the verifier recomputes from
  the round oracle, the context and the transmission;
* the Ligero encoding (`Lfzk.Encode`: a `Placement` and `encodeLig`).

## The honest Fiat–Shamir prover is the solution of a triangular system

With Fiat–Shamir the honest prover's transmission solves `t = blindEquiv (honest w (chalOf Gr κ t)) b`:
each blinded value is the honest value at challenges derived from the transmission so far, minus a
blinder.  `CausalFS.causal` says exactly that the honest value at coordinate `j`, read at the
challenges derived from `t`, depends on `t` only below `j`'s rank (the round it is sent in); it holds
for any derivation that hashes the transcript prefix and any honest prover whose round-`k` message
depends on challenges drawn before round `k`.  Then `t ↦ honest w (chalOf Gr κ t) − t` is
injective (strong induction on the rank), hence a bijection, and its inverse **is** the honest
transmission (`transmit`, characterised by `transmit_spec`).  This is the triangular bijection the
README of `ZkSetup` anticipated ("still a bijection, but proved by induction over rounds rather than
by `blindEquiv`").

## What is assumed

* `causal` (the round structure, above);
* `hwcol` — the committed input columns do not depend on the challenges (`ZkProver::commit` fixes
  them before the transcript exists; on the ZK path `logc = 0`, so there is no copy point);
* `htri` — the system's triples are fixed (they are the per-layer pad triples
  `(dwL, dwR, dwLR)`, public and independent of the transcript; `zkSetupOfRun_presentTri` proves it
  for `zkSetupOfRun`), so the committed tableau `embed pl tri …` is statement-independent.

`honest_sat` of the `Frontend` is then `ZkSetup.honest_sat` read through `transmit_spec` and
`satisfies_encodeLig` — derived, not assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Lfzk.ZkFrontendOfSetup

open LigeroFamily Lfzk.Encode Lfzk.CompiledLongfellowZk

variable {ninp M nb : ℕ} {F Witness Chal : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **A Fiat–Shamir challenge derivation, causal for the honest transmission.**  `rank j` is the
round in which coordinate `j` of the transmission is sent; the honest value at `j`, at the challenges
derived from `t`, depends on `t` only at coordinates of smaller rank. -/
structure CausalFS (S : ZkSetup ninp M nb F Witness Chal) (Ctx RO : Type) where
  chalOf : RO → Ctx → (Fin nb → F) → Chal
  rank : Fin nb → ℕ
  causal : ∀ (wit : Witness) (Gr : RO) (κ : Ctx) (t t' : Fin nb → F) (j : Fin nb),
    (∀ i, rank i < rank j → t i = t' i) →
      S.honest wit (chalOf Gr κ t) j = S.honest wit (chalOf Gr κ t') j

variable {Ctx RO : Type} (S : ZkSetup ninp M nb F Witness Chal) (fs : CausalFS S Ctx RO)

/-- Transmission ↦ blinders: `b = honest(chalOf t) − t`. -/
def unblind (wit : Witness) (Gr : RO) (κ : Ctx) (t : Fin nb → F) : Fin nb → F :=
  (blindEquiv (S.honest wit (fs.chalOf Gr κ t))).symm t

/-- **Triangularity**: `unblind` is injective, by strong induction on the rank. -/
theorem unblind_injective (wit : Witness) (Gr : RO) (κ : Ctx) :
    Function.Injective (unblind S fs wit Gr κ) := by
  intro t t' h
  have key : ∀ k, ∀ j, fs.rank j = k → t j = t' j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro j hjk
      have hlow : ∀ i, fs.rank i < fs.rank j → t i = t' i :=
        fun i hi => ih (fs.rank i) (hjk ▸ hi) i rfl
      have hh := fs.causal wit Gr κ t t' j hlow
      have hj := congrFun h j
      simp only [unblind, blindEquiv_symm_apply] at hj
      rw [hh] at hj
      exact sub_right_injective hj
  funext j
  exact key _ j rfl

/-- `unblind` as a bijection of the (finite) transmission space onto the blinders. -/
noncomputable def unblindEquiv (wit : Witness) (Gr : RO) (κ : Ctx) : (Fin nb → F) ≃ (Fin nb → F) :=
  Equiv.ofBijective (unblind S fs wit Gr κ) (unblind_injective S fs wit Gr κ).bijective_of_finite

/-- **The honest Fiat–Shamir transmission**: the unique solution of the triangular system. -/
noncomputable def transmit (wit : Witness) (Gr : RO) (κ : Ctx) (b : Fin nb → F) : Fin nb → F :=
  (unblindEquiv S fs wit Gr κ).symm b

/-- The honest transmission is the honest values at the challenges derived from it, blinded. -/
theorem transmit_spec (wit : Witness) (Gr : RO) (κ : Ctx) (b : Fin nb → F) :
    transmit S fs wit Gr κ b
      = blindEquiv (S.honest wit (fs.chalOf Gr κ (transmit S fs wit Gr κ b))) b := by
  have h : unblind S fs wit Gr κ (transmit S fs wit Gr κ b) = b :=
    (unblindEquiv S fs wit Gr κ).apply_symm_apply b
  unfold unblind at h
  exact (Equiv.symm_apply_eq _).mp h

theorem transmit_bijective (wit : Witness) (Gr : RO) (κ : Ctx) :
    Function.Bijective (transmit S fs wit Gr κ) :=
  (unblindEquiv S fs wit Gr κ).symm.bijective

variable {w nw nq nt : ℕ}

/--
**The `Frontend` of a `ZkSetup`.**  The committed tableau is the witness columns and the pad at
the fixed triple layout `tri`; the transmission is the honest Fiat–Shamir one; the Ligero statement
is `encodeLig` of the system at the derived challenges.  Every input is valid (`ZkSetup.honest_sat`
holds for every witness: the public data is part of `S`).
-/
noncomputable def frontendOfSetup (pl : Placement ninp M w nw nq nt) (nlin : ℕ)
    (wcol₀ : Witness → Fin ninp → F) (hwcol : ∀ wit chal, S.wcol wit chal = wcol₀ wit)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M))
    (htri : ∀ chal t, presentTri nt (S.sys chal t) = tri) :
    Frontend F nw nq w (Fin nlin ⊕ (Fin nt × QSide)) Ctx Witness (Fin nb → F) (Fin nb → F) RO where
  msgs wit b := embed pl tri (Sum.elim (wcol₀ wit) (S.padOf b))
  transmit := transmit S fs
  transmit_bijective := transmit_bijective S fs
  stmt Gr κ t := encodeLig pl nlin (S.sys (fs.chalOf Gr κ t) t)
  Valid _ _ := True
  honest_sat wit Gr κ b _ := by
    have hsat := S.honest_sat wit (fs.chalOf Gr κ (transmit S fs wit Gr κ b)) b
    rw [← transmit_spec, hwcol] at hsat
    have h := satisfies_encodeLig pl nlin
      (S.sys (fs.chalOf Gr κ (transmit S fs wit Gr κ b)) (transmit S fs wit Gr κ b))
      (wcol₀ wit) (S.padOf b) hsat
    simpa only [embedLig, htri] using h

/-! ## `zkSetupOfRun` has fixed triples -/

section Run

variable [SumcheckInterp F] {Circuit Input Witness' : Type}

/-- The triples of `zkSetupOfRun`'s system are the layers' `(dwL, dwR, dwLR)` pad slots, whatever
the challenges and the transmission: the `htri` hypothesis of `frontendOfSetup` holds for the whole
`nl`-layer run. -/
theorem zkSetupOfRun_presentTri {ninp npub logw nl M nb nt : ℕ}
    (R : RunPad logw nl M nb F) (last : Fin nl)
    (eqq : RunChal logw nl F → Fin nl → F)
    (P : Witness' → RunChal logw nl F → Fin nl → Fin (2 * logw) → Polynomial F)
    (wl wr : Witness' → RunChal logw nl F → Fin nl → F)
    (wcolOf : Witness' → RunChal logw nl F → Fin ninp → F)
    (bcoef : RunChal logw nl F → Fin ninp → F) (pub_binding : RunChal logw nl F → F)
    (hpub hmle hclaim) (c : RunChal logw nl F) (t : Fin nb → F) :
    presentTri nt
        ((zkSetupOfRun (npub := npub) R last eqq P wl wr wcolOf bcoef pub_binding
          hpub hmle hclaim).sys c t)
      = fun j => (List.ofFn fun ly : Fin nl =>
          ((R.slots ly).ivL, (R.slots ly).ivR, (R.slots ly).ivLR))[j.val]? := by
  funext j
  simp only [presentTri, zkSetupOfRun, buildSystemMulti, List.map_ofFn]
  rfl

end Run

/-! ## The headline at a `ZkSetup` -/

section Headline

open Merkle Merkle.MH Lfzk.ZkAdaptiveV1

variable {r n reps : ℕ}
variable {Salt D Enc Coin LQ V : Type}
variable [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D] [Inhabited D]
variable [DecidableEq Enc] [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
variable [Fintype LQ] [DecidableEq LQ] [Fintype RO] [DecidableEq V]

/--
**Compiled Longfellow zero knowledge at a `ZkSetup`.**  `compiled_longfellow_zk` at
`frontendOfSetup`: the honest Fiat–Shamir prover of the setup (its transmission the solution of the
triangular system), committed with V1 and Merkle, is `openingEps`-close to the witness-free
simulator, for **every** witness (every input is valid: the public data is part of `S`).
-/
theorem compiled_longfellow_zk_of_setup (C : MultiplicativeCode F r w n)
    (Cod : Codec Salt (Col F nw nq reps) D Enc) (hinjC : Cod.Inj)
    (pl : Placement ninp M w nw nq nt) (nlin : ℕ)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps (Fin nlin ⊕ (Fin nt × QSide)))
    (dec₂ : Coin → QuerySet n r)
    (wcol₀ : Witness → Fin ninp → F) (hwcol : ∀ wit chal, S.wcol wit chal = wcol₀ wit)
    (tri : Fin nt → Option (Fin M × Fin M × Fin M))
    (htri : ∀ chal t, presentTri nt (S.sys chal t) = tri)
    (ctx : D → Ctx) (pts : Points Ctx (Fin nb → F) Coin (LigeroFamily.Response F r w n reps) LQ)
    (wit : Witness) (hn : 0 < n) {T f : ℕ} (hT : 2 * n - 1 + f ≤ T)
    (dist : Distinguisher F r w n nw nq reps Salt D Enc (Fin nb → F) Coin LQ RO V f) :
    StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n f T (n - r)
        (Fintype.card (HidingSample n T Salt D)))
      (realExp C Cod dec₁ dec₂ (frontendOfSetup S fs pl nlin wcol₀ hwcol tri htri) ctx pts wit
        (T := T) dist)
      (simExp C Cod dec₁ dec₂ (frontendOfSetup S fs pl nlin wcol₀ hwcol tri htri).stmt ctx pts
        (T := T) dist) :=
  compiled_longfellow_zk C Cod dec₁ dec₂ _ ctx pts wit hinjC (fun _ => trivial) (n - r)
    (fun q => (unopened_card q).le) hn hT dist

end Headline

end Lfzk.ZkFrontendOfSetup
