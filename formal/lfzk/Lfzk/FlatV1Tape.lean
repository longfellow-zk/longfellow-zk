import Lfzk.FlatV1NoSat
import Bcs.TerminalPairTape

/-!
# A flat V1 terminal pair after Longfellow's field prefix

The built system, committed V1 oracle, role decoders, and response may all
depend on the preceding field answers.  Conditional on each such prefix,
the response-uniform V1 extraction envelope bounds the joint combination
challenge and opened-column query.  The field escape is counted separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkLigeroV1

open Finset LigeroFamily Lfzk.RbrZkLongfellow
open Ligero.Examples.Grid.LongfellowProfiledExtraction
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {w nw nq ninp M nt nlin : ℕ}

/-- A conditional flat V1 terminal estimate can be averaged over every
field-round prefix.  The response is allowed to inspect the *raw* terminal
challenge answer.  The estimate therefore composes with the deployed role
decoders without enumerating response messages. -/
theorem Result.v1_field_or_terminal_tape_ratio_le
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    (hfield : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (pl : Encode.Placement ninp M w nw nq nt)
    (hbound : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    {HashAnswer : Type} [Fintype HashAnswer] [Nonempty HashAnswer]
    (u : ℕ)
    (fieldEscape : (Fin u → HashAnswer) → Prop)
    (terminalGuard : (Fin u → HashAnswer) → Prop)
    (sysOf : (Fin u → HashAnswer) → LigeroSystem ninp M F)
    (oracleOf : (Fin u → HashAnswer) → Ligero.V1.Oracle F nw nq s.certificate.n 1)
    (decodeChallenge : (Fin u → HashAnswer) → HashAnswer →
      Ligero.V1.Challenge F nw nq 1
        (Fin nlin ⊕ (Fin nt × Encode.QSide)))
    (decodeQuery : (Fin u → HashAnswer) → HashAnswer →
      QuerySet s.certificate.n s.certificate.openings)
    (respond : (Fin u → HashAnswer) → HashAnswer →
      Response F s.certificate.openings w s.certificate.n 1)
    (hlin : ∀ pref, (sysOf pref).linear.length ≤ nlin)
    (hquad : ∀ pref, (sysOf pref).quad.length ≤ nt)
    (hno : ∀ pref, terminalGuard pref → NoSat
      (fun ℓ : SchemeLiftCandidate (s.code D hkn) (oracleOf pref)
        (s.certificate.e + s.certificate.g) =>
          Encode.decode pl ℓ.decodedMessages) (sysOf pref))
    (kchal kquery : ℕ)
    (hchal : ∀ pref challenge,
      (univ.filter fun c : HashAnswer =>
        decodeChallenge pref c = challenge).card ≤ kchal)
    (hquery : ∀ pref query,
      (univ.filter fun c : HashAnswer =>
        decodeQuery pref c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card (Ligero.V1.Challenge F nw nq 1
      (Fin nlin ⊕ (Fin nt × Encode.QSide))) ≤ Fintype.card HashAnswer)
    (hkquery : kquery * Fintype.card
      (QuerySet s.certificate.n s.certificate.openings) ≤ Fintype.card HashAnswer)
    (fieldBound : ℚ)
    (hfieldEscape : ((univ.filter fieldEscape).card : ℚ) /
      Fintype.card (Fin u → HashAnswer) ≤ fieldBound) :
    ((univ.filter fun tape : Fin (u + 2) → HashAnswer =>
      let p := Bcs.terminalPairEquiv u tape
      fieldEscape p.1 ∨
        (terminalGuard p.1 ∧
        (SchemeVerifier.policy
          (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
          (nw := nw) (nq := nq) (repetitions := 1)
          (s.code D hkn) Ligero.V1.scheme).accepts
          (Encode.encodeLig pl nlin (sysOf p.1))
          (decodeChallenge p.1 p.2.1) (respond p.1 p.2.1)
          (decodeQuery p.1 p.2.2)
          (openSchemeOracle (oracleOf p.1) (decodeQuery p.1 p.2.2)))).card : ℚ) /
        (Fintype.card HashAnswer : ℚ) ^ (u + 2) ≤
      fieldBound + (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  classical
  have hpair := Bcs.terminalPair_tape_ratio_le u fieldEscape
    (fun pref c d =>
      terminalGuard pref ∧
      (SchemeVerifier.policy
        (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (nw := nw) (nq := nq) (repetitions := 1)
        (s.code D hkn) Ligero.V1.scheme).accepts
        (Encode.encodeLig pl nlin (sysOf pref))
        (decodeChallenge pref c) (respond pref c)
        (decodeQuery pref d)
        (openSchemeOracle (oracleOf pref) (decodeQuery pref d)))
    fieldBound _ hfieldEscape
    (by
      intro pref
      by_cases hg : terminalGuard pref
      · simpa only [hg, true_and] using
          (Result.v1_hash_pair_acceptance_of_built_noSat s hp hv hfield hdim
            D hkn hrows pl (oracleOf pref) (sysOf pref)
            (hlin pref) (hquad pref) (hno pref hg) hbound
            (decodeChallenge pref) (decodeQuery pref) (respond pref)
            kchal kquery (hchal pref) (hquery pref))
      · have hnonneg : 0 ≤
          ((kchal * kquery : ℚ) *
            Fintype.card (Ligero.V1.Challenge F nw nq 1
              (Fin nlin ⊕ (Fin nt × Encode.QSide))) *
            Fintype.card (QuerySet s.certificate.n s.certificate.openings) /
              (Fintype.card HashAnswer : ℚ) ^ 2) *
            ((1 : ℚ) / 2 ^ s.certificate.targetBits) := by positivity
        simpa only [hg, false_and, Finset.filter_false, Finset.card_empty,
          Nat.cast_zero, zero_div] using hnonneg)
  have hfactor := Lfzk.ZkPotentialBalance.decoder_pair_factor_le_one
    kchal kquery hkchal hkquery
  have heps : 0 ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits := by positivity
  have hterm := mul_le_mul_of_nonneg_right hfactor heps
  calc
    _ ≤ fieldBound +
        ((kchal * kquery : ℚ) *
          Fintype.card (Ligero.V1.Challenge F nw nq 1
            (Fin nlin ⊕ (Fin nt × Encode.QSide))) *
          Fintype.card (QuerySet s.certificate.n s.certificate.openings) /
            (Fintype.card HashAnswer : ℚ) ^ 2) *
          ((1 : ℚ) / 2 ^ s.certificate.targetBits) := hpair
    _ ≤ fieldBound + (1 : ℚ) / 2 ^ s.certificate.targetBits := by
      simpa only [one_mul] using add_le_add_right hterm fieldBound

end Lfzk.ZkLigeroV1
