import Lfzk.ZkLigeroV1
import examples.Ligero.Longfellow.ProfiledExtraction

/-!
# Flat V1 acceptance at a built Longfellow system

The scalar-gap extraction certificate supplies one response-uniform envelope
over the combination challenge and opened-column query.  If no lift at the
certificate's radius satisfies the built system, the extractor returns none
for every response.  The same envelope then bounds raw V1 acceptance at the
encoded statement, without charging the challenge and query separately.

This is a proof bridge.  Concrete optimized Hahn certificates can be imported
by a separate target, leaving routine Longfellow builds independent of their
numerical checks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkLigeroV1

open Finset LigeroFamily Lfzk.RbrZkLongfellow
open Ligero.Examples.Grid.LongfellowProfiledExtraction
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {w nw nq ninp M nt nlin : ℕ}

omit [Fintype F] in
/-- A failed built-system extraction implies the no-decoded-solution premise
of the V1 flat acceptance certificate, at that certificate's actual radius. -/
theorem Result.noDecoded_of_built_noSat
    (s : Result)
    (pl : Encode.Placement ninp M w nw nq nt)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (O : Ligero.V1.Oracle F nw nq s.certificate.n 1)
    (sys : LigeroSystem ninp M F)
    (hlin : sys.linear.length ≤ nlin) (hquad : sys.quad.length ≤ nt)
    (hno : NoSat
      (fun ℓ : SchemeLiftCandidate (s.code D hkn) O
        (s.certificate.e + s.certificate.g) => Encode.decode pl ℓ.decodedMessages) sys) :
    NoDecodedSolution (s.code D hkn) O
      (s.certificate.e + s.certificate.g) (Encode.encodeLig pl nlin sys) := by
  intro ℓ hsat
  exact hno ℓ (Encode.sat_decode_encodeLig pl hlin hquad _ hsat)

/-- The certified flat, response-uniform Ligero V1 envelope at the system
built by Longfellow's field rounds.  `NoSat` refers to the same committed
lift list and radius as the certificate. -/
theorem Result.v1_uniform_acceptance_of_built_noSat
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    (hfield : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (pl : Encode.Placement ninp M w nw nq nt)
    (O : Ligero.V1.Oracle F nw nq s.certificate.n 1)
    (sys : LigeroSystem ninp M F)
    (hlin : sys.linear.length ≤ nlin) (hquad : sys.quad.length ≤ nt)
    (hno : NoSat
      (fun ℓ : SchemeLiftCandidate (s.code D hkn) O
        (s.certificate.e + s.certificate.g) => Encode.decode pl ℓ.decodedMessages) sys)
    (hbound : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits) :
    (∑ challenge : Ligero.V1.Challenge F nw nq 1
        (Fin nlin ⊕ (Fin nt × Encode.QSide)),
      (((Finset.univ : Finset (Response F s.certificate.openings w s.certificate.n 1)).sup
        fun response => (Finset.univ.filter fun query : QuerySet s.certificate.n
          s.certificate.openings =>
          (SchemeVerifier.policy (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
            (nw := nw) (nq := nq) (repetitions := 1)
            (s.code D hkn) Ligero.V1.scheme).accepts
            (Encode.encodeLig pl nlin sys) challenge response query
            (openSchemeOracle O query)).card : ℕ) : ℚ)
        / s.certificate.n.choose s.certificate.openings) /
      Fintype.card (Ligero.V1.Challenge F nw nq 1
        (Fin nlin ⊕ (Fin nt × Encode.QSide))) ≤
      (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  exact s.v1_uniform_acceptance_of_noDecoded hp hv hfield hdim D hkn hrows
    (Encode.encodeLig pl nlin sys) O hbound
    (Result.noDecoded_of_built_noSat s pl D hkn O sys hlin hquad hno)

/-- The flat V1 acceptance bound after the deployed role decoders.  The
response can depend on the *raw* challenge hash answer; response-uniformity
of the certificate is what avoids a response-list factor. -/
theorem Result.v1_hash_pair_acceptance_of_built_noSat
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    (hfield : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (pl : Encode.Placement ninp M w nw nq nt)
    (O : Ligero.V1.Oracle F nw nq s.certificate.n 1)
    (sys : LigeroSystem ninp M F)
    (hlin : sys.linear.length ≤ nlin) (hquad : sys.quad.length ≤ nt)
    (hno : NoSat
      (fun ℓ : SchemeLiftCandidate (s.code D hkn) O
        (s.certificate.e + s.certificate.g) => Encode.decode pl ℓ.decodedMessages) sys)
    (hbound : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    {HashAnswer : Type} [Fintype HashAnswer] [Nonempty HashAnswer]
    (decodeChallenge : HashAnswer → Ligero.V1.Challenge F nw nq 1
      (Fin nlin ⊕ (Fin nt × Encode.QSide)))
    (decodeQuery : HashAnswer → QuerySet s.certificate.n s.certificate.openings)
    (respond : HashAnswer → Response F s.certificate.openings w s.certificate.n 1)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : HashAnswer => decodeChallenge c = challenge).card ≤ kchal)
    (hquery : ∀ query,
      (univ.filter fun c : HashAnswer => decodeQuery c = query).card ≤ kquery) :
    ((univ.filter fun p : HashAnswer × HashAnswer =>
      (SchemeVerifier.policy (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (nw := nw) (nq := nq) (repetitions := 1)
        (s.code D hkn) Ligero.V1.scheme).accepts
        (Encode.encodeLig pl nlin sys) (decodeChallenge p.1) (respond p.1)
        (decodeQuery p.2) (openSchemeOracle O (decodeQuery p.2))).card : ℚ) /
        (Fintype.card HashAnswer : ℚ) ^ 2 ≤
      ((kchal * kquery : ℚ) *
        Fintype.card (Ligero.V1.Challenge F nw nq 1
          (Fin nlin ⊕ (Fin nt × Encode.QSide))) *
        Fintype.card (QuerySet s.certificate.n s.certificate.openings) /
          (Fintype.card HashAnswer : ℚ) ^ 2) *
        ((1 : ℚ) / 2 ^ s.certificate.targetBits) := by
  classical
  letI : Nonempty (QuerySet s.certificate.n s.certificate.openings) :=
    QuerySet.nonempty (by omega)
  let pol := SchemeVerifier.policy
    (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
    (nw := nw) (nq := nq) (repetitions := 1)
    (s.code D hkn) Ligero.V1.scheme
  let env := fun challenge : Ligero.V1.Challenge F nw nq 1
      (Fin nlin ⊕ (Fin nt × Encode.QSide)) =>
    (((univ : Finset (Response F s.certificate.openings w s.certificate.n 1)).sup
      fun response => (univ.filter fun query : QuerySet s.certificate.n
        s.certificate.openings =>
        pol.accepts (Encode.encodeLig pl nlin sys) challenge response query
          (openSchemeOracle O query)).card : ℕ) : ℚ) /
      s.certificate.n.choose s.certificate.openings
  have henv_nonneg (challenge) : 0 ≤ env challenge := by
    dsimp only [env]
    positivity
  have henv_query (challenge)
      (response : Response F s.certificate.openings w s.certificate.n 1) :
      ((univ.filter fun query : QuerySet s.certificate.n s.certificate.openings =>
        pol.accepts (Encode.encodeLig pl nlin sys) challenge response query
          (openSchemeOracle O query)).card : ℚ) /
        Fintype.card (QuerySet s.certificate.n s.certificate.openings) ≤
        env challenge := by
    rw [QuerySet.fintype_card]
    dsimp only [env]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Finset.le_sup
      (f := fun response : Response F s.certificate.openings w s.certificate.n 1 =>
        (univ.filter fun query : QuerySet s.certificate.n
          s.certificate.openings =>
          pol.accepts (Encode.encodeLig pl nlin sys) challenge response query
            (openSchemeOracle O query)).card)
      (Finset.mem_univ response)
  have henv_mean :
      (∑ challenge : Ligero.V1.Challenge F nw nq 1
        (Fin nlin ⊕ (Fin nt × Encode.QSide)), env challenge) /
        Fintype.card (Ligero.V1.Challenge F nw nq 1
          (Fin nlin ⊕ (Fin nt × Encode.QSide))) ≤
        (1 : ℚ) / 2 ^ s.certificate.targetBits := by
    simpa only [env, pol] using
      (Result.v1_uniform_acceptance_of_built_noSat s hp hv hfield hdim D hkn hrows
        pl O sys hlin hquad hno hbound)
  exact Lfzk.ZkPotentialBalance.decoded_pair_ratio_le_uniform
    decodeChallenge decodeQuery respond
    (fun challenge response query =>
      pol.accepts (Encode.encodeLig pl nlin sys) challenge response query
        (openSchemeOracle O query))
    env henv_nonneg henv_query
    ((1 : ℚ) / 2 ^ s.certificate.targetBits) henv_mean
    kchal kquery hchal hquery

/-- Exact decoder coverage turns the raw challenge/query pair bound into
the certificate's stated probability, with no response-count factor. -/
theorem Result.v1_hash_pair_acceptance_le_target
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    (hfield : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (pl : Encode.Placement ninp M w nw nq nt)
    (O : Ligero.V1.Oracle F nw nq s.certificate.n 1)
    (sys : LigeroSystem ninp M F)
    (hlin : sys.linear.length ≤ nlin) (hquad : sys.quad.length ≤ nt)
    (hno : NoSat
      (fun ℓ : SchemeLiftCandidate (s.code D hkn) O
        (s.certificate.e + s.certificate.g) => Encode.decode pl ℓ.decodedMessages) sys)
    (hbound : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    {HashAnswer : Type} [Fintype HashAnswer] [Nonempty HashAnswer]
    (decodeChallenge : HashAnswer → Ligero.V1.Challenge F nw nq 1
      (Fin nlin ⊕ (Fin nt × Encode.QSide)))
    (decodeQuery : HashAnswer → QuerySet s.certificate.n s.certificate.openings)
    (respond : HashAnswer → Response F s.certificate.openings w s.certificate.n 1)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : HashAnswer => decodeChallenge c = challenge).card ≤ kchal)
    (hquery : ∀ query,
      (univ.filter fun c : HashAnswer => decodeQuery c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card (Ligero.V1.Challenge F nw nq 1
      (Fin nlin ⊕ (Fin nt × Encode.QSide))) ≤ Fintype.card HashAnswer)
    (hkquery : kquery * Fintype.card
      (QuerySet s.certificate.n s.certificate.openings) ≤ Fintype.card HashAnswer) :
    ((univ.filter fun p : HashAnswer × HashAnswer =>
      (SchemeVerifier.policy (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (nw := nw) (nq := nq) (repetitions := 1)
        (s.code D hkn) Ligero.V1.scheme).accepts
        (Encode.encodeLig pl nlin sys) (decodeChallenge p.1) (respond p.1)
        (decodeQuery p.2) (openSchemeOracle O (decodeQuery p.2))).card : ℚ) /
        (Fintype.card HashAnswer : ℚ) ^ 2 ≤
      (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  have hpairs := Result.v1_hash_pair_acceptance_of_built_noSat s hp hv hfield hdim
    D hkn hrows pl O sys hlin hquad hno hbound decodeChallenge decodeQuery
    respond kchal kquery hchal hquery
  have hfactor := Lfzk.ZkPotentialBalance.decoder_pair_factor_le_one
    kchal kquery hkchal hkquery
  have heps : 0 ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfactor heps
  exact hpairs.trans (by simpa only [one_mul] using hmul)

end Lfzk.ZkLigeroV1
