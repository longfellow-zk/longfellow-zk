import Bcs.Compiled

/-!
# Every LigeroFamily protocol compiles

The non-vacuity witness for `Bcs.Compiler`.  It is stated once, for *any* public-coin IPCP whose
oracle is a `SchemeOracle` and whose `openOracle` is `openSchemeOracle` — which is every protocol in
the family (`SchemeVerifier.protocol`, `SchemeProtocolPolicy.protocol`, the direct-product
verifier), each satisfying the hypothesis by `rfl`.

The two interesting fields cost nothing:

* `columns` is `LigeroFamily.schemeOracleEquivColumns`, whose round-trips are definitional;
* `open_congr` is `LigeroFamily.openSchemeOracle_congr` — locality is a *theorem* about the family,
  because `openOracle` is applied to the whole commitment and reads one column per queried
  coordinate.

So the compilation assumes nothing about the protocol beyond the shape it already has.  A leaf is a
committed column, and the opened set is the drawn query set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open LigeroFamily

/-- **Non-vacuity: the Ligero family compiles.**  Leaves are committed columns, and the opened set
is the query's own coordinate set. -/
def schemeCompiler {Statement Challenge Response F CheckedMask DirectMask : Type*}
    {nw nq n repetitions r : ℕ}
    (protocol : PublicCoinIPCP Statement
      (SchemeOracle F CheckedMask DirectMask nw nq n repetitions)
      Challenge Response (QuerySet n r)
      (SchemeOpening F CheckedMask DirectMask nw nq repetitions n r))
    (hopen : protocol.openOracle = openSchemeOracle) (hr : 0 < r) :
    Compiler Statement (SchemeOracle F CheckedMask DirectMask nw nq n repetitions)
      Challenge Response (QuerySet n r)
      (SchemeOpening F CheckedMask DirectMask nw nq repetitions n r)
      (SchemeColumn F CheckedMask DirectMask nw nq repetitions) n where
  protocol := protocol
  columns := schemeOracleEquivColumns F CheckedMask DirectMask nw nq n repetitions
  indices query := query.coordinates
  indices_nonempty query := Finset.card_pos.mp (by rw [QuerySet.card_coordinates]; exact hr)
  open_congr first second query hagree := by
    rw [hopen]
    exact openSchemeOracle_congr query hagree

@[simp] theorem schemeCompiler_protocol
    {Statement Challenge Response F CheckedMask DirectMask : Type*}
    {nw nq n repetitions r : ℕ}
    (protocol : PublicCoinIPCP Statement
      (SchemeOracle F CheckedMask DirectMask nw nq n repetitions)
      Challenge Response (QuerySet n r)
      (SchemeOpening F CheckedMask DirectMask nw nq repetitions n r))
    (hopen : protocol.openOracle = openSchemeOracle) (hr : 0 < r) :
    (schemeCompiler protocol hopen hr).protocol = protocol := rfl

/-- The concrete family member: the mask-scheme verifier of `LigeroFamily.SchemeVerifier.protocol`,
which is V1 and V2.  The `openOracle` hypothesis is `rfl`. -/
noncomputable def schemeVerifierCompiler {F Equations CheckedMask DirectMask : Type*}
    [Field F] [Fintype Equations] [Fintype CheckedMask]
    {r w n nw nq repetitions : ℕ}
    (C : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n) (hr : 0 < r) :
    Compiler (ConstraintSystem F nw nq w Equations)
      (SchemeOracle F CheckedMask DirectMask nw nq n repetitions)
      (SchemeChallenge F CheckedMask nw nq repetitions Equations)
      (Response F r w n repetitions) (QuerySet n r)
      (SchemeOpening F CheckedMask DirectMask nw nq repetitions n r)
      (SchemeColumn F CheckedMask DirectMask nw nq repetitions) n :=
  schemeCompiler (SchemeVerifier.protocol C scheme) rfl hr

end Bcs
