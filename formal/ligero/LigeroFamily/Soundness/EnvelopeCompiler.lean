import Bcs.FixedKeyEnvelopeFiatShamir
import Merkle.PrefixBinding
import LigeroFamily.Soundness.ScalarGapProfiled

/-! Shared Merkle-committed, typed-ROM compiler from a response-uniform
extraction envelope. No response enumeration or compiler list factor. -/
namespace LigeroFamily.EnvelopeFS
open Finset Bcs.EnvelopeFiatShamir Bcs.TypedFiatShamir
open scoped Classical BigOperators
set_option maxHeartbeats 2000000

/-- A shared commitment prefix and arbitrary later openings selected by FS.
The commitment key is fixed before the typed challenge experiment, matching
the existing prefix-binding compiler model. -/
structure Experiment (Column Challenge Response AlphaKey Salt Digest Encoding Output PrefixOut RunOut : Type*)
    (n r N merkleT prefixFuel runFuel : ℕ)
    [Fintype Challenge] [DecidableEq Challenge] [DecidableEq Response] [DecidableEq AlphaKey]
    [Inhabited Column] [Inhabited Salt] [Inhabited Digest]
    [Fintype Digest] [DecidableEq Digest] [DecidableEq Encoding] where
  codec : Merkle.MH.Codec Salt Column Digest Encoding
  family : Merkle.MH.PrefixBindingFamily (Out := PrefixOut) (RunOut := RunOut) codec
    (Fin (N + 2) → Answer Challenge (QuerySet n r)) n merkleT prefixFuel runFuel
  decoders : Merkle.MH.RoleDecoders codec
  prefix_fits : prefixFuel ≤ merkleT
  adversary : Merkle.RandomOracle.Tree (Query AlphaKey (AlphaKey × Response))
    (Answer Challenge (QuerySet n r)) Output N
  defaultAnswer : Answer Challenge (QuerySet n r)
  alphaKey : AlphaKey
  responseOf : Output → Response

namespace Experiment
variable {Column Challenge Response AlphaKey Salt Digest Encoding Output PrefixOut RunOut : Type*}
variable {n r N merkleT prefixFuel runFuel : ℕ}
variable [Fintype Challenge] [DecidableEq Challenge] [DecidableEq Response] [DecidableEq AlphaKey]
variable [Inhabited Column] [Inhabited Salt] [Inhabited Digest]
variable [Fintype Digest] [DecidableEq Digest] [DecidableEq Encoding]
variable (experiment : Experiment Column Challenge Response AlphaKey Salt Digest Encoding Output PrefixOut RunOut
  n r N merkleT prefixFuel runFuel)

abbrev FsTape := Fin (N + 2) → Answer Challenge (QuerySet n r)
abbrev MerkleTape := Fin merkleT → Digest

def trace := Bcs.EnvelopeFiatShamir.trace experiment.adversary experiment.defaultAnswer
  experiment.alphaKey experiment.responseOf
def alpha (tape : FsTape (Challenge := Challenge) (n := n) (r := r) (N := N)) :=
  definingAlphaAnswer experiment.trace tape
def query (tape : FsTape (Challenge := Challenge) (n := n) (r := r) (N := N)) :=
  definingSubsetAnswer experiment.trace tape
def response (tape : FsTape (Challenge := Challenge) (n := n) (r := r) (N := N)) :=
  experiment.responseOf (Merkle.RandomOracle.lazyRun tape experiment.defaultAnswer experiment.adversary []).1

noncomputable def columns (answers : MerkleTape (Digest := Digest) (merkleT := merkleT)) :=
  (experiment.family.game (fun _ => experiment.defaultAnswer)).boundMessage experiment.decoders answers

def bindingError (_experiment : Experiment Column Challenge Response AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    n r N merkleT prefixFuel runFuel) : ℚ :=
  (((prefixFuel * (prefixFuel - 1) / 2 + merkleT * (2 * prefixFuel + 1)) *
    Fintype.card Digest ^ (merkleT - 1) : ℕ) : ℚ) / Fintype.card (Fin merkleT → Digest)

def compiledBound (epsilon : ℚ) : ℚ :=
  experiment.bindingError + Bcs.EnvelopeFiatShamir.FixedKey.errorBound N epsilon

/-- Exact interpretation of a printed linear FS coefficient. -/
theorem compiledBound_dyadic (coefficientBits : ℕ) :
    experiment.compiledBound ((1 : ℚ) / 2 ^ coefficientBits) =
      experiment.bindingError + min 1 ((N + 1 : ℚ) / 2 ^ coefficientBits) := by
  rw [compiledBound, Bcs.EnvelopeFiatShamir.FixedKey.errorBound_dyadic]

end Experiment

section Policy
variable {F CheckedMask DirectMask Equations Challenge Response AlphaKey Salt Digest Encoding Output PrefixOut RunOut : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype Challenge] [DecidableEq Challenge] [DecidableEq Response] [DecidableEq AlphaKey]
variable [Inhabited Salt] [Inhabited Digest] [Fintype Digest] [DecidableEq Digest] [DecidableEq Encoding]
variable {q r w n nw nq e g N merkleT prefixFuel runFuel : ℕ}
variable {C : MultiplicativeCode F r w n} {layout : ConstraintLayout F q w}
variable (policy : SchemeProtocolPolicy (Equations := Equations) C layout
  Challenge Response CheckedMask DirectMask nw nq 1)
variable (messages : ∀ oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1,
  SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
variable (statement : ConstraintSystem F nw nq q Equations)
variable (experiment : Experiment (SchemeColumn F CheckedMask DirectMask nw nq 1)
  Challenge Response AlphaKey Salt Digest Encoding Output PrefixOut RunOut n r N merkleT prefixFuel runFuel)

noncomputable def committedOracle (answers : Fin merkleT → Digest) :
    SchemeOracle F CheckedMask DirectMask nw nq n 1 := SchemeOracle.ofColumns (experiment.columns answers)

noncomputable def compiledAccepts (answers : Fin merkleT → Digest)
    (tape : Fin (N + 2) → Answer Challenge (QuerySet n r)) : Prop :=
  let game := experiment.family.game tape
  let claim := game.claim answers
  claim.I = (experiment.query tape).coordinates ∧
    Merkle.MH.Accepts (experiment.codec.withOracle (game.oracle answers)) n
      (game.root answers) claim.I claim.a claim.pf ∧
    policy.accepts statement (experiment.alpha tape) (experiment.response tape)
      (experiment.query tape) (fun j => claim.a j.1)

noncomputable def extract (answers : Fin merkleT → Digest)
    (tape : Fin (N + 2) → Answer Challenge (QuerySet n r)) :=
  ScalarGapExtraction.extract (oracle := committedOracle experiment answers) (e := e) (g := g)
    policy (messages (committedOracle experiment answers)) statement
    (experiment.alpha tape) (experiment.response tape)

omit [DecidableEq Response] in
/-- Bridge the existing profiled envelope to the compiler's local contract. -/
theorem localBound_of_mean [Fintype Response] [Nonempty Response] [Nonempty Challenge]
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1) (epsilon : ℚ)
    (hmean : (∑ alpha : Challenge,
      ScalarGapExtraction.profiledUniformEnvelope (oracle := oracle) (e := e) (g := g)
        policy (messages oracle) statement alpha) / Fintype.card Challenge ≤ epsilon) :
    Nonempty (ResponseUniformBound
      (fun alpha response query => policy.accepts statement alpha response query
        (openSchemeOracle oracle query) ∧
        ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g)
          policy (messages oracle) statement alpha response = none) epsilon) := by
  refine ⟨{
    envelope := ScalarGapExtraction.profiledUniformEnvelope (oracle := oracle) (e := e) (g := g)
      policy (messages oracle) statement
    mean_le := hmean
    dominates := ?_ }⟩
  intro alpha response
  rw [QuerySet.fintype_card]
  refine le_trans ?_ (ScalarGapExtraction.response_fraction_le_profiledUniformEnvelope
    (oracle := oracle) (e := e) (g := g) policy (messages oracle) statement alpha response)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro query hquery
  simpa only [ScalarGapExtraction.failingQueries, mem_filter, mem_univ, true_and] using hquery

omit [Fintype F] [DecidableEq F] [DecidableEq CheckedMask]
  [Fintype Equations] [DecidableEq Equations] in
theorem accepts_of_binding (answers : Fin merkleT → Digest)
    (tape : Fin (N + 2) → Answer Challenge (QuerySet n r))
    (haccept : compiledAccepts policy statement experiment answers tape)
    (hbinding : ¬(experiment.family.game tape).Bad experiment.decoders answers) :
    policy.accepts statement (experiment.alpha tape) (experiment.response tape)
      (experiment.query tape) (openSchemeOracle (committedOracle experiment answers) (experiment.query tape)) := by
  rcases haccept with ⟨hquery, hmerkle, hpolicy⟩
  have hopen : openSchemeOracle (committedOracle experiment answers) (experiment.query tape) =
      fun j => (experiment.family.game tape).claim answers |>.a j.1 := by
    rw [committedOracle, openSchemeOracle_ofColumns]
    funext j
    change (experiment.family.game tape).boundMessage experiment.decoders answers j.1 = _
    by_contra hne
    apply hbinding
    refine ⟨hmerkle, j.1, ?_, hne⟩
    rw [hquery]
    exact j.2
  rw [hopen]
  exact hpolicy

omit [DecidableEq CheckedMask] [Fintype Equations] [DecidableEq Equations] in
/-- The original response-assisted decoder remains the compiled extractor. -/
theorem extraction_ratio_le (epsilon : ℚ)
    (localBound : ∀ oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1,
      Nonempty (ResponseUniformBound
        (fun alpha response query => policy.accepts statement alpha response query
          (openSchemeOracle oracle query) ∧
          ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g)
            policy (messages oracle) statement alpha response = none) epsilon)) :
    ((univ.filter fun value : (Fin merkleT → Digest) ×
        (Fin (N + 2) → Answer Challenge (QuerySet n r)) =>
      compiledAccepts policy statement experiment value.1 value.2 ∧
        extract policy messages statement experiment value.1 value.2 = none).card : ℚ) /
      Fintype.card ((Fin merkleT → Digest) ×
        (Fin (N + 2) → Answer Challenge (QuerySet n r))) ≤ experiment.compiledBound epsilon := by
  classical
  letI : Nonempty Challenge := ⟨experiment.defaultAnswer.1⟩
  letI : Nonempty (QuerySet n r) := ⟨experiment.defaultAnswer.2⟩
  let Win := fun answers tape => compiledAccepts policy statement experiment answers tape ∧
    extract policy messages statement experiment answers tape = none
  let Bad := fun answers tape => (experiment.family.game tape).Bad experiment.decoders answers
  let Good := fun answers tape => ¬Bad answers tape ∧ Win answers tape
  let beta : ℚ := Bcs.EnvelopeFiatShamir.FixedKey.errorBound N epsilon
  have hgoodFiber (answers : Fin merkleT → Digest) :
      ((univ.filter (Good answers)).card : ℚ) /
        Fintype.card (Fin (N + 2) → Answer Challenge (QuerySet n r)) ≤ beta := by
    let oracle := committedOracle experiment answers
    let bad := fun alpha response query => policy.accepts statement alpha response query
      (openSchemeOracle oracle query) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g)
        policy (messages oracle) statement alpha response = none
    have hfs := Bcs.EnvelopeFiatShamir.FixedKey.extraction_ratio_le_capped experiment.adversary
      experiment.defaultAnswer experiment.alphaKey experiment.responseOf bad epsilon
      (Classical.choice (localBound oracle))
    have hfs' : ((univ.filter fun tape =>
        bad (experiment.alpha tape) (experiment.response tape) (experiment.query tape)).card : ℚ) /
        Fintype.card (Fin (N + 2) → Answer Challenge (QuerySet n r)) ≤ beta := by
      simpa only [Experiment.alpha, Experiment.response, Experiment.query, Experiment.trace,
        Bcs.EnvelopeFiatShamir.trace, definingAlphaAnswer, definingSubsetAnswer, beta] using hfs
    have hsubset : univ.filter (Good answers) ⊆ univ.filter (fun tape =>
        bad (experiment.alpha tape) (experiment.response tape) (experiment.query tape)) := by
      intro tape htape
      obtain ⟨hbinding, haccept, hfail⟩ := (mem_filter.mp htape).2
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_, hfail⟩
      exact accepts_of_binding policy statement experiment answers tape haccept hbinding
    have hden : (0 : ℚ) < Fintype.card (Fin (N + 2) → Answer Challenge (QuerySet n r)) := by
      exact_mod_cast Fintype.card_pos
    exact (div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsubset) hden.le).trans hfs'
  have hgood := Bcs.product_ratio_le_of_fst_fiber Good beta hgoodFiber
  have hbinding : ((univ.filter fun value : (Fin merkleT → Digest) ×
        (Fin (N + 2) → Answer Challenge (QuerySet n r)) => Bad value.1 value.2).card : ℚ) /
      Fintype.card ((Fin merkleT → Digest) ×
        (Fin (N + 2) → Answer Challenge (QuerySet n r))) ≤ experiment.bindingError := by
    apply Bcs.product_ratio_le_of_snd_fiber Bad experiment.bindingError
    intro tape
    exact (experiment.family.game tape).bad_ratio_le experiment.decoders experiment.prefix_fits
  let wins := univ.filter fun value : (Fin merkleT → Digest) ×
    (Fin (N + 2) → Answer Challenge (QuerySet n r)) => Win value.1 value.2
  let bads := univ.filter fun value : (Fin merkleT → Digest) ×
    (Fin (N + 2) → Answer Challenge (QuerySet n r)) => Bad value.1 value.2
  let goods := univ.filter fun value : (Fin merkleT → Digest) ×
    (Fin (N + 2) → Answer Challenge (QuerySet n r)) => Good value.1 value.2
  have hcover : wins ⊆ bads ∪ goods := by
    intro value hwin
    by_cases hbad : Bad value.1 value.2
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hbad⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hbad, (mem_filter.mp hwin).2⟩)
  have hcard := (card_le_card hcover).trans (card_union_le bads goods)
  have hden : (0 : ℚ) < Fintype.card ((Fin merkleT → Digest) ×
      (Fin (N + 2) → Answer Challenge (QuerySet n r))) := by exact_mod_cast Fintype.card_pos
  change (wins.card : ℚ) / _ ≤ experiment.bindingError + beta
  calc
    (wins.card : ℚ) / _ ≤ ((bads.card + goods.card : ℕ) : ℚ) / _ :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden.le
    _ = (bads.card : ℚ) / _ + (goods.card : ℚ) / _ := by push_cast; ring
    _ ≤ experiment.bindingError + beta := add_le_add hbinding hgood

omit [DecidableEq CheckedMask] in
/-- False-statement FS soundness follows from decoder validity, without
selecting a witness before the Fiat--Shamir transcript. -/
theorem soundness_ratio_le (epsilon : ℚ)
    (localBound : ∀ oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1,
      Nonempty (ResponseUniformBound
        (fun alpha response query => policy.accepts statement alpha response query
          (openSchemeOracle oracle query) ∧
          ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g)
            policy (messages oracle) statement alpha response = none) epsilon))
    (hfalse : ¬statement.Language) :
    ((univ.filter fun value : (Fin merkleT → Digest) ×
        (Fin (N + 2) → Answer Challenge (QuerySet n r)) =>
      compiledAccepts policy statement experiment value.1 value.2).card : ℚ) /
      Fintype.card ((Fin merkleT → Digest) ×
        (Fin (N + 2) → Answer Challenge (QuerySet n r))) ≤ experiment.compiledBound epsilon := by
  have h := extraction_ratio_le policy messages statement experiment epsilon localBound
  have hnone (answers : Fin merkleT → Digest) (tape : Fin (N + 2) → Answer Challenge (QuerySet n r)) :
      extract policy messages statement experiment answers tape = none := by
    apply ScalarGapExtraction.extract_none_of_no_valid
    intro candidate hsat
    exact hfalse ⟨messages _ candidate, hsat⟩
  simpa only [hnone, and_true] using h

end Policy
end LigeroFamily.EnvelopeFS
