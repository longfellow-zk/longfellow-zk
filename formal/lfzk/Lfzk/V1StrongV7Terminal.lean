import Lfzk.V1StrongV7HighCount
import Lfzk.V1StrongV7LowQuery
import Bcs.TwoScaleTerminal

/-! Adaptive terminal V1 policy bound at each v7 hash geometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7Terminal

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

abbrev Payload (i : Fin 4) (F : Type) :=
  Lfzk.LigeroTranscriptInputs.ResponsePayload F
    (row i).k (2 * (row i).k - 1) (row i).openings

noncomputable def decodePayload (i : Fin 4)
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {w : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n) :=
  Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes
    (by fin_cases i <;> native_decide : (row i).openings ≤ (row i).k)
    (by fin_cases i <;> native_decide : (row i).k ≤ 2 * (row i).k - 1)

noncomputable def good (i : Fin 4)
    {F : Type} {Equations : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
    (payload : Payload i F) : Finset (Fin (row i).n) :=
  let R := row i
  let C := R.code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow
  let policy := Ligero.V1.potentialFailedPolicy (Equations := Equations)
    (e := R.e) (g := R.g) C oracle
  policyAcceptingCoordinates policy oracle statement challenge
    (decodePayload i D baseNodes responseNodes payload)

noncomputable def accepts (i : Fin 4)
    {F : Type} {Equations : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
    (payload : Payload i F)
    (query : QuerySet (row i).n (row i).openings) : Prop :=
  let R := row i
  let C := R.code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow
  let policy := Ligero.V1.potentialFailedPolicy (Equations := Equations)
    (e := R.e) (g := R.g) C oracle
  policy.accepts statement challenge
    (decodePayload i D baseNodes responseNodes payload) query
    (openSchemeOracle oracle query)

/-- Unfold the event used by the FS bound: ordinary V1 verifier acceptance
and failure of its response-assisted extractor on that same response. -/
theorem accepts_iff_extraction_failure (i : Fin 4)
    {F : Type} {Equations : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
    (payload : Payload i F)
    (query : QuerySet (row i).n (row i).openings) :
    accepts i D hkrow baseNodes responseNodes oracle statement
        challenge payload query ↔
    let C := (row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow
    let policy := SchemeVerifier.policy
      (Equations := Equations) (nw := nw) (nq := nq)
      (repetitions := 1) C Ligero.V1.scheme
    let response := decodePayload i D baseNodes responseNodes payload
    policy.accepts statement challenge response query (openSchemeOracle oracle query) ∧
      ScalarGapExtraction.extract (oracle := oracle)
        (e := (row i).e) (g := (row i).g) policy
        (fun candidate => candidate.decodedMessages)
        statement challenge response = none := by
  rfl

/-- If the committed lift list contains no satisfying tableau, the event
charged by the response-assisted FS theorem is ordinary V1 acceptance. -/
theorem accepts_iff_of_noDecoded (i : Fin 4)
    {F : Type} {Equations : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
    (payload : Payload i F)
    (query : QuerySet (row i).n (row i).openings)
    (hnd : NoDecodedSolution
      ((row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow)
      oracle ((row i).e + (row i).g) statement) :
    accepts i D hkrow baseNodes responseNodes oracle statement
        challenge payload query ↔
      (SchemeVerifier.policy
        (Equations := Equations) (nw := nw) (nq := nq)
        (repetitions := 1)
        ((row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow)
        Ligero.V1.scheme).accepts statement challenge
        (decodePayload i D baseNodes responseNodes payload) query
        (openSchemeOracle oracle query) := by
  rw [accepts_iff_extraction_failure]
  simp [ScalarGapExtraction.extract_none_of_no_valid _ _ statement challenge
    (decodePayload i D baseNodes responseNodes payload) hnd]

/-- On every accepting V1 transcript, the response-assisted extractor either
returns a satisfying lift or the failed-extraction event charged by FS occurs. -/
theorem accepted_extracts_or_fails (i : Fin 4)
    {F : Type} {Equations : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
    (payload : Payload i F)
    (query : QuerySet (row i).n (row i).openings) :
    let C := (row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow
    let policy := SchemeVerifier.policy
      (Equations := Equations) (nw := nw) (nq := nq)
      (repetitions := 1) C Ligero.V1.scheme
    let response := decodePayload i D baseNodes responseNodes payload
    policy.accepts statement challenge response query (openSchemeOracle oracle query) →
      (∃ candidate : SchemeLiftCandidate C oracle ((row i).e + (row i).g),
        ScalarGapExtraction.extract (oracle := oracle)
          (e := (row i).e) (g := (row i).g) policy
          (fun x => x.decodedMessages) statement challenge response = some candidate ∧
        statement.Satisfies candidate.decodedMessages) ∨
      accepts i D hkrow baseNodes responseNodes oracle statement
        challenge payload query := by
  classical
  dsimp only
  intro hacc
  let C := (row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow
  let policy := SchemeVerifier.policy
    (Equations := Equations) (nw := nw) (nq := nq)
    (repetitions := 1) C Ligero.V1.scheme
  let response := decodePayload i D baseNodes responseNodes payload
  let extracted := ScalarGapExtraction.extract (oracle := oracle)
    (e := (row i).e) (g := (row i).g) policy
    (fun x => x.decodedMessages) statement challenge response
  cases hext : extracted with
  | none =>
      exact Or.inr ((accepts_iff_extraction_failure i D hkrow
        baseNodes responseNodes oracle statement challenge payload query).2
        ⟨hacc, hext⟩)
  | some candidate =>
      have hvalid := ScalarGapExtraction.extract_valid
        (oracle := oracle) (e := (row i).e) (g := (row i).g)
        policy (fun x => x.decodedMessages) statement challenge response
        candidate hext
      exact Or.inl ⟨candidate, hext, hvalid.2⟩

noncomputable def low (i : Fin 4)
    {F : Type} {Equations Coin : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (decodeChallenge : Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (payload : Payload i F) (a b : Coin) : Prop :=
  (good i D hkrow baseNodes responseNodes oracle statement
    (decodeChallenge a) payload).card ≤ cutoff (row i) ∧
  accepts i D hkrow baseNodes responseNodes oracle statement
    (decodeChallenge a) payload (decodeQuery b)

noncomputable def high (i : Fin 4)
    {F : Type} {Equations Coin : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (decodeChallenge : Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (payload : Payload i F) (a b : Coin) : Prop :=
  cutoff (row i) <
      (good i D hkrow baseNodes responseNodes oracle statement
        (decodeChallenge a) payload).card ∧
  accepts i D hkrow baseNodes responseNodes oracle statement
    (decodeChallenge a) payload (decodeQuery b)

/-- The radius partition is exhaustive.  Thus the charged event is exactly
acceptance by `potentialFailedPolicy`, whose definition is verifier acceptance
with the response-assisted extractor returning `none`. -/
theorem low_or_high_iff_accepts (i : Fin 4)
    {F : Type} {Equations Coin : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (decodeChallenge : Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (payload : Payload i F) (a b : Coin) :
    low i D hkrow baseNodes responseNodes oracle statement
        decodeChallenge decodeQuery payload a b ∨
    high i D hkrow baseNodes responseNodes oracle statement
        decodeChallenge decodeQuery payload a b ↔
    accepts i D hkrow baseNodes responseNodes oracle statement
        (decodeChallenge a) payload (decodeQuery b) := by
  unfold low high
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  · intro h
    by_cases hle :
      (good i D hkrow baseNodes responseNodes oracle statement
        (decodeChallenge a) payload).card ≤ cutoff (row i)
    · exact Or.inl ⟨hle, h⟩
    · exact Or.inr ⟨Nat.lt_of_not_ge hle, h⟩

/-- For each v7 hash geometry, the complete V1 policy event incurs at most
`N` times the certified low-plus-high density over an `N`-query random-oracle
tree.  This is a terminal policy bound; the deployed-verifier implication and
extraction conclusion are separate obligations. -/
theorem v7_v1_terminal_density_le (i : Fin 4)
    {F : Type} {Equations : Type*} {Coin Q Prefix Out : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype Coin] [Nonempty Coin]
    [Fintype Q] [DecidableEq Q] [Fintype Prefix]
    {w nw nq N : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (tree : Merkle.RandomOracle.Tree Q Coin Out N)
    (parent : Prefix → Q) (child : Prefix → Payload i F → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun pr : Prefix × Payload i F => child pr.1 pr.2))
    (hdisjoint : ∀ p p' payload, parent p ≠ child p' payload)
    (oracle : Prefix → Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : Prefix → ConstraintSystem F nw nq w Equations)
    (decodeChallenge : Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : Coin => decodeChallenge c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : Coin => decodeQuery c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card
      (Ligero.V1.Challenge F nw nq 1 Equations) ≤ Fintype.card Coin)
    (hkquery : kquery * Fintype.card
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin) :
    (∑ H : Q → Coin, ∑ p : Prefix, ∑ payload : Payload i F,
      ((if child p payload ∈ queried tree H ∧
          low i D hkrow baseNodes responseNodes (oracle p) (statement p)
            decodeChallenge decodeQuery payload (H (parent p))
            (H (child p payload)) then (1 : ℚ) else 0) +
      (if firstOfTwoOffResult tree (parent p) (child p payload)
          (hdisjoint p p payload) (fun z => H z.1) ≠ .neither ∧
          high i D hkrow baseNodes responseNodes (oracle p) (statement p)
            decodeChallenge decodeQuery payload (H (parent p))
            (H (child p payload)) then (1 : ℚ) else 0))) /
        (Fintype.card Coin : ℚ) ^ Fintype.card Q ≤
      (N : ℚ) * density i := by
  let lowAt := fun p payload a b =>
    low i D hkrow baseNodes responseNodes (oracle p) (statement p)
      decodeChallenge decodeQuery payload a b
  let highAt := fun p payload a b =>
    high i D hkrow baseNodes responseNodes (oracle p) (statement p)
      decodeChallenge decodeQuery payload a b
  have hlow (p : Prefix) (payload : Payload i F) (a : Coin) :
      ∑ b : Coin, (if lowAt p payload a b then (1 : ℚ) else 0) ≤
        Fintype.card Coin * cover (row i) (cutoff (row i)) := by
    by_cases ha : (good i D hkrow baseNodes responseNodes
        (oracle p) (statement p) (decodeChallenge a) payload).card ≤
        cutoff (row i)
    · have h := Lfzk.V1StrongV7LowQuery.decoded_low_query_le i
        D hkrow (oracle p) (statement p) (decodeChallenge a)
        (decodePayload i D baseNodes responseNodes payload)
        decodeQuery kquery hqueryBalance hkquery ha
      simp only [lowAt, low, ha, true_and]
      exact h
    · have hcover : 0 ≤ cover (row i) (cutoff (row i)) := by
        unfold cover hypergeometricRatio
        positivity
      simpa only [lowAt, low, ha, false_and, ite_false, Finset.sum_const_zero]
        using mul_nonneg (by positivity : (0 : ℚ) ≤ Fintype.card Coin) hcover
  have hhigh (p : Prefix) :
      ∑ payload : Payload i F, ∑ a : Coin, ∑ b : Coin,
        (if highAt p payload a b then (1 : ℚ) else 0) ≤
        (Fintype.card Coin : ℚ) ^ 2 * highMass i := by
    have h := Lfzk.V1StrongV7HighCount.v7_v1_high_count_le i
      hrows hfield D hkrow baseNodes responseNodes (oracle p)
      (statement p) decodeChallenge decodeQuery kchal kquery
      hchal hqueryBalance hkchal hkquery
    exact h
  have hcover : 0 ≤ cover (row i) (cutoff (row i)) := by
    unfold cover hypergeometricRatio
    positivity
  have hterminal := tree_two_scale_terminal_ratio_le tree
    parent child hparent hchild hdisjoint lowAt highAt
    (cover (row i) (cutoff (row i))) (highMass i)
    hcover (highMass_nonneg i) hlow hhigh
  simpa only [lowAt, highAt, density] using hterminal

end Lfzk.V1StrongV7Terminal
