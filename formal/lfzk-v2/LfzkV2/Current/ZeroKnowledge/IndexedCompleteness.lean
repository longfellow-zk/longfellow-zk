import Bcs.Indexed

/-! Completeness of the indexed commitment used by the current verifier.
An algebraically honest opening is authenticated without a collision or
freshness assumption. Values outside the queried set are irrelevant. -/
noncomputable section
open scoped Classical

namespace Merkle.Indexed

variable {Salt Message Digest Enc : Type*} [Inhabited Digest]
variable (scheme : Scheme Salt Message Digest Enc) {n : ℕ}

theorem checkValues_congr_on (I : Finset (Fin n)) (first second : Fin n → Message)
    (opening : Opening n I Salt Digest) (same : ∀ i ∈ I, first i = second i) (vertex : ℕ) :
    checkValues scheme n I first opening vertex = checkValues scheme n I second opening vertex := by
  conv_lhs => rw [checkValues]
  conv_rhs => rw [checkValues]
  split_ifs with leaf opened frontier frontier path
  · rw [same _ opened]
  · rfl
  · rfl
  · rfl
  · rw [checkValues_congr_on I first second opening same (2*vertex),
      checkValues_congr_on I first second opening same (2*vertex+1)]
  · rfl
termination_by 2*n-vertex
decreasing_by all_goals omega

theorem accepts_congr_on (I : Finset (Fin n)) (first second : Fin n → Message)
    (opening : Opening n I Salt Digest) (root : Digest) (same : ∀ i ∈ I, first i = second i) :
    Accepts scheme n root I first opening ↔ Accepts scheme n root I second opening := by
  unfold Accepts
  rw [checkValues_congr_on scheme I first second opening same]

end Merkle.Indexed

namespace Bcs.Compiler

variable {Statement Oracle Challenge Response Query : Type*}
variable {Opening : Query → Type*} {Salt Message Digest Enc : Type*} {n : ℕ}

/-- The current indexed compiler accepts any honest algebraic response,
using the literal opening of its committed column family. -/
theorem indexed_complete [Inhabited Digest]
    (compiler : Compiler Statement Oracle Challenge Response Query Opening Message n)
    (scheme : Merkle.Indexed.Scheme Salt Message Digest Enc)
    (nonce : Fin n → Salt) (oracle : Oracle) (statement : Statement)
    (challenge : Challenge) (response : Response) (query : Query)
    (verified : compiler.protocol.verify statement challenge response query
      (compiler.protocol.openOracle oracle query) = true) :
    compiler.AcceptsIndexed scheme statement
      (Merkle.Indexed.root scheme n nonce (compiler.columns oracle)) challenge response query
      ⟨compiler.indices query, compiler.columns oracle,
        Merkle.Indexed.openCore scheme n (compiler.indices query) nonce (compiler.columns oracle)⟩ := by
  refine ⟨rfl, Merkle.Indexed.mh_core_completeness scheme n (compiler.indices query)
    (compiler.indices_nonempty query) nonce (compiler.columns oracle), ?_⟩
  simpa only [oracleOfClaim, Equiv.symm_apply_apply] using verified

/-- Runtime decoding can fill unqueried columns with its default value.
This does not change either indexed authentication or the algebraic check. -/
theorem indexed_complete_with_defaults [Inhabited Digest] [Inhabited Message]
    (compiler : Compiler Statement Oracle Challenge Response Query Opening Message n)
    (scheme : Merkle.Indexed.Scheme Salt Message Digest Enc)
    (nonce : Fin n → Salt) (oracle : Oracle) (statement : Statement)
    (challenge : Challenge) (response : Response) (query : Query)
    (verified : compiler.protocol.verify statement challenge response query
      (compiler.protocol.openOracle oracle query) = true) :
    compiler.AcceptsIndexed scheme statement
      (Merkle.Indexed.root scheme n nonce (compiler.columns oracle)) challenge response query
      ⟨compiler.indices query,
        fun i => if i ∈ compiler.indices query then compiler.columns oracle i else default,
        Merkle.Indexed.openCore scheme n (compiler.indices query) nonce (compiler.columns oracle)⟩ := by
  let columns := fun i => if i ∈ compiler.indices query then compiler.columns oracle i else default
  have same : ∀ i ∈ compiler.indices query, compiler.columns oracle i = columns i := by
    intro i inside
    exact (if_pos inside).symm
  have accepted := indexed_complete compiler scheme nonce oracle statement challenge response query verified
  refine ⟨rfl, (Merkle.Indexed.accepts_congr_on scheme (compiler.indices query) _ _ _ _ same).mp accepted.2.1, ?_⟩
  have locality := compiler.open_congr oracle (compiler.oracleOfClaim columns) query (by
    simpa only [columns_oracleOfClaim] using same)
  exact locality ▸ verified

end Bcs.Compiler
