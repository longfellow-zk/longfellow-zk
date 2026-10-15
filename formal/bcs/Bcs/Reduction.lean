import Bcs.Compiled

/-!
# The deterministic reduction, composed

`Bcs/Compiled.lean` proves the compilation bridge from an *assumed* agreement between the extracted
leaves and the claimed ones.  `Merkle.MH.mh_extract_explains_of_trace_subset` proves that agreement
on a collision-free trace containing the check.  This file composes them, which is the whole
deterministic content of the BCS step:

> On a collision-free trace containing everything the Merkle check queries, the extractor succeeds,
> and the IPCP verifier accepts the extracted commitment on the same coins the compiled verifier
> accepted.

Nothing here is probabilistic.  What the ROM layer (Phase C of `../bcs-plan.md`) must supply is a
*bound on the tapes where the hypotheses fail* — `mh_extract_rom_card_le` for a single commitment,
`mh_multi_extract_rom_card_le` for `k` of them.  The reduction itself is finished.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open LigeroFamily Merkle

namespace Compiler

variable {Statement Oracle Challenge Response Query : Type*}
variable {Opening : Query → Type*}
variable {Salt M D Enc : Type*} {n : ℕ}

/-- **The deterministic BCS reduction.**  If a compiled acceptance's check trace lies inside a
collision-free trace, then the extractor built from that trace succeeds and the underlying IPCP
verifier accepts the extracted commitment — on the same statement, the same coins, and the same
response.

The extracted commitment `K.oracleOfClaim out.message` depends on the trace and the root, and on
nothing else: not on the challenge, not on the query, not on the statement.  That is what makes it
usable as `IPCPProver.commit`, and it is what an oracle-only extractor such as
`Ligero.V3.witness_extractor` requires. -/
theorem accepts_extracted [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] [Inhabited M]
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (S : MH.Scheme Salt M D Enc) (dec : MH.RoleDecoders S.toCodec)
    (statement : Statement) (root : D) (challenge : Challenge) (query : Query)
    (response : Challenge → Response) (claim : MH.OpeningClaim n Salt M D)
    (trace : List (Enc × D)) (hfree : MH.CollisionFree trace)
    (hsub : ∀ qa ∈ MH.checkTraceList S n claim.I claim.a claim.pf, qa ∈ trace)
    (hacc : K.Accepts S statement root challenge (response challenge) query claim) :
    ∃ out : MH.Extracted n Salt M D,
      MH.extract dec n root trace = some out ∧
        K.protocol.accepts (K.prover (K.oracleOfClaim out.message) response) statement
          (challenge, query) = true := by
  obtain ⟨out, hextract, hmessages, -⟩ :=
    MH.mh_extract_explains_of_trace_subset S dec n claim.I claim.a claim.pf root trace
      hfree hacc.2.1 hsub
  exact ⟨out, hextract,
    K.protocol_accepts_of_accepts S statement root challenge query claim out.message response
      hmessages hacc⟩

end Compiler

end Bcs
