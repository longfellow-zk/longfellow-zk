import LigeroFamily.Protocol.IPCP

/-! The common finite accept-and-extraction-failure event for every variant. -/
namespace LigeroFamily
open Finset
open scoped Classical

def extractionFailureRate {Statement Oracle Challenge Response Query α : Type*}
    {Opening : Query → Type*} [Fintype Challenge] [DecidableEq Challenge]
    [Fintype Query] [DecidableEq Query]
    (protocol : PublicCoinIPCP Statement Oracle Challenge Response Query Opening)
    (prover : IPCPProver Statement Oracle Challenge Response) (statement : Statement)
    (extractor : Challenge → Response → Option α) : ℚ :=
  ((univ.filter fun coins : Challenge × Query =>
    protocol.accepts prover statement coins = true ∧
    extractor coins.1 (prover.respond statement (prover.commit statement) coins.1) = none).card : ℚ) /
      Fintype.card (Challenge × Query)

end LigeroFamily
