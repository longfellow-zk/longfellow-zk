import LfzkV2.Current.ApplicationSetup

/-! The sampler projections of the current verifier: how one ideal answer
supplies each challenge. The verifier arithmetic reads challenges through
these projections only. -/
namespace LfzkV2.Current.ConcreteMetadata
local notation "N" => ZMod Adapter.Mdoc.primeOrder

/-- Sampler operations have the same role as the ideal sampler interface in
the endpoint theorem. In particular both conversion coordinates read one answer. -/
structure Samples (B C : Type) [Field B] where
  binary : C → ℕ → B
  binaryNonzero : C → Linear.TerminalSampling.Nonzero B
  prime : C → ℕ → N
  primeNonzero : C → Linear.TerminalSampling.Nonzero N
  conversion : C → Fin 2 → Linear.TerminalSampling.Nonzero N
  fallback : C

end LfzkV2.Current.ConcreteMetadata
