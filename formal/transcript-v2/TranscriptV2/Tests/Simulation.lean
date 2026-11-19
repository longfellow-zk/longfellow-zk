import TranscriptV2.Simulation

namespace TranscriptV2.Tests.Simulation
open TranscriptV2.Simulation Bcs.FiniteProbability Merkle.RandomOracle
open scoped Classical

private def real (_ : Unit) : OracleBoundary Bool Bool Bool Unit :=
  ⟨false,id,[(false,false)],()⟩

private def simulated (_ : Unit) : OracleBoundary Bool Bool Bool Unit :=
  ⟨false,fun _ => false,[(false,false)],()⟩

-- Full observed answers and proof equations agree even though an unqueried
-- coordinate differs. The interface must not expose the entire oracle table.
example : (real ()).oracle true ≠ (simulated ()).oracle true := by decide

end TranscriptV2.Tests.Simulation
