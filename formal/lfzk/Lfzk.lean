-- Ligero V1, round by round, on the `formal/ligero` analysis
import Lfzk.LigeroRbr
import Lfzk.LigeroV1Rbr
import Lfzk.LigeroV1Rows
-- the model
import Lfzk.Types
import Lfzk.WPoly
import Lfzk.Builder
import Lfzk.Circuit
import Lfzk.Rounds
import Lfzk.Layers
import Lfzk.LigeroRows
import Lfzk.LigeroSystem
-- LayerStep, round by round
import Lfzk.RbrBudgets
import Lfzk.RbrChain
import Lfzk.RbrLayerStep
import Lfzk.RbrLongfellow
import Lfzk.RbrSplit
import Lfzk.Nizk
import Lfzk.NizkMerkle
-- the certified rows
import Lfzk.CostV1
import Lfzk.LigeroV1LayerStep
import Lfzk.CertifiedV1
import Lfzk.ProfileMonoV1
-- Fiat–Shamir: grinding, re-committing, and the compiled verifier
import Lfzk.NizkGrinding
import Lfzk.NizkAdaptive
import Lfzk.CompiledLongfellow
-- the two-field MAC step
import Lfzk.Mac
import Lfzk.TwoField
import Lfzk.TwoFieldNizk
import Lfzk.TwoFieldBridge
import Lfzk.TwoFieldLongfellow
import Lfzk.TwoFieldV1
import Lfzk.TwoFieldV1Fields
import Lfzk.TwoFieldV1Rows
import Lfzk.NizkGrindingTwoField
import Lfzk.NizkAdaptiveTwoField
import Lfzk.CompiledLongfellowTwoField
-- the compiled verifier against a re-committing prover: `hlig` and `hright` discharged
import Lfzk.CompiledLongfellowAdaptive
-- the deployed v7 parameters (registry `zk_spec.rs`, version 7): rows and headlines
import Lfzk.LigeroV1RowsV7
import Lfzk.CertifiedV7
import Lfzk.TwoFieldV7Rows
import Lfzk.CompiledV7
-- the zero-knowledge verifier's rows and the pad (ported from `proofs/lfzk`)
import Lfzk.ZkHiding
import Lfzk.ZkSim
import Lfzk.ZkLayers
import Lfzk.Encode
-- zero knowledge: Ligero V1 (ported from `proofs/ligero`), Merkle hiding, the compiled argument
import Lfzk.LigeroZk.Witness
import Lfzk.LigeroZk.Distribution
import Lfzk.LigeroZk.Masking
import Lfzk.LigeroZk.Conditional
import Lfzk.LigeroZk.CoreTranslation
import Lfzk.LigeroZk.ResponseAdaptiveView
import Lfzk.LigeroZk.V1TapeTranslation
import Lfzk.LigeroZk.V1ResponseAdaptive
import Lfzk.FromLigeroZKV1
import Lfzk.ZkFiatShamir
import Lfzk.ZkMerkle
import Lfzk.ZkProgram
import Lfzk.ZkLongfellow
import Lfzk.CompiledLigeroZk
import Lfzk.TwoFieldZk
import Lfzk.ZkAdaptiveV1
import Lfzk.CompiledLongfellowZk
import Lfzk.ZkFrontendOfSetup
import Lfzk.ZkTwoTape
import Lfzk.CompiledLongfellowZkTwoField
import Lfzk.CompiledLongfellowZkV7
-- Fiat–Shamir with hash inputs as deployed: message prefixes only, challenges never re-absorbed
import Lfzk.NizkDeployedHash
import Lfzk.NizkDeployedHashAdaptive
import Lfzk.NizkDeployedHashTwoField
import Lfzk.NizkDeployedHashV7
-- the list factor charged at the field slots only (no list factor at the two Ligero slots)
import Lfzk.RbrLayerStepS
import Lfzk.RbrSplitS
import Lfzk.NizkAdaptiveS
import Lfzk.CompiledLongfellowAdaptiveS
import Lfzk.CompiledV7S
-- soundness against the deployed zero-knowledge verifier (padded rounds, statement built from the
-- transcript, `begin_circuit`'s point drawn, per-layer betas, dead-end assertions; no `hfalse`)
import Lfzk.ZkMultilinear
import Lfzk.RbrZkLongfellow
import Lfzk.RbrZkSplit
import Lfzk.ZkLigeroV1
import Lfzk.NizkZk
import Lfzk.CompiledZk
import Lfzk.CompiledZkRows
import Lfzk.NizkZkTwoField
import Lfzk.CompiledZkTwoField
import Lfzk.CompiledZkTwoFieldRows
-- the deployed zero-knowledge verifier with Fiat–Shamir hash inputs as deployed (message prefixes)
import Lfzk.NizkZkDeployedHash
import Lfzk.CompiledZkDeployedHash
import Lfzk.CompiledZkDeployedHashRows
-- the arithmetization, constructed from a concrete layered quadratic circuit
import Lfzk.ConcreteCircuit
import Lfzk.ConcreteCircuitBridge
import Lfzk.ZkArithInit
import Lfzk.ZkArithBoundary
-- the arithmetization at the deployed width profile (per-layer widths, interleaved hands)
import Lfzk.ZkArithProfile
-- the end-to-end headlines: deployed verifier, deployed hash inputs, field half from the circuits
import Lfzk.CompiledZkProfileRows

/-!
# Longfellow NIZK knowledge soundness

The round-by-round LayerStep of the Longfellow protocol, its Fiat–Shamir compilation as the
deployed prover and verifier use it, the Ligero V1 budgets built from the `ligero/` analysis, and
the two-field MAC step.  See `lfzk/README.md`.
-/
