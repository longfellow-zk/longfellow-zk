-- Ligero V1, round by round, on the `formal/ligero` analysis
import LfzkV1.LigeroRbr
import LfzkV1.LigeroV1Rbr
import LfzkV1.LigeroV1Rows
-- the model
import LfzkV1.Types
import LfzkV1.WPoly
import LfzkV1.Builder
import LfzkV1.Circuit
import LfzkV1.Rounds
import LfzkV1.Layers
import LfzkV1.LigeroRows
import LfzkV1.LigeroSystem
-- LayerStep, round by round
import LfzkV1.RbrBudgets
import LfzkV1.RbrChain
import LfzkV1.RbrLayerStep
import LfzkV1.RbrLongfellow
import LfzkV1.RbrSplit
import LfzkV1.Nizk
import LfzkV1.NizkMerkle
-- the certified rows
import LfzkV1.CostV1
import LfzkV1.LigeroV1LayerStep
import LfzkV1.CertifiedV1
import LfzkV1.ProfileMonoV1
-- Fiat–Shamir: grinding, re-committing, and the compiled verifier
import LfzkV1.NizkGrinding
import LfzkV1.NizkAdaptive
import LfzkV1.CompiledLongfellow
-- the two-field MAC step
import LfzkV1.Mac
import LfzkV1.TwoField
import LfzkV1.TwoFieldNizk
import LfzkV1.TwoFieldBridge
import LfzkV1.TwoFieldLongfellow
import LfzkV1.TwoFieldV1
import LfzkV1.TwoFieldV1Fields
import LfzkV1.TwoFieldV1Rows
import LfzkV1.IdealSampler
import LfzkV1.NizkGrindingTwoField
import LfzkV1.NizkAdaptiveTwoField
import LfzkV1.CompiledLongfellowTwoField
-- the compiled verifier against a re-committing prover: `hlig` and `hright` discharged
import LfzkV1.CompiledLongfellowAdaptive
-- the deployed v7 parameters (registry `zk_spec.rs`, version 7): rows and headlines
import LfzkV1.LigeroV1RowsV7
import LfzkV1.CertifiedV7
import LfzkV1.TwoFieldV7Rows
-- the zero-knowledge verifier's rows and the pad (ported from `proofs/lfzk-v1`)
import LfzkV1.ZkHiding
import LfzkV1.ZkSim
import LfzkV1.ZkLayers
import LfzkV1.Encode
-- zero knowledge: Ligero V1 (ported from `proofs/ligero`), Merkle hiding, the compiled argument
import LfzkV1.LigeroZk.Witness
import LfzkV1.LigeroZk.Distribution
import LfzkV1.LigeroZk.Masking
import LfzkV1.LigeroZk.Conditional
import LfzkV1.LigeroZk.CoreTranslation
import LfzkV1.LigeroZk.ResponseAdaptiveView
import LfzkV1.LigeroZk.V1TapeTranslation
import LfzkV1.LigeroZk.V1ResponseAdaptive
import LfzkV1.FromLigeroZKV1
import LfzkV1.ZkFiatShamir
import LfzkV1.ZkMerkle
import LfzkV1.ZkProgram
import LfzkV1.ZkLongfellow
import LfzkV1.CompiledLigeroZk
import LfzkV1.TwoFieldZk
import LfzkV1.ZkAdaptiveV1
import LfzkV1.CompiledLongfellowZk
import LfzkV1.ZkFrontendOfSetup
import LfzkV1.ZkTwoTape
import LfzkV1.CompiledLongfellowZkTwoField
-- Fiat–Shamir with hash inputs as deployed: message prefixes only, challenges never re-absorbed
import LfzkV1.NizkDeployedHash
import LfzkV1.NizkDeployedHashAdaptive
import LfzkV1.NizkDeployedHashTwoField
-- the list factor charged at the field slots only (no list factor at the two Ligero slots)
import LfzkV1.RbrLayerStepS
import LfzkV1.RbrSplitS
import LfzkV1.NizkAdaptiveS
import LfzkV1.CompiledLongfellowAdaptiveS
-- soundness against the deployed zero-knowledge verifier (padded rounds, statement built from the
-- transcript, `begin_circuit`'s point drawn, per-layer betas, dead-end assertions; no `hfalse`)
import LfzkV1.ZkMultilinear
import LfzkV1.RbrZkLongfellow
import LfzkV1.RbrZkSplit
import LfzkV1.ZkLigeroV1
import LfzkV1.NizkZk
import LfzkV1.CompiledZk
import LfzkV1.CompiledZkRows
import LfzkV1.NizkZkTwoField
import LfzkV1.CompiledZkTwoField
import LfzkV1.CompiledZkTwoFieldRows
-- the deployed zero-knowledge verifier with Fiat–Shamir hash inputs as deployed (message prefixes)
import LfzkV1.NizkZkDeployedHash
import LfzkV1.CompiledZkDeployedHash
import LfzkV1.CompiledZkDeployedHashRows
-- the arithmetization, constructed from a concrete layered quadratic circuit
import LfzkV1.ConcreteCircuit
import LfzkV1.ConcreteCircuitBridge
import LfzkV1.ZkArithInit
import LfzkV1.ZkArithBoundary
-- the arithmetization at the deployed width profile (per-layer widths, interleaved hands)
import LfzkV1.ZkArithProfile
-- the end-to-end headlines: deployed verifier, deployed hash inputs, field half from the circuits
import LfzkV1.CompiledZkProfileRows
-- Hahn/Delsarte mask bounds, a tighter T-security conversion, and audit checks
import LfzkV1.CompiledZkProfileHahn
import LfzkV1.SoundnessAudit
-- the two-field MAC with separate private witnesses (v7 shifted multiplier, v8 additive blind),
-- and the v7 MAC's zero-knowledge statement
import LfzkV1.MacSep
import LfzkV1.NizkZkDeployedHashSepMac
import LfzkV1.TwoFieldSepMacRows
import LfzkV1.CompiledZkProfileSepMac
import LfzkV1.CompiledLongfellowZkV7Mac
import LfzkV1.V7ZkProfile
import LfzkV1.V7ZkProfileInstance
import LfzkV1.V7Soundness125
import LfzkV1.V7Soundness125Instance

/-!
# Longfellow NIZK knowledge soundness

The round-by-round LayerStep of the Longfellow protocol, its Fiat–Shamir compilation as the
deployed prover and verifier use it, the Ligero V1 budgets built from the `ligero/` analysis, and
the two-field MAC step.  See `lfzk-v1/README.md`.
-/
