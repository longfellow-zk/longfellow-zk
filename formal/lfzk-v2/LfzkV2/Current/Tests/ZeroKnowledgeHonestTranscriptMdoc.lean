import LfzkV2.Current.ZeroKnowledge.HonestTranscriptRefresh
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptRoles
import LfzkV2.Current.ZeroKnowledge.OracleRefreshCompose

/-! The complete honest mdoc frontend and final batching prefix are actual
bounded query programs. Their construction has no oracle argument, while
the conformance theorems identify their runs with the existing staged prover.
Only ordinary foundational axioms occur in these proofs. -/

#check LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.program
#check LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.openingPrefix

#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.native_output
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.binaryRead_output
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.program_output
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.program_progress
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.openingPrefix_output
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.openingPrefix_progress
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.openingPrefix_internal_fresh
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.openingPrefix_update
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.program_rank
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.openingPrefix_rank
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.openingInput_atRun
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.opening_fresh
#print axioms LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc.opening_refresh_sameDistribution
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.Prefix.circuit_roles
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.Prefix.circuit_snapshots
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.Prefix.snapshots_frontend
#print axioms LfzkV2.Current.ZeroKnowledge.OracleRefreshCompose.fresh_iff_prior
