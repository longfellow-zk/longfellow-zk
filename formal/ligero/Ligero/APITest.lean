import Ligero.API
import examples.Ligero.Longfellow.EnvelopeFSCertificates

/-! Compile-time checks for the retained scalar IOP/FS extraction API. -/

-- Scalar, response-uniform IOP extraction and the false-statement corollary.
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.compatible_unique
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.extract_valid
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.Certificate.response_fraction_le_envelope
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.Certificate.envelope_mean
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.Certificate.false_statement
#guard_msgs (drop info) in #check Ligero.V1.scalarGap_extraction_failure
#guard_msgs (drop info) in #check Ligero.V2.scalarGap_extraction_failure
#guard_msgs (drop info) in #check Ligero.V3.scalarGap_extraction_failure
/-- info: 'Ligero.V1.scalarGap_extraction_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ligero.V1.scalarGap_extraction_failure
/-- info: 'Ligero.V2.scalarGap_extraction_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ligero.V2.scalarGap_extraction_failure
/-- info: 'Ligero.V3.scalarGap_extraction_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ligero.V3.scalarGap_extraction_failure

#guard_msgs (drop info) in #check Ligero.V1.scalarGap_iop_extraction_failure
/-- info: 'Ligero.V1.scalarGap_iop_extraction_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ligero.V1.scalarGap_iop_extraction_failure
#guard_msgs (drop info) in #check Ligero.V2.scalarGap_iop_extraction_failure
/-- info: 'Ligero.V2.scalarGap_iop_extraction_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ligero.V2.scalarGap_iop_extraction_failure
#guard_msgs (drop info) in #check Ligero.V3.scalarGap_iop_extraction_failure
/-- info: 'Ligero.V3.scalarGap_iop_extraction_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ligero.V3.scalarGap_iop_extraction_failure

#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.extract_agreement_errors

-- Hahn/Delsarte count behind the V1 unchecked-mask list (Johnson is degree one).
#guard_msgs (drop info) in #check CodingTheory.UniformFamilyBound
#guard_msgs (drop info) in #check CodingTheory.UniformFamilyBound.of_le_size
#guard_msgs (drop info) in #check CodingTheory.card_le_of_uniformFamilyBound
#guard_msgs (drop info) in #check CodingTheory.InterleavedJohnson.uniformFamilyBound_of_denominator_pos
#guard_msgs (drop info) in #check CodingTheory.HahnDelsarte.sum_hahnWeight_mul_hahnWeight
#guard_msgs (drop info) in #check CodingTheory.HahnDelsarte.hahnKernel_one
#guard_msgs (drop info) in #check CodingTheory.HahnDelsarte.hahnKernel_gram_nonneg
#guard_msgs (drop info) in #check CodingTheory.HahnDelsarte.card_le_of_delsarte
#guard_msgs (drop info) in #check CodingTheory.HahnDelsarte.uniformFamilyBound_of_certificate
#guard_msgs (drop info) in #check Ligero.V1.V1MaskRange
#guard_msgs (drop info) in #check Ligero.V1.V1JohnsonRange.toMaskRange
/-- info: 'CodingTheory.HahnDelsarte.card_le_of_delsarte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CodingTheory.HahnDelsarte.card_le_of_delsarte
/-- info: 'CodingTheory.HahnDelsarte.uniformFamilyBound_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CodingTheory.HahnDelsarte.uniformFamilyBound_of_certificate
-- Degree one recovers Johnson: pairwise disjoint pairs in `Fin 6` are certified by `[6, 1]`.
example : CodingTheory.HahnDelsarte.certificateValid 6 2 0 [6, 1] = true := by decide +kernel
example : CodingTheory.HahnDelsarte.certifiedBound 6 2 [6, 1] = 3 := by decide +kernel

-- Refined scalar extraction and the response-uniform envelope.
#guard_msgs (drop info) in #check Ligero.V1.scalarGap_profiled_extraction_failure
/-- info: 'Ligero.V1.scalarGap_profiled_extraction_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ligero.V1.scalarGap_profiled_extraction_failure
#guard_msgs (drop info) in #check Ligero.V2.scalarGap_profiled_extraction_failure
/-- info: 'Ligero.V2.scalarGap_profiled_extraction_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ligero.V2.scalarGap_profiled_extraction_failure
#guard_msgs (drop info) in #check Ligero.V3.scalarGap_profiled_extraction_failure
/-- info: 'Ligero.V3.scalarGap_profiled_extraction_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ligero.V3.scalarGap_profiled_extraction_failure
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.response_fraction_le_profiledUniformEnvelope
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies
/-- info: 'LigeroFamily.ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms LigeroFamily.ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies

#guard_msgs (drop info) in #check LigeroFamily.extractionFailureRate
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.CheckedArithmeticBudget
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.checked_gap_certificate
#guard_msgs (drop info) in #check LigeroFamily.ScalarGapExtraction.checked_profiled_extraction_failure
/-- info: 'LigeroFamily.ScalarGapExtraction.checked_profiled_extraction_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms LigeroFamily.ScalarGapExtraction.checked_profiled_extraction_failure

#guard_msgs (drop info) in #check Bcs.EnvelopeFiatShamir.ResponseUniformBound
#guard_msgs (drop info) in #check Bcs.EnvelopeFiatShamir.extraction_ratio_le_capped
#guard_msgs (drop info) in #check LigeroFamily.EnvelopeFS.Experiment
#guard_msgs (drop info) in #check LigeroFamily.EnvelopeFS.compiledAccepts
#guard_msgs (drop info) in #check LigeroFamily.EnvelopeFS.extract
#guard_msgs (drop info) in #check LigeroFamily.EnvelopeFS.extraction_ratio_le
#guard_msgs (drop info) in #check LigeroFamily.EnvelopeFS.soundness_ratio_le
/-- info: 'Bcs.EnvelopeFiatShamir.extraction_ratio_le_capped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Bcs.EnvelopeFiatShamir.extraction_ratio_le_capped
#guard_msgs (drop info) in #check Bcs.FiniteProbability.density_product_gate_le
#guard_msgs (drop info) in #check LigeroFamily.EnvelopeFS.Experiment.compiledBound_dyadic
/-- info: 'LigeroFamily.EnvelopeFS.Experiment.compiledBound_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LigeroFamily.EnvelopeFS.Experiment.compiledBound_dyadic
/-- info: 'LigeroFamily.EnvelopeFS.extraction_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LigeroFamily.EnvelopeFS.extraction_ratio_le
/-- info: 'LigeroFamily.EnvelopeFS.soundness_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LigeroFamily.EnvelopeFS.soundness_ratio_le

#guard_msgs (drop info) in #check Bcs.EnvelopeFiatShamir.FixedKey.extraction_ratio_le_capped
/-- info: 'Bcs.EnvelopeFiatShamir.FixedKey.extraction_ratio_le_capped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Bcs.EnvelopeFiatShamir.FixedKey.extraction_ratio_le_capped

#guard_msgs (drop info) in #check Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.v7Sig_v1_fs_extraction
#guard_msgs (drop info) in #check Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.v8Sig_v2_fs_extraction
#guard_msgs (drop info) in #check Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized.v8Hash4_v3_fs_soundness
