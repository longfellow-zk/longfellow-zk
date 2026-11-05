import LfzkV2.RuntimeProfiles

/-! Exact backend certificates for the packed native runtime. Both sides use
the same geometry; the smaller hash field needs a different committed-list
cutoff in the soundness analysis. This cutoff changes no protocol parameter. -/

namespace LfzkV2.Packed.RuntimeProfiles

open LfzkV2.RuntimeProfiles

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Hash

theorem committedPacking : CodingTheory.UniformFamilyBound 2912 1136 415 25 := by
  have h := CodingTheory.InterleavedJohnson.uniformFamilyBound_of_denominator_pos
    (n := 2912) (d := 2497) (E := 1776) (by decide) (by decide) (by decide)
    (by norm_num [CodingTheory.InterleavedJohnson.denominator])
  simpa [CodingTheory.InterleavedJohnson.listBound,
    CodingTheory.InterleavedJohnson.denominator] using h

def profile : Profile where
  n := 2912
  k := 416
  s := 15
  t := 86
  cutoff := 1136
  threshold := 1142
  candidates := 25
  capacities := 243
  minimumField := 2^128
  queryUnits := 925
  positive := by decide
  large := by decide
  query_pos := by decide
  overlap_lt := by decide
  field_pos := by decide
  cutoff_gt := by decide
  threshold_pos := by decide
  threshold_large := by decide
  committedPacking := committedPacking
  systemPacking := LfzkV2.RuntimeProfiles.Signature.systemPacking
  rank := by norm_num [Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]
  query := by norm_num [Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]

end Hash

namespace Signature

abbrev profile : Profile := LfzkV2.RuntimeProfiles.Signature.profile

end Signature
end LfzkV2.Packed.RuntimeProfiles
