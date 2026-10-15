// Benchmark-only configuration overlay. All other C++ headers are unchanged.
#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_TESTS_SHA3_SHA3_SLICING_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_TESTS_SHA3_SHA3_SLICING_H_
#include <cstddef>
namespace proofs {
static inline bool sha3_slice_at(size_t round) {
  constexpr size_t period = 4;
  return round == 0 || round == 23 || round % period == period - 1;
}
}  // namespace proofs
#endif
