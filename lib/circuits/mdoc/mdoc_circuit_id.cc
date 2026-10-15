// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <stdint.h>
#include <sys/types.h>

#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <vector>

#include "circuits/mdoc/mdoc_decompress.h"
#include "circuits/mdoc/mdoc_zk.h"
#include "ec/p256.h"
#include "gf2k/gf2_128.h"
#include "proto/circuit_io.h"
#include "proto/circuit_reader.h"
#include "sumcheck/circuit_id.h"
#include "util/crypto.h"
#include "util/log.h"
#include "util/readbuffer.h"
#include "zstd.h"

namespace proofs {

using f_128 = GF2_128<>;

extern "C" {

int circuit_id(uint8_t id[/*kSHA256DigestSize*/], const uint8_t* bcp,
               size_t bcsz, const ZkSpecStruct* zk_spec) {
  if (id == nullptr || bcp == nullptr || zk_spec == nullptr) {
    return 0;
  }
  SHA256 sha;
  uint8_t cid[kSHA256DigestSize];

  std::vector<uint8_t> bytes;  // sized by decompress from the frame header
  size_t full_size = decompress(bytes, bcp, bcsz);

  ReadBuffer rb_circuit(bytes.data(), full_size);
  CircuitReader<Fp256Base> cr_s(p256_base, P256_ID);
  auto c_sig = cr_s.from_bytes(rb_circuit, /*enforce_circuit_id=*/true);
  if (c_sig == nullptr) {
    log(ERROR, "signature circuit could not be parsed");
    return 0;
  }
  circuit_id(cid, *c_sig, p256_base);
  sha.Update(cid, kSHA256DigestSize);

  const f_128 Fs;
  CircuitReader<f_128> cr_h(Fs, GF2_128_ID);
  auto c_hash = cr_h.from_bytes(rb_circuit, /*enforce_circuit_id=*/true);
  if (c_hash == nullptr) {
    log(ERROR, "circuit could not be parsed");
    return 0;
  }

  size_t remaining = rb_circuit.remaining();
  if (remaining != 0) {
    log(ERROR, "circuit bytes contains extra data: %zu bytes", remaining);
    return 0;
  }

  circuit_id(cid, *c_hash, Fs);
  sha.Update(cid, kSHA256DigestSize);

  sha.DigestData(id);
  return 1;
}

} /* extern "C" */
}  // namespace proofs
