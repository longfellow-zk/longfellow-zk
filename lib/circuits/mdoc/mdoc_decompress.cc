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

#include "circuits/mdoc/mdoc_decompress.h"

#include <cstddef>
#include <cstdint>
#include <vector>

#include "util/log.h"
#include "zstd.h"

#include "circuits/mdoc/mdoc_zk.h"

namespace proofs {

// Decompress a circuit representation into a vector that has been reserved
// with size len.  The value len needs to be a good upper-bound estimate on
// the size of the uncompressed string.
size_t decompress(std::vector<uint8_t>& bytes, const uint8_t* compressed,
                  size_t compressed_len) {
  // Size the output buffer from the frame header rather than from the
  // kCircuitSizeMax upper bound. Constructing a std::vector of that bound
  // value-initialises 130 MB -- every page written, so every page resident --
  // when the v6 circuit needs only 87.7 MB of it.
  unsigned long long fcs = ZSTD_getFrameContentSize(compressed, compressed_len);
  size_t want = kCircuitSizeMax;
  if (fcs != ZSTD_CONTENTSIZE_ERROR && fcs != ZSTD_CONTENTSIZE_UNKNOWN &&
      fcs <= (unsigned long long)kCircuitSizeMax) {
    want = (size_t)fcs;
  }
  if (bytes.size() < want) {
    bytes.resize(want);
  }

  size_t res =
      ZSTD_decompress(bytes.data(), bytes.size(), compressed, compressed_len);

  if (ZSTD_isError(res)) {
    log(ERROR, "zlib.UncompressAtMost failed: %s", ZSTD_getErrorName(res));
    return 0;
  }
  return res;
}

}  // namespace proofs
