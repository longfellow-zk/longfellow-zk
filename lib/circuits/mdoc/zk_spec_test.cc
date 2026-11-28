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

#include <sys/types.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iterator>
#include <string>

#include "circuits/mdoc/mdoc_examples.h"
#include "circuits/mdoc/mdoc_test_attributes.h"
#include "circuits/mdoc/mdoc_zk.h"
#include "util/crypto.h"
#include "util/log.h"
#include "gtest/gtest.h"

#ifndef MDOC_CIRCUITS_DIR
#define MDOC_CIRCUITS_DIR "circuits/mdoc/circuits"
#endif

namespace proofs {
namespace {

TEST(ZkSpecTest, FindZkSpec) {
  const ZkSpecStruct& zk_spec = kZkSpecs[0];

  const ZkSpecStruct* found_zk_spec =
      find_zk_spec("longfellow-libzk-v1", zk_spec.circuit_hash);
  EXPECT_NE(found_zk_spec, nullptr);
  EXPECT_EQ(found_zk_spec->system, zk_spec.system);
  EXPECT_EQ(found_zk_spec->circuit_hash, zk_spec.circuit_hash);
  EXPECT_EQ(found_zk_spec->num_attributes, zk_spec.num_attributes);
  EXPECT_EQ(found_zk_spec->version, zk_spec.version);
}

TEST(ZkSpecTest, ReturnNullptrIfNoMatchingZkSpecFound) {
  const ZkSpecStruct* zk_spec = find_zk_spec(
      "longfellow-libzk-v1",
      "1234567890123456789012345678901234567890123456789012345678901234");
  EXPECT_EQ(zk_spec, nullptr);
}

void test_circuit_hash(size_t num_attributes) {
  // Find the latest version of the circuit for the given number of attributes.
  const ZkSpecStruct* zk_spec = nullptr;
  for (int i = 0; i < kNumZkSpecs; ++i) {
    if (kZkSpecs[i].num_attributes == num_attributes) {
      if (zk_spec == nullptr || kZkSpecs[i].version > zk_spec->version) {
        zk_spec = &kZkSpecs[i];
      }
    }
  }

  uint8_t* circuit;
  size_t circuit_len;
  auto ret = generate_circuit(zk_spec, &circuit, &circuit_len);
  EXPECT_EQ(ret, CIRCUIT_GENERATION_SUCCESS);

  uint8_t cid[kSHA256DigestSize];
  EXPECT_TRUE(circuit_id(cid, circuit, circuit_len, zk_spec));

  char buf[kSHA256DigestSize * 2 + 1] = {};
  hex_to_str(buf, cid, kSHA256DigestSize);
  log(INFO, "circuit hash %zu attr:: %s", num_attributes, buf);

  bool found = false;
  for (size_t k = 0; k < kNumZkSpecs; ++k) {
    if (strcmp(kZkSpecs[k].circuit_hash, buf) == 0) {
      found = true;
      break;
    }
  }
  // Must use free because generate_circuit is a pure C library that allocates
  // with malloc.
  free(circuit);
  EXPECT_TRUE(found);
}

// These tests ensure that the current circuit hash for 1--4 attributes is
// included in the zk_spec data structure.
// They are defined separately so that they can run in parallel.
// They can be run using
//    blaze test -c opt --test_output=streamed  \
//        //circuits/mdoc:zk_spec_test
// in order to print out the new circuit hashes.
TEST(ZkSpecTest, CorrectSpecFor1Attribute) { test_circuit_hash(1); }

TEST(ZkSpecTest, CorrectSpecFor2Attributes) { test_circuit_hash(2); }

TEST(ZkSpecTest, CorrectSpecFor3Attributes) { test_circuit_hash(3); }

TEST(ZkSpecTest, CorrectSpecFor4Attributes) { test_circuit_hash(4); }

void test_proof_creation_and_verification(const ZkSpecStruct& zk_spec) {
  // Read the circuit file from circuits/hash.
  std::string cp = std::string(MDOC_CIRCUITS_DIR) + "/" + zk_spec.circuit_hash;
  std::ifstream in(cp, std::ios::binary);
  ASSERT_TRUE(in.is_open()) << "Failed to open circuit file: " << cp;
  std::string circuit_bytes((std::istreambuf_iterator<char>(in)),
                            std::istreambuf_iterator<char>());
  ASSERT_FALSE(circuit_bytes.empty());

  const MdocTests* test = &mdoc_tests[3]; /* Sprind example w/4 attributes  */
  RequestedAttribute claims[4] = {test::age_over_18,
                                  test::familyname_mustermann,
                                  test::birthdate_1971_09_01, test::height_175};

  uint8_t* zkproof;
  size_t proof_len;

  {
    log(INFO, "starting prover");
    MdocProverErrorCode ret = run_mdoc_prover(
        (uint8_t*)circuit_bytes.data(), circuit_bytes.size(), test->mdoc,
        test->mdoc_size, test->pkx.as_pointer, test->pky.as_pointer,
        test->transcript, test->transcript_size, claims, zk_spec.num_attributes,
        (const char*)test->now, &zkproof, &proof_len, &zk_spec);
    EXPECT_EQ(ret, MDOC_PROVER_SUCCESS);
  }
  {
    log(INFO, "starting verifier");
    MdocVerifierErrorCode ret = run_mdoc_verifier(
        (uint8_t*)circuit_bytes.data(), circuit_bytes.size(),
        test->pkx.as_pointer, test->pky.as_pointer, test->transcript,
        test->transcript_size, claims, zk_spec.num_attributes,
        (const char*)test->now, zkproof, proof_len, test->doc_type, &zk_spec);
    EXPECT_EQ(ret, MDOC_VERIFIER_SUCCESS);
    free(zkproof);
  }
}

// Test proof creation and verification against all supported circuits.
TEST(ZkSpecTest, ProofCreationAndVerification) {
  for (size_t k = 0; k < kNumZkSpecs; ++k) {
    const ZkSpecStruct& zk_spec = kZkSpecs[k];
    log(INFO, "Testing circuit hash %s, %zu attributes", zk_spec.circuit_hash,
        zk_spec.num_attributes);
    test_proof_creation_and_verification(zk_spec);
  }
}

}  // namespace
}  // namespace proofs
