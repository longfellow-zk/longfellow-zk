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

#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

#include "algebra/convolution.h"
#include "algebra/fp2.h"
#include "algebra/reed_solomon.h"
#include "algebra/static_string.h"
#include "arrays/dense.h"
#include "circuits/compiler/circuit_dump.h"
#include "circuits/compiler/compiler.h"
#include "circuits/ecdsa/verify_circuit.h"
#include "circuits/ecdsa/verify_witness.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "ec/p256.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "sumcheck/testing.h"
#include "util/log.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"
#include "benchmark/benchmark.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {
struct ecdsa_testvec {
  StaticString pk_x, pk_y;
  StaticString e, r, s;
};

static const struct ecdsa_testvec P256_TEST[] = {
    {
        StaticString("0x88903e4e1339bde78dd5b3d7baf3efdd72eb5bf5aaaf686c8f9ff5e"
                     "7c6368d9c"),
        StaticString("0xeb8341fc38bb802138498d5f4c03733f457ebbafd0b2fe38e6f5862"
                     "6767f9e75"),
        StaticString("0x2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e8"
                     "86266e7ae"),
        StaticString(
            "0xc71bcbfb28bbe06299a225f057797aaf5f22669e90475de5f64176b2612671"),
        StaticString("0x42ad2f2ec7b6e91360b53427690dddfe578c10d8cf480a66a6c2410"
                     "ff4f6dd40"),
    },
    {StaticString(
         "0x105ccb7bd3bcc142082519cbe5b740b31c1bc8d5db8cd694e6f0a20c4198cd1"),
     StaticString(
         "0x494c2641ebf3be217f8a9a53ce0fc9768b2403024cb3f7a54fd1a78e972bc991"),
     StaticString(
         "0x7d54b750c56c32c1ef1b2c96f40739895b06ca0638a461287e802498b53583ae"),
     StaticString(
         "0x2fb4dae21a614a417f9fe42a54861425c38d1b861e0eaa6bf0a45709f02c85c6"),
     StaticString(
         "0xfb6f08a3a1640292b3ad9fb713a08f2392995fbbb4c2c1cd3c36a212246a7b6c")},
    {StaticString(
         "0xc054b53cd047893ac412dc779f50c7b00c38e5c3eceb29ecd8620999346d1503"),
     StaticString(
         "0x569881c1b54d03b28a083a8da37251b8e8fbc8dda44721f749176f6552d577e5"),
     StaticString(
         "0xf2ba08a9ad9e88d73538b01777dde3843182ad74e4ab80ac640049eecd027225"),
     StaticString(
         "0x40e11fee99753c42aa0327c102b53a49bf3654e2eb0cd09d2d54841aa1e33603"),
     StaticString(
         "0x25b8e6b6abb83cbdcc5d200cc9100f9e4ccee64420d27c21a5fe3b033636838d")},
    {StaticString(
         "0x92b31ba01ef2e229bd26822ab3a8763d9da40d8750c7c1534e84c3f209489836"),
     StaticString(
         "0x0e03689aed2711eec3a278316fcc8e965a65d5779d66036fde17a7bb265328e0"),
     StaticString(
         "0x3ad98d5cf8b691729bb684d7067b409e79aaf9359ced9972600e528d93a17ad2"),
     StaticString(
         "0xcdaec1053293d385857eff2896c63ea63a897b1d5f9114b147220d24eb61f7b7"),
     StaticString(
         "0x2f9389d65d9995e37e81ac4bdd0691ca7f325beb7474ecd6bde8c7aca58ab32d")},
    {StaticString(
         "0xdc1c1f55cff4cd5c76cf4169278f7217667f86ee81d8669b63f2e19bc12a0c9f"),
     StaticString(
         "0x12355dd0385fed3bc33bedc9781b9aad47b33e4c24704b8d14288b1b3cb45c28"),
     StaticString(
         "0x9e73b3df1394f4b17525fbe3d9f836b78d0f65840e7bf6b8c2b9b4972acbb780"),
     StaticString(
         "0x3D3197DE1E862DF865F04ACF13E72AE3DB4C8F6789049DB59C2C6B9F3BF7F460"),
     StaticString(
         "0x570FC235961E62E2A19A435E2F2802B1F10701E2E9D049A534C4535042DD8229")},
    {StaticString(
         "0x6d375ca27ae82d882ef5f50db5e94102aea455d0af5bfdd47b1e3a60ed97edaa"),
     StaticString(
         "0x18f64ba26e6ec9694a61c925ccf0d3766ff4a6b58040b8a43607b6eef966dbb"),
     StaticString(
         "0xd05f71edcd81f3f181042db9367873d873a30e4bc6736c08640b022aeb199a8b"),
     StaticString(
         "0x94c00eb61d5947b5e9786e464243eb1aadb69bcd1b64852dd73721a6a187ee9e"),
     StaticString(
         "0x3e2908351b7d9b9feaefeb2f8b32ecdee42151d043e7f63491e6333c58dc507f")},
    {StaticString(
         "0xe57ecf19f5790ceea156579531d258e025d3518c64ef8c353921cad45831420f"),
     StaticString(
         "0x551e76295ad864a3d057808ba9a57a61676d19700a5e5bfb8563a74057ed2295"),
     StaticString(
         "0x389f71c0bdad464e53c64628c1024967f3cd13e918367c352b2d24e845d21935"),
     StaticString(
         "0x5bb78d72deb16d1f6390b3d092e4bc95758e5c8f35a287f7d7785ef071204899"),
     StaticString(
         "0x19fc8d719596696401cb4e0dc28610957e34061788cc4cf099fab8bfbda00c0d")},
    {StaticString(
         "0xe277dbbf59f37362111f61ae7ae8891a5fc8216cf058aede1d9922756f17fa45"),
     StaticString(
         "0x2077085f8a157ba4be3a8b9ea390439244db6201c737dd58fb83a9b19b388c1d"),
     StaticString(
         "0x9162600824eb1c62069bcb656722dedce2af636e1ff7cd0922fe29b5096ae3cd"),
     StaticString(
         "0xe29cc486a0d42472205d125ede804920d779452d7e96047b82d8d3633e87dfaf"),
     StaticString(
         "0xd640fc77a00db25e48c9f89734ad2a192069957819860c5d372a53d7c6a70b8e")},
    // smaller pk
    {StaticString(
         "0x53556c0b8714f3dad02c3cdd570b7831182152df7265ab976725ea26c354f"),
     StaticString(
         "0x45eaaeb3cd6cfd67cb35b7a4efce2c80e38756f10f3fa631d332a6792f9c07b9"),
     StaticString(
         "0x215b9dbb044dc7d270f927887ae2e1ced888f3a609fe0eb8610e2f59f9f0456d"),
     StaticString(
         "0xb52d02cba797a9fecc4ad08286d3b411222da335cca301ff9af2a103351ab88a"),
     StaticString(
         "0x6d5e2cc8fb2f1ea3d781d36a6436a6b40c520c621cbfb6a76cfd88e50456a5f5")},
    // small pk and small e
    {StaticString(
         "0x34ccea4289f78756697fccd5fe555ce37e45893c79b25ee5073f05cc30ce1"),
     StaticString(
         "0xa184f469cd90a80b5fb382cf6de4f89bbf67009039786e0de9e434edaffd9371"),
     StaticString(
         "0x0000000000000000000000000000000001000000000000000000000000000000"),
     StaticString(
         "0xc6d1f3abcad6c11412546695d6fc46d6e3237cfe2bc523909789595182ccfb40"),
     StaticString(
         "0x8c2992eb37d7b152d668bf6b35a2fdf6a580fc7eda31b77c2c6d67d6b2d7646f")},
    // small r value for sig
    {StaticString(
         "0xbfb7fb8c8d241f2fa8ff70fa1799cde5796d1d316f17a556666b52c2bc2e7712"),
     StaticString(
         "0x65ddbe1fdeac4074d0f6b7b9e8987b44e0d962fa93a55d6fbae9eaf49e0b82c"),
     StaticString(
         "0x0000000000000000000000000000000001000000000000000000000000000000"),
     StaticString(
         "0x56bf962a6cc889cf1634e299cd8b44ae992790185b920dac52b8e0212b9f"),
     StaticString(
         "0x101736305e0c1be90981cd289c97a5c876b86d70cbe5f7342ff3ebd12cabdd30")},
};

static const struct ecdsa_testvec P256_FAILS[] = {
    // bad signature
    {
        StaticString("0x78903e4e1339bde78dd5b3d7baf3efdd72eb5bf5aaaf686c8f9ff5e"
                     "7c6368d9c"),
        StaticString("0xeb8341fc38bb802138498d5f4c03733f457ebbafd0b2fe38e6f5862"
                     "6767f9e75"),
        StaticString("0x2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e8"
                     "86266e7ae"),
        StaticString(
            "0xc71bcbfb28bbe06299a225f057797aaf5f22669e90475de5f64176b2612671"),
        StaticString("0x42ad2f2ec7b6e91360b53427690dddfe578c10d8cf480a66a6c2410"
                     "ff4f6dd40"),
    },
    // zero values, or values that are not on the curve
    {StaticString("0"),
     StaticString(
         "0x65ddbe1fdeac4074d0f6b7b9e8987b44e0d962fa93a55d6fbae9eaf49e0b82c"),
     StaticString(
         "0x0000000000000000000000000000000001000000000000000000000000000000"),
     StaticString(
         "0x56bf962a6cc889cf1634e299cd8b44ae992790185b920dac52b8e0212b9f"),
     StaticString(
         "0x101736305e0c1be90981cd289c97a5c876b86d70cbe5f7342ff3ebd12cabdd30")},
    {StaticString(
         "0xbfb7fb8c8d241f2fa8ff70fa1799cde5796d1d316f17a556666b52c2bc2e7712"),
     StaticString("0"),
     StaticString(
         "0x0000000000000000000000000000000001000000000000000000000000000000"),
     StaticString(
         "0x56bf962a6cc889cf1634e299cd8b44ae992790185b920dac52b8e0212b9f"),
     StaticString(
         "0x101736305e0c1be90981cd289c97a5c876b86d70cbe5f7342ff3ebd12cabdd30")},
    {StaticString(
         "0xbfb7fb8c8d241f2fa8ff70fa1799cde5796d1d316f17a556666b52c2bc2e7712"),
     StaticString(
         "0x65ddbe1fdeac4074d0f6b7b9e8987b44e0d962fa93a55d6fbae9eaf49e0b82c"),
     StaticString(
         "0x0000000000000000000000000000000001000000000000000000000000000000"),
     StaticString("0"),
     StaticString(
         "0x101736305e0c1be90981cd289c97a5c876b86d70cbe5f7342ff3ebd12cabdd30")},
    {StaticString(
         "0xbfb7fb8c8d241f2fa8ff70fa1799cde5796d1d316f17a556666b52c2bc2e7712"),
     StaticString(
         "0x65ddbe1fdeac4074d0f6b7b9e8987b44e0d962fa93a55d6fbae9eaf49e0b82c"),
     StaticString(
         "0x0000000000000000000000000000000001000000000000000000000000000000"),
     StaticString(
         "0x56bf962a6cc889cf1634e299cd8b44ae992790185b920dac52b8e0212b9f"),
     StaticString("0")},
    {StaticString(
         "0xbfb7fb8c8d241f2fa8ff70fa1799cde5796d1d316f17a556666b52c2bc2e7712"),
     StaticString(
         "0x65ddbe1fdeac4074d0f6b7b9e8987b44e0d962fa93a55d6fbae9eaf49e0b82c"),
     StaticString("0"), StaticString("0"), StaticString("0")},
    // pk not on curve
    {StaticString("0x1"), StaticString("0x2"),
     StaticString(
         "0x0000000000000000000000000000000001000000000000000000000000000000"),
     StaticString(
         "0xc6d1f3abcad6c11412546695d6fc46d6e3237cfe2bc523909789595182ccfb40"),
     StaticString(
         "0x8c2992eb37d7b152d668bf6b35a2fdf6a580fc7eda31b77c2c6d67d6b2d7646f")},
};

// The test_signature3 method below is expressed as a
// template so that we can extend this test for different elliptic
// curves such as secp256k1.
template <class EC, class ScalarField>
void test_signature3(const struct ecdsa_testvec tests[], size_t num,
                     const EC& ec, const ScalarField& Fn,
                     const typename EC::Field::N& order) {
  using Field = typename EC::Field;
  using EvalBackend = EvaluationBackend<Field>;
  using Logic = Logic<Field, EvalBackend>;

  const Field& F = ec.f_;
  const EvalBackend ebk(F);
  const Logic l(&ebk, F);

  using Nat = typename Field::N;
  using Elt = typename Field::Elt;
  using Verc = VerifyCircuit<Logic, Field, EC>;
  using Verw = VerifyWitness3<EC, ScalarField>;

  Verc verc(l, ec, order);

  for (size_t i = 0; i < num; ++i) {
    Elt pk_x = F.of_string(tests[i].pk_x);
    Elt pk_y = F.of_string(tests[i].pk_y);
    Nat e = Nat(tests[i].e);
    Nat r = Nat(tests[i].r);
    Nat s = Nat(tests[i].s);

    Verw vw(Fn, ec);
    vw.compute_witness(pk_x, pk_y, e, r, s);

    typename Verc::Witness vwc;
    vwc.rx = l.konst(vw.rx_);
    vwc.ry = l.konst(vw.ry_);
    vwc.rx_inv = l.konst(vw.rx_inv_);
    vwc.s_inv = l.konst(vw.s_inv_);
    vwc.pk_inv = l.konst(vw.pk_inv_);
    for (size_t j = 0; j < 8; ++j) {
      vwc.pre[j] = l.konst(vw.pre_[j]);
    }
    for (size_t j = 0; j < ec.kBits; j++) {
      vwc.bi[j] = l.konst(vw.bi_[j]);
      if (j < ec.kBits - 1) {
        vwc.int_x[j] = l.konst(vw.int_x_[j]);
        vwc.int_y[j] = l.konst(vw.int_y_[j]);
        vwc.int_z[j] = l.konst(vw.int_z_[j]);
      }
    }

    verc.verify_signature3(l.konst(pk_x), l.konst(pk_y),
                           l.konst(F.to_montgomery(e)), vwc);
  }
}

TEST(ecdsa, verify3_p256) {
  test_signature3<P256, Fp256Scalar>(P256_TEST,
                                     sizeof(P256_TEST) / sizeof(P256_TEST[0]),
                                     p256, p256_scalar, n256_order);
}

// d = 1, digest = 1, nonce = 2: the public key is the generator.
// Multiplication by the group order need not produce the canonical
// projective triple (0, 1, 0), but this is a valid public key.
TEST(ecdsa, generator_public_key) {
  const auto nG = p256.scalar_multf(p256.generator(), n256_order);
  EXPECT_EQ(nG.x, p256_base.zero());
  EXPECT_EQ(nG.z, p256_base.zero());
  EXPECT_NE(nG.y, p256_base.one());
  EXPECT_TRUE(p256.equal(nG, p256.zero()));
  const ecdsa_testvec tests[] = {{
      StaticString("0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296"),
      StaticString("0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5"),
      StaticString("1"),
      StaticString("0x7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978"),
      StaticString("0xbe793d8bc681a7bfc5291c01825a8d61beb832480f84dcdd4ce289dfa1e4df65"),
  }};
  test_signature3<P256, Fp256Scalar>(tests, 1, p256, p256_scalar, n256_order);
}

TEST(ecdsa, p256_failure) {
  using Field = Fp256Base;
  using Nat = Field::N;
  using Elt = Field::Elt;
  using ScalarField = Fp256Scalar;
  using EvalBackend = EvaluationBackend<Field>;
  using Logic = Logic<Field, EvalBackend>;

  const Field& F = p256.f_;
  const EvalBackend ebk(F, false);
  const Logic l(&ebk, F);

  using Verc = VerifyCircuit<Logic, Field, P256>;
  using Verw = VerifyWitness3<P256, ScalarField>;

  Verc verc(l, p256, n256_order);

  for (auto test : P256_FAILS) {
    Elt pk_x = F.of_string(test.pk_x);
    Elt pk_y = F.of_string(test.pk_y);
    Nat e = Nat(test.e);
    Nat r = Nat(test.r);
    Nat s = Nat(test.s);

    Verw vw(p256_scalar, p256);
    vw.compute_witness(pk_x, pk_y, e, r, s);

    typename Verc::Witness vwc;
    vwc.rx = l.konst(vw.rx_);
    vwc.ry = l.konst(vw.ry_);
    vwc.rx_inv = l.konst(vw.rx_inv_);
    vwc.s_inv = l.konst(vw.s_inv_);
    vwc.pk_inv = l.konst(vw.pk_inv_);
    for (size_t j = 0; j < 8; ++j) {
      vwc.pre[j] = l.konst(vw.pre_[j]);
    }
    for (size_t j = 0; j < p256.kBits; j++) {
      vwc.bi[j] = l.konst(vw.bi_[j]);
      if (j < p256.kBits - 1) {
        vwc.int_x[j] = l.konst(vw.int_x_[j]);
        vwc.int_y[j] = l.konst(vw.int_y_[j]);
        vwc.int_z[j] = l.konst(vw.int_z_[j]);
      }
    }

    verc.verify_signature3(l.konst(pk_x), l.konst(pk_y),
                           l.konst(F.to_montgomery(e)), vwc);

    EXPECT_TRUE(ebk.assertion_failed());
  }
}

std::unique_ptr<Circuit<Fp256Base>> make_circuit(size_t numSigs,
                                                 const Fp256Base& f) {
  using CompilerBackend = CompilerBackend<Fp256Base>;
  using LogicCircuit = Logic<Fp256Base, CompilerBackend>;
  using Verc = VerifyCircuit<LogicCircuit, Fp256Base, P256>;
  using EltW = LogicCircuit::EltW;

  QuadCircuit<Fp256Base> Q(p256_base);
  const CompilerBackend cbk(&Q);
  const LogicCircuit lc(&cbk, p256_base);
  Verc verc(lc, p256, n256_order);
  std::vector<Verc::Witness> vwc(numSigs);
  std::vector<EltW> pkx, pky, e;
  for (size_t i = 0; i < numSigs; ++i) {
    pkx.push_back(lc.eltw_input());
    pky.push_back(lc.eltw_input());
    e.push_back(lc.eltw_input());
  }
  Q.private_input();

  for (size_t i = 0; i < numSigs; ++i) {
    vwc[i].input(lc);
  }

  for (size_t i = 0; i < numSigs; ++i) {
    verc.verify_signature3(pkx[i], pky[i], e[i], vwc[i]);
  }
  auto CIRCUIT = Q.mkcircuit(1);
  return CIRCUIT;
}

void fill_input(Dense<Fp256Base>& W, size_t numSigs, const Fp256Base& f,
                bool prover = true) {
  using Nat = Fp256Base::N;
  using Elt = Fp256Base::Elt;
  using Verw = VerifyWitness3<P256, Fp256Scalar>;

  Elt pk_x = p256_base.of_string(P256_TEST[0].pk_x);
  Elt pk_y = p256_base.of_string(P256_TEST[0].pk_y);
  Nat e = Nat(P256_TEST[0].e);
  Nat r = Nat(P256_TEST[0].r);
  Nat s = Nat(P256_TEST[0].s);
  Verw vw(p256_scalar, p256);
  vw.compute_witness(pk_x, pk_y, e, r, s);

  DenseFiller<Fp256Base> filler(W);

  filler.push_back(p256_base.one());
  for (size_t i = 0; i < numSigs; ++i) {
    filler.push_back(pk_x);
    filler.push_back(pk_y);
    filler.push_back(p256_base.to_montgomery(e));
  }
  if (prover) {
    for (size_t i = 0; i < numSigs; ++i) {
      vw.fill_witness(filler);
    }
  }
}

TEST(ECDSA, prover_verifier3_p256) {
  set_log_level(INFO);
  const size_t nc = 1;

  std::unique_ptr<Circuit<Fp256Base>> CIRCUIT = make_circuit(1, p256_base);

  auto W = std::make_unique<Dense<Fp256Base>>(nc, CIRCUIT->ninputs);

  fill_input(*W, 1, p256_base);

  Proof<Fp256Base> pr(CIRCUIT->nl);
  run_prover<Fp256Base>(CIRCUIT.get(), W->clone(), &pr, p256_base);
  log(INFO, "Prover done");
  run_verifier<Fp256Base>(CIRCUIT.get(), std::move(W), pr, p256_base);
  log(INFO, "Verify done");
}

TEST(ECDSA, Size) {
  using CompilerBackend = CompilerBackend<Fp256Base>;
  using LogicCircuit = Logic<Fp256Base, CompilerBackend>;
  using EltW = LogicCircuit::EltW;
  using Verc = VerifyCircuit<LogicCircuit, Fp256Base, P256>;

  QuadCircuit<Fp256Base> Q(p256_base);
  const CompilerBackend cbk(&Q);
  const LogicCircuit lc(&cbk, p256_base);
  Verc verc(lc, p256, n256_order);

  Verc::Witness vwc;
  EltW pkx = lc.eltw_input(), pky = lc.eltw_input(), e = lc.eltw_input();
  vwc.input(lc);

  verc.verify_signature3(pkx, pky, e, vwc);

  auto CIRCUIT = Q.mkcircuit(/*nc=*/1);
  dump_info("ecdsa verify3", Q);
}

// ================ Benchmarks =================================================

constexpr size_t kZKRate = 7;
constexpr size_t kZKQueries = 132;  // 109+ bits of security

void BM_ECDSASumcheckProver(benchmark::State& state) {
  size_t numSigs = state.range(0);
  std::unique_ptr<Circuit<Fp256Base>> CIRCUIT =
      make_circuit(numSigs, p256_base);

  auto W = Dense<Fp256Base>(1, CIRCUIT->ninputs);

  fill_input(W, numSigs, p256_base);

  Proof<Fp256Base> proof(CIRCUIT->nl);
  for (auto s : state) {
    run_prover(CIRCUIT.get(), W.clone(), &proof, p256_base);
  }
}
BENCHMARK(BM_ECDSASumcheckProver)->DenseRange(1, 3);

void BM_ECDSACommit(benchmark::State& state) {
  size_t numSigs = state.range(0);
  std::unique_ptr<Circuit<Fp256Base>> CIRCUIT =
      make_circuit(numSigs, p256_base);
  set_log_level(ERROR);     // Quiet all of the intermediate output.
  auto W = Dense<Fp256Base>(1, CIRCUIT->ninputs);

  using f2_p256 = Fp2<Fp256Base>;
  using Elt2 = f2_p256::Elt;
  using FftExtConvolutionFactory = FFTExtConvolutionFactory<Fp256Base, f2_p256>;
  using RSFactory = ReedSolomonFactory<Fp256Base, FftExtConvolutionFactory>;
  const f2_p256 p256_2(p256_base);

  // Root of unity for the f_p256^2 extension field.
  static constexpr char kRootX[] =
      "112649224146410281873500457609690258373018840430489408729223714171582664"
      "680802";
  static constexpr char kRootY[] =
      "840879943585409076957404614278186605601821689971823787493130182544504602"
      "12908";

  fill_input(W, numSigs, p256_base);
  const Elt2 omega = p256_2.of_string(kRootX, kRootY);
  const FftExtConvolutionFactory fft_b(p256_base, p256_2, omega, 1ull << 31);
  const RSFactory rsf(fft_b, p256_base);

  Transcript tp((uint8_t*)"test", 4);
  SecureRandomEngine rng;

  ZkProof<Fp256Base> zkpr(*CIRCUIT, kZKRate, kZKQueries);
  ZkProver<Fp256Base, RSFactory> prover(*CIRCUIT, p256_base, rsf);
  for (auto s : state) {
    prover.commit(zkpr, W, tp, rng);
  }
}
BENCHMARK(BM_ECDSACommit)->DenseRange(1, 3);

void BM_ECDSAZKProver(benchmark::State& state) {
  size_t numSigs = state.range(0);
  std::unique_ptr<Circuit<Fp256Base>> CIRCUIT =
      make_circuit(numSigs, p256_base);

  set_log_level(ERROR);
  auto W = Dense<Fp256Base>(1, CIRCUIT->ninputs);

  using f2_p256 = Fp2<Fp256Base>;
  using Elt2 = f2_p256::Elt;
  using FftExtConvolutionFactory = FFTExtConvolutionFactory<Fp256Base, f2_p256>;
  using RSFactory = ReedSolomonFactory<Fp256Base, FftExtConvolutionFactory>;
  const f2_p256 p256_2(p256_base);

  // Root of unity for the f_p256^2 extension field.
  static constexpr char kRootX[] =
      "112649224146410281873500457609690258373018840430489408729223714171582664"
      "680802";
  static constexpr char kRootY[] =
      "840879943585409076957404614278186605601821689971823787493130182544504602"
      "12908";

  fill_input(W, numSigs, p256_base);
  const Elt2 omega = p256_2.of_string(kRootX, kRootY);
  const FftExtConvolutionFactory fft_b(p256_base, p256_2, omega, 1ull << 31);
  const RSFactory rsf(fft_b, p256_base);

  Transcript tp((uint8_t*)"test", 4);
  SecureRandomEngine rng;

  ZkProof<Fp256Base> zkpr(*CIRCUIT, kZKRate, kZKQueries);
  ZkProver<Fp256Base, RSFactory> prover(*CIRCUIT, p256_base, rsf);
  for (auto s : state) {
    prover.commit(zkpr, W, tp, rng);
    prover.prove(zkpr, W, tp);
  }
}
BENCHMARK(BM_ECDSAZKProver)->DenseRange(1, 3);

void BM_ECDSAZKVerifier(benchmark::State& state) {
  size_t numSigs = state.range(0);
  std::unique_ptr<Circuit<Fp256Base>> CIRCUIT =
      make_circuit(numSigs, p256_base);
  set_log_level(ERROR);

  auto W = Dense<Fp256Base>(1, CIRCUIT->ninputs);

  using f2_p256 = Fp2<Fp256Base>;
  using Elt2 = f2_p256::Elt;
  using FftExtConvolutionFactory = FFTExtConvolutionFactory<Fp256Base, f2_p256>;
  using RSFactory = ReedSolomonFactory<Fp256Base, FftExtConvolutionFactory>;
  const f2_p256 p256_2(p256_base);

  // Root of unity for the f_p256^2 extension field.
  static constexpr char kRootX[] =
      "112649224146410281873500457609690258373018840430489408729223714171582664"
      "680802";
  static constexpr char kRootY[] =
      "840879943585409076957404614278186605601821689971823787493130182544504602"
      "12908";

  fill_input(W, numSigs, p256_base);
  const Elt2 omega = p256_2.of_string(kRootX, kRootY);
  const FftExtConvolutionFactory fft_b(p256_base, p256_2, omega, 1ull << 31);
  const RSFactory rsf(fft_b, p256_base);

  Transcript tp((uint8_t *)"verify_test", 11);
  SecureRandomEngine rng;

  ZkProof<Fp256Base> zkpr(*CIRCUIT, kZKRate, kZKQueries);
  ZkProver<Fp256Base, RSFactory> prover(*CIRCUIT, p256_base, rsf);
  prover.commit(zkpr, W, tp, rng);
  prover.prove(zkpr, W, tp);

  ZkVerifier<Fp256Base, RSFactory> verifier(*CIRCUIT, rsf, kZKRate, kZKQueries,
                                            p256_base);
  auto pub = Dense<Fp256Base>(1, CIRCUIT->npub_in);
  fill_input(pub, numSigs, p256_base, false);
  for (auto s : state) {
    Transcript tv((uint8_t *)"verify_test", 11);
    verifier.recv_commitment(zkpr, tv);
    verifier.verify(zkpr, pub, tv);
  }
}
BENCHMARK(BM_ECDSAZKVerifier)->DenseRange(1, 3);

}  // namespace
}  // namespace proofs
