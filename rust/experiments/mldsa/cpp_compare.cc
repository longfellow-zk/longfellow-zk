// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
// Reuse the committed circuit and witness setup. The include-path overlay
// changes ONLY period/round-0 slicing. The full-input subfield boundary is
// applied to benchmark circuit metadata below, before serialization/proving.
#include "circuits/tests/pq/ml_dsa/ml_dsa_circuit_test.cc"

#include <chrono>
#include <fstream>
#include <map>
#include <set>
#include <sys/resource.h>
#include <zstd.h>

#include "proto/circuit_reader.h"
#include "proto/circuit_writer.h"
#include "sumcheck/circuit_id.h"

namespace proofs {
namespace {
using Clock = std::chrono::steady_clock;
double ms(Clock::time_point start) {
  return std::chrono::duration<double, std::milli>(Clock::now() - start).count();
}
void save(const std::string& path, const std::vector<uint8_t>& bytes) {
  std::ofstream out(path, std::ios::binary);
  out.write(reinterpret_cast<const char*>(bytes.data()), bytes.size());
  check(out.good(), "cannot save benchmark artifact");
}
std::vector<uint8_t> load(const std::string& path) {
  std::ifstream in(path, std::ios::binary | std::ios::ate);
  check(in.good(), "cannot open circuit");
  size_t n = static_cast<size_t>(in.tellg());
  std::vector<uint8_t> bytes(n);
  in.seekg(0); in.read(reinterpret_cast<char*>(bytes.data()), n);
  check(in.good(), "cannot read circuit"); return bytes;
}
size_t compress_save(const std::string& path, const std::vector<uint8_t>& bytes, int level) {
  std::vector<uint8_t> out(ZSTD_compressBound(bytes.size()));
  size_t n = ZSTD_compress(out.data(), out.size(), bytes.data(), bytes.size(), level);
  check(!ZSTD_isError(n), "zstd failed"); out.resize(n); save(path, out); return n;
}
void geometry(const Circuit<Field6>& c, const Field6& f) {
  size_t wires=c.nv, max_width=c.nv, local_deltas=0;
  std::map<std::array<uint8_t,24>,uint32_t> constants;
  std::set<std::array<int64_t,4>> global;
  size_t index=0;
  for (const auto& l:c.l) {
    wires += l.nw; max_width=std::max(max_width,static_cast<size_t>(l.nw));
    std::set<std::array<int64_t,4>> deltas;
    int64_t pg=0, ph0=0, ph1=0;
    for (const auto& ec:*l.quad) {
      std::array<uint8_t,24> bytes; f.to_bytes_field(bytes.data(),ec.v);
      auto [it,inserted]=constants.emplace(bytes,constants.size());
      int64_t g=static_cast<uint64_t>(ec.g), h0=static_cast<uint64_t>(ec.h[0]), h1=static_cast<uint64_t>(ec.h[1]);
      std::array<int64_t,4> d{g-pg,h0-ph0,h1-ph1,it->second};
      deltas.insert(d); global.insert(d); pg=g; ph0=h0; ph1=h1;
    }
    local_deltas += deltas.size();
    std::printf("CPP_LAYER layer=%zu wires=%zu terms=%zu logw=%zu deltas=%zu\n",index++,static_cast<size_t>(l.nw),l.nterms(),l.logw,deltas.size());
  }
  std::printf("CPP_GEOMETRY inputs=%zu public=%zu outputs=%zu wires=%zu noninput_wires=%zu terms=%zu layers=%zu max_width=%zu deltas=%zu global_deltas=%zu constants=%zu subfield_boundary=%zu field_bytes=%zu subfield_bytes=%zu period=4 first=1 bits=0\n",
              c.ninputs,c.npub_in,static_cast<size_t>(c.nv),wires,wires-c.ninputs,c.nterms(),c.nl,max_width,local_deltas,global.size(),constants.size(),c.subfield_boundary,Field6::kBytes,Field6::kSubFieldBytes);
}

template<class Params>
void run(const std::string& mode, const std::string& path, size_t repeats) {
  using Traits=MLDsaCircuitTestTraits<Params>;
  const Field6 f(ml_dsa::Fq(),kBeta);
  check(sha3_slice_at(0) && sha3_slice_at(3) && !sha3_slice_at(5),"wrong slicing overlay");
  if (mode=="compile") {
    auto start=Clock::now(); auto c=make_ml_dsa_circuit<Params>(1);
    c->subfield_boundary=c->ninputs;
    circuit_id(c->id,*c,f);
    double compile_ms=ms(start);
    geometry(*c,f);
    start=Clock::now(); std::vector<uint8_t> bytes;
    CircuitWriter<Field6>(f,NONE).to_bytes(*c,bytes); double encode_ms=ms(start);
    save(path,bytes);
    size_t z16=compress_save(path+".z16",bytes,16);
    size_t z22=compress_save(path+".z22",bytes,22);
    std::printf("CPP_CIRCUIT raw=%zu z16=%zu z22=%zu compile_ms=%.3f encode_ms=%.3f zstd=%s\n",bytes.size(),z16,z22,compile_ms,encode_ms,ZSTD_versionString());
    return;
  }
  check(mode=="prove","unknown phase");
  auto start=Clock::now(); auto bytes=load(path);
  ReadBuffer buf(bytes); auto c=CircuitReader<Field6>(f,NONE).from_bytes(buf,true);
  check(c!=nullptr && buf.remaining()==0,"circuit decode/ID failed");
  double load_ms=ms(start);
  bytes.clear(); bytes.shrink_to_fit();
  check(c->subfield_boundary==c->ninputs,"wrong subfield boundary");
  Dense<Field6> witness(1,c->ninputs), pub(1,c->ninputs);
  {
    auto wg=std::make_unique<typename Traits::WitnessGen>();
    auto examples=Traits::GetExamples(); const auto& ex=examples[0];
    wg->compute_witness(ex.pkey,ex.sig,ex.msg,ex.ctx);
    DenseFiller<Field6> fill(witness); fill.push_back(f.one()); wg->fill_witness(fill,f);
    for(size_t i=0;i<64;++i) fill.push_back(wg->mu_[i],8,f);
    check(fill.size()==c->ninputs,"witness length mismatch");
    DenseFiller<Field6> pf(pub); pf.push_back(f.one()); wg->fill_pk(pf,f);
    check(pf.size()==c->npub_in,"public input length mismatch");
  }
  for(const auto& x:witness.v_) check(f.in_subfield(x),"input outside base subfield");
  ReedSolomonExtensionFactory rsextf(ml_dsa::Fq());
  for(size_t repeat=0;repeat<repeats;++repeat) {
    ZkProof<Field6> proof(*c,4,128);
    ZkProver<Field6,ReedSolomonExtensionFactory> prover(*c,f,rsextf);
    SecureRandomEngine rng; Transcript tp(reinterpret_cast<const uint8_t*>("test"),4);
    start=Clock::now(); prover.commit(proof,witness,tp,rng); double commit_ms=ms(start);
    start=Clock::now(); check(prover.prove(proof,witness,tp),"prover failed"); double prove_ms=ms(start);
    std::vector<uint8_t> encoded; proof.write(encoded,f); save(path+".proof",encoded);
    ZkProof<Field6> decoded(*c,4,128); ReadBuffer pb(encoded);
    check(decoded.read(pb,f) && pb.remaining()==0,"proof round trip failed");
    ZkVerifier<Field6,ReedSolomonExtensionFactory> verifier(*c,rsextf,4,128,f);
    Transcript tv(reinterpret_cast<const uint8_t*>("test"),4);
    start=Clock::now(); verifier.recv_commitment(decoded,tv);
    check(verifier.verify(decoded,pub,tv),"verification failed"); double verify_ms=ms(start);
    rusage usage{}; getrusage(RUSAGE_SELF,&usage);
    std::printf("CPP_PROOF repeat=%zu load_ms=%.3f commit_ms=%.3f prove_ms=%.3f total_prover_ms=%.3f verify_ms=%.3f proof=%zu witnesses=%zu constraints=%zu block_enc=%zu block=%zu rows=%zu peak_rss_kib=%ld verified=1\n",
                repeat,load_ms,commit_ms,prove_ms,commit_ms+prove_ms,verify_ms,encoded.size(),proof.param.nw,proof.param.nq,proof.param.block_enc,proof.param.block,proof.param.nrow,usage.ru_maxrss);
    std::fflush(stdout);
  }
}
} // namespace
} // namespace proofs
int main(int argc,char** argv) {
  proofs::set_log_level(proofs::ERROR);
  if(argc!=5) { std::fprintf(stderr,"usage: cpp_compare compile|prove 44|65 circuit-path repeats\n"); return 2; }
  if(std::string(argv[2])=="44") proofs::run<proofs::ml_dsa::MLDsa44Params>(argv[1],argv[3],std::stoull(argv[4]));
  else if(std::string(argv[2])=="65") proofs::run<proofs::ml_dsa::MLDsa65Params>(argv[1],argv[3],std::stoull(argv[4]));
  else return 2;
}
