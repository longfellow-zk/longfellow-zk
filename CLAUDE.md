# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

Longfellow ZK is a C++17 library implementing zero-knowledge proof protocols for identity credentials (ISO mDOC, JWT, W3C Verifiable Credentials). The proof system combines the **Ligero** MPC-in-the-head commitment scheme with a **sumcheck**-based verifiable computation protocol to prove that a circuit `C(x, w) = 0` without revealing the witness `w`.

## Build Commands

**Dependencies (macOS):**
```
brew install googletest google-benchmark zstd
```

**CMake initialization:**
```
CXX=clang++ cmake -D CMAKE_BUILD_TYPE=Release -S lib -B clang-build-release --install-prefix ${PWD}/install
```

**Build and test:**
```
cd clang-build-release && make -j 16 && ctest -j 16
```

**Run a single test binary:**
```
./clang-build-release/circuits/mdoc/mdoc_zk_test
./clang-build-release/algebra/fft_test
```

**Run benchmarks:**
```
./clang-build-release/algebra/fft_test --benchmark_filter='BM_*'
./clang-build-release/circuits/sha/flatsha256_circuit_test --benchmark_filter=BM_ShaZK_fp2_128
```

**Build install target (needed for verifier service):**
```
cd clang-build-release && make install
```

## Architecture

All source lives under `lib/`. The build root is `lib/CMakeLists.txt`. Include paths are rooted at `lib/`, so headers are included as e.g. `#include "algebra/fp.h"`.

### Core ZK Layers (bottom → top)

| Layer | Path | Role |
|-------|------|------|
| **Algebra** | `lib/algebra/` | Finite field arithmetic: `Fp<N>` (Montgomery form) for prime fields, `Fp2` for extension fields, FFT, Reed-Solomon, polynomial ops |
| **GF2k** | `lib/gf2k/` | GF(2^128) arithmetic for the Ligero signature component |
| **Sumcheck** | `lib/sumcheck/` | Sumcheck-based IP prover/verifier; `Circuit<Field>` and `Quad<Field>` gate representation |
| **Ligero** | `lib/ligero/` | Ligero commitment/proof system; operates on a 2D tableau of Reed-Solomon-encoded witness rows |
| **ZK** | `lib/zk/` | Top-level ZK prover/verifier (`ZkProver`, `ZkVerifier`): commits witness+pad via Ligero, runs encrypted sumcheck, proves transcript validity |
| **Merkle** | `lib/merkle/` | Merkle tree commitments used by Ligero |
| **EC** | `lib/ec/` | Elliptic curve ops for P-256 and secp256k1 (used in ECDSA signature verification circuits) |

### Circuit Layer (`lib/circuits/`)

- **compiler/** — `QuadCircuit<Field>`: DSL for defining arithmetic circuits; `mkcircuit()` compiles to optimized `Circuit<Field>` with constant propagation and CSE
- **ecdsa/** — Circuit for ECDSA signature verification over P-256
- **sha/** — SHA-256 circuit
- **mac/** — Message Authentication Code circuit (splits MAC key between prover and verifier for ZK)
- **cbor_parser/** — CBOR parsing circuit
- **logic/** — Bit-level logic gates
- **mdoc/** — Top-level mDOC credential circuit; `mdoc_zk.cc` contains the C-API entry points `run_mdoc_prover`, `run_mdoc_verifier`, `generate_circuit`

### Supporting Modules

- `lib/proto/` — Serialization of `Circuit<Field>` to/from bytes (used for caching precomputed circuits)
- `lib/cbor/` — Host-side CBOR decoder for parsing mDOC inputs
- `lib/random/` — Transcript (Fiat-Shamir), secure RNG
- `lib/arrays/` — `Dense<Field>` witness array abstraction
- `lib/util/` — Logging, panic, crypto utilities

### Versioning and Circuit Specs (`ZkSpecStruct`)

`lib/circuits/mdoc/zk_spec.cc` contains the hardcoded `kZkSpecs[]` array. Each entry records:
- `system` — e.g. `"longfellow-libzk-v1"`
- `circuit_hash` — SHA-256 of the compressed circuit bytes (hex string)
- `num_attributes`, `version`, `block_enc_hash`, `block_enc_sig`

Precomputed compressed circuit files are stored in `lib/circuits/mdoc/circuits/` (filenames = circuit hashes). When circuits change, new hashes must be computed and added to `kZkSpecs`.

### Reference Verifier Service (`reference/verifier-service/`)

A Go HTTP server that exposes the C++ ZK verifier via CGo. Build steps:
1. Build and install the C++ library (see above, with `--install-prefix` pointing to the service's install dir)
2. `cd reference/verifier-service/server && go build`
3. Run: `./server -circuit_dir ../../../lib/circuits/mdoc/circuits`

Endpoints: `POST /zkverify` (verify a proof), `GET /specs` (list supported circuit specs).

Docker build: `docker build -t zk -f reference/verifier-service/Dockerfile ../..`

## Key Design Patterns

- **Template-parameterized by Field**: Nearly all code is templated on `Field` (e.g. `Fp256`, `Fp2`). The mDOC prover runs two parallel ZK instances: one over `Fp256` (for the hash circuit) and one over `Fp2/GF(2^128)` (for the ECDSA signature circuit).
- **C API for external callers**: `mdoc_zk.h` defines a C-compatible interface for use from Go (CGo), Android, and other languages.
- **Tests are collocated**: Test files (`*_test.cc`) live alongside the source they test in the same directory.
- **Experimental code**: `lib/circuits/tests/` contains non-production experiments (anoncred, jwt, base64, sha3, ripemd). `lib/circuits/tests/mdoc/` is experimental mdoc work.
