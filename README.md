# Longfellow ZK


[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE) [![eprint](https://img.shields.io/badge/eprint-2024%2F2010-blue)](https://eprint.iacr.org/2024/2010)
[![IETF Draft](https://img.shields.io/badge/IETF%20Draft-draft--google--cfrg--libzk-lightgrey)](https://datatracker.ietf.org/doc/draft-google-cfrg-libzk/)
## Overview

The Longfellow library enables the construction of  zero-knowledge protocols concerning legacy identity verification standards such as the ISO MDOC standard, the JWT standard, and W3 Verifiable Credentials.  This implementation is described in:

* [Anonymous credentials from ECDSA](https://eprint.iacr.org/2024/2010)
* [libzk: A C++ Library for Zero-Knowledge Proofs](https://datatracker.ietf.org/doc/draft-google-cfrg-libzk/)
* [Project documentation](https://longfellow-zk.github.io/longfellow-zk/)

It is named after the bridge outside the Google Cambridge office.

# Security

Earlier versions of this project have completed several independent security reviews by panels of academic and industry experts in the field. Their reports are available in the [Project documentation/Reviews](https://longfellow-zk.github.io/longfellow-zk/docs/reviews/) page; those reviews do not cover all subsequent Rust V2 changes.

The [Lean development](formal/README.md) proves conditional security bounds
for mathematical models of both protocol versions. V1 retains its 116-bit
T-security result. The current MAC-free V2 protocol has a Fiat–Shamir
extraction bound with leading term `2Q/2^128`, plus explicit terms over
`2^256`, for every transcript-query budget `Q >= 0`. The
[exact theorem and oracle assumptions](formal/lfzk-v2/README.md#current-mac-free-protocol)
cover the rate-1/7 profile, adaptive public requests, both fields, packing,
the cross-field adapter and one shared Merkle commitment. The
[formal audit](formal/AUDIT.md) states the implementation boundary and
verification commands. These results do not constitute source-level
verification of Rust or C++. The complete V2 mdoc model also has a
[statistical zero-knowledge theorem](formal/lfzk-v2/README.md#complete-mdoc-zero-knowledge)
with an explicit witness-free simulator and query-dependent hiding error.

# Specifications
This repository contains [the working files](https://github.com/longfellow-zk/longfellow-zk/tree/main/docs/specs) for a specification of Longfellow and its components.
If you are interested in contributing, please create an Issue or a Pull Request. Our discussions occur under Issues.

# Testing via devcontainer
You can test our library by using the associated devcontainer to create its environment. Select `Code` → `Codespaces` → `Create codespace on main` to get started. This creates a container on GitHub that includes the dependencies and provides a browser-based VS Code interface. You can compile and run our benchmarks there, though the VM may be slower than the reported measurements.

# Instructions to build

## Requirements

This package depends on cmake, openssl, zstd, clang, googletest and
googlebenchmark.

### Ubuntu, debian

```
$ sudo apt install -y build-essential clang cmake libssl-dev libzstd-dev libgtest-dev libbenchmark-dev zlib1g-dev
```

### Fedora, redhat

```
$ yum install -y clang libzstd-devel openssl-devel git cmake google-benchmark-devel gtest-devel
```

Newer versions of fedora seem to require `libpfm-devel`:
```
$ yum install -y clang libzstd-devel openssl-devel git cmake google-benchmark-devel gtest-devel libpfm-devel
```


### MacOS
Ensure that Xcode command line tools such as `clang` and `cmake` are installed.

```
$ brew install googletest google-benchmark zstd
```

## Building manually

First run the cmake initialization step

```
$ CXX=clang++ cmake -D CMAKE_BUILD_TYPE=Release -S lib -B clang-build-release --install-prefix ${PWD}/install
```

Next:

```
$ cd clang-build-release && make -j 16 && ctest -j 16
```

# Running benchmarks

We have defined several unit, sumcheck, and zk benchmarks. Here are some of
them:

```
$ ./algebra/fft_test --benchmark_filter='BM_*'
$ ./circuits/sha/flatsha256_circuit_test --benchmark_filter=BM_ShaZK_fp2_128
```
