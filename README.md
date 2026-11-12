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

The [Lean development](formal/README.md) proves security bounds for the
mathematical protocol models. V1 retains its 116-bit T-security result.
The current SHA-256 strand model of V2 has a checked Fiat–Shamir extraction
bound for original raw-query budgets `0 <= Q < 2^127`. At rate 1/7, put
$q=2^{128}$ and $c=1.0000012312149082441647508747\ldots$ (defined exactly
in the formal README). The soundness failure probability satisfies

$$
P_{\mathrm{fail}}(Q)\le \frac{cQ}{q}
+\left(1-\frac{c(q-1)}{2q}\right)
 \left[1-\left(1-\frac{2}{q-1}\right)^Q\right]
+\frac{\binom Q2+r+15}{q^2}.
$$

Here `r` counts rounds, one per `begin_squeeze()` call. The original
distinct-query bound `Q` holds for every adversarial coin and total byte oracle.
For every `Q < 2^127`,
the full failure probability is **strictly less than 0.97**, with the cap rounded
up to two decimal places. A convenient approximation for the mdoc circuit,
valid for every $Q\ge0$, is

$$
P_{\mathrm{fail}}(Q)\le Q\,2^{-127}+Q^2\,2^{-257}+2^{-246}.
$$

The largest supported mdoc circuit (four attributes) has 500 rounds, so
`r+15 = 515 < 2^10`. The [exact theorem and assumptions](formal/lfzk-v2/README.md#current-mac-free-protocol)
cover adaptive public requests, both fields, packing, the cross-field adapter,
joint Polygero and its shared indexed Merkle commitment.

The [formal audit](formal/AUDIT.md) describes source correspondence and the
trusted field/circuit and ideal-oracle boundaries. Rust correspondence is
reviewed and tested. The [complete numbered-strand statistical zero-knowledge
theorem](formal/lfzk-v2/README.md#current-numbered-strand-zero-knowledge) covers
shared-oracle public setup and complete observer views, with ideal-model error
at most `(Qpre+Qpost)/2^256`.

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
