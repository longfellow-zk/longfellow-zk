# Formal Verification of Zero-Knowledge Circuits

This directory contains the Lean 4 formalizations and mathematical proofs of
soundness and completeness for the Elliptic Curve (EC) and ECDSA Zero-Knowledge
(ZK) circuits.

It also contains two further developments:

-   **An artifact certificate** for the deployed circuits: that the bytes shipped
    in a circuit artifact describe a circuit whose constraints force a published
    specification to hold.
-   **The proof system**: that Ligero, sumcheck, the BCS compiler and Merkle
    commitments compose into a sound, zero-knowledge argument for a model of
    Longfellow's v7 protocol.

Each part has its own documentation; this file is the index.

## What is proved

### The circuits

`circuits/ECDSA/` proves the ECDSA circuit sound and complete against an ECDSA
signature verification specification, over curve arithmetic formalized from
first principles.

`circuits/quadcert/` goes one step further and starts from the **artifact**: for
ECDSA2 and for one-block SHA-256, a single theorem takes the committed payload
and an accepting witness, and concludes both that those bytes hash to the root
the verifier pins and that the specification holds of the values on the wires.
See [`circuits/README.md`](circuits/README.md) for the four-step argument, what
remains trusted, and how to regenerate and build it.

### The proof system

| directory | result | |
|---|---|---|
| `ligero/` | Ligero IOP extraction and false-statement soundness, with exact v7/v8 component certificates for V1, V2 and V3 | [README](ligero/README.md) |
| `polygero/` | witness extraction for the recursive public-coin Polygero protocol; false-statement soundness as a corollary | [README](polygero/README.md) |
| `bcs/` | the BCS compiler (Merkle-committed oracles plus Fiat–Shamir), sound against a prover that may re-commit and grind | [README](bcs/README.md) |
| `merkle/` | the Merkle-heap commitment | [README](merkle/README.md) |
| `sumcheck/` | the sumcheck protocol | |
| `lfzk/` | conditional knowledge soundness and zero knowledge for a model of the v7 protocol, which runs two circuits on one Fiat–Shamir transcript | [README](lfzk/README.md) |

## Directory Structure

-   `circuits/ECDSA/`: Contains the core elliptic curve arithmetic (`EC.lean`,
    `Curves.lean`, `Nat.lean`), the ECDSA signature verification spec
    (`EcdsaSpec.lean`), circuit constraints (`EcdsaCircuit.lean`), algebraic
    bridging lemmas (`Ecdsa.lean`), completeness (`EcdsaComplete.lean`), and
    soundness (`EcdsaSound.lean`) formalizations and proofs.
    The v2 development states the same result against the deployed Rust
    circuit's interface
    (`EcdsaV2.lean`), with its lookup tables (`Lagrange9.lean`, `BitTable.lean`,
    `RangeCert.lean`), its 256-bit comparator (`BitLt.lean`, `CmpBridge.lean`),
    and the curve facts it needs (`Pratt.lean`, `*NoRoot.lean`, `PowMod.lean`).
-   `circuits/tests/ec/`: Contains the projective public key validation circuit
    constraint logic (`PkCircuit.lean`) and its symbolic polynomial evaluation
    model (`PkCircuitPoly.lean`).
-   `circuits/quadcert/`: The artifact certificate -- bytes, to circuit, to
    assertions, to specification. `Core/` is the decoder and the quad semantics,
    `Bridge/` the per-circuit meaning proofs, and `Gen/` is generated and
    gitignored.
-   `circuits/SHA/`, `circuits/GF128/`, `circuits/mdoc/`: The SHA-256
    specification, GF(2¹²⁸) as the deployed code represents it, and the mdoc
    credential circuits.
-   `ligero/`, `polygero/`, `sumcheck/`, `bcs/`, `merkle/`, `lfzk/`: The proof
    system, as above.
-   `tools/`: The serial builder `leanseq`, and the generators that produce
    `circuits/quadcert/Gen/`.
-   `lakefile.toml` / `lake-manifest.json` / `lean-toolchain`: Standard Lean
    package configuration files.

## How to Compile & Verify

### 1. Using Blaze (Bazel)

To compile and mathematically verify all formalizations and proofs in the
package using Google's Blaze build system:

```bash
# Compile all targets
blaze build //privacy/proofs/zk/formal/...

# Run all tests
blaze test //privacy/proofs/zk/formal:ecdsa_lean_test //privacy/proofs/zk/formal:pk_lean_test
```

This will invoke the Lean compiler hermetically, resolving and checking all
proofs.

### 2. Using Lake (Lean's Package Manager)

To compile the project locally using Lake:

```bash
# Navigate to the formal/ package directory
cd privacy/proofs/zk/formal/

# Build the targets
lake build
```

A bare `lake build` builds the default targets: `ECDSA`, `pk_circuit` and the
proof-system libraries. The artifact certificate is not a default target. It is
generated, large, and memory-hungry enough that building it with plain `lake`
from cold will exhaust a typical machine, so it has its own instructions in
[`circuits/README.md`](circuits/README.md#building).
