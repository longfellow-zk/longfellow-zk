# Recursive Polygero

This development proves witness extraction for the recursive public-coin
Polygero protocol. False-statement soundness is a corollary of extraction.

For a recursive protocol with certified local errors `ε₀, …, εₕ`, the main
bound is

```
Pr[wireVerify accepts ∧ wireExtract returns none]
  ≤ 1 − ∏ᵢ (1 − εᵢ) ≤ ∑ᵢ εᵢ.
```

The probability is over independent, uniformly sampled verifier coins and
query sets, for any fixed root oracle and any allowed adaptive prover
strategy. Each child oracle is chosen after the parent challenge and before
the parent query; later messages may depend on the preceding verifier
messages. The extractor reads the full committed oracles and the execution
transcript. Every witness it returns satisfies the root constraint system.

The main results, in `RecursivePolygero.Protocol.ProfileProof`, are:

- `wireExtract_valid`: every returned witness satisfies the statement.
- `wire_extraction_failure`: the joint acceptance and extraction-failure
  event satisfies the product bound above, for the transmitted verifier.
- `soundness_of_extraction`: if no satisfying witness exists, acceptance
  probability satisfies the same product bound. Its proof uses the two
  extraction theorems directly.
- `randomTargetProbability_le`: the recursive induction bounds extraction
  failure together with hitting a target family chosen using earlier
  randomness. If every fixed witness has target frequency at most `ρ`, the
  bound is `ε + (1 − ε)ρ`.
- `error_eq_product` and `error_le_sum`: the recursive error equals the
  product bound and is at most the sum of the local errors.

Each invocation has a `ProfileCertificate` containing its encoding geometry,
an exact integer counting cutoff, and a field-size inequality. Write
`k = r + w`, `q = |F|`, and `t` for the number of queried columns. The local
error is

```
ε = θ + (1 − θ)(μ + 1/q)
μ = choose(n, k + 2s + 1) / q^(s + 1)
θ = max(choose(max(k + 2s + 1, 2k + s) − 1, t) / choose(n, t),
        (u − 1)/(2(q − 1)) + qη/(2u))
η = choose(k + 2s − 1, t) / choose(n, t).
```

Here `u` is the least positive integer satisfying
`q(q − 1)η ≤ u(u + 1)`. The certificate checks `k ≥ 1`, `t ≥ 1`,
`max(k + 2s + 1, 2k + s) ≤ n`, `k + 2s − 1 < n`, and `μ + 1/q < 1`;
the instance supplies the distinct evaluation points and `t ≤ n`.

The wire verifier supports optional root masks and expands omitted child
masks to zero. Its extraction bound quantifies over arbitrary transmitted
oracles. The local verifier uses polynomial batching challenges, checks
the linear response's global sum, and checks products in each opened column.
Recursive coefficient substitution connects child witnesses to the parent
responses through `Child.verify_iff`.

The existing Ligero Reed–Solomon domains,
tableau constraints, layouts, arithmetic evaluation, and query counting
are reused directly. `Algebra/Code.lean` supplies the small punctured-domain
adapter needed by the imported decoder. The public witness-valued API is in
`Theorems/Extraction.lean` and `Theorems/WireExtraction.lean`; its soundness
corollaries are in `Theorems/Soundness.lean`.

Sources live directly under `formal/polygero/`; `formal/polygero.lean`
is the public entry point. Imports use `polygero.*`, while declarations
retain the `RecursivePolygero` namespace. The development has six layers,
with separate import interfaces:

| Interface | Contents |
|---|---|
| `polygero.Algebra` | Protocol-independent polynomial geometry, Reed–Solomon adapters, and exact finite counting. |
| `polygero.Protocol` | One-layer instance, tableau, verifier, and physical wire representation. |
| `polygero.Local` | Candidate witnesses, concrete decoder, and response-uniform local recovery bounds. |
| `polygero.Reduction` | Child encoding and coefficient substitution, including `Child.verify_iff`. |
| `polygero.Recursion` | Adaptive execution, transcript extraction, correctness, and random-target composition. |
| `polygero` | Public extraction theorems and their soundness corollaries. |

Algebra does not import any higher layer. Protocol definitions do not import
local analysis or recursion. Local analysis and coefficient reduction depend
on algebra and protocol definitions independently; neither imports recursion.
The recursive probability proof combines the local response envelope with
the child link. Physical wire expansion is in `Protocol/Wire.lean`; recursive
wire strategies and their verifier are in `Recursion/Wire.lean`.

Within recursion, `Extractor.lean` defines the transcript-assisted extractor,
`Correctness.lean` proves witness validity, and `Probability.lean` proves the
random-target induction. `Error.lean` defines the canonical recursive error
and proves its range, product formula, and additive bound independently of
the probability proof. Declaration namespaces and public theorem names are
preserved from the initial import.

From `formal/`, run:

```sh
lake build RecursivePolygero
```

`polygero.APITest` checks the public API, the concrete proof
dependencies, and the foundational axioms of every imported theorem. It is
also part of the default `lake build`.
