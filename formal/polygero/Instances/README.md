# Checked Polygero instances

These Lean modules contain parameter choices, exact rational certificates,
and applications of the reusable proofs in `Local/` and `Recursion/`.
Declaration namespaces start with `RecursivePolygero.Instances`.
`Benchmarks/` now contains only independent Python calculations; `Tests/`
contains dependency and axiom audits. The protected API in `StableAPI.lean`
is unchanged.

Use `import polygero.Recursion.FiatShamir` for the generic FS development,
or `import polygero.Instances.FSJointChildCompiled81` for the current
81/80-opening end-to-end theorem. Neither `Local/` nor `Recursion/` imports
`Instances/`; `Tests/FSGenericTest.lean` checks this transitively for the
reusable FS interface.

The former `Benchmarks.FSRemainingBudget81` module is now
`Recursion.FSRemainingBudget`, with declarations under
`RecursivePolygero.FiatShamir.MerkleFS.RemainingBudget`. The shared
`extraction_failure_bound_of_root_bound` and `extraction_failure_bound_of_blocks`
are in `Recursion.FSRootSoundness`; `root_oracle_sound_of_blocks` is in
`Recursion.FSRootComposition`. Historical writeup references to these generic
proofs with an `81` suffix refer to these parameter-independent replacements.

## Capacity-C child charging

For a committed child oracle V, let x(V) be the total rigid-system excess
above the query baseline theta, and let m(V) be the number of high,
nonrigid systems. The generic child theorem takes a rational C >= 0 and
requires:

- x(V) + m(V) <= C for every V;
- the existing Hahn list bound is smaller than the field size q;
- theta + (1-theta)/q <= C/q.

It proves local-domain `OracleSound` with both ABS parameters equal to

```
kappa = (1-theta)*mu + C/q.
```

Here mu is the local rank-error bound. The last inequality also implies
that the fresh local error and theta are at most kappa; the generic proof
derives those facts rather than requesting separate numerical premises.
The cached ROM, arbitrary query order, and verifier completion are unchanged.
There is no fixed opening count, field size, or geometry in this interface.

`FSJointChild81.capacity_le_two` discharges the capacity premise at C = 2
for n = 8192, r+w = 512, s = 64, cutoff 2714, and the checked child
certificate. The 81/80 instance additionally checks q = 2^128, parent
openings 81, child openings 80, and the baseline inequality. A different
parameter choice needs its own capacity and numerical certificates, while
reusing the same ROM and Merkle proofs.

## End-to-end bound

`FiatShamir.MerkleFS.extraction_failure_bound_of_blocks` compiles arbitrary
proved parent and child ABS rates into the actual digest/opening verifier:

```
Pr[accept and extraction fails]
  <= e_parent + e_child + N*max(kappa_parent,kappa_child)
     + merkleError(tA,N).
```

The shared generic definition retains BOTH adaptive BCS terms:

```
merkleError(tA,N) =
  (adaptiveNumerator(checkFuel,tA,N+4)
   + adaptiveNumerator(checkFuel,tA,N+3)) / |Digest|.
```

`FSJointChildCompiled81.certified_bound` selects all algebraic certificates
before the adversary and specializes this to

```
(N+1)*(3.781/2^128) + childSlope + FSCompiledData.bcs(tA,N),
childSlope = (1-theta80)*mu + 2/2^128.
```

`false_statement_bound` gives the same bound for actual verifier acceptance
on a false statement. No work cap is needed for this raw bound. The existing
work-normalized comparisons retain their explicit cap and 256-bit digest
assumptions. This refactor changes no numerical security claim and does not
assert arbitrary-depth recursive FS soundness.

From `formal/`, build the generic boundary and the checked all-error audit:

```sh
lake build polygero.Tests.FSGenericTest polygero.Tests.FSCachedJointTest
lake build polygero.APITest Lfzk.PolygeroStructureTest
```

The separate nonrecursive rate-1/16 table is documented in
[HahnRateSixteenth.md](HahnRateSixteenth.md). Its pre-existing native
certificate checks are separate from the kernel-checked FS instance audits.
