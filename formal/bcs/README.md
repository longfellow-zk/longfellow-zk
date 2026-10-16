# Bcs and Fiat–Shamir

This directory formalizes the BCS compiler (Merkle-committed oracles plus Fiat–Shamir) and its soundness against a prover
that may re-commit and grind. The original round-by-round compiler and the newer
extraction-first potential compiler are both used by modeled Longfellow results.

## Round-by-round result — `Bcs.TotalOracleCommit.Setup.ratio_le`

**The setting** (`Bcs/TotalOracleCommit.lean`).

- **Prover.** One adaptive program that may interleave queries to two oracles, try various commitments and
  grind:
  - at most `tA` queries to the Merkle oracle, which is sampled lazily from a tape `mt`;
  - at most `N` queries to the challenge oracle `H : Pt → C`.
- **Challenge oracle.** `H` is a uniformly random function on a finite set `Pt` of hash inputs.
- **Verifier.** It recomputes round `k`'s challenge as `H(hashInput(proof, k))` for `k < L`.
  The hash input is read from the proof alone: context, round, message prefix, and no earlier
  challenge.
- **Extraction** is straight-line. The context of the proof's commitment is the Merkle queries
  the prover made before its first challenge query that names that commitment.

### The BCS theorem statement

```text
Pr_{mt, H}[ Acc  ∧  Fails(context) ]
    ≤  (N · βmax + ∑_{k<L} slotBeta k) / |C|  +  adaptiveNumerator fc tA (L + N) / |D|

adaptiveNumerator fc tA m = tA(tA−1)/2 + (fc + tA)(2·tA + 1) + (fc + tA)·m
```

- `Acc` is any acceptance event that includes the Merkle opening check.
- `Fails` is extraction failure in the commitment's context.
- `|C|` is the size of the challenge space, `|D|` the size of the Merkle digest space, and `fc`
  the Merkle-oracle queries the verifier's opening check makes.

- The first term is the Fiat–Shamir side. Each of the `N` points the prover asks, and each of the
  verifier's `L` points, is charged its round's escape budget `β`.
- The second term is the Merkle side. The opening verifies, but the cut-trace extraction does not
  explain it: a collision, a guessed root, or an opening not backed by a query.

**What the caller supplies.**

- `hbad`: per-point bad sets of size at most `β`.
- `hchain`: an accepted, explained, failing run has a round-level bad event.

`hchain` comes from a round-by-round argument:

- `Bcs.Rbr` (`RoundByRound.lean`) holds a doomed-state function with per-round escape budgets.
- `Bcs.ClaimChain` (`ClaimChain.lean`) builds one from per-candidate claims, paying the list size
  `|Cand|` once per round (`doom_preserved_of_perCandidate`).
- `Bcs.TotalOracle.Grinding.ofRbr` (`TotalOracle.lean`) links it to the hash inputs.

**`Setup.ratio_le_two`** is the same bound for two Merkle commitments under one key, the two
Ligero commitments of the two-field proof. It costs `2 · adaptiveNumerator / |D|`.

## Extraction-first potential compiler

[`Bcs.Potential`](Bcs/Potential.lean) proves the generic signed-change and
positive-increase accounting. The oracle modules charge a potential at fresh
hash answers, including a pair of dependent hash inputs when the prover asks
for the child query before its parent challenge. The caller supplies a
pointwise path-payment proof: an accepting transcript on which extraction
fails has at least one unit of total charge.

`Bcs.TotalOracleCommit.Setup.extraction_failure_ratio_le_two_verifier_potential`
in [PotentialCommit](Bcs/PotentialCommit.lean) is the two-opening theorem used
by the newer Longfellow proof. If the charge at each fresh point sums to at
most its local budget, each local budget is at most `βmax`, and the verifier's
`L` hash inputs have slot budgets `slotBeta`, it proves

```text
Pr[Acc ∧ extract = none]
  ≤ (N · βmax + ∑ᵢ slotBeta i) / |C|
    + 2 · adaptiveNumerator(fc, tA, L + N) / |D|.
```

The factor `N` is the current transcript-query factor; two Merkle openings
give the factor `2`. The compiler itself does not choose an agreement cutoff
or add a candidate-list multiplier. Its client proves the local potential
budgets and the extraction path payment.

**Where it is used.**

- `Lfzk.NizkZkDeployedHash` → `Lfzk.CompiledZkDeployedHash` → the modeled v7
  `Lfzk.CompiledZkProfileRows.v7P256Sha*_zk_circuit_tsec` bound
  `(1 + tA + N) · 2^-115` under its shared-blind premise. The separate-private-MAC headline
  `v7P256Sha*_zk_circuit_tsec_sepMac` composes the same BCS result with a
  fixed-candidate MAC collision bound.
- The Fiat–Shamir term becomes the row's field and Ligero densities plus
  `N · zkCoefficient`. The Merkle term keeps the exact query count.
  `Lfzk.TSec.tsec_of_uncapped` folds both into T-security: its `tA²` birthday
  part is at most `tA · 2^-115` for `tA ≤ 2^137`; beyond that the stated bound
  already exceeds 1.
- The earlier `v7P256Sha*_zk_circuit_ratio_le` theorem gives a different
  bound of `2^-115 + N·2^-117` plus its Merkle term. It is not the
  separate-private-MAC headline.
- The potential compiler feeds the separate
  [`Lfzk.FlatV7All`](../lfzk/Lfzk/FlatV7All.lean) extraction and
  false-statement theorems at `(1 + tA + N) / 2^116` for the modeled v7
  V1 circuits. Those headlines combine a flat zero-query result with a
  graded positive-query result; their circuit and transcript premises are
  listed in the [Longfellow README](../lfzk/README.md).

**Modelling.**

- SHA-256's running state followed by the PRF expansion is a random oracle on the deployed hash
  inputs. `Pt` finite is the only structural assumption.
- The Merkle oracle is independent of the challenge oracle.
