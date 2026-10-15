# Bcs and Fiat–Shamir

This directory formalizes the BCS compiler (Merkle-committed oracles plus Fiat–Shamir) and its soundness against a prover
that may re-commit and grind. The main result is used by the modeled Longfellow knowledge-soundness proof.

## Main result — `Bcs.TotalOracleCommit.Setup.ratio_le`

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

**Modelling.**

- SHA-256's running state followed by the PRF expansion is a random oracle on the deployed hash
  inputs. `Pt` finite is the only structural assumption.
- The Merkle oracle is independent of the challenge oracle.
