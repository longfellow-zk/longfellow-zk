# Longfellow ZK: knowledge soundness and zero knowledge

This directory contains a formalized proof that validates the knowledge-soundness and zero-knowledge properties of the Longfellow scheme, as deployed using two finite fields with the v7 mdoc_hash and mdoc_sig circuits in which Ligero is used at rate 1/7 with 132 opened columns.

The proof formalizes a version of round-by-round soundness together with the Fiat-Shamir transform, so the formalized security guarantees match our production environment.


```bash
cd formal && lake build Lfzk                    # everything below
python3 lfzk/scripts/audit_axioms.py            # #print axioms on 262 headlines; sorry/axiom scan
python3 lfzk/scripts/v7_rows.py --check         # re-derive every v7 numeral
python3 lfzk/scripts/rbr_v1_rows.py --check     # the v8 Ligero rows
python3 lfzk/scripts/inspect_v7_assertions.py   # WellFormedP/Isolated/DeadEnd on the registered v7 circuits
python3 lfzk/scripts/inspect_v7_circuit_profile.py  # regenerate v7-circuit-profiles.json from the registered artifacts
```

Every headline prints `[propext, Classical.choice, Quot.sound]`, plus, for theorems stated at a
numeric row, only that row's own `native_decide` facts (`<row>_valid`, `_slack_bound`,
`_slack_coeff`).  There is no `sorry`, `admit` or `axiom`.  This
library builds on its Ligero V1 analysis.

## Headlines

`Lfzk.CompiledZkProfileRows.v7P256Sha{1,2,3,4}_zk_circuit_tsec` (`CompiledZkProfileRows.lean`).
The setting:
- **The pairs** are the registered v7 ones: the 1–4-attribute hash circuit over GF(2^128), proved
  first, then the signature circuit over the P-256 base field, on one transcript.
- **The adversary** is one adaptive program that may re-commit and grind. It makes `tA` Merkle-oracle queries and `N` transcript-hash queries.

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```

This is **115-bit T-security**: an adversary that makes `T = tA + N` oracle queries wins with
probability at most `(T + 1) / 2^115`. Single-field forms:
- `v7Hash{1,2,3,4}_zk_circuit_tsec`: 115 bits;
- `v7Sig_zk_circuit_tsec`: 122 bits.

What each premise asks is explained under "The end-to-end theorem, part by part".

**Where the 115 comes from.** The proof first gives an exact bound with no query budget
(`CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT`):

```text
Pr[ … ]  ≤  zkCore  +  N · κ  +  2 · adaptiveNumerator(fc, tA, L + N) / 2^256

adaptiveNumerator(fc, tA, m) = tA(tA−1)/2 + (fc + tA)(2·tA + 1) + (fc + tA)·m
```

- `zkCore ≈ 2^-115.6` is what every adversary pays: the sumcheck rounds' error with the list
  factor, plus Ligero's.
- `κ ≈ 2^-117.1` is the worst single challenge, Ligero's combination challenge, paid once per hash
  query.
- The last term is extraction failure in the Merkle trees. Its `tA²` part is the birthday bound of
  the 256-bit Merkle hash. `fc` is the verifier's Merkle-check queries, and `L` the transcript's
  rounds.

`Lfzk.TSec.tsec_of_uncapped` turns this into `(1 + tA + N) · 2^-115`. For `tA, N ≤ 2^137` the
Merkle term is at most `tA · 2^-115`. Above that, the right-hand side exceeds 1 and the claim is
trivial. The signature row's per-query term is already about `2^-123`, which leaves it at 122 bits.

### Knowledge soundness at the deployed zero-knowledge verifier, field half abstract

`Lfzk.CompiledZkDeployedHash.row_zk_deployed_ratio_leT` and `twofield_zk_deployed_ratio_leT`
(`CompiledZkDeployedHash.lean`) are the exact bound above, with the field half (`ZkFieldData`) per
context as a premise. The headline discharges that premise from the circuits. The other
`CompiledZk*` and `*_zk_deployed_ratio_le` forms close the Merkle term at a fixed budget to print a
single numeral; they are corollaries of these.

The verifier is `zk_common.h` / `ZkVerifier::verify`:

- Sumcheck round polynomials are padded, and `p(1) := claim − p(0)` is substituted. There is no
  cleartext round check.
- Each layer emits its `finalize` row and triple, and the input row is emitted at `alpha_in`.
- `begin_circuit` draws the output point `G`.
- The only verdict is Ligero V1's, on the system the transcript built.

The extractor is straight-line. It reads the Merkle query trace and decodes the lift list, the
witnesses within the list-decoding radius of the committed matrix. Per row
(`CompiledZkProfileRows.lean`):

| row (v7) | field | n / k / r | Ligero RBR bits | `zkCore` | `κ` per hash query | T-security |
|---|---|---|---|---|---|---|
| `v7Hash1..4` (1–4 attributes) | GF(2^128) | 3230..3436 / 461..490 / 132 | 115 | ≈ 2^-115.6 | ≈ 2^-117.1 | 115 bits |
| `v7Sig` | P-256 base | 3187 / 455 / 132 | 122 | ≈ 2^-123.0 | ≈ 2^-123.0 | 122 bits |
| two-field `v7P256Sha1..4` | both | — | — | ≈ 2^-115.6 | ≈ 2^-117.1 | 115 bits |

- **Per-candidate doom has three branches** (`RbrZkLongfellow.ZkWrong`):
  - (a) the de-padded claim is wrong at the layer's own `beta`;
  - (b) an assertion two or more layers further down is violated;
  - (c) the next layer's assertion vector, with the coordinates bound so far, is not identically zero.

  The compiler gives each assert-zero gate its own wire, and no later layer reads it (`DeadEnd`,
  `Isolated`). So a violated intermediate assertion never reaches the output. It is caught at its
  own layer, where the incoming claim was sent before that layer's `beta`. Every layer's `beta` is
  a fresh challenge drawn in protocol order.
- **The budgets are unchanged.** They are `2|F|` per layer pair, 2 per round and 1 per binding. The
  `G` slot costs `(logv+2)/|F|` by Schwartz–Zippel (`ZkMultilinear`).

### Zero knowledge, as proved: an explicit simulator, against query-bounded distinguishers

`Lfzk.CompiledLongfellowZk.compiled_longfellow_zk` and `…TwoField.twofield_zk`. For every valid
witness, the real proof is `ε`-close to a simulation that reads no witness. This holds against
every distinguisher that sees the proof and both challenge oracles in full and makes `f`
Merkle-oracle queries. The proof consists of:

- the salted Merkle commitment;
- the padded sumcheck messages;
- the Ligero V1 response and openings;
- the MAC tags, for the two-field form.

The simulator (`simExp`, with Ligero's response from `ZkAdaptiveV1.simResp`):

- commits to the all-zero tableau with fresh padding. The opened columns are uniform because
  every row carries 132 random padding values;
- samples the sumcheck messages uniformly. The pad makes them uniform for every round oracle, so
  the round oracle is never programmed;
- answers Ligero with the honest formulas on the zero tableau, plus one public correction on the
  linear rows. The correction is the base-code row whose witness part carries the statement's
  target and which vanishes on the query set (`linCorr`). It is unique (`linCorr_unique`), so it
  is a function of public data;
- programs the Ligero challenge oracle at its two points.

`ZkAdaptiveV1.statClose_adaptive` shows this response is distributed exactly like the honest one,
by a bijection of the prover's randomness. Here `ε = (4n² + 2·d·f)/2^256 + (2n−1)(2n−2)/2^256` per
side, with `n` columns, `d` of them unopened. That is **≤ 2^-128 per side and ≤ 2^-127 for the
two-field proof at `f = 2^115`** (`…ZkV7.v7_twofield_zk_q115`).

What this is, and what it is not:

- **Computational, not statistical.** The bound grows with the distinguisher's Merkle (SHA-256)
  queries. The `2·d·f/2^256` term is guessing an unopened leaf's 256-bit nonce, so a distinguisher
  that can afford about `2^256/d` hash evaluations is not covered.
- **Witness indistinguishability follows**: `compiled_longfellow_wi` and `twofield_wi` (`2ε`; in
  the two-field form the MAC'd common value may differ too).
- **"Explicit" is up to Lean's representation of the code.** `linCorr` is picked with
  `Classical.choose`, exactly as the honest prover's own `C.encode` is; concretely both are
  interpolations.
- **Compiled setting only.** The simulator needs the query set before it answers, which
  programming the Ligero oracle gives. The IPCP-level theorems (`CompiledLigeroZk`,
  `FromLigeroZKV1`), where the query comes after the response, keep `formal/ligero`'s
  reference-witness simulator.
- **The model:** a programmable random oracle, a single session, and a statement fixed before the
  distinguisher queries. The Merkle hash and the transcript hash are independent oracles; deployed,
  all are SHA-256, with no domain separation between the two trees. The codec is injective
  (`Cod.Inj`), and causality of the honest prover (`CausalFS.causal`) is assumed at the abstract
  `ZkSetup`.

## The arithmetization is constructed, not assumed

`Lfzk.Arith` (`ConcreteCircuit.lean`, `ConcreteCircuitBridge.lean`) builds `LayeredCircuit` from a
concrete layered quadratic circuit in the deployed format, with `prep_v`'s `beta` substitution. It
proves the three fields that used to be assumed: `Quad_affine_beta`, `V_local` and `layer_rel`. It
also proves:

- the input-layer identification (`toLayered_input_wMle`);
- the verifier's EQQ agreement (`toLayered_eqqAgree`);
- compiler correctness in the form that is true (`toLayered_unsat_iff`): unsatisfied ⇔ the outputs
  are nonzero, or some intermediate layer moves with its own `beta`.

`ZkArithBoundary.zkFieldDataOf` builds the whole field half of the ZK chain at the honest
`Satisfied`, for circuits with one width at every layer. Its hypotheses are `WellFormed`,
`OneWire`, `Isolated`, `DeadEnd`, `CodeAgrees`, `AsgAgrees` and the decoder balances.


## The end-to-end theorem, part by part

`Lfzk.CompiledZkProfileRows.v7P256Sha1_zk_circuit_tsec`, for one attribute (the other three pairs
differ only in the hash row and its `logv`):

```lean
theorem v7P256Sha1_zk_circuit_tsec {tA N TM : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        S₁.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          S₂.toSide.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            S₂.toSide.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115
```

**The adversary and the oracles.**

- `body : TwoOracleTree Enc D (Pt2 …) C Out tA N` is the prover. It is one adaptive program that
  may re-commit and grind:
  - it makes `tA` queries to the Merkle oracle (inputs `Enc`, digests `D`);
  - it makes `N` queries to the transcript oracle, whose inputs are `Pt2` and answers `C`;
  - it outputs a proof `Out`.
- `Pt2` is the set of hash inputs as deployed. It has three kinds of point:
  - the key point (the two Merkle roots);
  - side 1's points: context, role, message prefix;
  - side 2's points, which also carry side 1's messages.

  No challenge is ever re-absorbed. Treating SHA-256's running state followed by the PRF expansion
  as a random oracle on these inputs is the hashing idealisation (`NizkDeployedHash`).
- The probability is over `(Fin TM → D) × (Pt2 … → C)`: a uniform Merkle tape and a uniform random
  function on the hash inputs. The left-hand side is the event's count over that space.
- `htape`, `hTM` give the Merkle tape room for the run (`fc + tA ≤ TM`). This is sampling
  bookkeeping, not a bound on the adversary.

**The two circuits** (`S₁`, `S₂ : CircuitSide …`). Side 1 is the hash circuit (output dimension 3),
side 2 the signature circuit (8). A `CircuitSide` bundles:

- **The circuit:** `c`, its layer count `hnl`, and the facts `hwf` (`WellFormedP` at the row's width
  profile), `hiso` (`Isolated`) and `hde` (`DeadEnd`). All three are decidable and checked on the
  registered v7 circuits by `inspect_v7_assertions.py`. That `QuadCircuit` is the artifact's bytes
  is not proved; the Lean side takes the circuit as data.
- **The public input:** `pubIn av x`, at the MAC key share and the public data.
- **The verifier's code:** `Vc`, with `hV : CodeAgreesP` and `hst0`. This is the transliteration of
  `zk_common.h`:
  - its next points are the bound list's interleaved even and odd coordinates;
  - its layer coefficient is `bind_gh_all` at the layer's own `beta`;
  - its input row is the `alpha_in`-combination of the two points' `EQ` vectors, the public part
    folded in;
  - `begin_circuit` puts both points at `G`;
  - `nlin`/`nt` fit (`hnlin`, `hnt`).

  That the deployed verifier computes exactly this is transliteration debt.
- **The Ligero layout:** the placement `pl` of the built system in the tableau, the Reed–Solomon
  domain `dom`, and how a message carries Ligero's response (`respOf`).
- **Exact decoder balance:** `kinit … kq`, `hbal…`, `hk…`. Each challenge decoder hits every value
  equally often. This idealises the PRF expansion of the transcript digest.
- **The field size:** `hF : |F| = fieldSize`.

**Reading the proof.**

- `rootOf₁`, `rootOf₂`, `avOf`, `pubOf`, `msgOf₁`, `msgOf₂`, `claimOf₁`, `claimOf₂` say where the
  roots, the MAC key share, the public data, the round messages and the Merkle openings sit in the
  proof.
- `codec₁`, `codec₂` encode a Merkle leaf as nonce ‖ column. Transliteration debt:
  - R1: a Merkle leaf is a column;
  - R6: the commitment context is the root.
- `hD`: digests have 256 bits.

**The MAC.**

- `aP`, `decode`, `kmac`, `hbal`, `hmac`, `hFmac`: the MAC key share is decoded from the key
  point's answer, balanced, over a field of `2^128` elements.
- `keyB`, `tagOf`, `common₁`, `common₂`: the proof's key blocks and tags, and how a witness carries
  its common value.
- `hrow₁`, `hrow₂`: if side `k` accepts and `a` is a good witness, then the MAC of `a`'s common value
  is the proof's tag. Each circuit enforces the MAC on its bit-packed common value, and this is
  assumed of the circuits.

**The event.**

- `S₁.toSide.acceptsDH …`, `S₂.toSide.acceptsDH …`: each side's deployed zero-knowledge verifier
  accepts. Its transcript, at its slice of the challenges, builds a Ligero system, and the
  Merkle-compiled V1 check accepts the proof's response on it. Transliteration debt R2: the
  deployed Ligero check is V1's policy.
- `challenges ⟨0⟩ = avOf proof`: the key share in the proof is the oracle's answer at the key point.
- `¬ ∃ a₁ a₂, Good … a₁ ∧ Good … a₂ ∧ common₁ a₁ = common₂ a₂`: extraction fails. A good witness
  is the committed witness of a lift-list member that satisfies its side's circuit
  (`QuadCircuit.Satisfied`) at the side's public input. No hash-side and signature-side good
  witnesses agree on the common value.

**The bound:** `(1 + N + tA) / 2^115`, 115-bit T-security; see "Where the 115 comes from".

## Superseded clear-verifier headlines

Phases 2–3 and their v7 and Phase 5 restatements
  (`CompiledLongfellowAdaptive.*`, `CompiledV7`, `NizkDeployedHash*`, and the `…S` mixed-accounting
  forms) take `RbrSplit.FieldData`, whose `harith` premise is the claim's non-vanishing at a
  **fixed** initial point. That premise is refuted:
- in general for honest satisfaction (`Lfzk.Arith.fieldData_harith_false`);
- for the deployed circuits by the dead-end assertions (a witness violating only a deep assertion
  leaves the output at zero).

Those theorems remain true statements, but they are not soundness results for the deployed
circuits. The `CompiledZk*` headlines replace them, and `CompiledZkProfileRows` end to end.

## Files

| group | files |
|---|---|
| model | `Types`, `WPoly`, `Builder`, `Circuit`, `Rounds`, `Layers`, `LigeroRows`, `LigeroSystem`, `Encode`, `ZkLayers`, `ZkHiding`, `ZkSim` |
| Ligero V1 RBR | `LigeroRbr`, `LigeroV1Rbr`, `LigeroV1Rows`, `LigeroV1RowsV7` |
| clear-verifier chain (superseded, see above) | `Rbr*`, `Nizk*`, `CertifiedV1`, `CertifiedV7`, `CompiledLongfellow*`, `TwoField*`, `CompiledV7`, `*S` |
| deployed hash inputs | `../bcs/Bcs/TotalOracle`, `TotalOracleCommit`, `NizkDeployedHash*` |
| ZK-verifier chain | `ZkMultilinear`, `RbrZkLongfellow`, `RbrZkSplit`, `ZkLigeroV1`, `NizkZk`, `NizkZkTwoField`, `CompiledZk`, `CompiledZkTwoField`, `CompiledZkRows`, `CompiledZkTwoFieldRows` |
| ZK-verifier chain, deployed hash inputs | `NizkZkDeployedHash`, `CompiledZkDeployedHash`, `CompiledZkDeployedHashRows` |
| arithmetization | `ConcreteCircuit`, `ConcreteCircuitBridge`, `ZkArithInit`, `ZkArithBoundary`, `ZkArithProfile` (deployed width profile) |
| end-to-end headlines | `CompiledZkProfileRows` |
| zero knowledge | `LigeroZk/*`, `../merkle/Merkle/{Hiding,CommitCollision}`, `FromLigeroZKV1`, `ZkFiatShamir`, `ZkMerkle`, `ZkProgram`, `ZkLongfellow`, `CompiledLigeroZk`, `TwoFieldZk`, `ZkAdaptiveV1`, `CompiledLongfellowZk`, `ZkFrontendOfSetup`, `ZkTwoTape`, `CompiledLongfellowZkTwoField`, `CompiledLongfellowZkV7` |
| scripts | `audit_axioms.py` (axiom footprint, no `sorry`); `inspect_v7_circuit_profile.{py,rs}` → `v7-circuit-profiles.json` (the deployed profiles, from the registered artifacts); `v7_rows.py` with `rbr_v1_rows.py` (`--check`: the Lean rows match those profiles); `inspect_v7_assertions.{py,rs}` (`WellFormedP`, `Isolated`, `DeadEnd` on the registered circuits) |
