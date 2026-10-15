# Longfellow ZK: knowledge soundness and zero knowledge

This directory contains a formalized proof that validates the knowledge-soundness and zero-knowledge properties of the Longfellow scheme, as deployed using two finite fields with the v7 mdoc_hash and mdoc_sig circuits in which Ligero is used at rate 1/7 with 132 opened columns.

**The conditional combined v7 theorem gives 115-bit T-security in its oracle model.**
The improved signature-side analysis proves **127-bit T-security** with the same
protocol parameters. The hash side limits the combined guarantee.

## Start here

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
=======
| Question | Entry point |
|---|---|
| What is the combined soundness claim? | `CompiledZkProfileRows.v7P256Sha{1,2,3,4}_zk_circuit_tsec` in [CompiledZkProfileRows.lean](Lfzk/CompiledZkProfileRows.lean) |
| What improved? | `CompiledZkProfileRows.v7SigHahn_zk_circuit_tsec` in [CompiledZkProfileHahn.lean](Lfzk/CompiledZkProfileHahn.lean): signature T-security improves from 122 to 127 bits |
| What is the exact bound before rounding? | `row_zk_deployed_circuit_ratio_leT` and `CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT` |
| Which premises are still external? | [Assumptions and deployment boundary](#assumptions-and-deployment-boundary) below |
| Why not use the 125/127-bit Ligero table directly? | [Improved Ligero rows and sumcheck](#improved-ligero-rows-and-sumcheck) below |
| What does the privacy theorem prove? | [Witness indistinguishability](#witness-indistinguishability) below |

Names in this README are under `Lfzk` unless otherwise qualified. Files named
`CompiledZk*` analyze **soundness of the ZK verifier**; `CompiledLongfellowZk*`
contain the **privacy** results.

## The end-to-end statement

One adaptive prover makes `tA` Merkle-oracle queries and `N` transcript-oracle
queries. It may change commitments and grind. For each v7 pair (1–4 attributes),
with the hash circuit proved first and the signature circuit second:

```text
Pr[ both modeled verifiers accept
    ∧ the supplied MAC-key share is the oracle answer at the two roots
    ∧ no hash-side and signature-side extracted witnesses satisfy their circuits
      and agree on the common value ]
  ≤ (1 + tA + N) / 2^115.
```

Here “extracted” means that a witness comes from the committed matrix's
list-decoding candidates, `ZkLigeroV1.Lift`. `CircuitSide.toSide.Good` requires
that witness to satisfy `QuadCircuit.Satisfied` at the public input. The MAC
premises include a shared private blind; under that premise they force two good
witnesses to agree unless the combined multiplier is zero, an event of
probability `1/2^128`. There is no extra factor for the number of MAC blocks.
The separately committed blinds in Rust need the different argument described
under [Two-field MAC constraints](#two-field-mac-constraints).

The probability is a finite count over a uniform Merkle tape and a uniform
transcript-oracle function. `TM` only supplies enough tape for the execution;
it does not cap the adversary's query budget. Writing `T = tA + N`, T-security
means success is at most `(T + 1)/2^λ`, not a constant `2^-λ` for every attacker.

| Component | Field | `n / k / openings` | Current end-to-end T-security |
|---|---|---|---|
| `v7Hash1..4` | GF(2^128) | 3230..3436 / 461..490 / 132 | 115 bits |
| `v7SigHahn` | P-256 base field | 3187 / 455 / 132 | **127 bits** |
| `v7P256Sha1..4` | both | above | **115 bits** |

The original `v7Sig_zk_circuit_tsec` (122 bits) is retained. The stronger theorem
uses a new analysis row, `CertifiedV1.v7SigHahn`, and a larger extraction radius;
the verifier, field, circuit profile and opening count are unchanged.

## Where the error comes from

The uncapped two-field theorem in
[CompiledZkDeployedHash.lean](Lfzk/CompiledZkDeployedHash.lean) proves:

```text
Pr[bad] ≤ A + N·κ + 2·adaptiveNumerator(fc, tA, L + N) / 2^256

A = core_hash + core_sig + 1/2^128
κ = max(κ_hash, κ_sig, 1/2^128)
fc = 2·n_hash + 2·n_sig
L = 1 + rounds_hash + rounds_sig   (all protocol slots, including Ligero)

adaptiveNumerator(fc, tA, m)
  = tA(tA−1)/2 + (fc + tA)(2·tA + 1) + (fc + tA)·m
```

For one field, omit the MAC term and the other side, use `fc = 2n`, and drop
the factor 2 on the Merkle term. The quadratic term is the 256-bit hash's
birthday contribution. The `N·κ` term accounts for transcript grinding.

For a row with candidate bound `B`, field order `q`, `nl` layers, `s` sumcheck
rounds and output dimension `logv`, the current accounting is:

```text
core = B·[nl·(logv+2) + 2s + 1]/q + fail + arith + cover
κ    = max(B·(logv+2)/q, fail + arith, cover)
```

`fail + arith` bounds escaping Ligero combination challenges, and `cover`
bounds accepting column queries at a doomed challenge. The candidate factor
multiplies the field terms only. The separate Ligero row certificate
`epsRbr = B·(fail + arith + cover)` is more conservative than this composition.

Approximate exponents below mean `error ≈ 2^-exponent`. They are not additional
integer security claims. [soundness_report.py](scripts/soundness_report.py)
recomputes them with exact fractions before formatting.

| Row | Field contribution | Ligero contribution | `core` | `κ` |
|---|---:|---:|---:|---:|
| `v7Hash1` | 116.750 | 116.601 | 115.673 | 117.081 |
| `v7Hash2` | 116.720 | 116.548 | 115.632 | 117.087 |
| `v7Hash3` | 116.711 | 116.587 | 115.648 | 117.130 |
| `v7Hash4` | 116.692 | 116.557 | 115.623 | 117.129 |
| original `v7Sig` | 244.661 | 123.012 | 123.012 | 123.012 |
| **`v7SigHahn`** | 244.661 | **127.489** | **127.489** | **127.489** |

The improved signature row can also be supplied to the generic two-field theorem
through `CircuitSide.toSide`. It strictly reduces the constant term, while the
hash row still determines `κ` and the integer target stays 115. For example,
the one-attribute pair's core exponent improves from 115.664 to 115.673.
The named `v7P256Sha*` corollaries retain their original rows.

[TSec.lean](Lfzk/TSec.lean) proves a tighter conversion to T-security. Below
`tA ≤ G = 2^λ`, it charges the Merkle numerator to separate constant, `N` and
`tA` coefficients; above that cutoff `(1+N+tA)/2^λ ≥ 1`. Three exact slack
checks certify 127 bits for `v7SigHahn`. Unlike the older conversion, this does
not reserve half of the transcript-query coefficient or require `2λ+4 ≤ 256`.

## Improved Ligero rows and sumcheck

The [Ligero table](../ligero/README.md) certifies V1 IOP bounds of 125 bits
(hash) and 127 bits (signature). Those bounds integrate a response-uniform
envelope. Longfellow's current composition instead separates the two Ligero
rounds using doom thresholds. A flat IOP error is not a valid replacement for
either of those per-round budgets. 

The improvement here transfers the *mask certificate*, then proves the required
RBR bounds anew:

1. `Ligero.V1.ligerov1_roundByRound_mask_profiled` accepts a certified
   `V1MaskRange`, including Hahn/Delsarte bounds below the Johnson threshold.
   The original Johnson theorem remains as a specialization.
2. `LigeroV1Rows.Row.arithProfile` and the ZK composition now consume the row's
   certified mask range. Existing rows keep their Johnson-only values.
3. [LigeroV1RowsHahn.lean](Lfzk/LigeroV1RowsHahn.lean) uses the existing signature
   Hahn certificate at agreement 1665, with both doom thresholds 1664, radius
   parameters `e = 1522`, `g = 0`, and candidate bound 2. Its RBR certificate is
   126 bits; its Ligero contribution without the outer candidate factor is
   about `2^-127.489`.
4. [CertifiedHahn.lean](Lfzk/CertifiedHahn.lean) and the new circuit headline
   carry this through to the verifier's acceptance event and uncapped queries.

For the hash fields, moving directly to the new flat certificates' mask cutoffs
charges their large unchecked-mask lists at full weight in the challenge slot.
That loses the envelope integration that made the flat bounds attractive.
A stronger combined headline needs a proved composition of those envelopes with
the transcript-dependent sumcheck system, or stronger RBR estimates.

The generic sumcheck charge `2/q` is justified: a quadratic difference can have
two distinct roots and a nonzero Boolean sum, including in characteristic two.
[SoundnessAudit.quadratic_two_roots](Lfzk/SoundnessAudit.lean) formalizes the
example `X(X−a)`, with `a ≠ 0,1`. Replacing `2/q` by `1/q` merely because the
incoming claim is false would be unsound.

There is some remaining accounting slack: only the initial layer needs
`(logv+2)/q`, while later layer pairs need `2/q`. The current uniform pair
budget charges the former to every layer. Separating them would save
`B·(nl−1)·logv/q`, but would not raise these hash rows above 115 integer bits.
Even removing the Ligero contribution entirely leaves the present
list-weighted sumcheck charge above `2^-117`: improved Ligero alone can reach
at most 116 integer bits with this accounting. `SoundnessAudit` checks these
numeric limitations. **They are limits of this bound, not attacks or upper
bounds on the protocol's actual security.**

## Assumptions and deployment boundary

The proof constructs the arithmetic transitions; it does not assume that a false
witness makes the final output nonzero. Intermediate assert-zero gates can be
dead ends. The claim chain tracks pending assertions and catches each at its
own layer's fresh `beta`. This is essential for the registered circuits.

The dependency chain is:

```text
QuadCircuit + WellFormedP + Isolated + DeadEnd
  → ZkArithProfile.zkFieldDataP
  → padded sumcheck / assertion chain
  → Ligero V1 classifier on the system built by that transcript
  → Merkle extraction + message-prefix Fiat–Shamir
  → two-field MAC consistency
  → exact probability bound → T-security
```

| Boundary | What is checked or assumed |
|---|---|
| Circuit arithmetic | `ConcreteCircuit*` and `ZkArithProfile` construct honest values and boundary lemmas, including variable layer widths. `Satisfied` checks outputs and assert-zero constraints. |
| Registered artifacts | Rust inspectors check `WellFormedP`, `Isolated`, `DeadEnd` and geometry on the registered files. Their identification with the Lean `QuadCircuit` data is outside Lean. |
| Verifier correspondence | `CodeAgreesP`, initial points, message readers, tableau placement and sizes are premises. Equivalence to `zk_common.h` / the deployed verifier is not proved from source or machine code. |
| Commitments | The modeled opening check and V1 policy are composed formally. Byte encoding, leaf-as-column and root-as-context correspondence remain deployment obligations (the earlier R1/R2/R6 boundary). |
| Challenge sampling | Exact decoder balance is assumed for field elements, pairs, initial points, Ligero combinations and uniform fixed-size query sets. No reduction from the actual SHA-256/PRF sampler, including any bias, is supplied. |
| Hash model | Soundness uses a Merkle random oracle and an independent transcript oracle on context, role and message prefix. No previous challenge is re-absorbed. The running SHA-256 state and PRF expansion are idealized by this typed oracle. |
| Two-field MAC | `hrow₁`, `hrow₂` use the same multiplier, **private blind** `keyB` and public tags. Rust shares the public tags and challenge but has separate private MAC witnesses (v8 additive blinds; v7 multiplier shares). The existing composition does not establish the required bridge. |
| Extractor | The failure event quantifies over a finite lift list, at most two candidates here. Efficient list decoding and a polynomial-time witness-selection algorithm are not established. “Straight-line” refers to the query trace, not a proved runtime bound. |

### Verifier correspondence

The theorem proves a property of a Lean verifier. To apply it to Rust, one must
prove that whenever Rust accepts, the modeled verifier accepts the corresponding
statement and proof, with the same challenge distribution. Full equivalence is
unnecessary for soundness: this one-way implication suffices. Such a proof would
replace the current correspondence premises. A verified translation of the Rust
verifier, or generating a verifier from a verified executable definition, are
ways to build that connection. Importing the actual circuit artifacts with a
proved checker would discharge the circuit-data portion; it would not by itself
verify parsing, transcript handling, field operations or the verifier's control flow.
The existing artifact inspectors are useful checks, but are not that proof.

### Balanced challenge decoders

A decoder maps raw random coins to a field element, a tuple of elements, or a
set of queried columns. “Balanced” means each possible decoded output occurs
equally often, hence is uniformly distributed. For example, mapping a uniform
byte modulo 10 is not balanced: 0–5 each have 26 preimages, while 6–9 have 25.
Tuples must be jointly uniform; uniform individual coordinates alone are insufficient.

Rust's [field sampler](../../rust/runtime/algebra/src/fp_generic.rs) rejects
out-of-range integers, and [column sampling](../../rust/runtime/random/src/lib.rs)
uses rejection sampling and partial shuffling. These algorithms can be proved
uniform when fed independent uniform bytes. Such proofs could replace the
sampling assumptions. Alternatively, the soundness analysis could account for a
proved sampling bias instead of requiring exact uniformity.

There is a separate cryptographic boundary:
[Transcript](../../rust/runtime/random/src/transcript.rs) expands a SHA-256
digest using AES-256 on counter blocks. The raw challenge alphabet `C` must not
be identified with a 256-bit digest
without further proof. For example, the hash side's initial decoder produces
`logv+2 ≥ 5` field elements, already more than 256 uniformly random bits.
Exact balance over that target cannot be achieved by deterministic expansion of
one uniform 256-bit value. The theorem idealizes the expanded challenge itself.
`SoundnessAudit.no_256bit_init_decoder` proves this obstruction for the smallest
v7 hash output dimension. This does not demonstrate a practical attack. It means
the actual expansion needs an explicit computational or idealized-primitive
analysis and any resulting error term. The AES key here is a public transcript
digest; ordinary secret-key PRF security alone is not that analysis.

### Two-field MAC constraints

Rust already supplies the **same** `proof.macs` and challenge `av_val` as public
inputs to both circuits in
[verifier.rs](../../rust/applications/mdoc_zk/runtime/src/verifier.rs).
Both circuits assert the MAC equations. In the v8 circuits, each block satisfies:

```text
tag = a * message_hash + blind_hash
tag = a * message_sig  + blind_sig
```

These private blinds are the v8 circuits' `mac_ap` witnesses (distinct from the formal
theorem's optional multiplier share `aP`, which can be zero). The honest prover uses
equal blinds, but a malicious prover need not. The current Lean composition
assumes they are equal through its shared `keyB` parameter. Its argument that
unequal messages force `a = 0` depends on this stronger premise. For example,
`a = 1`, `(message_hash, blind_hash) = (0, 0)` and
`(message_sig, blind_sig) = (1, -1)` give equal tags with unequal messages.
`SoundnessAudit.separate_blinds_collision` checks that example in Lean.

The v7 compatibility path in
[mac.rs](../../rust/applications/mdoc_zk/runtime/src/mac.rs) instead computes
`tag = (a + private_share) * message`, matching
[the C++ MAC circuit](../../lib/circuits/mac/mac_circuit.h). It has separate
per-block private shares on each side. For soundness, expand this to
`tag = a * message + offset`, where `offset = private_share * message` is fixed
with the candidate witness. The same shared-offset assumption cannot be inferred
just from the verifier sharing public tags and `a`.

The intended argument for separate blinds uses **commitment before challenge**:
for fixed unequal messages and fixed blinds, tag equality gives
`a * (message_hash - message_sig) = blind_sig - blind_hash`, which determines at
most one `a`. `Mac.macTag_collision_card_le_one` proves this, giving `2^-128`
for each fixed pair. `Mac.shiftedMultiplier_collision_card_le_one` proves the
corresponding v7 bound. Composing these facts requires proving that the commitments fix
candidate lists, including the blinds, before `a` is sampled and accounting for
selection from those lists. A union bound over lists of sizes `B_hash`, `B_sig`
would charge at most `B_hash * B_sig / 2^128` at that step. This replacement has
**not** been composed through the end-to-end theorem. The current combined
headline remains conditional on the stronger MAC premises.

### Older clear-verifier endpoints

The older clear-verifier headlines (`CompiledLongfellowAdaptive*`, `CompiledV7*`,
`NizkDeployedHash*` without `Zk`) use `RbrSplit.FieldData.harith`, a nonvanishing
claim at a fixed initial point. `Arith.fieldData_harith_false` refutes that
premise in general for honest satisfaction; dead-end assertions also prevent
using it for these circuits. Those conditional theorems remain valid Lean
statements, but are not the deployed-circuit soundness result. Use the
`CompiledZkProfile*` endpoints.

## Witness indistinguishability

`CompiledLongfellowZk.compiled_longfellow_wi` and
`CompiledLongfellowZkTwoField.twofield_wi` compare honest proofs from two valid
witnesses for the same statement. In the two-field form the hidden common value
may differ too. For each side:

```text
ε(n,r,f) = [4n² + (2n−1)(2n−2) + 2(n−r)f] / 2^256
```

Here nonces and digests are 256 bits, `r = 132`, and `f` bounds Merkle queries.
The real-to-simulation distance is `ε` per side and `ε₁+ε₂` for two fields.
WI compares two real distributions and therefore pays **twice** those bounds.

| At `f = 2^115` | One side | Two fields |
|---|---:|---:|
| Real → simulation | ≤ `2^-128` | ≤ `2^-127` |
| Witness indistinguishability | **≤ `2^-127`** | **≤ `2^-126`** |

`CompiledLongfellowZkV7.v7_twofield_zk_q115` is the real-to-simulation result;
its `2^-127` must not be quoted as the two-witness WI bound.

The MAC hiding step models the additive-blind construction. The v7 formula
`(a + private_share) * message` is always zero at a zero message block, so its
tag distribution is not uniformly hiding there. Applying this privacy result
to v7 needs a separate treatment of zero blocks; the formal v7 parameter
instantiation alone does not supply that argument.

The simulator uses a noncomputably chosen reference witness for Ligero's
response (`referenceMessages`), so this does not establish efficient
zero-knowledge simulation. The experiment has one session, fixes the statement
before queries, and lets the distinguisher query after receiving the proof.
It assumes an injective codec and an appropriate causal honest frontend.
The distance is query-bounded; it is not an unconditional statistical hiding
claim.

The privacy model also separates the two trees into independent Merkle oracles
(`ZkTwoTape`), whereas deployment uses SHA-256 without domain separation between
those trees. This is an additional model-to-deployment gap, distinct from the
soundness theorem's shared Merkle oracle. The privacy theorem is not a proof
that this replacement preserves its bound.

## Reproduce the checks

From the repository root:

```sh
cd formal
lake build Lfzk
python3 lfzk/scripts/audit_axioms.py
python3 lfzk/scripts/soundness_report.py
python3 lfzk/scripts/v7_rows.py --check
python3 lfzk/scripts/rbr_v1_rows.py --check
python3 lfzk/scripts/inspect_v7_assertions.py
```

The separate `inspect_v7_circuit_profile.py` regenerates
[scripts/v7-circuit-profiles.json](scripts/v7-circuit-profiles.json) from the
registered artifacts. Rust inspectors need Cargo dependencies and a writable
Cargo cache. The two legacy row scripts check the original Johnson rows;
`soundness_report.py` additionally rechecks the Hahn signature certificate,
its T-security arithmetic, and the privacy numerals.

The axiom audit prints dependencies for the headlines, allowing Lean's
`propext`, `Classical.choice`, `Quot.sound` and the numeric `native_decide`
checks. It also scans `lfzk`, `bcs`, `merkle` and `sumcheck` for `sorry`, `admit`
and explicit `axiom` declarations. `native_decide` extends trust to Lean's
native evaluation mechanism; this audit does not eliminate the theorem
premises listed above or prove a correspondence with deployment.

## File map

| Layer | Files |
|---|---|
| Circuit and constraint model | `ConcreteCircuit`, `ConcreteCircuitBridge`, `Builder`, `Encode`, `ZkLayers` |
| Circuit-to-proof bridge | `ZkArithInit`, `ZkArithBoundary`, `ZkArithProfile` |
| Padded sumcheck and pending assertions | `RbrZkLongfellow`, `RbrZkSplit`, `ZkMultilinear` |
| Ligero RBR and rows | `LigeroRbr`, `LigeroV1Rbr`, `LigeroV1Rows*`, `ZkLigeroV1`, `CertifiedHahn` |
| Fiat–Shamir and Merkle composition | `NizkZk*`, `CompiledZk*`, `../bcs/Bcs/TotalOracle*` |
| End-to-end circuit headlines | `CompiledZkProfileRows`, `CompiledZkProfileHahn`, `TSec`, `SoundnessAudit` |
| Privacy | `LigeroZk/*`, `ZkAdaptiveV1`, `CompiledLongfellowZk*`, `ZkFrontendOfSetup`, `ZkTwoTape` |
