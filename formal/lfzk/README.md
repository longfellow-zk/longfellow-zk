# Longfellow ZK: soundness and privacy for the modeled v7 protocol

This directory contains conditional Lean proofs of knowledge soundness and zero knowledge for a
model of Longfellow's v7 circuit and transcript layout. The model runs two circuits on one
Fiat–Shamir transcript:

- the registered **v7** SHA-256 hash circuit (1–4 attributes) over GF(2^128), proved first;
- the ECDSA signature circuit over the P-256 base field, proved second.

They are linked by a two-field MAC. Each circuit is a padded, layered sumcheck followed by Ligero V1
at rate 1/7 with 132 opened columns. The strongest result is extraction-first and combines a flat
zero-query bound with the graded positive-query Fiat–Shamir compiler. The earlier round-by-round
result remains available. Both account for a prover that may re-commit and grind.

| | result | where |
|---|---|---|
| **Combined extraction and false-statement soundness** (modeled v7, 1–4 attributes) | **116-bit T-security**: `Pr[win] ≤ (1 + tA + N)·2^-116`, for all query budgets, conditional on the circuit and transcript premises below. Each circuit keeps its own private MAC witness | `FlatV7Headline.v7Hash1_deployed_fs_extraction_116_circuit` and `v7Hash1_deployed_fs_false_statement_116`, with `FlatV7Hash{2,3,4}Headline` analogues; build `Lfzk.FlatV7All` |
| Earlier round-by-round combined bound | **115-bit T-security** under its stated premises | `CompiledZkProfileRows.v7P256Sha{1,2,3,4}_zk_circuit_tsec_sepMac` (v7 MAC) |
| Signature circuit alone | **127 bits** with the Hahn mask certificate (122 with the Johnson row) | `CompiledZkProfileRows.v7SigHahn_zk_circuit_tsec` |
| Hash circuit alone, earlier round-by-round result | 115 bits | `CompiledZkProfileRows.v7Hash{1,2,3,4}_zk_circuit_tsec` |
| **Zero knowledge**, 256-bit nonces | ≤ 2^-128 per side, ≤ 2^-127 two-field, against 2^115 Merkle queries. For the v7 MAC the simulator receives the message blocks' zero pattern | `CompiledLongfellowZkV7Mac.v7mac_twofield_zk_q115` (v7 MAC); `CompiledLongfellowZkV7.v7_twofield_zk_q115` (additive MAC) |
| Zero knowledge, 542-bit nonces | statistical, ≤ 2^-131 two-field, no query bound; the v7 MAC simulation receives the zero pattern | `CompiledLongfellowZkV7Mac.v7mac_twofield_zk_stat542` |
| Witness indistinguishability | ≤ 2^-127 per side and ≤ 2^-126 two-field at 2^115 queries; the v7 two-field claim requires equal zero patterns | `CompiledLongfellowZk.compiled_longfellow_wi`, `CompiledLongfellowZkV7Mac.twofield_wi_v7` |

The hash side limits the combined soundness level. Names are under `Lfzk` unless qualified.
For the transmitted four-slice Ligero V1 response, the interactive theorem
`V1StrongV7Interactive.v7_v1_payload_iop_uniform_failure_le` bounds a prover that
chooses its payload after a uniform combination challenge, before the uniform
column query, by the exact coefficient
`V1StrongV7Numeric.density`. At v7 hash1 this is approximately **125.511851
bits**. The earlier IOP certificate for arbitrary evaluation-form responses
gives approximately **125.158571 bits**; the response representations differ.
The companion `v7_v1_payload_iop_failure_le` states the same coefficient for
balanced raw challenge/query decoders. Under `NoDecodedSolution`,
`v7_v1_payload_iop_uniform_acceptance_of_noDecoded_le` bounds ordinary
interactive acceptance by the same coefficient.
For standalone Ligero V1, `V1StrongV7TranscriptOutsideOutput.v7_v1_outside_output_extraction_failure_le`
counts acceptance with the response-assisted extractor returning `none` at the verifier's
prefix-only hash points. For each of the four v7 hash geometries and an `N`-query prover,
its conditional probability bound is `(N+1)·density`, with the checked coefficient
`density < 6/2^128` (`V1StrongV7TranscriptFinal.v7_v1_final_budget_lt_six`).
`V1StrongV7Terminal.accepted_extracts_or_fails` proves that any accepted response outside
this event extracts a satisfying lift. The premises include the ideal balanced challenge/query
sampler. The statement and commitment oracle may depend on all hash answers outside the two
terminal Ligero roles, including earlier field challenges that the transcript does not re-absorb.
The optional `Lfzk.V1StrongV7Hash1HybridCircuitHeadline` target applies this direct
terminal count to the v7 hash1 two-field FS extraction event. It derives the
four-slice response-slot and decoder identities from the typed message constructor,
instantiates both circuit sides and the merged Merkle checker, and proves
extraction failure and false-statement soundness at `(1 + N + tA) / 2^116`
for every query budget, under its stated circuit-MAC row and resource premises.
This is an independent extraction-first route to the same 116-bit envelope and
is separate from the routine build.
The 116-bit circuit theorems use the certified flat Ligero extraction bound at zero transcript queries
and `v7_circuit_potential_extraction_116_of_pos_queries` from the graded extraction-first
compiler at positive query counts. The more general `v7Hash*_deployed_fs_extraction_116`
theorems retain the earlier positive-query compiler because their signature side is a
`CompiledZkSide`; the circuit headlines use a `CircuitSide` on both sides. The analysis radius enlarges
the hash candidate list; it does not change the verifier or its commitments.
Files named `CompiledZk*` are about **soundness of the zero-knowledge verifier**;
`CompiledLongfellowZk*` contain the **privacy** results.
The separate `_sepBlind` theorems use the v8 MAC equation with the same v7 circuit profiles;
they are not soundness theorems for the v8 circuits. Applying any of these theorems to deployed
Rust requires the correspondence assumptions described below.

## Reproduce the checks

```sh
cd formal
lake build Lfzk                                   # ordinary Longfellow target
lake build Lfzk.GradedCircuitGrid                 # separate v7/v8 graded extraction grid
lake build Lfzk.FlatV7All                         # separate 116-bit extraction target
lake build Lfzk.V1StrongV7TranscriptOutput         # separate V1 FS extraction bound
lake build Lfzk.V1StrongV7TranscriptOutsideOutput  # V1 bound with prior field-answer context
lake build Lfzk.V1StrongV7Hash1HybridCircuitHeadline # separate direct v7 hash1 circuit bound
python3 lfzk/scripts/generate_flat_v7_variants.py --check
python3 lfzk/scripts/audit_potential_axioms.py    # potential compiler, v7/v8 extraction, v7 headlines
python3 lfzk/scripts/audit_axioms.py              # #print axioms on every headline; sorry/admit/axiom scan
python3 lfzk/scripts/soundness_report.py          # earlier round-by-round exponents, Hahn certificate, privacy numerals
python3 lfzk/scripts/v7_rows.py --check           # re-derive every v7 row numeral
python3 lfzk/scripts/rbr_v1_rows.py --check       # the Johnson (and v8) Ligero rows
python3 lfzk/scripts/inspect_v7_assertions.py     # WellFormedP / Isolated / DeadEnd on the registered v7 circuits
python3 lfzk/scripts/inspect_v7_circuit_profile.py  # regenerate v7-circuit-profiles.json from the registered artifacts
```

The Rust inspectors need Cargo dependencies and a writable Cargo cache. `soundness_report.py`
recomputes the exponents below with exact fractions and rechecks the Hahn signature certificate.

**What the audit establishes.** The headline proofs use Lean's standard axioms
`[propext, Classical.choice, Quot.sound]`. Numeric row proofs also use `native_decide` facts
(`<row>_valid`, `_slack_bound`, `_slack_coeff`, …). The scan finds no `sorry`, `admit` or `axiom`
in `lfzk`, `bcs`, `merkle` or `sumcheck`. `native_decide` extends trust to Lean's native
evaluator. The audit does not remove the theorems' premises, and it does not prove correspondence
with the deployed code. This library builds on the Ligero V1 analysis in `formal/ligero/`.

## Where to look

| Question | Entry point |
|---|---|
| What is the strongest combined claim? | The extraction and false-statement theorems in [FlatV7Headline.lean](Lfzk/FlatV7Headline.lean), checked together with hash2–4 by `Lfzk.FlatV7All` |
| What is the earlier round-by-round claim? | `CompiledZkProfileRows.v7P256Sha{1,2,3,4}_zk_circuit_tsec_sepMac` in [CompiledZkProfileSepMac.lean](Lfzk/CompiledZkProfileSepMac.lean) |
| Which premises are still external? | [Assumptions and deployment boundary](#assumptions-and-deployment-boundary) |
| What does the privacy theorem prove? | [Zero knowledge](#zero-knowledge) |

# Soundness

## The end-to-end statement

One adaptive prover makes `tA` Merkle-oracle queries and `N` transcript-oracle queries. It may
change commitments and grind. For each v7 pair (1–4 attributes):

```text
Pr[ both modeled verifiers accept
    ∧ the supplied MAC-key share is the oracle answer at the two roots
    ∧ no hash-side and signature-side extracted witnesses satisfy their circuits
      and agree on the common value ]
  ≤ (1 + tA + N) / 2^116.
```

- **T-security.** Writing `T = tA + N`, success is at most `(T + 1)/2^λ`, not a constant `2^-λ`
  for every attacker.
- **The probability.** It is a finite count over a uniform Merkle tape and a uniform function on
  the transcript-hash inputs. `TM` only supplies enough tape for the execution; it does not cap
  the adversary's queries.
- **"Extracted".** A witness comes from the committed matrix's list-decoding candidates
  (`ZkLigeroV1.Lift`, at most two here). `CircuitSide.toSide.Good` requires that witness to
  satisfy `QuadCircuit.Satisfied` at the side's public input.
- **The MAC.** In the `_sepMac` / `_sepBlind` headlines each circuit checks the tag against its
  **own** private MAC witness (`share_k`, `blind_k`), exactly as Rust does. The key point's answer
  is drawn after both commitments, so both candidate lists are fixed before it. Each pair of
  candidates with different messages has at most one bad multiplier, which charges
  `B_hash·B_sig/2^128 = 4/2^128` at the key slot. It fits the 116-bit bound; see
  [Two-field MAC constraints](#two-field-mac-constraints). The original `v7P256Sha*_zk_circuit_tsec`
  remain; they assume a shared blind.

| Component | Field | `n / k / openings` | End-to-end T-security |
|---|---|---|---|
| `v7Hash1..4` | GF(2^128) | 3230..3436 / 461..490 / 132 | 115 bits |
| `v7Sig` (Johnson row) | P-256 base field | 3187 / 455 / 132 | 122 bits |
| `v7SigHahn` | P-256 base field | 3187 / 455 / 132 | **127 bits** |
| v7 hash1–4 paired with `v7SigHahn` (flat/graded extraction) | both | above | **116 bits** |
| `v7P256Sha1..4` (earlier round-by-round theorem) | both | above | 115 bits |

`v7SigHahn` is a new analysis row (`CertifiedV1.v7SigHahn`) with a larger extraction radius. The
verifier, field, circuit profile and opening count are unchanged. The named `v7P256Sha*`
corollaries keep the original signature row. Supplying `v7SigHahn` through `CircuitSide.toSide`
lowers the separate-MAC core from 115.663 to 115.672 bits for one attribute, but the
hash row still sets `κ` and the **earlier round-by-round** integer level stays at 115. With separate private MAC
witnesses, the full Hahn-paired constant, including the Merkle and transcript terms at
zero adversary queries, is at most `(651/1000)·2^-115` for each profile
(`SoundnessAudit.hahn_twofield_linear_slack`). The generic two-field theorem supplies
the query-dependent terms. For `tA ≤ 2^115`, its exact right-hand side with
the Hahn signature row is certified to be at most
`(651/1000)·2^-115 + N·2^-117 + tA·2^-138`
(`SoundnessAudit.hahn_twofield_linear_rhs`, for all four hash profiles). This is a
numerical specialization of the generic extraction theorem; the named `v7P256Sha*`
corollaries continue to use the Johnson signature row.

The separate 116-bit target replaces the hash-side zero-query Ligero charge by the
certified flat `2^-125` terminal-pair envelope. For `N > 0`, it uses the
six-step graded extraction-first compiler and proves that the enlarged-radius
extraction-failure event is contained in its old-radius failure event. The exact arithmetic
holds through `tA ≤ 2^116`; beyond that point the T-security right-hand side is
at least one. Its false-statement corollaries count accepting transcripts whose
public inputs admit no satisfying hash/signature witness pair with equal common
values. Both results retain the separate-MAC row premises for every satisfying
circuit assignment.

## The verifier and the claim chain

The modelled verifier is `zk_common.h` / `ZkVerifier::verify`:

- sumcheck round polynomials are padded, and `p(1) := claim − p(0)` is substituted, so there is
  no cleartext round check;
- each layer emits its `finalize` row and triple, and the input row is emitted at `alpha_in`;
- `begin_circuit` draws the output point `G`, and every layer's `beta` is a fresh challenge drawn
  in protocol order;
- the only verdict is Ligero V1's, on the system the transcript built.

The extractor reads the Merkle query trace and decodes the lift list. "Straight-line" refers to
the query trace, not to a proved running time.

**For RBR, Per-candidate doom has three branches** (`RbrZkLongfellow.ZkWrong`):

- (a) the de-padded claim is wrong at the layer's own `beta`;
- (b) an assertion two or more layers further down is violated;
- (c) the next layer's assertion vector, with the coordinates bound so far, is not identically
  zero.

This is essential for the registered circuits. The compiler gives each assert-zero gate its own
wire, and no later layer reads it (`DeadEnd`, `Isolated`). So a violated intermediate assertion
never reaches the output. It is caught at its own layer, where the incoming claim was sent
before that layer's `beta`. The proof never assumes that a false witness makes the final output
nonzero.

**Budgets.**

| slot | budget |
|---|---|
| layer pair | `2 sizeof(F)` |
| sumcheck round | 2 |
| close / input binding | 1 |
| `G` (Schwartz–Zippel, `ZkMultilinear`) | `(logv+2)/|F|` |

The list factor multiplies the field slots only. The Ligero slots are charged once for the whole
lift list: `NoDecodedSolution` is derived from "every candidate violates the built system"
(`ZkLigeroV1.noDecoded_of_noSat`), so no `hfalse` premise is needed.

The generic sumcheck charge `2/q` is necessary: a quadratic difference can have two distinct roots
and a nonzero Boolean sum, also in characteristic two (`SoundnessAudit.quadratic_two_roots`,
`X(X−a)` with `a ≠ 0, 1`). Replacing it by `1/q` because the incoming claim is false would be
unsound.

## Where the error comes from

The uncapped two-field theorem (`CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT`) proves

```text
Pr[bad] ≤ A + N·κ + 2·adaptiveNumerator(fc, tA, L + N) / 2^256

A  = core_hash + core_sig + 1/2^128
κ  = max(κ_hash, κ_sig, 1/2^128)
fc = 2·n_hash + 2·n_sig                (the verifier's Merkle-check queries)
L  = 1 + rounds_hash + rounds_sig      (all protocol slots, Ligero included)

adaptiveNumerator(fc, tA, m) = tA(tA−1)/2 + (fc + tA)(2·tA + 1) + (fc + tA)·m
```

- `A` is what every adversary pays.
- `N·κ` is transcript grinding: the worst single challenge, Ligero's combination challenge, paid
  once per hash query.
- The last term is Merkle extraction failure; its `tA²` part is the 256-bit hash's birthday bound.

For one field, omit the MAC term and the other side, use `fc = 2n`, and drop the factor 2 on the
Merkle term. For a row with candidate bound `B`, field order `q`, `nl` layers, `s` sumcheck rounds
and output dimension `logv`:

```text
core = B·[nl·(logv+2) + 2s + 1]/q + fail + arith + cover
κ    = max(B·(logv+2)/q, fail + arith, cover)
```

`fail + arith` bounds escaping Ligero combination challenges, and `cover` bounds the accepting
column queries at a doomed challenge. The separate Ligero row certificate
`epsRbr = B·(fail + arith + cover)` is more conservative than this composition.

Exponents (`error ≈ 2^-exponent`; these are not additional integer claims):

| Row | Field contribution | Ligero contribution | `core` | `κ` |
|---|---:|---:|---:|---:|
| `v7Hash1` | 116.750 | 116.601 | 115.673 | 117.081 |
| `v7Hash2` | 116.720 | 116.548 | 115.632 | 117.087 |
| `v7Hash3` | 116.711 | 116.587 | 115.648 | 117.130 |
| `v7Hash4` | 116.692 | 116.557 | 115.623 | 117.129 |
| `v7Sig` (Johnson) | 244.661 | 123.012 | 123.012 | 123.012 |
| **`v7SigHahn`** | 244.661 | **127.489** | **127.489** | **127.489** |

### Why the earlier round-by-round theorem stops at 115 bits

The hash side sets the two-field level. The signature side (`2^-123`, or `2^-127.5` with the Hahn
row) and the MAC slot (`2^-128`) change the two-field core by less than 0.01 bit. For `v7Hash1`
(GF(2^128); `nl = 17` layers, `s = 566` sumcheck rounds, `logv = 3`, candidate bound `B = 2`), the
constant term `core` builds up like this. The other three hash rows differ by under 0.05 bit.

| step | term | error | bits so far |
|---|---|---:|---:|
| one degree-2 sumcheck round | `2/q` | `2^-127` | |
| all `s = 566` rounds | `2·566/q` | `2^-117.86` | 117.86 |
| × candidate list, `B = 2` | `2·2·566/q` | `2^-116.86` | 116.86 |
| + layer pairs and `G`, input binding | `B·nl·(logv+2)/q + B/q` | `2^-120.59`, `2^-127` | **116.75** (field) |
| Ligero: combination challenge escapes doom (proximity-failure profile) | `fail` | `2^-117.27` | |
| Ligero: accepting column queries at a doomed challenge | `cover` | `2^-118.42` | |
| Ligero: combination challenge escapes doom (unchecked-mask arithmetic profile) | `arith` | `2^-120.08` | **116.60** (Ligero) |
| `core = field + Ligero` | | `2^-115.67` | **115.67 → 115** |

The `117.27` entry has the exact value `1694/(2^128 − 36)`: `1694 = m − 1` for the
certified `v7Hash1` row. It is only the challenge-escape summand, before `arith`, `cover`,
and all field checks. `SoundnessAudit.v7Hash1_challenge_escape_exact` and
`v7Hash1_cost_chain` check that decomposition in Lean. Substituting this one exponent
for the complete Ligero error would overstate the result.

In words:

- **The rounds cost about 10.1 bits.** That is `log₂(2·566)`, which leaves 117.9 bits.
- **The candidate list costs 1 bit.** The extractor returns every codeword within the
  list-decoding radius of the committed matrix, at most `B = 2` here, and soundness needs every
  one of them to fail. A sumcheck challenge may rescue any one of them, so each round is charged
  once per candidate. A smaller radius (`B = 1`) would make Ligero's query term far worse, about
  `2^-92` at 132 openings.
- **The per-layer slots cost 0.1 bit,** which leaves 116.75.
- **Ligero costs about 1.1 bits more in this accounting.** Its round-by-round term
  (`2^-116.6`) is about as large as the whole field term, and adding two nearly equal
  terms costs about one bit. That leaves 115.67.
- **T-security rounds down.** It needs `core ≤ 2^-λ` (and `κ ≤ 2^-λ`; here `κ = 2^-117.08`), so
  `λ = 115`.

The later extraction-first theorem handles the zero-query constant with the flat
terminal-pair bound and reaches 116 bits. Its positive-query branch uses the
graded circuit potential; the older calculation remains useful for separating
the field, Ligero, and MAC costs.

Limits of the older bound:

- **116 bits** requires a smaller zero-query Ligero charge. With no Ligero term at all,
  `core` would be the field term `2^-116.75`. Removing only `fail` gives about
  `2^-116.25`. The separate flat/graded theorem supplies the required improvement
  at zero transcript queries while the graded potential handles positive queries.
- **117 bits or more** needs the field term below `2^-117`: fewer sumcheck rounds, a single
  candidate, or a larger field. Improving Ligero alone cannot get there
  (`SoundnessAudit.hash_round_charge_exceeds_117`: the list-weighted round charge alone exceeds
  `2^-117`).

**From the exact bound to T-security.**

- `TSec.tsec_of_uncapped` turns the exact bound into `(1 + tA + N)·2^-115`. For `tA, N ≤ 2^137`
  the Merkle term is at most `tA·2^-115`; above that, the right-hand side exceeds 1 and the claim
  is trivial.
- `TSec.tsec_of_linear_slack` is a tighter conversion. Below `tA ≤ G = 2^λ` it charges the Merkle
  numerator to separate constant, `N` and `tA` coefficients; above that cutoff
  `(1+N+tA)/2^λ ≥ 1`. It does not reserve half of the transcript-query coefficient or require
  `2λ+4 ≤ 256`. Three exact slack checks certify 127 bits for `v7SigHahn`.

## Improved Ligero rows and sumcheck

The [Ligero table](../ligero/README.md) certifies V1 IOP bounds of 125 bits (hash) and 127 bits
(signature). The hash rows' Ligero term above is only `2^-116.6`. The difference is not a lost
proof step; the two numbers bound different things.

**What the Ligero table bounds.** Its numbers are *flat* bounds. Over both Ligero challenges
together — the combination challenge `α`, then the column query — they bound the probability
that a prover with a fixed commitment is accepted without a valid witness. The bound averages
over `α`: each `α` contributes its probability times the fraction of column queries the best
response passes at that `α` (the "response-uniform envelope"). An average is the right quantity
when `α` is drawn once. The local count certificates in `formal/ligero`
also give separate bounds for escape challenges and accepting column queries.

**Why the positive-query compiler does not use the flat bound directly.** In Longfellow, `α` is a hash of the
root *and the whole sumcheck transcript*. A cheating prover can obtain fresh `α` values by
changing sumcheck messages without re-committing, then concentrate its column-query attempts
on a favorable one. A flat average over `α` does not itself justify the compiler's **linear**
query factor. The earlier round-by-round composition instead needs one bound per
Ligero round, each charged once per hash query:

1. the probability that `α` escapes a *doom threshold* (`fail + arith`);
2. for a doomed `α`, the fraction of column queries that pass (`cover`).

**Why that compiler costs bits.** The threshold is a single cut. An `α` above it is charged as a total
loss, even though the prover would still have to pass the column test at that `α`. That is the
gap between `2^-116.6` and `2^-125` on the hash side. The 116-bit theorem uses the
flat envelope at zero transcript queries, where the commitment fixes a single
challenge path, and the six-step graded potential at positive query counts. A response-
counting analysis could sharpen the positive-query coefficient further. The
signature side already reaches flat parity (127 bits) through the improvement below.

The improvement transfers the *mask certificate* and proves the round-by-round bounds anew:

1. `Ligero.V1.ligerov1_roundByRound_mask_profiled` accepts a certified `V1MaskRange`, including
   Hahn/Delsarte bounds below the Johnson threshold. The Johnson theorem remains as a
   specialisation.
2. `LigeroV1Rows.Row.arithProfile` and the ZK composition consume the row's certified mask range.
   Existing rows keep their Johnson-only values.
3. [LigeroV1RowsHahn.lean](Lfzk/LigeroV1RowsHahn.lean) uses the signature Hahn certificate at
   agreement 1665: both doom thresholds 1664, `e = 1522`, `g = 0`, candidate bound 2. Its RBR
   certificate is 126 bits. Its Ligero contribution without the outer candidate factor is about
   `2^-127.489`.
4. [CertifiedHahn.lean](Lfzk/CertifiedHahn.lean) and the new circuit headline carry this through
   to the verifier's acceptance event and uncapped queries.

**Why the hash rows stay on the Johnson profile.** `formal/ligero` has Hahn–Delsarte
certificates for all four v7 hash geometries (`HahnMask.v7Hash1..4`). The lfzk hash rows
deliberately do not use them, because under per-round accounting they would make the bound far
worse. A Hahn certificate bounds the unchecked-mask list *below* the Johnson threshold, where the
list is large. Per-round accounting charges every listed mask as an escaping combination
challenge, `arith = B·list/|F|`. The flat analysis instead weights each list by the query pass
rate at its agreement level:

| row | field | Johnson / Hahn cutoff | Hahn list | `arith` with Hahn | `arith` now (Johnson) | pass rate at the cutoff |
|---|---|---|---:|---:|---:|---:|
| `v7Sig` | `2^256` | 1703 / 1665 | `2^49.1` | `2^-205.9` | `2^-245.4` | `2^-127.5` |
| `v7Hash1` | `2^128` | 1725 / 1681 | `2^58.4` | `2^-68.6` | `2^-120.1` | `2^-128.2` |
| `v7Hash2` | `2^128` | 1773 / 1728 | `2^59.1` | `2^-67.9` | `2^-120.1` | `2^-128.0` |
| `v7Hash3` | `2^128` | 1790 / 1744 | `2^60.1` | `2^-66.9` | `2^-119.9` | `2^-128.1` |
| `v7Hash4` | `2^128` | 1835 / 1788 | `2^63.3` | `2^-63.7` | `2^-119.9` | `2^-128.0` |

- **Over P-256** a `2^49` list divided by `2^256` is negligible. So the signature row can lower
  both doom thresholds to the Hahn cutoff, which improves `cover` from `2^-123` to `2^-127.5`.
- **Over GF(2^128)** a `2^58`–`2^63` list divided by `2^128` costs about 60 bits.
- **The binding hash term is `fail`, not `arith`.** `fail` is the proximity-failure (MCA) profile's
  tail, and a mask-list bound does not touch it. `cover` is tied to `fail` through the threshold
  `ft` (`queryCover = max(ft, n−e−1, g+at)`, all equal to 1765 at `v7Hash1`), so lowering `cover`
  raises `fail`.

These Hahn list bounds cannot simply replace the Johnson row's per-round list
term. Further positive-query improvement would require:

- response-counting that charges distinct high-agreement final-query inputs
  while preserving the prover's ability to re-draw the combination challenge; or
- a stronger proximity-failure (MCA) bound in `formal/ligero`.

The separate zero-query coupling already lifts the combined integer level to
116 bits. The field-round charge still prevents 117 bits with this accounting;
see [the earlier cost breakdown](#why-the-earlier-round-by-round-theorem-stops-at-115-bits).

There is some remaining accounting slack in the older round-by-round rows. Only the initial layer
needs `(logv+2)/q`; later layer pairs need `2/q`, but the uniform pair budget charges the former to
every layer. Separating them would save `B·(nl−1)·logv/q`, but would not raise those rows above
115 integer bits. Even
removing the Ligero contribution entirely leaves the list-weighted sumcheck charge above `2^-117`,
so improved Ligero alone can reach at most 116 integer bits with this accounting
(`SoundnessAudit.hash_core_exceeds_116`, `hash_round_charge_exceeds_117`). **These are limits of
this bound, not attacks or upper bounds on the protocol's actual security.**

## The arithmetization

`Lfzk.Arith` (`ConcreteCircuit.lean`, `ConcreteCircuitBridge.lean`) builds `LayeredCircuit` from a
concrete layered quadratic circuit in the deployed format, with `prep_v`'s `beta` substitution.
It proves the three fields that used to be assumed (`Quad_affine_beta`, `V_local`, `layer_rel`),
and also:

- the input-layer identification (`toLayered_input_wMle`);
- the verifier's EQQ agreement (`toLayered_eqqAgree`);
- compiler correctness in the form that is true (`toLayered_unsat_iff`): unsatisfied ⇔ the
  outputs are nonzero, or some intermediate layer moves with its own `beta`.

`ZkArithBoundary.zkFieldDataOf` builds the whole field half of the ZK chain at the honest
`Satisfied` for circuits of one width; `ZkArithProfile.zkFieldDataP` does it at the deployed
per-layer width profile. The dependency chain of the headline is

```text
QuadCircuit + WellFormedP + Isolated + DeadEnd
  → ZkArithProfile.zkFieldDataP
  → padded sumcheck / assertion chain
  → Ligero V1 classifier on the system built by that transcript
  → Merkle extraction + message-prefix Fiat–Shamir
  → two-field MAC consistency
  → exact probability bound → T-security
```

## The end-to-end theorem, part by part

Here we help interpret one of the formalized theorems in this directory.
`CompiledZkProfileRows.v7P256Sha1_zk_circuit_tsec` formalizes the soundness statement for a one attribute mdoc circuit (the other three pairs differ
only in the hash row and its `logv`):

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

We now explain the various parts of this statement.

**The adversary and the oracles.**

- `body : TwoOracleTree Enc D (Pt2 …) C Out tA N` is the prover, one adaptive program that may
  re-commit and grind. It makes `tA` Merkle-oracle queries (inputs `Enc`, digests `D`), makes `N`
  transcript-oracle queries (inputs `Pt2`, answers `C`), and outputs a proof `Out`.
- `Pt2` is the set of hash inputs as deployed, with three kinds of point:
  - the key point (the two Merkle roots);
  - side 1's points (context, role, message prefix);
  - side 2's points, which also carry side 1's messages.

  No challenge is ever re-absorbed. Treating SHA-256's running state and the PRF expansion as a
  random oracle on these inputs is the hashing idealisation (`NizkDeployedHash`); see
  [Balanced challenge decoders](#balanced-challenge-decoders).
- The probability is over `(Fin TM → D) × (Pt2 … → C)`. `htape`, `hTM` give the Merkle tape room
  for the run (`fc + tA ≤ TM`); this is sampling bookkeeping, not a bound on the adversary.

**The two circuits** (`S₁`, `S₂ : CircuitSide …`). Side 1 is the hash circuit (output dimension
3); side 2 is the signature circuit (8). A `CircuitSide` bundles:

- **The circuit:** `c`, its layer count `hnl`, and `hwf` (`WellFormedP` at the row's width
  profile), `hiso` (`Isolated`) and `hde` (`DeadEnd`). All three are decidable and checked on the
  registered v7 circuits by `inspect_v7_assertions.py`. That `QuadCircuit` is the artifact's bytes
  is not proved; the Lean side takes the circuit as data.
- **The public input:** `pubIn av x`, at the MAC key share and the public data.
- **The verifier's code:** `Vc`, with `hV : CodeAgreesP` and `hst0`, the transliteration of
  `zk_common.h`:
  - its next points are the bound list's interleaved even and odd coordinates;
  - its layer coefficient is `bind_gh_all` at the layer's own `beta`;
  - its input row is the `alpha_in`-combination of the two points' `EQ` vectors, with the public
    part folded in;
  - `begin_circuit` puts both points at `G`;
  - `nlin`/`nt` fit (`hnlin`, `hnt`).
- **The Ligero layout:** the placement `pl` of the built system in the tableau, the Reed–Solomon
  domain `dom`, and how a message carries Ligero's response (`respOf`).
- **Exact decoder balance:** `kinit … kq`, `hbal…`, `hk…`. Each challenge decoder hits every value
  equally often.
- **The field size:** `hF : |F| = fieldSize`.

**Reading the proof.** `rootOf₁`, `rootOf₂`, `avOf`, `pubOf`, `msgOf₁`, `msgOf₂`, `claimOf₁` and
`claimOf₂` say where the roots, the MAC key share, the public data, the round messages and the
Merkle openings sit in the proof. `codec₁`, `codec₂` encode a Merkle leaf as nonce ‖ column.
`hD`: digests have 256 bits.

**The MAC.**

- `aP`, `decode`, `kmac`, `hbal`, `hmac`, `hFmac`: the MAC key share is decoded from the key
  point's answer, balanced, over a field of `2^128` elements.
- `keyB`, `tagOf`, `common₁`, `common₂`: the proof's key blocks and tags, and how a witness
  carries its common value.
- `hrow₁`, `hrow₂`: if side `k` accepts and `a` is a good witness, the MAC of `a`'s common value
  is the proof's tag. In this original form both sides use the shared `aP` and `keyB`. The
  `_sepMac` form (`CompiledZkProfileSepMac.lean`) replaces `keyB` by `share₁ share₂ :
  witness → Fin nblk → Fmac`. Its premise is `shiftTag (aP κ + decode av) (share_k a) (common_k a)
  = tagOf proof`, that is `tag_j = (av + share_{k,j})·msg_j`, which is what each v7 circuit
  asserts. See [Two-field MAC constraints](#two-field-mac-constraints).

**The event.**

- `S₁.toSide.acceptsDH …`, `S₂.toSide.acceptsDH …`: each side's deployed zero-knowledge verifier
  accepts. Its transcript, at its slice of the challenges, builds a Ligero system, and the
  Merkle-compiled V1 check accepts the proof's response on it.
- `challenges ⟨0⟩ = avOf proof`: the key share in the proof is the oracle's answer at the key
  point.
- `¬ ∃ a₁ a₂, Good … a₁ ∧ Good … a₂ ∧ common₁ a₁ = common₂ a₂`: extraction fails. No hash-side and
  signature-side good witnesses agree on the common value.

# Zero knowledge

## Query-bounded zero knowledge, explicit simulator

`CompiledLongfellowZk.compiled_longfellow_zk` and `CompiledLongfellowZkTwoField.twofield_zk`. For
every valid witness, the real proof is `ε`-close to a simulation that reads no witness. This holds
against every distinguisher that sees the proof and both challenge oracles in full and makes `f`
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
by a bijection of the prover's randomness. Per side,

```text
ε(n, d, f) = (4n² + 2·d·f)/2^256 + (2n−1)(2n−2)/2^256
```

with `n` columns, `d = n − 132` of them unopened. That is **≤ 2^-128 per side and ≤ 2^-127 for the
two-field proof at `f = 2^115`** (`CompiledLongfellowZkV7.v7_twofield_zk_q115`).

What this is, and what it is not:

- **Computational at the deployed 256-bit nonces.** The bound grows with the distinguisher's
  Merkle (SHA-256) queries. The `2·d·f/2^256` term is guessing an unopened leaf's 256-bit nonce, so
  a distinguisher that can afford about `2^256/d` hash evaluations is not covered. With longer
  nonces the result becomes statistical; see the next section.
- **"Explicit" is up to Lean's representation of the code.** `linCorr` is picked with
  `Classical.choose`, exactly as the honest prover's own `C.encode` is; concretely both are
  interpolations.
- **Compiled setting only.** The simulator needs the query set before it answers, which
  programming the Ligero oracle gives. The IPCP-level theorems (`CompiledLigeroZk`,
  `FromLigeroZKV1`), where the query comes after the response, keep `formal/ligero`'s
  reference-witness simulator, which is not efficient.

## Statistical zero knowledge with 542-bit nonces

`CompiledLongfellowZkStat.compiled_longfellow_zk_stat`, `twofield_zk_stat` and
`v7_twofield_zk_stat542`. Here the distinguisher receives the Merkle oracle `H` **as a whole
function**, with the proof and both challenge oracles, so it is unbounded. For every valid witness
the real proof is `d·ε`-close to an explicit simulation (`d` unopened columns) whenever

```text
|Digest| ≤ 4 · ε² · |Nonce|
```

With 256-bit digests and **542-bit nonces**, `ε = 2^-144` per unopened leaf. The two-field proof
at the v7 geometries is then **≤ 2^-131 from its simulation**, with no query bound. At the deployed
256-bit nonces the condition forces `ε ≥ 1/2`, so this result is about a protocol with longer
nonces.

- **The simulator** (`simExpS`) is the one above, except that the unopened leaves' digests are
  fresh uniform values. The opened leaves are hashed from their columns and nonces, and the root
  and frontier digests are hashed up from there. The simulator samples `H` itself and hands it
  over; it programs only the two Ligero points.
- **The Merkle step** (`ZkMerkleStat.view_statClose`) is the only new hybrid. It replaces the
  unopened digests one leaf at a time, at `ε` each (`hyb_step`). Each step is a leftover-hash
  lemma for a uniformly random function (`leaf_statClose`): `(H, H(x(r)))`, with `r` a uniform
  nonce and `x` injective, is `ε`-close to `(H, y)` with `y` uniform. The proof is one
  Cauchy–Schwarz over the pairs `(H, y)`, with the collision count of
  `Merkle.RandomOracle.fixed_pair_card_le`.
- **What it needs:** a finite leaf-input space (fixed-width `nonce ‖ column`) and a leaf encoding
  injective in the nonce. Nonce distinctness, codec disjointness across roles and a digest-birthday
  term are unnecessary, so `(4n² + …)/|Salt|` and `(2n−1)(2n−2)/|Digest|` disappear.
- **The other hybrids are unchanged:** programming the Ligero points, the explicit V1 response
  and the pad.

## Witness indistinguishability

At 256-bit nonces, the simulation bound above limits the number of Merkle-oracle
queries. The separate 542-bit-nonce theorem gives statistical zero knowledge
even when the distinguisher receives the entire oracle. Witness
indistinguishability compares two real proofs and is available under the
corresponding simulation hypotheses.

`CompiledLongfellowZk.compiled_longfellow_wi` and `CompiledLongfellowZkTwoField.twofield_wi`
compare honest proofs from two valid witnesses for the same statement; in the two-field form the
hidden common value may differ too. WI compares two real distributions, each `ε`-close to the same
simulation, so it pays **twice** the simulation bound:

| At `f = 2^115`, 256-bit nonces | One side | Two fields |
|---|---:|---:|
| Real → simulation | ≤ `2^-128` | ≤ `2^-127` |
| Witness indistinguishability | **≤ `2^-127`** | **≤ `2^-126`** |

`v7_twofield_zk_q115`'s `2^-127` must not be quoted as the two-witness WI bound.

## The privacy model, and its gaps

- **The model.** A programmable random oracle and a single session. The statement and witness are
  fixed before the distinguisher queries, and the distinguisher queries after receiving the proof.
- **Premises.** An injective codec (`Cod.Inj`), and causality of the honest prover
  (`CausalFS.causal`) at the abstract `ZkSetup`.
- **Independent oracles.** The two trees are separate Merkle oracles (`ZkTwoTape`), independent
  of the transcript oracle. Deployed, all are SHA-256, with no domain separation between the
  trees. This gap is distinct from the soundness theorem's shared Merkle oracle; the privacy
  theorem does not prove that the replacement preserves its bound.
- **The v7 MAC formula.** The v7 formula `tag = (a + share)·msg` is always zero at a zero
  message block, so its tags reveal which blocks are zero. This is a property of the v7 MAC, not
  of the proof. `CompiledLongfellowZkV7Mac` proves the corresponding statements by reduction to
  the additive-MAC theorem: `shareEquiv` multiplies each nonzero block's share by the message,
  which turns v7 tags into additive tags.
  - `twofield_zk_v7`: the same `ε`, against a simulator that also receives the zero pattern
    `fun j => msg j = 0` and nothing else about the witness.
  - `twofield_zk_v7_nonzero`: if every message block is nonzero, the same `ε` against the
    unchanged simulator.
  - `twofield_wi_v7`: WI at `2ε` between messages with the same zero pattern.
  - Numerals: `v7mac_twofield_zk_q115` (`2^-127`), `v7mac_twofield_zk_stat542` (`2^-131`).

  The six blocks are the 128-bit halves of `issuer_sig_e`, a SHA-256 digest, and of the device
  key's coordinates. An honest block is zero with probability about `2^-128` each. Valid points
  and digests with a zero half do exist, so the nonzero form is not unconditional.

# Assumptions and deployment boundary

| Boundary | What is checked or assumed |
|---|---|
| Circuit arithmetic | `ConcreteCircuit*` and `ZkArithProfile` construct the honest values and boundary lemmas, including variable layer widths. `Satisfied` checks the outputs and the assert-zero constraints. |
| Registered artifacts | Rust inspectors check `WellFormedP`, `Isolated`, `DeadEnd` and the geometry on the registered files. Their identification with the Lean `QuadCircuit` data is outside Lean. |
| Verifier correspondence | `CodeAgreesP`, the initial points, the message readers, the tableau placement and the sizes are premises. Equivalence to `zk_common.h` / the deployed verifier is not proved from source or machine code. |
| Commitments | The modelled opening check and the V1 policy are composed formally. The byte encoding, leaf-as-column and root-as-context correspondences remain deployment obligations. |
| Challenge sampling | Each fresh transcript-oracle answer is an independent uniform ideal coin. Exact decoder balance is assumed for the joint initial tuples, field pairs and elements, Ligero combinations, fixed-size query sets, and the MAC challenge. [IdealSampler.lean](Lfzk/IdealSampler.lean) exhibits a common abstract coin alphabet and exactly balanced decoders. Correspondence to the deployed SHA-256/AES sampler is not proved. |
| Hash model | A Merkle random oracle and an independent transcript oracle on context, role and message prefix. No challenge is re-absorbed. The running SHA-256 state and the AES expansion are idealised by this typed oracle. |
| Two-field MAC | In the `_sepMac` / `_sepBlind` headlines, `hrow₁`, `hrow₂` say each circuit enforces its own MAC equation on its own private witness (v7: `(av + share)·msg`; v8: `av·msg + blind`) and the public tags, as Rust does. That each circuit asserts exactly this equation on its bit-packed common value is a circuit fact, assumed. `aP` is an optional public shift, `0` as deployed. |
| Extractor | The failure event quantifies over a finite lift list, at most two candidates here. Efficient list decoding and a polynomial-time witness-selection algorithm are not established. |

## Verifier correspondence

The theorem is about a Lean verifier. Applying it to Rust needs a proof that whenever Rust
accepts, the modelled verifier accepts the corresponding statement and proof, with the same
challenge distribution. Full equivalence is unnecessary for soundness; this one-way implication
suffices and would replace the correspondence premises.

Two ways to build that connection are a verified translation of the Rust verifier, or generating
the verifier from a verified executable definition. Importing the circuit artifacts with a proved
checker would discharge the circuit-data part only; it would not verify parsing, transcript
handling, field operations or the verifier's control flow. The artifact inspectors are useful
checks, but they are not that proof, and more theorems inside the abstract model cannot close this
gap.

## Ideal challenge sampler

The soundness theorem assumes each fresh transcript-oracle answer is an independent uniform
element of an abstract finite coin alphabet `C`. The verifier's deterministic decoders must
map this coin to uniform values at each role: a **joint** initial-point tuple, a field pair,
an individual field element, a Ligero challenge, a fixed-size query set, or the MAC key.
Uniformity of individual coordinates alone does not imply joint uniformity. In Lean the
premise is an upper bound on every decoder fiber together with `k · |target| ≤ |C|`; for a
nonempty target these inequalities force every fiber to have the same size. The independent
random-oracle outputs supply freshness even when the prover adaptively chooses its transcript.

This assumption is satisfiable as an abstract model. [IdealSampler.lean](Lfzk/IdealSampler.lean)
uses the product of the two initial-tuple spaces, both sides' challenge and query spaces,
both field-pair spaces, and the MAC field. Coordinate projections are exactly balanced for
all eleven decoder roles at once, by the existing `ExactDecoder.self`, `.fst`, and `.snd`
constructions. This proves consistency of the sampling premises, not existence of a complete
deployed verifier or circuit satisfying every other premise.

The abstract coin is not identified with one fixed 256-bit digest. The Rust transcript's
SHA-256/AES expansion and rejection samplers are outside this ideal-sampler assumption;
relating their output distribution to the ideal model remains a separate correspondence task.
`SoundnessAudit.no_256bit_init_decoder` shows why a single 256-bit coin cannot be used as the
joint initial tuple on the hash side.

## Two-field MAC constraints

Rust supplies the **same** `proof.macs` and challenge `av_val` as public inputs to both circuits
([verifier.rs](../../rust/applications/mdoc_zk/runtime/src/verifier.rs)), and both circuits
assert the MAC equations. Each circuit has its own private MAC witness. The formula depends on the
circuit version, through the gate `version >= 8` in `push_macs`
([mac.rs:32](../../rust/applications/mdoc_zk/runtime/src/mac.rs)). Per 128-bit message block, in
GF(2^128):

| version | formula | source | hiding |
|---|---|---|---|
| **v8 and later** | `tag = a_v·msg + a_p` | `push_modern_macs` → `compute_mac` ([concrete.rs:41](../../rust/circuits/mac/src/concrete.rs)) | perfect: the tag is the blind translated |
| **v7 and earlier** (the deployed registry entries) | `tag = (a_v + a_p)·msg` | `push_legacy_macs` ([mac.rs:83–86](../../rust/applications/mdoc_zk/runtime/src/mac.rs)); the C++ circuit asserts the same ([mac_circuit.h:105](../../lib/circuits/mac/mac_circuit.h)) | only for `msg ≠ 0`: the tag is 0 at a zero block |

The C++ circuit says so itself ([mac_circuit.h:47](../../lib/circuits/mac/mac_circuit.h)): the
optimisation computes `a·x` instead of `a·x + b`, is "hiding whenever x is non-zero", and adds "a
small error to the zero-knowledge analysis". For soundness both formulas behave the same:
`(a_v + a_p)·msg = a_v·msg + a_p·msg` is affine in `a_v`, with the offset `a_p·msg` fixed by the
committed witness.

The honest prover uses equal blinds or shares; a malicious prover need not. The older
shared-blind composition assumes they are equal, through its shared `keyB`, and argues that
unequal messages force `a = 0`. That argument fails for separate blinds: `a = 1`,
`(message_hash, blind_hash) = (0, 0)` and `(message_sig, blind_sig) = (1, −1)` give equal tags
with unequal messages (`SoundnessAudit.separate_blinds_collision`).

The argument for separate blinds uses **commitment before challenge**. For fixed unequal messages
and fixed blinds, tag equality gives `a·(message_hash − message_sig) = blind_sig − blind_hash`,
which determines at most one `a`:

- `Mac.macTag_collision_card_le_one` proves this for v8, `2^-128` per fixed pair;
- `Mac.shiftedMultiplier_collision_card_le_one` proves it for v7, where the offset
  `share·message` is fixed with the candidate witness.

**This is composed for the modeled verifier** (`CompiledZkProfileSepMac.lean`, generic layers in
`MacSep`, `NizkZkDeployedHashSepMac`):

- **Candidates are fixed before `a`.** Each side's candidate list is the lift list of its
  extracted matrix, a function of its root and cut trace only (`CircuitSide.cands`,
  `cands_card_le`, `good_mem_cands`). The key point's answer is drawn after both commitments.
- **The key slot's bad event** (`MacSep.SepMacBad`): some pair of candidates with different
  common values has equal tags at the multiplier. The tags are chosen after `a`, but both
  equations share the same tag, so it drops out. `sepMacBad_card_le` bounds it by `B₁·B₂`
  multipliers.
- **The bound.** `twofield_zk_deployed_ratio_leT_sep` is the exact bound with the MAC term
  `B₁B₂/|Fmac|` in place of `1/|Fmac|`, both in the constant and in `κ`. At the v7 pairs that is
  `4/2^128`. It stays below the per-query `κ` (`v7P256ShaK_sep_mac_le_coeff`), so `κ` is unchanged
  (`_sep_coeff_eq`) and the constant grows by `3/2^128`.
- **Headlines.** `v7P256Sha{1..4}_zk_circuit_tsec_sepMac` (v7 formula) and `…_sepBlind` (v8
  formula), both at `(1 + N + tA)/2^115`.


# File map

| Layer | Files |
|---|---|
| Circuit and constraint model | `Types`, `WPoly`, `Builder`, `Circuit`, `Rounds`, `Layers`, `LigeroRows`, `LigeroSystem`, `Encode`, `ZkLayers`, `ZkHiding`, `ZkSim` |
| Concrete arithmetization | `ConcreteCircuit`, `ConcreteCircuitBridge`, `ZkArithInit`, `ZkArithBoundary`, `ZkArithProfile` (deployed width profile) |
| Padded sumcheck and pending assertions | `RbrZkLongfellow`, `RbrZkSplit`, `ZkMultilinear` |
| Ligero RBR and rows | `LigeroRbr`, `LigeroV1Rbr`, `LigeroV1Rows`, `LigeroV1RowsV7`, `LigeroV1RowsHahn`, `ZkLigeroV1`, `CertifiedV7`, `CertifiedHahn` |
| Fiat–Shamir and Merkle composition | `NizkZk`, `NizkZkTwoField`, `NizkZkDeployedHash`, `CompiledZk`, `CompiledZkTwoField`, `CompiledZkRows`, `CompiledZkTwoFieldRows`, `CompiledZkDeployedHash`, `CompiledZkDeployedHashRows`, `../bcs/Bcs/TotalOracle`, `TotalOracleCommit` |
| End-to-end circuit headlines | `CompiledZkProfileRows`, `CompiledZkProfileHahn`, `TSec`, `SoundnessAudit` |
| Two-field MAC | `Mac`, `MacSep`, `TwoField`, `TwoFieldZk`, `NizkZkDeployedHashSepMac`, `TwoFieldSepMacRows`, `CompiledZkProfileSepMac`, `CompiledLongfellowZkV7Mac` |
| Privacy | `LigeroZk/*`, `../merkle/Merkle/{Hiding,CommitCollision}`, `FromLigeroZKV1`, `ZkFiatShamir`, `ZkMerkle`, `ZkMerkleStat`, `ZkProgram`, `ZkLongfellow`, `CompiledLigeroZk`, `ZkAdaptiveV1`, `CompiledLongfellowZk`, `CompiledLongfellowZkTwoField`, `CompiledLongfellowZkStat`, `CompiledLongfellowZkV7`, `ZkFrontendOfSetup`, `ZkTwoTape` |
| Superseded clear-verifier chain | `Rbr*` (non-`Zk`), `Nizk*` (non-`Zk`), `CertifiedV1`, `CompiledLongfellow*` (non-`Zk`), `TwoField*` rows, `CompiledV7`, `NizkDeployedHash*`, `*S` |
| Scripts | `audit_axioms.py`, `soundness_report.py`, `v7_rows.py`, `rbr_v1_rows.py`, `inspect_v7_assertions.{py,rs}`, `inspect_v7_circuit_profile.{py,rs}` → `v7-circuit-profiles.json` |
