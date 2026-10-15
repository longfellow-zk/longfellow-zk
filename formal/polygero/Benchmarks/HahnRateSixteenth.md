# Nonrecursive rate-1/16 benchmark

Geometry: `|F| = 2^128`, encoded length `n = 8192`, RS dimension `k = r + w = 512`, `s = 64`, and `t = 50,...,70`. The table reports `-log₂(error)` for the paper profile theorem and the fixed-weight Hahn/Delsarte refinement. The decimal columns are numerical evaluations of exact rational errors; the integer columns are Lean-certified floors, meaning `2^-(b+1) < error ≤ 2^-b`.

| t | Paper bits (approx.) | Hahn bits (approx.) | Paper certified floor | Hahn certified floor | Hahn cutoff |
|---:|---:|---:|---:|---:|---:|
| 50 | 93.3201 | 97.0722 | 93 | 97 | 2152 |
| 51 | 95.2147 | 99.0265 | 95 | 99 | 2152 |
| 52 | 97.1103 | 100.9814 | 97 | 100 | 2152 |
| 53 | 99.0071 | 102.9367 | 99 | 102 | 2152 |
| 54 | 100.9051 | 104.8925 | 100 | 104 | 2152 |
| 55 | 102.8041 | 107.2985 | 102 | 107 | 2140 |
| 56 | 104.7044 | 109.2636 | 104 | 109 | 2140 |
| 57 | 106.6057 | 111.2292 | 106 | 111 | 2140 |
| 58 | 108.5083 | 113.1954 | 108 | 113 | 2140 |
| 59 | 110.4119 | 115.1619 | 110 | 115 | 2140 |
| 60 | 112.3168 | 117.5809 | 112 | 117 | 2129 |
| 61 | 114.2227 | 119.5531 | 114 | 119 | 2129 |
| 62 | 116.1297 | 121.5170 | 116 | 121 | 2129 |
| 63 | 118.0375 | 123.4468 | 118 | 123 | 2129 |
| 64 | 119.9450 | 125.2537 | 119 | 125 | 2129 |
| 65 | 121.8481 | 126.9556 | 121 | 126 | 2119 |
| 66 | 123.7321 | 127.6570 | 123 | 127 | 2119 |
| 67 | 125.5451 | 127.9054 | 125 | 127 | 2119 |
| 68 | 127.0940 | 127.9755 | 127 | 127 | 2119 |
| 69 | 127.9140 | 127.9938 | 127 | 127 | 2119 |
| 70 | 127.9938 | 127.9989 | 127 | 127 | 2109 |

The Lean module [HahnRateSixteenth.lean](HahnRateSixteenth.lean) checks all 21 exact rational inequalities, the paper theorem’s least discrete cutoffs, the Hahn threshold condition with incidence index one, and coverage of every integer `t` in the range. Five integer Hahn polynomial certificates in [HahnRateSixteenth/](HahnRateSixteenth/) are checked against every realizable pairwise overlap and supply the exact list-size bounds. `certifiedRows` constructs both the paper `ProfileCertificate` and the Hahn `HahnSystemCertificate` for any Polygero instance with this geometry. `certifiedTerminalFailure` and `certifiedTerminalSoundness` then apply the existing nonrecursive wire extraction and soundness theorems; the latter is a corollary of extraction.

Each table row selects one certificate record, which supplies its cutoff,
list-size bound, and polynomial coefficients together.

The Hahn column takes the active-set cutoff `a` shown in the table and uses `θ = choose(a-1,t)/choose(n,t)`. Its list-size threshold condition is checked exactly for each row. These five certificates are a selected set of valid fixed-weight Delsarte bounds, not a proof that the optimization is globally strongest. The benchmark assumes an instance with `|F| = 2^128` and does not include recursion or Fiat–Shamir compilation.

The numerical checks use Lean's `native_decide`, as do the existing Ligero
integer certificates. Their trust base therefore includes Lean's native
reduction axiom in addition to the ordinary proof kernel. The decimal values
are display approximations; the exact certified claims are the rational
inequalities and integer-bit floors in the Lean module.
