# Pair segmentation: exact byte measurements

All sizes are bytes, not KiB. Each cell is **raw / zstd-22**. mdoc is the actual joint LFA2 archive.

| Policy | MLDSA44 | MLDSA65 | mdoc archive |
|---|---:|---:|---:|
| `reuse` | 1,642,397 / 367,947 | 1,805,553 / 377,432 | 789,028 / 156,667 |
| `reuse_cdcstored_64` | 1,841,003 / 362,947 | 2,037,884 / 368,416 | 764,931 / 149,386 |
| `reuse_cdc_128` | 2,030,895 / 363,275 | 2,205,120 / 369,259 | 1,009,975 / 146,340 |
| `pair_delta_repair_128` | 1,201,967 / 377,214 | 1,234,532 / 384,222 | 495,345 / 158,465 |
| `pair_delta_repair_512_prune` | 942,255 / 371,594 | 997,577 / 375,943 | 421,936 / 159,472 |
| `pair_delta_gain_32` | 1,374,881 / 411,552 | 1,551,994 / 417,324 | 676,437 / 169,323 |
| `pair_delta_aligned_128` | 2,649,993 / 472,194 | 2,736,695 / 479,690 | 1,031,560 / 226,497 |
| `pair_lz78_128` | 12,561,352 / 2,745,408 | 15,285,208 / 3,248,209 | 7,236,351 / 859,883 |
| `pair_cdc_repair_8192_prune` | 2,207,291 / 382,501 | 2,329,327 / 386,096 | 1,050,401 / 145,818 |
| `pair_stock_repair_8192` | 4,028,635 / 377,730 | 5,950,044 / 403,368 | 1,556,359 / 146,111 |
| `reuse_pair_stock_repair_8192` | 2,132,755 / 363,214 | 2,376,485 / 370,060 | 1,553,788 / 146,032 |
| `reuse_pair_stock_repair_65536` | 2,306,201 / 363,029 | 2,630,911 / 369,092 | 2,485,610 / 146,369 |
| `dictsuffix@reuse_cdc_128` | 2,032,118 / 351,542 | 2,206,603 / 358,360 | 1,022,504 / 150,983 |
| `dictbucketsuffix@reuse_cdc_128` | 2,030,895 / 351,999 | 2,205,120 / 358,593 | 1,009,975 / 151,234 |
| `extractboth8@reuse_cdc_128` | 1,653,777 / 360,493 | 1,832,319 / 369,191 | 801,489 / 149,350 |
| `dictbucketsuffix@extractprefix8@reuse_cdc_128` | 1,853,855 / 350,419 | 2,019,758 / 357,407 | 925,594 / 152,493 |
| `dictbucketsuffix@extractprefix32@reuse_cdc_128` | 1,856,648 / 349,727 | 2,021,330 / 359,537 | 923,922 / 152,005 |
| `dictbucketsuffix@extractprefix128@reuse_cdc_128` | 1,874,970 / 352,705 | 2,041,745 / 356,269 | 937,816 / 151,807 |
| `dictbucketsuffix@extractboth8@reuse_cdc_128` | 1,653,777 / 350,637 | 1,832,319 / 358,333 | 801,489 / 153,060 |

## Per-dataset compressed minima (not one common policy)

| Dataset | Policy | Raw bytes | zstd-16 | zstd-22 |
|---|---|---:|---:|---:|
| mldsa44 | `dictbucketsuffix@extractprefix32@reuse_cdc_128` | 1,856,648 | 385,883 | 349,727 |
| mldsa65 | `dictbucketsuffix@extractprefix128@reuse_cdc_128` | 2,041,745 | 393,294 | 356,269 |
| mdoc_sig | `extractboth32@reuse_cdc_128` | 227,756 | 54,888 | 54,514 |
| mdoc_hash2 | `pair_stock_rank_8192` | 1,211,986 | 103,001 | 91,383 |
| mdoc archive | `pair_cdc_repair_8192_prune` | 1,050,401 | 167,694 | 145,818 |

## Smallest raw circuits (not compressed winners)

| Dataset | Policy | Raw bytes | zstd-22 |
|---|---|---:|---:|
| mldsa44 | `pair_delta_repair_512_prune` | 942,255 | 371,594 |
| mldsa65 | `pair_delta_repair_512_prune` | 997,577 | 375,943 |
| mdoc_sig | `pair_delta_repair_2048_prune` | 141,365 | 60,719 |
| mdoc_hash2 | `pair_delta_rank_512_prune` | 280,277 | 102,580 |
