# Three-level segmentation: exact bytes

Each cell is raw / zstd-22 bytes. mdoc is a complete joint LFA2 archive.

| Policy | MLDSA44 | MLDSA65 | mdoc |
|---|---:|---:|---:|
| Flat: `reuse_cdc_128` | 2,030,895 / 363,275 | 2,205,120 / 369,259 | 1,009,975 / 146,340 |
| Flat: `dictbucketsuffix@reuse_cdc_128` | 2,030,895 / 351,999 | 2,205,120 / 358,593 | 1,009,975 / 151,234 |
| Flat: `pair_delta_repair_512_prune` | 942,255 / 371,594 | 997,577 / 375,943 | 421,936 / 159,472 |
| Three-level: `cdc/top_64_prune` | 2,027,942 / 364,979 | 2,198,978 / 372,101 | 989,780 / 147,303 |
| Three-level: `cdc/top_64_suffix` | 2,029,226 / 354,961 | 2,201,980 / 362,292 | 990,675 / 152,082 |
| Three-level: `cdc/factor_128_prune` | 821,662 / 399,224 | 859,157 / 405,844 | 438,494 / 175,843 |
| Three-level: `reuse/two_32_128_prune` | 844,809 / 400,126 | 910,189 / 403,292 | 366,057 / 164,745 |
| Three-level: `factored/top_64_prune` | 1,626,460 / 357,243 | 1,794,886 / 363,161 | 728,266 / 154,782 |
