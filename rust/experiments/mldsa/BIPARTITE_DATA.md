# Per-layer bipartite experiment: complete size data

2026-09-11. See [method, conclusions, and caveats](BIPARTITE_REPORT.md).

All sizes are bytes. LFC2 means the existing **segmented** encoding, not the one-index-per-term representation. Complete files include metadata, coefficients, and circuit IDs. No external zstd dictionary is used.

Raw LFC1 size is unchanged within each fixture: signature 3,134,392; hash 60,467,613; MLDSA 78,996,522. `input_first_` means globally distinct vertex IDs (inputs before outputs); no such prefix means mixed numeric layer-local IDs. `packed_` additionally packs output wires forward. All other policies change traversal only. `global_morton` restores a global term sort after packing; `morton` means Morton traversal **inside each component**.

| Circuit | Policy | LFC1 zstd-16 | LFC1 zstd-22 | LFC2 raw | LFC2 zstd-16 | LFC2 zstd-22 | Global deltas |
|---|---|---:|---:|---:|---:|---:|---:|
| signature | Original | 93,955 | 89,077 | 273,192 | 125,279 | 117,854 | 14,192 |
| signature | `input_first_with_one_morton` | 87,766 | 83,010 | 268,590 | 122,017 | 113,785 | 14,646 |
| signature | `input_first_without_one_morton` | 204,432 | 196,989 | 586,441 | 306,103 | 267,908 | 49,081 |
| signature | `input_first_packed_with_one_morton` | 83,903 | 80,261 | 276,450 | 121,554 | 111,336 | 15,148 |
| signature | `input_first_packed_without_one_morton` | 140,655 | 132,333 | 506,658 | 244,230 | 195,357 | 43,487 |
| signature | `with_one_morton` | 90,890 | 86,164 | 273,965 | 127,027 | 117,011 | 15,473 |
| signature | `with_one_h1_h0_g` | 137,879 | 133,825 | 518,215 | 241,096 | 188,144 | 42,213 |
| signature | `with_one_h0_h1_g` | 115,858 | 113,757 | 382,360 | 187,466 | 158,856 | 26,517 |
| signature | `without_one_morton` | 194,262 | 186,192 | 563,747 | 284,520 | 248,107 | 47,443 |
| signature | `without_one_h1_h0_g` | 210,711 | 204,342 | 660,588 | 339,005 | 276,050 | 59,619 |
| signature | `without_one_h0_h1_g` | 216,645 | 205,225 | 659,623 | 336,875 | 282,686 | 55,741 |
| signature | `packed_with_one_global_morton` | 109,206 | 104,204 | 296,801 | 145,206 | 135,622 | 17,370 |
| signature | `packed_with_one_morton` | 108,900 | 103,598 | 320,380 | 154,140 | 141,042 | 20,655 |
| signature | `packed_without_one_global_morton` | 202,541 | 196,113 | 460,448 | 259,241 | 242,698 | 35,663 |
| signature | `packed_without_one_morton` | 267,769 | 262,110 | 664,577 | 373,779 | 326,214 | 61,797 |
| hash | Original | 133,225 | 117,606 | 598,054 | 173,602 | 161,848 | 18,449 |
| hash | `input_first_with_one_morton` | 125,581 | 111,208 | 574,988 | 169,238 | 154,628 | 18,994 |
| hash | `input_first_without_one_morton` | 484,348 | 433,749 | 2,446,832 | 931,178 | 695,419 | 200,243 |
| hash | `input_first_packed_with_one_morton` | 105,136 | 92,854 | 555,470 | 153,281 | 138,850 | 19,913 |
| hash | `input_first_packed_without_one_morton` | 462,629 | 416,348 | 2,435,713 | 853,179 | 701,012 | 193,233 |
| hash | `with_one_morton` | 126,746 | 112,374 | 575,686 | 169,899 | 155,244 | 18,991 |
| hash | `with_one_h1_h0_g` | 1,034,239 | 639,064 | 8,618,116 | 2,166,819 | 1,564,389 | 608,797 |
| hash | `with_one_h0_h1_g` | 107,103 | 103,128 | 611,562 | 180,692 | 147,985 | 24,338 |
| hash | `without_one_morton` | 489,761 | 447,998 | 2,449,602 | 900,012 | 726,151 | 197,205 |
| hash | `without_one_h1_h0_g` | 1,283,983 | 897,797 | 9,921,937 | 2,744,877 | 2,075,224 | 728,070 |
| hash | `without_one_h0_h1_g` | 446,443 | 416,106 | 2,354,652 | 859,367 | 682,992 | 193,009 |
| hash | `packed_with_one_global_morton` | 137,843 | 122,764 | 642,104 | 187,691 | 175,668 | 23,305 |
| hash | `packed_with_one_morton` | 139,651 | 125,699 | 636,043 | 204,253 | 177,793 | 26,627 |
| hash | `packed_without_one_global_morton` | 159,075 | 142,491 | 676,377 | 209,706 | 195,867 | 21,498 |
| hash | `packed_without_one_morton` | 482,076 | 439,511 | 2,443,416 | 893,748 | 720,370 | 195,429 |
| mldsa | Original | 1,768,703 | 1,606,804 | 4,830,797 | 2,197,840 | 2,091,823 | 174,923 |
| mldsa | `input_first_with_one_morton` | 1,343,649 | 1,221,104 | 4,086,917 | 1,790,232 | 1,695,604 | 159,372 |
| mldsa | `input_first_without_one_morton` | 3,462,811 | 3,334,439 | 14,723,044 | 5,104,365 | 4,720,469 | 1,070,184 |
| mldsa | `input_first_packed_with_one_morton` | 1,235,647 | 1,113,704 | 4,181,523 | 1,829,476 | 1,709,103 | 166,012 |
| mldsa | `input_first_packed_without_one_morton` | 3,157,942 | 2,586,395 | 13,781,397 | 4,332,415 | 3,940,073 | 840,846 |
| mldsa | `with_one_morton` | 1,382,662 | 1,261,893 | 4,162,315 | 1,845,061 | 1,744,121 | 167,181 |
| mldsa | `with_one_h1_h0_g` | 1,142,898 | 978,803 | 5,291,440 | 2,058,272 | 1,645,101 | 373,285 |
| mldsa | `with_one_h0_h1_g` | 3,141,691 | 2,862,706 | 13,362,216 | 5,350,640 | 4,308,956 | 987,697 |
| mldsa | `without_one_morton` | 3,665,778 | 3,285,815 | 14,661,217 | 5,270,710 | 4,758,033 | 1,015,933 |
| mldsa | `without_one_h1_h0_g` | 3,587,337 | 3,306,031 | 16,373,544 | 5,616,951 | 4,919,479 | 1,199,878 |
| mldsa | `without_one_h0_h1_g` | 4,089,819 | 3,661,612 | 16,992,707 | 6,272,365 | 5,574,490 | 1,277,647 |
| mldsa | `packed_with_one_global_morton` | 1,865,804 | 1,694,732 | 5,332,377 | 2,460,184 | 2,309,331 | 236,387 |
| mldsa | `packed_with_one_morton` | 1,328,749 | 1,198,448 | 4,299,062 | 1,902,501 | 1,777,553 | 177,877 |
| mldsa | `packed_without_one_global_morton` | 2,885,789 | 2,666,905 | 7,291,997 | 3,875,459 | 3,659,319 | 351,348 |
| mldsa | `packed_without_one_morton` | 3,978,290 | 3,662,171 | 14,906,788 | 5,949,674 | 5,403,124 | 990,559 |

Global delta counts include coefficient indices and deduplicate across all layers. Actual LFC2 dictionaries are per-layer and their summed counts are larger. Memory estimates and decoding observations are retained in the logs linked from the report.
