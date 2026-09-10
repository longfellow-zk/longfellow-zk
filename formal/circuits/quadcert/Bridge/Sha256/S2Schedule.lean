/-
# The 48 `sha256/schedule/N` assertions

Entry point for the schedule class. Importing this reaches every generated schedule module, so
`lake build` will not skip them.

## What is proved

For each `t = 16 … 63`, over the deployed artifact:

* `zval_S{t}` — the assertion's `z` wire equals `σ₀(W (t-15)) + W (t-7) + σ₁(W (t-2)) + W (t-16)`
  minus `W t`, as four separated bit-linear addend groups. This is a statement about the
  *circuit*: `tmpl_zS{t}` proves it of a 266-node template, and `coneS{t}` (one `decide +kernel`)
  transports it along the cone match.
* `allWrap4` — all 48 product assertions force `wrapPoly 4 (2^32) z = 0`, from a single edge list
  over `tnWrap4`.

Together those are the two halves of one `SHA256F.wrap_four_words` application.

* `lvBits{t}` — booleanity of all 161 template leaves, from the cone's own 160
  `(assertion, bit)` pairs. The mid layer needs no assertions: `Core/ConeXor.lean` derives it.
* `sched{t}` — **the whole thing**:

      SHA256.ofBits (bitsOf inputs (wordBits t))
        = SHA256.w32 (SHA256.sigma0 (SHA256.ofBits (bitsOf inputs (wordBits (t-15))))
            + SHA256.ofBits (bitsOf inputs (wordBits (t-7)))
            + SHA256.sigma1 (SHA256.ofBits (bitsOf inputs (wordBits (t-2))))
            + SHA256.ofBits (bitsOf inputs (wordBits (t-16))))

  which is `SHA256.sha256_soundness`'s `hsched` at step `t`. Phrased over the global `wordBits`
  table, so the 48 steps chain: step `t` speaks about the same list step `t-15` produced.

## What is not proved here

Nothing about the schedule class. What remains for SHA-256 as a whole is `hcopy` and `hinit`,
and the 128 `round_step` assertions — a different and larger class (`Ch`/`Maj` need `andW`/`notW`
bit lemmas that `SHA/Sigma.lean` does not yet provide).
-/

import quadcert.Bridge.Sha256.S2SchedA
import quadcert.Bridge.Sha256.S2SchedB
import quadcert.Bridge.Sha256.S2SchedC
import quadcert.Bridge.Sha256.S2SchedD
import quadcert.Bridge.Sha256.S2SchedE
import quadcert.Bridge.Sha256.S2SchedF
import quadcert.Bridge.Sha256.S2SchedG
import quadcert.Bridge.Sha256.S2SchedH
import quadcert.Bridge.Sha256.S2EdgesSched
import quadcert.Bridge.Sha256.S2Xor
import quadcert.Bridge.Sha256.S2Words
import quadcert.Bridge.Sha256.S2CompA
import quadcert.Bridge.Sha256.S2CompB
import quadcert.Bridge.Sha256.S2CompC
import quadcert.Bridge.Sha256.S2CompD
import quadcert.Bridge.Sha256.S2CompE
import quadcert.Bridge.Sha256.S2CompF
import quadcert.Bridge.Sha256.S2CompG
import quadcert.Bridge.Sha256.S2CompH
