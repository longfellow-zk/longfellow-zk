import os
NL = chr(10)
OUT = "/Users/abhi/Projects/longfellow-zk/formal/circuits/quadcert/Bridge/Sha256"
LETS = "ABCDEFGH"; RLETS = "ABCDEFGHIJKLMNOP"
o = []; A = o.append
A("""/-
# The deployed SHA-256 circuit computes the SHA-256 block transform

The assembly. `SHA256.sha256_soundness` states the block transform in terms of abstract
`h`, `w`, `s` and `out`; this file instantiates them with the circuit's own words — `hWord`,
`wWord`, `stateWord`, `outWord` — and discharges each of its seven hypotheses from the bridges:

| hypothesis | source |
|---|---|
| `hcopy`, `hinit`, `hshift` | `S2State`, generic in `t` |
| `hsched` | 48 x `sched t` |
| `hrnd_a` | 64 x `rndR7_t` |
| `hrnd_e` | 64 x `rndR6_t` |
| `hout` | `S2FinalComp.hout` |

`hcopy` and `hinit` are structural: `wordBits t` *is* `input_block t` below 16, and
`stateBits 0 i` *is* `hinBits i`. `hshift` needed no per-round work either -- one lemma about
`stateBits` covers all 64 rounds.

## What this theorem assumes

That the circuit's assertion nodes evaluate to zero. Those hypotheses are stated here per
family, over the generated `(assertion, bit)` tables, rather than derived from `Accepts`:
`S2Sound.assertions_zero_of_bytes` proves every asserted node is zero from the committed bytes,
but connecting it to these tables needs a membership check for each of the ~41,000 nodes the
bridges name, which is not done. That is the one remaining link between this theorem and
`bytes -> spec`.
-/

""")
for L in LETS: A(f"import quadcert.Bridge.Sha256.S2Comp{L}")
for L in RLETS: A(f"import quadcert.Bridge.Sha256.S2CRnd{L}")
A("""import quadcert.Bridge.Sha256.S2FinalComp
import SHA.Sound

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

/-- The 48 schedule cones' booleanity tables. -/
def bpSchedAt : Nat → List (Nat × Nat)""")
for t in range(16, 64): A(f"  | {t} => bpS{t}")
A("  | _ => []" + NL)
A("/-- The 64 `n = 6` round cones' booleanity tables. -/")
A("def bpR6At : Nat → List (Nat × Nat)")
for t in range(64): A(f"  | {t} => bpR6_{t}")
A("  | _ => []" + NL)
A("/-- The 64 `n = 7` round cones' booleanity tables. -/")
A("def bpR7At : Nat → List (Nat × Nat)")
for t in range(64): A(f"  | {t} => bpR7_{t}")
A("  | _ => []" + NL)
A("""variable {F : Type} [Field F]

/-- **`hsched` for every `t`.** -/
theorem schedAll [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbSched : ∀ t, 16 ≤ t → t < 64 → ∀ j, j < 160 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpSchedAt t).getD j (0, 0)).1 = 0)
    (hrSched : ∀ e, e < 48 → interpDag (raw.toDag (cnstw F)) inputs (rootOfS e) = 0) :
    ∀ t, 16 ≤ t → t < 64 → wWord inputs t
      = SHA256.w32 (SHA256.sigma1 (wWord inputs (t - 2)) + wWord inputs (t - 7)
          + SHA256.sigma0 (wWord inputs (t - 15)) + wWord inputs (t - 16)) := by
  intro t h16 h64
  match t, h16, h64 with""")
for t in range(16):
    A(f"  | {t}, hx, _ => exact absurd hx (by omega)")
for t in range(16, 64):
    A(f"  | {t}, _, _ =>")
    A(f"    simp only [wWord, show ({t} : Nat) - 2 = {t-2} from rfl, show ({t} : Nat) - 7 = {t-7} from rfl,")
    A(f"      show ({t} : Nat) - 15 = {t-15} from rfl, show ({t} : Nat) - 16 = {t-16} from rfl]")
    A(f"    rw [show SHA256.ofBits (bitsOf inputs (wordBits {t})) = _ from")
    A(f"      sched{t} inputs hin0 (hbSched {t} (by norm_num) (by norm_num)) hrSched]")
    A(f"    exact congrArg SHA256.w32 (by omega)")
A("  | (n + 64), _, hx => exact absurd hx (by omega)")
A("")
A("""/-- **`hrnd_a` for every `t`.** -/
theorem rndAAll [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbR7 : ∀ t, t < 64 → ∀ j, j < 288 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpR7At t).getD j (0, 0)).1 = 0)
    (hrR7 : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf7 e) = 0) :
    ∀ t, t < 64 → stateWord inputs (t + 1) 0 = SHA256.w32 (stateWord inputs t 7
      + SHA256.Sigma1 (stateWord inputs t 4)
      + SHA256.Ch (stateWord inputs t 4) (stateWord inputs t 5) (stateWord inputs t 6)
      + SHA256.K.getD t 0 + wWord inputs t
      + (SHA256.Sigma0 (stateWord inputs t 0)
        + SHA256.Maj (stateWord inputs t 0) (stateWord inputs t 1) (stateWord inputs t 2))) := by
  intro t ht
  match t, ht with""")
for t in range(64):
    A(f"  | {t}, _ => exact rndR7_{t} inputs hin0 (hbR7 {t} (by norm_num)) hrR7")
A("  | (n + 64), hx => exact absurd hx (by omega)")
A("")
A("""/-- **`hrnd_e` for every `t`.** -/
theorem rndEAll [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbR6 : ∀ t, t < 64 → ∀ j, j < 224 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpR6At t).getD j (0, 0)).1 = 0)
    (hrR6 : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf6 e) = 0) :
    ∀ t, t < 64 → stateWord inputs (t + 1) 4 = SHA256.w32 (stateWord inputs t 3
      + (stateWord inputs t 7 + SHA256.Sigma1 (stateWord inputs t 4)
        + SHA256.Ch (stateWord inputs t 4) (stateWord inputs t 5) (stateWord inputs t 6)
        + SHA256.K.getD t 0 + wWord inputs t)) := by
  intro t ht
  match t, ht with""")
for t in range(64):
    A(f"  | {t}, _ => exact rndR6_{t} inputs hin0 (hbR6 {t} (by norm_num)) hrR6")
A("  | (n + 64), hx => exact absurd hx (by omega)")
A("")
A("""

/-- **The deployed circuit computes `SHA256.blockFrom`.** -/
theorem sha256_block_of_circuit [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbSched : ∀ t, 16 ≤ t → t < 64 → ∀ j, j < 160 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpSchedAt t).getD j (0, 0)).1 = 0)
    (hrSched : ∀ e, e < 48 → interpDag (raw.toDag (cnstw F)) inputs (rootOfS e) = 0)
    (hbR6 : ∀ t, t < 64 → ∀ j, j < 224 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpR6At t).getD j (0, 0)).1 = 0)
    (hrR6 : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf6 e) = 0)
    (hbR7 : ∀ t, t < 64 → ∀ j, j < 288 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpR7At t).getD j (0, 0)).1 = 0)
    (hrR7 : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf7 e) = 0)
    (hbFin : ∀ i, i < 8 → ∀ j, j < 96 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpAt i).getD j (0, 0)).1 = 0)
    (hblFin : ∀ i, i < 8 → ∀ j, j < 96 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpLAt i).getD j (0, 0)).1 = 0)
    (hrFin : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    (List.range 8).map (outWord inputs)
      = SHA256.blockFrom ((List.range 8).map (hWord inputs)) (msgBlock inputs) :=
  SHA256.sha256_soundness (msgBlock inputs) (msgBlock_length inputs)
    (hWord inputs) (wWord inputs) (stateWord inputs) (outWord inputs)
    (fun t ht => hcopy inputs t ht)
    (schedAll inputs hin0 hbSched hrSched)
    (fun i _ => hinit inputs i)
    (rndAAll inputs hin0 hbR7 hrR7)
    (rndEAll inputs hin0 hbR6 hrR6)
    (fun t _ => hshift inputs t)
    (hout inputs hin0 hbFin hblFin hrFin)
""")
A("end Sha256Blk")
open(os.path.join(OUT, "S2Assemble.lean"), "w").write(NL.join(o) + NL)
print("emitted S2Assemble.lean", len(o), "lines")
