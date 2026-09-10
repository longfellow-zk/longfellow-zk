import os, sys, pickle
SP = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, SP)
NL = chr(10)
OUT = "/Users/abhi/Projects/longfellow-zk/formal/circuits/quadcert/Bridge/Sha256"
T = pickle.load(open(os.path.join(SP, "asserttbl.pkl"), "rb")); idx = T["idx"]
sched = pickle.load(open(os.path.join(SP, "insts.pkl"), "rb"))
rnd   = pickle.load(open(os.path.join(SP, "rinsts.pkl"), "rb"))
import gen_final_bridge as G
rootS  = [d['root'] for d in sorted(sched, key=lambda d: d['t'])]
rootR6 = [d['root'] for d in sorted([d for d in rnd if d['n'] == 6], key=lambda d: d['t'])]
rootR7 = [d['root'] for d in sorted([d for d in rnd if d['n'] == 7], key=lambda d: d['t'])]
rootW  = [d['root'] for d in sorted(G.instances, key=lambda d: d['i'])]
for nm, r in (("S", rootS), ("6", rootR6), ("7", rootR7), ("W", rootW)):
    miss = [x for x in r if x not in idx]
    print(f"root{nm}: {len(r)} roots, missing from assert list: {len(miss)}")
def bisect(v, lo, hi):
    if hi - lo == 1: return str(v[lo])
    m = (lo + hi) // 2
    return f"if e < {m} then {bisect(v, lo, m)} else {bisect(v, m, hi)}"
o = []; A = o.append
A('''/-
# `bytes → SHA-256`

The four wrap-root families (184 references) and the composition: `S2Sound.assertions_zero_of_bytes`
gives every asserted node from the committed LFC3 bytes, `S2Assert` and this file cash that in for
the nine hypotheses of `sha256_block_of_circuit`.
-/

import quadcert.Bridge.Sha256.S2Assert

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk
''')
fams = [("S", rootS, "rootOfS", 48), ("R6", rootR6, "rootOf6", 64),
        ("R7", rootR7, "rootOf7", 64), ("W", rootW, "rootOfW", 8)]
for nm, r, fn, n in fams:
    A(f"/-- Flat assert index of the `{fn}` roots. -/")
    A(f"def kRoot{nm} (e : Nat) : Nat :=")
    A("  " + bisect([idx[x] for x in r], 0, n) + NL)
    A(f"theorem okRoot{nm} : (List.range {n}).all")
    A(f"    (fun e => decide (kRoot{nm} e < 6840 ∧ assertNode (kRoot{nm} e) = {fn} e)) = true := by")
    A("  decide +kernel" + NL)
A("variable {F : Type} [Field F]" + NL)
for nm, r, fn, n in fams:
    A(f"""theorem hr{nm} (inputs : Nat → F)
    (hacc : ∀ r ∈ raw.toRecs, interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0) :
    ∀ e, e < {n} → interpDag (raw.toDag (cnstw F)) inputs ({fn} e) = 0 := by
  intro e he
  have hb := okRoot{nm}
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  obtain ⟨hk, heq⟩ := hb e he
  rw [← heq]
  exact zeroFlat inputs hacc (kRoot{nm} e) hk
""")
A('''/-- **The deployed SHA-256 circuit, from the committed bytes.**

    Hypotheses: the artifact's LFC3 pages decode to `c`, and `inputs` satisfies the quad system.
    Conclusion: the eight outgoing chaining words are `SHA256.blockFrom` of the incoming ones and
    the message block, in `SHA/Spec.lean`'s vocabulary. -/
theorem sha256_block_of_bytes (c : Lfc3.DecodedCircuit)
    (hdec : Lfc3.decode Lfc3.p256 packedInput deltaTrees = .ok c)
    [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hacc : Accepts ((c.toRaw advice).toQuad (consts F)) inputs) :
    (List.range 8).map (outWord inputs)
      = SHA256.blockFrom ((List.range 8).map (hWord inputs)) (msgBlock inputs) := by
  have hz := assertions_zero_of_bytes c hdec inputs hacc
  rw [raw_from_bytes c hdec] at hz
  have hz' : ∀ r ∈ raw.toRecs,
      interpDag (raw.toDag (cnstw F)) inputs r.assertedNode = 0 := hz
  exact sha256_block_of_circuit inputs hin0
    (fun t h16 h64 j hj => hbSched inputs hz' t h16 h64 j hj)
    (hrS inputs hz')
    (fun t ht j hj => hbR6 inputs hz' t (by omega) ht j hj)
    (hrR6 inputs hz')
    (fun t ht j hj => hbR7 inputs hz' t (by omega) ht j hj)
    (hrR7 inputs hz')
    (fun i hi j hj => hbFin inputs hz' i (by omega) hi j hj)
    (fun i hi j hj => hbFinL inputs hz' i (by omega) hi j hj)
    (hrW inputs hz')

end Sha256Blk''')
open(os.path.join(OUT, "S2Bytes.lean"), "w").write(NL.join(o) + NL)
print("emitted S2Bytes.lean")
