"""Identify each injection-factor row against the word layer: which word, which bit, which form.

Reads `Bridge/Sha256Gf2/Gf2Words.lean` for the bit-node lists and reports, per cone, the addend
groups: 32 rows sharing a form and drawing on the same word(s), with the bit-index offsets that
say which rotation or shift it is.
"""
import sys, os, re
from collections import defaultdict, Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_gf2_inj as I
import gen_gf2_row as R

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WORDS = os.path.join(ROOT, "circuits", "quadcert", "Bridge", "Sha256Gf2", "Gf2Words.lean")


def read_words():
    s = open(WORDS).read()
    out = {}
    for name in ("wordBits", "hinBits", "h1Bits", "outaBits", "outeBits"):
        m = re.search(rf"def {name} : Nat → List Nat\n(.*?)\n\n", s, re.S)
        for t, body in re.findall(r"\|\s*(\d+)\s*=>\s*\[([\d,\s]+)\]", m.group(1)):
            out[(name, int(t))] = [int(x) for x in body.replace(" ", "").split(",")]
    return out


WORD = read_words()
NODE2WORD = defaultdict(list)
for (name, t), bits in WORD.items():
    for i, nd in enumerate(bits):
        NODE2WORD[nd].append((name, t, i))


def describe(o):
    b = I.build(o)
    L, M = b['L'], b['M']
    mp = b['mp']
    rows = []
    for j in range(M):
        if b['kk'][j] is not None:
            continue
        f = R.classify(b['ts'][j])
        wires = [mp[w] for w in f[1:]]
        ids = [NODE2WORD.get(w, []) for w in wires]
        rows.append((b['bit'][j], f[0], wires, ids))
    return b, rows


def group(rows):
    """Group rows by (form kind, the word each wire comes from, the bit offsets)."""
    gs = defaultdict(list)
    for (p, kind, wires, ids) in rows:
        sig = []
        for w, cand in zip(wires, ids):
            if not cand:
                sig.append(("?", w))
                continue
            # prefer a candidate whose bit index is a fixed offset from the row's bit position
            sig.append(tuple(sorted({(n, t, (i - p) % 32) for (n, t, i) in cand})))
        # `xor3` and `maj` are symmetric in their wires, so the compiler's per-bit wire order is
        # presentational; `ch` is not (the first wire is the selector).
        if kind in ('xor2', 'xor3'):
            # σ₀/σ₁ mix arities: the `≫n` leg vanishes at the top n bits, giving n two-leg rows
            # and 32−n three-leg ones.  They are one addend, so key on the rotated word alone and
            # collect the offsets that actually occur.
            bases = sorted({(n, t) for sg in sig if sg and sg[0] != "?" for (n, t, _) in sg})
            offs = tuple(sorted({off for sg in sig if sg and sg[0] != "?"
                                 for (_, _, off) in sorted(sg)[:1]}))
            gs[("xor", tuple(bases), offs)].append(p)
        else:
            sig = tuple(sorted(sig)) if kind == 'maj' else tuple(sig)
            gs[(kind, sig)].append(p)
    return gs


if __name__ == "__main__":
    for o in [int(x) for x in sys.argv[1:]]:
        b, rows = describe(o)
        print(f"\n=== cone {o}: {b['M']} rows, {len(rows)} factors ===")
        gs = group(rows)
        # collapse: report each group's kind, size, and the (word, offset) it resolves to
        for key, ps in sorted(gs.items(), key=lambda kv: -len(kv[1])):
            if key[0] == "xor":
                _, bases, offs = key
                bb = "+".join(f"{n}[{t}]" for (n, t) in bases)
                print(f"  {len(ps):3} rows  xor    bits {min(ps)}..{max(ps)}  {bb} @{list(offs)}")
                continue
            kind, sig = key
            if len(ps) < 4:
                continue
            desc = []
            for s in sig:
                if s and s[0] == "?":
                    desc.append(f"node{s[1]}")
                else:
                    opts = {(n, t, off) for (n, t, off) in s}
                    desc.append("|".join(f"{n}[{t}]@{off}" for (n, t, off) in sorted(opts)[:3]))
            print(f"  {len(ps):3} rows  {kind:5}  bits {min(ps)}..{max(ps)}  " + "  ".join(desc))
        small = [(k, ps) for k, ps in gs.items() if len(ps) < 4]
        if small:
            print(f"  ({sum(len(ps) for _, ps in small)} rows in {len(small)} small groups)")


def instance_sig(mp, t):
    """A wrap instance's addend structure, with word indices made relative to `t`."""
    def rel(name, u):
        return f"{name}[t{u - t:+d}]" if u != t else f"{name}[t]"
    out = []
    for k, o in enumerate(mp[:4]):
        b, rows = describe(o)
        for key, ps in sorted(group(rows).items(), key=lambda kv: -len(kv[1])):
            if key[0] == "xor":
                _, bases, offs = key
                bb = "+".join(rel(n, u) for (n, u) in bases)
                tagp = "" if len(ps) == 32 else f" PARTIAL:{len(ps)}"
                out.append((k, "xor", f"{bb}@{list(offs)}{tagp}"))
                continue
            kind, sig = key
            if len(ps) != 32:
                out.append((k, kind, "PARTIAL:%d" % len(ps)))
                continue
            desc = []
            for s in sig:
                if s and s[0] == "?":
                    desc.append("?")
                else:
                    n, u, off = sorted(s)[0]
                    desc.append(rel(n, u) + (f"@{off}" if off else ""))
            out.append((k, kind, ",".join(desc)))
    return tuple(sorted(out))


def sweep():
    import gen_gf2_seam as S
    maps = S.read_maps()
    for tag, n, _ in S.CLASSES:
        sigs = Counter()
        for e, mp in sorted(maps[tag].items()):
            sigs[instance_sig(mp, e)] += 1
        print(f"\n### {tag}  (n={n}, {sum(sigs.values())} instances, {len(sigs)} distinct shapes)")
        for sig, c in sigs.most_common():
            print(f"  {c:3} x")
            for (k, kind, d) in sig:
                slot = ["got1", "got2", "want1", "want2"][k]
                print(f"        {slot:5} {kind:5} {d}")
