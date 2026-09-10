import re, sys, os
NL = chr(10)
ROTS = {'S1': (6,11,25), 'S0': (2,13,22)}

def make(d, helpers):
    (nodes, ONE, statename, wname, bitpos, xlegs, sigma_rows, maj_rows) = helpers
    t, n, L, ti = d['t'], d['n'], d['L'], d['ti']
    nm = f"R{n}_{t}"
    W = d['words']
    a,b,c,dd,e,f,g,h = (statename(t,i) for i in (0,1,2,3,4,5,6,7))
    wt = f"input_block{t}" if t < 16 else f"outw{t-16}"
    outw = f"oute{t}" if n == 6 else f"outa{t}"
    lf = lambda w, j: ti[W[w][j]]
    s1 = sigma_rows(d, e, ROTS['S1'], 'S1')
    s0 = sigma_rows(d, a, ROTS['S0'], 'S0') if n == 7 else None
    mj = maj_rows(d) if n == 7 else None
    # group -> (letter, kind, data)
    if n == 6:
        gs = [('a','plain',dd), ('b','plain',h), ('c','s1',s1), ('d','ch',(e,f,g)), ('e','plain',wt)]
    else:
        gs = [('a','plain',h), ('b','s1',s1), ('c','ch',(e,f,g)), ('d','plain',wt),
              ('e','s0',s0), ('f','maj',(a,b,c,mj))]
    o = []; A = o.append
    A(f"/-! #### Composition for round {t}, `n = {n}` -/" + NL)
    A(f"noncomputable def lv{nm} (inputs : Nat → F) : Nat → F :=")
    A(f"  fun k => interpDag (raw.toDag (cnstw F)) inputs (mp{nm}.getD k 0)" + NL)
    def entry(kind, dat, j):
        if kind == 'plain': return f"lv {lf(dat, j)}"
        if kind == 's1' or kind == 's0':
            u, th, *_ = dat[j]
            return f"Quadcert.xorVal (midLeafVal (cnstw F) lv {L} mv{nm} {u}) (lv {th})"
        if kind == 'ch':
            e_, f_, g_ = dat
            return f"Quadcert.chVal (lv {lf(e_,j)}) (lv {lf(f_,j)}) (lv {lf(g_,j)})"
        a_, b_, c_, mjr = dat
        la, lb = (ti[x] for x in xlegs([m for m in d['xormids'] if ti[m] == mjr[j]][0]))
        return (f"Quadcert.majVal (lv {la}) (lv {lb}) (lv {lf(c_,j)}) "
                f"(midLeafVal (cnstw F) lv {L} mv{nm} {mjr[j]})")
    for let, kind, dat in gs:
        A(f"noncomputable def v{nm}{let} (lv : Nat → F) : Nat → F")
        for j in range(32): A(f"  | {j} => {entry(kind, dat, j)}")
        A("  | _ => 0" + NL)
    A(f"noncomputable def v{nm}p (lv : Nat → F) : Nat → F")
    for j in range(32): A(f"  | {j} => lv {lf(outw, j)}")
    A("  | _ => 0" + NL)
    for let, _, _ in gs:
        A(f"theorem g{nm}{let}_eq (lv : Nat → F) :")
        A(f"    g{nm}{let} lv = (List.range 32).map (fun i => ((2 ^ i : Nat), v{nm}{let} lv i)) := rfl")
    A(f"theorem ds{nm}_eq (lv : Nat → F) :")
    A(f"    ds{nm} lv = (List.range 32).map (fun i => ((2 ^ i : Nat), v{nm}p lv i)) := rfl" + NL)
    # indexed booleanity
    def vbit(let, kind, dat):
        A(f"theorem vb{nm}{let} (lv : Nat → F) (hone : lv 0 = 1) (c0 : cnstw F 0 = 1)")
        A(f"    (c1 : cnstw F 1 = -2) (hlv : ∀ i, i < {L} → lv i = 0 ∨ lv i = 1) :")
        A(f"    ∀ j, j < 32 → v{nm}{let} lv j = 0 ∨ v{nm}{let} lv j = 1 := by")
        A("  intro j hj")
        A("  match j, hj with")
        for j in range(32):
            if kind == 'plain':
                A(f"  | {j}, _ => exact hlv {lf(dat,j)} (by norm_num)")
            elif kind in ('s1','s0'):
                u, th, *_ = dat[j]
                la, lb = (ti[x] for x in xlegs([m for m in d['xormids'] if ti[m] == u][0]))
                A(f"  | {j}, _ =>")
                A(f"      rw [show v{nm}{let} lv {j} = Quadcert.xorVal")
                A(f"          (midLeafVal (cnstw F) lv {L} mv{nm} {u}) (lv {th}) from rfl,")
                A(f"        Quadcert.midLeafVal_xor_at (cnstw F) lv {L} mv{nm} 0 1 c0 c1 hone")
                A(f"          {u} {u-L} (by norm_num) {la} {lb} (by rfl)]")
                A(f"      exact Quadcert.xorVal_isBit (Quadcert.xorVal_isBit")
                A(f"        (hlv {la} (by norm_num)) (hlv {lb} (by norm_num))) (hlv {th} (by norm_num))")
            elif kind == 'ch':
                e_, f_, g_ = dat
                A(f"  | {j}, _ =>")
                A(f"      exact Quadcert.chVal_isBit (hlv {lf(e_,j)} (by norm_num)) "
                  f"(hlv {lf(f_,j)} (by norm_num)) (hlv {lf(g_,j)} (by norm_num))")
            else:
                a_, b_, c_, mjr = dat
                la, lb = (ti[x] for x in xlegs([m for m in d['xormids'] if ti[m] == mjr[j]][0]))
                A(f"  | {j}, _ =>")
                A(f"      rw [show v{nm}{let} lv {j} = Quadcert.majVal (lv {la}) (lv {lb})")
                A(f"          (lv {lf(c_,j)}) (midLeafVal (cnstw F) lv {L} mv{nm} {mjr[j]}) from rfl,")
                A(f"        Quadcert.midLeafVal_xor_at (cnstw F) lv {L} mv{nm} 0 1 c0 c1 hone")
                A(f"          {mjr[j]} {mjr[j]-L} (by norm_num) {la} {lb} (by rfl)]")
                A(f"      exact Quadcert.majVal_isBit (hlv {la} (by norm_num))")
                A(f"        (hlv {lb} (by norm_num)) (hlv {lf(c_,j)} (by norm_num))")
        A("  | (n + 32), hx => exact absurd hx (by omega)")
        A("")
    for let, kind, dat in gs: vbit(let, kind, dat)
    vbit('p', 'plain', outw)
    return NL.join(o), gs, (a,b,c,dd,e,f,g,h,wt,outw)

def make2(d, helpers, gs, wnames):
    (nodes, ONE, statename, wname, bitpos, xlegs, sigma_rows, maj_rows) = helpers
    t, n, L, ti = d['t'], d['n'], d['L'], d['ti']
    nm = f"R{n}_{t}"; W = d['words']
    a,b,c,dd,e,f,g,h,wt,outw = wnames
    lf = lambda w, j: ti[W[w][j]]
    NB = lambda x: f"SHA256F.natBit (lv{nm} inputs {x})"
    o = []; A = o.append
    # which global list each word is
    glob = {a:("st",t,0), b:("st",t,1), c:("st",t,2), dd:("st",t,3), e:("st",t,4),
            f:("st",t,5), g:("st",t,6), h:("st",t,7), wt:("w",t,None),
            outw:("st",t+1, 4 if n == 6 else 0)}
    used = [dd,h,e,f,g,wt,outw] if n == 6 else [a,b,c,e,f,g,h,wt,outw]
    tag = {}
    for w in used:
        tg = re.sub(r'[^A-Za-z0-9]', '', w)
        tag[w] = tg
        A(f"noncomputable def bw{nm}{tg} (inputs : Nat → F) : List Nat :=")
        A("  [" + ", ".join(NB(lf(w, j)) for j in range(32)) + "]")
        A("")
        kind, x, y = glob[w]
        tgt = f"bitsOf inputs (wordBits {x})" if kind == "w" else f"bitsOf inputs (stateBits {x} {y})"
        A(f"theorem bw{nm}{tg}_eq (inputs : Nat → F) : bw{nm}{tg} inputs = {tgt} := rfl")
        A("")
    # sigma joins
    for let, kind, dat in gs:
        if kind not in ('s1','s0'): continue
        r1, r2, r3 = ROTS['S1' if kind == 's1' else 'S0']
        src = e if kind == 's1' else a
        ls = [lf(src, j) for j in range(32)]
        A(f"theorem nb{nm}{let} (inputs : Nat → F) (hone : lv{nm} inputs 0 = 1)")
        A(f"    (c0 : cnstw F 0 = 1) (c1 : cnstw F 1 = -2)")
        A(f"    (hlv : ∀ i, i < {L} → lv{nm} inputs i = 0 ∨ lv{nm} inputs i = 1) :")
        A(f"    ∀ j, j < 32 → SHA256F.natBit (v{nm}{let} (lv{nm} inputs) j)")
        A(f"      = SHA256.xb (SHA256.xb ((bw{nm}{tag[src]} inputs).getD ((j + {r1}) % 32) 0)")
        A(f"          ((bw{nm}{tag[src]} inputs).getD ((j + {r2}) % 32) 0))")
        A(f"          ((bw{nm}{tag[src]} inputs).getD ((j + {r3}) % 32) 0) := by")
        A("  intro j hj")
        A("  match j, hj with")
        for j in range(32):
            u, th, *_ = dat[j]
            la, lb = (ti[x] for x in xlegs([m for m in d['xormids'] if ti[m] == u][0]))
            p, q, rr = (j+r1) % 32, (j+r2) % 32, (j+r3) % 32
            A(f"  | {j}, _ =>")
            A(f"      show SHA256F.natBit (Quadcert.xorVal")
            A(f"          (midLeafVal (cnstw F) (lv{nm} inputs) {L} mv{nm} {u}) (lv{nm} inputs {th}))")
            A(f"        = SHA256.xb (SHA256.xb ({NB(ls[p])}) ({NB(ls[q])})) ({NB(ls[rr])})")
            A(f"      rw [Quadcert.midLeafVal_xor_at (cnstw F) (lv{nm} inputs) {L} mv{nm} 0 1 c0 c1")
            A(f"          hone {u} {u-L} (by norm_num) {la} {lb} (by rfl),")
            A(f"        natBit_xorVal (Quadcert.xorVal_isBit (hlv {la} (by norm_num))")
            A(f"          (hlv {lb} (by norm_num))) (hlv {th} (by norm_num)),")
            A(f"        natBit_xorVal (hlv {la} (by norm_num)) (hlv {lb} (by norm_num))]")
            A(f"      exact SHA256.xb3_perm (SHA256F.natBit_isBit _) (SHA256F.natBit_isBit _)")
            A(f"        (SHA256F.natBit_isBit _) (SHA256F.natBit_isBit _) (SHA256F.natBit_isBit _)")
            A(f"        (SHA256F.natBit_isBit _) (by omega)")
        A("  | (m + 32), hx => exact absurd hx (by omega)")
        A("")
    # Ch join
    letc = [l for l,k,_ in gs if k == 'ch'][0]
    A(f"theorem nb{nm}{letc} (inputs : Nat → F)")
    A(f"    (hlv : ∀ i, i < {L} → lv{nm} inputs i = 0 ∨ lv{nm} inputs i = 1) :")
    A(f"    ∀ j, j < 32 → SHA256F.natBit (v{nm}{letc} (lv{nm} inputs) j)")
    A(f"      = SHA256.chb ((bw{nm}{tag[e]} inputs).getD j 0) ((bw{nm}{tag[f]} inputs).getD j 0)")
    A(f"          ((bw{nm}{tag[g]} inputs).getD j 0) := by")
    A("  intro j hj")
    A("  match j, hj with")
    for j in range(32):
        A(f"  | {j}, _ =>")
        A(f"      show SHA256F.natBit (Quadcert.chVal (lv{nm} inputs {lf(e,j)}) (lv{nm} inputs {lf(f,j)})")
        A(f"          (lv{nm} inputs {lf(g,j)}))")
        A(f"        = SHA256.chb ({NB(lf(e,j))}) ({NB(lf(f,j))}) ({NB(lf(g,j))})")
        A(f"      exact natBit_chVal (hlv {lf(e,j)} (by norm_num)) (hlv {lf(f,j)} (by norm_num))")
        A(f"        (hlv {lf(g,j)} (by norm_num))")
    A("  | (m + 32), hx => exact absurd hx (by omega)")
    A("")
    # Maj join
    if n == 7:
        letm = [l for l,k,_ in gs if k == 'maj'][0]
        mjr = [x for l,k,x in gs if k == 'maj'][0][3]
        A(f"theorem nb{nm}{letm} (inputs : Nat → F) (hone : lv{nm} inputs 0 = 1)")
        A(f"    (c0 : cnstw F 0 = 1) (c1 : cnstw F 1 = -2)")
        A(f"    (hlv : ∀ i, i < {L} → lv{nm} inputs i = 0 ∨ lv{nm} inputs i = 1) :")
        A(f"    ∀ j, j < 32 → SHA256F.natBit (v{nm}{letm} (lv{nm} inputs) j)")
        A(f"      = SHA256.majb ((bw{nm}{tag[a]} inputs).getD j 0) ((bw{nm}{tag[b]} inputs).getD j 0)")
        A(f"          ((bw{nm}{tag[c]} inputs).getD j 0) := by")
        A("  intro j hj")
        A("  match j, hj with")
        for j in range(32):
            la, lb = (ti[x] for x in xlegs([m for m in d['xormids'] if ti[m] == mjr[j]][0]))
            A(f"  | {j}, _ =>")
            flipped = (la != lf(a,j))
            A(f"      show SHA256F.natBit (Quadcert.majVal (lv{nm} inputs {la})")
            A(f"          (lv{nm} inputs {lb}) (lv{nm} inputs {lf(c,j)})")
            A(f"          (midLeafVal (cnstw F) (lv{nm} inputs) {L} mv{nm} {mjr[j]}))")
            A(f"        = SHA256.majb ({NB(lf(a,j))}) ({NB(lf(b,j))}) ({NB(lf(c,j))})")
            A(f"      rw [Quadcert.midLeafVal_xor_at (cnstw F) (lv{nm} inputs) {L} mv{nm} 0 1 c0 c1")
            A(f"          hone {mjr[j]} {mjr[j]-L} (by norm_num) {la} {lb} (by rfl),")
            A(f"        natBit_majVal (hlv {la} (by norm_num)) (hlv {lb} (by norm_num))")
            A(f"          (hlv {lf(c,j)} (by norm_num))]")
            if flipped:
                A(f"      exact SHA256.majb_comm (SHA256F.natBit_isBit _) (SHA256F.natBit_isBit _)")
                A(f"        (SHA256F.natBit_isBit _)")
        A("  | (m + 32), hx => exact absurd hx (by omega)")
        A("")
    return NL.join(o), tag

def make3(d, helpers, gs, wnames, tag):
    (nodes, ONE, statename, wname, bitpos, xlegs, sigma_rows, maj_rows) = helpers
    t, n, L = d['t'], d['n'], d['L']
    nm = f"R{n}_{t}"; nb = L - 1
    a,b,c,dd,e,f,g,h,wt,outw = wnames
    lv = f"(lv{nm} inputs)"
    oi = 4 if n == 6 else 0
    S = lambda x, i: f"stateWord inputs {x} {i}"
    o = []; A = o.append
    A(f"/-- **Round {t}, `n = {n}`: the compression step over the deployed circuit.** -/")
    A(f"theorem rnd{nm} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)")
    A(f"    (hbz : ∀ j, j < {nb} → interpDag (raw.toDag (cnstw F)) inputs (bp{nm}.getD j (0, 0)).1 = 0)")
    A(f"    (hroot : ∀ k, k < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf{n} k) = 0) :")
    A(f"    {S(t+1, oi)} = SHA256.w32 (")
    if n == 6:
        A(f"      {S(t,3)} + ({S(t,7)} + SHA256.Sigma1 ({S(t,4)})")
        A(f"        + SHA256.Ch ({S(t,4)}) ({S(t,5)}) ({S(t,6)})")
        A(f"        + SHA256.K.getD {t} 0 + wWord inputs {t})) := by")
    else:
        A(f"      {S(t,7)} + SHA256.Sigma1 ({S(t,4)})")
        A(f"        + SHA256.Ch ({S(t,4)}) ({S(t,5)}) ({S(t,6)})")
        A(f"        + SHA256.K.getD {t} 0 + wWord inputs {t}")
        A(f"        + (SHA256.Sigma0 ({S(t,0)}) + SHA256.Maj ({S(t,0)}) ({S(t,1)}) ({S(t,2)}))) := by")
    A(f"  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]")
    A(f"  have hlv : ∀ i, i < {L} → lv{nm} inputs i = 0 ∨ lv{nm} inputs i = 1 :=")
    A(f"    lvBits{nm} inputs hin0 hbz")
    A(f"  have hone : lv{nm} inputs 0 = 1 := by")
    A(f"    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1")
    A(f"    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0")
    A(f"      (by rw [hdaglen, nodes_len]; norm_num)")
    A(f"      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]")
    A(f"    exact hin0")
    A(f"  have c0 : cnstw F 0 = 1 := cnstw_0")
    A(f"  have c1 : cnstw F 1 = -2 := by")
    A(f"    have hh := cnstw_neg (F := F) 1 2 (by rfl) (by norm_num)")
    A(f"    simpa using hh")
    A(f"  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num")
    lets = [l for l,_,_ in gs]
    for let in lets:
        A(f"  have hm{let} : ∀ q ∈ g{nm}{let} {lv}, q.2 = 0 ∨ q.2 = 1 := by")
        A(f"    rw [g{nm}{let}_eq]")
        A(f"    intro q hq")
        A(f"    simp only [List.mem_map, List.mem_range] at hq")
        A(f"    obtain ⟨i, hi, rfl⟩ := hq")
        A(f"    exact vb{nm}{let} {lv} hone c0 c1 hlv i hi")
    A(f"  have hmp : ∀ q ∈ ds{nm} {lv}, q.2 = 0 ∨ q.2 = 1 := by")
    A(f"    rw [ds{nm}_eq]")
    A(f"    intro q hq")
    A(f"    simp only [List.mem_map, List.mem_range] at hq")
    A(f"    obtain ⟨i, hi, rfl⟩ := hq")
    A(f"    exact vb{nm}p {lv} hone c0 c1 hlv i hi")
    big = "ABCDEG"[:len(lets)]
    A(f"  obtain ⟨{', '.join(big)}, P, " + ", ".join(f"h{x}" for x in big)
      + ", hP, " + ", ".join(f"h{x}lt" for x in big) + ", hPlt, hres⟩ :=")
    A(f"    SHA256F.wrap_{'six' if n == 6 else 'seven'}_words (p := p256w) "
      + " ".join(f"(g{nm}{l} {lv})" for l in lets))
    A(f"      (ds{nm} {lv}) {d['K']} (interpDag (raw.toDag (cnstw F)) inputs {d['z']})")
    A("      " + " ".join(f"hm{l}" for l in lets) + " hmp")
    A("      " + " ".join(f"(by norm_num [g{nm}{l}])" for l in lets) + f" (by norm_num [ds{nm}])")
    A(f"      (by norm_num) (by norm_num) (zval_{nm} inputs hin0)")
    A(f"      (allWrap{n} inputs hin0 hroot {t} (by norm_num))")
    for l, x in zip(lets, big):
        A(f"  rw [g{nm}{l}_eq] at h{x}")
        A(f"  have hv{x} : {x} = SHA256.ofBits ((List.range 32).map")
        A(f"      (fun i => SHA256F.natBit (v{nm}{l} {lv} i))) :=")
        A(f"    SHA256F.group_val_eq' (p := p256w) _ 32 {x}")
        A(f"      (fun i hi => vb{nm}{l} {lv} hone c0 c1 hlv i hi) h{x}")
        A(f"      (by simp only [p256w]; omega) (by norm_num)")
    A(f"  rw [ds{nm}_eq] at hP")
    A(f"  have hvP : P = SHA256.ofBits ((List.range 32).map")
    A(f"      (fun i => SHA256F.natBit (v{nm}p {lv} i))) :=")
    A(f"    SHA256F.group_val_eq' (p := p256w) _ 32 P")
    A(f"      (fun i hi => vb{nm}p {lv} hone c0 c1 hlv i hi) hP")
    A(f"      (by simp only [p256w]; omega) (by norm_num)")
    # identify each group
    idents = []
    for (let, kind, dat), x in zip(gs, big):
        if kind == 'plain':
            w = dat
            A(f"  have he{x} : {x} = SHA256.ofBits (bw{nm}{tag[w]} inputs) := by rw [hv{x}]; rfl")
            idents.append((x, f"SHA256.ofBits (bw{nm}{tag[w]} inputs)", w))
        elif kind in ('s1','s0'):
            src = e if kind == 's1' else a; fn = 'Sigma1' if kind == 's1' else 'Sigma0'
            A(f"  have he{x} : {x} = SHA256.{fn} (SHA256.ofBits (bw{nm}{tag[src]} inputs)) := by")
            A(f"    rw [hv{x}, SHA256.{fn}_bits (bw{nm}{tag[src]} inputs) (by rfl)")
            A(f"      (fun q hq => by rw [bw{nm}{tag[src]}_eq] at hq; exact bitsOf_isBit inputs _ q hq)]")
            A(f"    refine congrArg SHA256.ofBits (List.map_congr_left ?_)")
            A(f"    intro i hi")
            A(f"    exact nb{nm}{let} inputs hone c0 c1 hlv i (List.mem_range.mp hi)")
            idents.append((x, f"SHA256.{fn} (SHA256.ofBits (bw{nm}{tag[src]} inputs))", src))
        elif kind == 'ch':
            A(f"  have he{x} : {x} = SHA256.Ch (SHA256.ofBits (bw{nm}{tag[e]} inputs))")
            A(f"      (SHA256.ofBits (bw{nm}{tag[f]} inputs)) (SHA256.ofBits (bw{nm}{tag[g]} inputs)) := by")
            A(f"    rw [hv{x}, SHA256.Ch_bits (bw{nm}{tag[e]} inputs) (bw{nm}{tag[f]} inputs)")
            A(f"      (bw{nm}{tag[g]} inputs) (by rfl)")
            for w in (e, f, g):
                A(f"      (fun q hq => by rw [bw{nm}{tag[w]}_eq] at hq; exact bitsOf_isBit inputs _ q hq)")
            A(f"      ]")
            A(f"    refine congrArg SHA256.ofBits (List.map_congr_left ?_)")
            A(f"    intro i hi")
            A(f"    exact nb{nm}{let} inputs hlv i (List.mem_range.mp hi)")
            idents.append((x, "Ch", None))
        else:
            A(f"  have he{x} : {x} = SHA256.Maj (SHA256.ofBits (bw{nm}{tag[a]} inputs))")
            A(f"      (SHA256.ofBits (bw{nm}{tag[b]} inputs)) (SHA256.ofBits (bw{nm}{tag[c]} inputs)) := by")
            A(f"    rw [hv{x}, SHA256.Maj_bits (bw{nm}{tag[a]} inputs) (bw{nm}{tag[b]} inputs)")
            A(f"      (bw{nm}{tag[c]} inputs)")
            for w in (a, b, c):
                A(f"      (fun q hq => by rw [bw{nm}{tag[w]}_eq] at hq; exact bitsOf_isBit inputs _ q hq)")
            A(f"      ]")
            A(f"    refine congrArg SHA256.ofBits (List.map_congr_left ?_)")
            A(f"    intro i hi")
            A(f"    exact nb{nm}{let} inputs hone c0 c1 hlv i (List.mem_range.mp hi)")
            idents.append((x, "Maj", None))
    A(f"  have heP : P = SHA256.ofBits (bw{nm}{tag[outw]} inputs) := by rw [hvP]; rfl")
    A(f"  simp only [stateWord, wWord, ← bw{nm}{tag[outw]}_eq, "
      + ", ".join(f"← bw{nm}{tag[w]}_eq" for w in sorted(set(tag) - {outw})) + "]")
    A(f"  rw [← heP, " + ", ".join(f"← he{x}" for x in big) + "]")
    A(f"  rw [hres]")
    A(f"  refine congrArg SHA256.w32 ?_")
    A(f"  norm_num [SHA256.K]")
    A(f"  try omega")
    A("")
    return NL.join(o)
