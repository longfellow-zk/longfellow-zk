import re
NL = chr(10)
ROTS = {'s0': (7, 18, 3), 's1': (17, 19, 10)}

def make(d, detail, wordleaves, lname, bitpos):
    t, L = d['t'], d['L']
    det = detail(d)
    out = []; A = out.append
    srcs = {'a': (d['s0w'], t-15), 'b': (d['p7'], t-7), 'c': (d['s1w'], t-2),
            'd': (d['p16'], t-16), 'p': (d['outw'], t)}
    leafmap = {}
    for nm, (w, k) in srcs.items():
        ls = wordleaves(d, w); leafmap[nm] = ls
        A(f"/-- `W{k}`'s bits, in this cone's own vocabulary. -/")
        A(f"noncomputable def bwS{t}{nm} (inputs : Nat → F) : List Nat :=")
        A("  [" + ", ".join(f"SHA256F.natBit (lvS{t} inputs {x})" for x in ls) + "]")
        A("")
        A(f"/-- and it is the global word list. -/")
        A(f"theorem bwS{t}{nm}_eq (inputs : Nat → F) :")
        A(f"    bwS{t}{nm} inputs = bitsOf inputs (wordBits {k}) := rfl")
        A("")
    for nm, tag in (('a','s0'), ('c','s1')):
        r1, r2, sh = ROTS[tag]
        rows = det[tag][1]; ls = leafmap[nm]
        A(f"/-- The σ join for `W{srcs[nm][1]}`: each group entry's bit is the spec's three-way xor. -/")
        A(f"theorem nbS{t}{nm} (inputs : Nat → F) (hone : lvS{t} inputs 0 = 1)")
        A(f"    (c0 : cnstw F 0 = 1) (c1 : cnstw F 1 = -2)")
        A(f"    (hlv : ∀ i, i < 161 → lvS{t} inputs i = 0 ∨ lvS{t} inputs i = 1) :")
        A(f"    ∀ j, j < 32 → SHA256F.natBit (vS{t}{nm} (lvS{t} inputs) j)")
        A(f"      = SHA256.xb (SHA256.xb ((bwS{t}{nm} inputs).getD ((j + {r1}) % 32) 0)")
        A(f"          ((bwS{t}{nm} inputs).getD ((j + {r2}) % 32) 0)) ((bwS{t}{nm} inputs).getD (j + {sh}) 0) := by")
        A("  intro j hj")
        A("  match j, hj with")
        for j in range(32):
            r = rows[j]
            p, q, rr = (j+r1) % 32, (j+r2) % 32, j+sh
            NB = lambda x: f"SHA256F.natBit (lvS{t} inputs {x})"
            rhs = (f"SHA256.xb (SHA256.xb ({NB(ls[p])}) ({NB(ls[q])})) "
                   + (f"({NB(ls[rr])})" if rr < 32 else "0"))
            if r[0] == '3':
                _, U, _, _, _, la, lb, lc = r
                A(f"  | {j}, _ =>")
                A(f"      show SHA256F.natBit (Quadcert.xorVal")
                A(f"          (midLeafVal (cnstw F) (lvS{t} inputs) {L} mvS{t} {U}) (lvS{t} inputs {lc}))")
                A(f"        = {rhs}")
                A(f"      rw [Quadcert.midLeafVal_xor_at (cnstw F) (lvS{t} inputs) {L} mvS{t} 0 1 c0 c1 hone")
                A(f"          {U} {U-L} (by norm_num) {la} {lb} (by rfl),")
                A(f"        natBit_xorVal (Quadcert.xorVal_isBit (hlv {la} (by norm_num)) (hlv {lb} (by norm_num)))")
                A(f"          (hlv {lc} (by norm_num)),")
                A(f"        natBit_xorVal (hlv {la} (by norm_num)) (hlv {lb} (by norm_num))]")
                A(f"      exact SHA256.xb3_perm (SHA256F.natBit_isBit _) (SHA256F.natBit_isBit _)")
                A(f"        (SHA256F.natBit_isBit _) (SHA256F.natBit_isBit _) (SHA256F.natBit_isBit _)")
                A(f"        (SHA256F.natBit_isBit _) (by omega)")
            else:
                _, ia, ib, _, _ = r
                A(f"  | {j}, _ =>")
                A(f"      show SHA256F.natBit (Quadcert.xorVal (lvS{t} inputs {ia}) (lvS{t} inputs {ib}))")
                A(f"        = {rhs}")
                A(f"      rw [natBit_xorVal (hlv {ia} (by norm_num)) (hlv {ib} (by norm_num)),")
                A(f"        SHA256.xb_eq_mod (SHA256F.natBit_isBit _) (SHA256F.natBit_isBit _),")
                A(f"        SHA256.xb_eq_mod (by unfold SHA256.IsBit; omega) (Or.inl rfl)]")
                A(f"      omega")
        A("  | (n + 32), h => exact absurd h (by omega)")
        A("")
    return NL.join(out)

def final(d):
    t, L = d['t'], d['L']
    e = t - 16
    z = d['z']
    lv = f"(lvS{t} inputs)"
    out = []; A = out.append
    A(f"/-- **The schedule recurrence for `W{t}`, over the deployed circuit.** -/")
    A(f"theorem sched{t} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)")
    A(f"    (hbz : ∀ j, j < 160 → interpDag (raw.toDag (cnstw F)) inputs (bpS{t}.getD j (0, 0)).1 = 0)")
    A(f"    (hroot : ∀ k, k < 48 → interpDag (raw.toDag (cnstw F)) inputs (rootOfS k) = 0) :")
    A(f"    SHA256.ofBits (bitsOf inputs (wordBits {t}))")
    A(f"      = SHA256.w32 (SHA256.sigma0 (SHA256.ofBits (bitsOf inputs (wordBits {t-15})))")
    A(f"          + SHA256.ofBits (bitsOf inputs (wordBits {t-7}))")
    A(f"          + SHA256.sigma1 (SHA256.ofBits (bitsOf inputs (wordBits {t-2})))")
    A(f"          + SHA256.ofBits (bitsOf inputs (wordBits {t-16}))) := by")
    A(f"  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]")
    A(f"  have hlv : ∀ i, i < 161 → lvS{t} inputs i = 0 ∨ lvS{t} inputs i = 1 :=")
    A(f"    lvBits{t} inputs hin0 hbz")
    A(f"  have hone : lvS{t} inputs 0 = 1 := by")
    A(f"    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1")
    A(f"    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0")
    A(f"      (by rw [hdaglen, nodes_len]; norm_num)")
    A(f"      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]")
    A(f"    exact hin0")
    A(f"  have c0 : cnstw F 0 = 1 := cnstw_0")
    A(f"  have c1 : cnstw F 1 = -2 := by")
    A(f"    have h := cnstw_neg (F := F) 1 2 (by rfl) (by norm_num)")
    A(f"    simpa using h")
    A(f"  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num")
    for nm in ('a','b','c','d'):
        A(f"  have hm{nm} : ∀ q ∈ gS{t}{nm} {lv}, q.2 = 0 ∨ q.2 = 1 := by")
        A(f"    rw [gS{t}{nm}_eq]")
        A(f"    intro q hq")
        A(f"    simp only [List.mem_map, List.mem_range] at hq")
        A(f"    obtain ⟨i, hi, rfl⟩ := hq")
        A(f"    exact vbS{t}{nm} {lv} hone c0 c1 hlv i hi")
    A(f"  have hmp : ∀ q ∈ dsS{t} {lv}, q.2 = 0 ∨ q.2 = 1 := by")
    A(f"    rw [dsS{t}_eq]")
    A(f"    intro q hq")
    A(f"    simp only [List.mem_map, List.mem_range] at hq")
    A(f"    obtain ⟨i, hi, rfl⟩ := hq")
    A(f"    exact vbS{t}p {lv} hone c0 c1 hlv i hi")
    A(f"  obtain ⟨A, B, C, D, P, hA, hB, hC, hD, hP, hAlt, hBlt, hClt, hDlt, hPlt, hres⟩ :=")
    A(f"    SHA256F.wrap_four_words (p := p256w) (gS{t}a {lv}) (gS{t}b {lv}) (gS{t}c {lv})")
    A(f"      (gS{t}d {lv}) (dsS{t} {lv}) (interpDag (raw.toDag (cnstw F)) inputs {z})")
    A(f"      hma hmb hmc hmd hmp (by norm_num [gS{t}a]) (by norm_num [gS{t}b])")
    A(f"      (by norm_num [gS{t}c]) (by norm_num [gS{t}d]) (by norm_num [dsS{t}]) (by norm_num)")
    A(f"      (zval_S{t} inputs hin0) (allWrap4 inputs hin0 hroot {e} (by norm_num))")
    for nm, V in (('a','a'),('b','b'),('c','c'),('d','d')):
        big = {'a':'A','b':'B','c':'C','d':'D'}[nm]
        A(f"  rw [gS{t}{nm}_eq] at h{big}")
        A(f"  have hv{big} : {big} = SHA256.ofBits ((List.range 32).map")
        A(f"      (fun i => SHA256F.natBit (vS{t}{V} {lv} i))) :=")
        A(f"    SHA256F.group_val_eq' (p := p256w) _ 32 {big}")
        A(f"      (fun i hi => vbS{t}{V} {lv} hone c0 c1 hlv i hi) h{big}")
        A(f"      (by simp only [p256w]; omega) (by norm_num)")
    A(f"  rw [dsS{t}_eq] at hP")
    A(f"  have hvP : P = SHA256.ofBits ((List.range 32).map")
    A(f"      (fun i => SHA256F.natBit (vS{t}p {lv} i))) :=")
    A(f"    SHA256F.group_val_eq' (p := p256w) _ 32 P")
    A(f"      (fun i hi => vbS{t}p {lv} hone c0 c1 hlv i hi) hP")
    A(f"      (by simp only [p256w]; omega) (by norm_num)")
    # sigma joins
    for nm, big, src, fn in (('a','A',t-15,'sigma0'), ('c','C',t-2,'sigma1')):
        A(f"  have hs{big} : {big} = SHA256.{fn} (SHA256.ofBits (bitsOf inputs (wordBits {src}))) := by")
        A(f"    rw [hv{big}, ← bwS{t}{nm}_eq, SHA256.{fn}_bits (bwS{t}{nm} inputs) (by rfl)")
        A(f"      (fun b hb => by rw [bwS{t}{nm}_eq] at hb; exact bitsOf_isBit inputs _ b hb)]")
        A(f"    refine congrArg SHA256.ofBits ?_")
        A(f"    refine List.map_congr_left ?_")
        A(f"    intro i hi")
        A(f"    exact nbS{t}{nm} inputs hone c0 c1 hlv i (List.mem_range.mp hi)")
    for nm, big, src in (('b','B',t-7), ('d','D',t-16), ('p','P',t)):
        A(f"  have he{big} : {big} = SHA256.ofBits (bitsOf inputs (wordBits {src})) := by")
        A(f"    rw [hv{big}, ← bwS{t}{nm}_eq]")
        A(f"    rfl")
    A(f"  rw [← heP, ← heB, ← heD, ← hsA, ← hsC]")
    A(f"  exact hres")
    A("")
    return NL.join(out)
