/-
# Chained templates: a leaf block, then a block whose nodes may read each other

`ConeMid` handles a leaf block, a block of sums **over leaves only**, and one root. Its own
docstring says why that was exactly right for the 48 schedule cones: no mid there references
another mid. The GF(2^128) wrapping-sum cones are not like that.

Measured on `Gen/Sha256Gf2`, one `assert_wrapping_sum_gf2` cone has 632 nodes in three kinds:

| kind | count | shape |
|---|---:|---|
| one term | 208 | `1 · [a] · [b]` — the binary product trees |
| two terms | 134 | `1 + c₂₊ᵢ · b` — one injection factor over an input bit |
| four terms | 64 | `1 + c₂₊ᵢ · (g + eg + ef)` — a factor over a *computed* bit, `Ch` fused in |

The 208 product nodes are the problem: they multiply *other product nodes*, so the block is a
chain rather than two levels. `interpDagAux_chainBlock` below allows node `j` to read leaves and
nodes `0 … j-1`, which is the weakest condition `coneIs` already enforces, so it subsumes
`ConeMid` and needs nothing from the shape of a particular cone.

## Why a lemma rather than `simp`

The same reason as `ConeFlat` and `ConeMid`. Evaluating one node by `interpDag_sum` reads its
operands out of the accumulator with `List.getD`, and here the accumulator reaches 632 entries;
at two operands per product node that is ~130,000 rewrite steps for the product trees alone.
`chainVals` computes the block once, by induction, so the instance pays only for the reads that
survive into the statement.
-/

import quadcert.Core.ConeMid

namespace Quadcert

variable {F : Type} [Field F]

/-- Reading a template operand inside a chain block: a leaf below `L`, otherwise the value
    already computed for chain node `i - L`. -/
def chainRead (lv : Nat → F) (L : Nat) (prev : List F) (i : Nat) : F :=
  if i < L then lv i else prev.getD (i - L) 0

/-- The chain block's values, in order. Node `j` reads leaves and nodes `0 … j-1`. -/
def chainVals (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat)) : Nat → List F
  | 0 => []
  | j + 1 =>
      chainVals consts lv L mv j ++
        [(mv j).foldl (fun acc t => acc
            + consts t.1 * chainRead lv L (chainVals consts lv L mv j) t.2.1
              * chainRead lv L (chainVals consts lv L mv j) t.2.2) 0]

theorem chainVals_length (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat)) :
    ∀ M, (chainVals consts lv L mv M).length = M
  | 0 => by simp [chainVals]
  | j + 1 => by simp [chainVals, chainVals_length consts lv L mv j]

theorem getD_app_lt (l₁ l₂ : List F) {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_ge (l₁ l₂ : List F) {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- Reading the accumulator is exactly `chainRead`. Total in `i`, so no bound is needed. -/
theorem getD_leaves_chain (consts lv : Nat → F) (L M : Nat)
    (mv : Nat → List (Nat × Nat × Nat)) (i : Nat) :
    ((List.range L).map lv ++ chainVals consts lv L mv M).getD i 0
      = chainRead lv L (chainVals consts lv L mv M) i := by
  have hlen : ((List.range L).map lv).length = L := by simp
  rw [chainRead]
  by_cases h : i < L
  · rw [if_pos h, getD_app_lt _ _ (by omega), getD_range_map lv L i h]
  · rw [if_neg h, getD_app_ge _ _ (by omega), hlen]

/-- **The chain block evaluates to `chainVals`.** The only hypothesis is that each node's
    operands precede it, which is what `coneIs` checks. -/
theorem interpDagAux_chainBlock (consts lv : Nat → F) (L : Nat)
    (mv : Nat → List (Nat × Nat × Nat)) :
    ∀ (M : Nat), (∀ j, j < M → ∀ t ∈ mv j, t.2.1 < L + j ∧ t.2.2 < L + j) →
      interpDagAux lv ((List.range M).map (fun j =>
          (DagNode.sum ((mv j).map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩)) : DagNode F)))
        ((List.range L).map lv)
        = (List.range L).map lv ++ chainVals consts lv L mv M := by
  intro M
  induction M with
  | zero => intro _; simp [interpDagAux, chainVals]
  | succ k ih =>
      intro hb
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        interpDagAux_append, ih (fun j hj => hb j (by omega))]
      simp only [interpDagAux, nodeValue, List.append_nil]
      rw [chainVals]
      rw [List.append_assoc]
      refine congrArg _ (congrArg _ (List.cons_eq_cons.mpr ⟨?_, rfl⟩))
      rw [List.foldl_map]
      congr 1
      funext acc t
      rw [getD_leaves_chain, getD_leaves_chain]

/-- **A chained template evaluates by `chainVals`.** `L` leaves then `M` sum nodes; chain node
    `j` sits at template index `L + j`. -/
theorem interpDag_leafChain (consts lv : Nat → F) (L M : Nat)
    (mv : Nat → List (Nat × Nat × Nat))
    (hb : ∀ j, j < M → ∀ t ∈ mv j, t.2.1 < L + j ∧ t.2.2 < L + j)
    {j : Nat} (hj : j < M) :
    interpDag (tmplDag consts ((List.range L).map (fun i => (TmplNode.leaf i : TmplNode))
        ++ (List.range M).map (fun k => TmplNode.sum (mv k)))) lv (L + j)
      = (chainVals consts lv L mv M).getD j 0 := by
  have hdag : tmplDag consts ((List.range L).map (fun i => (TmplNode.leaf i : TmplNode))
      ++ (List.range M).map (fun k => TmplNode.sum (mv k)))
      = ((List.range L).map (fun i => (DagNode.input i : DagNode F)))
        ++ (List.range M).map (fun k =>
            (DagNode.sum ((mv k).map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩)) : DagNode F)) := by
    simp [tmplDag, List.map_append, List.map_map, Function.comp_def]
  show (interpDagAux lv _ []).getD (L + j) 0 = _
  rw [hdag, interpDagAux_append, interpDagAux_leafBlock consts lv L [],
    List.nil_append, interpDagAux_chainBlock consts lv L mv M hb]
  have hlen : ((List.range L).map lv).length = L := by simp
  rw [getD_app_ge _ _ (by omega), hlen]
  congr 1
  omega

/-! ## Reading one row against the whole list

`interpDag_leafChain` lands on `(chainVals … M).getD j 0` for the root only. An instance that
wants to name every row -- which is what the injection cones need, since each row is a *power of
α* and the exponents add -- would otherwise have to unfold the whole chain at once. The lemmas
below let a row be read on its own, with its operands still read out of the full list, so a
proof pays `O(1)` per row instead of `O(M)`.
-/

/-- A longer chain extends a shorter one. -/
theorem chainVals_prefix (consts lv : Nat → F) (L : Nat)
    (mv : Nat → List (Nat × Nat × Nat)) :
    ∀ M j, j ≤ M → ∃ t, chainVals consts lv L mv M = chainVals consts lv L mv j ++ t := by
  intro M
  induction M with
  | zero => intro j hj; exact ⟨[], by rw [Nat.le_zero.mp hj]; simp⟩
  | succ k ih =>
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | h
      · exact ⟨[], by simp⟩
      · obtain ⟨t, ht⟩ := ih j (Nat.lt_succ_iff.mp h)
        refine ⟨t ++ [(mv k).foldl (fun acc s => acc
            + consts s.1 * chainRead lv L (chainVals consts lv L mv k) s.2.1
              * chainRead lv L (chainVals consts lv L mv k) s.2.2) 0], ?_⟩
        rw [chainVals, ht, List.append_assoc]

/-- Values already computed do not change as the chain grows. -/
theorem chainVals_getD_of_le (consts lv : Nat → F) (L : Nat)
    (mv : Nat → List (Nat × Nat × Nat)) {i j M : Nat} (hij : i < j) (hjM : j ≤ M) :
    (chainVals consts lv L mv M).getD i 0 = (chainVals consts lv L mv j).getD i 0 := by
  obtain ⟨t, ht⟩ := chainVals_prefix consts lv L mv M j hjM
  rw [ht, getD_app_lt _ _ (by rw [chainVals_length]; exact hij)]

/-- Hence an operand of row `j` reads the same from the full list as from row `j`'s own prefix. -/
theorem chainRead_of_le (consts lv : Nat → F) (L : Nat)
    (mv : Nat → List (Nat × Nat × Nat)) {i j M : Nat} (hi : i < L + j) (hjM : j ≤ M) :
    chainRead lv L (chainVals consts lv L mv M) i
      = chainRead lv L (chainVals consts lv L mv j) i := by
  rw [chainRead, chainRead]
  by_cases h : i < L
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact chainVals_getD_of_le consts lv L mv (by omega) hjM

private theorem foldl_read_congr (consts lv : Nat → F) (L : Nat) (p q : List F) :
    ∀ (ts : List (Nat × Nat × Nat)),
      (∀ t ∈ ts, chainRead lv L p t.2.1 = chainRead lv L q t.2.1
        ∧ chainRead lv L p t.2.2 = chainRead lv L q t.2.2) →
      ∀ acc : F,
        ts.foldl (fun acc t => acc + consts t.1 * chainRead lv L p t.2.1
            * chainRead lv L p t.2.2) acc
          = ts.foldl (fun acc t => acc + consts t.1 * chainRead lv L q t.2.1
            * chainRead lv L q t.2.2) acc
  | [], _, _ => rfl
  | a :: l, h, acc => by
      simp only [List.foldl_cons]
      rw [(h a (List.mem_cons_self ..)).1, (h a (List.mem_cons_self ..)).2]
      exact foldl_read_congr consts lv L p q l (fun t ht => h t (List.mem_cons_of_mem _ ht)) _

/-- **One row of a chain, read against the whole chain.** The bound on the row's operands is the
    same one `coneIs` already enforces, and is what makes the self-reference well founded. -/
theorem chainVals_row (consts lv : Nat → F) (L : Nat)
    (mv : Nat → List (Nat × Nat × Nat)) {j M : Nat} (hj : j < M)
    (hb : ∀ t ∈ mv j, t.2.1 < L + j ∧ t.2.2 < L + j) :
    (chainVals consts lv L mv M).getD j 0
      = (mv j).foldl (fun acc t => acc + consts t.1
          * chainRead lv L (chainVals consts lv L mv M) t.2.1
          * chainRead lv L (chainVals consts lv L mv M) t.2.2) 0 := by
  rw [chainVals_getD_of_le consts lv L mv (Nat.lt_succ_self j) hj, chainVals,
    getD_app_ge _ _ (by rw [chainVals_length]), chainVals_length, Nat.sub_self]
  simp only [List.getD_cons_zero]
  exact (foldl_read_congr consts lv L _ _ (mv j)
    (fun t ht => ⟨chainRead_of_le consts lv L mv (hb t ht).1 (Nat.le_of_lt hj),
                  chainRead_of_le consts lv L mv (hb t ht).2 (Nat.le_of_lt hj)⟩) 0).symm

/-! ## Sanity

Three leaves, then the chain the wrapping-sum cone is made of: two injection factors over leaves,
their product, and one two-term combination of that product with a leaf. Kernel-checked, so the
index convention is pinned rather than asserted. -/

section Sanity

/-- Three leaves, then the chain the wrapping-sum cone is made of: two injection factors over
    leaves, their product (a node reading two chain nodes -- the case `ConeMid` cannot express),
    and a two-term combination of that product with leaves. -/
private def mvS : Nat → List (Nat × Nat × Nat)
  | 0 => [(0, 0, 0), (1, 0, 1)]
  | 1 => [(0, 0, 0), (2, 0, 2)]
  | 2 => [(0, 3, 4)]
  | _ => [(0, 5, 0), (2, 1, 2)]

private def cS : Nat → ℚ
  | 0 => 1
  | 1 => 3
  | _ => 5

private def lS : Nat → ℚ
  | 0 => 1
  | 1 => 2
  | _ => 7

private def tnS : List TmplNode :=
  (List.range 3).map (fun i => (TmplNode.leaf i : TmplNode))
    ++ (List.range 4).map (fun k => TmplNode.sum (mvS k))

private theorem tnS_eq : tnS =
    [.leaf 0, .leaf 1, .leaf 2, .sum (mvS 0), .sum (mvS 1), .sum (mvS 2), .sum (mvS 3)] := rfl

/-- Direct evaluation, not using the lemma: `7`, `36`, `7·36 = 252`, `252 + 5·2·7 = 322`. -/
private theorem directS : interpDag (tmplDag cS tnS) lS 6 = 322 := by
  rw [tnS_eq]
  norm_num [interpDag, interpDagAux, nodeValue, tmplDag, mvS, cS, lS,
    List.map_cons, List.map_nil, List.getD]

/-- The lemma, applied. -/
private theorem viaLemmaS : interpDag (tmplDag cS tnS) lS (3 + 3)
    = (chainVals cS lS 3 mvS 4).getD 3 0 :=
  interpDag_leafChain cS lS 3 4 mvS (by decide) (by decide)

private theorem sidesS : (chainVals cS lS 3 mvS 4).getD 3 0 = 322 := by
  norm_num [chainVals, chainRead, mvS, cS, lS, List.getD]

example : (322 : ℚ) = 322 := by rw [← directS, viaLemmaS, sidesS]

end Sanity

end Quadcert
