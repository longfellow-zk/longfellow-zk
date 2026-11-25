import Merkle.ExtractionROM
import Bcs.AdaptiveCommit
import Mathlib.Algebra.BigOperators.Fin

/-!
# Merkle query work in the v1 good event

A disclosed path certifies chronological work when its verifier queries were already made
by the adversary and no answer hit a child digest named at an earlier or the same input.
-/

set_option autoImplicit false

namespace LfzkV1.MerkleWork125

open Merkle Merkle.MH

variable {Salt Salt' M M' D Enc : Type} [Inhabited D] [DecidableEq Enc]

/-- Every child whose input occurs in the trace was queried before each node naming its answer. -/
def OrderedChildren (H : Enc → D) (decodeNode : Enc → Option (D × D)) (seen : List Enc) : Prop :=
  ∀ parent child labels, parent ∈ seen → child ∈ seen → decodeNode parent = some labels →
    (H child = labels.1 ∨ H child = labels.2) → seen.idxOf child < seen.idxOf parent

variable (C : Codec Salt M D Enc) (H : Enc → D)
  (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (pf : Opening n I Salt D)
  (i : Fin n) (hi : i ∈ I)

private def pathInput (v : ℕ) : Enc :=
  if v = n + i.val then C.leafEnc (pf.nonce ⟨i, hi⟩, a i)
  else C.nodeEnc (checkValues (C.withOracle H) n I a pf (2 * v),
    checkValues (C.withOracle H) n I a pf (2 * v + 1))

private theorem pathVertex_lt_n (v : ℕ) (hv : v ∈ Heap.pathOf n i) (hne : v ≠ n + i.val) :
    v < n := by
  obtain ⟨_, k, hk⟩ := Heap.mem_pathOf.mp hv
  cases k with
  | zero => exact False.elim (hne (by simpa using hk))
  | succ k =>
    have hi' := i.isLt
    rw [hk, pow_succ, ← Nat.div_div_eq_div_mul]
    have hle := Nat.div_le_self (n + i.val) (2 ^ k)
    omega

omit [DecidableEq Enc] in
private theorem pathInput_query (v : ℕ) (hv : v ∈ Heap.pathOf n i) :
    vertexQuery (C.withOracle H) n I a pf v = some (pathInput C H n I a pf i hi v) := by
  by_cases he : v = n + i.val
  · subst v
    simpa only [pathInput, if_true, Codec.withOracle] using
      vertexQuery_leaf_pos (C.withOracle H) n I a pf i hi
  · simp only [pathInput, if_neg he]
    exact vertexQuery_node (C.withOracle H) n I a pf v
      ⟨(Heap.mem_pathOf.mp hv).1, pathVertex_lt_n n i v hv he, Heap.mem_pathSet.mpr ⟨i, hi, hv⟩⟩

omit [DecidableEq Enc] in
private theorem leaf_input_mem [DecidableEq Enc] :
    C.leafEnc (pf.nonce ⟨i, hi⟩, a i) ∈ checkTraceQueries (C.withOracle H) n I a pf := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩

private theorem pathInput_mem (v : ℕ) (hv : v ∈ Heap.pathOf n i) :
    pathInput C H n I a pf i hi v ∈ checkTraceQueries (C.withOracle H) n I a pf := by
  by_cases he : v = n + i.val
  · rw [pathInput, if_pos he]
    exact leaf_input_mem C H n I a pf i hi
  · rw [pathInput, if_neg he]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Heap.mem_pathSet.mpr ⟨i, hi, hv⟩,
      (Heap.mem_pathOf.mp hv).1, pathVertex_lt_n n i v hv he⟩, rfl⟩

private theorem child_before_parent (dec : RoleDecoders C) (seen : List Enc)
    (hseen : ∀ x ∈ checkTraceQueries (C.withOracle H) n I a pf, x ∈ seen)
    (horder : OrderedChildren H dec.nodeDec seen)
    (v : ℕ) (hv : v ∈ Heap.pathOf n i) (hv1 : 1 < v) :
    seen.idxOf (pathInput C H n I a pf i hi v) <
      seen.idxOf (pathInput C H n I a pf i hi (v / 2)) := by
  have hp := Heap.parent_mem_pathOf hv hv1
  have hvle := (Finset.mem_Icc.mp (Heap.pathOf_mem_nodes_iff hv)).2
  have hne : v / 2 ≠ n + i.val := by omega
  have hd := vertexQuery_answer (C.withOracle H) n I a pf v _
      (pathInput_query C H n I a pf i hi v hv)
  apply horder _ _ _
    (hseen _ (pathInput_mem C H n I a pf i hi (v / 2) hp))
    (hseen _ (pathInput_mem C H n I a pf i hi v hv))
  · rw [pathInput, if_neg hne, dec.node_roundTrip]
  · change H (pathInput C H n I a pf i hi v) =
        checkValues (C.withOracle H) n I a pf (2 * (v / 2)) ∨
      H (pathInput C H n I a pf i hi v) =
        checkValues (C.withOracle H) n I a pf (2 * (v / 2) + 1)
    rcases (show v = 2 * (v / 2) ∨ v = 2 * (v / 2) + 1 by omega) with h | h
    · exact Or.inl (hd.trans (congrArg _ h))
    · exact Or.inr (hd.trans (congrArg _ h))

private theorem ancestor_order (dec : RoleDecoders C) (seen : List Enc)
    (hseen : ∀ x ∈ checkTraceQueries (C.withOracle H) n I a pf, x ∈ seen)
    (horder : OrderedChildren H dec.nodeDec seen)
    (v : ℕ) (hv : v ∈ Heap.pathOf n i) (k : ℕ) (hk : 0 < v / 2 ^ k) :
    seen.idxOf (pathInput C H n I a pf i hi v) ≤
      seen.idxOf (pathInput C H n I a pf i hi (v / 2 ^ k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul] at hk ⊢
    have hp : v / 2 ^ k ∈ Heap.pathOf n i :=
      Heap.ancestor_mem_pathOf hv ⟨k, rfl⟩ (by omega)
    exact (ih (by omega)).trans
      (child_before_parent C H n I a pf i hi dec seen hseen horder _ hp (by omega)).le

private theorem ancestor_strict (dec : RoleDecoders C) (seen : List Enc)
    (hseen : ∀ x ∈ checkTraceQueries (C.withOracle H) n I a pf, x ∈ seen)
    (horder : OrderedChildren H dec.nodeDec seen)
    (v : ℕ) (hv : v ∈ Heap.pathOf n i) (k : ℕ) (hk : 0 < k)
    (hp : 0 < v / 2 ^ k) :
    seen.idxOf (pathInput C H n I a pf i hi v) <
      seen.idxOf (pathInput C H n I a pf i hi (v / 2 ^ k)) := by
  cases k with
  | zero => omega
  | succ k =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul] at hp ⊢
    have hvk : v / 2 ^ k ∈ Heap.pathOf n i :=
      Heap.ancestor_mem_pathOf hv ⟨k, rfl⟩ (by omega)
    exact (ancestor_order C H n I a pf i hi dec seen hseen horder v hv k (by omega)).trans_lt
      (child_before_parent C H n I a pf i hi dec seen hseen horder _ hvk (by omega))

private theorem pathInput_injOn (dec : RoleDecoders C) (seen : List Enc)
    (hseen : ∀ x ∈ checkTraceQueries (C.withOracle H) n I a pf, x ∈ seen)
    (horder : OrderedChildren H dec.nodeDec seen) :
    Set.InjOn (pathInput C H n I a pf i hi) (Heap.pathOf n i : Set ℕ) := by
  intro u hu v hv he
  change u ∈ Heap.pathOf n i at hu
  change v ∈ Heap.pathOf n i at hv
  rcases Heap.comparable_of_mem_pathOf hu hv with ⟨k, hk⟩ | ⟨k, hk⟩
  · by_cases h0 : k = 0
    · simpa [h0] using hk
    · have hpos : 0 < v / 2 ^ k := hk ▸ (Heap.mem_pathOf.mp hu).1
      have hlt := ancestor_strict C H n I a pf i hi dec seen hseen horder v hv k (by omega) hpos
      rw [← hk, he] at hlt
      exact False.elim (Nat.lt_irrefl _ hlt)
  · by_cases h0 : k = 0
    · simpa [h0] using hk.symm
    · have hpos : 0 < u / 2 ^ k := hk ▸ (Heap.mem_pathOf.mp hv).1
      have hlt := ancestor_strict C H n I a pf i hi dec seen hseen horder u hu k (by omega) hpos
      rw [← hk, he] at hlt
      exact False.elim (Nat.lt_irrefl _ hlt)

/-- An opening in a heap of at least 2048 leaves and a leaf of a disjoint encoding length
require at least thirteen adversary input queries in the ordered, replayable branch. -/
theorem queryFloor (i : Fin n) (hi : i ∈ I) (dec : RoleDecoders C) (seen : List Enc)
    (hseen : ∀ x ∈ checkTraceQueries (C.withOracle H) n I a pf, x ∈ seen)
    (horder : OrderedChildren H dec.nodeDec seen) (hn : 2048 ≤ n)
    {x : Enc} (hx : x ∈ seen) (hLeaf : ∀ sm, x ≠ C.leafEnc sm)
    (hNode : ∀ labels, x ≠ C.nodeEnc labels) :
    13 ≤ seen.length := by
  let path := (Heap.pathOf n i).image (pathInput C H n I a pf i hi)
  have hpath : path.card = (Heap.pathOf n i).card :=
    Finset.card_image_of_injOn (pathInput_injOn C H n I a pf i hi dec seen hseen horder)
  have hxpath : x ∉ path := by
    intro h
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
    by_cases he : v = n + i.val
    · exact hLeaf _ (hv.symm.trans (if_pos he))
    · exact hNode _ (hv.symm.trans (if_neg he))
  have hsub : insert x path ⊆ seen.toFinset := by
    intro y hy
    apply List.mem_toFinset.mpr
    rcases Finset.mem_insert.mp hy with h | h
    · exact h ▸ hx
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
      exact hseen _ (pathInput_mem C H n I a pf i hi v hv)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxpath, hpath, Heap.pathOf_card,
    Nat.log2_eq_log_two] at hcard
  have d : 11 ≤ Nat.log 2 (n + i.val) := calc
    11 = Nat.log 2 2048 := by decide
    _ ≤ Nat.log 2 (n + i.val) := Nat.log_mono_right (by omega)
  exact le_trans (by omega) (List.toFinset_card_le seen)

/-- The second field's opened leaf supplies the extra input when its encoding length
differs from every first-field leaf and node. -/
theorem twoFieldQueryFloor (i : Fin n) (hi : i ∈ I) (C' : Codec Salt' M' D Enc)
    (n' : ℕ) (I' : Finset (Fin n')) (a' : Fin n' → M')
    (pf' : Opening n' I' Salt' D) (i' : Fin n') (hi' : i' ∈ I')
    (dec : RoleDecoders C) (seen : List Enc)
    (hseen : ∀ x ∈ checkTraceQueries (C.withOracle H) n I a pf, x ∈ seen)
    (hseen' : ∀ x ∈ checkTraceQueries (C'.withOracle H) n' I' a' pf', x ∈ seen)
    (horder : OrderedChildren H dec.nodeDec seen) (hn : 2048 ≤ n)
    (inputLength : Enc → ℕ)
    (leafLen leafLen' nodeLen : ℕ) (hll : leafLen' ≠ leafLen) (hln : leafLen' ≠ nodeLen)
    (hl : ∀ sm, inputLength (C.leafEnc sm) = leafLen)
    (hnl : ∀ labels, inputLength (C.nodeEnc labels) = nodeLen)
    (hl' : ∀ sm, inputLength (C'.leafEnc sm) = leafLen') :
    13 ≤ seen.length := by
  apply queryFloor C H n I a pf i hi dec seen hseen horder hn
    (hseen' _ (leaf_input_mem C' H n' I' a' pf' i' hi'))
  · intro sm h
    exact hll ((hl' _).symm.trans ((congrArg inputLength h).trans (hl sm)))
  · intro labels h
    exact hln ((hl' _).symm.trans ((congrArg inputLength h).trans (hnl labels)))


open Merkle.RandomOracle

variable {A : Type*} {T budget : ℕ}

/-- At child slot j, the targets are the two children named by each input up to and
including slot j. -/
abbrev ForwardIndex (budget : ℕ) := Σ j : Fin budget, Fin (j.val + 1) × Bool

def forwardSlot (hbudget : budget ≤ T) (k : ForwardIndex budget) : Fin T :=
  ⟨k.1.val, k.1.isLt.trans_le hbudget⟩

private def namedChild (decodeNode : Enc → Option (D × D))
    (x : Option Enc) (right : Bool) : D :=
  (x.bind decodeNode).elim default fun labels => if right then labels.2 else labels.1

/-- Read the target from a tape with the tested slot neutralized. -/
def forwardTarget (decodeNode : Enc → Option (D × D)) (R : Tree Enc D A budget)
    (hbudget : budget ≤ T) (k : ForwardIndex budget) (answers : Fin T → D) : D :=
  namedChild decodeNode
    (runSlots T R (Function.update answers (forwardSlot hbudget k) default))[k.2.1.val]? k.2.2

/-- The answers in the original and neutralized tape determine the same prospective
inputs up through the tested slot, so the target still names the real child. -/
private theorem forwardTarget_eq (decodeNode : Enc → Option (D × D)) (R : Tree Enc D A budget)
    (hbudget : budget ≤ T) (k : ForwardIndex budget) (answers : Fin T → D) :
    forwardTarget decodeNode R hbudget k answers =
      namedChild decodeNode (runSlots T R answers)[k.2.1.val]? k.2.2 := by
  have htake := lazyRun_seen_take_congr answers
    (Function.update answers (forwardSlot hbudget k) default) default k.1.val
    (fun s hs => (Function.update_of_ne (show s ≠ forwardSlot hbudget k from
      fun h => Nat.lt_irrefl _ (by simpa only [h, forwardSlot] using hs)) _ _).symm)
    R []
  change (runSlots T R answers).take (k.1.val + 1) =
    (runSlots T R (Function.update answers (forwardSlot hbudget k) default)).take (k.1.val + 1)
    at htake
  have hget := congrArg (fun seen : List Enc => seen[k.2.1.val]?) htake
  simp only [List.getElem?_take_of_lt k.2.1.isLt] at hget
  rw [forwardTarget, hget]

theorem forwardIndex_card (budget : ℕ) :
    Fintype.card (ForwardIndex budget) = budget * (budget + 1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  induction budget with
  | zero => simp
  | succ k ih => rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last, ih]; ring

/-- At a fixed challenge tape, forward hits cost at most t_A(t_A+1) guesses
over the Merkle answer tape. -/
theorem forward_card_le [Fintype D] [DecidableEq D]
    (decodeNode : Enc → Option (D × D)) (R : Tree Enc D A budget) (hbudget : budget ≤ T) :
    (Finset.univ.filter (HitFamily T Finset.univ (forwardSlot hbudget)
      (forwardTarget decodeNode R hbudget))).card
      ≤ budget * (budget + 1) * Fintype.card D ^ (T - 1) := by
  have h := answerTape_hitFamily_card_le T (Finset.univ : Finset (ForwardIndex budget))
    (forwardSlot hbudget) (forwardTarget decodeNode R hbudget)
    (fun k _ => hitTarget_of_neutralize _ _ fun tape =>
      namedChild decodeNode (runSlots T R tape)[k.2.1.val]? k.2.2)
  simpa only [Finset.card_univ, forwardIndex_card] using h

/-- Outside the forward-hit family, every named child in the adversary trace occurs before
its parent. The verifier continuation can supply the same oracle because R is its prefix. -/
theorem orderedChildren_of_noForward {B : Type*} {fuel : ℕ}
    (decodeNode : Enc → Option (D × D)) (R : Tree Enc D A budget)
    (full : Tree Enc D B fuel) (hbudget : budget ≤ T) (answers : Fin T → D)
    (hpref : runSlots T R answers <+: runSlots T full answers)
    (hfree : ¬ HitFamily T Finset.univ (forwardSlot hbudget)
      (forwardTarget decodeNode R hbudget) answers) :
    OrderedChildren (runOracle T full answers) decodeNode (runSlots T R answers) := by
  intro parent child labels hparent hchild hlabels hanswer
  let seen := runSlots T R answers
  have hplen : seen.idxOf parent < seen.length := List.idxOf_lt_length_of_mem hparent
  have hclen : seen.idxOf child < seen.length := List.idxOf_lt_length_of_mem hchild
  have hlen : seen.length ≤ budget := by
    simpa [seen, runSlots] using lazyRun_seen_length_le answers default R []
  change seen.idxOf child < seen.idxOf parent
  by_contra horder
  have hij : seen.idxOf parent < seen.idxOf child + 1 := by omega
  let j : Fin budget := ⟨seen.idxOf child, hclen.trans_le hlen⟩
  have hidx : (runSlots T full answers).idxOf child = seen.idxOf child :=
    by obtain ⟨suffix, hs⟩ := hpref; rw [← hs, List.idxOf_append_of_mem hchild]
  have hget : seen[seen.idxOf parent]? = some parent := List.getElem?_idxOf hparent
  have hy : runOracle T full answers child = answers ⟨j.val, j.isLt.trans_le hbudget⟩ := by
    rw [runOracle, hidx, tapeAt, dif_pos (j.isLt.trans_le hbudget)]
  apply hfree
  rcases hanswer with h | h
  · let k : ForwardIndex budget := ⟨j, ⟨seen.idxOf parent, hij⟩, false⟩
    refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [forwardTarget_eq]
    change answers ⟨j.val, j.isLt.trans_le hbudget⟩ =
      namedChild decodeNode seen[seen.idxOf parent]? false
    rw [← hy, h, hget]
    simp [namedChild, hlabels]
  · let k : ForwardIndex budget := ⟨j, ⟨seen.idxOf parent, hij⟩, true⟩
    refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [forwardTarget_eq]
    change answers ⟨j.val, j.isLt.trans_le hbudget⟩ =
      namedChild decodeNode seen[seen.idxOf parent]? true
    rw [← hy, h, hget]
    simp [namedChild, hlabels]


section Adaptive

open Bcs.AdaptiveCommit
open Merkle.RandomOracle.TwoOracleTree

variable {Pt Challenge Out Key : Type} [DecidableEq Pt] [DecidableEq Key]
  [DecidableEq D] [Fintype Challenge] [Inhabited Salt] [Inhabited M]
  {N L TC fc : ℕ}
variable (S : Setup Enc D Pt Challenge Out Key budget N L)

omit [DecidableEq D] [Inhabited Salt] [Inhabited M] in
/-- A missing verifier input is covered by the existing fresh-hit family, even if the
deterministic extraction happens to explain the opening. -/
private theorem missingInput_hit (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hL : 0 < L) (hF : fc + budget ≤ T) (mt : Fin T → D) (ct : Fin TC → Challenge)
    (hacc : S.MerkleAccepts codec check rootOf claimOf mt ct)
    (hfresh : ∃ x ∈ checkTraceQueries (codec.withOracle (S.merkleOracle check mt ct)) n
      (claimOf (S.output mt ct).1).I (claimOf (S.output mt ct).1).a (claimOf (S.output mt ct).1).pf,
      x ∉ runSlots T (S.cutRun ct (S.cutIdx mt ct (S.keyOut (S.output mt ct).1))) mt) :
    HitFamily T (Setup.hits fc budget (L + N)) (Setup.hitSlot hF)
      (S.hitTarget codec dec rootOf ct hF) mt := by
  classical
  set out := (S.output mt ct).1
  set jCut := S.cutIdx mt ct (S.keyOut out)
  have hi : jCut < (S.fsSeen mt ct).length := S.cutIdx_lt mt ct hL
  set commit := S.cutRun ct jCut with hcommit
  set R := S.merkleRun check ct
  let cutRoot : Option Pt → D := fun o => o.elim default (rootOf ∘ S.key)
  have hprefA := S.cutRun_seen_prefix mt ct jCut
  have hpref : (lazyRun mt default commit []).2.1 <+: runSlots T R mt :=
    hprefA.trans (lazyRun_seen_prefix_bind mt default _ _ [])
  have hkeyi : S.key ((S.fsSeen mt ct)[jCut]'hi) = S.keyOut out :=
    of_decide_eq_true (List.findIdx_getElem (xs := S.fsSeen mt ct)
      (p := fun q => decide (S.key q = S.keyOut out)) (w := hi))
  have hrt : rootOf (S.keyOut out) = cutRoot (lazyRun mt default commit []).1 := by
    rw [hcommit, S.cutRun_output, List.getElem?_eq_getElem hi]
    simp only [cutRoot, Option.elim, Function.comp, hkeyi]
  have hcheck' : ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf
      (2 * n) fun _ => default).run (runOracle T R mt)).2, qa ∈ (R.run (runOracle T R mt)).2 :=
    fun qa hqa => S.mem_merkleRun_trace check mt ct qa (hcheck _ out qa hqa)
  obtain ⟨x, hx, hxFresh⟩ := hfresh
  obtain ⟨⟨j, m⟩, hp, heq⟩ := hitFamily_of_fresh_generic_eligible codec dec n budget T commit cutRoot
    R mt (claimOf out) (rootOf (S.keyOut out)) hF hpref hrt hcheck' hacc
    ⟨x, hx, hxFresh⟩
  set jj : Fin T := ⟨j.val, j.isLt.trans_le hF⟩
  set neutral := Function.update mt jj default
  have hval : mt jj = candidateLabel codec dec cutRoot (lazyRun neutral default commit []) m := heq
  by_cases hm : m = 0
  · refine ⟨Sum.inr (j, jCut), Finset.inr_mem_disjSum.mpr (Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (hi.trans_le (S.fsSeen_length_le mt ct))⟩), ?_⟩
    rw [hm, candidateLabel_zero] at hval
    exact hval
  · have hprefN := S.cutRun_seen_prefix neutral ct jCut
    rw [candidateLabel_of_ne_zero codec dec cutRoot _ hm] at hval
    by_cases hlt : (m - 1) / 2 < (lazyRun neutral default commit []).2.1.length
    · refine ⟨Sum.inl (j, m), Finset.inl_mem_disjSum.mpr hp, ?_⟩
      show mt jj = candidateLabel codec dec (fun _ => default)
        (lazyRun neutral default (fixRight ct S.dflt S.joint []) []) m
      rw [candidateLabel_of_ne_zero codec dec _ _ hm, hval]
      congr 2
      rw [List.prefix_iff_eq_take.mp hprefN, List.getElem?_take_of_lt hlt]
    · refine ⟨Sum.inl (j, 0), Finset.inl_mem_disjSum.mpr (Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (by omega)⟩), ?_⟩
      show mt jj = candidateLabel codec dec (fun _ => default)
        (lazyRun neutral default (fixRight ct S.dflt S.joint []) []) 0
      rw [candidateLabel_zero, hval, List.getElem?_eq_none (by omega)]
      rfl

/-- The adaptive proof's existing two exceptions jointly cover both failed extraction and
every missing verifier input. This uses the same family and pays no additional guesses. -/
theorem explains_and_replays_of_good (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hL : 0 < L) (ht : budget ≤ T) (hF : fc + budget ≤ T)
    (mt : Fin T → D) (ct : Fin TC → Challenge)
    (hacc : S.MerkleAccepts codec check rootOf claimOf mt ct)
    (hcoll : ¬ PairCollision T (slotPairs T budget) mt)
    (hhit : ¬ HitFamily T (Setup.hits fc budget (L + N)) (Setup.hitSlot hF)
      (S.hitTarget codec dec rootOf ct hF) mt) :
    S.Explains dec rootOf claimOf mt ct ∧
      ∀ x ∈ checkTraceQueries (codec.withOracle (S.merkleOracle check mt ct)) n
        (claimOf (S.proof mt ct)).I (claimOf (S.proof mt ct)).a (claimOf (S.proof mt ct)).pf,
        x ∈ runSlots T (S.cutRun ct (S.cutIdx mt ct (S.keyOut (S.output mt ct).1))) mt := by
  classical
  constructor
  · by_contra hfail
    rcases S.cover codec dec check rootOf claimOf hcheck hL ht hF mt ct hacc hfail with h | h
    · exact hcoll h
    · exact hhit h
  · intro x hx
    by_contra h
    exact hhit (missingInput_hit n S codec dec check rootOf claimOf hcheck hL hF mt ct hacc
      ⟨x, hx, h⟩)


/-- The typed data for one authenticated opening in a joint verifier replay. -/
structure OpeningReplay (Salt M D Enc Out Key : Type) [Inhabited D] [DecidableEq Enc]
    (n : ℕ) (check : Out → Tree Enc D Unit fc) where
  codec : Codec Salt M D Enc
  dec : RoleDecoders codec
  rootOf : Key → D
  claimOf : Out → OpeningClaim n Salt M D
  replays : ∀ (H : Enc → D) (out : Out),
    ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
        fun _ => default).run H).2, qa ∈ ((check out).run H).2

variable [Inhabited Salt'] [Inhabited M'] {n' : ℕ}
variable {check : Out → Tree Enc D Unit fc}
variable (left : OpeningReplay Salt M D Enc Out Key n check)
  (right : OpeningReplay Salt' M' D Enc Out Key n' check)

/-- Both typed openings share a collision family. Only the first field needs the
path ordering bound, so there is one forward-hit family. -/
def adaptiveMerkleException (hF : fc + budget ≤ T)
    (mt : Fin T → D) (ct : Fin TC → Challenge) : Prop :=
  let ht : budget ≤ T := Nat.le_trans (Nat.le_add_left _ _) hF
  PairCollision T (slotPairs T budget) mt ∨
    HitFamily T (Setup.hits fc budget (L + N)) (Setup.hitSlot hF)
      (S.hitTarget left.codec left.dec left.rootOf ct hF) mt ∨
    HitFamily T (Setup.hits fc budget (L + N)) (Setup.hitSlot hF)
      (S.hitTarget right.codec right.dec right.rootOf ct hF) mt ∨
    HitFamily T Finset.univ (forwardSlot ht)
      (forwardTarget left.dec.nodeDec (fixRight ct S.dflt S.joint []) ht) mt

/-- On the complement of the enlarged Merkle exception, both openings are explained and
v7's distinguishing leaf lengths force thirteen actual adversary queries. -/
theorem explains_and_work_of_good (hL : 0 < L) (hF : fc + budget ≤ T)
    (mt : Fin T → D) (ct : Fin TC → Challenge)
    (hleft : S.MerkleAccepts left.codec check left.rootOf left.claimOf mt ct)
    (hright : S.MerkleAccepts right.codec check right.rootOf right.claimOf mt ct)
    (hne : ¬ adaptiveMerkleException n S left right hF mt ct)
    (hsize : 2048 ≤ n)
    (hleftOpen : (left.claimOf (S.proof mt ct)).I.Nonempty)
    (hrightOpen : (right.claimOf (S.proof mt ct)).I.Nonempty)
    (inputLength : Enc → ℕ) (leafLen leafLen' nodeLen : ℕ)
    (hll : leafLen' ≠ leafLen) (hln : leafLen' ≠ nodeLen)
    (hl : ∀ sm, inputLength (left.codec.leafEnc sm) = leafLen)
    (hnl : ∀ labels, inputLength (left.codec.nodeEnc labels) = nodeLen)
    (hl' : ∀ sm, inputLength (right.codec.leafEnc sm) = leafLen') :
    S.Explains left.dec left.rootOf left.claimOf mt ct ∧
    S.Explains right.dec right.rootOf right.claimOf mt ct ∧
    13 ≤ (runSlots T (fixRight ct S.dflt S.joint []) mt).length := by
  have ht : budget ≤ T := by omega
  have hcoll : ¬ PairCollision T (slotPairs T budget) mt := fun h => hne (Or.inl h)
  have ⟨hleftExp, hleftReplay⟩ := explains_and_replays_of_good n S left.codec left.dec
    check left.rootOf left.claimOf left.replays hL ht hF mt ct hleft hcoll
      (fun h => hne (Or.inr (Or.inl h)))
  have ⟨hrightExp, hrightReplay⟩ := explains_and_replays_of_good n' S right.codec right.dec
    check right.rootOf right.claimOf right.replays hL ht hF mt ct hright hcoll
      (fun h => hne (Or.inr (Or.inr (Or.inl h))))
  refine ⟨hleftExp, hrightExp, ?_⟩
  obtain ⟨i, hi⟩ := hleftOpen
  obtain ⟨i', hi'⟩ := hrightOpen
  let adv := fixRight ct S.dflt S.joint []
  have horder := orderedChildren_of_noForward left.dec.nodeDec adv (S.merkleRun check ct)
    ht mt (lazyRun_seen_prefix_bind mt default _ _ [])
    (fun h => hne (Or.inr (Or.inr (Or.inr h))))
  have hprefix := S.cutRun_seen_prefix mt ct (S.cutIdx mt ct (S.keyOut (S.proof mt ct)))
  exact twoFieldQueryFloor left.codec (S.merkleOracle check mt ct) n _ _ _ i hi
    right.codec n' _ _ _ i' hi' left.dec (runSlots T adv mt)
    (fun x hx => List.IsPrefix.subset hprefix (hleftReplay x hx))
    (fun x hx => List.IsPrefix.subset hprefix (hrightReplay x hx))
    horder hsize inputLength leafLen leafLen' nodeLen hll hln hl hnl hl'

/-- The joint Merkle exception's numerator, for fixed challenge tape. -/
def adaptiveMerkleNumerator (fc budget len : ℕ) : ℕ :=
  budget * (budget - 1) / 2 +
    2 * ((fc + budget) * (2 * budget + 1) + (fc + budget) * len) +
    budget * (budget + 1)

open scoped Classical in
omit [DecidableEq Key] [Fintype Challenge] [Inhabited Salt] [Inhabited M]
  [Inhabited Salt'] [Inhabited M'] in
theorem adaptiveMerkleException_card [Fintype D] (hF : fc + budget ≤ T)
    (ct : Fin TC → Challenge) :
    (Finset.univ.filter fun mt => adaptiveMerkleException n S left right hF mt ct).card
      ≤ adaptiveMerkleNumerator fc budget (L + N) * Fintype.card D ^ (T - 1) := by
  classical
  have ht : budget ≤ T := by omega
  let coll := Finset.univ.filter (PairCollision (D := D) T (slotPairs T budget))
  let leftHit := Finset.univ.filter (HitFamily T (Setup.hits fc budget (L + N)) (Setup.hitSlot hF)
    (S.hitTarget left.codec left.dec left.rootOf ct hF))
  let rightHit := Finset.univ.filter (HitFamily T (Setup.hits fc budget (L + N)) (Setup.hitSlot hF)
    (S.hitTarget right.codec right.dec right.rootOf ct hF))
  let forward := Finset.univ.filter (HitFamily T Finset.univ (forwardSlot ht)
    (forwardTarget left.dec.nodeDec (fixRight ct S.dflt S.joint []) ht))
  have heq : (Finset.univ.filter fun mt => adaptiveMerkleException n S left right hF mt ct) =
      coll ∪ (leftHit ∪ (rightHit ∪ forward)) := by
    ext mt
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_union, true_and, coll, leftHit,
      rightHit, forward, adaptiveMerkleException]
  have hcoll := (answerTape_pairCollision_card_le (D := D) T (slotPairs T budget)
    slotPairs_distinct).trans (Nat.mul_le_mul_right _ (slotPairs_card_le T budget))
  have hleft := answerTape_hitFamily_card_le T (Setup.hits fc budget (L + N)) (Setup.hitSlot hF)
    (S.hitTarget left.codec left.dec left.rootOf ct hF)
    (fun k _ => S.hitTarget_isHitTarget left.codec left.dec left.rootOf ct hF k)
  have hright := answerTape_hitFamily_card_le T (Setup.hits fc budget (L + N)) (Setup.hitSlot hF)
    (S.hitTarget right.codec right.dec right.rootOf ct hF)
    (fun k _ => S.hitTarget_isHitTarget right.codec right.dec right.rootOf ct hF k)
  have hforward := forward_card_le left.dec.nodeDec (fixRight ct S.dflt S.joint []) ht
  rw [heq]
  calc
    _ ≤ coll.card + (leftHit.card + (rightHit.card + forward.card)) := by
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)) _)
    _ ≤ _ := by
      rw [Setup.hits_card] at hleft hright
      unfold adaptiveMerkleNumerator
      rw [add_mul, add_mul, two_mul, add_mul, add_assoc, add_assoc]
      exact Nat.add_le_add hcoll (Nat.add_le_add hleft (Nat.add_le_add hright hforward))


open scoped Classical in
omit [DecidableEq Key] [Inhabited Salt] [Inhabited M] [Inhabited Salt'] [Inhabited M'] in
/-- The joint Merkle count on the product of the Merkle and challenge tapes. -/
theorem adaptiveMerkleException_prod_card [Fintype D] (hF : fc + budget ≤ T) :
    (Finset.univ.filter fun tapes : (Fin T → D) × (Fin TC → Challenge) =>
      adaptiveMerkleException n S left right hF tapes.1 tapes.2).card
      ≤ Fintype.card Challenge ^ TC *
        (adaptiveMerkleNumerator fc budget (L + N) * Fintype.card D ^ (T - 1)) := by
  classical
  rw [Bcs.card_filter_prod_snd]
  calc
    _ ≤ ∑ _ct : Fin TC → Challenge,
          adaptiveMerkleNumerator fc budget (L + N) * Fintype.card D ^ (T - 1) :=
      Finset.sum_le_sum fun ct _ => adaptiveMerkleException_card n S left right hF ct
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

end Adaptive

/-- A coarse bound valid for all the v7 combined replay fuels and schedule lengths. -/
theorem adaptiveMerkleNumerator_le_v7 (fc L N budget : ℕ) (hfc : fc ≤ 14000) (hL : L ≤ 1200) :
    adaptiveMerkleNumerator fc budget (L + N) ≤
      6 * (1 + N + budget)^2 + 2^26 * (1 + N + budget) := by
  let total := 1 + N + budget
  have htot : 1 ≤ total := by omega
  have htQ : budget ≤ total := by omega
  have hpair : budget * (budget - 1) / 2 ≤ total * total := by
    apply (Nat.div_le_self _ _).trans
    exact Nat.mul_le_mul htQ (by omega)
  have hforward : budget * (budget + 1) ≤ total * (total + 1) :=
    Nat.mul_le_mul htQ (by omega)
  have hmain : 2 * ((fc + budget) * (2 * budget + 1) + (fc + budget) * (L + N))
      ≤ 2 * ((14000 + total) * (2 * total + 1201)) := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  unfold adaptiveMerkleNumerator
  calc
    _ ≤ total * total + 2 * ((14000 + total) * (2 * total + 1201)) + total * (total + 1) :=
      Nat.add_le_add (Nat.add_le_add hpair hmain) hforward
    _ = 6 * total^2 + 58403 * total + 33628000 := by ring
    _ ≤ 6 * total^2 + 2^26 * total := by
      have hconstant : 33628000 ≤ 33628000 * total := by
        simpa using Nat.mul_le_mul_left 33628000 htot
      omega

end LfzkV1.MerkleWork125
