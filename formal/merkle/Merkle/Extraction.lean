import Mathlib.Tactic.Ring.RingNF
import Merkle.Collision
import Merkle.Trapdoor

/-!
# Extraction: role decoders and the materialized check trace

Item 2 of `README.md`'s implementation order.  Two pieces of machinery that every
extraction result downstream needs:

* **`RoleDecoders`** — executable partial inverses of the two role encodings, with
  round-trip laws (decoding an honest encoding succeeds) and soundness laws (a
  successful decode is a genuine preimage).  The round-trip laws alone imply the
  same-role injectivity `Codec.Inj`.

* **`checkTraceQueries` / `checkTraceList`** — the materialized query trace of a core
  check: every oracle input `checkValues` can present, as data rather than as the
  predicate `InIndexTrace`.

This is the vocabulary `ExtractionROM`'s three-event cover counts.
-/

open Finset Nat Heap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

universe uSalt uMsg uDigest uEnc

variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest}
variable {Enc : Type uEnc}

/-! ## Role decoders -/

/-- Executable partial inverses of the two role encodings.

The round-trip laws say honest encodings always decode; the soundness laws say a
successful decode is always a genuine preimage.  Heap position, not range
disjointness, selects which decoder the extractor applies — the two roles may
overlap as encodings (they do at 32-byte leaf payloads). -/
structure RoleDecoders (C : Codec Salt M D Enc) where
  leafDec : Enc → Option (Salt × M)
  nodeDec : Enc → Option (D × D)
  leaf_roundTrip : ∀ sm, leafDec (C.leafEnc sm) = some sm
  node_roundTrip : ∀ dd, nodeDec (C.nodeEnc dd) = some dd
  leaf_sound : ∀ x sm, leafDec x = some sm → C.leafEnc sm = x
  node_sound : ∀ x dd, nodeDec x = some dd → C.nodeEnc dd = x

/-- The round-trip laws imply same-role injectivity: the decoders witness an
inverse on each role's range. -/
theorem RoleDecoders.inj {C : Codec Salt M D Enc} (dec : RoleDecoders C) :
    C.Inj := by
  constructor
  · intro sm₀ sm₁ heq
    have h₀ := congrArg dec.leafDec heq
    rw [dec.leaf_roundTrip, dec.leaf_roundTrip] at h₀
    exact Option.some_inj.mp h₀
  · intro dd₀ dd₁ heq
    have h₀ := congrArg dec.nodeDec heq
    rw [dec.node_roundTrip, dec.node_roundTrip] at h₀
    exact Option.some_inj.mp h₀

variable (S : Scheme Salt M D Enc) [Inhabited D]

/-! ## The materialized check trace -/

/-- Every oracle input the core check `checkValues` presents: one leaf input per
opened index, and one node input per internal path vertex.  This is `InIndexTrace`
turned from a predicate into data, uniformly over all opened indices. -/
def checkTraceQueries [DecidableEq Enc]
    (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) : Finset Enc :=
  (I.attach.image fun ⟨i, hi⟩ => S.leafEnc (pf.nonce ⟨i, hi⟩, a i)) ∪
    ((Heap.pathSet n I).filter (fun v => 0 < v ∧ v < n)).image fun v =>
      S.nodeEnc (checkValues S n I a pf (2 * v),
        checkValues S n I a pf (2 * v + 1))

/-- The materialized check trace as a list of query-answer pairs: every trace
query paired with the answer the scheme's hash gives it. -/
noncomputable def checkTraceList [DecidableEq Enc]
    (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) : List (Enc × D) :=
  (checkTraceQueries S n I a pf).toList.map fun q => (q, S.H q)

/-! ## The partial-tree extractor -/

variable {C : Codec Salt M D Enc}

/-- The extractor's working knowledge: partial labels, nonces and messages.
`none` means "no preimage was found in the trace". -/
structure ExtractState (n : ℕ) (Salt D M : Type*) where
  label : ℕ → Option D
  nonce : Fin n → Option Salt
  message : Fin n → Option M

/-- The descent's initial state: only the root carries a label, `rt`. -/
def initialState (n : ℕ) (Salt D M : Type*) (rt : D) :
    ExtractState n Salt D M :=
  { label := fun v => if v = 1 then some rt else none
    nonce := fun _ => none
    message := fun _ => none }

/-- One extractor step at vertex `v`: if the label there is known, find the
first trace pair carrying it as an answer and decode — at an internal vertex,
assigning the two child labels; at a leaf, assigning the nonce and message.
Vertices are processed in index order, parents before children, so one pass
saturates. -/
def ExtractState.step (dec : RoleDecoders C) [DecidableEq D]
    (tr : List (Enc × D)) (n v : ℕ) (s : ExtractState n Salt D M) :
    ExtractState n Salt D M :=
  match hlabel : s.label v with
  | none => s
  | some d =>
      match List.find? (fun qa : Enc × D => qa.2 = d) tr with
      | none => s
      | some qa =>
          if hv : v < n then
            match dec.nodeDec qa.1 with
            | some (l, r) =>
                let newLabel := Function.update
                  (Function.update s.label (2 * v) (some l))
                  (2 * v + 1) (some r)
                { s with label := newLabel }
            | none => s
          else if hleaf : n ≤ v ∧ v < 2 * n then
            match dec.leafDec qa.1 with
            | some (salt, m) =>
                let i : Fin n := ⟨v - n, by omega⟩
                { s with nonce := Function.update s.nonce i (some salt),
                         message := Function.update s.message i (some m) }
            | none => s
          else s

/-- The top-down descent: process vertices `1, 2, …, k`, in index order. -/
def descend (dec : RoleDecoders C) [DecidableEq D] (n : ℕ)
    (tr : List (Enc × D)) :
    ℕ → ExtractState n Salt D M → ExtractState n Salt D M
  | 0, s => s
  | k + 1, s => ExtractState.step dec tr n (k + 1) (descend dec n tr k s)

/-- What the extractor produces: a stored-label trapdoor and a total message,
gaps filled with defaults. -/
structure Extracted (n : ℕ) (Salt M D : Type*) where
  trapdoor : Trapdoor n Salt D
  message : Fin n → M

/-- The partial-tree extractor (README §Extractor construction).  Rejects when
the claimed root is not an answer of the trace; otherwise runs the descent from
the root-labelled initial state and fills the gaps with defaults. -/
noncomputable def extract (dec : RoleDecoders C) [DecidableEq D]
    [Inhabited Salt] [Inhabited M] (n : ℕ) (rt : D)
    (tr : List (Enc × D)) : Option (Extracted n Salt M D) := by
  classical
  exact if hroot : ∃ q, (q, rt) ∈ tr then
    let s₀ : ExtractState n Salt D M :=
      { label := fun v => if v = 1 then some rt else none
        nonce := fun _ => none
        message := fun _ => none }
    let s := descend dec n tr (2 * n - 1) s₀
    let td : Trapdoor n Salt D :=
      { nonce := fun i => (s.nonce i).elim default id
        label := fun v _ => (s.label v).elim default id }
    some { trapdoor := td, message := fun i => (s.message i).elim default id }
  else none

omit [Inhabited D] in
/-- The extractor is sound on labels: every label the descent knows is derived
from the root by a chain of trace decodings.  This is the invariant everything
downstream uses — the deterministic extraction theorems read it against a
collision-free trace, where the derivation chain is unique. -/
private theorem find?_answer_mem [DecidableEq D] (tr : List (Enc × D)) (d : D)
    (qa : Enc × D)
    (h : List.find? (fun qa : Enc × D => qa.2 = d) tr = some qa) :
    qa ∈ tr ∧ qa.2 = d := by
  have hiff :=
    (List.find?_eq_some_iff_getElem
      (p := fun qa : Enc × D => decide (qa.2 = d))).mp h
  obtain ⟨hpred, i, hi, hget, _⟩ := hiff
  exact ⟨hget ▸ List.getElem_mem hi, by simpa using hpred⟩

omit [Inhabited D] in
/-- Away from the two children of the processed vertex, a step leaves every
label unchanged: the descent only ever *adds* child labels, never disturbs
existing knowledge. -/
private theorem step_label_of_ne (dec : RoleDecoders C) [DecidableEq D]
    (tr : List (Enc × D)) (n v u : ℕ) (s : ExtractState n Salt D M)
    (hu : u ≠ 2 * v ∧ u ≠ 2 * v + 1) :
    (ExtractState.step dec tr n v s).label u = s.label u := by
  dsimp [ExtractState.step]
  split
  · rfl
  · split
    · rfl
    · split
      · split
        · dsimp
          rw [Function.update_apply, Function.update_apply]
          split_ifs with h₁ h₂
          · omega
          · omega
          · rfl
        · rfl
      · split
        · split
          · rfl
          · rfl
        · rfl

/-! ## Complete honest traces: the deterministic core

The completeness side of extraction.  A trace is *sound* when every pair is a
genuine query–answer of the scheme's hash, and *collision-free* when equal
answers come only from equal encoded inputs.  Under the latter, an answer
determines its query, which is what makes the descent's `find?` deterministic.
`CompleteDerivation` says the trace carries the entire honest derivation of the
root. -/

/-- Every pair in the trace is a genuine query–answer of the scheme's hash. -/
def TraceSound (S : Scheme Salt M D Enc) (tr : List (Enc × D)) : Prop :=
  ∀ qa ∈ tr, qa.2 = S.H qa.1

/-- No answer collisions: equal answers in the trace come from equal encoded
inputs.  Under this hypothesis an answer determines its query. -/
def CollisionFree (tr : List (Enc × D)) : Prop :=
  ∀ qa₀ ∈ tr, ∀ qa₁ ∈ tr, qa₀.2 = qa₁.2 → qa₀.1 = qa₁.1

/-- The trace carries the entire honest derivation of `rt`: the leaf
query–answer of every leaf and the node query–answer of every internal vertex,
with `rt` the honest root. -/
def CompleteDerivation (S : Scheme Salt M D Enc)
    (n : ℕ) (nonce : Fin n → Salt) (m : Fin n → M) (rt : D)
    (tr : List (Enc × D)) : Prop :=
  rt = root S n nonce m ∧
  (∀ i : Fin n,
    (S.leafEnc (nonce i, m i), commitLabels S n nonce m (n + i.val)) ∈ tr) ∧
  ∀ v : ℕ, 0 < v → v < n →
    (S.nodeEnc (commitLabels S n nonce m (2 * v),
       commitLabels S n nonce m (2 * v + 1)),
      commitLabels S n nonce m v) ∈ tr

omit [Inhabited D] in
/-- Under a collision-free trace, `find?` for an answer returns the unique
query carrying that answer: any other trace pair with the same answer has the
same encoded input. -/
theorem find?_answer_unique [DecidableEq D] (tr : List (Enc × D))
    (hfree : CollisionFree tr) (d : D) (qa : Enc × D)
    (hfind : List.find? (fun qa : Enc × D => qa.2 = d) tr = some qa)
    (qa' : Enc × D) (hqa' : qa' ∈ tr) (hans : qa'.2 = d) :
    qa'.1 = qa.1 := by
  have ⟨hqamem, hqans⟩ := find?_answer_mem tr d qa hfind
  exact hfree qa' hqa' qa hqamem (by rw [hans, hqans])

omit [Inhabited D] in
/-- Reduction of `step` when the label is present, the trace lookup succeeds,
and the vertex is internal: the result is the state with the two child labels
updated. -/
private theorem step_eq_internal [DecidableEq D]
    (dec : RoleDecoders C) (tr : List (Enc × D)) (n v : ℕ)
    (s : ExtractState n Salt D M) (d : D) (qa : Enc × D) (l r : D)
    (hlabel : s.label v = some d)
    (hfind : List.find? (fun qa : Enc × D => qa.2 = d) tr = some qa)
    (hvn : v < n)
    (hdec : dec.nodeDec qa.1 = some (l, r)) :
    ExtractState.step dec tr n v s =
      ({ s with label := Function.update (Function.update s.label (2 * v) (some l)) (2 * v + 1) (some r) } : ExtractState n Salt D M) := by
  dsimp [ExtractState.step]
  split
  · rename_i hnone
    cases hlabel.symm.trans hnone
  · rename_i d' hslabel
    have hdd : d' = d := Option.some_inj.mp (hslabel.symm.trans hlabel)
    subst hdd
    split
    · rename_i hfnone
      cases hfind.symm.trans hfnone
    · rename_i qa' hsfind
      have hqae : qa' = qa := Option.some_inj.mp (hsfind.symm.trans hfind)
      subst hqae
      split
      · split
        · rename_i l' r' hdec'
          have hlr : (l', r') = (l, r) :=
            Option.some_inj.mp (hdec'.symm.trans hdec)
          cases hlr
          rfl
        · rename_i hdecnone
          cases hdec.symm.trans hdecnone
      · rename_i hnot
        exact absurd hvn hnot

omit [Inhabited D] in
/-- A step at an internal vertex whose label is `d` sets the two child labels to
`l` and `r`, provided the trace carries the node query–answer
`(nodeEnc (l, r), d)` for the vertex and is collision-free. -/
theorem step_sets_children [DecidableEq D]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n v : ℕ) (l r d : D) (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hnode : (S.nodeEnc (l, r), d) ∈ tr)
    (hvn : v < n)
    (s : ExtractState n Salt D M)
    (hlabel : s.label v = some d) :
    (ExtractState.step dec tr n v s).label (2 * v) = some l ∧
    (ExtractState.step dec tr n v s).label (2 * v + 1) = some r := by
  obtain ⟨qa, hfind⟩ :
      ∃ qa, List.find? (fun qa : Enc × D => qa.2 = d) tr = some qa := by
    cases h : List.find? (fun qa : Enc × D => qa.2 = d) tr
    · exact absurd (decide_eq_true (rfl : d = d))
        ((List.find?_eq_none.mp h) (S.nodeEnc (l, r), d) hnode)
    · rename_i qa
      exact ⟨qa, rfl⟩
  have hq1 : qa.1 = S.nodeEnc (l, r) :=
    (find?_answer_unique tr hfree d qa hfind (S.nodeEnc (l, r), d) hnode
      rfl).symm
  have hdec : dec.nodeDec qa.1 = some (l, r) := by
    rw [hq1]
    exact dec.node_roundTrip (l, r)
  have hstep := step_eq_internal dec tr n v s d qa l r hlabel hfind hvn hdec
  rw [hstep]
  dsimp only
  constructor
  · rw [Function.update_apply]
    split_ifs with hA
    · omega
    · rw [Function.update_apply]
      split_ifs with hB
      · rfl
      · omega
  · rw [Function.update_apply]
    split_ifs with hA
    · rfl
    · omega

omit [Inhabited D] in
/-- Reduction of `step` at a leaf vertex whose label is present and whose trace
lookup succeeds: the result is the state with the leaf's nonce and message
updated. -/
private theorem step_eq_leaf [DecidableEq D]
    (dec : RoleDecoders C) (tr : List (Enc × D)) (n v : ℕ)
    (s : ExtractState n Salt D M) (d : D) (qa : Enc × D) (salt : Salt)
    (msg : M)
    (hlabel : s.label v = some d)
    (hfind : List.find? (fun qa : Enc × D => qa.2 = d) tr = some qa)
    (hnv : ¬ v < n)
    (hrange : n ≤ v ∧ v < 2 * n)
    (hdec : dec.leafDec qa.1 = some (salt, msg)) :
    ExtractState.step dec tr n v s =
      ({ s with
         nonce := Function.update s.nonce ⟨v - n, by omega⟩ (some salt),
         message := Function.update s.message ⟨v - n, by omega⟩ (some msg) } :
        ExtractState n Salt D M) := by
  dsimp [ExtractState.step]
  split
  · rename_i hnone
    cases hlabel.symm.trans hnone
  · rename_i d' hslabel
    have hdd : d' = d := Option.some_inj.mp (hslabel.symm.trans hlabel)
    subst hdd
    split
    · rename_i hfnone
      cases hfind.symm.trans hfnone
    · rename_i qa' hsfind
      have hqae : qa' = qa := Option.some_inj.mp (hsfind.symm.trans hfind)
      subst hqae
      split
      · rename_i hlt
        exact absurd hlt hnv
      · rename_i hnot
        split
        · rename_i salt' msg' hdec'
          have heq : (salt', msg') = (salt, msg) :=
            Option.some_inj.mp (hdec'.symm.trans hdec)
          cases heq
          rfl
        · rename_i hdecnone
          cases hdec.symm.trans hdecnone

omit [Inhabited D] in
/-- A step at a leaf vertex `n + i` whose label is `d` sets the nonce and
message of leaf `i` to `salt` and `msg`, provided the trace carries the leaf
query–answer `(leafEnc (salt, msg), d)` and is collision-free. -/
theorem step_sets_leaf [DecidableEq D]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n : ℕ) (i : Fin n) (salt : Salt) (msg : M) (d : D) (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hleaf : (S.leafEnc (salt, msg), d) ∈ tr)
    (s : ExtractState n Salt D M)
    (hlabel : s.label (n + i.val) = some d) :
    (ExtractState.step dec tr n (n + i.val) s).nonce i = some salt ∧
    (ExtractState.step dec tr n (n + i.val) s).message i = some msg := by
  set v := n + i.val
  obtain ⟨qa, hfind⟩ :
      ∃ qa, List.find? (fun qa : Enc × D => qa.2 = d) tr = some qa := by
    cases h : List.find? (fun qa : Enc × D => qa.2 = d) tr
    · exact absurd (decide_eq_true (rfl : d = d))
        ((List.find?_eq_none.mp h) (S.leafEnc (salt, msg), d) hleaf)
    · rename_i qa
      exact ⟨qa, rfl⟩
  have hq1 : qa.1 = S.leafEnc (salt, msg) :=
    (find?_answer_unique tr hfree d qa hfind (S.leafEnc (salt, msg), d)
      hleaf rfl).symm
  have hdec : dec.leafDec qa.1 = some (salt, msg) := by
    rw [hq1]
    exact dec.leaf_roundTrip (salt, msg)
  have hnv : ¬ v < n := by dsimp [v]; omega
  have hrange : n ≤ v ∧ v < 2 * n := by
    dsimp [v]; constructor <;> omega
  have hstep := step_eq_leaf dec tr n v s d qa salt msg hlabel hfind
    hnv hrange hdec
  rw [hstep]
  dsimp only
  constructor
  · rw [Function.update_apply]
    split_ifs with hA
    · rfl
    · exact absurd (by apply Fin.ext; dsimp [v]; omega) hA
  · rw [Function.update_apply]
    split_ifs with hA
    · rfl
    · exact absurd (by apply Fin.ext; dsimp [v]; omega) hA

omit [Inhabited D] in
/-- Away from the leaf vertex `n + i`, a step leaves `nonce i` unchanged. -/
private theorem step_nonce_of_ne [DecidableEq D]
    (dec : RoleDecoders C) (tr : List (Enc × D)) (n w : ℕ)
    (s : ExtractState n Salt D M) (i : Fin n) (hw : w ≠ n + i.val) :
    (ExtractState.step dec tr n w s).nonce i = s.nonce i := by
  dsimp [ExtractState.step]
  split
  · rfl
  · split
    · rfl
    · split
      · split
        · rfl
        · rfl
      · rename_i hnot
        split
        · split
          · dsimp
            rw [Function.update_apply]
            split_ifs with h
            · exfalso
              apply hw
              have hv : i.val = w - n := by
                simpa using congrArg Fin.val h
              omega
            · rfl
          · rfl
        · rfl

omit [Inhabited D] in
/-- Away from the leaf vertex `n + i`, a step leaves `message i` unchanged. -/
theorem step_message_of_ne [DecidableEq D]
    (dec : RoleDecoders C) (tr : List (Enc × D)) (n w : ℕ)
    (s : ExtractState n Salt D M) (i : Fin n) (hw : w ≠ n + i.val) :
    (ExtractState.step dec tr n w s).message i = s.message i := by
  dsimp [ExtractState.step]
  split
  · rfl
  · split
    · rfl
    · split
      · split
        · rfl
        · rfl
      · rename_i hnot
        split
        · split
          · dsimp
            rw [Function.update_apply]
            split_ifs with h
            · exfalso
              apply hw
              have hv : i.val = w - n := by
                simpa using congrArg Fin.val h
              omega
            · rfl
          · rfl
        · rfl

/-- **Label completeness.**  Over a collision-free trace carrying the entire
honest derivation, the descent recovers every honest label: once a vertex's
parent has been processed, its label is the honest `commitLabels`, and it is
never disturbed afterwards. -/
theorem descend_complete_labels [DecidableEq D]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n : ℕ) (nonce : Fin n → Salt) (m : Fin n → M) (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hcomplete : CompleteDerivation S n nonce m (root S n nonce m) tr) :
    ∀ k v, v ∈ Heap.nodes n → v / 2 ≤ k →
      (descend dec n tr k
        (initialState n Salt D M (root S n nonce m))).label v =
        some (commitLabels S n nonce m v) := by
  intro k
  induction k with
  | zero =>
    intro v hv hle
    have hv1 : v = 1 := by
      rw [Heap.mem_nodes] at hv
      omega
    subst hv1
    dsimp [descend, initialState, root]
  | succ k ih =>
    intro v hv hle
    show (ExtractState.step dec tr n (k + 1)
        (descend dec n tr k
          (initialState n Salt D M (root S n nonce m)))).label v =
      some (commitLabels S n nonce m v)
    by_cases hchild : v = 2 * (k + 1) ∨ v = 2 * (k + 1) + 1
    · have hk1n : k + 1 < n := by
        rw [Heap.mem_nodes] at hv
        rcases hchild with hchild | hchild <;> omega
      have hk1nodes : k + 1 ∈ Heap.nodes n := by
        rw [Heap.mem_nodes] at hv
        rw [Heap.mem_nodes]
        omega
      have hplabel := ih (k + 1) hk1nodes (by omega)
      have hstep := step_sets_children S dec n (k + 1)
        (commitLabels S n nonce m (2 * (k + 1)))
        (commitLabels S n nonce m (2 * (k + 1) + 1))
        (commitLabels S n nonce m (k + 1)) tr hfree
        (hcomplete.2.2 (k + 1) (by omega) hk1n) hk1n
        (descend dec n tr k
          (initialState n Salt D M (root S n nonce m))) hplabel
      rcases hchild with rfl | rfl
      · exact hstep.1
      · exact hstep.2
    · have hne : v ≠ 2 * (k + 1) ∧ v ≠ 2 * (k + 1) + 1 :=
        ⟨fun h => hchild (Or.inl h), fun h => hchild (Or.inr h)⟩
      rw [step_label_of_ne dec tr n (k + 1) v _ hne]
      exact ih v hv (by omega)

/-- **Leaf-data completeness.**  Over a collision-free complete trace, the
descent recovers the honest nonce and message of every leaf: step `n + i`
decodes leaf `i`'s query, and no other step touches nonce/message `i`. -/
theorem descend_complete_leaf_data [DecidableEq D]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n : ℕ) (nonce : Fin n → Salt) (m : Fin n → M) (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hcomplete : CompleteDerivation S n nonce m (root S n nonce m) tr) :
    ∀ i : Fin n,
      (descend dec n tr (2 * n - 1)
          (initialState n Salt D M (root S n nonce m))).nonce i =
        some (nonce i) ∧
      (descend dec n tr (2 * n - 1)
          (initialState n Salt D M (root S n nonce m))).message i =
        some (m i) := by
  intro i
  set v := n + i.val with hvdef
  have hvnodes : v ∈ Heap.nodes n := by
    rw [Heap.mem_nodes]
    omega
  have hvle : v ≤ 2 * n - 1 := by
    rw [Heap.mem_nodes] at hvnodes
    omega
  have hnonce : ∀ k, v ≤ k →
      (descend dec n tr k
        (initialState n Salt D M (root S n nonce m))).nonce i =
      some (nonce i) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk
      by_cases heq : v = k + 1
      · show (ExtractState.step dec tr n (k + 1)
            (descend dec n tr k
              (initialState n Salt D M (root S n nonce m)))).nonce i =
          some (nonce i)
        rw [← hvdef.symm.trans heq]
        exact (step_sets_leaf S dec n i (nonce i) (m i)
            (commitLabels S n nonce m v) tr hfree (hcomplete.2.1 i)
            (descend dec n tr k
              (initialState n Salt D M (root S n nonce m)))
            (descend_complete_labels S dec n nonce m tr hfree hcomplete k v
              hvnodes (by omega))).1
      · have hvk : v ≤ k := by omega
        show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
            (initialState n Salt D M (root S n nonce m)))).nonce i =
          some (nonce i)
        rw [step_nonce_of_ne dec tr n (k + 1)
            (descend dec n tr k
              (initialState n Salt D M (root S n nonce m))) i (by omega)]
        exact ih hvk
  have hmsg : ∀ k, v ≤ k →
      (descend dec n tr k
        (initialState n Salt D M (root S n nonce m))).message i =
      some (m i) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk
      by_cases heq : v = k + 1
      · show (ExtractState.step dec tr n (k + 1)
            (descend dec n tr k
              (initialState n Salt D M (root S n nonce m)))).message i =
          some (m i)
        rw [← hvdef.symm.trans heq]
        exact (step_sets_leaf S dec n i (nonce i) (m i)
            (commitLabels S n nonce m v) tr hfree (hcomplete.2.1 i)
            (descend dec n tr k
              (initialState n Salt D M (root S n nonce m)))
            (descend_complete_labels S dec n nonce m tr hfree hcomplete k v
              hvnodes (by omega))).2
      · have hvk : v ≤ k := by omega
        show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
            (initialState n Salt D M (root S n nonce m)))).message i =
          some (m i)
        rw [step_message_of_ne dec tr n (k + 1)
            (descend dec n tr k
              (initialState n Salt D M (root S n nonce m))) i (by omega)]
        exact ih hvk
  exact ⟨hnonce (2 * n - 1) hvle, hmsg (2 * n - 1) hvle⟩

/-- The node query–answer of an internal path vertex belongs to the materialized
check trace, with the answer the verifier's reconstructed value. -/
private lemma checkTraceList_node_mem [DecidableEq Enc]
    (S : Scheme Salt M D Enc) (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (v : ℕ) (hvp : v ∈ Heap.pathSet n I)
    (hv0 : 0 < v) (hvn : v < n) :
    (S.nodeEnc (checkValues S n I a pf (2 * v),
       checkValues S n I a pf (2 * v + 1)),
      checkValues S n I a pf v) ∈ checkTraceList S n I a pf := by
  set q := S.nodeEnc (checkValues S n I a pf (2 * v),
    checkValues S n I a pf (2 * v + 1))
  have hq_mem : q ∈ checkTraceQueries S n I a pf := by
    dsimp [checkTraceQueries]
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hvp, ⟨hv0, hvn⟩⟩
  have hlist : (q, S.H q) ∈ checkTraceList S n I a pf := by
    dsimp [checkTraceList]
    refine List.mem_map.mpr ⟨q, ?_, rfl⟩
    rwa [Finset.mem_toList]
  have hHq : S.H q = checkValues S n I a pf v := by
    rw [checkValues_node S n I a pf v ⟨hv0, hvn, hvp⟩]
  rw [hHq] at hlist
  exact hlist

/-- **Local recovery of the verifier's reconstruction.**  If an opening
`(I, a, pf)` is accepted at root `rt` and the check's entire query trace lies in
the collision-free commitment trace `tr`, then the descent from `rt` recovers
`checkValues` on every opened-path vertex. -/
theorem descend_recovers_checkValues [DecidableEq D] [DecidableEq Enc]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (pf : Opening n I Salt D)
    (rt : D) (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hacc : Accepts S n rt I a pf)
    (hsub : ∀ qa ∈ checkTraceList S n I a pf, qa ∈ tr) :
    ∀ k v, v ∈ Heap.pathSet n I → v / 2 ≤ k →
      (descend dec n tr k (initialState n Salt D M rt)).label v =
        some (checkValues S n I a pf v) := by
  intro k
  induction k with
  | zero =>
    intro v hv hle
    have hv1 : v = 1 := by
      have := Heap.pathSet_subset_nodes n I hv
      rw [Heap.mem_nodes] at this
      omega
    subst hv1
    dsimp [descend, initialState]
    rw [hacc.2]
  | succ k ih =>
    intro v hv hle
    show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
        (initialState n Salt D M rt))).label v =
      some (checkValues S n I a pf v)
    by_cases hchild : v = 2 * (k + 1) ∨ v = 2 * (k + 1) + 1
    · -- v is a child of k+1; step k+1 decodes the node query there
      have hk1path : k + 1 ∈ Heap.pathSet n I := by
        have hv1 : 1 < v := by
          rcases hchild with h | h <;> omega
        rw [Heap.mem_pathSet] at hv ⊢
        rcases hv with ⟨i, hi, hvi⟩
        refine ⟨i, hi, ?_⟩
        have := Heap.parent_mem_pathOf hvi hv1
        have hdiv : v / 2 = k + 1 := by
          rcases hchild with h | h <;> omega
        rwa [hdiv] at this
      have hk1n : k + 1 < n := by
        have := Heap.pathSet_subset_nodes n I hv
        rw [Heap.mem_nodes] at this
        rcases hchild with hchild | hchild <;> omega
      have hk10 : 0 < k + 1 := by omega
      have hplabel := ih (k + 1) hk1path (by omega)
      have hnode_tr : (S.nodeEnc (checkValues S n I a pf (2 * (k + 1)),
          checkValues S n I a pf (2 * (k + 1) + 1)),
          checkValues S n I a pf (k + 1)) ∈ tr :=
        hsub _ (checkTraceList_node_mem S n I a pf (k + 1) hk1path hk10 hk1n)
      have hstep := step_sets_children S dec n (k + 1)
        (checkValues S n I a pf (2 * (k + 1)))
        (checkValues S n I a pf (2 * (k + 1) + 1))
        (checkValues S n I a pf (k + 1)) tr hfree hnode_tr hk1n
        (descend dec n tr k (initialState n Salt D M rt)) hplabel
      rcases hchild with rfl | rfl
      · exact hstep.1
      · exact hstep.2
    · have hne : v ≠ 2 * (k + 1) ∧ v ≠ 2 * (k + 1) + 1 :=
        ⟨fun h => hchild (Or.inl h), fun h => hchild (Or.inr h)⟩
      rw [step_label_of_ne dec tr n (k + 1) v _ hne]
      exact ih v hv (by omega)

/-- **Recovery along one path.**  `descend_recovers_checkValues` asks for the check's *whole* trace
inside `tr`.  To recover the value at one opened-path vertex `v` it is enough that the node query of
every proper ancestor of `v` is there: the descent reaches `v` through those alone.  This is what lets
a fresh-hit target be indexed by heap vertex — the extractor's label at the first fresh vertex is the
value the fresh answer has to hit. -/
theorem descend_recovers_checkValues_of_ancestors [DecidableEq D] [DecidableEq Enc]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (pf : Opening n I Salt D)
    (rt : D) (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hroot : checkValues S n I a pf 1 = rt) :
    ∀ k v, v ∈ Heap.pathSet n I → v / 2 ≤ k →
      (∀ u m, 0 < m → v / 2 ^ m = u → 0 < u →
        (S.nodeEnc (checkValues S n I a pf (2 * u), checkValues S n I a pf (2 * u + 1)),
          checkValues S n I a pf u) ∈ tr) →
      (descend dec n tr k (initialState n Salt D M rt)).label v =
        some (checkValues S n I a pf v) := by
  intro k
  induction k with
  | zero =>
    intro v hv hle _
    have hv1 : v = 1 := by
      have := Heap.pathSet_subset_nodes n I hv
      rw [Heap.mem_nodes] at this
      omega
    subst hv1
    dsimp [descend, initialState]
    rw [hroot]
  | succ k ih =>
    intro v hv hle hanc
    show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
        (initialState n Salt D M rt))).label v =
      some (checkValues S n I a pf v)
    by_cases hchild : v = 2 * (k + 1) ∨ v = 2 * (k + 1) + 1
    · have hdiv : v / 2 = k + 1 := by rcases hchild with h | h <;> omega
      have hk1path : k + 1 ∈ Heap.pathSet n I := by
        have hv1 : 1 < v := by rcases hchild with h | h <;> omega
        rw [Heap.mem_pathSet] at hv ⊢
        rcases hv with ⟨i, hi, hvi⟩
        exact ⟨i, hi, by simpa [hdiv] using Heap.parent_mem_pathOf hvi hv1⟩
      have hk1n : k + 1 < n := by
        have := Heap.pathSet_subset_nodes n I hv
        rw [Heap.mem_nodes] at this
        rcases hchild with hchild | hchild <;> omega
      have hanc' : ∀ u m, 0 < m → (k + 1) / 2 ^ m = u → 0 < u →
          (S.nodeEnc (checkValues S n I a pf (2 * u), checkValues S n I a pf (2 * u + 1)),
            checkValues S n I a pf u) ∈ tr := by
        intro u m hm hu hu0
        refine hanc u (m + 1) (by omega) ?_ hu0
        rw [pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, hdiv, hu]
      have hplabel := ih (k + 1) hk1path (by omega) hanc'
      have hnode_tr := hanc (k + 1) 1 (by omega) (by simpa using hdiv) (by omega)
      have hstep := step_sets_children S dec n (k + 1)
        (checkValues S n I a pf (2 * (k + 1)))
        (checkValues S n I a pf (2 * (k + 1) + 1))
        (checkValues S n I a pf (k + 1)) tr hfree hnode_tr hk1n
        (descend dec n tr k (initialState n Salt D M rt)) hplabel
      rcases hchild with rfl | rfl
      · exact hstep.1
      · exact hstep.2
    · have hne : v ≠ 2 * (k + 1) ∧ v ≠ 2 * (k + 1) + 1 :=
        ⟨fun h => hchild (Or.inl h), fun h => hchild (Or.inr h)⟩
      rw [step_label_of_ne dec tr n (k + 1) v _ hne]
      exact ih v hv (by omega) hanc

/-- The leaf query–answer of an opened index belongs to the materialized check
trace, with the answer the verifier's reconstructed leaf value. -/
private lemma checkTraceList_leaf_mem [DecidableEq Enc]
    (S : Scheme Salt M D Enc) (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (i : Fin n) (hi : i ∈ I) :
    (S.leafEnc (pf.nonce ⟨i, hi⟩, a i),
      checkValues S n I a pf (n + i.val)) ∈ checkTraceList S n I a pf := by
  set q := S.leafEnc (pf.nonce ⟨i, hi⟩, a i)
  have hq_mem : q ∈ checkTraceQueries S n I a pf := by
    dsimp [checkTraceQueries]
    apply Finset.mem_union_left
    refine Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach I ⟨i, hi⟩, rfl⟩
  have hlist : (q, S.H q) ∈ checkTraceList S n I a pf := by
    dsimp [checkTraceList]
    refine List.mem_map.mpr ⟨q, ?_, rfl⟩
    rwa [Finset.mem_toList]
  have hHq : S.H q = checkValues S n I a pf (n + i.val) := by
    rw [checkValues_leaf S n I a pf i hi]
  rw [hHq] at hlist
  exact hlist

/-- **Local recovery of leaf data.**  Under the local-extraction hypotheses, the
descent recovers the claimed message and the proof's nonce at every opened
index. -/
theorem descend_recovers_leaf_data [DecidableEq D] [DecidableEq Enc]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (pf : Opening n I Salt D)
    (rt : D) (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hacc : Accepts S n rt I a pf)
    (hsub : ∀ qa ∈ checkTraceList S n I a pf, qa ∈ tr)
    (i : Fin n) (hi : i ∈ I) :
    (descend dec n tr (2 * n - 1) (initialState n Salt D M rt)).message i =
      some (a i) ∧
    (descend dec n tr (2 * n - 1) (initialState n Salt D M rt)).nonce i =
      some (pf.nonce ⟨i, hi⟩) := by
  set v := n + i.val with hvdef
  have hvpath : v ∈ Heap.pathSet n I :=
    Heap.mem_pathSet.mpr ⟨i, hi, Heap.leaf_mem_pathOf n i⟩
  have hleaf_tr : (S.leafEnc (pf.nonce ⟨i, hi⟩, a i),
      checkValues S n I a pf v) ∈ tr :=
    hsub _ (checkTraceList_leaf_mem S n I a pf i hi)
  have hvle : v ≤ 2 * n - 1 := by dsimp [v]; omega
  have hmsg : ∀ k, v ≤ k →
      (descend dec n tr k (initialState n Salt D M rt)).message i =
        some (a i) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk
      by_cases heq : v = k + 1
      · show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
          (initialState n Salt D M rt))).message i = some (a i)
        rw [← hvdef.symm.trans heq]
        exact (step_sets_leaf S dec n i (pf.nonce ⟨i, hi⟩) (a i)
            (checkValues S n I a pf v) tr hfree hleaf_tr
            (descend dec n tr k (initialState n Salt D M rt))
            (descend_recovers_checkValues S dec n I a pf rt tr hfree hacc
              hsub k v hvpath (by omega))).2
      · have hvk : v ≤ k := by omega
        show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
            (initialState n Salt D M rt))).message i = some (a i)
        rw [step_message_of_ne dec tr n (k + 1)
            (descend dec n tr k (initialState n Salt D M rt)) i (by omega)]
        exact ih hvk
  have hnonce : ∀ k, v ≤ k →
      (descend dec n tr k (initialState n Salt D M rt)).nonce i =
        some (pf.nonce ⟨i, hi⟩) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk
      by_cases heq : v = k + 1
      · show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
          (initialState n Salt D M rt))).nonce i = some (pf.nonce ⟨i, hi⟩)
        rw [← hvdef.symm.trans heq]
        exact (step_sets_leaf S dec n i (pf.nonce ⟨i, hi⟩) (a i)
            (checkValues S n I a pf v) tr hfree hleaf_tr
            (descend dec n tr k (initialState n Salt D M rt))
            (descend_recovers_checkValues S dec n I a pf rt tr hfree hacc
              hsub k v hvpath (by omega))).1
      · have hvk : v ≤ k := by omega
        show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
            (initialState n Salt D M rt))).nonce i = some (pf.nonce ⟨i, hi⟩)
        rw [step_nonce_of_ne dec tr n (k + 1)
            (descend dec n tr k (initialState n Salt D M rt)) i (by omega)]
        exact ih hvk
  exact ⟨hmsg (2 * n - 1) hvle, hnonce (2 * n - 1) hvle⟩

/-- **Frontier attachment.**  Under the local-extraction hypotheses, the
descent recovers the proof's frontier value at every frontier vertex. -/
theorem descend_recovers_frontier_label [DecidableEq D] [DecidableEq Enc]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (pf : Opening n I Salt D)
    (rt : D) (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hacc : Accepts S n rt I a pf)
    (hsub : ∀ qa ∈ checkTraceList S n I a pf, qa ∈ tr)
    (v : ℕ) (hv : v ∈ Heap.frontier n I) :
    (descend dec n tr (2 * n - 1) (initialState n Salt D M rt)).label v =
      some (pf.frontierValue ⟨v, hv⟩) := by
  rcases Heap.mem_frontier_iff.mp hv with ⟨hv1, hvnodes, hvnpath, hppath⟩
  set p := v / 2 with hpdef
  have hp0 : 0 < p := by dsimp [p]; omega
  have hpn : p < n := by
    dsimp [p]
    have := Heap.mem_nodes.mp hvnodes
    omega
  have hvchild : v = 2 * p ∨ v = 2 * p + 1 := by dsimp [p]; omega
  have hnode_tr : (S.nodeEnc (checkValues S n I a pf (2 * p),
      checkValues S n I a pf (2 * p + 1)), checkValues S n I a pf p) ∈ tr :=
    hsub _ (checkTraceList_node_mem S n I a pf p hppath hp0 hpn)
  have hlabel : ∀ k, p ≤ k →
      (descend dec n tr k (initialState n Salt D M rt)).label v =
        some (checkValues S n I a pf v) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk
      by_cases heq : p = k + 1
      · show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
          (initialState n Salt D M rt))).label v =
          some (checkValues S n I a pf v)
        rw [← heq]
        have hplabel := descend_recovers_checkValues S dec n I a pf rt tr
          hfree hacc hsub k p hppath (by omega)
        have hstep := step_sets_children S dec n p
          (checkValues S n I a pf (2 * p))
          (checkValues S n I a pf (2 * p + 1))
          (checkValues S n I a pf p) tr hfree hnode_tr hpn
          (descend dec n tr k (initialState n Salt D M rt)) hplabel
        rcases hvchild with hc | hc
        · rw [hc]; exact hstep.1
        · rw [hc]; exact hstep.2
      · show (ExtractState.step dec tr n (k + 1) (descend dec n tr k
          (initialState n Salt D M rt))).label v =
          some (checkValues S n I a pf v)
        have hne : v ≠ 2 * (k + 1) ∧ v ≠ 2 * (k + 1) + 1 := by
          constructor <;> intro h <;> rcases hvchild with hc | hc <;> omega
        rw [step_label_of_ne dec tr n (k + 1) v _ hne]
        exact ih (by omega)
  have hple : p ≤ 2 * n - 1 := by
    dsimp [p]
    have := Heap.mem_nodes.mp hvnodes
    omega
  rw [hlabel (2 * n - 1) hple]
  rw [checkValues_frontier S n I a pf v hv]

/-- **`mh_extract_complete` (README target, deterministic core).**  On a
collision-free trace carrying the entire honest derivation of the root, the
extractor succeeds and recovers the honest message, nonces, and every honest
heap label. -/
theorem mh_extract_complete [DecidableEq D] [Inhabited Salt] [Inhabited M]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n : ℕ) (hn : 0 < n) (nonce : Fin n → Salt) (m : Fin n → M)
    (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hcomplete : CompleteDerivation S n nonce m (root S n nonce m) tr) :
    ∃ out : Extracted n Salt M D,
      extract dec n (root S n nonce m) tr = some out ∧
      (∀ i, out.message i = m i) ∧
      (∀ i, out.trapdoor.nonce i = nonce i) ∧
      ∀ v (hv : v ∈ Heap.nodes n),
        out.trapdoor.label v hv = commitLabels S n nonce m v := by
  -- the root's preimage is in the trace, so the extractor does not reject
  have hroot : ∃ q, (q, root S n nonce m) ∈ tr := by
    by_cases hn1 : n = 1
    · subst hn1
      exact ⟨_, by simpa [root] using hcomplete.2.1 ⟨0, by omega⟩⟩
    · exact ⟨_, by simpa [root] using hcomplete.2.2 1 (by omega) (by omega)⟩
  set s := descend dec n tr (2 * n - 1)
    (initialState n Salt D M (root S n nonce m)) with hsdef
  set out : Extracted n Salt M D :=
    { trapdoor :=
        { nonce := fun i => (s.nonce i).elim default id
          label := fun v _ => (s.label v).elim default id }
      message := fun i => (s.message i).elim default id } with houtdef
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · dsimp [extract]
    rw [if_pos hroot]
    dsimp [out, s, initialState]
  · intro i
    dsimp [out, s]
    rw [(descend_complete_leaf_data S dec n nonce m tr hfree hcomplete i).2]
    simp
  · intro i
    dsimp [out, s]
    rw [(descend_complete_leaf_data S dec n nonce m tr hfree hcomplete i).1]
    simp
  · intro v hv
    dsimp [out, s]
    rw [descend_complete_labels S dec n nonce m tr hfree hcomplete
      (2 * n - 1) v hv (by rw [Heap.mem_nodes] at hv; omega)]
    simp

/-- **`mh_extract_explains_of_trace_subset` (README target, local extraction).**
If an opening `(I, a, pf)` is accepted at root `rt`, the trace is sound and
collision-free, and the check's entire query trace lies in the commitment trace,
then the extractor succeeds, recovers the claimed messages on `I`, and its
trapdoor opens `I` exactly as `pf`. -/
theorem mh_extract_explains_of_trace_subset
    [DecidableEq D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)
    (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (pf : Opening n I Salt D)
    (rt : D) (tr : List (Enc × D))
    (hfree : CollisionFree tr)
    (hacc : Accepts S n rt I a pf)
    (hsub : ∀ qa ∈ checkTraceList S n I a pf, qa ∈ tr) :
    ∃ out : Extracted n Salt M D,
      extract dec n rt tr = some out ∧
      (∀ i ∈ I, out.message i = a i) ∧
      openFromTrapdoor out.trapdoor I = pf := by
  -- the root's query–answer lies in the check trace, so the extractor does not
  -- reject
  have hroot : ∃ q, (q, rt) ∈ tr := by
    obtain ⟨i₀, hi₀⟩ := hacc.1
    by_cases h1n : 1 < n
    · have h1path : (1 : ℕ) ∈ Heap.pathSet n I :=
        Heap.root_mem_pathSet n hacc.1
      have := hsub _ (checkTraceList_node_mem S n I a pf 1 h1path
        (by omega) h1n)
      refine ⟨S.nodeEnc (checkValues S n I a pf 2,
        checkValues S n I a pf 3), ?_⟩
      rwa [← hacc.2]
    · have hn1 : n = 1 := by have := i₀.isLt; omega
      have hi0 : i₀.val = 0 := by have := i₀.isLt; omega
      have := hsub _ (checkTraceList_leaf_mem S n I a pf i₀ hi₀)
      refine ⟨S.leafEnc (pf.nonce ⟨i₀, hi₀⟩, a i₀), ?_⟩
      have hsum : n + i₀.val = 1 := by omega
      have hcv : checkValues S n I a pf (n + i₀.val) = rt := by
        rw [hsum]
        exact hacc.2
      rwa [← hcv]
  set s := descend dec n tr (2 * n - 1) (initialState n Salt D M rt)
    with hsdef
  set out : Extracted n Salt M D :=
    { trapdoor :=
        { nonce := fun i => (s.nonce i).elim default id
          label := fun v _ => (s.label v).elim default id }
      message := fun i => (s.message i).elim default id } with houtdef
  refine ⟨out, ?_, ?_, ?_⟩
  · dsimp [extract]
    rw [if_pos hroot]
    dsimp [out, s, initialState]
  · intro i hi
    dsimp [out, s]
    rw [(descend_recovers_leaf_data S dec n I a pf rt tr hfree hacc hsub
      i hi).1]
    simp
  · -- the trapdoor opens I exactly as pf: agree on nonces and frontier labels
    have hext : ∀ (x y : Opening n I Salt D),
        x.nonce = y.nonce → x.frontierValue = y.frontierValue → x = y := by
      intro x y h1 h2
      cases x; cases y; simp_all
    apply hext (openFromTrapdoor out.trapdoor I) pf
    · funext i
      dsimp [openFromTrapdoor, out, s]
      rw [(descend_recovers_leaf_data S dec n I a pf rt tr hfree hacc hsub
        i.val i.property).2]
      simp
    · funext v
      dsimp [openFromTrapdoor, out, s]
      rw [descend_recovers_frontier_label S dec n I a pf rt tr hfree hacc
        hsub v.val v.property]
      simp

/-! ## Trace-extension stability

The deterministic descent is stable under extending the trace: a label already
derived from a prefix is still derived (to the same value) from any extension.
This is the core of the ROM extraction argument — the opening phase's extra
queries cannot disturb what the commitment phase already determined, because
`find?` returns the *first* query carrying an answer and the prefix comes
first. -/

/-- `find?` is stable under appending: a query found in the prefix is still the
first match in the extension. -/
private lemma find?_append_of_some {α : Type*} (p : α → Bool)
    (tr tr' : List α) (qa : α) (h : List.find? p tr = some qa) :
    List.find? p (tr ++ tr') = some qa := by
  rw [List.find?_append, h]
  simp

omit [Inhabited D] in
/-- **Support bound.**  After `k` descent steps from a state labelled only at
the root, labels can occur only at vertices `≤ 2k + 1`: steps `1..k` set only
the children of `1..k`. -/
theorem descend_label_support [DecidableEq D]
    (dec : RoleDecoders C) (n : ℕ) (tr : List (Enc × D))
    (s₀ : ExtractState n Salt D M)
    (hs₀ : ∀ v, v ≠ 1 → s₀.label v = none) :
    ∀ k v, 2 * k + 1 < v → (descend dec n tr k s₀).label v = none := by
  intro k
  induction k with
  | zero =>
    intro v hv
    dsimp [descend]
    exact hs₀ v (by omega)
  | succ k ih =>
    intro v hv
    show (ExtractState.step dec tr n (k + 1)
      (descend dec n tr k s₀)).label v = none
    by_cases hchild : v = 2 * (k + 1) ∨ v = 2 * (k + 1) + 1
    · exfalso
      rcases hchild with hc | hc <;> omega
    · have hne : v ≠ 2 * (k + 1) ∧ v ≠ 2 * (k + 1) + 1 := by
        constructor
        · intro hc; apply hchild; exact Or.inl hc
        · intro hc; apply hchild; exact Or.inr hc
      rw [step_label_of_ne dec tr n (k + 1) v _ hne]
      exact ih v (by omega)

omit [Inhabited D] in
/-- **Nonce support bound.**  Leaf `i`'s nonce is written only by step `n + i`,
so after `k < n + i` steps from a state that knows no nonces it is still
unknown.  This is the nonce-side dual of `descend_label_support`, and it is what
turns "the descent produced a nonce" into "the step at `n + i` decoded". -/
theorem descend_nonce_support [DecidableEq D]
    (dec : RoleDecoders C) (n : ℕ) (tr : List (Enc × D))
    (s₀ : ExtractState n Salt D M)
    (hs₀ : ∀ i, s₀.nonce i = none) :
    ∀ k (i : Fin n), k < n + i.val →
      (descend dec n tr k s₀).nonce i = none := by
  intro k
  induction k with
  | zero =>
    intro i _
    dsimp [descend]
    exact hs₀ i
  | succ k ih =>
    intro i hk
    show (ExtractState.step dec tr n (k + 1)
      (descend dec n tr k s₀)).nonce i = none
    rw [step_nonce_of_ne dec tr n (k + 1) (descend dec n tr k s₀) i (by omega)]
    exact ih i (by omega)

omit [Inhabited D] in
/-- **Message support bound.**  The message half of `descend_nonce_support`. -/
theorem descend_message_support [DecidableEq D]
    (dec : RoleDecoders C) (n : ℕ) (tr : List (Enc × D))
    (s₀ : ExtractState n Salt D M)
    (hs₀ : ∀ i, s₀.message i = none) :
    ∀ k (i : Fin n), k < n + i.val →
      (descend dec n tr k s₀).message i = none := by
  intro k
  induction k with
  | zero =>
    intro i _
    dsimp [descend]
    exact hs₀ i
  | succ k ih =>
    intro i hk
    show (ExtractState.step dec tr n (k + 1)
      (descend dec n tr k s₀)).message i = none
    rw [step_message_of_ne dec tr n (k + 1) (descend dec n tr k s₀) i
      (by omega)]
    exact ih i (by omega)

omit [Inhabited D] in
private lemma update_child_left (f : ℕ → Option D) (w : ℕ) (l r : D) :
    Function.update (Function.update f (2 * w) (some l)) (2 * w + 1) (some r)
      (2 * w) = some l := by
  rw [Function.update_apply]
  split_ifs with h
  · omega
  · rw [Function.update_apply]
    split_ifs with h2
    · rfl
    · omega

omit [Inhabited D] in
private lemma update_child_right (f : ℕ → Option D) (w : ℕ) (l r : D) :
    Function.update (Function.update f (2 * w) (some l)) (2 * w + 1) (some r)
      (2 * w + 1) = some r := by
  rw [Function.update_apply]
  split_ifs with h
  · rfl
  · omega

omit [Inhabited D] in
/-- If two states agree on the label of an internal vertex `w`, and `find?`
returns the same query over `tr` and `tr ++ tr'`, then the two steps agree on
both child labels. -/
private lemma step_child_labels_eq [DecidableEq D]
    (dec : RoleDecoders C) (tr tr' : List (Enc × D)) (n w : ℕ) (hwn : w < n)
    (s s' : ExtractState n Salt D M) (dpar : D) (qa : Enc × D)
    (hs : s.label w = some dpar) (hs' : s'.label w = some dpar)
    (hfind : List.find? (fun qa : Enc × D => qa.2 = dpar) tr = some qa)
    (hfind_ext : List.find? (fun qa : Enc × D => qa.2 = dpar) (tr ++ tr') =
      some qa)
    (l r : D) (hlr : dec.nodeDec qa.1 = some (l, r)) :
    (ExtractState.step dec tr n w s).label (2 * w) =
      (ExtractState.step dec (tr ++ tr') n w s').label (2 * w) ∧
    (ExtractState.step dec tr n w s).label (2 * w + 1) =
      (ExtractState.step dec (tr ++ tr') n w s').label (2 * w + 1) := by
  have hstep_tr := step_eq_internal dec tr n w s dpar qa l r hs hfind hwn hlr
  have hstep_ext := step_eq_internal dec (tr ++ tr') n w s' dpar qa l r hs'
    hfind_ext hwn hlr
  constructor
  · rw [hstep_tr, hstep_ext]
    dsimp only
    rw [update_child_left, update_child_left]
  · rw [hstep_tr, hstep_ext]
    dsimp only
    rw [update_child_right, update_child_right]

omit [Inhabited D] in
/-- A step at a leaf vertex (`w ≥ n`) updates only the nonce and message, never
the labels. -/
private lemma step_label_unchanged_of_leaf [DecidableEq D]
    (dec : RoleDecoders C) (tr : List (Enc × D)) (n w : ℕ) (hwn : ¬ w < n)
    (s : ExtractState n Salt D M) (v : ℕ) :
    (ExtractState.step dec tr n w s).label v = s.label v := by
  dsimp [ExtractState.step]
  split
  · rfl
  · split
    · rfl
    · split
      · exfalso; exact hwn (by assumption)
      · split
        · split
          · rfl
          · rfl
        · rfl

omit [Inhabited D] in
/-- **Trace-extension stability for labels.**  A label derived from the prefix
`tr` is derived to the same value from the extension `tr ++ tr'`. -/
theorem descend_label_preserved_append [DecidableEq D]
    (dec : RoleDecoders C) (n : ℕ) (tr tr' : List (Enc × D))
    (s₀ : ExtractState n Salt D M)
    (hs₀ : ∀ v, v ≠ 1 → s₀.label v = none) :
    ∀ k v d, (descend dec n tr k s₀).label v = some d →
      (descend dec n (tr ++ tr') k s₀).label v = some d := by
  intro k
  induction k with
  | zero =>
    intro v d h
    dsimp [descend] at h ⊢
    exact h
  | succ k ih =>
    intro v d h
    dsimp [descend] at h ⊢
    by_cases hchild : v = 2 * (k + 1) ∨ v = 2 * (k + 1) + 1
    · by_cases hk1n : k + 1 < n
      · -- internal vertex k+1
        have hv_none : (descend dec n tr k s₀).label v = none :=
          descend_label_support dec n tr s₀ hs₀ k v (by
            rcases hchild with hc | hc <;> omega)
        by_cases hk1label : (descend dec n tr k s₀).label (k + 1) = none
        · -- parent unlabeled: step returns the state unchanged
          have hstep_id : ExtractState.step dec tr n (k + 1)
              (descend dec n tr k s₀) = descend dec n tr k s₀ := by
            dsimp [ExtractState.step]; rw [hk1label]
          rw [hstep_id] at h
          rw [hv_none] at h
          contradiction
        · obtain ⟨dpar, hdpar_eq⟩ : ∃ dpar, some dpar =
              (descend dec n tr k s₀).label (k + 1) :=
            Option.ne_none_iff_exists.mp hk1label
          have hdpar : (descend dec n tr k s₀).label (k + 1) = some dpar :=
            hdpar_eq.symm
          have hdpar_ext := ih (k + 1) dpar hdpar
          by_cases hfind : List.find? (fun qa : Enc × D => qa.2 = dpar) tr =
              none
          · have hstep_id : ExtractState.step dec tr n (k + 1)
                (descend dec n tr k s₀) = descend dec n tr k s₀ := by
              dsimp [ExtractState.step]; rw [hdpar]; dsimp; rw [hfind]
            rw [hstep_id] at h
            rw [hv_none] at h
            contradiction
          · obtain ⟨qa, hqa_eq⟩ : ∃ qa, some qa =
                List.find? (fun qa : Enc × D => qa.2 = dpar) tr :=
              Option.ne_none_iff_exists.mp hfind
            have hqa : List.find? (fun qa : Enc × D => qa.2 = dpar) tr =
                some qa := hqa_eq.symm
            have hqa_ext : List.find? (fun qa : Enc × D => qa.2 = dpar)
                (tr ++ tr') = some qa :=
              find?_append_of_some (fun qa : Enc × D => decide (qa.2 = dpar))
                tr tr' qa hqa
            by_cases hndec : dec.nodeDec qa.1 = none
            · have hstep_id : ExtractState.step dec tr n (k + 1)
                  (descend dec n tr k s₀) = descend dec n tr k s₀ := by
                dsimp [ExtractState.step]
                rw [hdpar]; dsimp
                rw [hqa]; dsimp
                split
                · rw [hndec]
                · contradiction
              rw [hstep_id] at h
              rw [hv_none] at h
              contradiction
            · obtain ⟨lr, hlr_eq⟩ : ∃ lr, some lr = dec.nodeDec qa.1 :=
                Option.ne_none_iff_exists.mp hndec
              rcases lr with ⟨l, r⟩
              have hlr : dec.nodeDec qa.1 = some (l, r) := hlr_eq.symm
              rcases hchild with hc | hc
              · rw [hc] at h ⊢
                have hagree := step_child_labels_eq dec tr tr' n (k + 1)
                  hk1n (descend dec n tr k s₀)
                  (descend dec n (tr ++ tr') k s₀) dpar qa hdpar hdpar_ext
                  hqa hqa_ext l r hlr
                rw [← hagree.1]
                exact h
              · rw [hc] at h ⊢
                have hagree := step_child_labels_eq dec tr tr' n (k + 1)
                  hk1n (descend dec n tr k s₀)
                  (descend dec n (tr ++ tr') k s₀) dpar qa hdpar hdpar_ext
                  hqa hqa_ext l r hlr
                rw [← hagree.2]
                exact h
      · -- k+1 is a leaf: step updates nonce/message only, labels unchanged
        have hleaf_tr := step_label_unchanged_of_leaf dec tr n (k + 1) hk1n
          (descend dec n tr k s₀) v
        rw [hleaf_tr] at h
        have hv_ext := ih v d h
        have hleaf_ext := step_label_unchanged_of_leaf dec (tr ++ tr') n
          (k + 1) hk1n (descend dec n (tr ++ tr') k s₀) v
        rw [hleaf_ext]
        exact hv_ext
    · have hne : v ≠ 2 * (k + 1) ∧ v ≠ 2 * (k + 1) + 1 := by
        constructor
        · intro hc; apply hchild; exact Or.inl hc
        · intro hc; apply hchild; exact Or.inr hc
      have hstr : (descend dec n tr k s₀).label v = some d := by
        rw [← step_label_of_ne dec tr n (k + 1) v _ hne]
        exact h
      have hv_ext := ih v d hstr
      rw [step_label_of_ne dec (tr ++ tr') n (k + 1) v _ hne]
      exact hv_ext

omit [Inhabited D] in
/-- A step either leaves *all* leaf data unchanged, or it decoded a leaf query
at `w` — the only way it can write a nonce or a message.  This is the converse
reading of `step_eq_leaf`: it lets a proof that starts from "the leaf data
changed" recover the decoding that changed it, without unfolding
`ExtractState.step` again. -/
private lemma step_leafData_eq_or_decoded [DecidableEq D]
    (dec : RoleDecoders C) (tr : List (Enc × D)) (n w : ℕ)
    (s : ExtractState n Salt D M) :
    ((∀ i, (ExtractState.step dec tr n w s).nonce i = s.nonce i) ∧
      (∀ i, (ExtractState.step dec tr n w s).message i = s.message i)) ∨
    ∃ d qa salt msg, s.label w = some d ∧
      List.find? (fun qa : Enc × D => qa.2 = d) tr = some qa ∧
      (¬ w < n) ∧ (n ≤ w ∧ w < 2 * n) ∧
      dec.leafDec qa.1 = some (salt, msg) := by
  dsimp [ExtractState.step]
  split
  · exact Or.inl ⟨fun _ => rfl, fun _ => rfl⟩
  · rename_i d hlabel
    split
    · exact Or.inl ⟨fun _ => rfl, fun _ => rfl⟩
    · rename_i qa hfind
      split
      · split
        · exact Or.inl ⟨fun _ => rfl, fun _ => rfl⟩
        · exact Or.inl ⟨fun _ => rfl, fun _ => rfl⟩
      · rename_i hnv
        split
        · rename_i hleaf
          split
          · rename_i salt msg hldec
            exact Or.inr ⟨d, qa, salt, msg, hlabel, hfind, hnv, hleaf, hldec⟩
          · exact Or.inl ⟨fun _ => rfl, fun _ => rfl⟩
        · exact Or.inl ⟨fun _ => rfl, fun _ => rfl⟩

omit [Inhabited D] in
/-- **Trace-extension stability for nonces.**  A nonce derived from the prefix
`tr` is derived to the same value from the extension `tr ++ tr'`. -/
theorem descend_nonce_preserved_append [DecidableEq D]
    (dec : RoleDecoders C) (n : ℕ) (tr tr' : List (Enc × D))
    (s₀ : ExtractState n Salt D M)
    (hs₀_label : ∀ v, v ≠ 1 → s₀.label v = none)
    (hs₀_nonce : ∀ i, s₀.nonce i = none) :
    ∀ k i salt, (descend dec n tr k s₀).nonce i = some salt →
      (descend dec n (tr ++ tr') k s₀).nonce i = some salt := by
  intro k
  induction k with
  | zero =>
    intro i salt h
    dsimp [descend] at h ⊢
    exact h
  | succ k ih =>
    intro i salt h
    dsimp [descend] at h ⊢
    by_cases heq : k + 1 = n + i.val
    · -- leaf step for leaf i; it decoded in tr, so it decodes the same in the
      -- extension (label stability + find?-stability)
      have hw_ge_n : n ≤ k + 1 := by omega
      have hw_lt_2n : k + 1 < 2 * n := by
        have := i.isLt
        omega
      have hi : i = (⟨k + 1 - n, by omega⟩ : Fin n) := by
        apply Fin.ext
        show (i : ℕ) = k + 1 - n
        omega
      -- before step `n + i` the nonce is unknown, so this step wrote it, so it
      -- decoded a leaf query
      have hnone : (descend dec n tr k s₀).nonce i = none :=
        descend_nonce_support dec n tr s₀ hs₀_nonce k i (by omega)
      rcases step_leafData_eq_or_decoded dec tr n (k + 1)
          (descend dec n tr k s₀) with
        ⟨hfix, -⟩ | ⟨leafval, qa, salt', msg', hleafval, hqa, hnv, hrange,
          hldec⟩
      · rw [hfix i, hnone] at h
        simp at h
      · -- label stability gives the same leaf value in the extension, and
        -- `find?` returns the same query there
        have hleafval_ext := descend_label_preserved_append dec n tr tr' s₀
          hs₀_label k (k + 1) leafval hleafval
        have hqa_ext : List.find? (fun qa : Enc × D => qa.2 = leafval)
            (tr ++ tr') = some qa :=
          find?_append_of_some (fun qa : Enc × D => decide (qa.2 = leafval))
            tr tr' qa hqa
        -- in tr the leaf step sets nonce i to salt'; h forces salt' = salt
        have hstep_tr := step_eq_leaf dec tr n (k + 1)
          (descend dec n tr k s₀) leafval qa salt' msg' hleafval hqa hnv
          hrange hldec
        have hnonce_tr : (ExtractState.step dec tr n (k + 1)
            (descend dec n tr k s₀)).nonce i = some salt' := by
          rw [hstep_tr]
          dsimp only
          rw [Function.update_apply]
          split_ifs with hi_eq
          · rfl
          · exact absurd hi hi_eq
        have hsalt_eq : salt' = salt :=
          Option.some_inj.mp (hnonce_tr.symm.trans h)
        -- in the extension the leaf step decodes the same query
        have hstep_ext := step_eq_leaf dec (tr ++ tr') n (k + 1)
          (descend dec n (tr ++ tr') k s₀) leafval qa salt' msg'
          hleafval_ext hqa_ext hnv hrange hldec
        rw [hstep_ext]
        dsimp only
        rw [Function.update_apply]
        split_ifs with hi_eq
        · rw [hsalt_eq]
        · exact absurd hi hi_eq
    · -- k+1 ≠ n + i.val: step k+1 does not touch nonce i
      have hne : k + 1 ≠ n + i.val := heq
      rw [step_nonce_of_ne dec tr n (k + 1) (descend dec n tr k s₀) i hne]
        at h
      have h_ext := ih i salt h
      rw [step_nonce_of_ne dec (tr ++ tr') n (k + 1)
        (descend dec n (tr ++ tr') k s₀) i hne]
      exact h_ext

omit [Inhabited D] in
/-- **Trace-extension stability for messages.**  The message half of
`descend_nonce_preserved_append`: same step, same decoding, same value. -/
theorem descend_message_preserved_append [DecidableEq D]
    (dec : RoleDecoders C) (n : ℕ) (tr tr' : List (Enc × D))
    (s₀ : ExtractState n Salt D M)
    (hs₀_label : ∀ v, v ≠ 1 → s₀.label v = none)
    (hs₀_message : ∀ i, s₀.message i = none) :
    ∀ k i msg, (descend dec n tr k s₀).message i = some msg →
      (descend dec n (tr ++ tr') k s₀).message i = some msg := by
  intro k
  induction k with
  | zero =>
    intro i msg h
    dsimp [descend] at h ⊢
    exact h
  | succ k ih =>
    intro i msg h
    dsimp [descend] at h ⊢
    by_cases heq : k + 1 = n + i.val
    · have hw_ge_n : n ≤ k + 1 := by omega
      have hw_lt_2n : k + 1 < 2 * n := by
        have := i.isLt
        omega
      have hi : i = (⟨k + 1 - n, by omega⟩ : Fin n) := by
        apply Fin.ext
        show (i : ℕ) = k + 1 - n
        omega
      have hnone : (descend dec n tr k s₀).message i = none :=
        descend_message_support dec n tr s₀ hs₀_message k i (by omega)
      rcases step_leafData_eq_or_decoded dec tr n (k + 1)
          (descend dec n tr k s₀) with
        ⟨-, hfix⟩ | ⟨leafval, qa, salt', msg', hleafval, hqa, hnv, hrange,
          hldec⟩
      · rw [hfix i, hnone] at h
        simp at h
      · have hleafval_ext := descend_label_preserved_append dec n tr tr' s₀
          hs₀_label k (k + 1) leafval hleafval
        have hqa_ext : List.find? (fun qa : Enc × D => qa.2 = leafval)
            (tr ++ tr') = some qa :=
          find?_append_of_some (fun qa : Enc × D => decide (qa.2 = leafval))
            tr tr' qa hqa
        have hstep_tr := step_eq_leaf dec tr n (k + 1)
          (descend dec n tr k s₀) leafval qa salt' msg' hleafval hqa hnv
          hrange hldec
        have hmsg_tr : (ExtractState.step dec tr n (k + 1)
            (descend dec n tr k s₀)).message i = some msg' := by
          rw [hstep_tr]
          dsimp only
          rw [Function.update_apply]
          split_ifs with hi_eq
          · rfl
          · exact absurd hi hi_eq
        have hmsg_eq : msg' = msg :=
          Option.some_inj.mp (hmsg_tr.symm.trans h)
        have hstep_ext := step_eq_leaf dec (tr ++ tr') n (k + 1)
          (descend dec n (tr ++ tr') k s₀) leafval qa salt' msg'
          hleafval_ext hqa_ext hnv hrange hldec
        rw [hstep_ext]
        dsimp only
        rw [Function.update_apply]
        split_ifs with hi_eq
        · rw [hmsg_eq]
        · exact absurd hi hi_eq
    · have hne : k + 1 ≠ n + i.val := heq
      rw [step_message_of_ne dec tr n (k + 1) (descend dec n tr k s₀) i hne]
        at h
      have h_ext := ih i msg h
      rw [step_message_of_ne dec (tr ++ tr') n (k + 1)
        (descend dec n (tr ++ tr') k s₀) i hne]
      exact h_ext

end MH

end Merkle
