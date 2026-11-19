import Mathlib.Tactic.Ring
import Merkle.FreshHit
import Merkle.Extraction
import Merkle.CheckPass

/-!
# The two-stage extraction experiment in the random-oracle model

`Extraction.lean` proves the deterministic core: on a collision-free commitment trace that already
contains every input the verifier's check presents, the extractor recovers the claimed messages and
*literally* the opening the adversary later exhibits (`mh_extract_explains_of_trace_subset`).  This
file puts that core inside a bounded ROM experiment.

The experiment is one lazy execution, exactly as in `BindingInstance.lean`:

    commitment stage (t₁ queries) → opening stage (t₂ queries, resumed from aux) → the check

Only the *commitment* stage's trace is handed to the extractor — that is the whole point of the
game: a theorem about it says the adversary already knew the accepted opening when it produced the
root.  The opening stage's queries and its private state are invisible to the extractor.

What is proved here: **ROM extraction reduces to a single query-level statement** —

> every input the check presents was already queried during the commitment stage.

`extractionExplains_of_commitQueries` discharges everything else (trace soundness of a real
execution, the pair-vs-query gap between `checkTraceList` and a trace, and the deterministic
descent).  What remains is bounding the tapes where that statement fails; `FreshHit.lean` supplies
the counting kernel for the two events that are not a commitment collision, and the README's open
obligations record the rest.
-/

open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

open RandomOracle

universe uSalt uMsg uDigest uEnc uAux uRun

variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest} {Enc : Type uEnc}

/-- What an opening stage outputs: an opened set, claimed messages, and a proof for that set.  The
proof's type depends on the set, which is why this is a structure rather than a tuple. -/
structure OpeningClaim (n : ℕ) (Salt : Type uSalt) (M : Type uMsg) (D : Type uDigest) where
  I : Finset (Fin n)
  a : Fin n → M
  pf : Opening n I Salt D

/-! ## The experiment -/

/-- The two-stage experiment as one bounded execution: commitment stage, then opening stage resumed
from its private state, then the reconstruction the verifier performs on the claim.  The check is
run for the same reason as in the binding game — so that the inputs it hashes occupy answer-tape
slots — and the output keeps only what the game is about, the root and the claim. -/
def extractionRun [Inhabited D] [DecidableEq Enc] (C : Codec Salt M D Enc) (n t₁ t₂ : ℕ)
    {Aux : Type uAux} (commit : Tree Enc D (D × Aux) t₁)
    (opening : Aux → Tree Enc D (OpeningClaim n Salt M D) t₂) :
    Tree Enc D (D × OpeningClaim n Salt M D) (2 * n + t₂ + t₁) :=
  commit.bind fun ra =>
    (opening ra.2).bind fun claim =>
      (checkPass C n claim.I claim.a claim.pf (2 * n) fun _ => default).map fun _ =>
        (ra.1, claim)

/-! ## The candidate labels the commitment stage determines -/

/-- The values a commitment stage can have fixed: the root it output, and the two children decoded
from each input it queried.  There are at most `2 * t₁ + 1` of them — the book's `L(t₁, n)`, here in
its `2t₁+1` form. -/
def candidateLabel [Inhabited D] {Out : Type uAux} (C : Codec Salt M D Enc)
    (dec : RoleDecoders C) (rootOf : Out → D) (run : Out × List Enc × List (Enc × D))
    (m : ℕ) : D :=
  if m = 0 then rootOf run.1
  else
    ((run.2.1[(m - 1) / 2]?).bind dec.nodeDec).elim default fun lr =>
      if (m - 1) % 2 = 0 then lr.1 else lr.2

theorem candidateLabel_zero [Inhabited D] {Out : Type uAux} (C : Codec Salt M D Enc)
    (dec : RoleDecoders C) (rootOf : Out → D) (run : Out × List Enc × List (Enc × D)) :
    candidateLabel C dec rootOf run 0 = rootOf run.1 := by
  rw [candidateLabel, if_pos rfl]

theorem candidateLabel_left [Inhabited D] {Out : Type uAux} (C : Codec Salt M D Enc)
    (dec : RoleDecoders C) (rootOf : Out → D) (run : Out × List Enc × List (Enc × D)) (i : ℕ)
    (h : i < run.2.1.length) (l r : D) (hdec : dec.nodeDec (run.2.1[i]) = some (l, r)) :
    candidateLabel C dec rootOf run (2 * i + 1) = l := by
  rw [candidateLabel, if_neg (by omega), show (2 * i + 1 - 1) / 2 = i by omega,
    List.getElem?_eq_getElem h]
  simp [hdec]

theorem candidateLabel_right [Inhabited D] {Out : Type uAux} (C : Codec Salt M D Enc)
    (dec : RoleDecoders C) (rootOf : Out → D) (run : Out × List Enc × List (Enc × D)) (i : ℕ)
    (h : i < run.2.1.length) (l r : D) (hdec : dec.nodeDec (run.2.1[i]) = some (l, r)) :
    candidateLabel C dec rootOf run (2 * i + 2) = r := by
  rw [candidateLabel, if_neg (by omega), show (2 * i + 2 - 1) / 2 = i by omega,
    List.getElem?_eq_getElem h]
  simp [hdec]

/-- The target a fresh slot is tested against: a commitment-stage candidate label read off the tape
with that slot *neutralized*, so that it cannot depend on the very slot being tested.  On the tapes
where the commitment stage stopped short of the slot — which is exactly where a fresh query sits —
`commitRun_neutralize` says this is the real label. -/
def hitTargetOf [Inhabited D] [DecidableEq Enc] {Out : Type uAux} (C : Codec Salt M D Enc)
    (dec : RoleDecoders C) (t₁ T : ℕ) (commit : Tree Enc D Out t₁) (rootOf : Out → D)
    (j : Fin T) (m : ℕ) (answers : Fin T → D) : D :=
  candidateLabel C dec rootOf (lazyRun (Function.update answers j default) default commit []) m

/-- The fixed family: every slot, against every candidate label. -/
def extractionHits (T t₁ : ℕ) : Finset (Fin T × ℕ) :=
  Finset.univ ×ˢ Finset.range (2 * t₁ + 1)

theorem extractionHits_card (T t₁ : ℕ) :
    (extractionHits T t₁).card = T * (2 * t₁ + 1) := by
  simp [extractionHits]

theorem hitTarget_hitTargetOf [Inhabited D] [DecidableEq Enc] {Out : Type uAux}
    (C : Codec Salt M D Enc) (dec : RoleDecoders C) (t₁ T : ℕ)
    (commit : Tree Enc D Out t₁) (rootOf : Out → D) (j : Fin T) (m : ℕ) :
    HitTarget j (hitTargetOf C dec t₁ T commit rootOf j m) :=
  hitTarget_of_neutralize j default fun tape =>
    candidateLabel C dec rootOf (lazyRun tape default commit []) m

/-! ## From queries to pairs

The deterministic theorem wants the check's *query-answer pairs* inside the commitment trace, while
the ROM argument produces membership of *queries*.  Trace soundness closes the gap: both sides
answer with the same oracle. -/

/-- Every input the materialized check trace lists is presented at some heap vertex.  This is what
lets the ROM argument talk about *vertices* while the deterministic theorems talk about queries. -/
theorem vertexQuery_of_mem_checkTraceQueries [DecidableEq Enc] [Inhabited D]
    (S : Scheme Salt M D Enc) (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (x : Enc) (hx : x ∈ checkTraceQueries S n I a pf) :
    ∃ w, 0 < w ∧ w < 2 * n ∧ vertexQuery S n I a pf w = some x := by
  rw [checkTraceQueries] at hx
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨ii, -, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨i, hi⟩ := ii
    have hlt := i.isLt
    exact ⟨n + i.val, by omega, by omega, vertexQuery_leaf_pos S n I a pf i hi⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hvpath, hvpos, hvlt⟩ := Finset.mem_filter.mp hv
    exact ⟨v, hvpos, by omega, vertexQuery_node S n I a pf v ⟨hvpos, hvlt, hvpath⟩⟩

theorem checkTraceList_subset_of_queries [DecidableEq Enc] (S : Scheme Salt M D Enc) [Inhabited D]
    (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (pf : Opening n I Salt D)
    (tr : List (Enc × D)) (hsound : TraceSound S tr)
    (hq : ∀ x ∈ checkTraceQueries S n I a pf, ∃ y, (x, y) ∈ tr) :
    ∀ qa ∈ checkTraceList S n I a pf, qa ∈ tr := by
  intro qa hqa
  rcases List.mem_map.mp hqa with ⟨q, hqmem, rfl⟩
  obtain ⟨y, hy⟩ := hq q (Finset.mem_toList.mp hqmem)
  have hyval : y = S.H q := hsound (q, y) hy
  rw [← hyval]
  exact hy

/-- Neutralizing a slot the commitment stage never reached leaves its execution — and so everything
the extractor is given — unchanged.  This is `lazyRun_congr_of_agree` at the point of use. -/
theorem commitRun_neutralize [Inhabited D] [DecidableEq Enc] {Out : Type uAux} {t₁ T : ℕ}
    (commit : Tree Enc D Out t₁) (answers : Fin T → D) (j : Fin T)
    (hj : (lazyRun answers default commit []).2.1.length ≤ j.val) :
    lazyRun (Function.update answers j default) default commit [] =
      lazyRun answers default commit [] := by
  refine lazyRun_congr_of_agree answers (Function.update answers j default) default commit []
    fun i hi => ?_
  have hij : i ≠ j := by
    intro heq
    rw [heq] at hi
    omega
  rw [Function.update_apply, if_neg hij]

/-! ## The cover, for an arbitrary experiment

The argument below never uses that the run *is* `extractionRun`.  What it needs is that the
commitment phase's slots are a **prefix** of the run's layout, and that the claim's check happens
inside the run.  Stating it that way is what lets it apply per-root inside a `k`-commitment
experiment, where the `i`-th commitment phase is a prefix of the run without being its syntactic
first `bind`. -/

/-- The slots of an arbitrary experiment. -/
def runSlots [Inhabited D] [DecidableEq Enc] {A : Type uRun} {F : ℕ} (T : ℕ)
    (R : Tree Enc D A F) (answers : Fin T → D) : List Enc :=
  (lazyRun answers default R []).2.1

/-- Its lazy-sampling oracle. -/
def runOracle [Inhabited D] [DecidableEq Enc] {A : Type uRun} {F : ℕ} (T : ℕ)
    (R : Tree Enc D A F) (answers : Fin T → D) (x : Enc) : D :=
  tapeAt answers default ((runSlots T R answers).idxOf x)

/-- Every input the experiment queries sits at a slot the oracle answers from. -/
theorem run_slot_of_trace [Inhabited D] [DecidableEq Enc] {A : Type uRun} {F : ℕ} (T : ℕ)
    (R : Tree Enc D A F) (answers : Fin T → D) (x : Enc) (y : D) (hFT : F ≤ T)
    (hx : (x, y) ∈ (R.run (runOracle T R answers)).2) :
    ∃ j : Fin T, (runSlots T R answers).idxOf x = j.val ∧
      runOracle T R answers x = answers j ∧ j.val < F := by
  have hrun : R.run (runOracle T R answers) =
      ((lazyRun answers default R []).1, (lazyRun answers default R []).2.2) :=
    lazyRun_eq_run answers default R [] (runOracle T R answers) fun _ => rfl
  rw [hrun] at hx
  obtain ⟨hmem, -⟩ := lazyRun_trace_slot answers default R [] (x, y) hx
  have hlt : (runSlots T R answers).idxOf x < F := by
    have h := lazyRun_slot_lt answers default R [] x hmem
    simpa [runSlots] using h
  have hltT : (runSlots T R answers).idxOf x < T := by omega
  refine ⟨⟨_, hltT⟩, rfl, ?_, hlt⟩
  rw [runOracle, tapeAt, dif_pos hltT]

/-- **Events 2 and 3, for an arbitrary experiment.**  If the check accepts but presents an input the
commitment phase never queried, some slot of the fixed family carries a commitment-determined
candidate label.

The argument takes the *smallest* vertex whose input is fresh.  Its parent is smaller, hence not
fresh, so the commitment phase queried the parent's input — and that input decodes to this vertex's
value.  So the value is one of the commitment phase's candidate labels, while the fresh input's
answer is its slot's tape entry: the slot carries the label.

No collision-freeness is needed: the parent's input decodes to the children by the decoder's
round-trip law alone, which is why this is independent of the commitment-collision event rather than
layered on it. -/
theorem hitFamily_of_fresh_generic_eligible [Inhabited D] [DecidableEq Enc]
    (C : Codec Salt M D Enc) (dec : RoleDecoders C) (n t₁ T : ℕ)
    {Out : Type uAux} (commit : Tree Enc D Out t₁) (rootOf : Out → D)
    {A : Type uRun} {F : ℕ} (R : Tree Enc D A F) (answers : Fin T → D)
    (cl : OpeningClaim n Salt M D) (rt : D) (hFT : F ≤ T)
    (hpref : (lazyRun answers default commit []).2.1 <+: runSlots T R answers)
    (hrt : rt = rootOf (lazyRun answers default commit []).1)
    (hcheck : ∀ qa ∈ ((checkPass C n cl.I cl.a cl.pf (2 * n) fun _ => default).run
        (runOracle T R answers)).2, qa ∈ (R.run (runOracle T R answers)).2)
    (hacc : Accepts (C.withOracle (runOracle T R answers)) n rt cl.I cl.a cl.pf)
    (hfresh : ∃ x ∈ checkTraceQueries (C.withOracle (runOracle T R answers)) n cl.I cl.a cl.pf,
      x ∉ (lazyRun answers default commit []).2.1) :
    HitFamily T (extractionHits F t₁)
      (fun p => (⟨p.1.val, lt_of_lt_of_le p.1.isLt hFT⟩ : Fin T))
      (fun p => hitTargetOf C dec t₁ T commit rootOf
        ⟨p.1.val, lt_of_lt_of_le p.1.isLt hFT⟩ p.2) answers := by
  classical
  obtain ⟨x₀, hx₀mem, hx₀fresh⟩ := hfresh
  set S := C.withOracle (runOracle T R answers) with hS
  set seenC := (lazyRun answers default commit []).2.1 with hseenC
  obtain ⟨w₀, hw₀pos, hw₀lt, hw₀q⟩ :=
    vertexQuery_of_mem_checkTraceQueries S n cl.I cl.a cl.pf x₀ hx₀mem
  set W : Finset ℕ := (Finset.range (2 * n)).filter
    (fun v => 0 < v ∧ ∃ x, vertexQuery S n cl.I cl.a cl.pf v = some x ∧ x ∉ seenC) with hW
  have hw₀W : w₀ ∈ W := by
    rw [hW]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw₀lt, hw₀pos, x₀, hw₀q, hx₀fresh⟩
  obtain ⟨w, hwW, hwmin⟩ : ∃ w, w ∈ W ∧ ∀ v ∈ W, w ≤ v :=
    ⟨W.min' ⟨w₀, hw₀W⟩, W.min'_mem _, fun v hv => W.min'_le v hv⟩
  obtain ⟨hwrange, hwpos, xw, hxwq, hxwfresh⟩ := Finset.mem_filter.mp hwW
  have hwlt : w < 2 * n := Finset.mem_range.mp hwrange
  obtain ⟨yw, hyw⟩ := mem_checkPass_trace_of_vertexQuery C n cl.I cl.a cl.pf
    (runOracle T R answers) w xw hwpos hwlt hxwq
  obtain ⟨j, hjidx, hjval, hjlt⟩ :=
    run_slot_of_trace T R answers xw yw hFT (hcheck (xw, yw) hyw)
  let jf : Fin F := ⟨j.val, hjlt⟩
  have hjf : (⟨jf.val, lt_of_lt_of_le jf.isLt hFT⟩ : Fin T) = j := by
    apply Fin.ext
    rfl
  have hjge : seenC.length ≤ j.val := by
    rw [← hjidx]
    obtain ⟨rest, hrest⟩ := hpref
    rw [← hrest]
    exact le_idxOf_of_not_mem_prefix xw hxwfresh
  have hneutral : lazyRun (Function.update answers j default) default commit [] =
      lazyRun answers default commit [] :=
    commitRun_neutralize (commit := commit) (answers := answers) (j := j) hjge
  have hans : answers j = checkValues S n cl.I cl.a cl.pf w := by
    rw [← hjval]
    exact vertexQuery_answer S n cl.I cl.a cl.pf w xw hxwq
  by_cases hw1 : w = 1
  · refine ⟨(jf, 0), Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (by omega)⟩, ?_⟩
    dsimp only
    rw [hjf, hans, hw1, hacc.2, hitTargetOf, hneutral, candidateLabel_zero, hrt]
  · have hwpath : w ∈ Heap.pathSet n cl.I :=
      mem_pathSet_of_vertexQuery S n cl.I cl.a cl.pf w xw hxwq
    obtain ⟨i₀, hi₀, hwpathOf⟩ := Heap.mem_pathSet.mp hwpath
    have hppath : w / 2 ∈ Heap.pathSet n cl.I :=
      Heap.mem_pathSet.mpr ⟨i₀, hi₀, Heap.parent_mem_pathOf hwpathOf (by omega)⟩
    have hpq := vertexQuery_node S n cl.I cl.a cl.pf (w / 2) ⟨by omega, by omega, hppath⟩
    have hpseen : S.nodeEnc (checkValues S n cl.I cl.a cl.pf (2 * (w / 2)),
        checkValues S n cl.I cl.a cl.pf (2 * (w / 2) + 1)) ∈ seenC := by
      by_contra hc
      have hmem : w / 2 ∈ W := by
        rw [hW]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, _, hpq, hc⟩
      have := hwmin _ hmem
      omega
    obtain ⟨i, hilen, hget⟩ := List.getElem_of_mem hpseen
    have hit₁ : i < t₁ := by
      have hlen : seenC.length ≤ t₁ := by
        have h := lazyRun_seen_length_le answers default commit []
        simpa [hseenC] using h
      omega
    have hdec : dec.nodeDec (seenC[i]) =
        some (checkValues S n cl.I cl.a cl.pf (2 * (w / 2)),
          checkValues S n cl.I cl.a cl.pf (2 * (w / 2) + 1)) := by
      rw [hget]
      exact dec.node_roundTrip _
    rcases Nat.mod_two_eq_zero_or_one w with hpar | hpar
    · refine ⟨(jf, 2 * i + 1), Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (by omega)⟩, ?_⟩
      dsimp only
      rw [hjf, hans, hitTargetOf, hneutral,
        candidateLabel_left C dec rootOf _ i (by rw [← hseenC]; exact hilen) _ _ hdec,
        show 2 * (w / 2) = w by omega]
    · refine ⟨(jf, 2 * i + 2), Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (by omega)⟩, ?_⟩
      dsimp only
      rw [hjf, hans, hitTargetOf, hneutral,
        candidateLabel_right C dec rootOf _ i (by rw [← hseenC]; exact hilen) _ _ hdec,
        show 2 * (w / 2) + 1 = w by omega]

/-- Embed an eligible-run fresh-hit family into the historical full-tape family.  This is a pure
relaxation used by compatibility callers; concrete staged composition should retain the eligible
family and its smaller cardinality. -/
theorem hitFamily_extractionHits_mono [Inhabited D] [DecidableEq Enc]
    (C : Codec Salt M D Enc) (dec : RoleDecoders C) (t₁ F T : ℕ)
    {Out : Type uAux} (commit : Tree Enc D Out t₁) (rootOf : Out → D)
    (answers : Fin T → D) (hFT : F ≤ T)
    (h : HitFamily T (extractionHits F t₁)
      (fun p => (⟨p.1.val, lt_of_lt_of_le p.1.isLt hFT⟩ : Fin T))
      (fun p => hitTargetOf C dec t₁ T commit rootOf
        ⟨p.1.val, lt_of_lt_of_le p.1.isLt hFT⟩ p.2) answers) :
    HitFamily T (extractionHits T t₁) Prod.fst
      (fun p => hitTargetOf C dec t₁ T commit rootOf p.1 p.2) answers := by
  rcases h with ⟨p, hp, heq⟩
  have hp2 := (Finset.mem_product.mp hp).2
  let j : Fin T := ⟨p.1.val, lt_of_lt_of_le p.1.isLt hFT⟩
  refine ⟨(j, p.2), Finset.mem_product.mpr ⟨Finset.mem_univ _, hp2⟩, ?_⟩
  simpa [j] using heq

/-! ### The rest of the cover, generically -/

section GenericCover

variable [Inhabited D] [DecidableEq Enc] (C : Codec Salt M D Enc) (n t₁ T : ℕ)
  {Out : Type uAux} (commit : Tree Enc D Out t₁)
  {A : Type uRun} {F : ℕ} (R : Tree Enc D A F) (answers : Fin T → D)

/-- A phase's trace inside the run is its own lazy trace. -/
theorem commitTrace_eq_generic
    (hpref : (lazyRun answers default commit []).2.1 <+: runSlots T R answers) :
    (commit.run (runOracle T R answers)).2 = (lazyRun answers default commit []).2.2 :=
  congrArg Prod.snd
    (lazyRun_run_eq_of_prefix answers default commit [] (runOracle T R answers) _
      (fun _ => rfl) hpref)

/-- An input absent from the phase's trace is absent from its slots. -/
theorem not_mem_seen_of_not_mem_trace
    (hpref : (lazyRun answers default commit []).2.1 <+: runSlots T R answers)
    (x : Enc) (hx : ∀ y, (x, y) ∉ (commit.run (runOracle T R answers)).2) :
    x ∉ (lazyRun answers default commit []).2.1 := by
  intro hmem
  obtain ⟨y, hy⟩ := lazyRun_mem_trace_of_mem_seen answers default commit [] x hmem (by simp)
  exact hx y (by rw [commitTrace_eq_generic (commit := commit) (R := R)
    (answers := answers) (hpref := hpref)]; exact hy)

/-- **Event 1, generically.**  A collision inside a phase's trace is a repeat of the tape at two
distinct slots below that phase's budget. -/
theorem pairCollision_of_not_collisionFree_generic (ht₁ : t₁ ≤ T)
    (hpref : (lazyRun answers default commit []).2.1 <+: runSlots T R answers)
    (h : ¬ CollisionFree ((commit.run (runOracle T R answers)).2)) :
    PairCollision T (slotPairs T t₁) answers := by
  classical
  have hcol : TraceCollision (lazyRun answers default commit []).2.2 := by
    rw [commitTrace_eq_generic (commit := commit) (R := R) (answers := answers)
      (hpref := hpref)] at h
    unfold CollisionFree at h
    push Not at h
    obtain ⟨qa₀, h₀, qa₁, h₁, hans, hne⟩ := h
    exact ⟨qa₀, h₀, qa₁, h₁, hne, hans⟩
  exact traceCollision_pairCollision answers default commit ht₁ hcol

variable [Inhabited Salt] [Inhabited M] [DecidableEq D] (dec : RoleDecoders C)

/-- **The reduction, generically.**  On a collision-free phase trace containing every input the
check presents, extraction from that phase explains the accepted claim. -/
theorem explains_of_commitQueries_generic (rt : D) (cl : OpeningClaim n Salt M D)
    (hfree : CollisionFree ((commit.run (runOracle T R answers)).2))
    (hacc : Accepts (C.withOracle (runOracle T R answers)) n rt cl.I cl.a cl.pf)
    (hq : ∀ x ∈ checkTraceQueries (C.withOracle (runOracle T R answers)) n cl.I cl.a cl.pf,
      ∃ y, (x, y) ∈ (commit.run (runOracle T R answers)).2) :
    ∃ out : Extracted n Salt M D,
      extract dec n rt (commit.run (runOracle T R answers)).2 = some out ∧
        (∀ j ∈ cl.I, out.message j = cl.a j) ∧
        openFromTrapdoor out.trapdoor cl.I = cl.pf :=
  mh_extract_explains_of_trace_subset (C.withOracle (runOracle T R answers)) dec n
    cl.I cl.a cl.pf rt _ hfree hacc
    (checkTraceList_subset_of_queries (C.withOracle (runOracle T R answers)) n cl.I cl.a cl.pf
      _ (Tree.trace_sound commit (runOracle T R answers)) hq)

/-- **The failure cover, generically.**  An accepted claim that the phase's extraction does not
explain forces a collision in that phase's trace, or a slot carrying one of its candidate labels. -/
theorem cover_of_failure_generic_eligible (rootOf : Out → D) (rt : D)
    (cl : OpeningClaim n Salt M D)
    (hFT : F ≤ T) (hpref : (lazyRun answers default commit []).2.1 <+: runSlots T R answers)
    (hrt : rt = rootOf (lazyRun answers default commit []).1)
    (hcheck : ∀ qa ∈ ((checkPass C n cl.I cl.a cl.pf (2 * n) fun _ => default).run
        (runOracle T R answers)).2, qa ∈ (R.run (runOracle T R answers)).2)
    (hacc : Accepts (C.withOracle (runOracle T R answers)) n rt cl.I cl.a cl.pf)
    (hfail : ¬ ∃ out : Extracted n Salt M D,
      extract dec n rt (commit.run (runOracle T R answers)).2 = some out ∧
        (∀ j ∈ cl.I, out.message j = cl.a j) ∧
        openFromTrapdoor out.trapdoor cl.I = cl.pf) :
    ¬ CollisionFree ((commit.run (runOracle T R answers)).2) ∨
      HitFamily T (extractionHits F t₁)
        (fun p => (⟨p.1.val, lt_of_lt_of_le p.1.isLt hFT⟩ : Fin T))
        (fun p => hitTargetOf C dec t₁ T commit rootOf
          ⟨p.1.val, lt_of_lt_of_le p.1.isLt hFT⟩ p.2) answers := by
  classical
  by_cases hfree : CollisionFree ((commit.run (runOracle T R answers)).2)
  · refine Or.inr (hitFamily_of_fresh_generic_eligible C dec n t₁ T commit rootOf R answers cl rt hFT
      hpref hrt hcheck hacc ?_)
    by_contra hq
    push Not at hq
    refine hfail (explains_of_commitQueries_generic C n (t₁ := t₁) (T := T) commit R answers dec
      rt cl hfree hacc fun x hx => ?_)
    by_contra hc
    push Not at hc
    exact absurd (hq x hx) (not_mem_seen_of_not_mem_trace (commit := commit) (R := R)
      (answers := answers) (hpref := hpref) (x := x) (hx := hc))
  · exact Or.inl hfree

/-- Backwards-compatible full-tape relaxation of `cover_of_failure_generic_eligible`. -/
theorem cover_of_failure_generic (rootOf : Out → D) (rt : D) (cl : OpeningClaim n Salt M D)
    (hFT : F ≤ T) (hpref : (lazyRun answers default commit []).2.1 <+: runSlots T R answers)
    (hrt : rt = rootOf (lazyRun answers default commit []).1)
    (hcheck : ∀ qa ∈ ((checkPass C n cl.I cl.a cl.pf (2 * n) fun _ => default).run
        (runOracle T R answers)).2, qa ∈ (R.run (runOracle T R answers)).2)
    (hacc : Accepts (C.withOracle (runOracle T R answers)) n rt cl.I cl.a cl.pf)
    (hfail : ¬ ∃ out : Extracted n Salt M D,
      extract dec n rt (commit.run (runOracle T R answers)).2 = some out ∧
        (∀ j ∈ cl.I, out.message j = cl.a j) ∧
        openFromTrapdoor out.trapdoor cl.I = cl.pf) :
    ¬ CollisionFree ((commit.run (runOracle T R answers)).2) ∨
      HitFamily T (extractionHits T t₁) Prod.fst
        (fun p => hitTargetOf C dec t₁ T commit rootOf p.1 p.2) answers := by
  rcases cover_of_failure_generic_eligible C n t₁ T commit R answers dec rootOf rt cl hFT
      hpref hrt hcheck hacc hfail with hcollision | hhit
  · exact Or.inl hcollision
  · exact Or.inr (hitFamily_extractionHits_mono C dec t₁ F T commit rootOf answers hFT hhit)

end GenericCover

section Experiment

variable [Inhabited D] [DecidableEq Enc] (C : Codec Salt M D Enc) (n t₁ t₂ T : ℕ)
  {Aux : Type uAux} (commit : Tree Enc D (D × Aux) t₁)
  (opening : Aux → Tree Enc D (OpeningClaim n Salt M D) t₂)

/-- The occupied slots of the whole experiment, in order of first occurrence. -/
def extractionSlots (answers : Fin T → D) : List Enc :=
  runSlots T (extractionRun C n t₁ t₂ commit opening) answers

/-- The experiment's lazy-sampling oracle: every input is answered from the slot of its first
occurrence.  Acceptance and the extractor both see this one total oracle. -/
def extractionOracle (answers : Fin T → D) (x : Enc) : D :=
  runOracle T (extractionRun C n t₁ t₂ commit opening) answers x

/-- The commitment stage's own query-answer trace — the extractor's only input. -/
def commitTrace (answers : Fin T → D) : List (Enc × D) :=
  (commit.run (extractionOracle C n t₁ t₂ T commit opening answers)).2

/-- The root the commitment stage outputs. -/
def commitRoot (answers : Fin T → D) : D :=
  (commit.run (extractionOracle C n t₁ t₂ T commit opening answers)).1.1

/-- The claim the opening stage outputs, resumed from the commitment stage's private state. -/
def openingClaim (answers : Fin T → D) : OpeningClaim n Salt M D :=
  ((opening (commit.run (extractionOracle C n t₁ t₂ T commit opening answers)).1.2).run
    (extractionOracle C n t₁ t₂ T commit opening answers)).1

/-- Every pair of the commitment trace is answered by the experiment's oracle.  A real execution
supplies this; the deterministic theorems take it as a hypothesis. -/
theorem commitTrace_sound (answers : Fin T → D) :
    TraceSound (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers))
      (commitTrace C n t₁ t₂ T commit opening answers) :=
  Tree.trace_sound commit (extractionOracle C n t₁ t₂ T commit opening answers)

/-- The commitment stage sees the same answers inside the experiment as it would alone: its slots
are a prefix of the experiment's.  Everything the extractor gets is therefore a function of the
commitment stage's own lazy run. -/
theorem commitRun_eq (answers : Fin T → D) :
    commit.run (extractionOracle C n t₁ t₂ T commit opening answers) =
      ((lazyRun answers default commit []).1, (lazyRun answers default commit []).2.2) :=
  lazyRun_prefix_run_eq answers default commit _ [] _ fun _ => rfl

theorem commitTrace_eq (answers : Fin T → D) :
    commitTrace C n t₁ t₂ T commit opening answers =
      (lazyRun answers default commit []).2.2 :=
  congrArg Prod.snd (commitRun_eq C n t₁ t₂ T commit opening answers)

/-! ### Event 1: a collision inside the commitment stage

The extractor's descent is deterministic only on a collision-free trace.  Under lazy sampling a
commitment-stage collision is a repeat of the tape at two distinct slots below `t₁` — the sharp
birthday count, with no assumption tying the adaptive adversary to the layout. -/

theorem pairCollision_of_not_collisionFree (answers : Fin T → D) (ht₁ : t₁ ≤ T)
    (h : ¬ CollisionFree (commitTrace C n t₁ t₂ T commit opening answers)) :
    PairCollision T (slotPairs T t₁) answers := by
  classical
  have hcol : TraceCollision (lazyRun answers default commit []).2.2 := by
    rw [commitTrace_eq] at h
    unfold CollisionFree at h
    push Not at h
    obtain ⟨qa₀, h₀, qa₁, h₁, hans, hne⟩ := h
    exact ⟨qa₀, h₀, qa₁, h₁, hne, hans⟩
  exact traceCollision_pairCollision answers default commit ht₁ hcol

/-- **Event 1, counted.**  The commitment trace fails to be collision-free on at most a
`t₁(t₁−1)/2` in `|D|` fraction of tapes. -/
theorem commitCollision_card_le [Fintype D] [DecidableEq D] (ht₁ : t₁ ≤ T)
    [DecidablePred fun answers : Fin T → D =>
      ¬ CollisionFree (commitTrace C n t₁ t₂ T commit opening answers)] :
    (Finset.filter (fun answers : Fin T → D =>
        ¬ CollisionFree (commitTrace C n t₁ t₂ T commit opening answers))
      Finset.univ).card ≤ t₁ * (t₁ - 1) / 2 * (Fintype.card D) ^ (T - 1) := by
  classical
  calc
    (Finset.filter (fun answers : Fin T → D =>
          ¬ CollisionFree (commitTrace C n t₁ t₂ T commit opening answers))
        Finset.univ).card
        ≤ (Finset.filter (PairCollision (D := D) T (slotPairs T t₁)) Finset.univ).card := by
      apply Finset.card_le_card
      intro answers hanswers
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hanswers ⊢
      exact pairCollision_of_not_collisionFree C n t₁ t₂ T commit opening answers ht₁ hanswers
    _ ≤ (slotPairs T t₁).card * (Fintype.card D) ^ (T - 1) :=
      answerTape_pairCollision_card_le T (slotPairs T t₁) slotPairs_distinct
    _ ≤ t₁ * (t₁ - 1) / 2 * (Fintype.card D) ^ (T - 1) :=
      Nat.mul_le_mul_right _ (slotPairs_card_le T t₁)

/-! ### Events 2 and 3: a fresh query landing on a commitment-determined value

These are not pair collisions.  The value a fresh query must hit is a *label*, decoded out of a
queried input rather than read off the tape, so `FreshHit.lean` rather than
`answerTape_pairCollision_card_le` is the kernel.  The two lemmas below are what let a label be a
`HitTarget`: a query the commitment stage never made sits at or after the commitment stage's slots,
and the commitment stage's run is unchanged by neutralizing any slot it never reached. -/

/-- An input absent from the commitment stage's trace is absent from its slots. -/
theorem not_mem_commitSeen (answers : Fin T → D) (x : Enc)
    (hx : ∀ y, (x, y) ∉ commitTrace C n t₁ t₂ T commit opening answers) :
    x ∉ (lazyRun answers default commit []).2.1 := by
  intro hmem
  obtain ⟨y, hy⟩ := lazyRun_mem_trace_of_mem_seen answers default commit [] x hmem (by simp)
  exact hx y (by rw [commitTrace_eq]; exact hy)

/-- An input the reconstruction queries is queried by the experiment. -/
theorem mem_extractionRun_trace_of_checkPass (answers : Fin T → D) (qa : Enc × D)
    (h : qa ∈ ((checkPass C n (openingClaim C n t₁ t₂ T commit opening answers).I
          (openingClaim C n t₁ t₂ T commit opening answers).a
          (openingClaim C n t₁ t₂ T commit opening answers).pf (2 * n) fun _ => default).run
        (extractionOracle C n t₁ t₂ T commit opening answers)).2) :
    qa ∈ ((extractionRun C n t₁ t₂ commit opening).run
      (extractionOracle C n t₁ t₂ T commit opening answers)).2 := by
  rw [extractionRun, Tree.run_bind, Tree.run_bind, Tree.run_map]
  dsimp only
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h)))

/-- **Events 2 and 3.**  If the check accepts but presents an input the commitment stage never
queried, some slot of the fixed family carries a commitment-determined candidate label.

The argument takes the *smallest* vertex whose input is fresh.  Its parent is smaller, hence not
fresh, so the commitment stage queried the parent's input — and that input decodes to this vertex's
value.  So the value is one of the commitment stage's candidate labels, while the fresh input's
answer is its slot's tape entry: the slot carries the label.

No collision-freeness is needed here.  The parent's input decodes to the children by the decoder's
round-trip law alone, which is why this is independent of event 1 rather than layered on it. -/
theorem hitFamily_of_fresh (dec : RoleDecoders C) (answers : Fin T → D)
    (hT : 2 * n + t₂ + t₁ ≤ T)
    (hacc : Accepts (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
      (commitRoot C n t₁ t₂ T commit opening answers)
      (openingClaim C n t₁ t₂ T commit opening answers).I
      (openingClaim C n t₁ t₂ T commit opening answers).a
      (openingClaim C n t₁ t₂ T commit opening answers).pf)
    (hfresh : ∃ x ∈ checkTraceQueries
        (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
        (openingClaim C n t₁ t₂ T commit opening answers).I
        (openingClaim C n t₁ t₂ T commit opening answers).a
        (openingClaim C n t₁ t₂ T commit opening answers).pf,
      ∀ y, (x, y) ∉ commitTrace C n t₁ t₂ T commit opening answers) :
    HitFamily T (extractionHits (2 * n + t₂ + t₁) t₁)
      (fun p => (⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ : Fin T))
      (fun p => hitTargetOf C dec t₁ T commit Prod.fst
        ⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ p.2) answers := by
  obtain ⟨x₀, hx₀mem, hx₀fresh⟩ := hfresh
  refine hitFamily_of_fresh_generic_eligible C dec n t₁ T commit Prod.fst
    (extractionRun C n t₁ t₂ commit opening) answers
    (openingClaim C n t₁ t₂ T commit opening answers)
    (commitRoot C n t₁ t₂ T commit opening answers) hT
    (lazyRun_seen_prefix_bind answers default _ commit []) ?_
    (mem_extractionRun_trace_of_checkPass C n t₁ t₂ T commit opening answers) hacc
    ⟨x₀, hx₀mem, not_mem_commitSeen C n t₁ t₂ T commit opening answers x₀ hx₀fresh⟩
  rw [commitRoot, commitRun_eq C n t₁ t₂ T commit opening answers]

end Experiment

/-! ## The reduction -/

section Explains

variable [Inhabited D] [Inhabited Salt] [Inhabited M] [DecidableEq D] [DecidableEq Enc]
  (C : Codec Salt M D Enc) (dec : RoleDecoders C) (n t₁ t₂ T : ℕ)
  {Aux : Type uAux} (commit : Tree Enc D (D × Aux) t₁)
  (opening : Aux → Tree Enc D (OpeningClaim n Salt M D) t₂)

/-- Extraction succeeded on this tape: from the commitment trace alone, the extractor produced the
messages the opening stage later claimed and *literally* the proof it exhibited. -/
def ExtractionExplains (answers : Fin T → D) : Prop :=
  ∃ out : Extracted n Salt M D,
    extract dec n (commitRoot C n t₁ t₂ T commit opening answers)
        (commitTrace C n t₁ t₂ T commit opening answers) = some out ∧
      (∀ i ∈ (openingClaim C n t₁ t₂ T commit opening answers).I,
        out.message i = (openingClaim C n t₁ t₂ T commit opening answers).a i) ∧
      openFromTrapdoor out.trapdoor (openingClaim C n t₁ t₂ T commit opening answers).I =
        (openingClaim C n t₁ t₂ T commit opening answers).pf

/-- **ROM extraction, reduced to a query-level statement.**  On a tape where

* the commitment trace is collision-free, and
* every input the check presents was already queried during the commitment stage,

an accepted opening is explained by the commitment-stage extraction.  Everything else — trace
soundness, the pair/query gap, and the deterministic descent — is discharged here, so the remaining
ROM obligation is exactly to bound the tapes violating one of the two hypotheses. -/
theorem extractionExplains_of_commitQueries (answers : Fin T → D)
    (hfree : CollisionFree (commitTrace C n t₁ t₂ T commit opening answers))
    (hacc : Accepts (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
      (commitRoot C n t₁ t₂ T commit opening answers)
      (openingClaim C n t₁ t₂ T commit opening answers).I
      (openingClaim C n t₁ t₂ T commit opening answers).a
      (openingClaim C n t₁ t₂ T commit opening answers).pf)
    (hq : ∀ x ∈ checkTraceQueries
        (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
        (openingClaim C n t₁ t₂ T commit opening answers).I
        (openingClaim C n t₁ t₂ T commit opening answers).a
        (openingClaim C n t₁ t₂ T commit opening answers).pf,
      ∃ y, (x, y) ∈ commitTrace C n t₁ t₂ T commit opening answers) :
    ExtractionExplains C dec n t₁ t₂ T commit opening answers := by
  have hsub := checkTraceList_subset_of_queries
    (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
    (openingClaim C n t₁ t₂ T commit opening answers).I
    (openingClaim C n t₁ t₂ T commit opening answers).a
    (openingClaim C n t₁ t₂ T commit opening answers).pf
    (commitTrace C n t₁ t₂ T commit opening answers)
    (commitTrace_sound C n t₁ t₂ T commit opening answers) hq
  exact mh_extract_explains_of_trace_subset
    (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) dec n
    (openingClaim C n t₁ t₂ T commit opening answers).I
    (openingClaim C n t₁ t₂ T commit opening answers).a
    (openingClaim C n t₁ t₂ T commit opening answers).pf
    (commitRoot C n t₁ t₂ T commit opening answers)
    (commitTrace C n t₁ t₂ T commit opening answers) hfree hacc hsub

/-- **The failure cover.**  An accepted opening that the commitment-stage extraction does not
explain forces one of two events: a collision inside the commitment trace, or a slot of the fixed
family carrying a commitment-determined label. -/
theorem cover_of_extractionFailure (answers : Fin T → D) (hT : 2 * n + t₂ + t₁ ≤ T)
    (hacc : Accepts (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
      (commitRoot C n t₁ t₂ T commit opening answers)
      (openingClaim C n t₁ t₂ T commit opening answers).I
      (openingClaim C n t₁ t₂ T commit opening answers).a
      (openingClaim C n t₁ t₂ T commit opening answers).pf)
    (hfail : ¬ ExtractionExplains C dec n t₁ t₂ T commit opening answers) :
    ¬ CollisionFree (commitTrace C n t₁ t₂ T commit opening answers) ∨
      HitFamily T (extractionHits (2 * n + t₂ + t₁) t₁)
        (fun p => (⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ : Fin T))
        (fun p => hitTargetOf C dec t₁ T commit Prod.fst
          ⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ p.2) answers := by
  classical
  by_cases hfree : CollisionFree (commitTrace C n t₁ t₂ T commit opening answers)
  · refine Or.inr (hitFamily_of_fresh C n t₁ t₂ T commit opening dec answers hT hacc ?_)
    by_contra hq
    push Not at hq
    exact hfail (extractionExplains_of_commitQueries C dec n t₁ t₂ T commit opening answers
      hfree hacc hq)
  · exact Or.inl hfree

/-- **ROM extraction, counted.**  Over uniform answer tapes, an accepted opening is explained by the
commitment-stage extraction except on at most

`(t₁(t₁−1)/2 + (2n+t₂+t₁)(2t₁+1)) · |D|^(T−1)`

of the `|D|^T` tapes: the sharp birthday term for the commitment stage, plus one fresh-hit term per
eligible extraction-program slot per candidate label.  The eligible range is the actual combined
commitment/opening/check fuel, not the ambient tape length. -/
theorem mh_extract_rom_card_le_eligible [Fintype D] (ht₁ : t₁ ≤ T)
    (hT : 2 * n + t₂ + t₁ ≤ T)
    [DecidablePred fun answers : Fin T → D =>
      ¬ CollisionFree (commitTrace C n t₁ t₂ T commit opening answers)]
    [DecidablePred fun answers : Fin T → D =>
      Accepts (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
          (commitRoot C n t₁ t₂ T commit opening answers)
          (openingClaim C n t₁ t₂ T commit opening answers).I
          (openingClaim C n t₁ t₂ T commit opening answers).a
          (openingClaim C n t₁ t₂ T commit opening answers).pf ∧
        ¬ ExtractionExplains C dec n t₁ t₂ T commit opening answers] :
    (Finset.filter (fun answers : Fin T → D =>
        Accepts (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
            (commitRoot C n t₁ t₂ T commit opening answers)
            (openingClaim C n t₁ t₂ T commit opening answers).I
            (openingClaim C n t₁ t₂ T commit opening answers).a
            (openingClaim C n t₁ t₂ T commit opening answers).pf ∧
          ¬ ExtractionExplains C dec n t₁ t₂ T commit opening answers)
      Finset.univ).card ≤
      (t₁ * (t₁ - 1) / 2 + (2 * n + t₂ + t₁) * (2 * t₁ + 1)) *
        (Fintype.card D) ^ (T - 1) := by
  calc
    (Finset.filter (fun answers : Fin T → D =>
        Accepts (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
            (commitRoot C n t₁ t₂ T commit opening answers)
            (openingClaim C n t₁ t₂ T commit opening answers).I
            (openingClaim C n t₁ t₂ T commit opening answers).a
            (openingClaim C n t₁ t₂ T commit opening answers).pf ∧
          ¬ ExtractionExplains C dec n t₁ t₂ T commit opening answers)
      Finset.univ).card
        ≤ ((Finset.filter (fun answers : Fin T → D =>
              ¬ CollisionFree (commitTrace C n t₁ t₂ T commit opening answers))
            Finset.univ) ∪
          (Finset.filter (HitFamily (D := D) T (extractionHits (2 * n + t₂ + t₁) t₁)
              (fun p => (⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ : Fin T))
              (fun p => hitTargetOf C dec t₁ T commit Prod.fst
                ⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ p.2))
            Finset.univ)).card := by
      apply Finset.card_le_card
      intro answers ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rcases cover_of_extractionFailure C dec n t₁ t₂ T commit opening answers hT ha.1 ha.2 with
        h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    _ ≤ (Finset.filter (fun answers : Fin T → D =>
            ¬ CollisionFree (commitTrace C n t₁ t₂ T commit opening answers))
          Finset.univ).card +
        (Finset.filter (HitFamily (D := D) T (extractionHits (2 * n + t₂ + t₁) t₁)
            (fun p => (⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ : Fin T))
            (fun p => hitTargetOf C dec t₁ T commit Prod.fst
              ⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ p.2))
          Finset.univ).card := Finset.card_union_le _ _
    _ ≤ t₁ * (t₁ - 1) / 2 * (Fintype.card D) ^ (T - 1) +
        (2 * n + t₂ + t₁) * (2 * t₁ + 1) * (Fintype.card D) ^ (T - 1) := by
      refine Nat.add_le_add (commitCollision_card_le C n t₁ t₂ T commit opening ht₁) ?_
      have h := answerTape_hitFamily_card_le (D := D) T
        (extractionHits (2 * n + t₂ + t₁) t₁)
        (fun p => (⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ : Fin T))
        (fun p => hitTargetOf C dec t₁ T commit Prod.fst
          ⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ p.2)
        (fun p _ => hitTarget_hitTargetOf C dec t₁ T commit Prod.fst
          ⟨p.1.val, lt_of_lt_of_le p.1.isLt hT⟩ p.2)
      rwa [extractionHits_card] at h
    _ = (t₁ * (t₁ - 1) / 2 + (2 * n + t₂ + t₁) * (2 * t₁ + 1)) *
        (Fintype.card D) ^ (T - 1) := by ring

/-- Backwards-compatible tape-length relaxation of `mh_extract_rom_card_le_eligible`.  Concrete
composition should use the eligible-range theorem so unused tape padding is not charged. -/
theorem mh_extract_rom_card_le [Fintype D] (ht₁ : t₁ ≤ T) (hT : 2 * n + t₂ + t₁ ≤ T)
    [DecidablePred fun answers : Fin T → D =>
      ¬ CollisionFree (commitTrace C n t₁ t₂ T commit opening answers)]
    [DecidablePred fun answers : Fin T → D =>
      Accepts (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
          (commitRoot C n t₁ t₂ T commit opening answers)
          (openingClaim C n t₁ t₂ T commit opening answers).I
          (openingClaim C n t₁ t₂ T commit opening answers).a
          (openingClaim C n t₁ t₂ T commit opening answers).pf ∧
        ¬ ExtractionExplains C dec n t₁ t₂ T commit opening answers] :
    (Finset.filter (fun answers : Fin T → D =>
        Accepts (C.withOracle (extractionOracle C n t₁ t₂ T commit opening answers)) n
            (commitRoot C n t₁ t₂ T commit opening answers)
            (openingClaim C n t₁ t₂ T commit opening answers).I
            (openingClaim C n t₁ t₂ T commit opening answers).a
            (openingClaim C n t₁ t₂ T commit opening answers).pf ∧
          ¬ ExtractionExplains C dec n t₁ t₂ T commit opening answers)
      Finset.univ).card ≤
      (t₁ * (t₁ - 1) / 2 + T * (2 * t₁ + 1)) * (Fintype.card D) ^ (T - 1) := by
  refine (mh_extract_rom_card_le_eligible C dec n t₁ t₂ T commit opening ht₁ hT).trans ?_
  gcongr

end Explains

end MH

end Merkle
