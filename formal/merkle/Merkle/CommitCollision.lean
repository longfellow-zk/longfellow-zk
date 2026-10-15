import Merkle.CheckPass

/-!
# Costing the commitment's collision events: the first-collision induction

`CheckPass.lean` reduces the commit-first slot layout to `commitInputsInjective` — the honest
commitment's `2n-1` oracle inputs are pairwise distinct — which fails only through three events: two
leaves colliding, two internal vertices colliding, and a leaf colliding with an internal vertex.  Only the first of those is a plain nonce birthday
event.  The other two are stated in terms of the *labels*, and bounding them looks circular: a
birthday argument over labels needs the labels to be answers at distinct tape slots, which is exactly
the distinctness the events are there to establish.

This file breaks the circle by inducting on a **threshold**.  The commitment pass runs downwards, so
when it reaches vertex `b` it has already processed every vertex above `b`; write
`commitInputsInjectiveAbove … b` for injectivity restricted to those.  Then:

* `commitPass_trace_take_nodup` — above the threshold the trace has no repeats, in the `take` form
  that `RandomOracle.lazyRun_slot_eq_of_take_nodup` consumes.  What the pass does *below* `b` is
  irrelevant, which is the whole point: no full-injectivity assumption is smuggled in.
* `commitLabels_eq_tapeAt_above` — hence every vertex above the threshold carries the tape entry at
  its own fixed index `2n-1-v`, a value independent of the nonces and of the message.
* `commitInputsInjective_of_no_tape_collision` — the downward induction. Stepping from `b+1` to `b`
  needs only vertex `b+1`, whose input is built from labels *strictly above* `b+1`, already pinned to
  the tape.  The three cases become three genuinely countable events:
  - two leaves: `leafInputCollision`, a nonce birthday event;
  - two internal vertices: their left children's labels are the tape at two distinct indices below
    `2n-1`, i.e. `RandomOracle.PairCollision T (slotPairs T (2n-1))`;
  - leaf against internal: the internal input is a function of the tape alone, so this is the
    nonce *guessing* event `nodeInputHit` against a nonce-independent set of at most `n` targets.

The conclusion discharges the `commitInputsInjective` hypothesis carried through `Hiding.lean` — it
is no longer an assumption but a consequence of three counted events.
-/

open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

open RandomOracle

universe uSalt uMsg uDigest uEnc

variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest} {Enc : Type uEnc}
variable [Inhabited D]

/-! ## Injectivity above a threshold -/

/-- The commitment's inputs are pairwise distinct among the vertices *above* `b` — the ones the
downward pass has already processed when it reaches `b`.  `commitInputsInjective` is the case
`b = 0`, definitionally. -/
def commitInputsInjectiveAbove [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (nonce : Fin n → Salt) (m : Fin n → M) (H : Enc → D) (b : ℕ) : Prop :=
  ∀ v w : ℕ, b < v → v < 2 * n → b < w → w < 2 * n → v ≠ w →
    ∀ x, commitInput C n nonce m H v = some x → commitInput C n nonce m H w ≠ some x

theorem commitInputsInjective_of_above_zero [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (nonce : Fin n → Salt) (m : Fin n → M) (H : Enc → D)
    (h : commitInputsInjectiveAbove C n nonce m H 0) :
    commitInputsInjective C n nonce m H := h

/-- Threshold refinement of `mem_commitPass_trace_vertex`: an input among the pass's *first `N`*
queries belongs to one of the *last `N`* vertices it processed. -/
theorem mem_commitPass_trace_take_vertex [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (nonce : Fin n → Salt) (m : Fin n → M) (H : Enc → D) :
    ∀ (k : ℕ) (vals : ℕ → D), k < 2 * n →
      (∀ v, k < v → vals v = commitLabels (C.withOracle H) n nonce m v) →
      ∀ (N : ℕ), ∀ x ∈ ((((commitPass C n nonce m k vals).run H).2.map Prod.fst).take N),
        ∃ v, k - N < v ∧ 0 < v ∧ v ≤ k ∧ commitInput C n nonce m H v = some x := by
  intro k
  induction k with
  | zero => intro vals _ _ N x hx; simp [commitPass] at hx
  | succ k ih =>
    intro vals hk hinv N x hx
    match N with
    | 0 => simp at hx
    | N + 1 =>
      by_cases hleaf : n ≤ k + 1 ∧ k + 1 < 2 * n
      · have hcv : commitLabels (C.withOracle H) n nonce m (k + 1) =
            H (C.leafEnc (nonce ⟨k + 1 - n, by omega⟩, m ⟨k + 1 - n, by omega⟩)) := by
          rw [commitLabels_leaf (C.withOracle H) n nonce m (k + 1) hleaf]; rfl
        rw [commitPass_step_leaf C n nonce m k vals hleaf, Tree.run_query] at hx
        simp only [List.map_cons, List.take_succ_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨k + 1, by omega, by omega, by omega, by rw [commitInput, dif_pos hleaf]⟩
        · obtain ⟨v, hvN, hv, hvk, hvx⟩ := ih _ (by omega)
            (commitPass_invariant_update C n nonce m H k vals hinv _ hcv) N x hx
          exact ⟨v, by omega, hv, by omega, hvx⟩
      · by_cases hint : 0 < k + 1 ∧ k + 1 < n
        · have hcv : commitLabels (C.withOracle H) n nonce m (k + 1) =
              H (C.nodeEnc (vals (2 * (k + 1)), vals (2 * (k + 1) + 1))) := by
            rw [commitLabels_node (C.withOracle H) n nonce m (k + 1) hint,
              hinv _ (by omega), hinv _ (by omega)]
            rfl
          rw [commitPass_step_node C n nonce m k vals hleaf hint, Tree.run_query] at hx
          simp only [List.map_cons, List.take_succ_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · refine ⟨k + 1, by omega, by omega, by omega, ?_⟩
            rw [commitInput, dif_neg hleaf, if_pos hint, hinv _ (by omega), hinv _ (by omega)]
          · obtain ⟨v, hvN, hv, hvk, hvx⟩ := ih _ (by omega)
              (commitPass_invariant_update C n nonce m H k vals hinv _ hcv) N x hx
            exact ⟨v, by omega, hv, by omega, hvx⟩
        · -- unreachable: below `2n` every vertex is a leaf or an internal node
          exact absurd hk (by omega)

/-- **Above the threshold the commitment's queries never repeat.**  Threshold refinement of
`commitPass_trace_nodup`: only the vertices above `b` are assumed to present distinct inputs, and
only the first `N` trace entries — the ones they produced — are claimed `Nodup`. -/
theorem commitPass_trace_take_nodup [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (nonce : Fin n → Salt) (m : Fin n → M) (H : Enc → D) (b : ℕ)
    (hinj : commitInputsInjectiveAbove C n nonce m H b) :
    ∀ (k : ℕ) (vals : ℕ → D), k < 2 * n →
      (∀ v, k < v → vals v = commitLabels (C.withOracle H) n nonce m v) →
      ∀ N, b ≤ k - N →
        ((((commitPass C n nonce m k vals).run H).2.map Prod.fst).take N).Nodup := by
  intro k
  induction k with
  | zero => intro vals _ _ N _; simp [commitPass]
  | succ k ih =>
    intro vals hk hinv N hbN
    match N with
    | 0 => simp
    | N + 1 =>
      by_cases hleaf : n ≤ k + 1 ∧ k + 1 < 2 * n
      · have hcv : commitLabels (C.withOracle H) n nonce m (k + 1) =
            H (C.leafEnc (nonce ⟨k + 1 - n, by omega⟩, m ⟨k + 1 - n, by omega⟩)) := by
          rw [commitLabels_leaf (C.withOracle H) n nonce m (k + 1) hleaf]; rfl
        have hself : commitInput C n nonce m H (k + 1) =
            some (C.leafEnc (nonce ⟨k + 1 - n, by omega⟩, m ⟨k + 1 - n, by omega⟩)) := by
          rw [commitInput, dif_pos hleaf]
        rw [commitPass_step_leaf C n nonce m k vals hleaf, Tree.run_query]
        simp only [List.map_cons, List.take_succ_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, ih _ (by omega)
          (commitPass_invariant_update C n nonce m H k vals hinv _ hcv) N (by omega)⟩
        obtain ⟨v, hvN, hv, hvk, hvx⟩ := mem_commitPass_trace_take_vertex C n nonce m H k _
          (by omega) (commitPass_invariant_update C n nonce m H k vals hinv _ hcv) N _ hmem
        exact hinj (k + 1) v (by omega) (by omega) (by omega) (by omega) (by omega) _ hself hvx
      · by_cases hint : 0 < k + 1 ∧ k + 1 < n
        · have hcv : commitLabels (C.withOracle H) n nonce m (k + 1) =
              H (C.nodeEnc (vals (2 * (k + 1)), vals (2 * (k + 1) + 1))) := by
            rw [commitLabels_node (C.withOracle H) n nonce m (k + 1) hint,
              hinv _ (by omega), hinv _ (by omega)]
            rfl
          have hself : commitInput C n nonce m H (k + 1) =
              some (C.nodeEnc (vals (2 * (k + 1)), vals (2 * (k + 1) + 1))) := by
            rw [commitInput, dif_neg hleaf, if_pos hint, hinv _ (by omega), hinv _ (by omega)]
          rw [commitPass_step_node C n nonce m k vals hleaf hint, Tree.run_query]
          simp only [List.map_cons, List.take_succ_cons, List.nodup_cons]
          refine ⟨fun hmem => ?_, ih _ (by omega)
            (commitPass_invariant_update C n nonce m H k vals hinv _ hcv) N (by omega)⟩
          obtain ⟨v, hvN, hv, hvk, hvx⟩ := mem_commitPass_trace_take_vertex C n nonce m H k _
            (by omega) (commitPass_invariant_update C n nonce m H k vals hinv _ hcv) N _ hmem
          exact hinj (k + 1) v (by omega) (by omega) (by omega) (by omega) (by omega) _ hself hvx
        · have hcv : commitLabels (C.withOracle H) n nonce m (k + 1) = default := by
            rw [commitLabels, dif_neg hleaf, dif_neg hint]
          rw [commitPass_step_none C n nonce m k vals hleaf hint, Tree.run_weaken]
          exact ih _ (by omega) (commitPass_invariant_update C n nonce m H k vals hinv _ hcv)
            (N + 1) (by omega)

/-- **Above the threshold, every label is the tape at a fixed index.**  Threshold refinement of
`commitLabels_eq_tape`, and the lemma that makes the induction non-circular: pinning vertex `v`'s
label needs distinctness only among the vertices above `b`, never among all of them.

No range hypothesis on `T` is needed — the answer *is* `tapeAt`, by construction. -/
theorem commitLabels_eq_tapeAt_above [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D) (b : ℕ)
    (hinj : commitInputsInjectiveAbove C n nonce m (commitOracle C n nonce m answers) b)
    (v : ℕ) (hvb : b < v) (hv : v ≤ 2 * n - 1) :
    commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m v =
      tapeAt answers default (2 * n - 1 - v) := by
  classical
  have hinvinit : ∀ w, 2 * n - 1 < w →
      (fun _ => (default : D)) w =
        commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m w :=
    fun w hw => (commitLabels_of_ge (S := C.withOracle (commitOracle C n nonce m answers))
      n nonce m w (by omega)).symm
  have hrun : (commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers) =
      ((lazyRun answers default (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1,
        (lazyRun answers default
          (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2) :=
    lazyRun_eq_run answers default _ [] _ fun _ => rfl
  have htr : ((commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers)).2 =
      (lazyRun answers default (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2 := by
    rw [hrun]
  have hlen : ((commitPass C n nonce m (2 * n - 1) fun _ => default).run
      (commitOracle C n nonce m answers)).2.length = 2 * n - 1 :=
    commitPass_trace_length C n hn nonce m _ (2 * n - 1) _ (le_refl _)
  have hnd : ((((commitPass C n nonce m (2 * n - 1) fun _ => default).run
      (commitOracle C n nonce m answers)).2.map Prod.fst).take (2 * n - 1 - b)).Nodup :=
    commitPass_trace_take_nodup C n nonce m _ b hinj (2 * n - 1) _ (by omega) hinvinit
      (2 * n - 1 - b) (by omega)
  obtain ⟨qa, hqamem, hqasnd⟩ := Option.map_eq_some_iff.mp
    (commitPass_trace_getElem C n hn nonce m (commitOracle C n nonce m answers)
      (2 * n - 1) _ (le_refl _) hinvinit v (by omega) hv)
  have hlt : 2 * n - 1 - v < ((lazyRun answers default
      (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2.map Prod.fst).length := by
    rw [List.length_map, ← htr, hlen]
    omega
  have hget : ((lazyRun answers default
      (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2.map Prod.fst)[2 * n - 1 - v] =
      qa.1 := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hlt, ← htr, List.getElem?_map, hqamem]
    rfl
  have hidx : (lazyRun answers default
      (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.1.idxOf qa.1 =
      2 * n - 1 - v := by
    rw [← hget]
    exact lazyRun_slot_eq_of_take_nodup answers default _ (2 * n - 1 - b)
      (by rw [← htr]; exact hnd) _ (by omega) hlt
  have hslot := lazyRun_trace_slot answers default
    (commitPass C n nonce m (2 * n - 1) fun _ => default) [] qa
    (by rw [← htr]; exact List.mem_of_getElem? hqamem)
  rw [← hqasnd, hslot.2, hidx]

/-! ## The three countable events -/

/-- Two honest leaf inputs coincide: the nonce birthday event.  Stated at the codec, so that it is
available before an oracle is fixed. -/
def leafInputCollision (C : Codec Salt M D Enc) (n : ℕ) (nonce : Fin n → Salt)
    (m : Fin n → M) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ C.leafEnc (nonce i, m i) = C.leafEnc (nonce j, m j)

/-- The node inputs the honest commitment presents, read off the tape alone.  Off the threshold
injectivity, internal vertex `c`'s children carry the tape at indices `2n-1-2c` and `2n-2-2c`, so
this finite set of at most `n` encodings knows nothing about the nonces — which is exactly what a
nonce-guessing count requires of its target set. -/
def nodeInputs [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) {T : ℕ}
    (answers : Fin T → D) : Finset Enc :=
  Finset.image (fun c : Fin n =>
    C.nodeEnc (tapeAt answers default (2 * n - 1 - 2 * c.val),
      tapeAt answers default (2 * n - 2 - 2 * c.val))) Finset.univ

theorem nodeInputs_card_le [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) {T : ℕ}
    (answers : Fin T → D) : (nodeInputs C n answers).card ≤ n := by
  rw [nodeInputs]
  exact le_trans Finset.card_image_le (by simp)

/-- A leaf input hits one of the tape-determined node inputs: the cross event, in the shape
`Hiding.nonceGuess_card_le` consumes. -/
def nodeInputHit [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (nonce : Fin n → Salt)
    (m : Fin n → M) {T : ℕ} (answers : Fin T → D) : Prop :=
  ∃ i : Fin n, C.leafEnc (nonce i, m i) ∈ nodeInputs C n answers

instance leafInputCollisionDecidable [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (m : Fin n → M) :
    DecidablePred fun nonce : Fin n → Salt => leafInputCollision C n nonce m := by
  intro nonce
  unfold leafInputCollision
  infer_instance

instance nodeInputHitDecidable [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (m : Fin n → M) {T : ℕ} (answers : Fin T → D) :
    DecidablePred fun nonce : Fin n → Salt => nodeInputHit C n nonce m answers := by
  intro nonce
  unfold nodeInputHit
  infer_instance

/-! ## The first-collision induction -/

/-- **The commitment's inputs are pairwise distinct off three counted events.**

Downward induction on the threshold.  Everything above `b+1` is already distinct, so its labels are
tape entries at fixed indices; vertex `b+1`'s input is built from those; and a collision with any
vertex above it is a leaf birthday collision, a repeat of the tape at two distinct slots below
`2n-1`, or a leaf encoding hitting the nonce-independent set `nodeInputs`.

This replaces `commitInputsInjective` as a *hypothesis* everywhere downstream: the three disjuncts
are events over the nonce/tape sample space, each with its own count. -/
theorem commitInputsInjective_of_no_tape_collision [DecidableEq Enc] (C : Codec Salt M D Enc)
    (n : ℕ) (hn : 0 < n) (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hT : 2 * n - 1 ≤ T) (hinjC : C.Inj)
    (hleafcol : ¬ leafInputCollision C n nonce m)
    (hpair : ¬ PairCollision T (slotPairs T (2 * n - 1)) answers)
    (hguess : ¬ nodeInputHit C n nonce m answers) :
    commitInputsInjective C n nonce m (commitOracle C n nonce m answers) := by
  refine commitInputsInjective_of_above_zero C n nonce m _ ?_
  have key : ∀ d b : ℕ, 2 * n ≤ b + d →
      commitInputsInjectiveAbove C n nonce m (commitOracle C n nonce m answers) b := by
    intro d
    induction d with
    | zero => intro b hb v w hv hvlt; exact absurd hvlt (by omega)
    | succ d ih =>
      intro b hb
      have habove : commitInputsInjectiveAbove C n nonce m
          (commitOracle C n nonce m answers) (b + 1) := ih (b + 1) (by omega)
      -- Labels strictly above `b+1` are tape entries at their own fixed indices.
      have hlab : ∀ u : ℕ, b + 1 < u → u ≤ 2 * n - 1 →
          commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m u =
            tapeAt answers default (2 * n - 1 - u) :=
        fun u hu hu2 => commitLabels_eq_tapeAt_above C n hn nonce m answers (b + 1) habove u hu hu2
      -- The step: vertex `b+1` against any vertex above it.
      have hstep : ∀ w : ℕ, b + 1 < w → w < 2 * n → ∀ x,
          commitInput C n nonce m (commitOracle C n nonce m answers) (b + 1) = some x →
          commitInput C n nonce m (commitOracle C n nonce m answers) w = some x → False := by
        intro w hbw hwlt x hxc hxw
        unfold commitInput at hxc hxw
        split at hxc
        · rename_i hcleaf
          split at hxw
          · -- two leaves: a nonce collision
            rename_i hwleaf
            refine hleafcol ⟨⟨b + 1 - n, by omega⟩, ⟨w - n, by omega⟩, ?_, ?_⟩
            · intro hij
              have := Fin.mk.inj_iff.mp hij
              omega
            · exact (Option.some_inj.mp hxc).trans (Option.some_inj.mp hxw).symm
          · split at hxw
            · -- impossible: `w > b+1 ≥ n` cannot be internal
              rename_i hwint
              omega
            · exact absurd hxw (by simp)
        · split at hxc
          · rename_i hcint
            have hlabL : commitLabels (C.withOracle (commitOracle C n nonce m answers))
                n nonce m (2 * (b + 1)) =
                tapeAt answers default (2 * n - 1 - 2 * (b + 1)) :=
              hlab _ (by omega) (by omega)
            have hlabR : commitLabels (C.withOracle (commitOracle C n nonce m answers))
                n nonce m (2 * (b + 1) + 1) =
                tapeAt answers default (2 * n - 2 - 2 * (b + 1)) := by
              rw [hlab _ (by omega) (by omega),
                show 2 * n - 1 - (2 * (b + 1) + 1) = 2 * n - 2 - 2 * (b + 1) by omega]
            split at hxw
            · -- cross: the internal input is tape-determined, so this is a nonce guess
              rename_i hwleaf
              refine hguess ⟨⟨w - n, by omega⟩, ?_⟩
              rw [nodeInputs, Finset.mem_image]
              refine ⟨⟨b + 1, hcint.2⟩, Finset.mem_univ _, ?_⟩
              show C.nodeEnc (tapeAt answers default (2 * n - 1 - 2 * (b + 1)),
                  tapeAt answers default (2 * n - 2 - 2 * (b + 1))) = _
              rw [← hlabL, ← hlabR]
              exact (Option.some_inj.mp hxc).trans (Option.some_inj.mp hxw).symm
            · split at hxw
              · -- two internal vertices: the tape repeats at two distinct slots below `2n-1`
                rename_i hwint
                have hlabW : commitLabels (C.withOracle (commitOracle C n nonce m answers))
                    n nonce m (2 * w) =
                    tapeAt answers default (2 * n - 1 - 2 * w) :=
                  hlab _ (by omega) (by omega)
                have hnode := hinjC.node
                  ((Option.some_inj.mp hxc).trans (Option.some_inj.mp hxw).symm)
                have hchild : tapeAt answers default (2 * n - 1 - 2 * (b + 1)) =
                    tapeAt answers default (2 * n - 1 - 2 * w) := by
                  rw [← hlabL, ← hlabW]
                  exact congrArg Prod.fst hnode
                have h1 : 2 * n - 1 - 2 * (b + 1) < T := by omega
                have h2 : 2 * n - 1 - 2 * w < T := by omega
                rw [tapeAt, dif_pos h1, tapeAt, dif_pos h2] at hchild
                refine hpair ⟨(⟨2 * n - 1 - 2 * w, h2⟩, ⟨2 * n - 1 - 2 * (b + 1), h1⟩), ?_,
                  hchild.symm⟩
                rw [slotPairs, Finset.mem_filter]
                refine ⟨Finset.mem_univ _, ?_, ?_⟩
                · show 2 * n - 1 - 2 * w < 2 * n - 1 - 2 * (b + 1)
                  omega
                · show 2 * n - 1 - 2 * (b + 1) < 2 * n - 1
                  omega
              · exact absurd hxw (by simp)
          · exact absurd hxc (by simp)
      intro v w hv hvlt hw hwlt hvw x hxv hxw
      rcases Nat.lt_or_ge (b + 1) v with hv' | hv'
      · rcases Nat.lt_or_ge (b + 1) w with hw' | hw'
        · exact habove v w hv' hvlt hw' hwlt hvw x hxv hxw
        · have hweq : w = b + 1 := by omega
          subst hweq
          exact hstep v hv' hvlt x hxw hxv
      · have hveq : v = b + 1 := by omega
        subst hveq
        exact hstep w (by omega) hwlt x hxv hxw
  exact key (2 * n) 0 (by omega)

/-- Contrapositive form: a failure of the commitment's input distinctness *is* one of three events.
This is the shape the counting sections consume. -/
theorem commitInputsInjective_failure_disj [DecidableEq Enc] (C : Codec Salt M D Enc)
    (n : ℕ) (hn : 0 < n) (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hT : 2 * n - 1 ≤ T) (hinjC : C.Inj)
    (h : ¬ commitInputsInjective C n nonce m (commitOracle C n nonce m answers)) :
    leafInputCollision C n nonce m ∨
      PairCollision T (slotPairs T (2 * n - 1)) answers ∨
      nodeInputHit C n nonce m answers := by
  by_contra hc
  exact h (commitInputsInjective_of_no_tape_collision C n hn nonce m answers hT hinjC
    (fun hx => hc (Or.inl hx)) (fun hx => hc (Or.inr (Or.inl hx)))
    (fun hx => hc (Or.inr (Or.inr hx))))

end MH

end Merkle
