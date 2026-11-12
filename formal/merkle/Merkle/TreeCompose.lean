import Merkle.LazyTape

/-!
# Composing bounded executions, and lazy sampling as a total oracle

The binding and extraction games run *two* things against the same oracle — the adversary and the
verifier's reconstruction — because the events they cost involve queries from both, and only
queried inputs occupy slots.  This file supplies the two pieces that needs.

**Composition.**  `Tree.bind` runs one bounded execution and then another, adding the query budgets;
`Tree.map` and `Tree.weaken`/`Tree.weakenAdd` are the bookkeeping around it.  The fuel of
`Tree.bind` is deliberately `f₂ + f₁` rather than `f₁ + f₂`: `Nat.add` recurses on its second
argument, so `f₂ + (g + 1)` is *definitionally* `(f₂ + g) + 1` and the query case needs no cast.

**Lazy sampling is a total oracle.**  `lazyRun_eq_run` says the lazy execution against a tape
coincides — same output, same trace — with the ordinary execution against the total oracle

    H x = tape (slot of x in the final seen-list)

This is what makes the lazy model faithful rather than merely convenient: a game may sample the
oracle lazily and still be *stated* with a total oracle, with acceptance evaluated against it.
-/

open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace RandomOracle

universe uQ uD uA uB uS

variable {Q : Type uQ} {D : Type uD} {A : Type uA} {B : Type uB}

/-! ## Fuel weakening -/

/-- A `f`-query execution is an `f+1`-query execution. -/
def Tree.weaken : {f : ℕ} → Tree Q D A f → Tree Q D A (f + 1)
  | _, .done a => .done a
  | _, .query q next => .query q fun y => (next y).weaken

/-- Weakening by a fixed amount. -/
def Tree.weakenAdd : {f : ℕ} → (k : ℕ) → Tree Q D A f → Tree Q D A (f + k)
  | _, 0, c => c
  | _, k + 1, c => (Tree.weakenAdd k c).weaken

/-- Post-process the output of an execution. -/
def Tree.map : {f : ℕ} → Tree Q D A f → (A → B) → Tree Q D B f
  | _, .done a, g => .done (g a)
  | _, .query q next, g => .query q fun y => (next y).map g

/-- Run one execution, then a second chosen from its output.  The fuel order `f₂ + f₁` keeps the
query case cast-free. -/
def Tree.bind {f₂ : ℕ} :
    {f₁ : ℕ} → Tree Q D A f₁ → (A → Tree Q D B f₂) → Tree Q D B (f₂ + f₁)
  | _, .done a, k => Tree.weakenAdd _ (k a)
  | _, .query q next, k => .query q fun y => (next y).bind k

@[simp] theorem Tree.run_weaken {f : ℕ} (c : Tree Q D A f) (H : Q → D) :
    c.weaken.run H = c.run H := by
  induction c with
  | done a => rfl
  | @query f q next ih => simp [Tree.weaken, Tree.run_query, ih]

@[simp] theorem Tree.run_weakenAdd {f : ℕ} (k : ℕ) (c : Tree Q D A f) (H : Q → D) :
    (c.weakenAdd k).run H = c.run H := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Tree.weakenAdd, Tree.run_weaken, ih]

@[simp] theorem Tree.run_map {f : ℕ} (c : Tree Q D A f) (g : A → B) (H : Q → D) :
    (c.map g).run H = (g (c.run H).1, (c.run H).2) := by
  induction c with
  | done a => rfl
  | @query f q next ih => simp [Tree.map, Tree.run_query, ih]

/-- The trace of a composed execution is the concatenation of the two phases' traces, and its
output is the second phase's output. -/
theorem Tree.run_bind {f₁ f₂ : ℕ} (c : Tree Q D A f₁) (k : A → Tree Q D B f₂) (H : Q → D) :
    (c.bind k).run H =
      (((k (c.run H).1).run H).1, (c.run H).2 ++ ((k (c.run H).1).run H).2) := by
  induction c with
  | done a => simp [Tree.bind]
  | @query f q next ih => simp [Tree.bind, Tree.run_query, ih]

/-! ## Lazy sampling against a total oracle -/

section Lazy

variable [DecidableEq Q] {T : ℕ}

/-- **Lazy sampling is a total oracle.**

Let `final` be the seen-list at the end of a lazy execution and let `H` answer every input from
its slot in `final`.  Then the ordinary execution against `H` has the same output and the same
trace as the lazy execution.

The hypothesis is stated for *all* inputs, which is how the game uses it: `H` is defined by this
formula, so `hH` is `rfl`.  The proof needs it only on the queried inputs, where slot permanence
(`lazyRun_seen_prefix`) makes the answer read at query time agree with the answer `H` gives. -/
theorem lazyRun_eq_run (tape : Fin T → D) (dflt : D) :
    ∀ {f : ℕ} (c : Tree Q D A f) (seen : List Q) (H : Q → D),
      (∀ x, H x = tapeAt tape dflt ((lazyRun tape dflt c seen).2.1.idxOf x)) →
      c.run H = ((lazyRun tape dflt c seen).1, (lazyRun tape dflt c seen).2.2)
  | _, .done a, _, _, _ => rfl
  | _, .query q next, seen, H, hH => by
      set seen' := if q ∈ seen then seen else seen ++ [q] with hseen'
      set y := tapeAt tape dflt (seen'.idxOf q) with hy
      have hmemq : q ∈ seen' := by
        by_cases hq : q ∈ seen
        · simp [hseen', hq]
        · simp [hseen', hq]
      have hfinal : (lazyRun tape dflt (Tree.query q next) seen).2.1 =
          (lazyRun tape dflt (next y) seen').2.1 := rfl
      have hpref : seen' <+: (lazyRun tape dflt (next y) seen').2.1 :=
        lazyRun_seen_prefix tape dflt (next y) seen'
      have hidx : (lazyRun tape dflt (next y) seen').2.1.idxOf q = seen'.idxOf q := by
        obtain ⟨rest, hrest⟩ := hpref
        rw [← hrest, List.idxOf_append_of_mem hmemq]
      have hHq : H q = y := by
        rw [hH q, hfinal, hidx, hy]
      have hH' : ∀ x, H x =
          tapeAt tape dflt ((lazyRun tape dflt (next y) seen').2.1.idxOf x) := by
        intro x
        rw [hH x, hfinal]
      have hrec := lazyRun_eq_run tape dflt (next y) seen' H hH'
      rw [Tree.run_query, lazyRun_query]
      simp only [hHq, hrec, ← hseen', ← hy]

/-- **Locality.**  A lazy execution reads only the slots it occupies: two tapes agreeing on every
slot below the final seen-list's length give the same execution.

This is what makes a value produced by an early phase *independent* of the later phases' slots — the
`HitTarget` obligation of `FreshHit.lean`, which is how a fresh query landing on an already-derived
value gets counted. -/
theorem lazyRun_congr_of_agree (tape tape' : Fin T → D) (dflt : D) :
    ∀ {f : ℕ} (c : Tree Q D A f) (seen : List Q),
      (∀ i : Fin T, i.val < (lazyRun tape dflt c seen).2.1.length → tape i = tape' i) →
      lazyRun tape' dflt c seen = lazyRun tape dflt c seen
  | _, .done _, _, _ => rfl
  | _, .query q next, seen, hagree => by
      set seen' := if q ∈ seen then seen else seen ++ [q] with hseen'
      set y := tapeAt tape dflt (seen'.idxOf q) with hy
      have hmemq : q ∈ seen' := by
        by_cases hq : q ∈ seen
        · simp [hseen', hq]
        · simp [hseen', hq]
      have hfinal : (lazyRun tape dflt (Tree.query q next) seen).2.1 =
          (lazyRun tape dflt (next y) seen').2.1 := rfl
      have hpref : seen' <+: (lazyRun tape dflt (next y) seen').2.1 :=
        lazyRun_seen_prefix tape dflt (next y) seen'
      have hidx : seen'.idxOf q < (lazyRun tape dflt (next y) seen').2.1.length :=
        lt_of_lt_of_le (List.idxOf_lt_length_of_mem hmemq) hpref.length_le
      have hy' : tapeAt tape' dflt (seen'.idxOf q) = y := by
        rw [hy, tapeAt, tapeAt]
        by_cases hlt : seen'.idxOf q < T
        · rw [dif_pos hlt, dif_pos hlt]
          exact (hagree ⟨seen'.idxOf q, hlt⟩ (by rw [hfinal]; exact hidx)).symm
        · rw [dif_neg hlt, dif_neg hlt]
      have hagree' : ∀ i : Fin T,
          i.val < (lazyRun tape dflt (next y) seen').2.1.length → tape i = tape' i := by
        intro i hi
        exact hagree i (by rw [hfinal]; exact hi)
      have hrec := lazyRun_congr_of_agree tape tape' dflt (next y) seen' hagree'
      rw [lazyRun_query, lazyRun_query]
      simp only [← hseen', hy', ← hy, hrec]

/-! ### Lazy runs compose

`run_bind` and friends describe executions against a *total* oracle.  These are their lazy
counterparts, needed once a game has to talk about a phase of a run rather than the whole of it —
for instance the `i`-th commitment of a `k`-commitment experiment, which is neither the whole run
nor its first phase. -/

@[simp] theorem lazyRun_weaken (tape : Fin T → D) (dflt : D) :
    ∀ {f : ℕ} (c : Tree Q D A f) (seen : List Q),
      lazyRun tape dflt c.weaken seen = lazyRun tape dflt c seen
  | _, .done _, _ => rfl
  | _, .query q next, seen => by
      show lazyRun tape dflt (Tree.query q fun y => (next y).weaken) seen = _
      rw [lazyRun_query, lazyRun_query]
      dsimp only
      rw [lazyRun_weaken tape dflt
        (next (tapeAt tape dflt ((if q ∈ seen then seen else seen ++ [q]).idxOf q)))
        (if q ∈ seen then seen else seen ++ [q])]

@[simp] theorem lazyRun_weakenAdd (tape : Fin T → D) (dflt : D) {f : ℕ} (m : ℕ)
    (c : Tree Q D A f) (seen : List Q) :
    lazyRun tape dflt (c.weakenAdd m) seen = lazyRun tape dflt c seen := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Tree.weakenAdd, lazyRun_weaken, ih]

@[simp] theorem lazyRun_map (tape : Fin T → D) (dflt : D) (g : A → B) :
    ∀ {f : ℕ} (c : Tree Q D A f) (seen : List Q),
      lazyRun tape dflt (c.map g) seen =
        (g (lazyRun tape dflt c seen).1, (lazyRun tape dflt c seen).2.1,
          (lazyRun tape dflt c seen).2.2)
  | _, .done _, _ => rfl
  | _, .query q next, seen => by
      show lazyRun tape dflt (Tree.query q fun y => (next y).map g) seen = _
      rw [lazyRun_query, lazyRun_query]
      dsimp only
      rw [lazyRun_map tape dflt g
        (next (tapeAt tape dflt ((if q ∈ seen then seen else seen ++ [q]).idxOf q)))
        (if q ∈ seen then seen else seen ++ [q])]

/-- A composed execution, lazily: the phases run in order, sharing the slot layout, and the traces
concatenate. -/
theorem lazyRun_bind (tape : Fin T → D) (dflt : D) {f₂ : ℕ} (k : A → Tree Q D B f₂) :
    ∀ {f₁ : ℕ} (c : Tree Q D A f₁) (seen : List Q),
      lazyRun tape dflt (c.bind k) seen =
        ((lazyRun tape dflt (k (lazyRun tape dflt c seen).1) (lazyRun tape dflt c seen).2.1).1,
          (lazyRun tape dflt (k (lazyRun tape dflt c seen).1)
            (lazyRun tape dflt c seen).2.1).2.1,
          (lazyRun tape dflt c seen).2.2 ++
            (lazyRun tape dflt (k (lazyRun tape dflt c seen).1)
              (lazyRun tape dflt c seen).2.1).2.2)
  | f₁, .done a, seen => by
      show lazyRun tape dflt (Tree.weakenAdd f₁ (k a)) seen = _
      rw [lazyRun_weakenAdd]
      simp
  | _, .query q next, seen => by
      show lazyRun tape dflt (Tree.query q fun y => (next y).bind k) seen = _
      rw [lazyRun_query, lazyRun_query]
      dsimp only
      rw [lazyRun_bind tape dflt k
        (next (tapeAt tape dflt ((if q ∈ seen then seen else seen ++ [q]).idxOf q)))
        (if q ∈ seen then seen else seen ++ [q])]
      simp

/-- Every slot the execution occupies was really queried.  `lazyRun_trace_slot` is the converse —
together they say the seen-list past its starting point is exactly the set of queried inputs, which
is what lets "absent from the commitment stage" be stated against either one. -/
theorem lazyRun_mem_trace_of_mem_seen (tape : Fin T → D) (dflt : D) :
    ∀ {f : ℕ} (c : Tree Q D A f) (seen : List Q) (x : Q),
      x ∈ (lazyRun tape dflt c seen).2.1 → x ∉ seen →
      ∃ y, (x, y) ∈ (lazyRun tape dflt c seen).2.2
  | _, .done _, _, _, hmem, hns => absurd hmem hns
  | _, .query q next, seen, x, hmem, hns => by
      set seen' := if q ∈ seen then seen else seen ++ [q] with hseen'
      set y := tapeAt tape dflt (seen'.idxOf q) with hy
      rw [lazyRun_query]
      simp only [← hseen', ← hy]
      by_cases hxq : x = q
      · exact ⟨y, by simp [hxq]⟩
      · have hns' : x ∉ seen' := by
          by_cases hq : q ∈ seen
          · simpa [hseen', hq] using hns
          · simp only [hseen', hq, if_false]
            intro hc
            rcases List.mem_append.mp hc with h | h
            · exact hns h
            · exact hxq (by simpa using h)
        obtain ⟨y', hy'⟩ := lazyRun_mem_trace_of_mem_seen tape dflt (next y) seen' x hmem hns'
        exact ⟨y', List.mem_cons_of_mem _ hy'⟩

/-- A query the first phase never made occupies a slot at or after the first phase's range.  With
`lazyRun_congr_of_agree` this is what places a *fresh* query outside everything the first phase
determined. -/
theorem le_idxOf_of_not_mem_prefix {l r : List Q} (x : Q) (hx : x ∉ l) :
    l.length ≤ (l ++ r).idxOf x := by
  rw [List.idxOf_append_of_notMem hx]
  exact Nat.le_add_right _ _

/-- The first phase's seen-list is a prefix of the composed execution's, so a slot assigned during
the first phase means the same thing in the composed run.  This is what lets a game state its
`attempt` in terms of the binder alone while answering with the composed oracle. -/
theorem lazyRun_seen_prefix_bind (tape : Fin T → D) (dflt : D) {f₂ : ℕ}
    (k : A → Tree Q D B f₂) {f₁ : ℕ} (c : Tree Q D A f₁) (seen : List Q) :
    (lazyRun tape dflt c seen).2.1 <+: (lazyRun tape dflt (c.bind k) seen).2.1 := by
  rw [lazyRun_bind]
  exact lazyRun_seen_prefix tape dflt _ _

/-- **A phase of a run reads the same answers as it would alone**, provided its slots are a prefix
of the layout the oracle answers from.  `Tree.run_congr_on_trace` then replays it.

Stated against an arbitrary slot list rather than against `c.bind k`: what the argument actually
needs is the prefix property, and a phase can sit inside a run without being its syntactic first
`bind` — the `i`-th commitment of a `k`-commitment experiment, for instance. -/
theorem lazyRun_run_eq_of_prefix (tape : Fin T → D) (dflt : D)
    {f : ℕ} (c : Tree Q D A f) (seen : List Q) (H : Q → D) (final : List Q)
    (hH : ∀ x, H x = tapeAt tape dflt (final.idxOf x))
    (hpref : (lazyRun tape dflt c seen).2.1 <+: final) :
    c.run H = ((lazyRun tape dflt c seen).1, (lazyRun tape dflt c seen).2.2) := by
  set Hb : Q → D := fun x => tapeAt tape dflt ((lazyRun tape dflt c seen).2.1.idxOf x) with hHb
  have hb : c.run Hb = ((lazyRun tape dflt c seen).1, (lazyRun tape dflt c seen).2.2) :=
    lazyRun_eq_run tape dflt c seen Hb fun _ => rfl
  have hagree : ∀ qa ∈ (c.run Hb).2, H qa.1 = qa.2 := by
    intro qa hqa
    rw [hb] at hqa
    obtain ⟨hmem, hval⟩ := lazyRun_trace_slot tape dflt c seen qa hqa
    obtain ⟨rest, hrest⟩ := hpref
    rw [hH qa.1, ← hrest, List.idxOf_append_of_mem hmem, hval]
  rw [Tree.run_congr_on_trace c Hb H hagree, hb]

/-- The first phase of a composed execution reads the same answers as it would alone. -/
theorem lazyRun_prefix_run_eq (tape : Fin T → D) (dflt : D)
    {f₁ f₂ : ℕ} (c : Tree Q D A f₁) (k : A → Tree Q D B f₂) (seen : List Q) (H : Q → D)
    (hH : ∀ x, H x = tapeAt tape dflt ((lazyRun tape dflt (c.bind k) seen).2.1.idxOf x)) :
    c.run H = ((lazyRun tape dflt c seen).1, (lazyRun tape dflt c seen).2.2) :=
  lazyRun_run_eq_of_prefix tape dflt c seen H _ hH (lazyRun_seen_prefix_bind tape dflt k c seen)

/-! ### Distinct queries occupy consecutive slots

Lazy sampling assigns slot `i` to the `i`-th *distinct* query, so an execution whose queries happen
to repeat leaves gaps in the correspondence between query order and slot order.  When they do not
repeat, the correspondence is exact: the seen-list is the query list, and the `j`-th query sits at
slot `j`.

This is what makes a *fixed* slot index available to something that must not depend on the values —
a simulator, say — and it is the shape the commit-first hiding experiment needs: the honest
commitment runs first, from an empty seen-list, so off a nonce collision its queries are pairwise
distinct and its top query occupies a constant slot. -/

theorem lazyRun_seen_eq_of_nodup (tape : Fin T → D) (dflt : D) :
    ∀ {f : ℕ} (c : Tree Q D A f) (seen : List Q),
      ((lazyRun tape dflt c seen).2.2.map Prod.fst).Nodup →
      (∀ q ∈ (lazyRun tape dflt c seen).2.2.map Prod.fst, q ∉ seen) →
      (lazyRun tape dflt c seen).2.1 =
        seen ++ (lazyRun tape dflt c seen).2.2.map Prod.fst
  | _, .done _, seen, _, _ => by simp
  | _, .query q next, seen, hnodup, hfresh => by
      set seen' := if q ∈ seen then seen else seen ++ [q] with hseen'
      set y := tapeAt tape dflt (seen'.idxOf q) with hy
      rw [lazyRun_query] at hnodup hfresh ⊢
      simp only [← hseen', ← hy, List.map_cons] at hnodup hfresh ⊢
      have hq : q ∉ seen := hfresh q (by simp)
      have hseq : seen' = seen ++ [q] := by rw [hseen', if_neg hq]
      have hcons := List.nodup_cons.mp hnodup
      have hsubfresh : ∀ r ∈ (lazyRun tape dflt (next y) seen').2.2.map Prod.fst,
          r ∉ seen' := by
        intro r hr hc
        rw [hseq] at hc
        rcases List.mem_append.mp hc with h | h
        · exact hfresh r (List.mem_cons_of_mem _ hr) h
        · exact hcons.1 (by rwa [List.mem_singleton.mp h] at hr)
      rw [lazyRun_seen_eq_of_nodup tape dflt (next y) seen' hcons.2 hsubfresh, hseq,
        List.append_assoc, List.singleton_append]

/-- The `j`-th query of a repetition-free execution occupies slot `j`. -/
theorem lazyRun_slot_eq_of_nodup (tape : Fin T → D) (dflt : D) {f : ℕ} (c : Tree Q D A f)
    (hnodup : ((lazyRun tape dflt c []).2.2.map Prod.fst).Nodup)
    (j : ℕ) (hj : j < ((lazyRun tape dflt c []).2.2.map Prod.fst).length) :
    (lazyRun tape dflt c []).2.1.idxOf
        (((lazyRun tape dflt c []).2.2.map Prod.fst)[j]) = j := by
  have hseen := lazyRun_seen_eq_of_nodup tape dflt c [] hnodup (by simp)
  rw [hseen, List.nil_append]
  set l := (lazyRun tape dflt c []).2.2.map Prod.fst with hl
  have hmem : l[j] ∈ l := List.getElem_mem hj
  have hlt : l.idxOf l[j] < l.length := List.idxOf_lt_length_of_mem hmem
  have hget : l[l.idxOf l[j]] = l[j] := List.getElem_idxOf hlt
  exact (List.Nodup.getElem_inj_iff hnodup).mp hget

/-! ### Only a repetition-free *prefix* is needed

`lazyRun_slot_eq_of_nodup` asks the whole execution not to repeat.  A first-collision argument cannot
afford that: it wants to pin the slots of the queries made *before* the first repeat while saying
nothing about what happens after.  Since the seen-list only ever grows by appending, that is enough —
a slot assigned inside a repetition-free prefix is already final. -/

/-- The distinct queries of a repetition-free prefix form a prefix of the final seen-list. -/
theorem lazyRun_seen_prefix_of_take_nodup (tape : Fin T → D) (dflt : D) :
    ∀ {f : ℕ} (c : Tree Q D A f) (seen : List Q) (N : ℕ),
      (((lazyRun tape dflt c seen).2.2.map Prod.fst).take N).Nodup →
      (∀ q ∈ ((lazyRun tape dflt c seen).2.2.map Prod.fst).take N, q ∉ seen) →
      seen ++ ((lazyRun tape dflt c seen).2.2.map Prod.fst).take N <+:
        (lazyRun tape dflt c seen).2.1
  | _, .done _, seen, _, _, _ => by simp
  | _, .query _ _, seen, 0, _, _ => by
      simpa using lazyRun_seen_prefix tape dflt _ seen
  | _, .query q next, seen, (N + 1), hnodup, hfresh => by
      set seen' := if q ∈ seen then seen else seen ++ [q] with hseen'
      set y := tapeAt tape dflt (seen'.idxOf q) with hy
      rw [lazyRun_query] at hnodup hfresh ⊢
      simp only [← hseen', ← hy, List.map_cons, List.take_succ_cons] at hnodup hfresh ⊢
      have hq : q ∉ seen := hfresh q (by simp)
      have hseq : seen' = seen ++ [q] := by rw [hseen', if_neg hq]
      have hcons := List.nodup_cons.mp hnodup
      have hsubfresh : ∀ r ∈ ((lazyRun tape dflt (next y) seen').2.2.map Prod.fst).take N,
          r ∉ seen' := by
        intro r hr hc
        rw [hseq] at hc
        rcases List.mem_append.mp hc with h | h
        · exact hfresh r (List.mem_cons_of_mem _ hr) h
        · exact hcons.1 (by rwa [List.mem_singleton.mp h] at hr)
      have ih := lazyRun_seen_prefix_of_take_nodup tape dflt (next y) seen' N hcons.2 hsubfresh
      have hcalc : seen ++ q :: ((lazyRun tape dflt (next y) seen').2.2.map Prod.fst).take N =
          seen' ++ ((lazyRun tape dflt (next y) seen').2.2.map Prod.fst).take N := by
        simp only [hseq, List.append_assoc, List.singleton_append]
      rw [hcalc]
      exact ih

/-- **The `j`-th query occupies slot `j` as soon as the first `N` queries do not repeat.**  The
threshold version of `lazyRun_slot_eq_of_nodup`: what happens after the prefix is irrelevant. -/
theorem lazyRun_slot_eq_of_take_nodup (tape : Fin T → D) (dflt : D) {f : ℕ} (c : Tree Q D A f)
    (N : ℕ) (hnodup : (((lazyRun tape dflt c []).2.2.map Prod.fst).take N).Nodup)
    (j : ℕ) (hjN : j < N) (hj : j < ((lazyRun tape dflt c []).2.2.map Prod.fst).length) :
    (lazyRun tape dflt c []).2.1.idxOf
        (((lazyRun tape dflt c []).2.2.map Prod.fst)[j]) = j := by
  have hpref := lazyRun_seen_prefix_of_take_nodup tape dflt c [] N hnodup (by simp)
  rw [List.nil_append] at hpref
  obtain ⟨rest, hrest⟩ := hpref
  set l := (lazyRun tape dflt c []).2.2.map Prod.fst with hl
  have hjt : j < (l.take N).length := by rw [List.length_take]; omega
  have hmem : (l.take N)[j] ∈ l.take N := List.getElem_mem hjt
  have hgetl : (l.take N)[j] = l[j] := by simp
  rw [← hrest, List.idxOf_append_of_mem (hgetl ▸ hmem), ← hgetl]
  exact (List.Nodup.getElem_inj_iff hnodup).mp
    (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem))

/-! ### Identical-until-bad for two slot layouts

Two experiments whose earlier phases queried *different* inputs hand the same continuation two
different seen-lists.  If those lists have the same length and the continuation never asks about
either one's own inputs, it cannot tell them apart: a query it repeats reads the same offset into the
shared tail, and a fresh one reads the same offset past the end.  So its output and trace are
identical.

This is the identical-until-bad step the hiding argument needs, and it is what lets the distinguisher
run *inside* the lazy execution — taking genuinely fresh slots — rather than against a truncated
oracle. -/

/-- **Two bases are interchangeable for a query if it sees them the same way.**  Either it is absent
from both — then it takes the next free slot, common to both by `hlen` — or it is present in both at
the same offset.  This is the exact condition the induction below consumes.

`lazyRun_congr_of_base` is the special case where the continuation avoids both bases entirely
(`baseCompat_of_not_mem`).  The general form is what a *partially* shared base needs: two honest
commitments to messages agreeing on the opened set present the same inputs everywhere except at the
leaves where the messages differ, so a distinguisher may freely query the shared ones. -/
def BaseCompat (base₀ base₁ : List Q) (q : Q) : Prop :=
  (q ∈ base₀ ↔ q ∈ base₁) ∧ base₀.idxOf q = base₁.idxOf q

theorem baseCompat_of_not_mem {base₀ base₁ : List Q} (hlen : base₀.length = base₁.length)
    {q : Q} (h₀ : q ∉ base₀) (h₁ : q ∉ base₁) : BaseCompat base₀ base₁ q := by
  refine ⟨⟨fun h => absurd h h₀, fun h => absurd h h₁⟩, ?_⟩
  rw [List.idxOf_eq_length h₀, List.idxOf_eq_length h₁, hlen]

theorem lazyRun_congr_of_base_compat (tape : Fin T → D) (dflt : D) (base₀ base₁ : List Q)
    (hlen : base₀.length = base₁.length) :
    ∀ {f : ℕ} (c : Tree Q D A f) (tail : List Q),
      (∀ qa ∈ (lazyRun tape dflt c (base₀ ++ tail)).2.2, BaseCompat base₀ base₁ qa.1) →
      (lazyRun tape dflt c (base₀ ++ tail)).1 = (lazyRun tape dflt c (base₁ ++ tail)).1 ∧
        (lazyRun tape dflt c (base₀ ++ tail)).2.2 =
          (lazyRun tape dflt c (base₁ ++ tail)).2.2
  | _, .done _, _, _ => ⟨rfl, rfl⟩
  | _, .query q next, tail, hcompat => by
      have hq : BaseCompat base₀ base₁ q := by
        refine hcompat (q, tapeAt tape dflt
          ((if q ∈ base₀ ++ tail then base₀ ++ tail else (base₀ ++ tail) ++ [q]).idxOf q)) ?_
        rw [lazyRun_query]
        simp
      by_cases hb : q ∈ base₀
      · -- present in both bases, at the same offset
        have hb₁ : q ∈ base₁ := hq.1.mp hb
        have hmem : ∀ b : List Q, q ∈ b → q ∈ b ++ tail := fun b h =>
          List.mem_append.mpr (Or.inl h)
        rw [lazyRun_query, lazyRun_query]
        simp only [if_pos (hmem base₀ hb), if_pos (hmem base₁ hb₁),
          List.idxOf_append_of_mem hb, List.idxOf_append_of_mem hb₁, hq.2]
        have hrec := lazyRun_congr_of_base_compat tape dflt base₀ base₁ hlen
          (next (tapeAt tape dflt (base₁.idxOf q))) tail
          (by
            intro qa hqa
            refine hcompat qa ?_
            rw [lazyRun_query]
            simp only [if_pos (hmem base₀ hb), List.idxOf_append_of_mem hb, hq.2]
            exact List.mem_cons_of_mem _ hqa)
        exact ⟨hrec.1, by rw [hrec.2]⟩
      · have hb₁ : q ∉ base₁ := fun h => hb (hq.1.mpr h)
        by_cases hqt : q ∈ tail
        · -- a repeat inside the shared tail
          have hmem : ∀ b : List Q, q ∈ b ++ tail := fun b =>
            List.mem_append.mpr (Or.inr hqt)
          have hidx : ∀ b : List Q, q ∉ b →
              (b ++ tail).idxOf q = b.length + tail.idxOf q := fun b hbb =>
            List.idxOf_append_of_notMem hbb
          rw [lazyRun_query, lazyRun_query]
          simp only [if_pos (hmem base₀), if_pos (hmem base₁), hidx base₀ hb, hidx base₁ hb₁]
          rw [← hlen]
          have hrec := lazyRun_congr_of_base_compat tape dflt base₀ base₁ hlen
            (next (tapeAt tape dflt (base₀.length + tail.idxOf q))) tail
            (by
              intro qa hqa
              refine hcompat qa ?_
              rw [lazyRun_query]
              simp only [if_pos (hmem base₀), hidx base₀ hb]
              exact List.mem_cons_of_mem _ hqa)
          exact ⟨hrec.1, by rw [hrec.2]⟩
        · -- fresh: the next free slot, common to both by `hlen`
          have hnmem : ∀ b : List Q, q ∉ b → q ∉ b ++ tail := by
            intro b hbb hc
            rcases List.mem_append.mp hc with h | h
            · exact hbb h
            · exact hqt h
          have hidx : ∀ b : List Q, q ∉ b →
              (b ++ (tail ++ [q])).idxOf q = b.length + tail.length := by
            intro b hbb
            rw [List.idxOf_append_of_notMem hbb, List.idxOf_append_of_notMem hqt]
            simp
          have happ : ∀ b : List Q, (b ++ tail) ++ [q] = b ++ (tail ++ [q]) := fun b =>
            List.append_assoc b tail [q]
          rw [lazyRun_query, lazyRun_query]
          simp only [if_neg (hnmem base₀ hb), if_neg (hnmem base₁ hb₁), happ base₀, happ base₁,
            hidx base₀ hb, hidx base₁ hb₁]
          rw [← hlen]
          have hrec := lazyRun_congr_of_base_compat tape dflt base₀ base₁ hlen
            (next (tapeAt tape dflt (base₀.length + tail.length))) (tail ++ [q])
            (by
              intro qa hqa
              refine hcompat qa ?_
              rw [lazyRun_query]
              simp only [if_neg (hnmem base₀ hb), happ base₀, hidx base₀ hb]
              exact List.mem_cons_of_mem _ hqa)
          exact ⟨hrec.1, by rw [hrec.2]⟩

/-- **The prefix form.**  If the first `N` queries all see the two bases the same way, the first `N+1`
agree — the `(N+1)`-st is determined by the first `N` answers, so it is common to both runs even when
it is the query that breaks compatibility.

This is what a "one query catches one candidate" argument runs on: it must compare two runs *up to*
the first query that distinguishes them. -/
theorem lazyRun_take_congr_of_base_compat (tape : Fin T → D) (dflt : D) (base₀ base₁ : List Q)
    (hlen : base₀.length = base₁.length) :
    ∀ {f : ℕ} (c : Tree Q D A f) (tail : List Q) (N : ℕ),
      (∀ q ∈ ((lazyRun tape dflt c (base₀ ++ tail)).2.2.map Prod.fst).take N,
        BaseCompat base₀ base₁ q) →
      ((lazyRun tape dflt c (base₀ ++ tail)).2.2.map Prod.fst).take (N + 1) =
        ((lazyRun tape dflt c (base₁ ++ tail)).2.2.map Prod.fst).take (N + 1)
  | _, .done _, _, _, _ => by simp
  | _, .query _ _, _, 0, _ => by
      rw [lazyRun_query, lazyRun_query]
      simp
  | _, .query q next, tail, (N + 1), hcompat => by
      rw [lazyRun_query] at hcompat
      simp only [List.map_cons, List.take_succ_cons, List.mem_cons] at hcompat
      have hq : BaseCompat base₀ base₁ q := hcompat q (Or.inl rfl)
      have hsub : ∀ r ∈ ((lazyRun tape dflt (next (tapeAt tape dflt
          ((if q ∈ base₀ ++ tail then base₀ ++ tail
            else (base₀ ++ tail) ++ [q]).idxOf q))) (if q ∈ base₀ ++ tail then base₀ ++ tail
              else (base₀ ++ tail) ++ [q])).2.2.map Prod.fst).take N,
          BaseCompat base₀ base₁ r :=
        fun r hr => hcompat r (Or.inr hr)
      by_cases hb : q ∈ base₀
      · -- in both bases, at the same offset
        have hb₁ : q ∈ base₁ := hq.1.mp hb
        have hmem : ∀ b : List Q, q ∈ b → q ∈ b ++ tail := fun b h =>
          List.mem_append.mpr (Or.inl h)
        rw [lazyRun_query, lazyRun_query]
        simp only [if_pos (hmem base₀ hb), if_pos (hmem base₁ hb₁),
          List.idxOf_append_of_mem hb, List.idxOf_append_of_mem hb₁, hq.2, List.map_cons,
          List.take_succ_cons]
        refine congrArg _ ?_
        refine lazyRun_take_congr_of_base_compat tape dflt base₀ base₁ hlen
          (next (tapeAt tape dflt (base₁.idxOf q))) tail N ?_
        intro r hr
        refine hsub r ?_
        simp only [if_pos (hmem base₀ hb), List.idxOf_append_of_mem hb, hq.2]
        exact hr
      · have hb₁ : q ∉ base₁ := fun h => hb (hq.1.mpr h)
        by_cases hqt : q ∈ tail
        · -- a repeat inside the shared tail
          have hmem : ∀ b : List Q, q ∈ b ++ tail := fun b =>
            List.mem_append.mpr (Or.inr hqt)
          have hidx : ∀ b : List Q, q ∉ b →
              (b ++ tail).idxOf q = b.length + tail.idxOf q := fun b hbb =>
            List.idxOf_append_of_notMem hbb
          rw [lazyRun_query, lazyRun_query]
          simp only [if_pos (hmem base₀), if_pos (hmem base₁), hidx base₀ hb, hidx base₁ hb₁,
            ← hlen, List.map_cons, List.take_succ_cons]
          refine congrArg _ ?_
          refine lazyRun_take_congr_of_base_compat tape dflt base₀ base₁ hlen
            (next (tapeAt tape dflt (base₀.length + tail.idxOf q))) tail N ?_
          intro r hr
          refine hsub r ?_
          simp only [if_pos (hmem base₀), hidx base₀ hb]
          exact hr
        · -- fresh in both: the next free slot, common by `hlen`
          have hnmem : ∀ b : List Q, q ∉ b → q ∉ b ++ tail := by
            intro b hbb hcc
            rcases List.mem_append.mp hcc with h | h
            · exact hbb h
            · exact hqt h
          have happ : ∀ b : List Q, (b ++ tail) ++ [q] = b ++ (tail ++ [q]) := fun b =>
            List.append_assoc b tail [q]
          have hidx : ∀ b : List Q, q ∉ b →
              (b ++ (tail ++ [q])).idxOf q = b.length + tail.length := by
            intro b hbb
            rw [List.idxOf_append_of_notMem hbb, List.idxOf_append_of_notMem hqt]
            simp
          rw [lazyRun_query, lazyRun_query]
          simp only [if_neg (hnmem base₀ hb), if_neg (hnmem base₁ hb₁), happ base₀, happ base₁,
            hidx base₀ hb, hidx base₁ hb₁, ← hlen, List.map_cons, List.take_succ_cons]
          refine congrArg _ ?_
          refine lazyRun_take_congr_of_base_compat tape dflt base₀ base₁ hlen
            (next (tapeAt tape dflt (base₀.length + tail.length))) (tail ++ [q]) N ?_
          intro r hr
          refine hsub r ?_
          simp only [if_neg (hnmem base₀ hb), happ base₀, hidx base₀ hb]
          exact hr

/-- The special case the hiding argument used first: the continuation avoids both bases entirely. -/
theorem lazyRun_congr_of_base (tape : Fin T → D) (dflt : D) (base₀ base₁ : List Q)
    (hlen : base₀.length = base₁.length) {f : ℕ} (c : Tree Q D A f) (tail : List Q)
    (havoid : ∀ qa ∈ (lazyRun tape dflt c (base₀ ++ tail)).2.2,
      qa.1 ∉ base₀ ∧ qa.1 ∉ base₁) :
    (lazyRun tape dflt c (base₀ ++ tail)).1 = (lazyRun tape dflt c (base₁ ++ tail)).1 ∧
      (lazyRun tape dflt c (base₀ ++ tail)).2.2 =
        (lazyRun tape dflt c (base₁ ++ tail)).2.2 :=
  lazyRun_congr_of_base_compat tape dflt base₀ base₁ hlen c tail
    fun qa hqa => baseCompat_of_not_mem hlen (havoid qa hqa).1 (havoid qa hqa).2

/-! ### One query catches at most one candidate

A guessing count needs its guess list fixed independently of the secret.  Sometimes it cannot be: the
run's own base *contains* the secret's distinguishing input, so whether a query is a repeat — and hence
what the run does next — depends on the secret.  Reading the list off a *reference* secret does not
help, because the two runs part ways as soon as either one's own input is queried.

The way out is that the dependence is self-limiting.  Index the runs by the candidate `s`, with `w s`
the input that only `s`'s base contains.  Two candidates' runs agree until one of their two inputs is
queried, and `w` injective means a single query can be `w s` for at most one `s`.  So each query
eliminates at most one candidate: an `f`-query execution catches at most `f` of them, however large the
candidate space.  No reference, and no fixed guess list. -/

/-- `idxOf` really is the *first* occurrence. -/
theorem idxOf_le_of_getElem {l : List Q} {a : Q} {j : ℕ} (hj : j < l.length) (h : l[j] = a) :
    l.idxOf a ≤ j := by
  have hjt : j < (l.take (j + 1)).length := by rw [List.length_take]; omega
  have hmem : a ∈ l.take (j + 1) := by
    have hg := List.getElem_mem hjt
    rwa [show (l.take (j + 1))[j] = l[j] from by simp, h] at hg
  have heq : l.idxOf a = (l.take (j + 1)).idxOf a := by
    conv_lhs => rw [← List.take_append_drop (j + 1) l]
    rw [List.idxOf_append_of_mem hmem]
  rw [heq]
  have hlt := List.idxOf_lt_length_of_mem hmem
  rw [List.length_take] at hlt
  omega

/-- **An `f`-query execution catches at most `2f` candidates.**  The candidate space may be enormous
and the run's query list may genuinely depend on the secret; neither matters.  Each candidate carries
*two* distinguishing inputs `w s` and `u s` — in the hiding application, its leaf encoding under each of
the two messages — and since each of `w`, `u` is injective, one query can be a marker for at most two
candidates.  So each query rules out at most two, and the bound is `2f`.

`G` is the set of candidates the hypotheses are asked about, so candidates whose own base misbehaves —
a colliding commitment, say — can be excluded and charged elsewhere rather than costing a factor of the
candidate space. -/
theorem caught_card_le {S : Type uS} [Fintype S] [DecidableEq S] (tape : Fin T → D) (dflt : D)
    {f : ℕ} (c : Tree Q D A f) (base : S → List Q) (w u : S → Q)
    (hw : Function.Injective w) (hu : Function.Injective u)
    (G : Finset S)
    (hlen : ∀ s ∈ G, ∀ t ∈ G, (base s).length = (base t).length)
    (hcompat : ∀ s ∈ G, ∀ t ∈ G, ∀ q : Q, q ≠ w s → q ≠ u s → q ≠ w t → q ≠ u t →
      BaseCompat (base s) (base t) q)
    (hG : ∀ s ∈ G, w s ∈ (lazyRun tape dflt c (base s)).2.2.map Prod.fst ∨
      u s ∈ (lazyRun tape dflt c (base s)).2.2.map Prod.fst) :
    G.card ≤ 2 * f := by
  classical
  set L : S → List Q := fun s => (lazyRun tape dflt c (base s)).2.2.map Prod.fst with hL
  set k : S → ℕ := fun s => min ((L s).idxOf (w s)) ((L s).idxOf (u s)) with hk
  have hkmin : ∀ s, k s ≤ (L s).idxOf (w s) ∧ k s ≤ (L s).idxOf (u s) := by
    intro s
    rw [hk]
    exact ⟨min_le_left _ _, min_le_right _ _⟩
  have hLlen : ∀ s, (L s).length ≤ f := by
    intro s
    rw [hL]
    simp only [List.length_map]
    exact lazyRun_trace_length_le tape dflt c (base s)
  have hklt : ∀ s ∈ G, k s < (L s).length := by
    intro s hs
    rcases hG s hs with h | h
    · exact lt_of_le_of_lt (hkmin s).1 (List.idxOf_lt_length_of_mem h)
    · exact lt_of_le_of_lt (hkmin s).2 (List.idxOf_lt_length_of_mem h)
  -- the query at a candidate's first own-marker index *is* one of its markers
  have hmark : ∀ s ∈ G, (L s)[k s]? = some (w s) ∨ (L s)[k s]? = some (u s) := by
    intro s hs
    have hks := hklt s hs
    rcases Nat.le_total ((L s).idxOf (w s)) ((L s).idxOf (u s)) with hle | hle
    · left
      have hkeq : k s = (L s).idxOf (w s) := by simp only [hk]; omega
      have hlt : (L s).idxOf (w s) < (L s).length := by rw [← hkeq]; exact hks
      rw [hkeq, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
    · right
      have hkeq : k s = (L s).idxOf (u s) := by simp only [hk]; omega
      have hlt : (L s).idxOf (u s) < (L s).length := by rw [← hkeq]; exact hks
      rw [hkeq, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  -- two candidates caught at the same index saw the same query there
  have hcommon : ∀ s ∈ G, ∀ t ∈ G, k s = k t → (L s)[k s]? = (L t)[k s]? := by
    intro s hs t ht hkst
    set K := min (k s) (min ((L s).idxOf (w t)) ((L s).idxOf (u t))) with hKdef
    have hKks : K ≤ k s := by rw [hKdef]; exact min_le_left _ _
    have h1 : K ≤ (L s).idxOf (w s) := le_trans hKks (hkmin s).1
    have h2 : K ≤ (L s).idxOf (u s) := le_trans hKks (hkmin s).2
    have h3 : K ≤ (L s).idxOf (w t) := by
      rw [hKdef]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h4 : K ≤ (L s).idxOf (u t) := by
      rw [hKdef]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hKlt : K < (L s).length := lt_of_le_of_lt hKks (hklt s hs)
    have havoid : ∀ q ∈ (L s).take K, BaseCompat (base s) (base t) q := by
      intro q hq
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hq
      rw [List.length_take] at hj
      have hjL : j < (L s).length := by omega
      have hgetj : (L s)[j] = q := by rw [← hget]; simp
      refine hcompat s hs t ht q ?_ ?_ ?_ ?_ <;> intro hcc <;>
        exact absurd (idxOf_le_of_getElem hjL (hgetj.trans hcc)) (by omega)
    have hagree : (L s).take (K + 1) = (L t).take (K + 1) := by
      have h := lazyRun_take_congr_of_base_compat tape dflt (base s) (base t) (hlen s hs t ht)
        c [] K (by simpa [hL] using havoid)
      simpa [hL] using h
    have hKt : K < (L t).length := by
      have hh := congrArg List.length hagree
      rw [List.length_take, List.length_take] at hh
      omega
    have hsame : (L s)[K]? = (L t)[K]? := by
      have hh : ((L s).take (K + 1))[K]? = ((L t).take (K + 1))[K]? := by rw [hagree]
      rwa [List.getElem?_take, List.getElem?_take, if_pos (Nat.lt_succ_self K),
        if_pos (Nat.lt_succ_self K)] at hh
    -- `K` is `s`'s own index: otherwise `t` was caught strictly earlier
    have hKeq : K = k s := by
      by_contra hne
      have hKlt' : K < k s := by omega
      have hKt' : K = min ((L s).idxOf (w t)) ((L s).idxOf (u t)) := by rw [hKdef]; omega
      have hgets : (L s)[K]? = some (w t) ∨ (L s)[K]? = some (u t) := by
        rcases Nat.le_total ((L s).idxOf (w t)) ((L s).idxOf (u t)) with hle | hle
        · left
          have hq : K = (L s).idxOf (w t) := by omega
          rw [hq, List.getElem?_eq_getElem (by rw [← hq]; exact hKlt),
            List.getElem_idxOf (by rw [← hq]; exact hKlt)]
        · right
          have hq : K = (L s).idxOf (u t) := by omega
          rw [hq, List.getElem?_eq_getElem (by rw [← hq]; exact hKlt),
            List.getElem_idxOf (by rw [← hq]; exact hKlt)]
      rw [hsame] at hgets
      rw [List.getElem?_eq_getElem hKt] at hgets
      have hle : k t ≤ K := by
        rcases hgets with hgt | hgt
        · exact le_trans (hkmin t).1 (idxOf_le_of_getElem hKt (Option.some_inj.mp hgt))
        · exact le_trans (hkmin t).2 (idxOf_le_of_getElem hKt (Option.some_inj.mp hgt))
      omega
    rw [← hKeq]
    exact hsame
  -- each index value is shared by at most two candidates
  have hfib : ∀ a ∈ G.image k, (G.filter fun s => k s = a).card ≤ 2 := by
    intro a ha
    obtain ⟨s₀, hs₀G, hs₀⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq⟩ : ∃ q, (L s₀)[a]? = some q := by
      rw [← hs₀, List.getElem?_eq_getElem (hklt s₀ hs₀G)]
      exact ⟨_, rfl⟩
    have hval : ∀ s ∈ G.filter fun s => k s = a, q = w s ∨ q = u s := by
      intro s hsm
      obtain ⟨hsG, hsa⟩ := Finset.mem_filter.mp hsm
      have h1 : (L s)[a]? = (L s₀)[a]? := by
        have hcc := hcommon s hsG s₀ hs₀G (by rw [hsa, hs₀])
        rwa [hsa] at hcc
      rcases hmark s hsG with h2 | h2
      · left
        rw [hsa] at h2
        exact Option.some_inj.mp (hq.symm.trans (h1.symm.trans h2))
      · right
        rw [hsa] at h2
        exact Option.some_inj.mp (hq.symm.trans (h1.symm.trans h2))
    refine le_trans (Finset.card_le_card_of_injOn (fun s => decide (q = w s))
      (fun _ _ => Finset.mem_univ _) ?_) (le_of_eq (by simp))
    intro x hx y hy hxy
    have hiff : (q = w x) ↔ (q = w y) := decide_eq_decide.mp hxy
    by_cases hcx : q = w x
    · exact hw (hcx.symm.trans (hiff.mp hcx))
    · have hcy : ¬ (q = w y) := fun hc => hcx (hiff.mpr hc)
      rcases hval x hx with h | h
      · exact absurd h hcx
      · rcases hval y hy with h' | h'
        · exact absurd h' hcy
        · exact hu (h.symm.trans h')
  refine le_trans (Finset.card_le_mul_card_image G 2 hfib) ?_
  refine Nat.mul_le_mul_left 2 ?_
  refine le_trans (Finset.card_le_card (fun a ha => ?_)) (le_of_eq (Finset.card_range f))
  obtain ⟨s, hsG, hsa⟩ := Finset.mem_image.mp ha
  exact Finset.mem_range.mpr (hsa ▸ lt_of_lt_of_le (hklt s hsG) (hLlen s))

/-! ### Dropping a base the run never queries

`lazyRun_congr_of_base` compares two *different* bases of the same length.  Here is the absolute form:
a run that never queries its base behaves exactly like a run from the **empty** base against the tape
shifted past it, because every answer it reads sits at offset `base.length + something`.  So its query
list is a function of the high slots alone — nothing the base's own phase computed can influence it.

That independence has to be available up to the *first* query that does land in the base, which is why
this is stated on prefixes: assuming the first `N` queries avoid the base, the first `N+1` agree. The
`N+1` is not an off-by-one — the `(N+1)`-st query is determined by the first `N` answers, so it is
still common to both runs even though it may be the one that hits. -/

theorem lazyRun_shift_take_congr (tape : Fin T → D) (dflt : D) (base : List Q) :
    ∀ {f : ℕ} (c : Tree Q D A f) (tail : List Q) (N : ℕ),
      (∀ q ∈ ((lazyRun tape dflt c (base ++ tail)).2.2.map Prod.fst).take N, q ∉ base) →
      ((lazyRun tape dflt c (base ++ tail)).2.2.map Prod.fst).take (N + 1) =
        ((lazyRun (shiftTape base.length tape dflt) dflt c tail).2.2.map Prod.fst).take (N + 1)
  | _, .done _, _, _, _ => by simp
  | _, .query q next, tail, 0, _ => by
      rw [lazyRun_query, lazyRun_query]
      simp
  | _, .query q next, tail, (N + 1), havoid => by
      rw [lazyRun_query] at havoid
      simp only [List.map_cons, List.take_succ_cons, List.mem_cons] at havoid
      have hq : q ∉ base := havoid q (Or.inl rfl)
      have hsub : ∀ r ∈ ((lazyRun tape dflt (next (tapeAt tape dflt
          ((if q ∈ base ++ tail then base ++ tail
            else (base ++ tail) ++ [q]).idxOf q))) (if q ∈ base ++ tail then base ++ tail
              else (base ++ tail) ++ [q])).2.2.map Prod.fst).take N, r ∉ base :=
        fun r hr => havoid r (Or.inr hr)
      by_cases hqt : q ∈ tail
      · -- a repeat of an earlier fresh query: both sides read the same offset into `tail`
        have hmem : q ∈ base ++ tail := List.mem_append.mpr (Or.inr hqt)
        have hidx : (base ++ tail).idxOf q = base.length + tail.idxOf q :=
          List.idxOf_append_of_notMem hq
        rw [lazyRun_query, lazyRun_query]
        simp only [if_pos hmem, if_pos hqt, hidx, tapeAt_shiftTape, List.map_cons,
          List.take_succ_cons]
        refine congrArg _ ?_
        refine lazyRun_shift_take_congr tape dflt base
          (next (tapeAt tape dflt (base.length + tail.idxOf q))) tail N ?_
        intro r hr
        refine hsub r ?_
        simp only [if_pos hmem, hidx]
        exact hr
      · -- fresh: both sides append it, at the same offset past the end
        have hnmem : q ∉ base ++ tail := by
          intro hc
          rcases List.mem_append.mp hc with h | h
          · exact hq h
          · exact hqt h
        have hidx' : (tail ++ [q]).idxOf q = tail.length := by
          rw [List.idxOf_append_of_notMem hqt]
          simp
        -- stated after `append_assoc`, which `simp only` normalizes with first
        have hidx : (base ++ (tail ++ [q])).idxOf q = base.length + tail.length := by
          rw [List.idxOf_append_of_notMem hq, hidx']
        have happ : (base ++ tail) ++ [q] = base ++ (tail ++ [q]) := List.append_assoc base tail [q]
        rw [lazyRun_query, lazyRun_query]
        simp only [if_neg hnmem, if_neg hqt, hidx, hidx', tapeAt_shiftTape, List.map_cons,
          List.take_succ_cons, happ]
        refine congrArg _ ?_
        refine lazyRun_shift_take_congr tape dflt base
          (next (tapeAt tape dflt (base.length + tail.length))) (tail ++ [q]) N ?_
        intro r hr
        refine hsub r ?_
        simp only [if_neg hnmem, hidx, happ]
        exact hr

end Lazy

end RandomOracle

end Merkle
