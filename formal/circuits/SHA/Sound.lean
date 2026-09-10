import SHA.Spec

/-!
# SHA-256 soundness, abstractly

The analogue of `ECDSA/EcdsaSound.lean` for the one-block SHA-256 circuit, and the theorem the
circuit bridges are meant to aim at. Nothing here mentions wires, assertions, `interpDag` or a
field: every hypothesis is a statement about `Nat`s, and the conclusion is `SHA256.block` from
`SHA/Spec.lean`.

## The shape, and why it is this shape

`SHA/Spec.lean` defines the schedule and the compression function as *folds* — `schedule 48` and
`rounds 64` — because that is how FIPS 180-4 reads. A circuit cannot produce a fold. What it
produces is one witnessed word per computed quantity plus one assertion per step, which is an
*indexed recurrence*. So the content of this file is that the two agree:

* `sched_eq` — any `w : Nat → Nat` satisfying the 16 copy equations and the 48 recurrence
  equations agrees with `(W m).getD · 0` below 64;
* `rounds_run` — any `s : Nat → Nat → Nat` satisfying the 64 round steps reaches
  `rounds 64 (W m) H0` at `t = 64`;
* `sha256_soundness` — the two together, plus the eight final sums, give `block m`.

The hypotheses are deliberately one-per-assertion-family, matching what the artifact actually
asserts (`SHA/Spec.lean`'s table): `hsched` is the 48 `sha256/schedule/N` assertions, `hrnd_a`
and `hrnd_e` are the 128 `sha256/rounds/N/round_step` ones split by which working variable they
constrain, and `hout` is the 8 `sha256/final/N` ones. The 6,656 `is_boolean` assertions do not
appear: they are what a bridge needs in order to *establish* these hypotheses (they make each
`w32` a no-op on a witnessed word), not clauses of the specification. That asymmetry is the same
one `ECDSA2.soundness_of_v2` has with its digit range checks.

## What is assumed rather than proved

The addend *order* inside each wrapping sum, and which wire is which working variable, are facts
about the circuit's layout. They enter here as the shape of `hrnd_a` / `hrnd_e` / `hsched`, and a
bridge discharges them by exhibiting the cone. As in `Gen/E2/E2Ecdsa.lean`, the input layout is
the one place meaning is chosen rather than checked.
-/

namespace SHA256

/-! ### `w32` absorption

The circuit asserts one wrapping sum per computed word — a single `% 2 ^ 32` over all the
addends. The specification nests them (`t1` is reduced, then `d + t1` is reduced again). These
three lemmas are the whole difference. -/

theorem w32_idem (x : Nat) : w32 (w32 x) = w32 x := by
  simp [w32]

theorem w32_add_left (x y : Nat) : w32 (w32 x + y) = w32 (x + y) := by
  simp [w32, Nat.add_mod]

theorem w32_add_right (x y : Nat) : w32 (x + w32 y) = w32 (x + y) := by
  simp [w32, Nat.add_mod]

/-! ### List helpers

`getD` on an append, in the two positions the schedule needs. Stated locally so this file does
not depend on which spelling of `List.getD_append` the current Mathlib has. -/

private theorem getD_append_lt {α : Type} (l₁ l₂ : List α) (d : α) {i : Nat}
    (h : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_len {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD_eq_getElem?_getD]

/-! ### The message schedule

`schedule` iterates `scheduleStep`, which appends one word. Everything below is the standard
consequence: it extends, it preserves what is already there, and the word it appends is the
recurrence. -/

/-- `schedule` peels from the *right* as well as the left. This is the lemma that makes induction
    on the schedule possible: the definition recurses by stepping the argument, but every proof
    wants to step the result. -/
theorem schedule_succ_right (n : Nat) (w : List Nat) :
    schedule (n + 1) w = scheduleStep (schedule n w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => rw [schedule, ih (scheduleStep w)]; rfl

theorem schedule_add (a b : Nat) (w : List Nat) :
    schedule (a + b) w = schedule a (schedule b w) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
      rw [Nat.succ_add, schedule_succ_right, ih, schedule_succ_right]

theorem scheduleStep_length (w : List Nat) : (scheduleStep w).length = w.length + 1 := by
  simp [scheduleStep]

theorem schedule_length (n : Nat) (w : List Nat) : (schedule n w).length = w.length + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [schedule_succ_right, scheduleStep_length, ih]; omega

/-- Stepping never disturbs an entry that is already there. -/
theorem schedule_prefix (n : Nat) (w : List Nat) {i : Nat} (hi : i < w.length) :
    (schedule n w).getD i 0 = w.getD i 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [schedule_succ_right, scheduleStep]
      rw [getD_append_lt _ _ _ (by rw [schedule_length]; omega)]
      exact ih

/-- The word `scheduleStep` appends, in terms of the list it appends to. -/
theorem schedule_step_val (n : Nat) (m : List Nat) (hm : m.length = 16) :
    (schedule (n + 1) m).getD (16 + n) 0
      = w32 (sigma1 ((schedule n m).getD (16 + n - 2) 0)
             + (schedule n m).getD (16 + n - 7) 0
             + sigma0 ((schedule n m).getD (16 + n - 15) 0)
             + (schedule n m).getD (16 + n - 16) 0) := by
  have hlen : (schedule n m).length = 16 + n := by rw [schedule_length, hm]
  rw [schedule_succ_right, scheduleStep, ← hlen, getD_append_len, hlen]

/-! ### The schedule, indexed

`W m` is `schedule 48 m`, so an entry at `t = 16 + n` was written by step `n` and is stable from
then on. These two lemmas are the recurrence a circuit assertion can be compared against. -/

/-- `W` is the 48-step schedule; `rfl` at default transparency, but `rw` will not unfold it. -/
theorem W_eq (m : List Nat) : W m = schedule 48 m := rfl

theorem W_getD_lo (m : List Nat) (hm : m.length = 16) {t : Nat} (ht : t < 16) :
    (W m).getD t 0 = m.getD t 0 :=
  schedule_prefix 48 m (by omega)

theorem W_getD_hi (m : List Nat) (hm : m.length = 16) {t : Nat} (h16 : 16 ≤ t) (h64 : t < 64) :
    (W m).getD t 0
      = w32 (sigma1 ((W m).getD (t - 2) 0) + (W m).getD (t - 7) 0
             + sigma0 ((W m).getD (t - 15) 0) + (W m).getD (t - 16) 0) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = 16 + n := ⟨t - 16, by omega⟩
  have hn : n < 48 := by omega
  -- `W m` and `schedule (n+1) m` agree up to and including position `16 + n`.
  have harith : 48 - (n + 1) + (n + 1) = 48 := by omega
  have hsplit : W m = schedule (48 - (n + 1)) (schedule (n + 1) m) := by
    rw [← schedule_add, harith, W_eq]
  have hstable : ∀ i, i ≤ 16 + n → (W m).getD i 0 = (schedule (n + 1) m).getD i 0 := by
    intro i hi
    rw [hsplit]
    exact schedule_prefix _ _ (by rw [schedule_length, hm]; omega)
  -- and with `schedule n m` strictly below it.
  have hstable' : ∀ i, i < 16 + n → (W m).getD i 0 = (schedule n m).getD i 0 := by
    intro i hi
    have harith' : 48 - n + n = 48 := by omega
    have hsp : W m = schedule (48 - n) (schedule n m) := by
      rw [← schedule_add, harith', W_eq]
    rw [hsp]
    exact schedule_prefix _ _ (by rw [schedule_length, hm]; omega)
  rw [hstable (16 + n) (by omega), schedule_step_val n m hm,
      hstable' (16 + n - 2) (by omega), hstable' (16 + n - 7) (by omega),
      hstable' (16 + n - 15) (by omega), hstable' (16 + n - 16) (by omega)]

/-- **Schedule uniqueness.** The 16 copies and the 48 recurrences determine every word below 64.
    This is the half of the argument the `sha256/schedule/N/assert_wrapping_sum_prime` family
    supplies. -/
theorem sched_eq (m : List Nat) (hm : m.length = 16) (w : Nat → Nat)
    (hlo : ∀ t, t < 16 → w t = m.getD t 0)
    (hhi : ∀ t, 16 ≤ t → t < 64 →
      w t = w32 (sigma1 (w (t - 2)) + w (t - 7) + sigma0 (w (t - 15)) + w (t - 16))) :
    ∀ t, t < 64 → w t = (W m).getD t 0 := by
  -- induction on an explicit bound, so this file needs no strong-recursion import
  have key : ∀ N t, t < N → t < 64 → w t = (W m).getD t 0 := by
    intro N
    induction N with
    | zero => intro t ht; omega
    | succ N ih =>
        intro t htN ht
        by_cases h16 : t < 16
        · rw [hlo t h16, W_getD_lo m hm h16]
        · have h16' : 16 ≤ t := by omega
          rw [hhi t h16' ht, W_getD_hi m hm h16' ht,
              ih (t - 2) (by omega) (by omega), ih (t - 7) (by omega) (by omega),
              ih (t - 15) (by omega) (by omega), ih (t - 16) (by omega) (by omega)]
  exact fun t ht => key 64 t ht ht

/-! ### The compression rounds

The circuit witnesses the eight working variables at every round as `s t i`. `stateAt` is the
list the specification wants; the six copy equations and the two wrapping sums are exactly one
`round`. -/

/-- The eight working variables at round `t`, as the specification's list. -/
def stateAt (s : Nat → Nat → Nat) (t : Nat) : List Nat :=
  [s t 0, s t 1, s t 2, s t 3, s t 4, s t 5, s t 6, s t 7]

/-- Reading a working variable back out. Eight `rfl`s rather than `interval_cases`, so this file
    stays independent of Mathlib's tactic set. -/
theorem stateAt_getD (s : Nat → Nat → Nat) (t : Nat) :
    ∀ {i : Nat}, i < 8 → (stateAt s t).getD i 0 = s t i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | (_ + 8), h => absurd h (by omega)

/-- Discharge `i < 8` by cases, without `interval_cases`. -/
private theorem interval_cases_8 {P : Nat → Prop} {i : Nat} (hi : i < 8)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : P i := by
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7

/-- `List.range 8` as a literal, so the final map is eight component equations. -/
private theorem map_range8 (f : Nat → Nat) :
    (List.range 8).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := rfl

/-- One round, from the two wrapping sums and the six copies.

    `hrnd_a` is the `n = 7` assertion (`h + Σ₁e + Ch efg + Kt + Wt + Σ₀a + Maj abc`) and `hrnd_e`
    the `n = 6` one (`d + h + Σ₁e + Ch efg + Kt + Wt`); the specification reduces `t1` before
    reusing it, and `w32_add_left` / `w32_add_right` are what make that immaterial. -/
theorem round_of_steps (s : Nat → Nat → Nat) (w : Nat → Nat) (t : Nat)
    (ha : s (t + 1) 0 = w32 (s t 7 + Sigma1 (s t 4) + Ch (s t 4) (s t 5) (s t 6)
            + K.getD t 0 + w t + (Sigma0 (s t 0) + Maj (s t 0) (s t 1) (s t 2))))
    (he : s (t + 1) 4 = w32 (s t 3 + (s t 7 + Sigma1 (s t 4) + Ch (s t 4) (s t 5) (s t 6)
            + K.getD t 0 + w t)))
    (h1 : s (t + 1) 1 = s t 0) (h2 : s (t + 1) 2 = s t 1) (h3 : s (t + 1) 3 = s t 2)
    (h5 : s (t + 1) 5 = s t 4) (h6 : s (t + 1) 6 = s t 5) (h7 : s (t + 1) 7 = s t 6) :
    stateAt s (t + 1) = round t (w t) (stateAt s t) := by
  simp only [stateAt, round, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
    and_true]
  refine ⟨?_, h1, h2, h3, ?_, h5, h6, h7⟩
  · rw [ha, w32_add_left, w32_add_right]
  · rw [he, w32_add_right]

/-- **Round chaining.** 64 single-step equations compose into the specification's fold.

    Stated with the loop counter `j` and the round index `k` linked by `k + j = 64`, because
    `rounds` counts down while the circuit's assertions are indexed up. -/
theorem rounds_run (wl : List Nat) (s : Nat → Nat → Nat)
    (hstep : ∀ t, t < 64 → stateAt s (t + 1) = round t (wl.getD t 0) (stateAt s t)) :
    ∀ j k, k + j = 64 → rounds j wl (stateAt s k) = stateAt s 64 := by
  intro j
  induction j with
  | zero =>
      intro k hk
      have hk64 : k = 64 := by omega
      subst hk64
      rfl
  | succ j ih =>
      intro k hk
      have hk' : 64 - (j + 1) = k := by omega
      rw [rounds, hk', ← hstep k (by omega)]
      exact ih (k + 1) (by omega)

/-! ### The theorem -/

/-- Reading back a chaining word. -/
private theorem getD_map_range8 (h : Nat → Nat) {i : Nat} (hi : i < 8) :
    ((List.range 8).map h).getD i 0 = h i := by
  rw [map_range8]
  exact interval_cases_8 (P := fun j => ([h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7] : List Nat).getD j 0 = h j)
    hi rfl rfl rfl rfl rfl rfl rfl rfl

/-- **Abstract SHA-256 soundness.**

    A witness assigning
    * `h i` to the `i`-th incoming chaining word,
    * `w t` to the `t`-th schedule word,
    * `s t i` to working variable `i` after `t` rounds, and
    * `out i` to the `i`-th outgoing chaining word,

    and satisfying the copy, schedule, round and final equations, computes the SHA-256 block
    transform of `m` from `h`.

    `h` is a *parameter*, not `H0`: the deployed circuit takes its incoming hash on input wires
    (`h0_i_j` in the artifact layout) so that blocks chain, and asserts the final sum against
    those wires. `sha256_block_soundness` below specialises to `H0` for the one-block case.

    Every hypothesis is one assertion family of the deployed circuit. Nothing is assumed about
    how the words are represented: a bridge instantiates `h`, `w`, `s` and `out` with `ofBits` of
    the witnessed bit vectors, and discharges each `w32` from the booleanity assertions. -/
theorem sha256_soundness
    (m : List Nat) (hm : m.length = 16)
    (h : Nat → Nat) (w : Nat → Nat) (s : Nat → Nat → Nat) (out : Nat → Nat)
    -- the 16 message words are copied into the schedule
    (hcopy : ∀ t, t < 16 → w t = m.getD t 0)
    -- the 48 `sha256/schedule/N` assertions
    (hsched : ∀ t, 16 ≤ t → t < 64 →
      w t = w32 (sigma1 (w (t - 2)) + w (t - 7) + sigma0 (w (t - 15)) + w (t - 16)))
    -- the compression starts at the incoming chaining value
    (hinit : ∀ i, i < 8 → s 0 i = h i)
    -- the 64 `round_step` assertions constraining `a`  (`n = 7`)
    (hrnd_a : ∀ t, t < 64 → s (t + 1) 0 = w32 (s t 7 + Sigma1 (s t 4)
      + Ch (s t 4) (s t 5) (s t 6) + K.getD t 0 + w t
      + (Sigma0 (s t 0) + Maj (s t 0) (s t 1) (s t 2))))
    -- the 64 `round_step` assertions constraining `e`  (`n = 6`)
    (hrnd_e : ∀ t, t < 64 → s (t + 1) 4 = w32 (s t 3 + (s t 7 + Sigma1 (s t 4)
      + Ch (s t 4) (s t 5) (s t 6) + K.getD t 0 + w t)))
    -- the six working variables that are copied, not computed
    (hshift : ∀ t, t < 64 →
      s (t + 1) 1 = s t 0 ∧ s (t + 1) 2 = s t 1 ∧ s (t + 1) 3 = s t 2 ∧
      s (t + 1) 5 = s t 4 ∧ s (t + 1) 6 = s t 5 ∧ s (t + 1) 7 = s t 6)
    -- the 8 `sha256/final/N` assertions
    (hout : ∀ i, i < 8 → out i = w32 (h i + s 64 i)) :
    (List.range 8).map out = blockFrom ((List.range 8).map h) m := by
  -- the witnessed schedule is the specification's schedule
  have hw : ∀ t, t < 64 → w t = (W m).getD t 0 := sched_eq m hm w hcopy hsched
  -- the witnessed states run the specification's fold
  have hstep : ∀ t, t < 64 → stateAt s (t + 1) = round t ((W m).getD t 0) (stateAt s t) := by
    intro t ht
    obtain ⟨h1, h2, h3, h5, h6, h7⟩ := hshift t ht
    rw [← hw t ht]
    exact round_of_steps s w t (hrnd_a t ht) (hrnd_e t ht) h1 h2 h3 h5 h6 h7
  have hrun : rounds 64 (W m) (stateAt s 0) = stateAt s 64 :=
    rounds_run (W m) s hstep 64 0 rfl
  have hstart : stateAt s 0 = (List.range 8).map h := by
    simp only [stateAt, map_range8, hinit 0 (by omega), hinit 1 (by omega), hinit 2 (by omega),
      hinit 3 (by omega), hinit 4 (by omega), hinit 5 (by omega), hinit 6 (by omega),
      hinit 7 (by omega)]
  rw [hstart] at hrun
  -- and the eight final sums are the specification's output map
  -- `hrun` must fire before `map_range8` expands its argument
  simp only [blockFrom]
  rw [hrun]
  simp only [map_range8]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    · rw [hout _ (by omega), stateAt_getD s 64 (by omega)]; rfl

/-- The one-block case: the incoming chaining value is the standard initial hash. -/
theorem sha256_block_soundness
    (m : List Nat) (hm : m.length = 16)
    (w : Nat → Nat) (s : Nat → Nat → Nat) (out : Nat → Nat)
    (hcopy : ∀ t, t < 16 → w t = m.getD t 0)
    (hsched : ∀ t, 16 ≤ t → t < 64 →
      w t = w32 (sigma1 (w (t - 2)) + w (t - 7) + sigma0 (w (t - 15)) + w (t - 16)))
    (hinit : ∀ i, i < 8 → s 0 i = H0.getD i 0)
    (hrnd_a : ∀ t, t < 64 → s (t + 1) 0 = w32 (s t 7 + Sigma1 (s t 4)
      + Ch (s t 4) (s t 5) (s t 6) + K.getD t 0 + w t
      + (Sigma0 (s t 0) + Maj (s t 0) (s t 1) (s t 2))))
    (hrnd_e : ∀ t, t < 64 → s (t + 1) 4 = w32 (s t 3 + (s t 7 + Sigma1 (s t 4)
      + Ch (s t 4) (s t 5) (s t 6) + K.getD t 0 + w t)))
    (hshift : ∀ t, t < 64 →
      s (t + 1) 1 = s t 0 ∧ s (t + 1) 2 = s t 1 ∧ s (t + 1) 3 = s t 2 ∧
      s (t + 1) 5 = s t 4 ∧ s (t + 1) 6 = s t 5 ∧ s (t + 1) 7 = s t 6)
    (hout : ∀ i, i < 8 → out i = w32 (H0.getD i 0 + s 64 i)) :
    (List.range 8).map out = block m := by
  have := sha256_soundness m hm (fun i => H0.getD i 0) w s out hcopy hsched hinit hrnd_a hrnd_e
    hshift hout
  rwa [show (List.range 8).map (fun i => H0.getD i 0) = H0 from rfl] at this

/-! ### The theorem, applied

`block_empty` in `SHA/Spec.lean` checks the specification against a published test vector. This
section checks `sha256_soundness` against the specification: it builds the witness the spec
itself produces for the padded empty message, discharges all six hypothesis families, and reads
the digest off the *conclusion*. If a hypothesis were mis-stated — an addend in the wrong sum, an
off-by-one in the round index, `sigma0` where `Sigma0` belongs — this section stops compiling
even though the theorem above would still be true and still be provable.

It is also the smallest worked example of what a circuit bridge has to supply. -/

namespace Demo

/-- The schedule of the padded empty message. -/
def w (t : Nat) : Nat := (W emptyBlock).getD t 0

/-- The working variables after `t` rounds, from the specification's own `round`. -/
def stateList : Nat → List Nat
  | 0 => H0
  | t + 1 => round t (w t) (stateList t)

def s (t i : Nat) : Nat := (stateList t).getD i 0
def out (i : Nat) : Nat := w32 (H0.getD i 0 + s 64 i)

theorem rnd_a (t : Nat) : s (t + 1) 0 = w32 (s t 7 + Sigma1 (s t 4)
    + Ch (s t 4) (s t 5) (s t 6) + K.getD t 0 + w t
    + (Sigma0 (s t 0) + Maj (s t 0) (s t 1) (s t 2))) := by
  simp only [s, stateList, round, List.getD_cons_zero]
  rw [w32_add_left, w32_add_right]

theorem rnd_e (t : Nat) : s (t + 1) 4 = w32 (s t 3 + (s t 7 + Sigma1 (s t 4)
    + Ch (s t 4) (s t 5) (s t 6) + K.getD t 0 + w t)) := by
  simp only [s, stateList, round, List.getD_cons_zero, List.getD_cons_succ]
  rw [w32_add_right]

theorem shift (t : Nat) :
    s (t + 1) 1 = s t 0 ∧ s (t + 1) 2 = s t 1 ∧ s (t + 1) 3 = s t 2 ∧
    s (t + 1) 5 = s t 4 ∧ s (t + 1) 6 = s t 5 ∧ s (t + 1) 7 = s t 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The digest of the padded empty message, obtained by *applying* `sha256_soundness`. -/
theorem empty_digest :
    (List.range 8).map out
      = [0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924,
         0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855] := by
  have hm : emptyBlock.length = 16 := rfl
  have happly : (List.range 8).map out = block emptyBlock :=
    sha256_block_soundness emptyBlock hm w s out
      (fun t ht => W_getD_lo emptyBlock hm ht)
      (fun t h16 h64 => W_getD_hi emptyBlock hm h16 h64)
      (fun i _ => rfl)
      (fun t _ => rnd_a t)
      (fun t _ => rnd_e t)
      (fun t _ => shift t)
      (fun i _ => rfl)
  rw [happly, block_empty]

end Demo

end SHA256
