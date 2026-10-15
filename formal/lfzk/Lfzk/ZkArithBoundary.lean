import Lfzk.ZkArithInit

/-!
# The zero-knowledge chain's boundary facts, discharged for the constructed circuit

`Lfzk.ZkArithInit` gives the construction's `ZkHonest` and its `hinit`.  This file gives the rest of
the analysis data of `RbrZkSplit.ZkFieldData` for `Lfzk.Arith`'s construction under
`QuadCircuit.DeadEnd`: a concrete pending predicate and a whole `RbrZkLongfellow.ZkBoundary`.

* `cPend` — **the construction's pending predicate**: layer `ly + 1` is a gate layer and some
  completion of the bound prefix to a full `(L, R)` (`challenge_split`'s layout: `L` the first `logw`
  coordinates, `R` the next `logw`) has a non-zero assertion MLE of layer `ly + 1` at `L` or `R`;
* `cPend_sees` — it sees a non-zero assertion vector with nothing bound (`ZkArithInit.SeesAsserts`),
  so `zk_hinit` applies to it;
* `cPend_round` — **binding a coordinate keeps it pending but for one value**: the MLE is affine in
  each coordinate (`mle_mlin`), and the other hand's point is untouched;
* `cPend_close` — at the full bound it is the slope of the next layer's pair in its `beta`
  (`toLayered_V_decomp`);
* `zkBoundaryOf` — **the `ZkBoundary`**, at `nl := c.nl` and `w := fun _ => 2 * logw`, from
  `honest_final` (with `V_local`: the next layer reads `beta_{ly+1} = 0`), `honest_rel`,
  `toLayered_V_affine`, `toLayered_hin`, and the four `cPend` facts;
* `zkFieldDataOf` — **a whole `RbrZkSplit.ZkFieldData`** at `Sat := Satisfied`: `zkBoundaryOf`, and
  `ZkArithInit.zk_hinit` at `cPend`; only the decoders' balances are inputs.

**What the verifier's code is assumed to be** (`CodeAgrees`): `stNext`'s two points are
`challenge_split`'s, `eqqOf` is `bindGhAll` of the layer's gates at its `beta` (the shape
`toLayered_eqqAgree` proves for the deployed coefficients), the input row's coefficients are
`eq_mle_basis i L + alpha · eq_mle_basis i R` and its public binding is the same combination of the
public inputs, with `npub` the circuit's; and the candidates' committed columns are their witnesses
on the private indices (`AsgAgrees`).  These are statements about the code `V` and the encoding, not
about the prover.  The construction binds `L` then `R`; the deployed sumcheck interleaves the two
hands per round — the same count, but `cPend` follows the construction's layout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkArithInit

open Finset Lfzk.Arith Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.ZkMultilinear

variable {F : Type} [Field F] [DecidableEq F] [Fintype F]
variable {c : QuadCircuit F} {nv logw : ℕ}

/-! ## 1. Points from lists -/

/-- The coordinates a challenge list determines (`challenge_split` pads with zeros). -/
def ptOf (l : List F) : ℕ → F := fun i => l.getD i 0

/-- The left point of a coordinate function: the first `logw` coordinates. -/
def Lv (logw : ℕ) (y : ℕ → F) : Vector F logw := Vector.ofFn fun j : Fin logw => y j.val

/-- The right point of a coordinate function: the next `logw` coordinates. -/
def Rv (logw : ℕ) (y : ℕ → F) : Vector F logw := Vector.ofFn fun j : Fin logw => y (logw + j.val)

omit [DecidableEq F] [Fintype F] in
theorem cs_L (l : List F) :
    (challenge_split (logw := logw) (logc := 0) l).2.1 = Lv logw (ptOf l) := by
  unfold challenge_split extract_vars Lv ptOf
  ext j hj
  simp [Vector.get]

omit [DecidableEq F] [Fintype F] in
theorem cs_R (l : List F) :
    (challenge_split (logw := logw) (logc := 0) l).2.2 = Rv logw (ptOf l) := by
  unfold challenge_split extract_vars Rv ptOf
  ext j hj
  simp [Vector.get]

omit [DecidableEq F] [Fintype F] in
/-- Coordinates below a list's length do not see what is appended. -/
theorem ptOf_append_lt (l l' : List F) {i : ℕ} (hi : i < l.length) :
    ptOf (l ++ l') i = ptOf l i :=
  List.getD_append l l' 0 i hi

omit [DecidableEq F] [Fintype F] in
/-- **Binding the next coordinate** to `r`: the completion `ext` of `bnd` becomes the completion
`ext.tail` of `bnd ++ [r]`, at the point with coordinate `bnd.length` replaced by `r`. -/
theorem ptOf_bind (bnd ext : List F) (r : F) :
    ptOf ((bnd ++ [r]) ++ ext.tail) = Function.update (ptOf (bnd ++ ext)) bnd.length r := by
  funext i
  rcases Nat.lt_trichotomy i bnd.length with hlt | heq | hgt
  · rw [Function.update_of_ne (by omega), ptOf_append_lt (bnd ++ [r]) ext.tail (by simp; omega),
      ptOf_append_lt bnd [r] hlt, ptOf_append_lt bnd ext hlt]
  · subst heq
    rw [Function.update_self, ptOf_append_lt _ _ (by simp)]
    unfold ptOf
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
  · rw [Function.update_of_ne (by omega)]
    unfold ptOf
    rw [List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, i = bnd.length + 1 + m := ⟨i - bnd.length - 1, by omega⟩
    cases ext with
    | nil => simp
    | cons e t =>
        simp only [List.length_append, List.length_singleton, List.tail_cons]
        rw [show bnd.length + 1 + m - (bnd.length + 1) = m by omega,
          show bnd.length + 1 + m - bnd.length = m + 1 by omega, List.getD_cons_succ]

omit [Field F] [DecidableEq F] [Fintype F] in
/-- Updating a left coordinate moves the left point by the same update and fixes the right one. -/
theorem Lv_update_lt (y : ℕ → F) {k : ℕ} (hk : k < logw) (t : F) :
    Lv logw (Function.update y k t) = Vector.ofFn (Function.update (fun j : Fin logw => y j.val)
      ⟨k, hk⟩ t) ∧ Rv logw (Function.update y k t) = Rv logw y := by
  constructor
  · unfold Lv
    congr 1
    funext j
    by_cases hj : j.val = k
    · have : j = ⟨k, hk⟩ := Fin.ext hj
      subst this
      simp
    · rw [Function.update_of_ne hj, Function.update_of_ne (fun h => hj (by rw [h]))]
  · unfold Rv
    congr 1
    funext j
    rw [Function.update_of_ne (by omega)]

omit [Field F] [DecidableEq F] [Fintype F] in
/-- Updating a right coordinate moves the right point and fixes the left one. -/
theorem Rv_update_ge (y : ℕ → F) {k : ℕ} (hk1 : logw ≤ k) (hk2 : k < 2 * logw) (t : F) :
    Rv logw (Function.update y k t) = Vector.ofFn (Function.update
      (fun j : Fin logw => y (logw + j.val)) ⟨k - logw, by omega⟩ t) ∧
      Lv logw (Function.update y k t) = Lv logw y := by
  constructor
  · unfold Rv
    congr 1
    funext j
    by_cases hj : logw + j.val = k
    · have : j = ⟨k - logw, by omega⟩ := Fin.ext (by simp; omega)
      rw [hj, Function.update_self, this, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne (fun h => hj (by rw [h]; simp; omega))]
  · unfold Lv
    congr 1
    funext j
    rw [Function.update_of_ne (by omega)]

omit [DecidableEq F] [Fintype F] in
/-- **A multilinear function with two distinct zeros along a coordinate vanishes on that line.** -/
theorem mlin_line_zero {n : ℕ} (h : (Fin n → F) → F) (H : MLin h) (v : Fin n → F) (j : Fin n)
    {r1 r2 : F} (hne : r1 ≠ r2) (h1 : h (Function.update v j r1) = 0)
    (h2 : h (Function.update v j r2) = 0) (t : F) : h (Function.update v j t) = 0 := by
  obtain ⟨a, b, hab⟩ := H v j
  rw [hab] at h1 h2 ⊢
  have hb : (r1 - r2) * b = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.mp hb with h' | h'
  · exact absurd (sub_eq_zero.mp h') hne
  · rw [h'] at h1 ⊢
    linear_combination h1

/-! ## 2. The pending predicate -/

/-- Layer `ly`'s assertion MLE is non-zero at the left or the right point of `y`. -/
def AssertsAt (pub priv : Fin c.ninp → F) (logw ly : ℕ) (y : ℕ → F) : Prop :=
  mle logw (c.assertVec pub priv ly) (Lv logw y) ≠ 0 ∨ mle logw (c.assertVec pub priv ly) (Rv logw y) ≠ 0

/-- **The construction's pending predicate**: layer `ly + 1` is a gate layer and some completion of
the bound prefix has a non-zero assertion MLE of layer `ly + 1` at its left or right point. -/
def cPend (pub : Fin c.ninp → F) (logw : ℕ) {Lift : Type} (wOf : Lift → Fin c.ninp → F) :
    Lift → ℕ → List F → Prop :=
  fun ℓ ly bnd => ly + 1 < c.nl ∧ ∃ ext : List F, AssertsAt pub (wOf ℓ) logw (ly + 1) (ptOf (bnd ++ ext))

omit [Fintype F] in
/-- **`cPend` sees the assertion vectors** with nothing bound: a non-zero entry `i` is the MLE at the
cube point `i`, which a completion reaches. -/
theorem cPend_sees (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw) {Lift : Type}
    (wOf : Lift → Fin c.ninp → F) : SeesAsserts pub wOf (cPend pub logw wOf) := by
  intro ℓ j hj ⟨i, hi⟩
  refine ⟨hj, List.ofFn (fun k : Fin logw => if bit_value i k.val = 1 then (1 : F) else 0), Or.inl ?_⟩
  have hlt : i < 2 ^ logw := by
    by_contra hge
    exact hi (QuadCircuit.assertVec_supp hwf pub (wOf ℓ) hj (le_trans hwf.1 (by omega)))
  have hL : Lv logw (ptOf ([] ++ List.ofFn (fun k : Fin logw =>
      if bit_value i k.val = 1 then (1 : F) else 0))) = boolean_vector i := by
    rw [← ofFn_bit]
    unfold Lv ptOf
    congr 1
    funext k
    simp [List.getD_eq_getElem?_getD]
  rw [hL, mle_bv _ hlt]
  exact hi

open scoped Classical in
/-- **Binding a coordinate keeps `cPend` but for one value** (`ZkBoundary.pend_round`). -/
theorem cPend_round (pub : Fin c.ninp → F) {Lift : Type} (wOf : Lift → Fin c.ninp → F)
    (ℓ : Lift) (ly : ℕ) (bnd : List F) (hp : cPend pub logw wOf ℓ ly bnd) :
    (univ.filter fun r : F => ¬ cPend pub logw wOf ℓ ly (bnd ++ [r])).card ≤ 1 := by
  obtain ⟨hly, ext, hb⟩ := hp
  refine Finset.card_le_one.mpr fun r1 h1 r2 h2 => ?_
  simp only [mem_filter, mem_univ, true_and, cPend, not_and, not_exists] at h1 h2
  have h1' := h1 hly ext.tail
  have h2' := h2 hly ext.tail
  by_contra hne
  rw [ptOf_bind] at h1' h2'
  set y := ptOf (bnd ++ ext)
  set S := c.assertVec pub (wOf ℓ) (ly + 1)
  unfold AssertsAt at h1' h2' hb
  push Not at h1' h2'
  by_cases hk : bnd.length < 2 * logw
  · by_cases hkl : bnd.length < logw
    · obtain ⟨hL1, hR1⟩ := Lv_update_lt y hkl r1
      obtain ⟨hL2, -⟩ := Lv_update_lt y hkl r2
      rw [hL1, hR1] at h1'
      rw [hL2] at h2'
      have hz := mlin_line_zero (fun v => mle logw S (Vector.ofFn v)) (mle_mlin S)
        (fun j : Fin logw => y j.val) ⟨bnd.length, hkl⟩ hne h1'.1 h2'.1 (y bnd.length)
      have hfix : Function.update (fun j : Fin logw => y j.val) ⟨bnd.length, hkl⟩ (y bnd.length)
          = fun j : Fin logw => y j.val := by
        funext j
        by_cases hj : j = ⟨bnd.length, hkl⟩
        · subst hj; simp
        · rw [Function.update_of_ne hj]
      rw [hfix] at hz
      rcases hb with hb | hb
      · exact hb hz
      · exact hb h1'.2
    · obtain ⟨hR1, hL1⟩ := Rv_update_ge y (by omega) hk r1
      obtain ⟨hR2, -⟩ := Rv_update_ge y (by omega) hk r2
      rw [hR1, hL1] at h1'
      rw [hR2] at h2'
      have hz := mlin_line_zero (fun v => mle logw S (Vector.ofFn v)) (mle_mlin S)
        (fun j : Fin logw => y (logw + j.val)) ⟨bnd.length - logw, by omega⟩ hne h1'.2 h2'.2
        (y bnd.length)
      have hfix : Function.update (fun j : Fin logw => y (logw + j.val))
          ⟨bnd.length - logw, by omega⟩ (y bnd.length) = fun j : Fin logw => y (logw + j.val) := by
        funext j
        by_cases hj : j = ⟨bnd.length - logw, by omega⟩
        · subst hj
          simp only [Function.update_self]
          congr 1
          omega
        · rw [Function.update_of_ne hj]
      rw [hfix] at hz
      rcases hb with hb | hb
      · exact hb h1'.1
      · exact hb hz
  · -- past the full bound nothing moves
    have hL : ∀ t, Lv logw (Function.update y bnd.length t) = Lv logw y := fun t => by
      unfold Lv; congr 1; funext j; rw [Function.update_of_ne (by omega)]
    have hR : ∀ t, Rv logw (Function.update y bnd.length t) = Rv logw y := fun t => by
      unfold Rv; congr 1; funext j; rw [Function.update_of_ne (by omega)]
    rw [hL, hR] at h1'
    rcases hb with hb | hb
    · exact hb h1'.1
    · exact hb h1'.2

omit [DecidableEq F] [Fintype F] in
/-- At or past the full bound, a completion does not move the two points. -/
theorem LR_append_full (bnd ext : List F) (hlen : 2 * logw ≤ bnd.length) :
    Lv logw (ptOf (bnd ++ ext)) = Lv logw (ptOf bnd) ∧ Rv logw (ptOf (bnd ++ ext)) = Rv logw (ptOf bnd) := by
  constructor
  · unfold Lv; congr 1; funext j; exact ptOf_append_lt _ _ (by omega)
  · unfold Rv; congr 1; funext j; exact ptOf_append_lt _ _ (by omega)

/-! ## 3. The code the boundary is stated against -/

/-- **The verifier's code agrees with the construction**: the next state's points, the layer
coefficient, and the input row. -/
structure CodeAgrees {C X Q Msg Gpt : Type} {M : ℕ} (pub : Fin c.ninp → F)
    (V : ZkCode C F X Q Msg Gpt M c.ninp logw 0) : Prop where
  hst : ∀ bnd wc0 wc1, (V.stNext bnd wc0 wc1).g0 = (challenge_split (logw := logw) (logc := 0) bnd).2.1
    ∧ (V.stNext bnd wc0 wc1).g1 = (challenge_split (logw := logw) (logc := 0) bnd).2.2
  heqq : ∀ ly st b a bnd, V.eqqOf ly st b a bnd = bindGhAll (c.qgates ly) b a st.g0 st.g1
    (challenge_split (logw := logw) (logc := 0) bnd).2.1
    (challenge_split (logw := logw) (logc := 0) bnd).2.2
  hnpub : V.npub = c.npub
  hinC : ∀ bnd a (i : Fin c.ninp), V.inCoeffs bnd a i
    = eq_mle_basis i.val (challenge_split (logw := logw) (logc := 0) bnd).2.1
      + a * eq_mle_basis i.val (challenge_split (logw := logw) (logc := 0) bnd).2.2
  hpubB : ∀ bnd a, V.pubBinding bnd a
    = ∑ i ∈ univ \ privIdx c.ninp c.npub,
        (eq_mle_basis i.val (challenge_split (logw := logw) (logc := 0) bnd).2.1
          + a * eq_mle_basis i.val (challenge_split (logw := logw) (logc := 0) bnd).2.2) * pub i

/-- **The candidates' committed columns are their witnesses** on the private indices. -/
def AsgAgrees {M : ℕ} {Lift : Type} (asg : Lift → LigeroAssignment c.ninp M F)
    (wOf : Lift → Fin c.ninp → F) : Prop :=
  ∀ ℓ, ∀ i ∈ privIdx c.ninp c.npub, (asg ℓ).1 i = wOf ℓ i

/-! ## 4. The boundary -/

/-- The next layer read at the current layer's schedule is the next layer at `beta = 0`
(`V_local`). -/
theorem V_next_sched (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw) (hone : c.OneWire pub)
    (priv : Fin c.ninp → F) (ly : ℕ) (b : F) :
    (c.toLayered pub hwf hone).V (ly + 1) priv (sched ly b)
      = (c.toLayered pub hwf hone).V (ly + 1) priv (sched (ly + 1) 0) :=
  (c.toLayered pub hwf hone).V_local (ly + 1) priv _ _ fun i hi => by
    simp only [sched]
    rw [Function.update_of_ne (by omega)]
    by_cases h : i = ly + 1
    · subst h; simp
    · rw [Function.update_of_ne h]

/-- **`cPend` at the full bound is the slope of the next layer's pair in its `beta`**
(`ZkBoundary.pend_close`). -/
theorem cPend_close {C X Q Msg Gpt : Type} {M : ℕ} (pub : Fin c.ninp → F)
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (hde : c.DeadEnd)
    {V : ZkCode C F X Q Msg Gpt M c.ninp logw 0} (hV : CodeAgrees pub V) {Lift : Type}
    (wOf : Lift → Fin c.ninp → F) (ℓ : Lift) (ly : ℕ) (bnd : List F) (wc0 wc1 : F)
    (hlen : bnd.length = 2 * logw) (hp : cPend pub logw wOf ℓ ly bnd) :
    zkW pub hwf hone wOf ℓ (ly + 1) (V.stNext bnd wc0 wc1) 1
      ≠ zkW pub hwf hone wOf ℓ (ly + 1) (V.stNext bnd wc0 wc1) 0 := by
  obtain ⟨hly, ext, hb⟩ := hp
  obtain ⟨hLe, hRe⟩ := LR_append_full (logw := logw) bnd ext (by omega)
  have hdec : ∀ b g, (c.toLayered pub hwf hone).V (ly + 1) (wOf ℓ) (sched (ly + 1) b) g
      (V.stNext bnd wc0 wc1).q
      = (c.toLayered pub hwf hone).V (ly + 1) (wOf ℓ) (fun _ => 0) g (V.stNext bnd wc0 wc1).q
        + b * mle logw (c.assertVec pub (wOf ℓ) (ly + 1)) g := fun b g => by
    rw [QuadCircuit.toLayered_V_decomp pub hwf hone hde hly]
    simp only [sched, Function.update_self]
  intro heq
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  simp only [zkW, hdec, one_mul, zero_mul, add_zero] at h1 h2
  rw [(hV.hst bnd wc0 wc1).1, cs_L] at h1
  rw [(hV.hst bnd wc0 wc1).2, cs_R] at h2
  unfold AssertsAt at hb
  rw [hLe, hRe] at hb
  rcases hb with hb | hb
  · exact hb (by linear_combination h1)
  · exact hb (by linear_combination h2)

/--
**The construction's `ZkBoundary`**, under `DeadEnd`, for a code that agrees with the construction
and candidates whose committed columns are their witnesses.  The pending predicate is `cPend`; the
round count is `2 · logw` per layer (`honest_final`'s full bound).
-/
noncomputable def zkBoundaryOf [SumcheckInterp F] {C X Q Msg Gpt : Type} {M : ℕ}
    (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (hde : c.DeadEnd)
    (V : ZkCode C F X Q Msg Gpt M c.ninp logw 0) (hV : CodeAgrees pub V) {Lift : Type}
    (wOf : Lift → Fin c.ninp → F) (asg : Lift → LigeroAssignment c.ninp M F)
    (hasg : AsgAgrees asg wOf) :
    ZkBoundary V (zkHonestOf pub hwf hone wOf (cPend pub logw wOf)) asg c.nl (fun _ => 2 * logw) where
  W := zkW pub hwf hone wOf
  rel ℓ ly st b a := zkW_rel pub hwf hone wOf _ ℓ ly st b a
  final ℓ ly st b a bnd wc0 wc1 hlen _ := by
    show c.honestSum pub hwf hone (wOf ℓ) ly st (sched ly b) a bnd = _
    rw [QuadCircuit.honest_final pub hwf hone (wOf ℓ) ly st _ a bnd (by omega), hV.heqq,
      V_next_sched pub hwf hone (wOf ℓ) ly b]
    simp only [zkW, sched, Function.update_self, (hV.hst bnd wc0 wc1).1, (hV.hst bnd wc0 wc1).2]
    rfl
  W_affine ℓ ly st b := zkW_affine pub hwf hone wOf ℓ ly st b
  pend_round ℓ ly bnd hp := by
    convert cPend_round pub wOf ℓ ly bnd hp
    rfl
  pend_close ℓ ly bnd wc0 wc1 hlen hp := cPend_close pub hwf hone hde hV wOf ℓ ly bnd wc0 wc1 hlen hp
  pend_last ℓ j bnd hj hp := by
    have := hp.1
    omega
  hin ℓ ly bnd wc0 wc1 a hlen hlast := by
    have h := QuadCircuit.toLayered_hin pub hwf hone (wOf ℓ) (sched (ly + 1) 0) a
      (challenge_split (logw := logw) (logc := 0) bnd).2.1
      (challenge_split (logw := logw) (logc := 0) bnd).2.2
    rw [← hlast] at h
    rw [hV.hpubB, hV.hnpub]
    simp only [hV.hinC]
    simp only [zkW, (hV.hst bnd wc0 wc1).1, (hV.hst bnd wc0 wc1).2]
    refine Eq.trans ?_ h
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hasg ℓ i hi]

/-! ## 5. The field half's analysis data -/

/--
**A `ZkFieldData` for the construction**, at `Sat ℓ := c.Satisfied pub (wOf ℓ)`: the boundary is
`zkBoundaryOf`, the layer-0 count is `zk_hinit` at `binit = (logw + 2)·|F|^(logw+1)`, and the
decoders' balances are the only further inputs.  Under `WellFormed`, `OneWire`, `Isolated`,
`DeadEnd` and `0 < nl`, for a code that agrees with the construction (`CodeAgrees`, and `begin_circuit`
puts both points at the output point) and candidates whose committed columns are their witnesses.
-/
noncomputable def zkFieldDataOf [SumcheckInterp F] {C X Q Msg : Type} [Fintype C] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] {M : ℕ} (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (hiso : c.Isolated) (hde : c.DeadEnd) (hnl : 0 < c.nl)
    (V : ZkCode C F X Q Msg (Fin logw → F) M c.ninp logw 0) (hV : CodeAgrees pub V)
    (hst0 : ∀ G, (V.st0 G).g0 = Vector.ofFn G ∧ (V.st0 G).g1 = Vector.ofFn G)
    {Lift : Type} (wOf : Lift → Fin c.ninp → F) (asg : Lift → LigeroAssignment c.ninp M F)
    (hasg : AsgAgrees asg wOf) (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin logw → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : X, (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : Q, (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq) :
    ZkFieldData C F X Q Msg (Fin logw → F) Lift M c.ninp logw 0 c.nl (fun _ => 2 * logw) V
      (zkHonestOf pub hwf hone wOf (cPend pub logw wOf)) asg (fun ℓ => c.Satisfied pub (wOf ℓ)) where
  B := zkBoundaryOf pub hwf hone hde V hV wOf asg hasg
  binit := (logw + 2) * Fintype.card F ^ (logw + 1)
  hinit ℓ hns hnp := by
    convert zk_hinit pub hwf hone hiso hde hnl wOf (cPend pub logw wOf) (cPend_sees pub hwf wOf) V
      hst0 ℓ hns hnp
  kinit := kinit
  kpair := kpair
  k := k
  kchal := kchal
  kq := kq
  hbalInit := hbalInit
  hbalPair := hbalPair
  hbalF := hbalF
  hbalChal := hbalChal
  hbalQuery := hbalQuery

end Lfzk.ZkArithInit
