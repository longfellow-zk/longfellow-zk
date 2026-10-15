import Lfzk.ConcreteCircuit
import Lfzk.ZkLayers
import Lfzk.RbrSplit

/-!
# The constructed arithmetization, against the soundness chain's interfaces

`Lfzk.ConcreteCircuit` builds a `LayeredCircuit` from a deployed `QuadCircuit`.  This file shows how
the chain's arithmetization premises are met by it — or, where an interface is too strong, proves
that it cannot be met.

## Discharged (theorems about the construction)

* **`EqqAgree`** (copied from `proofs/lfzk/Lfzk/LigeroBridge.lean`): `toLayered_eqq` — the model's
  `LayeredCircuit.eqq` is `Quad::bind_gh_all` on the sparse terms (`bindGhAll`), a function of public
  data only; `toLayered_eqqAgree` — the verifier's coefficients along a run (`runEqqs`) agree with it
  at every layer.
* **`ZkBoundary`-shaped facts** (`RbrZkLongfellow`): `honest_rel` (`rel`), `honest_final` (`final`,
  with `EQQ = bindGhAll` at the layer's own `beta`), `honest_W_affine` (`W_affine`), `toLayered_hin`
  (`hin`: public binding plus private row = `alpha`-combination of the input layer's pair).
* **`ZkHonest`-shaped honest values**: `honestSum`/`honestPoly` (partial hypercube sums of the layer
  polynomial, continued past the last round so `sum_eq`/`next_eq` hold at every prefix length) with
  `honest_deg_le`, `honest_sum_eq`, `honest_next_eq`.
* **`RbrSplit.FieldData.LC` and `hclaim`**: `LC := toLayered`, `H := honestOf` (an
  `RbrLongfellow.Honest` at schedule `update tail 0 beta₀`), and `honestOf_hclaim` is the `hclaim`
  field; `honestOf_rel` is a `Boundary`'s `rel`.  `layer_claim_at_schedule` (any `LayeredCircuit`):
  the layer claim at `beta = b` is the `alpha`-combination of layer `ly`'s values at `update tail ly b`.
* **Layer 0's slot** (`hinit_of_output`'s hypotheses): `honest_rel` (`hclaim0`), `mle_mlin` (`hml`),
  `toLayered_V_affine` (`haff`), and `top_harith` (`harith`) — at `TopSat`.
* **Intermediate assertions** (what `hinit` cannot see): `toLayered_pair_card` — at layer `ly`'s pair
  slot, claims fixed before `(beta_ly, alpha_ly)` are correct on at most `2|F|` pairs when the layer's
  assertion MLE is non-zero at one of the two points; `toLayered_assert_point_card`, `mlin_cons`,
  `mlin_bind_card` — the points keep it non-zero except on `logw·|F|^(logw-1)` points, one bad
  challenge per bound coordinate.

## Refuted (the interface is stronger than any honest arithmetization)

* **`RbrSplit.FieldData.harith` at a fixed `st0`** (`ThreeOut.harith_fixed_state_false`,
  `fieldData_harith_false`): for every initial state there is an unsatisfied input of a one-layer
  three-output circuit at which all four corners vanish, so no `FieldData` over that circuit with an
  honest `Sat` and a candidate set reaching every input exists.  `toLayered_corners_iff`
  characterises the corners exactly.
* **`ArithmetizedCircuit.arith`** (`ThreeOut.arithmetized_arith_false`): its conclusion is quantified
  over all `(g0, g1)`, so an `ArithmetizedCircuit` whose `eval` is honest on `threeOut` does not exist.
* **`hinit_of_output`'s `harith` at `Sat := Satisfied`** — false for compiled circuits
  (`Cex.output_only_false` in `ConcreteCircuit`); true at `TopSat` (`top_harith`), and
  `satisfied_iff_top` says what is missing: the intermediate layers' assertion vectors.

## Not done here

An `RbrSplit.FieldData`/`ZkFieldData` value: their remaining fields are protocol data (decoders,
boundary close maps, the prover), not arithmetization, and their `harith`/`hinit` are refuted or
need `TopSat` as above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Arith
open Finset Sumcheck

variable {F : Type} [Field F] [DecidableEq F] [Fintype F]

/-! ## 1. Any `LayeredCircuit`: the layer claim at the run's own schedule -/

/--
**The honest layer claim, at the schedule.**  For any `LayeredCircuit`, the hypercube sum of layer
`ly`'s polynomial at `beta = b`, with the next layer read at a schedule `tail`, is the
`alpha`-combination of layer `ly`'s values at the schedule `update tail ly b` (`layer_rel` there, and
`V_local` to replace the next layer's schedule).  At `ly = 0` this is the right-hand side of
`RbrSplit.FieldData.hclaim`.
-/
theorem layer_claim_at_schedule {Witness : Type} {nc nv logw logc : ℕ}
    (LC : LayeredCircuit Witness nc nv logw logc F) (ly : ℕ) (w : Witness) (tail : ℕ → F)
    (b a : F) (st : LayerState logw logc F) :
    layer_claim (nc := nc) (nv := nv) (LC.Quad ly b) (LC.V (ly + 1) w tail) a st.q st.g0 st.g1
      = LC.V ly w (Function.update tail ly b) st.g0 st.q
        + a * LC.V ly w (Function.update tail ly b) st.g1 st.q := by
  have hrel := LC.layer_rel ly w a (Function.update tail ly b) st
  rw [Function.update_self,
    LC.V_local (ly + 1) w (Function.update tail ly b) tail
      (fun i hi => Function.update_of_ne (by omega) _ _)] at hrel
  exact hrel

/-! ## 2. The verifier's `EQQ` is `Quad::bind_gh_all` on the sparse terms -/

omit [Fintype F] in
/-- `Quad::bind_gh_all` (`quad.h`): `∑_t prep_v(v_t, β) · (EQ[g_t, G0] + α·EQ[g_t, G1]) ·
EQ[h0_t, H0] · EQ[h1_t, H1]`, a function of the public gate list and the challenges only. -/
noncomputable def bindGhAll {n : ℕ} (gates : List (GateTerm F)) (b alpha : F)
    (G0 G1 H0 H1 : Vector F n) : F :=
  ∑ k : Fin gates.length, prepV (gates.get k).v b
    * (eq_mle_basis (gates.get k).g G0 + alpha * eq_mle_basis (gates.get k).g G1)
    * eq_mle_basis (gates.get k).h0 H0 * eq_mle_basis (gates.get k).h1 H1

namespace QuadCircuit

variable {c : QuadCircuit F}

/--
**`LayeredCircuit.eqq` of the construction is the verifier's own computation**: `EQ[Q,C] = 1`
(`logc = 0`, one copy) times `bind_gh_all` of layer `ly`'s stored terms at the layer's `beta`, the
fold coefficient and the layer's points and challenges.  Nothing in it reads a claim, a pad or the
witness — which is what `EqqAgree` asks of the public `eqqs`.
-/
theorem toLayered_eqq (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (betas : ℕ → F) (ly : ℕ) (st : LayerState logw 0 F)
    (ld : LayerData logw 0 F) :
    (c.toLayered pub hwf hone).eqq betas ly st ld
      = bindGhAll (c.qgates ly) (betas ly) ld.alpha st.g0 st.g1
          (challenge_split (logw := logw) (logc := 0) ld.challenges).2.1
          (challenge_split (logw := logw) (logc := 0) ld.challenges).2.2 := by
  unfold LayeredCircuit.eqq
  rw [eqMat_one, one_mul]
  exact bind_g_sum (c.qgates ly) (betas ly) ld.alpha (fun t ht => (qgates_lt hwf ly t ht).1) hwf.1
    st.g0 st.g1 _ _

/-- **The layer identity at the full bound** (`ZkBoundary.final`'s shape): layer `ly`'s polynomial at
the transcript's challenges is the verifier's `EQQ` times the next layer's values at the two hand
points.  `layer_poly_at_challenges` with `toLayered_eqq`. -/
theorem toLayered_final (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (betas : ℕ → F) (ly : ℕ) (w : Fin c.ninp → F)
    (st : LayerState logw 0 F) (ld : LayerData logw 0 F) :
    layer_poly_of (nc := 1) (nv := nv) ((c.toLayered pub hwf hone).Quad ly (betas ly))
        ((c.toLayered pub hwf hone).V (ly + 1) w betas) ld.alpha st
        (Vector.ofFn (n := 0 + 2 * logw) fun i => ld.challenges.getD i.val 0)
      = bindGhAll (c.qgates ly) (betas ly) ld.alpha st.g0 st.g1
          (challenge_split (logw := logw) (logc := 0) ld.challenges).2.1
          (challenge_split (logw := logw) (logc := 0) ld.challenges).2.2
        * (c.toLayered pub hwf hone).V (ly + 1) w betas (next_state ld).g0 (next_state ld).q
        * (c.toLayered pub hwf hone).V (ly + 1) w betas (next_state ld).g1 (next_state ld).q := by
  rw [layer_poly_at_challenges, toLayered_eqq]

end QuadCircuit

/-! ### `EqqAgree`, along a run -/

section Eqq

variable [SumcheckInterp F] {M : ℕ}

/--
**`EqqAgree`** (copied from `proofs/lfzk/Lfzk/LigeroBridge.lean`): the public layer coefficients
`eqqs` a Ligero system is built from agree with the model's `LayeredCircuit.eqq` at the states the
run passes through.
-/
def EqqAgree {Witness : Type} {nc nv logw logc : ℕ}
    (LC : LayeredCircuit Witness nc nv logw logc F) (betas : ℕ → F) (pad : Pad M F)
    (eqqs : ℕ → F) : ℕ → LayerState logw logc F → List (ZkLayer M F) → Prop
  | _, _, [] => True
  | ly, st, zl :: rest =>
      eqqs ly = LC.eqq betas ly st (zl.toLayerData (logw := logw) (logc := logc) pad
        (st.claim0 + zl.alpha * st.claim1)) ∧
      EqqAgree LC betas pad eqqs (ly + 1)
        (next_state (zl.toLayerData (logw := logw) (logc := logc) pad
          (st.claim0 + zl.alpha * st.claim1))) rest

omit [Fintype F] [SumcheckInterp F] in
/-- **The verifier's layer coefficients along a run** (`zk_common.h:L107-L111`): at layer `ly`,
`bind_gh_all` of the layer's terms at the layer's `beta`, the layer's `alpha`, the points the run
reached (`G` at layer `0`, the previous layer's hand challenges after) and the layer's own
challenges.  Public: no pad, no claim, no witness. -/
noncomputable def runEqqs {n : ℕ} (gl : ℕ → List (GateTerm F)) (betas : ℕ → F) :
    ℕ → Vector F n → Vector F n → List (ZkLayer M F) → ℕ → F
  | _, _, _, [], _ => 0
  | ly, g0, g1, zl :: rest, k =>
      if k = ly then bindGhAll (gl ly) (betas ly) zl.alpha g0 g1
          (challenge_split (logw := n) (logc := 0) (run_challenges zl.rounds)).2.1
          (challenge_split (logw := n) (logc := 0) (run_challenges zl.rounds)).2.2
      else runEqqs gl betas (ly + 1)
          (challenge_split (logw := n) (logc := 0) (run_challenges zl.rounds)).2.1
          (challenge_split (logw := n) (logc := 0) (run_challenges zl.rounds)).2.2 rest k

namespace QuadCircuit

variable {c : QuadCircuit F}

/-- `EqqAgree` for the construction, at any `eqqs` that is the verifier's from layer `ly` on. -/
theorem toLayered_eqqAgree_from (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (betas : ℕ → F) (pad : Pad M F) :
    ∀ (zls : List (ZkLayer M F)) (ly : ℕ) (st : LayerState logw 0 F) (eqqs : ℕ → F),
      (∀ k, ly ≤ k → eqqs k = runEqqs c.qgates betas ly st.g0 st.g1 zls k) →
      EqqAgree (c.toLayered pub hwf hone) betas pad eqqs ly st zls := by
  intro zls
  induction zls with
  | nil => intro _ _ _ _; trivial
  | cons zl rest ih =>
      intro ly st eqqs h
      refine ⟨?_, ih (ly + 1) _ eqqs (fun k hk => ?_)⟩
      · rw [h ly le_rfl, runEqqs, if_pos rfl, toLayered_eqq]
        rfl
      · rw [h k (by omega), runEqqs, if_neg (by omega)]
        rfl

/--
**`EqqAgree`, discharged for the construction**: the verifier's own `bind_gh_all` coefficients
along the run (`runEqqs`, from the output point `G`) are the model's `eqq` at every layer.
-/
theorem toLayered_eqqAgree (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (betas : ℕ → F) (pad : Pad M F)
    (zls : List (ZkLayer M F)) (st0 : LayerState logw 0 F) :
    EqqAgree (c.toLayered pub hwf hone) betas pad
      (runEqqs c.qgates betas 0 st0.g0 st0.g1 zls) 0 st0 zls :=
  toLayered_eqqAgree_from pub hwf hone betas pad zls 0 st0 _ (fun _ _ => rfl)

end QuadCircuit

end Eqq

/-! ## 3. The input row (`ZkBoundary.hin`'s shape) -/

namespace QuadCircuit

variable {c : QuadCircuit F}

/-- **The input row's linear form is the `alpha`-combination of the input layer's values** at the
last layer's two hand points: `∑_i (EQ[i, H0] + alpha·EQ[i, H1]) · wCol_i = V_nl(H0) + alpha·V_nl(H1)`
(`input_constraint`, `zk_common.h:L406-L418`). -/
theorem toLayered_input_row (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (betas : ℕ → F)
    (alpha : F) (H0 H1 : Vector F logw) :
    ∑ i : Fin c.ninp, (eq_mle_basis i.val H0 + alpha * eq_mle_basis i.val H1)
        * wCol c.npub pub priv i
      = (c.toLayered pub hwf hone).V c.nl priv betas H0 0
        + alpha * (c.toLayered pub hwf hone).V c.nl priv betas H1 0 := by
  rw [toLayered_input pub hwf hone c.nl le_rfl, toLayered_input pub hwf hone c.nl le_rfl,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The same row split as the verifier folds it: the public part into the constant
(`pubBinding`), the private part on the committed columns (`privIdx`). -/
theorem toLayered_hin (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (betas : ℕ → F)
    (alpha : F) (H0 H1 : Vector F logw) :
    (∑ i ∈ univ \ privIdx c.ninp c.npub,
        (eq_mle_basis i.val H0 + alpha * eq_mle_basis i.val H1) * pub i)
      + ∑ i ∈ privIdx c.ninp c.npub,
        (eq_mle_basis i.val H0 + alpha * eq_mle_basis i.val H1) * priv i
      = (c.toLayered pub hwf hone).V c.nl priv betas H0 0
        + alpha * (c.toLayered pub hwf hone).V c.nl priv betas H1 0 := by
  rw [← toLayered_input_row pub hwf hone priv betas alpha H0 H1,
    ← Finset.sum_sdiff (Finset.subset_univ (privIdx c.ninp c.npub))]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [privIdx, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hi
    simp [wCol, show i.val < c.npub by omega]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [privIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [wCol, show ¬ i.val < c.npub by omega]

end QuadCircuit

/-! ## 4a. The points, round by round

The two hand points `L, R` of layer `ly - 1` are bound one coordinate per sumcheck round.  For a
round-by-round doom "the assertion MLE, with the coordinates bound so far, is not identically zero",
each round costs one value of the challenge: binding the first coordinate of a non-zero multilinear
function to `r` leaves it non-zero for all but at most one `r`. -/

omit [DecidableEq F] [Fintype F] in
/-- Binding the first coordinate keeps a function multilinear. -/
lemma mlin_cons {n : ℕ} (h : (Fin (n + 1) → F) → F) (H : ZkMultilinear.MLin h) (r : F) :
    ZkMultilinear.MLin (fun v' : Fin n → F => h (Fin.cons r v')) := by
  intro v' j
  obtain ⟨a, b, hab⟩ := H (Fin.cons r v') j.succ
  refine ⟨a, b, fun X => ?_⟩
  have hx := hab X
  rw [ZkMultilinear.cons_update_succ] at hx
  exact hx

/-- **One round of the point: at most one bad challenge.**  A multilinear function that is not
identically zero stays non-zero after binding its first coordinate, for all but at most one value. -/
theorem mlin_bind_card {n : ℕ} (h : (Fin (n + 1) → F) → F) (H : ZkMultilinear.MLin h)
    (hne : ∃ v, h v ≠ 0) :
    (univ.filter fun r : F => ∀ v' : Fin n → F, h (Fin.cons r v') = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun r1 h1 r2 h2 => ?_)
  simp only [mem_filter, mem_univ, true_and] at h1 h2
  by_contra hne12
  obtain ⟨v, hv⟩ := hne
  apply hv
  have hsl : ∀ v', ZkMultilinear.mlinSlope h v' = 0 := by
    intro v'
    have e1 := h1 v'
    have e2 := h2 v'
    rw [ZkMultilinear.mlin_split h H v' r1] at e1
    rw [ZkMultilinear.mlin_split h H v' r2] at e2
    have : (r1 - r2) * ZkMultilinear.mlinSlope h v' = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hne12
    · exact h'
  have hlo : ∀ v', ZkMultilinear.mlinLo h v' = 0 := by
    intro v'
    have e1 := h1 v'
    rw [ZkMultilinear.mlin_split h H v' r1, hsl v'] at e1
    simpa using e1
  rw [← Fin.cons_self_tail v, ZkMultilinear.mlin_split h H _ (v 0), hlo, hsl]
  ring

/-! ## 4b. Where a violated assertion is caught: the layer's own pair slot

Under `DeadEnd`, `V ly` at the schedule is `V ly⁰ + betas ly · S_ly` with `S_ly` the MLE of the
assertion vector (`toLayered_V_decomp`).  The claims `(c0, c1)` a run carries into layer `ly` are
fixed before `begin_layer` draws `(alpha_ly, beta_ly)`; they are correct only on a bilinear zero set
in `(beta, alpha)`, which is small as soon as `S_ly` does not vanish at both points.  At layer `0`
this is the output slot (`toLayered_init_card_of_top`); at `0 < ly` it is the only place an
intermediate assertion is seen. -/

namespace QuadCircuit

variable {c : QuadCircuit F}

/-- **Layer `ly`'s pair slot, counted over `(beta_ly, alpha_ly)`**: if the assertion MLE of layer
`ly` is non-zero at one of the two points, then whatever claims were carried in, at most `2|F|` of
the `|F|²` pairs make them correct. -/
theorem toLayered_pair_card (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (hde : c.DeadEnd) {ly : ℕ}
    (hly : ly < c.nl) (priv : Fin c.ninp → F) (tail : ℕ → F) (c0 c1 : F) (L R : Vector F logw)
    (hS : mle logw (c.assertVec pub priv ly) L ≠ 0 ∨ mle logw (c.assertVec pub priv ly) R ≠ 0) :
    (univ.filter fun p : F × F =>
        c0 + p.2 * c1
          = (c.toLayered pub hwf hone).V ly priv (Function.update tail ly p.1) L 0
            + p.2 * (c.toLayered pub hwf hone).V ly priv (Function.update tail ly p.1) R 0).card
      ≤ 2 * Fintype.card F := by
  set V0 := fun X => (c.toLayered pub hwf hone).V ly priv (fun _ => 0) X 0 with hV0
  set S := fun X => mle logw (c.assertVec pub priv ly) X with hSdef
  have hdec : ∀ b X, (c.toLayered pub hwf hone).V ly priv (Function.update tail ly b) X 0
      = V0 X + b * S X := fun b X => by
    rw [toLayered_V_decomp pub hwf hone hde hly priv _ X 0, Function.update_self]
  refine le_trans (Finset.card_le_card (t := univ.filter fun p : F × F =>
      (fun b a => (V0 L - c0) + a * (V0 R - c1) + b * S L + a * b * S R) p.1 p.2 = 0) ?_) ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    rw [hdec, hdec] at hp
    linear_combination -hp
  · refine bilinear_zero_card _ (V0 L - c0) (V0 R - c1) (S L) (S R) (fun b a => rfl) ?_
    rintro ⟨-, -, h1, h2⟩
    rcases hS with h | h
    · exact h h1
    · exact h h2

/-- The points `L` at which a non-zero assertion vector's MLE vanishes: at most
`logw · |F|^(logw-1)` (`mle_zero_card`). -/
theorem toLayered_assert_point_card (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) {ly : ℕ} (hly : ly < c.nl) (priv : Fin c.ninp → F)
    (hne : ∃ j, c.assertVec pub priv ly j ≠ 0) :
    (univ.filter fun L : Fin logw → F =>
        mle logw (c.assertVec pub priv ly) (Vector.ofFn L) = 0).card
      ≤ logw * Fintype.card F ^ (logw - 1) := by
  obtain ⟨j, hj⟩ := hne
  refine mle_zero_card _ ⟨j, ?_, hj⟩
  by_contra hge
  exact hj (assertVec_supp hwf pub priv hly (le_trans hwf.1 (by omega)))

/-! ## 5. `RbrSplit.FieldData.harith` at a fixed initial state -/

/-- **The four corners of `harith`, for the construction**: layer 0's claim vanishes at
`(beta₀, alpha₀) ∈ {0,1}²` iff the honest output MLE and the layer-0 assertion MLE both vanish at
both points.  (`layer_claim_at_schedule` and `toLayered_V_decomp`.) -/
theorem toLayered_corners_iff (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (hde : c.DeadEnd) (hnl : 0 < c.nl)
    (priv : Fin c.ninp → F) (tail : ℕ → F) (st : LayerState logw 0 F) :
    (layer_claim (nc := 1) (nv := nv) ((c.toLayered pub hwf hone).Quad 0 0)
          ((c.toLayered pub hwf hone).V 1 priv tail) 0 st.q st.g0 st.g1 = 0 ∧
       layer_claim (nc := 1) (nv := nv) ((c.toLayered pub hwf hone).Quad 0 0)
          ((c.toLayered pub hwf hone).V 1 priv tail) 1 st.q st.g0 st.g1 = 0 ∧
       layer_claim (nc := 1) (nv := nv) ((c.toLayered pub hwf hone).Quad 0 1)
          ((c.toLayered pub hwf hone).V 1 priv tail) 0 st.q st.g0 st.g1 = 0 ∧
       layer_claim (nc := 1) (nv := nv) ((c.toLayered pub hwf hone).Quad 0 1)
          ((c.toLayered pub hwf hone).V 1 priv tail) 1 st.q st.g0 st.g1 = 0)
      ↔ (mle logw (c.honest pub priv 0) st.g0 = 0 ∧ mle logw (c.honest pub priv 0) st.g1 = 0 ∧
          mle logw (c.assertVec pub priv 0) st.g0 = 0 ∧
          mle logw (c.assertVec pub priv 0) st.g1 = 0) := by
  have hcl : ∀ b a : F, layer_claim (nc := 1) (nv := nv) ((c.toLayered pub hwf hone).Quad 0 b)
      ((c.toLayered pub hwf hone).V 1 priv tail) a st.q st.g0 st.g1
        = (mle logw (c.honest pub priv 0) st.g0 + b * mle logw (c.assertVec pub priv 0) st.g0)
          + a * (mle logw (c.honest pub priv 0) st.g1
            + b * mle logw (c.assertVec pub priv 0) st.g1) := by
    intro b a
    rw [layer_claim_at_schedule (c.toLayered pub hwf hone) 0 priv tail b a st,
      toLayered_V_decomp pub hwf hone hde hnl priv _ st.g0 st.q,
      toLayered_V_decomp pub hwf hone hde hnl priv _ st.g1 st.q, Function.update_self]
    rfl
  simp only [hcl]
  constructor
  · rintro ⟨h00, h01, h10, h11⟩
    refine ⟨by linear_combination h00, by linear_combination h01 - h00,
      by linear_combination h10 - h00, by linear_combination h11 - h10 - h01 + h00⟩
  · rintro ⟨a1, a2, a3, a4⟩
    rw [a1, a2, a3, a4]
    norm_num

end QuadCircuit

/-! ### At a fixed point the corners can always be made to vanish

`threeOut` outputs three private inputs (through the constant wire); it is satisfied iff they are
zero.  At **any** fixed pair of points `(g0, g1)` the output MLE is two linear forms in the three
outputs, so some non-zero output vector — an unsatisfied input — makes all four corners vanish
(`threeOut_corners`).  So `harith` at a fixed `st0` is false for any candidate set containing all
inputs, and `ArithmetizedCircuit.arith` (quantified over all `g0 g1`) is false for any honest
`eval` (`arithmetized_arith_false`).  The random output point is what the deployed verifier
uses instead (`toLayered_init_card`). -/

namespace ThreeOut

/-- Inputs `1, x₁, x₂, x₃`; one layer, output `j` is `1 · x_{j+1}`. -/
def threeOut : QuadCircuit F :=
  ⟨[[⟨0, 0, 1, 1⟩, ⟨1, 0, 2, 1⟩, ⟨2, 0, 3, 1⟩]], 4, 1⟩

omit [DecidableEq F] [Fintype F] in
lemma threeOut_nl : (threeOut (F := F)).nl = 1 := rfl
omit [DecidableEq F] [Fintype F] in
lemma threeOut_gates0 :
    (threeOut (F := F)).gates 0 = [⟨0, 0, 1, 1⟩, ⟨1, 0, 2, 1⟩, ⟨2, 0, 3, 1⟩] := rfl
omit [DecidableEq F] [Fintype F] in
lemma threeOut_gates1 : (threeOut (F := F)).gates 1 = [] := rfl

omit [DecidableEq F] [Fintype F] in
theorem threeOut_wf : (threeOut (F := F)).WellFormed 4 2 := by
  refine ⟨by norm_num, by norm_num [threeOut], by norm_num [threeOut], by norm_num [threeOut], ?_⟩
  intro ly hly t ht
  rw [threeOut_nl] at hly
  interval_cases ly
  rw [threeOut_gates0] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp

omit [DecidableEq F] [Fintype F] in
theorem threeOut_deadEnd : (threeOut (F := F)).DeadEnd := by
  intro ly hly t _
  rw [threeOut_nl] at hly
  interval_cases ly
  simp [QuadCircuit.AssertWire, threeOut_gates1]

/-- The public input: the constant one. -/
def tPub : Fin (threeOut (F := F)).ninp → F := fun _ => 1

omit [DecidableEq F] [Fintype F] in
theorem threeOut_one : (threeOut (F := F)).OneWire tPub := fun _ => rfl

/-- The private input carrying the three outputs `x`. -/
def tPriv (x : Fin 3 → F) : Fin (threeOut (F := F)).ninp → F :=
  fun i => if h : 0 < i.val then x ⟨i.val - 1, by have h4 : i.val < 4 := i.isLt; omega⟩
    else 0

omit [DecidableEq F] [Fintype F] in
lemma threeOut_input (x : Fin 3 → F) (j : ℕ) (hj : j < 3) :
    (threeOut (F := F)).inputVec tPub (tPriv x) (j + 1) = x ⟨j, hj⟩ := by
  unfold QuadCircuit.inputVec
  rw [dif_pos (show j + 1 < (threeOut (F := F)).ninp by simp [threeOut]; omega)]
  simp [wCol, tPriv, show (threeOut (F := F)).npub = 1 from rfl]

omit [DecidableEq F] [Fintype F] in
lemma threeOut_input0 (x : Fin 3 → F) :
    (threeOut (F := F)).inputVec tPub (tPriv x) 0 = 1 := by
  unfold QuadCircuit.inputVec
  rw [dif_pos (show 0 < (threeOut (F := F)).ninp by simp [threeOut])]
  simp [wCol, tPub, show (threeOut (F := F)).npub = 1 from rfl]

omit [Fintype F] in
/-- The honest output vector is `x`. -/
lemma threeOut_honest (x : Fin 3 → F) (j : ℕ) :
    (threeOut (F := F)).honest tPub (tPriv x) 0 j = if h : j < 3 then x ⟨j, h⟩ else 0 := by
  unfold QuadCircuit.honest
  rw [QuadCircuit.wires_lt (by rw [threeOut_nl]; norm_num), QuadCircuit.evalGates_eq_list,
    QuadCircuit.wires_ge (show (threeOut (F := F)).nl ≤ 0 + 1 from le_rfl), threeOut_gates0]
  have h1 : prepV (1 : F) 0 = 1 := by simp [prepV]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1, one_mul,
    threeOut_input0]
  rw [threeOut_input x 0 (by norm_num), threeOut_input x 1 (by norm_num),
    threeOut_input x 2 (by norm_num)]
  by_cases h : j < 3
  · rw [dif_pos h]
    interval_cases j <;> simp
  · rw [dif_neg h, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

omit [Fintype F] in
/-- No assertions: the assertion vector of layer `0` is zero. -/
lemma threeOut_assertVec (x : Fin 3 → F) (j : ℕ) :
    (threeOut (F := F)).assertVec tPub (tPriv x) 0 j = 0 := by
  unfold QuadCircuit.assertVec QuadCircuit.assertSum
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [if_neg]
  rintro ⟨-, hv⟩
  obtain ⟨i, hi⟩ := i
  have hi' : i < 3 := hi
  simp only [threeOut_gates0] at hv
  interval_cases i <;> simp at hv

omit [Fintype F] in
lemma threeOut_unsat (x : Fin 3 → F) (hx : x ≠ 0) :
    ¬ (threeOut (F := F)).Satisfied tPub (tPriv x) := by
  rintro ⟨-, hout⟩
  apply hx
  funext j
  have := hout j.val
  rw [threeOut_honest, dif_pos j.isLt] at this
  exact this

omit [Fintype F] in
/-- The output MLE is `∑_{j<3} EQ[j, g] · x_j`. -/
lemma threeOut_mle (x : Fin 3 → F) (g : Vector F 2) :
    mle 2 ((threeOut (F := F)).honest tPub (tPriv x) 0) g
      = ∑ j : Fin 3, eq_mle_basis j.val g * x j := by
  unfold mle
  rw [show 2 ^ 2 = 3 + 1 by norm_num, Finset.sum_range_succ, threeOut_honest,
    dif_neg (by norm_num), mul_zero, add_zero, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [threeOut_honest, dif_pos j.isLt]

omit [Fintype F] in
/--
**At every fixed pair of points, some unsatisfied input makes all four corners vanish.**
-/
theorem threeOut_corners (g0 g1 : Vector F 2) :
    ∃ x : Fin 3 → F, x ≠ 0 ∧
      mle 2 ((threeOut (F := F)).honest tPub (tPriv x) 0) g0 = 0 ∧
      mle 2 ((threeOut (F := F)).honest tPub (tPriv x) 0) g1 = 0 := by
  let A : Matrix (Fin 2) (Fin 3) F := fun i j => eq_mle_basis j.val (if i = 0 then g0 else g1)
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
  refine ⟨x, hx0, ?_, ?_⟩
  · rw [threeOut_mle]
    have := congrFun hx 0
    simpa [Matrix.mulVec, dotProduct, A] using this
  · rw [threeOut_mle]
    have := congrFun hx 1
    simpa [Matrix.mulVec, dotProduct, A] using this

/--
**`RbrSplit.FieldData.harith` is false at every fixed initial state** for a candidate set that
contains every input: whatever `st0` is, some unsatisfied input of `threeOut` has all four of
`harith`'s corners equal to zero.
-/
theorem harith_fixed_state_false (st0 : LayerState 2 0 F) (tail : ℕ → F) :
    ∃ x : Fin 3 → F, ¬ (threeOut (F := F)).Satisfied tPub (tPriv x) ∧
      (layer_claim (nc := 1) (nv := 4) (((threeOut (F := F)).toLayered tPub threeOut_wf
            threeOut_one).Quad 0 0)
          (((threeOut (F := F)).toLayered tPub threeOut_wf threeOut_one).V 1 (tPriv x) tail) 0
          st0.q st0.g0 st0.g1 = 0 ∧
       layer_claim (nc := 1) (nv := 4) (((threeOut (F := F)).toLayered tPub threeOut_wf
            threeOut_one).Quad 0 0)
          (((threeOut (F := F)).toLayered tPub threeOut_wf threeOut_one).V 1 (tPriv x) tail) 1
          st0.q st0.g0 st0.g1 = 0 ∧
       layer_claim (nc := 1) (nv := 4) (((threeOut (F := F)).toLayered tPub threeOut_wf
            threeOut_one).Quad 0 1)
          (((threeOut (F := F)).toLayered tPub threeOut_wf threeOut_one).V 1 (tPriv x) tail) 0
          st0.q st0.g0 st0.g1 = 0 ∧
       layer_claim (nc := 1) (nv := 4) (((threeOut (F := F)).toLayered tPub threeOut_wf
            threeOut_one).Quad 0 1)
          (((threeOut (F := F)).toLayered tPub threeOut_wf threeOut_one).V 1 (tPriv x) tail) 1
          st0.q st0.g0 st0.g1 = 0) := by
  obtain ⟨x, hx0, h0, h1⟩ := threeOut_corners (F := F) st0.g0 st0.g1
  refine ⟨x, threeOut_unsat x hx0, ?_⟩
  rw [QuadCircuit.toLayered_corners_iff tPub threeOut_wf threeOut_one threeOut_deadEnd
    (by rw [threeOut_nl]; norm_num) (tPriv x) tail st0]
  have ha : ∀ X : Vector F 2, mle 2 ((threeOut (F := F)).assertVec tPub (tPriv x) 0) X = 0 :=
    fun X => Finset.sum_eq_zero (fun j _ => by rw [threeOut_assertVec, mul_zero])
  exact ⟨h0, h1, ha _, ha _⟩

/--
**`ArithmetizedCircuit.arith` is unsatisfiable with an honest `eval`.**  Its conclusion is quantified
over every pair of points `(g0, g1)`; for an arithmetization that contains `threeOut` (its gates, the
constant-one public input, an `eval` that is `Satisfied`, and witnesses realising every private
column), fixing any points gives an unsatisfied witness whose four corners all vanish.
-/
theorem arithmetized_arith_false {Circuit Input Witness : Type}
    (AC : ArithmetizedCircuit Circuit Input Witness 1 4 4 1 2 2 0 F) (c : Circuit) (inp : Input)
    (hgates : AC.gates c = (threeOut (F := F)).gates 0)
    (hpub : ∀ cp, AC.pub_col inp cp = tPub)
    (heval : ∀ w, AC.eval c inp w = false ↔
      ¬ (threeOut (F := F)).Satisfied tPub (AC.priv_col w 0))
    (hsurj : ∀ x : Fin 4 → F, ∃ w, ∀ cp, AC.priv_col w cp = x) (g0 g1 : Vector F 2) :
    False := by
  obtain ⟨x, hx0, h0, h1⟩ := threeOut_corners (F := F) g0 g1
  obtain ⟨w, hw⟩ := hsurj (tPriv x)
  have hevf : AC.eval c inp w = false := by
    rw [heval, hw 0]
    exact threeOut_unsat x hx0
  let LC := (threeOut (F := F)).toLayered tPub threeOut_wf threeOut_one
  have hQ : ∀ b, quadMle (logv := 2) (logw := 2) (AC.gates c) b = LC.Quad 0 b := fun b => by
    rw [hgates]
    rfl
  have hV : (fun (g : Vector F 2) (cp : Vector F 0) =>
      wMle 1 (AC.pub_col inp cp) (AC.priv_col w cp) g) = LC.V 1 (tPriv x) (fun _ => 0) := by
    funext g cp
    rw [hpub, hw]
    exact (QuadCircuit.toLayered_input_wMle tPub threeOut_wf threeOut_one (tPriv x) _ g cp).symm
  apply AC.arith c inp w (Vector.ofFn fun i => i.elim0) g0 g1 hevf
  simp only [hQ, hV]
  let st : LayerState 2 0 F := ⟨0, 0, Vector.ofFn fun i => i.elim0, g0, g1⟩
  have hc := (QuadCircuit.toLayered_corners_iff tPub threeOut_wf threeOut_one threeOut_deadEnd
    (by rw [threeOut_nl]; norm_num) (tPriv x) (fun _ => 0) st).mpr
  have ha : ∀ X : Vector F 2, mle 2 ((threeOut (F := F)).assertVec tPub (tPriv x) 0) X = 0 :=
    fun X => Finset.sum_eq_zero (fun j _ => by rw [threeOut_assertVec, mul_zero])
  exact hc ⟨h0, h1, ha _, ha _⟩

end ThreeOut

/-! ## 6. The honest values: partial hypercube sums of the layer polynomial

`ZkHonest` (and `RbrLongfellow.Honest`) take the honest claim at every bound prefix `bnd` of **any**
length, with `sum_eq` and `next_eq` at every length.  Below the round count `n` this is the usual
partial hypercube sum (`sumcheck_eval_round`, `sumcheck_round_poly`); past it the sum is continued
by `f(bnd[:n]) · ∏_{i ≥ n} bnd[i]` (each extra "round" is the line `X`, which sums to `1` over
`{0, 1}`), so the two laws hold at every length.  The deployed verifier never runs past `n`. -/

section Partial

variable {n : ℕ}

omit [DecidableEq F] [Fintype F] in
lemma chalVec_append (bnd : List F) (r : F) {k : ℕ} (hk : k ≤ bnd.length) :
    chalVec (bnd ++ [r]) k = chalVec bnd k := by
  ext i hi
  simp only [chalVec, Vector.getElem_ofFn]
  rw [List.getD_append _ _ _ _ (by omega)]

omit [DecidableEq F] [Fintype F] in
lemma getD_append_length (bnd : List F) (r : F) : (bnd ++ [r]).getD bnd.length 0 = r := by
  simp

omit [DecidableEq F] [Fintype F] in
/-- The last round's partial sum is the polynomial at the full point. -/
lemma sumcheck_eval_round_last (f : Vector F n → F) (k : ℕ) (hk : k + 1 = n) (bnd : List F) :
    sumcheck_eval_round f k (by omega) (chalVec bnd k) (bnd.getD k 0) = f (chalVec bnd n) := by
  subst hk
  rw [sumcheck_eval_round_range]
  have hr : Finset.range (2 ^ (k + 1 - k - 1)) = Finset.range 1 := by
    congr 1
    rw [show k + 1 - k - 1 = 0 from by omega, pow_zero]
  rw [hr, Finset.sum_range_one]
  refine congrArg f ?_
  ext i hi
  simp only [construct_assignment, chalVec, Vector.getElem_ofFn]
  by_cases h : i < k
  · rw [dif_pos h]; simp [Vector.get]
  · rw [dif_neg h]
    have hik : i = k := by omega
    rw [dif_pos hik, hik]

omit [DecidableEq F] [Fintype F] in
/-- The partial sum at a prefix of a given length. -/
noncomputable def psum (f : Vector F n → F) (bnd : List F) : ℕ → F
  | 0 => ∑ j ∈ range (2 ^ n), f (boolean_vector j)
  | k + 1 => if h : k < n then sumcheck_eval_round f k h (chalVec bnd k) (bnd.getD k 0)
      else f (chalVec bnd n) * ∏ i ∈ Finset.Ico n (k + 1), bnd.getD i 0

omit [DecidableEq F] [Fintype F] in
/-- **The honest partial sum** of `f` at a bound prefix. -/
noncomputable def partialSum (f : Vector F n → F) (bnd : List F) : F := psum f bnd bnd.length

/-- **The honest round polynomial** at a bound prefix. -/
noncomputable def partialPoly (f : Vector F n → F) (bnd : List F) : Polynomial F :=
  if h : bnd.length < n then sumcheck_round_poly f bnd.length h (chalVec bnd bnd.length)
  else Polynomial.C (partialSum f bnd) * Polynomial.X

omit [DecidableEq F] [Fintype F] in
lemma partialSum_nil (f : Vector F n → F) :
    partialSum f [] = ∑ j ∈ range (2 ^ n), f (boolean_vector j) := rfl

omit [DecidableEq F] [Fintype F] in
/-- At or past the round count, the partial sum is the polynomial at the point times the extra
coordinates. -/
lemma partialSum_ge (f : Vector F n → F) (bnd : List F) (h : n ≤ bnd.length) :
    partialSum f bnd = f (chalVec bnd n) * ∏ i ∈ Finset.Ico n bnd.length, bnd.getD i 0 := by
  unfold partialSum
  rcases hl : bnd.length with _ | k
  · have hn : n = 0 := by omega
    subst hn
    simp only [psum, pow_zero, Finset.range_one, Finset.sum_singleton, Finset.Ico_self,
      Finset.prod_empty, mul_one]
    exact congrArg f (Vector.ext (fun i hi => absurd hi (by omega)))
  · simp only [psum]
    split_ifs with hk
    · have hkn : k + 1 = n := by omega
      rw [sumcheck_eval_round_last f k hkn bnd, Finset.Ico_eq_empty_of_le (by omega),
        Finset.prod_empty, mul_one]
    · rfl

omit [DecidableEq F] [Fintype F] in
lemma partialSum_lt (f : Vector F n → F) (bnd : List F) (r : F) (h : bnd.length < n) :
    partialSum f (bnd ++ [r]) = sumcheck_eval_round f bnd.length h (chalVec bnd bnd.length) r := by
  unfold partialSum
  rw [List.length_append, List.length_singleton]
  simp only [psum, dif_pos h]
  rw [chalVec_append bnd r le_rfl, getD_append_length]

/-- `next_eq`: the round polynomial at `r` is the partial sum one round on. -/
theorem partialPoly_next (f : Vector F n → F) (bnd : List F) (r : F) :
    (partialPoly f bnd).eval r = partialSum f (bnd ++ [r]) := by
  unfold partialPoly
  split_ifs with h
  · rw [sumcheck_round_poly_eval, partialSum_lt f bnd r h]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      partialSum_ge f bnd (by omega),
      partialSum_ge f (bnd ++ [r]) (by simp; omega), chalVec_append bnd r (by omega),
      List.length_append, List.length_singleton,
      Finset.prod_Ico_succ_top (by omega), getD_append_length, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [List.getD_append _ _ _ _ (by simp at hi; omega)]

omit [DecidableEq F] [Fintype F] in
lemma sumcheck_eval_round_congr (f : Vector F n → F) (bnd : List F) (X : F) {m k : ℕ}
    (hm : m = k) (hh : m < n) :
    sumcheck_eval_round f m hh (chalVec bnd m) X
      = sumcheck_eval_round f k (hm ▸ hh) (chalVec bnd k) X := by
  subst hm; rfl

/-- `sum_eq`: the round polynomial sums over `{0, 1}` to the partial sum. -/
theorem partialPoly_sum (f : Vector F n → F) (bnd : List F) :
    (partialPoly f bnd).eval 0 + (partialPoly f bnd).eval 1 = partialSum f bnd := by
  unfold partialPoly
  split_ifs with h
  · rw [sumcheck_round_poly_eval, sumcheck_round_poly_eval]
    by_cases h0 : bnd.length = 0
    · have hb : bnd = [] := List.length_eq_zero_iff.mp h0
      subst hb
      rw [partialSum_nil]
      exact head_eval_hypercube f h (chalVec [] 0)
    · obtain ⟨k, hk⟩ : ∃ k, bnd.length = k + 1 := ⟨bnd.length - 1, by omega⟩
      have hsplit := sumcheck_eval_round_split f k (by omega) (chalVec bnd k) (bnd.getD k 0)
      rw [prefSucc_chalVec] at hsplit
      have e : partialSum f bnd
          = sumcheck_eval_round f k (by omega) (chalVec bnd k) (bnd.getD k 0) := by
        unfold partialSum
        rw [hk]
        simp only [psum, dif_pos (show k < n by omega)]
      rw [e, ← hsplit, sumcheck_eval_round_congr f bnd 0 hk h,
        sumcheck_eval_round_congr f bnd 1 hk h]
  · simp

/-- `deg_le`: every round polynomial has degree at most `2` when `f` is quadratic in every
coordinate (`WPoly = Poly<3, Field>`). -/
theorem partialPoly_deg [SumcheckInterp F] (f : Vector F n → F) (hf : IsQuadratic f)
    (bnd : List F) : (partialPoly f bnd).natDegree ≤ 2 := by
  unfold partialPoly
  split_ifs with h
  · exact sumcheck_round_poly_natDegree_le_two f _ h _ (hf _ h) three_le_card
  · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X]
    norm_num

end Partial

/-! ### The construction's honest values -/

omit [Fintype F] in
/-- `quadMle` is multilinear in the left hand. -/
lemma quadMle_ml_l {n : ℕ} (gates : List (GateTerm F)) (b : F) (g r : Vector F n) :
    IsMultilinear (fun l => quadMle (logv := n) (logw := n) gates b g l r) := by
  have h : (fun l => quadMle (logv := n) (logw := n) gates b g l r)
      = fun l => ∑ i : Fin gates.length, eq_mle_basis (gates.get i).h0 l
          * (prepV (gates.get i).v b * eq_mle_basis (gates.get i).g g
              * eq_mle_basis (gates.get i).h1 r) := by
    funext l
    simp only [quadMle]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h]
  exact IsMultilinear.sum _ _ (fun i => (eq_mle_basis_multilinear _).mul_const _)

omit [Fintype F] in
/-- `quadMle` is multilinear in the right hand. -/
lemma quadMle_ml_r {n : ℕ} (gates : List (GateTerm F)) (b : F) (g l : Vector F n) :
    IsMultilinear (fun r => quadMle (logv := n) (logw := n) gates b g l r) := by
  have h : (fun r => quadMle (logv := n) (logw := n) gates b g l r)
      = fun r => ∑ i : Fin gates.length, eq_mle_basis (gates.get i).h1 r
          * (prepV (gates.get i).v b * eq_mle_basis (gates.get i).g g
              * eq_mle_basis (gates.get i).h0 l) := by
    funext r
    simp only [quadMle]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h]
  exact IsMultilinear.sum _ _ (fun i => (eq_mle_basis_multilinear _).mul_const _)

namespace QuadCircuit

variable {c : QuadCircuit F}

variable (c) in
/-- The layer polynomial `EQ · QUAD · W · W` of layer `ly` at schedule `X`, fold `a` and state
`st`, for candidate input `priv`. -/
noncomputable def layerPoly (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ) (st : LayerState logw 0 F)
    (X : ℕ → F) (a : F) : Vector F (0 + 2 * logw) → F :=
  layer_poly_of (nc := 1) (nv := nv) ((c.toLayered pub hwf hone).Quad ly (X ly))
    ((c.toLayered pub hwf hone).V (ly + 1) priv X) a st

omit [DecidableEq F] [Fintype F] in
lemma mle_ml {n : ℕ} (v : ℕ → F) : IsMultilinear (fun l : Vector F n => mle n v l) :=
  IsMultilinear.sum _ _ (fun j => (eq_mle_basis_multilinear j).mul_const _)

/-- The constructed `V ly` is multilinear in the point. -/
lemma toLayered_V_ml (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (ly : ℕ) (priv : Fin c.ninp → F) (X : ℕ → F) (q : Vector F 0) :
    IsMultilinear (fun l => (c.toLayered pub hwf hone).V ly priv X l q) :=
  mle_ml (c.wires pub priv X ly)

/-- **Every hand round is quadratic** (`layer_quadratic`). -/
theorem layerPoly_quadratic (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ) (st : LayerState logw 0 F)
    (X : ℕ → F) (a : F) : IsQuadratic (c.layerPoly pub hwf hone priv ly st X a) :=
  _root_.layer_quadratic (nc := 1) (nv := nv) _ _ a st.q st.g0 st.g1
    (fun g r => quadMle_ml_l _ _ g r) (fun g l => quadMle_ml_r _ _ g l)
    (fun q => toLayered_V_ml pub hwf hone (ly + 1) priv X q)

variable (c) in
/-- **The construction's honest claim** at layer `ly`, state `st`, schedule `X`, fold `a` and bound
prefix `bnd` (`ZkHonest.sum`'s shape). -/
noncomputable def honestSum (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ) (st : LayerState logw 0 F)
    (X : ℕ → F) (a : F) (bnd : List F) : F :=
  partialSum (c.layerPoly pub hwf hone priv ly st X a) bnd

variable (c) in
/-- **The construction's honest round polynomial** (`ZkHonest.poly`'s shape). -/
noncomputable def honestPoly (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ) (st : LayerState logw 0 F)
    (X : ℕ → F) (a : F) (bnd : List F) : Polynomial F :=
  partialPoly (c.layerPoly pub hwf hone priv ly st X a) bnd

theorem honest_deg_le [SumcheckInterp F] (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ)
    (st : LayerState logw 0 F) (X : ℕ → F) (a : F) (bnd : List F) :
    (c.honestPoly pub hwf hone priv ly st X a bnd).natDegree ≤ 2 :=
  partialPoly_deg _ (layerPoly_quadratic pub hwf hone priv ly st X a) bnd

theorem honest_sum_eq (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ)
    (st : LayerState logw 0 F) (X : ℕ → F) (a : F) (bnd : List F) :
    (c.honestPoly pub hwf hone priv ly st X a bnd).eval 0
        + (c.honestPoly pub hwf hone priv ly st X a bnd).eval 1
      = c.honestSum pub hwf hone priv ly st X a bnd :=
  partialPoly_sum _ bnd

theorem honest_next_eq (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ)
    (st : LayerState logw 0 F) (X : ℕ → F) (a : F) (bnd : List F) (r : F) :
    (c.honestPoly pub hwf hone priv ly st X a bnd).eval r
      = c.honestSum pub hwf hone priv ly st X a (bnd ++ [r]) :=
  partialPoly_next _ bnd r

/-- **`rel`**: the honest claim a layer starts from is the `alpha`-combination of the layer's values
at its two points, at the schedule (`layer_rel`). -/
theorem honest_rel (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ)
    (st : LayerState logw 0 F) (X : ℕ → F) (a : F) :
    c.honestSum pub hwf hone priv ly st X a []
      = (c.toLayered pub hwf hone).V ly priv X st.g0 st.q
        + a * (c.toLayered pub hwf hone).V ly priv X st.g1 st.q :=
  (c.toLayered pub hwf hone).layer_rel ly priv a X st

/-- **`final`**: at the full bound the honest claim is the verifier's `EQQ` (`bind_gh_all` at the
layer's own `beta`) times the next layer's values at the two hand points the bound determines. -/
theorem honest_final (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ)
    (st : LayerState logw 0 F) (X : ℕ → F) (a : F) (bnd : List F)
    (hlen : bnd.length = 0 + 2 * logw) :
    c.honestSum pub hwf hone priv ly st X a bnd
      = bindGhAll (c.qgates ly) (X ly) a st.g0 st.g1
          (challenge_split (logw := logw) (logc := 0) bnd).2.1
          (challenge_split (logw := logw) (logc := 0) bnd).2.2
        * (c.toLayered pub hwf hone).V (ly + 1) priv X
            (challenge_split (logw := logw) (logc := 0) bnd).2.1
            (challenge_split (logw := logw) (logc := 0) bnd).1
        * (c.toLayered pub hwf hone).V (ly + 1) priv X
            (challenge_split (logw := logw) (logc := 0) bnd).2.2
            (challenge_split (logw := logw) (logc := 0) bnd).1 := by
  unfold honestSum
  rw [partialSum_ge _ bnd (by omega), hlen, Finset.Ico_self, Finset.prod_empty, mul_one]
  exact toLayered_final pub hwf hone X ly priv st ⟨[], bnd, 0, 0, a⟩

/-- **`W_affine`**: a layer's honest pair is affine in the layer's own `beta`. -/
theorem honest_W_affine (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (ly : ℕ)
    (g : Vector F logw) (q : Vector F 0) (X : ℕ → F) (b : F) :
    (c.toLayered pub hwf hone).V ly priv (Function.update X ly b) g q
      = (c.toLayered pub hwf hone).V ly priv (Function.update X ly 0) g q
        + b * ((c.toLayered pub hwf hone).V ly priv (Function.update X ly 1) g q
          - (c.toLayered pub hwf hone).V ly priv (Function.update X ly 0) g q) :=
  toLayered_V_affine pub hwf hone ly priv X b g q

/-! ### Layer 0's slot (`hinit_of_output`'s hypotheses)

`hinit_of_output` (`RbrZkSplit`) takes an output extension `out ℓ Xs G` with `hclaim0`, `hml`,
`haff`, and `harith : ¬ Sat ℓ → ∃ Xs G, out ℓ Xs G ≠ 0`.  For the construction `out` is `V 0` at
`G`; the first three are theorems (`honest_rel`, `mle_mlin`, `toLayered_V_affine`).  `harith` holds
for **`TopSat`** — outputs zero and layer-0 assertions satisfied — and **not** for `Satisfied`
(`Cex.output_only_false`): a violated intermediate assertion never reaches the output. -/

variable (c) in
/-- **Satisfaction as layer 0 sees it**: every output wire is zero and every assertion of layer `0`
holds. -/
def TopSat (pub priv : Fin c.ninp → F) : Prop :=
  (∀ j, c.honest pub priv 0 j = 0) ∧ ∀ j, c.assertVec pub priv 0 j = 0

omit [Fintype F] in
/-- `Satisfied` is `TopSat` plus the assertions of the intermediate layers (isolated assertions). -/
theorem satisfied_iff_top (hiso : c.Isolated) (hnl : 0 < c.nl) (pub priv : Fin c.ninp → F) :
    c.Satisfied pub priv ↔
      c.TopSat pub priv ∧ ∀ ly, 0 < ly → ly < c.nl → ∀ j, c.assertVec pub priv ly j = 0 := by
  have h := unsat_iff hiso pub priv
  constructor
  · intro hs
    have hn : ¬ ((∃ j, c.honest pub priv 0 j ≠ 0) ∨ ∃ ly < c.nl, ∃ j, c.assertVec pub priv ly j ≠ 0) :=
      fun hc => (h.mpr hc) hs
    push Not at hn
    exact ⟨⟨hn.1, hn.2 0 hnl⟩, fun ly _ hly => hn.2 ly hly⟩
  · rintro ⟨⟨hout, hass0⟩, hass⟩
    by_contra hns
    rcases h.mp hns with ⟨j, hj⟩ | ⟨ly, hly, j, hj⟩
    · exact hj (hout j)
    · rcases Nat.eq_zero_or_pos ly with h0 | hpos
      · subst h0; exact hj (hass0 j)
      · exact hj (hass ly hpos hly j)

/-- **`harith` for `hinit_of_output`, at `TopSat`.** -/
theorem top_harith (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (hde : c.DeadEnd) (hnl : 0 < c.nl) (priv : Fin c.ninp → F)
    (hns : ¬ c.TopSat pub priv) :
    ∃ (Xs : ℕ → F) (G : Fin logw → F),
      (c.toLayered pub hwf hone).V 0 priv Xs (Vector.ofFn G) 0 ≠ 0 := by
  have hdec : ∀ (Xs : ℕ → F) j, c.wires pub priv Xs 0 j
      = c.honest pub priv 0 j + Xs 0 * c.assertVec pub priv 0 j := fun Xs j =>
    wires_decomp hde pub priv Xs hnl j
  have hlt : ∀ j, (c.honest pub priv 0 j ≠ 0 ∨ c.assertVec pub priv 0 j ≠ 0) → j < 2 ^ logw := by
    intro j hj
    by_contra hge
    have hge' : nv ≤ j := le_trans hwf.1 (by omega)
    rcases hj with h | h
    · exact h (wires_supp hwf pub priv _ 0 hge')
    · exact h (assertVec_supp hwf pub priv hnl hge')
  have hcube : ∀ (Xs : ℕ → F) j, j < 2 ^ logw → c.wires pub priv Xs 0 j ≠ 0 →
      ∃ G : Fin logw → F, (c.toLayered pub hwf hone).V 0 priv Xs (Vector.ofFn G) 0 ≠ 0 :=
    fun Xs j hj hw => ⟨fun k => if bit_value j k.val = 1 then 1 else 0, by
      show mle logw _ (Vector.ofFn _) ≠ 0
      rw [ofFn_bit, mle_bv _ hj]
      exact hw⟩
  unfold TopSat at hns
  push Not at hns
  by_cases hout : ∃ j, c.honest pub priv 0 j ≠ 0
  · obtain ⟨j, hj⟩ := hout
    obtain ⟨G, hG⟩ := hcube (fun _ => 0) j (hlt j (Or.inl hj))
      (by rw [hdec, zero_mul, add_zero]; exact hj)
    exact ⟨fun _ => 0, G, hG⟩
  · push Not at hout
    obtain ⟨j, hj⟩ := hns (fun j => hout j)
    obtain ⟨G, hG⟩ := hcube (fun _ => 1) j (hlt j (Or.inr hj))
      (by rw [hdec, hout j, zero_add, one_mul]; exact hj)
    exact ⟨fun _ => 1, G, hG⟩

end QuadCircuit

/-! ## 7. `RbrSplit.FieldData`: `LC` and `hclaim` instantiated, `harith` refuted

`FieldData` charges `beta` at layer 0 only (`b`), the other layers' `beta`s being the fixed `tail`.
`honestOf` is `RbrLongfellow.Honest` for the construction at that schedule (`update tail 0 b`):
`FieldData.LC := toLayered`, `FieldData.hclaim` is `honestOf_hclaim`, and a `Boundary`'s `rel` is
`honestOf_rel`.  `fieldData_harith_false`: `harith` cannot hold for a candidate set reaching every
input of `threeOut`. -/

namespace QuadCircuit

variable {c : QuadCircuit F}

/-- **`RbrLongfellow.Honest` for the construction**, at schedule `update tail 0 beta₀`. -/
noncomputable def honestOf [SumcheckInterp F] (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) {Cand : Type}
    (wOf : Cand → Fin c.ninp → F) (tail : ℕ → F) : RbrLongfellow.Honest F Cand logw 0 where
  sum cand ly st b a bnd := c.honestSum pub hwf hone (wOf cand) ly st (Function.update tail 0 b) a bnd
  poly cand ly st b a bnd :=
    c.honestPoly pub hwf hone (wOf cand) ly st (Function.update tail 0 b) a bnd
  deg_le _ ly st _ a bnd := honest_deg_le pub hwf hone _ ly st _ a bnd
  sum_eq _ ly st _ a bnd := honest_sum_eq pub hwf hone _ ly st _ a bnd
  next_eq _ ly st _ a bnd r := honest_next_eq pub hwf hone _ ly st _ a bnd r

/-- **`FieldData.hclaim`, discharged** for `LC := toLayered` and `H := honestOf`. -/
theorem honestOf_hclaim [SumcheckInterp F] (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) {Cand : Type}
    (wOf : Cand → Fin c.ninp → F) (tail : ℕ → F) (st0 : LayerState logw 0 F) :
    ∀ (cand : Cand) (b a : F),
      (c.honestOf pub hwf hone wOf tail).sum cand 0 st0 b a []
        = layer_claim (nc := 1) (nv := nv) ((c.toLayered pub hwf hone).Quad 0 b)
            ((c.toLayered pub hwf hone).V 1 (wOf cand) tail) a st0.q st0.g0 st0.g1 := by
  intro cand b a
  show c.honestSum pub hwf hone (wOf cand) 0 st0 (Function.update tail 0 b) a [] = _
  rw [honest_rel, layer_claim_at_schedule]

/-- **A `Boundary`'s `rel`** for `honestOf`, with the honest pair `W` the layer's values at its two
points at schedule `update tail 0 beta₀`. -/
theorem honestOf_rel [SumcheckInterp F] (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) {Cand : Type}
    (wOf : Cand → Fin c.ninp → F) (tail : ℕ → F) :
    ∀ (cand : Cand) (ly : ℕ) (st : LayerState logw 0 F) (b a : F),
      (c.honestOf pub hwf hone wOf tail).sum cand ly st b a []
        = (c.toLayered pub hwf hone).V ly (wOf cand) (Function.update tail 0 b) st.g0 st.q
          + a * (c.toLayered pub hwf hone).V ly (wOf cand) (Function.update tail 0 b) st.g1 st.q :=
  fun cand ly st _ a => honest_rel pub hwf hone (wOf cand) ly st _ a

end QuadCircuit

/--
**`FieldData.harith` is unsatisfiable** with `LC := toLayered` of `threeOut`, an honest `Sat`, and a
candidate set reaching every input: at the data's own `st0`, `harith_fixed_state_false` supplies an
unsatisfied candidate whose four corners vanish.
-/
theorem fieldData_harith_false [SumcheckInterp F] {C X Q Cand : Type} [Fintype C] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] {H : RbrLongfellow.Honest F Cand 2 0} {Sat : Cand → Prop}
    (FD : RbrSplit.FieldData C F X Q Cand (Fin (ThreeOut.threeOut (F := F)).ninp → F) 1 4 2 0 H
      Sat)
    (hLC : FD.LC = (ThreeOut.threeOut (F := F)).toLayered ThreeOut.tPub ThreeOut.threeOut_wf
      ThreeOut.threeOut_one)
    (hSat : ∀ cand, Sat cand ↔ (ThreeOut.threeOut (F := F)).Satisfied ThreeOut.tPub (FD.wOf cand))
    (hall : ∀ x : Fin 3 → F, ∃ cand, FD.wOf cand = ThreeOut.tPriv x) : False := by
  obtain ⟨x, hns, hcorners⟩ := ThreeOut.harith_fixed_state_false (F := F) FD.st0 FD.tail
  obtain ⟨cand, hcand⟩ := hall x
  refine FD.harith cand (fun hs => hns (by rw [← hcand]; exact (hSat cand).mp hs)) ?_
  rw [hLC, hcand]
  exact hcorners

end Lfzk.Arith
