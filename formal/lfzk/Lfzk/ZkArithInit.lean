import Lfzk.ConcreteCircuitBridge
import Lfzk.RbrZkSplit

/-!
# The zero-knowledge chain's layer-0 premise, discharged for the constructed circuit

`RbrZkSplit.ZkFieldData.hinit` is the one premise of the zero-knowledge chain that is about the
*arithmetization* rather than about honest values: an unsatisfied candidate whose intermediate
assertions all hold has a layer-0 claim that vanishes on few output points.  This file proves it
for `Lfzk.Arith`'s construction (`QuadCircuit.toLayered`) at the honest satisfaction predicate
`Sat ℓ := c.Satisfied pub (wOf ℓ)`, under `QuadCircuit.Isolated` and `QuadCircuit.DeadEnd`:

* `zkHonestOf` — the construction's `RbrZkLongfellow.ZkHonest`: the honest partial sums
  `honestSum` at the schedule `sched ly b` (the layer's own `beta = b`, every other `beta` zero, so
  the next layer is read at `beta = 0` as `ZkHonest` asks), `deg_le`/`sum_eq`/`next_eq` from
  `honest_deg_le`/`honest_sum_eq`/`honest_next_eq`, and the pending predicate a parameter;
* `zkW`, `zkW_rel`, `zkW_affine` — the honest pair at a layer's points, and `ZkBoundary`'s `rel`
  and `W_affine` for it (`honest_rel`, `honest_W_affine`);
* `outExt_ne` — **`hinit_of_output`'s `harith` at `Satisfied`**: an unsatisfied witness all of whose
  intermediate assertion vectors vanish has a non-zero output extension at some `(beta₀, G)`
  (`satisfied_iff_top`, `top_harith`, `toLayered_V_decomp`);
* `zk_hinit` — **the `hinit` field itself**, at `binit = (logw + 2)·|F|^(logw+1)`, for any pending
  predicate that sees a non-zero assertion vector with nothing bound (`SeesAsserts`), and any code
  whose `begin_circuit` state has both points at the output point.

So the arithmetization premise of the zero-knowledge headlines is **satisfiable at the honest
`Satisfied`** (under `Isolated`, `DeadEnd`, `WellFormed`, `OneWire`, `0 < nl`): it is this theorem.
What is not assembled here is the rest of a `ZkFieldData` for the construction: a concrete `Pend`
with `pend_round` (`mlin_bind_card` per bound coordinate), `pend_close` and `pend_last`, and `final`,
`hin` against a concrete `ZkCode` (`honest_final`, `toLayered_hin`, `toLayered_eqqAgree` have those
shapes).  Note also that the construction's output dimension is its uniform `logw`, while the row
headlines use the deployed circuits' `logv`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkArithInit

open Finset Lfzk.Arith Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.ZkMultilinear

variable {F : Type} [Field F] [DecidableEq F] [Fintype F]
variable {c : QuadCircuit F} {nv logw : ℕ}

/-- The schedule with layer `ly`'s `beta` equal to `b` and every other `beta` zero. -/
abbrev sched (ly : ℕ) (b : F) : ℕ → F := Function.update (fun _ => 0) ly b

/-- **The construction's honest values, as a `ZkHonest`**, with the pending predicate `Pend` a
parameter. -/
noncomputable def zkHonestOf [SumcheckInterp F] (pub : Fin c.ninp → F)
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) {Lift : Type}
    (wOf : Lift → Fin c.ninp → F) (Pend : Lift → ℕ → List F → Prop) : ZkHonest F Lift logw 0 where
  sum ℓ ly st b a bnd := c.honestSum pub hwf hone (wOf ℓ) ly st (sched ly b) a bnd
  poly ℓ ly st b a bnd := c.honestPoly pub hwf hone (wOf ℓ) ly st (sched ly b) a bnd
  deg_le ℓ ly st _ a bnd := QuadCircuit.honest_deg_le pub hwf hone (wOf ℓ) ly st _ a bnd
  sum_eq ℓ ly st _ a bnd := QuadCircuit.honest_sum_eq pub hwf hone (wOf ℓ) ly st _ a bnd
  next_eq ℓ ly st _ a bnd r := QuadCircuit.honest_next_eq pub hwf hone (wOf ℓ) ly st _ a bnd r
  Pend := Pend

/-- **The construction's honest pair** at a layer's two points, at the layer's `beta = b`. -/
noncomputable def zkW (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw) (hone : c.OneWire pub)
    {Lift : Type} (wOf : Lift → Fin c.ninp → F) (ℓ : Lift) (ly : ℕ) (st : LayerState logw 0 F)
    (b : F) : F × F :=
  ((c.toLayered pub hwf hone).V ly (wOf ℓ) (sched ly b) st.g0 st.q,
    (c.toLayered pub hwf hone).V ly (wOf ℓ) (sched ly b) st.g1 st.q)

/-- **`ZkBoundary.rel`** for the construction. -/
theorem zkW_rel [SumcheckInterp F] (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) {Lift : Type} (wOf : Lift → Fin c.ninp → F)
    (Pend : Lift → ℕ → List F → Prop) (ℓ : Lift) (ly : ℕ) (st : LayerState logw 0 F) (b a : F) :
    (zkHonestOf pub hwf hone wOf Pend).sum ℓ ly st b a []
      = (zkW pub hwf hone wOf ℓ ly st b).1 + a * (zkW pub hwf hone wOf ℓ ly st b).2 :=
  QuadCircuit.honest_rel pub hwf hone (wOf ℓ) ly st (sched ly b) a

/-- **`ZkBoundary.W_affine`** for the construction. -/
theorem zkW_affine (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw) (hone : c.OneWire pub)
    {Lift : Type} (wOf : Lift → Fin c.ninp → F) (ℓ : Lift) (ly : ℕ) (st : LayerState logw 0 F)
    (b : F) :
    (zkW pub hwf hone wOf ℓ ly st b).1 = (zkW pub hwf hone wOf ℓ ly st 0).1
        + b * ((zkW pub hwf hone wOf ℓ ly st 1).1 - (zkW pub hwf hone wOf ℓ ly st 0).1) ∧
      (zkW pub hwf hone wOf ℓ ly st b).2 = (zkW pub hwf hone wOf ℓ ly st 0).2
        + b * ((zkW pub hwf hone wOf ℓ ly st 1).2 - (zkW pub hwf hone wOf ℓ ly st 0).2) :=
  ⟨QuadCircuit.toLayered_V_affine pub hwf hone ly (wOf ℓ) (fun _ => 0) b st.g0 st.q,
    QuadCircuit.toLayered_V_affine pub hwf hone ly (wOf ℓ) (fun _ => 0) b st.g1 st.q⟩

/-! ## Layer 0 -/

/-- **The output extension** at layer 0's `beta = b` and output point `G`. -/
noncomputable def outExt (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw) (hone : c.OneWire pub)
    (priv : Fin c.ninp → F) (b : F) (G : Fin logw → F) : F :=
  (c.toLayered pub hwf hone).V 0 priv (sched 0 b) (Vector.ofFn G) 0

/-- The output extension is multilinear in the output point. -/
theorem outExt_mlin (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw) (hone : c.OneWire pub)
    (priv : Fin c.ninp → F) (b : F) : MLin (outExt pub hwf hone priv b) :=
  mle_mlin (c.wires pub priv (sched 0 b) 0)

/-- The output extension is affine in `beta₀`. -/
theorem outExt_affine (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw) (hone : c.OneWire pub)
    (priv : Fin c.ninp → F) (b : F) (G : Fin logw → F) :
    outExt pub hwf hone priv b G = outExt pub hwf hone priv 0 G
      + b * (outExt pub hwf hone priv 1 G - outExt pub hwf hone priv 0 G) :=
  QuadCircuit.toLayered_V_affine pub hwf hone 0 priv (fun _ => 0) b (Vector.ofFn G) 0

/--
**`hinit_of_output`'s `harith`, at `Satisfied`.**  If a witness does not satisfy the circuit but
every intermediate assertion vector vanishes, then `TopSat` fails (`satisfied_iff_top`, under
`Isolated`), so some output or layer-0 assertion wire is non-zero (`top_harith`, under `DeadEnd`),
and the output extension is non-zero at some `(beta₀, G)`: under `DeadEnd` layer 0's values read
the schedule only at `beta₀` (`toLayered_V_decomp`).
-/
theorem outExt_ne (pub : Fin c.ninp → F) (hwf : c.WellFormed nv logw) (hone : c.OneWire pub)
    (hiso : c.Isolated) (hde : c.DeadEnd) (hnl : 0 < c.nl) (priv : Fin c.ninp → F)
    (hns : ¬ c.Satisfied pub priv)
    (hint : ∀ ly, 0 < ly → ly < c.nl → ∀ j, c.assertVec pub priv ly j = 0) :
    ∃ (b : F) (G : Fin logw → F), outExt pub hwf hone priv b G ≠ 0 := by
  have htop : ¬ c.TopSat pub priv := fun ht =>
    hns ((QuadCircuit.satisfied_iff_top hiso hnl pub priv).mpr ⟨ht, hint⟩)
  obtain ⟨Xs, G, hG⟩ := QuadCircuit.top_harith pub hwf hone hde hnl priv htop
  refine ⟨Xs 0, G, ?_⟩
  unfold outExt
  rw [QuadCircuit.toLayered_V_decomp pub hwf hone hde hnl priv]
  simp only [sched, Function.update_self]
  rwa [QuadCircuit.toLayered_V_decomp pub hwf hone hde hnl priv] at hG

/-- **A pending predicate sees the assertion vectors**: a non-zero assertion vector at a gate layer
`j + 1` makes `Pend ℓ j []` (nothing bound yet in layer `j`'s sumcheck). -/
def SeesAsserts (pub : Fin c.ninp → F) {Lift : Type} (wOf : Lift → Fin c.ninp → F)
    (Pend : Lift → ℕ → List F → Prop) : Prop :=
  ∀ ℓ j, j + 1 < c.nl → (∃ i, c.assertVec pub (wOf ℓ) (j + 1) i ≠ 0) → Pend ℓ j []

/--
**`ZkFieldData.hinit`, discharged for the construction at `Sat := Satisfied`.**  For any code whose
`begin_circuit` state has both points at the output point (`hst0`) and any pending predicate that
sees the assertion vectors (`hsees`): an unsatisfied candidate with nothing pending vanishes at most
`(logw + 2)·|F|^(logw+1)` of the `|F|^(logw+2)` triples `(G, beta₀, alpha₀)`.
-/
theorem zk_hinit [SumcheckInterp F] {C X Q Msg : Type} {M ninp : ℕ} (pub : Fin c.ninp → F)
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (hiso : c.Isolated) (hde : c.DeadEnd)
    (hnl : 0 < c.nl) {Lift : Type} (wOf : Lift → Fin c.ninp → F)
    (Pend : Lift → ℕ → List F → Prop) (hsees : SeesAsserts pub wOf Pend)
    (V : ZkCode C F X Q Msg (Fin logw → F) M ninp logw 0)
    (hst0 : ∀ G, (V.st0 G).g0 = Vector.ofFn G ∧ (V.st0 G).g1 = Vector.ofFn G) :
    ∀ ℓ : Lift, ¬ c.Satisfied pub (wOf ℓ) →
      (∀ j, ¬ (zkHonestOf pub hwf hone wOf Pend).Pend ℓ j []) →
      (univ.filter fun p : (Fin logw → F) × F × F =>
        (zkHonestOf pub hwf hone wOf Pend).sum ℓ 0 (V.st0 p.1) p.2.1 p.2.2 [] = 0).card
        ≤ (logw + 2) * Fintype.card F ^ (logw + 1) := by
  refine hinit_of_output (V := V) (fun ℓ => outExt pub hwf hone (wOf ℓ)) ?_
    (fun ℓ b => outExt_mlin pub hwf hone (wOf ℓ) b)
    (fun ℓ b G => outExt_affine pub hwf hone (wOf ℓ) b G) ?_
  · intro ℓ G b a
    rw [zkW_rel pub hwf hone wOf Pend ℓ 0 (V.st0 G) b a]
    simp only [zkW, outExt, (hst0 G).1, (hst0 G).2]
    rfl
  · intro ℓ hns hnp
    refine outExt_ne pub hwf hone hiso hde hnl (wOf ℓ) hns fun ly hly hlt j => ?_
    by_contra hj
    obtain ⟨k, rfl⟩ : ∃ k, ly = k + 1 := ⟨ly - 1, by omega⟩
    exact hnp k (hsees ℓ k hlt ⟨j, hj⟩)

end Lfzk.ZkArithInit
