import LfzkV1.ResidualReplay125
import LfzkV1.ZkArithProfile
import LfzkV1.CertifiedV7

/-! Width bounds and concrete v7 verifier code for the symbolic replay. -/

open BigOperators MvPolynomial SumcheckV1
open LfzkV1.Arith LfzkV1.CertifiedV1 LfzkV1.RbrZkLongfellow
open LfzkV1.ZkArithProfile LfzkV1.ZkArithInit

set_option autoImplicit false

namespace LfzkV1.ResidualReplay125

/-- The deployed SHA profiles use at most 20 bits per hand. -/
def V7HashProfile (R : CertifiedV1.Row) : Prop :=
  R = v7Hash1 ∨ R = v7Hash2 ∨ R = v7Hash3 ∨ R = v7Hash4

theorem v7_hash_width {R : CertifiedV1.Row} (hR : V7HashProfile R)
    (i : ℕ) (hi : i < R.params.nl) : R.params.logw i ≤ 20 := by
  have h (R : CertifiedV1.Row) (ht : ∀ j : Fin R.params.nl, R.params.logw j.val ≤ 20) :
      ∀ j < R.params.nl, R.params.logw j ≤ 20 := fun j hj => ht ⟨j, hj⟩
  rcases hR with rfl | rfl | rfl | rfl
  · exact h v7Hash1 (by decide +kernel) i hi
  · exact h v7Hash2 (by decide +kernel) i hi
  · exact h v7Hash3 (by decide +kernel) i hi
  · exact h v7Hash4 (by decide +kernel) i hi

theorem v7_hash_rounds {R : CertifiedV1.Row} (hR : V7HashProfile R)
    (i : ℕ) (hi : i < R.params.nl) : R.params.rounds i ≤ 40 := by
  have := v7_hash_width hR i hi
  unfold CostV1.Params.rounds
  omega

theorem v7_hash_gate_width {R : CertifiedV1.Row} (hR : V7HashProfile R)
    (i : ℕ) (hi : i ≤ R.params.nl) : ow 5 R.params.logw i ≤ 20 := by
  cases i with
  | zero => change 5 ≤ 20; decide
  | succ i => exact v7_hash_width hR i (by omega)

variable {σ : Type*} {F : Type} [Field F]

/-- The symbolic left/right point reads every other round exactly as the verifier does. -/
noncomputable def hand {L : ℕ} (bnd : List (Poly σ F)) (s : Fin 2) (j : Fin L) : Poly σ F :=
  bnd.getD (2 * j.val + s.val) 0

theorem eval_hand_left {L : ℕ} (x : σ → F) (bnd : List (Poly σ F)) :
    (Vector.ofFn fun j : Fin L => eval x (hand bnd 0 j)) =
      evenPt L (ptOf (bnd.map (eval x))) := by
  unfold evenPt ptOf hand
  congr 1
  funext j
  change eval x (bnd.getD (2 * j.val) 0) = (bnd.map (eval x)).getD (2 * j.val) 0
  simpa only [map_zero] using (List.getD_map bnd (0 : Poly σ F) (eval x)).symm

theorem eval_hand_right {L : ℕ} (x : σ → F) (bnd : List (Poly σ F)) :
    (Vector.ofFn fun j : Fin L => eval x (hand bnd 1 j)) =
      oddPt L (ptOf (bnd.map (eval x))) := by
  unfold oddPt ptOf hand
  congr 1
  funext j
  change eval x (bnd.getD (2 * j.val + 1) 0) = (bnd.map (eval x)).getD (2 * j.val + 1) 0
  simpa only [map_zero] using (List.getD_map bnd (0 : Poly σ F) (eval x)).symm

theorem degree_hand {L width : ℕ} {bnd : List (Poly σ F)}
    (hcount : bnd.length = 2 * width) (hdeg : ∀ p ∈ bnd, p.totalDegree ≤ 1)
    (s : Fin 2) (j : Fin L) :
    (hand bnd s j).totalDegree ≤ if j.val < width then 1 else 0 := by
  by_cases hj : j.val < width
  · have h : 2 * j.val + s.val < bnd.length := by have := s.isLt; omega
    rw [if_pos hj, hand, List.getD_eq_getElem _ _ h]
    exact hdeg _ (List.getElem_mem h)
  · have h : bnd.length ≤ 2 * j.val + s.val := by omega
    rw [if_neg hj, hand, List.getD_eq_default _ _ h]
    simp

/-- The symbolic common output point of the first layer. -/
noncomputable def initial {logv L : ℕ} (G : Fin logv → Poly σ F) (j : Fin L) : Poly σ F :=
  if h : j.val < logv then G ⟨j.val, h⟩ else 0

theorem eval_initial {logv L : ℕ} (x : σ → F) (G : Fin logv → Poly σ F) :
    (Vector.ofFn fun j : Fin L => eval x (initial G j)) = padG L (fun k => eval x (G k)) := by
  unfold padG initial
  congr 1
  funext j
  split_ifs <;> simp

theorem degree_initial {logv L : ℕ} {G : Fin logv → Poly σ F}
    (hd : ∀ j, (G j).totalDegree ≤ 1) (j : Fin L) :
    (initial G j).totalDegree ≤ if j.val < logv then 1 else 0 := by
  unfold initial
  split_ifs
  · exact hd _
  · simp

/-- Fix a transmitted round message and leave its ordinary challenge symbolic. -/
def replayRound {M : ℕ} (msg : ZkRoundMsg M F) (r : Poly σ F) : Round σ F M :=
  ⟨msg.tr0, msg.tr2, msg.pp0, msg.pp2, r⟩

theorem eval_replayRound {M : ℕ} (x : σ → F) (msg : ZkRoundMsg M F) (r : Poly σ F) :
    (replayRound msg r).eval x = roundData msg (eval x r) := rfl

section ProfileCode

variable [DecidableEq F]
variable {L M : ℕ} {C₀ X₀ Q Msg Gpt : Type} {c : QuadCircuit F}
variable {pub : Fin c.ninp → F}
variable {V : ZkCode C₀ F X₀ Q Msg Gpt M c.ninp L 0}
variable (hV : CodeAgreesP c pub L V)

include hV in
/-- A symbolic sparse gate coefficient agrees with the verifier whenever its gate points agree. -/
theorem eval_wiring_of_code (x : σ → F) {i : ℕ} (hi : i < c.nl)
    (st : LayerState L 0 F) (β α : Poly σ F) (bnd : List (Poly σ F))
    (g0 g1 : Fin L → Poly σ F)
    (hg0 : (Vector.ofFn fun j => eval x (g0 j)) = st.g0)
    (hg1 : (Vector.ofFn fun j => eval x (g1 j)) = st.g1) :
    eval x (wiring (c.gates i) β α g0 g1 (hand bnd 0) (hand bnd 1)) =
      V.eqqOf i st (eval x β) (eval x α) (bnd.map (eval x)) := by
  rw [hV.heqq i hi, eval_wiring, hg0, hg1, eval_hand_left, eval_hand_right]

/-- Compile the final verifier row from the last round challenges and the input-fold scalar. -/
noncomputable def profiledInput (c : QuadCircuit F) (pub : Fin c.ninp → F)
    (bnd : List (Poly σ F)) (α : Poly σ F) (cm : ZkCloseMsg M F) (L : ℕ) :
    Row σ F c.ninp M :=
  let b := fun i : Fin c.ninp => inCoefficient α (hand (L := L) bnd 0) (hand bnd 1) i.val
  Row.input c.npub b (∑ i ∈ Finset.univ \ privIdx c.ninp c.npub, b i * C (pub i))
    cm.wc0 cm.wc1 α cm.dwL cm.dwR

include hV in
theorem eval_profiledInput (x : σ → F) (bnd : List (Poly σ F)) (α : Poly σ F)
    (cm : ZkCloseMsg M F) :
    (profiledInput c pub bnd α cm L).eval x =
      inputRow V.npub (V.inCoeffs (bnd.map (eval x)) (eval x α))
        (V.pubBinding (bnd.map (eval x)) (eval x α)) (cm.wc0 + eval x α * cm.wc1)
        (eval x α) cm.dwL cm.dwR := by
  rw [hV.hnpub, hV.hpubB, profiledInput, Row.eval_input]
  have h (i : Fin c.ninp) :
      eval x (inCoefficient α (hand (L := L) bnd 0) (hand bnd 1) i.val) =
        V.inCoeffs (bnd.map (eval x)) (eval x α) i := by
    rw [hV.hinC, eval_inCoefficient, eval_hand_left, eval_hand_right]
  rw [funext h]
  simp only [map_sum, map_mul, eval_C, eval_inCoefficient, eval_hand_left, eval_hand_right]

omit [DecidableEq F] in
theorem degree_profiledInput (c : QuadCircuit F) (pub : Fin c.ninp → F)
    {bnd : List (Poly σ F)} {α : Poly σ F} (cm : ZkCloseMsg M F) (L width : ℕ)
    (hcount : bnd.length = 2 * width) (hdeg : ∀ p ∈ bnd, p.totalDegree ≤ 1)
    (hα : α.totalDegree ≤ 1) : (profiledInput c pub bnd α cm L).Bounded (1 + width) := by
  unfold profiledInput
  have h (i : Fin c.ninp) :=
    degree_inCoefficient hα (L := L) (degree_hand hcount hdeg 0) (degree_hand hcount hdeg 1) i.val
  exact Row.input_bounded c.npub h
    (totalDegree_finsetSum_le fun i _ => degree_scale _ (h i))
    cm.wc0 cm.wc1 (hα.trans (by omega)) cm.dwL cm.dwR

/-- The layer emitted by the public sparse circuit at a replayed proof layer. -/
noncomputable def profiledLayer (c : QuadCircuit F) (i : ℕ)
    (g0 g1 : Fin L → Poly σ F) (β α : Poly σ F)
    (start : Expression σ F M) (rs : List (Round σ F M)) (cm : ZkCloseMsg M F) :
    Layer σ F M :=
  let bnd := rs.map Round.challenge
  ⟨start, rs, wiring (c.gates i) β α g0 g1 (hand bnd 0) (hand bnd 1),
    cm.wc0, cm.wc1, cm.dwL, cm.dwR, cm.dwLR⟩

include hV in
/-- Every layer close uses the polynomial coefficients of the real `closeRow`. The state
invariants are the builder run and the even/odd challenge list, already tracked by the verifier. -/
theorem eval_profiledLayer [SumcheckV1Interp F] (x : σ → F)
    (zs : ZkRunning M L 0 F) (hi : zs.layer < c.nl)
    (g0 g1 : Fin L → Poly σ F) (β α : Poly σ F)
    (start : Expression σ F M) (rs : List (Round σ F M)) (cm : ZkCloseMsg M F)
    (hg0 : (Vector.ofFn fun j => eval x (g0 j)) = zs.st.g0)
    (hg1 : (Vector.ofFn fun j => eval x (g1 j)) = zs.st.g1)
    (hβ : eval x β = zs.beta) (hα : eval x α = zs.alpha)
    (hbound : (rs.map fun r => eval x r.challenge) = zs.bound)
    (hexpr : builder_run (start.eval x) (rs.map (Round.eval x)) = zs.e) :
    (profiledLayer c zs.layer g0 g1 β α start rs cm).data x = closeRow V zs cm := by
  have hq := eval_wiring_of_code hV x hi zs.st β α (rs.map Round.challenge) g0 g1 hg0 hg1
  simp only [List.map_map, Function.comp_def, hbound, hβ, hα] at hq
  simp [profiledLayer, Layer.data, closeRow, hexpr, hq]

theorem profiledLayer_bounded81 [SumcheckV1Interp F] (c : QuadCircuit F) (i : ℕ)
    {g0 g1 : Fin L → Poly σ F} {β α : Poly σ F}
    {start : Expression σ F M} {rs : List (Round σ F M)}
    (cm : ZkCloseMsg M F) {gw hw : ℕ} (hgw : gw ≤ 20) (hhw : hw ≤ 20)
    (hβ : β.totalDegree ≤ 1) (hα : α.totalDegree ≤ 1)
    (hg0 : ∀ j, (g0 j).totalDegree ≤ if j.val < gw then 1 else 0)
    (hg1 : ∀ j, (g1 j).totalDegree ≤ if j.val < gw then 1 else 0)
    (he : start.Bounded 1) (hr : rs.length = 2 * hw)
    (hrdeg : ∀ r ∈ rs, r.challenge.totalDegree ≤ 1) :
    ((profiledLayer c i g0 g1 β α start rs cm).row (ninp := c.ninp)).Bounded 81 := by
  apply Layer.row_bounded81 _ he (by simpa [profiledLayer, hr] using (show 2 * hw ≤ 40 by omega))
    hrdeg
  have hc : (rs.map Round.challenge).length = 2 * hw := by simpa using hr
  have hd : ∀ p ∈ rs.map Round.challenge, p.totalDegree ≤ 1 := by
    intro p hp
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hp
    exact hrdeg r hr'
  exact (degree_wiring (c.gates i) hβ hα hg0 hg1 (degree_hand hc hd 0) (degree_hand hc hd 1)).trans
    (by omega)

end ProfileCode

end LfzkV1.ResidualReplay125
