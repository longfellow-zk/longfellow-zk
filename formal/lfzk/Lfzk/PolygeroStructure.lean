import Lfzk.Encode
import Lfzk.ZkSim
import Lfzk.ZkArithProfile

/-!
# What the LFZK terminal row format does and does not exclude

The rows emitted by LFZK have considerably more structure than an arbitrary
linear constraint system: each layer row touches only the pad, there is one
input row, and there are product triples with copy equations in the encoded
tableau.  Those syntactic properties do not force all invalid candidates to
have the same arithmetic exception hyperplane.

This file supplies an actual false quadratic-format circuit and a
circuit-agreeing verifier whose reachable field prefix remains doomed for
every candidate.  The affine candidates satisfy every product triple and
every standard encoded copy equation, but their two linear residuals are
`(-(1+alpha)*a, 1-a)`.  Unless the initial fold is its one cancellation
value, different candidates have distinct arithmetic exception lines,
including in characteristic two.

This proves the circuit-format and field-prefix bridge.  It does not
construct the multi-region Reed--Solomon oracle, the lift-list membership,
or the full 81/80-opening grinding prover at this encoded terminal system.
The terminal system can have satisfying pads outside this family; the
proved invariant is the LFZK seam's candidate-relative `NoSat` invariant.
It also makes no claim about the particular registered SHA/ECDSA circuits.
The existing complete 116-bit LFZK soundness bound is unaffected.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.PolygeroStructure

open Finset
open scoped BigOperators

variable {F : Type} [Field F]

/-- The residual of one actual LFZK linear row. -/
noncomputable def rowResidual {ninp M : ℕ} (row : LigeroRow ninp M F)
    (wcol : Fin ninp → F) (pad : Fin M → F) : F :=
  (∑ i, row.cw i * wcol i) + (∑ j, row.cp j * pad j) - row.rhs

/-- The standard encoding preserves a genuine LFZK row's residual exactly,
as well as preserving its zero set. -/
theorem encoded_row_residual {ninp M w nw nq nt nlin : ℕ}
    (pl : Encode.Placement ninp M w nw nq nt) (sys : LigeroSystem ninp M F)
    (wit : Fin ninp → F) (pad : Fin M → F) (i : Fin nlin) :
    (Encode.encodeLig pl nlin sys).linearValue (Encode.embedLig pl sys wit pad) (.inl i) -
        (Encode.encodeLig pl nlin sys).target (.inl i) =
      rowResidual (Encode.presentLin nlin sys i) wit pad := by
  change (∑ b : LigeroFamily.CoreBlock,
    ∑ r : Fin (b.rowCount nw nq), ∑ c : Fin w,
      Encode.rowCoeff pl (Encode.presentLin nlin sys i) b r c *
        Encode.embedLig pl sys wit pad b r c) - _ = _
  rw [Encode.linearValue_rowCoeff]
  unfold Encode.embedLig
  rw [Encode.decodeVec_embed]
  rfl

/-- Different candidates have the same exceptional weight pair only at
the origin.  This is the geometry needed by the multi-region obstruction. -/
theorem exception_lines_intersect_only_zero (a b u v : F) (hab : a ≠ b)
    (ha : u * a + v * (1 - a) = 0)
    (hb : u * b + v * (1 - b) = 0) :
    u = 0 ∧ v = 0 := by
  have h : (a - b) * (u - v) = 0 := by linear_combination ha - hb
  have huv : u - v = 0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hab)
  have hv : v = 0 := by linear_combination ha - a * huv
  constructor
  · simpa [hv] using huv
  · exact hv

end Lfzk.PolygeroStructure

namespace Lfzk.PolygeroStructure.Circuit

open Sumcheck Lfzk.Arith Lfzk.ZkArithInit Lfzk.ZkArithProfile Lfzk.RbrZkLongfellow

variable {F : Type} [Field F]

/-- An actual quadratic-format circuit whose output is the public constant
`1 * 1`.  Its output must be zero, so its public instance is false. -/
def falseCircuit : QuadCircuit F := ⟨[[⟨0, 0, 0, 1⟩]], 1, 1⟩

def publicInput : Fin (falseCircuit (F := F)).ninp → F := fun _ => 1

theorem wellFormed : WellFormedP (falseCircuit (F := F)) 0 (fun _ => 0) 0 := by
  refine ⟨by simp [falseCircuit, QuadCircuit.nl], by simp, by simp, by simp [falseCircuit], ?_⟩
  intro ly hly t ht
  have h : ly = 0 := by simpa [falseCircuit, QuadCircuit.nl] using hly
  subst ly
  simp [falseCircuit, QuadCircuit.gates] at ht
  subst t
  simp [ow]

theorem deadEnd : (falseCircuit (F := F)).DeadEnd := by
  intro ly hly t ht
  have h : ly = 0 := by simpa [falseCircuit, QuadCircuit.nl] using hly
  subst ly
  simp [falseCircuit, QuadCircuit.gates] at ht
  subst t
  simp [QuadCircuit.AssertWire, falseCircuit, QuadCircuit.gates]

theorem isolated : (falseCircuit (F := F)).Isolated := by
  intro ly hly i k hv _
  have h : ly = 0 := by simpa [falseCircuit, QuadCircuit.nl] using hly
  subst ly
  apply Fin.ext
  have hi : i.val < 1 := i.isLt
  have hk : k.val < 1 := k.isLt
  omega

theorem false_for_every_witness [DecidableEq F]
    (w : Fin (falseCircuit (F := F)).ninp → F) :
    ¬ (falseCircuit (F := F)).Satisfied publicInput w := by
  intro hs
  have h := hs.2 0
  have hlt : 0 < (falseCircuit (F := F)).nl := by simp [falseCircuit, QuadCircuit.nl]
  have hge : (falseCircuit (F := F)).nl ≤ 1 := by simp [falseCircuit, QuadCircuit.nl]
  simp only [QuadCircuit.honest, QuadCircuit.wires_lt hlt,
    QuadCircuit.wires_ge hge] at h
  simp [QuadCircuit.evalGates_eq_list, falseCircuit, QuadCircuit.gates,
    QuadCircuit.inputVec, publicInput, wCol, prepV] at h

/-- The actual close message uses three different pad indices. -/
def closeMessage : ZkCloseMsg 3 F := ⟨0, 0, 0, 1, 2⟩

/-- A circuit-agreeing verifier at this zero-width profile.  The first coin
coordinate is the beta/field decoder; the second is the layer fold alpha. -/
noncomputable def code : ZkCode (F × F) F Unit Unit Unit (Fin 0 → F) 3 1 0 0 where
  st0 _ := ⟨0, 0, #v[], #v[], #v[]⟩
  stNext _ _ _ := ⟨0, 0, #v[], #v[], #v[]⟩
  eqqOf _ _ _ a _ := 1 + a
  npub := 1
  inCoeffs _ a _ := 1 + a
  pubBinding _ a := 1 + a
  nlin := 2
  nt := 1
  roundOf _ := ⟨0, 0, 0, 1⟩
  closeOf _ := closeMessage
  decodeInit c := (Fin.elim0, c.1, c.2)
  decodePair c := c
  decodeF c := c.1
  decodeChal _ := ()
  decodeQuery _ := ()

theorem agrees [Fintype F] [DecidableEq F] :
    CodeAgreesP (falseCircuit (F := F)) publicInput 0 code := by
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro bnd wc0 wc1
    constructor <;> ext i hi <;> omega
  · intro ly hly st b a bnd
    have h : ly = 0 := by simpa [falseCircuit, QuadCircuit.nl] using hly
    subst ly
    simp [code, bindGhAll, falseCircuit, QuadCircuit.gates, prepV,
      eq_mle_basis]
  · intro bnd a i
    simp [code, eq_mle_basis]
  · intro bnd a
    change 1 + a = ∑ i ∈ (Finset.univ \ privIdx 1 1 : Finset (Fin 1)),
      (eq_mle_basis i.val (evenPt 0 (ptOf bnd)) +
        a * eq_mle_basis i.val (oddPt 0 (ptOf bnd))) * 1
    simp [privIdx, eq_mle_basis]

/-- Exactly one alpha value cancels the initial honest claim.  Thus the
non-escape side condition holds on all but `1 / |F|` of the actual uniform
two-coordinate initialization answers. -/
theorem initialization_cancellation_card [Fintype F] [DecidableEq F] :
    (Finset.univ.filter fun c : F × F => 1 + c.2 = 0).card = Fintype.card F := by
  classical
  have he : (Finset.univ.filter fun c : F × F => 1 + c.2 = 0) =
      (Finset.univ : Finset F) ×ˢ {-1} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton]
    constructor
    · intro h
      linear_combination h
    · intro h
      rw [h]
      ring
  rw [he, Finset.card_product, Finset.card_univ, Finset.card_singleton, mul_one]

/-- The exact system reached from the initial state at the input binding;
there are zero sumcheck rounds at this well-formed circuit profile. -/
noncomputable def system (alpha alphaIn : F) : LigeroSystem 1 3 F :=
  buildSystem 1 (Expression.zero 3 F) (1 + alpha) 0 0
    (fun _ => 1 + alphaIn) (1 + alphaIn) alphaIn 0 1 2

/-- The actual arithmetization's honest oracle, with the (empty) assertion
pending predicate.  Every input is public in this circuit. -/
noncomputable def honest [Fintype F] [DecidableEq F] [SumcheckInterp F] :
    ZkHonest F F 0 0 :=
  zkHonestP wellFormed publicInput (fun _ : F => fun _ => 0) (fun _ _ _ => False)

theorem honest_init_sum [Fintype F] [DecidableEq F] [SumcheckInterp F]
    (a beta alpha : F) (st : LayerState 0 0 F) :
    honest.sum a 0 st beta alpha [] = 1 + alpha := by
  simp [honest, zkHonestP, partialSum, psum, lpoly, dimP, lpolyFn,
    falseCircuit, QuadCircuit.nl, QuadCircuit.gates, bindGhAll, prepV,
    eq_mle_basis, VP, mle, QuadCircuit.wires, QuadCircuit.inputVec,
    publicInput, wCol]

theorem actual_prefix_reaches (init input : F × F) :
    zkInputBind 1 (fun _ => 0) code closeMessage input
        (zkInit code init .start) = .built (system init.2 input.1) := by
  simp [zkInputBind, zkInit, code, closeMessage, Fits, inputSystem, closeRow,
    system, buildSystem, buildSystemMulti]

/-- Every scalar labels a product-consistent candidate.  In particular,
the presence of an actual product triple does not limit the family to two
scalars: its right factor is the shared constant one. -/
def pad (a : F) : Fin 3 → F := ![a, 1, a]

theorem product (alpha alphaIn a : F) :
    ∀ t ∈ (system alpha alphaIn).quad,
      pad a t.2.2 = pad a t.1 * pad a t.2.1 := by
  intro t ht
  simp only [system, buildSystem, List.mem_singleton] at ht
  subst t
  simp [pad]

theorem layer_residual (alpha a : F) (w : Fin 1 → F) :
    rowResidual (layerRow 1 (Expression.zero 3 F) (1 + alpha) 0 0 0 1 2)
      w (pad a) = -(1 + alpha) * a := by
  simp [rowResidual, layerRow, builder_finalize, Expression.zero, pad]

theorem input_residual (alphaIn a : F) (w : Fin 1 → F) :
    rowResidual (inputRow (M := 3) 1 (fun _ => 1 + alphaIn)
      (1 + alphaIn) 0 alphaIn 0 1) w (pad a) = 1 - a := by
  simp [rowResidual, inputRow, pad, Fin.sum_univ_succ]
  ring

theorem encoded_residuals {w nw nq : ℕ}
    (pl : Encode.Placement 1 3 w nw nq 1) (alpha alphaIn a : F)
    (wit : Fin 1 → F) (i : Fin 2) :
    (Encode.encodeLig pl 2 (system alpha alphaIn)).linearValue
          (Encode.embedLig pl (system alpha alphaIn) wit (pad a)) (.inl i) -
        (Encode.encodeLig pl 2 (system alpha alphaIn)).target (.inl i) =
      if i = 0 then -(1 + alpha) * a else 1 - a := by
  rw [encoded_row_residual]
  fin_cases i
  · simpa [Encode.presentLin, system, buildSystem] using layer_residual alpha a wit
  · simpa [Encode.presentLin, system, buildSystem] using input_residual alphaIn a wit

/-- Every candidate is still doomed at the terminal seam whenever the
initial layer fold avoids its single honest-cancellation value. -/
theorem no_candidate_satisfies (alpha alphaIn a : F) (ha : 1 + alpha ≠ 0)
    (w : Fin 1 → F) : ¬ (system alpha alphaIn).Sat w (pad a) := by
  rintro ⟨hlin, _⟩
  have hl := hlin (layerRow 1 (Expression.zero 3 F) (1 + alpha) 0 0 0 1 2)
    (by simp [system, buildSystem])
  have hi := hlin (inputRow (M := 3) 1 (fun _ => 1 + alphaIn)
    (1 + alphaIn) 0 alphaIn 0 1) (by simp [system, buildSystem])
  have hl' : rowResidual (layerRow 1 (Expression.zero 3 F) (1 + alpha) 0 0 0 1 2)
      w (pad a) = 0 := sub_eq_zero.mpr hl
  have hi' : rowResidual (inputRow (M := 3) 1 (fun _ => 1 + alphaIn)
      (1 + alphaIn) 0 alphaIn 0 1) w (pad a) = 0 := sub_eq_zero.mpr hi
  rw [layer_residual] at hl'
  have hz : a = 0 := (mul_eq_zero.mp hl').resolve_left (neg_ne_zero.mpr ha)
  rw [input_residual, hz] at hi'
  simp at hi'

/-- This is not merely an arbitrary terminal system: each real candidate
is doomed at the start, after the actual initialization, and after the
actual input binding.  The reachable prefix does not use a field escape
when `1 + alpha_init` is nonzero. -/
theorem prefix_stays_wrong [Fintype F] [DecidableEq F] [SumcheckInterp F]
    (init input : F × F) (hinit : 1 + init.2 ≠ 0) (a : F)
    (ligDoomed : LigeroSystem 1 3 F → Unit → Prop) :
    let asg := fun a : F => ((fun _ : Fin 1 => (0 : F)), pad a)
    let sat := fun _ : F => (falseCircuit (F := F)).Satisfied publicInput (fun _ => 0)
    ZkWrong code honest asg sat ligDoomed (some a) .start ∧
      ZkWrong code honest asg sat ligDoomed (some a) (zkInit code init .start) ∧
      ZkWrong code honest asg sat ligDoomed (some a)
        (zkInputBind 1 (fun _ => 0) code closeMessage input (zkInit code init .start)) := by
  dsimp only
  refine ⟨false_for_every_witness _, ?_, ?_⟩
  · change RowsBad _ [] ∨ _ ∨ _ ∨ _
    apply Or.inr
    apply Or.inl
    rw [honest_init_sum]
    simpa [zkInit, code, Expression.zero, evaluates_to] using hinit.symm
  · rw [actual_prefix_reaches]
    change Fits code (system init.2 input.1) ∧ _
    exact ⟨by simp [Fits, code, system, buildSystem],
      no_candidate_satisfies init.2 input.1 a hinit _⟩

/-- The standard LFZK encoding preserves every product and copy equation
of these candidates.  Only the two genuine arithmetic rows have residuals.
The result is independent of how the LFZK pad is packed into the tableau. -/
theorem encoded_copy_and_product {w nw nq : ℕ}
    (pl : Encode.Placement 1 3 w nw nq 1) (alpha alphaIn a : F)
    (wit : Fin 1 → F) :
    (∀ j : Fin 1, ∀ side : Encode.QSide,
      (Encode.encodeLig pl 2 (system alpha alphaIn)).linearValue
          (Encode.embedLig pl (system alpha alphaIn) wit (pad a)) (.inr (j, side)) =
        (Encode.encodeLig pl 2 (system alpha alphaIn)).target (.inr (j, side))) ∧
      (∀ r c,
        Encode.embedLig pl (system alpha alphaIn) wit (pad a) .left r c *
            Encode.embedLig pl (system alpha alphaIn) wit (pad a) .right r c =
          Encode.embedLig pl (system alpha alphaIn) wit (pad a) .output r c) := by
  let Z : LigeroSystem 1 3 F := ⟨[], (system alpha alphaIn).quad⟩
  have hz : Z.Sat wit (pad a) := ⟨by simp [Z], product alpha alphaIn a⟩
  have he := Encode.satisfies_encodeLig pl 0 Z wit (pad a) hz
  constructor
  · intro j side
    exact he.1 (.inr (j, side))
  · exact he.2

/-- The reachable false circuit has genuinely different exception lines
for different candidates, including in characteristic two. -/
theorem distinct_exception_lines (alpha a b u v : F) (halpha : 1 + alpha ≠ 0)
    (hab : a ≠ b)
    (ha : u * (-(1 + alpha) * a) + v * (1 - a) = 0)
    (hb : u * (-(1 + alpha) * b) + v * (1 - b) = 0) :
    u = 0 ∧ v = 0 := by
  have ha' : (u * -(1 + alpha)) * a + v * (1 - a) = 0 := by
    simpa only [mul_assoc] using ha
  have hb' : (u * -(1 + alpha)) * b + v * (1 - b) = 0 := by
    simpa only [mul_assoc] using hb
  obtain ⟨hu, hv⟩ := exception_lines_intersect_only_zero a b _ v hab ha' hb'
  exact ⟨(mul_eq_zero.mp hu).resolve_right (neg_ne_zero.mpr halpha), hv⟩

end Lfzk.PolygeroStructure.Circuit
