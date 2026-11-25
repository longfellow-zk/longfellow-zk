import LfzkV1.SignatureBudget125
import LfzkV1.MacCharge125
import LfzkV1.LigeroOrder125
import LfzkV1.HashOpening125
import Bcs.PotentialGrinding

/-!
# Direct two-field coverage at a fixed Merkle tape

The transcript's key annotation is the decoded MAC share. Its raw ideal
answer is still an element of the common expanded alphabet. Signature
public data is read from signature points, so it need not enlarge any
earlier hash point. This module counts the signature and MAC charges and
states the terminal hash classifications.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace LfzkV1.TwoFieldCover125

open Bcs Bcs.TotalOracleCommit Bcs.TotalOracle Finset Merkle.MH
  Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open LfzkV1.CompiledZk LfzkV1.CertifiedV1 LfzkV1.SoundnessAudit
open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.CompiledLongfellowAdaptive (Sig slice1 slice2)
open LfzkV1.NizkDeployedHash LfzkV1.NizkDeployedHashTwoField LfzkV1.NizkGrinding
open LfzkV1.NizkAdaptiveTwoField (SideCtx)
open LfzkV1.NizkZk LfzkV1.RbrZkSplit LfzkV1.RbrZkFlat LfzkV1.NizkZkDeployedHash
open LfzkV1.TwoFieldV1Rows LfzkV1.MacSep
open scoped Classical

abbrev Cut (D Enc : Type) := (D × D) × List (Enc × D)

section Signature

variable {C K D Enc Early Public MsgH Msg : Type}
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [DecidableEq K] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
variable [DecidableEq Early] [Inhabited MsgH] [DecidableEq MsgH]
variable [Inhabited Msg] [DecidableEq Msg]
variable {F Witness Salt : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
variable [Inhabited Salt]
variable {M ninp nt nlin logw logc : ℕ} {hS : v7SigHahn.Valid}
variable {codec : Codec Salt (Col F v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
variable {dec : RoleDecoders codec}
variable {R : Row}

abbrev SignaturePoint (D K Early MsgH Msg : Type) (R : Row) :=
  MPoint (SideCtx D K Early × (Fin (Rounds.Role.length R.params.nl R.params.rounds) → MsgH))
    Msg v7SigHahn.params.nl v7SigHahn.params.rounds

local notation "Pt" => SignatureBudget125.PairPoint D K Early MsgH Msg R
local notation "SPoint" => SignaturePoint D K Early MsgH Msg R
local notation "SigSide" => CompiledZkSide v7SigHahn hS v7SigHahn_openings_pos 8
  C F Msg Witness M ninp nt nlin logw logc Public dec Prod.snd

/-- The prescribed budget on projected addresses with raw answers in `C`. -/
noncomputable def signatureRawBudget (p : Pt) : ℚ :=
  match p with
  | Sum.inr (Sum.inr q) => SignatureBudget125.roleBudget C q.role
  | _ => 0

theorem signature_raw_budget_replay_le {Out : Type}
    (rootH rootS : Out → D) (avOf : Out → K) (earlyOf : Out → Early)
    (msgH : Out → ℕ → MsgH) (msgS : Out → ℕ → Msg)
    (out : Out) :
    (∑ j : Fin (1 + Rounds.Role.length R.params.nl R.params.rounds +
        Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds),
      signatureRawBudget (C := C) (hash2 rootH rootS avOf earlyOf msgH msgS out j.val : Pt)) ≤
      (Fintype.card C : ℚ) * ((1426 : ℚ) / (1000 * 2^128)) := by
  rw [sum_hash2]
  simp only [signatureRawBudget, Finset.sum_const_zero, zero_add]
  have hr (i : Fin (Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds)) :
      (msgPoint (ctxOf rootH rootS avOf earlyOf out, fun j => msgH out j.val) msgS out i.val
        : SPoint).role = Rounds.Role.indexEquiv.symm i := roleAt_val i
  simpa only [hr] using SignatureBudget125.roleBudget_sum_le C

theorem signature_raw_budget_observed_le (p : Pt) :
    signatureRawBudget (C := C) p ≤ (Fintype.card C : ℚ) * ((1426 : ℚ) / (1000 * 2^128)) := by
  rcases p with p | p | p
  · change 0 ≤ _
    positivity
  · change 0 ≤ _
    positivity
  · exact SignatureBudget125.roleBudget_le C p.role

end Signature

section CutStability

variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [DecidableEq D] [Inhabited D]
variable [DecidableEq Pt] [DecidableEq Key] {tA N L TM : ℕ}

theorem ctxAt_off_pair (S : Setup Enc D Pt C Out Key tA N L)
    (mt : Fin TM → D) (H H' : Pt → C) (x y : Pt) (hkey : S.key y = S.key x)
    (hoff : ∀ q, q ≠ x → q ≠ y → H q = H' q) :
    (S.atOracle H).ctxAt mt Setup.emptyTape (S.key x) =
      (S.atOracle H').ctxAt mt Setup.emptyTape (S.key x) := by
  let middle := Function.update H x (H' x)
  have hx : AgreeOff x H middle := agreeOff_update x H (H' x)
  have hy : AgreeOff y middle H' := by
    intro q hq
    by_cases h : q = x
    · subst q
      exact Function.update_self _ _ _
    · change Function.update H x (H' x) q = H' q
      rw [Function.update_of_ne h]
      exact hoff q h hq
  have hfirst := S.ctxAt_off mt H middle x hx
  have hsecond := S.ctxAt_off mt middle H' y hy
  rw [hkey] at hsecond
  exact hfirst.symm.trans hsecond.symm

end CutStability

section Terminal

open LigeroFamily CodingTheory LfzkV1.LigeroHighMass125 LfzkV1.LiftOpening125

private abbrev cert (i : Fin 4) := (OpeningGeometry125.result i).certificate

variable {F E : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
variable {w nw nq : ℕ} (i : Fin 4)
variable (code : MultiplicativeCode F (cert i).openings w (cert i).n)
variable (oracle : Ligero.V1.Oracle F nw nq (cert i).n 1)
variable (statement : ConstraintSystem F nw nq w E)
variable (challenge : SchemeChallenge F NoMask nw nq 1 E)
variable (response : Response F (cert i).openings w (cert i).n 1)
variable (query : QuerySet (cert i).n (cert i).openings)

local notation "Lift" => SchemeLiftCandidate code oracle (HashCut125.radius i)

/-- An accepted hash terminal transcript either incurs a direct charge or
determines one satisfying lift compatible with the opened columns. -/
theorem hash_terminal_cover
    (hmin : HasMinimumDistanceAtLeast code.baseCode (cert i).d)
    (hacc : SchemeVerifier.Accepts code Ligero.V1.scheme statement challenge response query
      (openSchemeOracle oracle query)) :
    LigeroOrder125.lowEvent i code (oracle, statement) response challenge query ∨
      LigeroOrder125.badHighEvent i code (oracle, statement) response challenge query ∨
      (∃ x y : Lift, x ≠ y ∧ Compatible x query (cert i).g ∧ Compatible y query (cert i).g) ∨
      ∃ x : Lift, statement.Satisfies x.decodedMessages ∧ Compatible x query (cert i).g ∧
        response ∈ liftedResponses statement x (highCutoff i) (cert i).g challenge ∧
        ∀ y : Lift, Compatible y query (cert i).g → x = y := by
  by_cases hl : (columns (C := code) oracle statement challenge response).card < highCutoff i
  · exact Or.inl ⟨hl, hacc⟩
  right
  by_cases hb : response ∈ badHighResponses (C := code) oracle statement (highCutoff i)
      (cert i).e (cert i).g challenge
  · exact Or.inl ⟨hb, hacc⟩
  right
  by_cases ha : ∃ x y : Lift, x ≠ y ∧ Compatible x query (cert i).g ∧ Compatible y query (cert i).g
  · exact Or.inl ha
  exact Or.inr (HashOpening125.selected_lift_of_accepts i statement hmin hacc (Nat.le_of_not_gt hl) hb ha)

end Terminal

section Ledger

variable {D K X MsgH MsgS C Out P R : Type} {nlH nlS N : ℕ}
variable {wH wS : ℕ → ℕ}
variable [DecidableEq D] [DecidableEq K] [DecidableEq X]
variable [DecidableEq MsgH] [DecidableEq MsgS]
variable [Fintype D] [Fintype K] [Fintype X] [Fintype MsgH] [Fintype MsgS]
variable [Fintype C] [Nonempty C] [Fintype P] [Fintype R]
local notation "Point" => Pt2 D K X MsgH MsgS nlH nlS wH wS

inductive QueryRole where
  | key
  | signature
  | field
  | batch
  | opening
  deriving DecidableEq

def queryRole (p : Point) : QueryRole :=
  match p with
  | Sum.inl _ => .key
  | Sum.inr (Sum.inr _) => .signature
  | Sum.inr (Sum.inl q) =>
    match q.role with
    | .ligeroChallenge => .batch
    | .ligeroQuery => .opening
    | _ => .field

/-- A role counts only actual distinct observed points at the common search. -/
noncomputable def observedRole (tree : Tree Point C Out N) (role : QueryRole)
    (H : Point → C) : Finset Point :=
  MacCharge125.observedKeys tree (fun q => queryRole q = role) H

/-- Every observed address, including addresses with invalid padding,
counts toward exactly one transcript role. -/
theorem observed_role_partition (tree : Tree Point C Out N) (H : Point → C) :
    (observedRole tree .opening H).card + (observedRole tree .batch H).card +
      (observedRole tree .field H).card + (observedRole tree .signature H).card +
      (observedRole tree .key H).card = (queried tree H).toFinset.card := by
  classical
  let seen := (queried tree H).toFinset
  have hcount (r : QueryRole) : (observedRole tree r H).card =
      ∑ p ∈ seen, if queryRole p = r then 1 else 0 := by
    have heq : observedRole tree r H = seen.filter (fun p => queryRole p = r) := by
      ext p
      simp only [observedRole, MacCharge125.observedKeys, seen, mem_filter]
    rw [heq, card_filter]
  simp_rw [hcount]
  simp only [← sum_add_distrib]
  rw [show seen.card = ∑ _p ∈ seen, (1 : ℕ) by simp]
  apply sum_congr rfl
  intro p _
  cases queryRole p <;> simp

theorem observed_role_partition_le (tree : Tree Point C Out N) (H : Point → C) :
    (observedRole tree .opening H).card + (observedRole tree .batch H).card +
      (observedRole tree .field H).card + (observedRole tree .signature H).card +
      (observedRole tree .key H).card ≤ N := by
  rw [observed_role_partition]
  exact (List.toFinset_card_le _).trans (queried_length_le tree H)

/-- Injectively represented labels fit within the corresponding observed role. -/
theorem observed_image_count_le {Labels : Type} [Fintype Labels]
    (tree : Tree Point C Out N) (H : Point → C) (labels : Labels → Point)
    (hlabels : Function.Injective labels) (role : QueryRole) (hrole : ∀ i, queryRole (labels i) = role)
    (seenLabels : Finset Labels) (hseen : ∀ i ∈ seenLabels, labels i ∈ queried tree H) :
    (seenLabels.card : ℚ) ≤ (observedRole tree role H).card := by
  classical
  have hc : (seenLabels.image labels).card = seenLabels.card := card_image_of_injective _ hlabels
  have hsub : seenLabels.image labels ⊆ observedRole tree role H := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    simp only [observedRole, MacCharge125.observedKeys, mem_filter, List.mem_toFinset]
    exact ⟨hseen i hi, hrole i⟩
  have hle := card_le_card hsub
  rw [hc] at hle
  exact_mod_cast hle

theorem batch_count_le_observed (tree : Tree Point C Out N) (H : Point → C)
    (batch : P → Point) (hb : Function.Injective batch)
    (hbRole : ∀ p, queryRole (batch p) = .batch) :
    LigeroOrder125.batchCount tree batch H ≤ (observedRole tree .batch H).card := by
  rw [LigeroOrder125.batchCount_eq]
  apply observed_image_count_le tree H batch hb .batch hbRole
  intro i hi
  simpa only [mem_filter, mem_univ, true_and] using hi

theorem opening_counts_le_observed (tree : Tree Point C Out N) (H : Point → C)
    (batch : P → Point) (opening : P → R → Point)
    (ho : Function.Injective (fun i : P × R => opening i.1 i.2))
    (hoRole : ∀ p r, queryRole (opening p r) = .opening) :
    LigeroOrder125.earlyCount tree batch opening H + LigeroOrder125.lateCount tree batch opening H ≤
      (observedRole tree .opening H).card := by
  rw [LigeroOrder125.openingCounts_eq]
  apply observed_image_count_le tree H (fun i : P × R => opening i.1 i.2) ho .opening
    (fun i => hoRole i.1 i.2)
  intro i hi
  simpa only [mem_filter, mem_univ, true_and] using hi

end Ledger


section SignatureCount

variable {C K D Enc Early Public MsgH Msg Out : Type}
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [DecidableEq K] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
variable [DecidableEq Early] [Inhabited MsgH] [DecidableEq MsgH]
variable [Inhabited Msg] [DecidableEq Msg]
variable [Fintype D] [Fintype K] [Fintype Early] [Fintype MsgH] [Fintype Msg]
variable {F Witness Salt : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
variable [Inhabited Salt]
variable {M ninp nt nlin logw logc : ℕ} {hS : v7SigHahn.Valid}
variable {codec : Codec Salt (Col F v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
variable {dec : RoleDecoders codec}
variable {R : Row} {tA N L TM : ℕ}

local notation "Pt" => SignatureBudget125.PairPoint D K Early MsgH Msg R
local notation "SPoint" => SignaturePoint D K Early MsgH Msg R
local notation "SigSide" => CompiledZkSide v7SigHahn hS v7SigHahn_openings_pos 8
  C F Msg Witness M ninp nt nlin logw logc Public dec Prod.snd

/-- Signature path payment at a fixed Merkle tape costs the expected
number of observed signature points and at most its full replay budget.
Only original signature points consume the shared query budget. -/
theorem signature_count_of_charge
    (S : Setup Enc D Pt C Out (D × D) tA N L)
    (charge : Cut D Enc → Pt → (Pt → C) → C → ℚ)
    (hcharge_nonneg : ∀ κ p H a, 0 ≤ charge κ p H a)
    (hcharge_local : ∀ κ p H, (∑ a : C, charge κ p H a) ≤ signatureRawBudget (C := C) p)
    (hcharge_off : ∀ κ p H H', AgreeOff p H H' → ∀ a, charge κ p H a = charge κ p H' a)
    (mt : Fin TM → D)
    (hinputs : ∀ out, Function.Injective (fun j : Fin L => S.hashInput out j.val))
    (hReplay : ∀ out,
      (∑ j : Fin L, signatureRawBudget (C := C) (S.hashInput out j.val)) ≤
        (Fintype.card C : ℚ) * ((1426 : ℚ) / (1000 * 2^128)))
    (event : (Pt → C) → Prop)
    (hpath : ∀ H, event H →
      1 ≤ ∑ j : Fin L, let p := S.hashInput (S.proof mt H) j.val
        charge (S.context mt H) p H (H p)) :
    ((univ.filter event).card : ℚ) ≤
      ((1426 : ℚ) / (1000 * 2^128)) * ∑ H : Pt → C,
        ((observedRole (S.search mt) .signature H).card + (1 : ℚ)) := by
  classical
  let G := S.grinding mt pts2 (fun _ _ _ _ => False) (fun _ => 0) (by simp)
  let ε : ℚ := 1426 / (1000 * 2^128)
  let q : ℚ := Fintype.card C
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := C)
  let wt (p : Pt) (H : Pt → C) (a : C) :=
    if G.Charged p H then charge (G.ctxAt H (G.key p)) p H a else 0
  let budget (p : Pt) := signatureRawBudget (C := C) p
  have hbudget_nonneg (p : Pt) : 0 ≤ budget p := by
    rcases p with p | p | p
    · exact le_rfl
    · exact le_rfl
    · exact SignatureBudget125.roleBudget_nonneg C p.role
  have hsig_only (p : Pt) : budget p = if queryRole p = .signature then budget p else 0 := by
    rcases p with p | p | p
    · rfl
    · change (0 : ℚ) = if queryRole (Sum.inr (Sum.inl p) : Pt) = .signature then 0 else 0
      split_ifs <;> rfl
    · simp only [queryRole, if_true]
  have hoff (p : Pt) (H H' : Pt → C) (h : AgreeOff p H H') (a : C) :
      wt p H a = wt p H' a := by
    unfold wt
    by_cases hp : G.Charged p H
    · rw [if_pos hp, if_pos (G.charged_off h hp), G.ctxAt_off H H' p h]
      exact hcharge_off _ p H H' h a
    · have hp' : ¬ G.Charged p H' := fun ht => hp (G.charged_off h.symm ht)
      rw [if_neg hp, if_neg hp']
  have hfiber (p : Pt) (H : Pt → C) :
      ∑ a : C, wt p H a ≤ if G.Charged p H then budget p else 0 := by
    by_cases hp : G.Charged p H
    · simpa only [wt, if_pos hp] using hcharge_local (G.ctxAt H (G.key p)) p H
    · simp only [wt, if_neg hp, sum_const_zero, le_refl]
  have hbudgets (H : Pt → C) :
      (∑ p : Pt, if G.Charged p H then budget p else 0) ≤
        q * (ε * ((observedRole (S.search mt) .signature H).card + 1)) := by
    let seen := (queried (S.search mt) H).toFinset
    let replay := univ.image (fun j : Fin L => S.hashInput (S.proof mt H) j.val)
    have hset : (univ.filter fun p : Pt => G.Charged p H) = seen ∪ replay := by
      ext p
      simp only [mem_filter, mem_univ, true_and, mem_union, seen, replay, List.mem_toFinset,
        mem_image, G, Bcs.TotalOracle.CtxGrinding.Charged, Bcs.TotalOracle.CtxGrinding.point,
        Bcs.TotalOracle.CtxGrinding.proof, Setup.grinding,
        S.proof_eq mt H]
    have hseen : ∑ p ∈ seen, budget p ≤ q * ε * (observedRole (S.search mt) .signature H).card := by
      calc
        _ ≤ ∑ p ∈ seen, if queryRole p = .signature then q * ε else 0 := by
          apply sum_le_sum
          intro p _
          by_cases hp : queryRole p = .signature
          · simpa only [if_pos hp] using signature_raw_budget_observed_le (C := C) p
          · rw [if_neg hp, hsig_only p, if_neg hp]
        _ = _ := by
          have hfilter : (seen.filter fun p => queryRole p = .signature) =
              observedRole (S.search mt) .signature H := by
            ext p
            simp only [observedRole, MacCharge125.observedKeys, seen, mem_filter]
          rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul]
          ring
    have hrep : ∑ p ∈ replay, budget p ≤ q * ε := by
      rw [show replay = _ from rfl, sum_image (hinputs (S.proof mt H)).injOn]
      exact hReplay (S.proof mt H)
    rw [← sum_filter, hset]
    exact (LigeroHighMass125.sum_union_le hbudget_nonneg).trans
      ((add_le_add hseen hrep).trans_eq (by ring))
  have hwt_sum :
      (∑ H : Pt → C, ∑ p : Pt, wt p H (H p)) ≤
        ε * (∑ H : Pt → C, (((observedRole (S.search mt) .signature H).card : ℚ) + 1)) := by
    apply le_of_mul_le_mul_right ?_ hq
    change (∑ H : Pt → C, ∑ p : Pt, wt p H (H p)) * (Fintype.card C : ℚ) ≤ _
    rw [sum_comm, sum_mul]
    simp_rw [sum_coord_mul_rat _ _ (hoff _)]
    rw [sum_comm]
    have hsum : (∑ H : Pt → C, ∑ p : Pt, ∑ a : C, wt p H a) ≤
        ∑ H : Pt → C, q * (ε * ((observedRole (S.search mt) .signature H).card + 1)) :=
      sum_le_sum (fun H _ => (sum_le_sum (fun p _ => hfiber p H)).trans (hbudgets H))
    have heq : (∑ H : Pt → C, q * (ε * ((observedRole (S.search mt) .signature H).card + 1))) =
        (ε * (∑ H : Pt → C, (((observedRole (S.search mt) .signature H).card : ℚ) + 1))) * q := by
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro H _
      ring
    rw [heq] at hsum
    exact hsum
  have hcover (H : Pt → C) : (if event H then (1 : ℚ) else 0) ≤
      ∑ p : Pt, wt p H (H p) := by
    by_cases he : event H
    · rw [if_pos he]
      have hg (j : ℕ) : G.point H j = S.hashInput (S.proof mt H) j :=
        S.grinding_point mt pts2 _ _ _ H j
      have hctx (j : ℕ) : G.ctxAt H (G.key (S.hashInput (S.proof mt H) j)) = S.context mt H := by
        rw [← hg j]
        exact S.grinding_ctx_point mt pts2 _ _ _ H j
      have hpath' := hpath H he
      have hlocalPath := G.verifier_charge_le_total
        (fun out i j h => hinputs out h)
        (fun p => charge (G.ctxAt H (G.key p)) p H (H p))
        (fun p => hcharge_nonneg _ p H (H p)) H
      simp only [hg, hctx] at hlocalPath
      exact hpath'.trans hlocalPath
    · rw [if_neg he]
      apply sum_nonneg
      intro p _
      unfold wt
      split_ifs
      · exact hcharge_nonneg _ p H (H p)
      · exact le_rfl
  rw [card_filter, Nat.cast_sum]
  apply le_trans _ hwt_sum
  apply sum_le_sum
  intro H _
  by_cases he : event H
  · simpa only [if_pos he, Nat.cast_one] using hcover H
  · simpa only [if_neg he, Nat.cast_zero] using hcover H

end SignatureCount

section KeyCount

variable {C D Enc Early HashPublic SigPublic SaltH SaltS : Type}
variable [Fintype C] [Nonempty C] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
variable [Fintype D] [Fintype Early] [DecidableEq Early] [Nonempty HashPublic]
variable [Inhabited SaltH] [Inhabited SaltS]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {Fh Fs MsgH MsgS : Type}
variable [Field Fh] [Fintype Fh] [DecidableEq Fh] [SumcheckV1Interp Fh]
variable [Field Fs] [Fintype Fs] [DecidableEq Fs] [SumcheckV1Interp Fs]
variable [Fintype MsgH] [Inhabited MsgH] [DecidableEq MsgH]
variable [Fintype MsgS] [Inhabited MsgS] [DecidableEq MsgS]
variable {Mh Ms nth nts nlinh nlins nblk : ℕ} {i : Fin 4}
variable {hH : (v7HashRow i).Valid} {hrH : 0 < (v7HashRow i).params.row.openings}
variable {hS : v7SigHahn.Valid}
variable {codecH : Codec SaltH (Col Fh (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {codecS : Codec SaltS (Col Fs v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
variable {decH : RoleDecoders codecH} {decS : RoleDecoders codecS}
variable (Hash : CircuitSide (v7HashRow i) hH hrH (v7HashLogv i)
  C Fh MsgH Mh nth nlinh HashPublic decH Prod.fst)
variable (Signature : CircuitSide v7SigHahn hS v7SigHahn_openings_pos 8
  C Fs MsgS Ms nts nlins SigPublic decS Prod.snd)
variable {Out : Type} {tA N TM : ℕ}

local notation "Pt" => SignatureBudget125.PairPoint D Fmac Early MsgH MsgS (v7HashRow i)

set_option maxHeartbeats 1000000 in
/-- The projected MAC event at the actual selected key, including at most
one analytical lookup on the submitted transcript. -/
theorem key_failure_count_le
    (body : TwoOracleTree Enc D Pt C Out tA N)
    (rootH rootS : Out → D) (avOf : Out → Fmac) (earlyOf : Out → Early)
    (msgH : Out → ℕ → MsgH) (msgS : Out → ℕ → MsgS)
    (mt : Fin TM → D) (d : ExactDecoder C Fmac) (hq : Fintype.card Fmac = 2 ^ 128)
    (commonH shareH : (Fin Hash.c.ninp → Fh) → Fin nblk → Fmac)
    (commonS shareS : (Fin Signature.c.ninp → Fs) → Fin nblk → Fmac)
    (shift : Cut D Enc → Fmac) (event : (Pt → C) → Prop)
    (hcover : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H →
        let κ := S.context mt H
        MacCharge125.badKey (Signature.cands κ) (Hash.candsAt (HashCut125.radius i) κ)
          commonS commonH shareS shareH (shift κ) (d.decode (H (S.hashInput (S.proof mt H) 0)))) :
    let S := setup2 body rootH rootS avOf earlyOf msgH msgS
    ((univ.filter event).card : ℚ) ≤ (4 / (2^128 : ℚ)) * ∑ H : Pt → C,
      ((observedRole (S.search mt) .key H).card + (1 : ℚ)) := by
  let S := setup2 body rootH rootS avOf earlyOf msgH msgS
  let key (out : Out) : Pt := Sum.inl (rootH out, rootS out)
  let cut (q : Pt) (H : Pt → C) := (S.atOracle H).ctxAt mt Setup.emptyTape (S.key q)
  have hoff (q : Pt) (H H' : Pt → C) (h : AgreeOff q H H') : cut q H = cut q H' :=
    (S.ctxAt_off mt H H' q h).symm
  have h := MacCharge125.v7_key_charge_sum_le Signature Hash (S.search mt)
    (fun q => queryRole q = .key) key (fun _ => rfl) cut hoff commonS shareS commonH shareH
    shift d hq event (by
      intro H he
      have hc : cut (key ((S.search mt).run H).1) H = S.context mt H := by
        rw [← S.proof_eq mt H]
        rfl
      have hp : key ((S.search mt).run H).1 = S.hashInput (S.proof mt H) 0 := by
        rw [← S.proof_eq mt H]
        exact (hash2_zero rootH rootS avOf earlyOf msgH msgS _).symm
      let q := key ((S.search mt).run H).1
      change MacCharge125.badKey (Signature.cands (cut q H))
        (Hash.candsAt (HashCut125.radius i) (cut q H)) commonS commonH shareS shareH
        (shift (cut q H)) (d.decode (H q))
      dsimp only [q]
      rw [hc, hp]
      exact hcover H he)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro H _
  exact add_le_add le_rfl (MacCharge125.appendedKeyCount_le_one (S.search mt) key H)

end KeyCount

end LfzkV1.TwoFieldCover125
