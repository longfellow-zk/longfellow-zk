import Lfzk.CompiledZkTwoField
import Lfzk.ZkLigeroV1
import Lfzk.RbrZkPotentialData
import Lfzk.RbrZkPotentialPoint
import Lfzk.ZkPotentialBalance
import Lfzk.GradedCost

/-!
# Graded V1 charges for a compiled Longfellow side

The committed oracle is the same cut-trace extraction used by
`CompiledZkSide.toZkSide`.  These are local hash-answer counts; the merged
two-field potential compiler handles adaptive queries and both Merkle
openings separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZk.CompiledZkSide

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree LigeroFamily Lfzk.CertifiedV1
  Lfzk.ZkLigeroV1 Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit
  Lfzk.CompiledLongfellow Lfzk.CompiledLongfellowAdaptive
open scoped Classical

variable {R : Lfzk.CertifiedV1.Row} {hR : R.Valid}
  {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C]
  {F Msg Witness : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [DecidableEq Msg] [Inhabited Msg]
variable {M ninp nt nlin logw logc : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D]
  [DecidableEq Enc] [Inhabited Salt]
variable {X : Type}
  {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}
variable (L : CompiledZkSide R hR hr logv C F Msg Witness
  M ninp nt nlin logw logc X dec rootOfKey)

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- A no-solution premise at a larger certified extraction radius also
supplies the premise expected by the existing field-round analysis.  The
field rounds can therefore keep their deployed list while the flat terminal
Ligero check uses the larger list from its optimized certificate. -/
theorem noSat_at_implies_sideNoSat
    (σ : Sig D C X Enc) (sys : LigeroSystem ninp M F) (radius : ℕ)
    (hradius : R.params.row.e + R.params.row.g ≤ radius)
    (hno : NoSat
      (asgAt L.pl radius (h := Row.rowValid hR) (D := L.dom)
        (hkrow := Row.hkrow hR)
        (O := extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
          hr dec (rootOfKey σ.1.1, σ.1.2))) sys) :
    NoSat
      (asgOf L.pl (h := Row.rowValid hR) (D := L.dom)
        (hkrow := Row.hkrow hR)
        (O := extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
          hr dec (rootOfKey σ.1.1, σ.1.2))) sys := by
  exact ZkLigeroV1.noSat_of_larger_radius L.pl hradius sys hno

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- Exact full-tail charge for a decoded Ligero combination challenge at a
compiled side's built system.  This estimate is uniform in the system and
does not use a challenge/query agreement cutoff. -/
theorem potential_challenge_hash_charge_le
    (σ : Sig D C X Enc) (sys : LigeroSystem ninp M F)
    (ψ : LigeroFamily.PotentialProfile.Curve R.params.row.n)
    {HashAnswer : Type} [Fintype HashAnswer]
    (decode : HashAnswer → ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
    (kchal : ℕ)
    (hbalance : ∀ challenge,
      (univ.filter fun c : HashAnswer => decode c = challenge).card ≤ kchal) :
    let O := extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
      hr dec (rootOfKey σ.1.1, σ.1.2)
    let X := policyMaxResponseAgreement
      (Ligero.V1.potentialFailedPolicy (e := R.params.row.e)
        (g := R.params.row.g) (R.params.row.code (Row.rowValid hR) L.dom
          (Row.hkrow hR)) O) O (stmtOf L.pl nlin sys)
    (∑ c : HashAnswer, ψ.value (X (decode c))) ≤
      kchal * Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt) *
        (∑ a ∈ range (R.params.row.n + 1), ψ.increment a *
          PolicyDoublyProfiledSoundnessClassifier.gradedTail
            (R.params.row.failureProfileAt (Fintype.card F))
            (maskAgreementProfile (Fintype.card F) R.params.row.n
              R.params.row.listBound R.params.row.certificate.maskStart
              R.params.row.certificate.maskBound)
            (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
              (Fintype.card F) R.params.row.g)
            (Fintype.card F) R.params.row.e R.params.row.g a) := by
  exact ZkLigeroV1.potential_challenge_hash_charge_built L.pl
    (Row.rowValid hR) (Row.coreRows hR) L.hF L.dom (Row.hkrow hR)
    (extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
      hr dec (rootOfKey σ.1.1, σ.1.2)) sys ψ decode kchal hbalance

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- Exact residual query charge after the combination challenge, at a
compiled side whose built system has no satisfying member in the committed
lift list.  The response may be selected after the challenge. -/
theorem potential_query_hash_charge_le
    (σ : Sig D C X Enc) (sys : LigeroSystem ninp M F)
    (hf : Fits (L.Vc σ.2.1 σ.2.2) sys)
    (hn : NoSat (asgOf L.pl (h := Row.rowValid hR) (D := L.dom)
      (hkrow := Row.hkrow hR)
      (O := extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
        hr dec (rootOfKey σ.1.1, σ.1.2))) sys)
    (ψ : LigeroFamily.PotentialProfile.Curve R.params.row.n)
    (challenge : ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
    (response : Response F R.params.row.openings R.params.q R.params.row.n 1)
    {HashAnswer : Type} [Fintype HashAnswer]
    (decode : HashAnswer → LigeroV1LayerStep.Qry R.params.row)
    (kq : ℕ)
    (hbalance : ∀ query,
      (univ.filter fun c : HashAnswer => decode c = query).card ≤ kq) :
    let O := extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
      hr dec (rootOfKey σ.1.1, σ.1.2)
    let X := policyMaxResponseAgreement
      (Ligero.V1.potentialFailedPolicy (e := R.params.row.e)
        (g := R.params.row.g) (R.params.row.code (Row.rowValid hR) L.dom
          (Row.hkrow hR)) O) O (stmtOf L.pl nlin sys) challenge
    (∑ c : HashAnswer, if decode c ∈
      acceptingR (Row.rowValid hR) L.dom (Row.hkrow hR)
        ⟨stmtOf L.pl nlin sys, O⟩ response challenge then
        1 - ψ.value X else 0) ≤
      kq * Fintype.card (LigeroV1LayerStep.Qry R.params.row) *
        ψ.queryCost (fun a => hypergeometricRatio a R.params.row.n
          R.params.row.openings) := by
  exact ZkLigeroV1.potential_query_hash_charge_built_noSat
    (L.Vc σ.2.1 σ.2.2) (L.hnlin _ _) (L.hnt _ _) L.pl
    (Row.rowValid hR) L.dom (Row.hkrow hR)
    (extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
      hr dec (rootOfKey σ.1.1, σ.1.2)) sys hf hn ψ challenge response
      decode kq hbalance

/-- The actual compiled V1 side supplies the two graded terminal budgets
required by the extraction-first Longfellow chain.  Both decoder
preimage counts come from the side's existing exact decoder certificate. -/
noncomputable def terminalPotential
    (σ : Sig D C X Enc)
    (ψ : LigeroFamily.PotentialProfile.Curve R.params.row.n) :
    Lfzk.RbrZkFlat.TerminalPotential (L.LD σ) where
  weight := fun sys x =>
    ψ.value (policyMaxResponseAgreement
      (Ligero.V1.potentialFailedPolicy (e := R.params.row.e)
        (g := R.params.row.g) (R.params.row.code (Row.rowValid hR)
          L.dom (Row.hkrow hR))
        (extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
          hr dec (rootOfKey σ.1.1, σ.1.2)))
      (extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
        hr dec (rootOfKey σ.1.1, σ.1.2))
      (stmtOf L.pl nlin sys) x)
  nonneg := by
    intro sys x
    exact ψ.nonneg _ (policyMaxResponseAgreement_le
      (policy := Ligero.V1.potentialFailedPolicy (e := R.params.row.e)
        (g := R.params.row.g) (R.params.row.code (Row.rowValid hR)
          L.dom (Row.hkrow hR))
        (extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
          hr dec (rootOfKey σ.1.1, σ.1.2)))
      (oracle := extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
        hr dec (rootOfKey σ.1.1, σ.1.2))
      (statement := stmtOf L.pl nlin sys) x)
  le_one := by
    intro sys x
    exact ψ.le_one _ (policyMaxResponseAgreement_le
      (policy := Ligero.V1.potentialFailedPolicy (e := R.params.row.e)
        (g := R.params.row.g) (R.params.row.code (Row.rowValid hR)
          L.dom (Row.hkrow hR))
        (extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
          hr dec (rootOfKey σ.1.1, σ.1.2)))
      (oracle := extOracle nlin nt (Row.rowValid hR) L.dom (Row.hkrow hR)
        hr dec (rootOfKey σ.1.1, σ.1.2))
      (statement := stmtOf L.pl nlin sys) x)
  challengeBudget := max 0 ((L.FD σ).kchal *
    Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt) *
      (∑ a ∈ range (R.params.row.n + 1), ψ.increment a *
        PolicyDoublyProfiledSoundnessClassifier.gradedTail
          (R.params.row.failureProfileAt (Fintype.card F))
          (maskAgreementProfile (Fintype.card F) R.params.row.n
            R.params.row.listBound R.params.row.certificate.maskStart
            R.params.row.certificate.maskBound)
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
            (Fintype.card F) R.params.row.g)
          (Fintype.card F) R.params.row.e R.params.row.g a))
  queryBudget := max 0 ((L.FD σ).kq *
    Fintype.card (LigeroV1LayerStep.Qry R.params.row) *
      ψ.queryCost (fun a => hypergeometricRatio a R.params.row.n
        R.params.row.openings))
  challengeBudget_nonneg := le_max_left _ _
  queryBudget_nonneg := le_max_left _ _
  challenge_le := by
    intro sys _ _
    exact (L.potential_challenge_hash_charge_le σ sys ψ
      (L.Vc σ.2.1 σ.2.2).decodeChal (L.FD σ).kchal
      (L.FD σ).hbalChal).trans (le_max_right _ _)
  query_le := by
    intro m pref msg sys x hf hn
    apply le_trans (by simpa only [L.LD_acc, ZkLigeroV1.accZ] using
      (L.potential_query_hash_charge_le σ sys hf hn ψ x (L.respOf msg)
        (L.Vc σ.2.1 σ.2.2).decodeQuery (L.FD σ).kq
        (L.FD σ).hbalQuery))
    exact le_max_right _ _

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- Exact decoder balance removes the context-dependent challenge fiber
size from the graded local budget. -/
theorem terminalPotential_challengeBudget_le
    (σ : Sig D C X Enc)
    (ψ : LigeroFamily.PotentialProfile.Curve R.params.row.n) :
    (L.terminalPotential σ ψ).challengeBudget ≤
      max 0 ((Fintype.card C : ℚ) *
        (∑ a ∈ range (R.params.row.n + 1), ψ.increment a *
          PolicyDoublyProfiledSoundnessClassifier.gradedTail
            (R.params.row.failureProfileAt (Fintype.card F))
            (maskAgreementProfile (Fintype.card F) R.params.row.n
              R.params.row.listBound R.params.row.certificate.maskStart
              R.params.row.certificate.maskBound)
            (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
              (Fintype.card F) R.params.row.g)
            (Fintype.card F) R.params.row.e R.params.row.g a)) := by
  let T := ∑ a ∈ range (R.params.row.n + 1), ψ.increment a *
    PolicyDoublyProfiledSoundnessClassifier.gradedTail
      (R.params.row.failureProfileAt (Fintype.card F))
      (maskAgreementProfile (Fintype.card F) R.params.row.n
        R.params.row.listBound R.params.row.certificate.maskStart
        R.params.row.certificate.maskBound)
      (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
        (Fintype.card F) R.params.row.g)
      (Fintype.card F) R.params.row.e R.params.row.g a
  have hbal : (L.FD σ).kchal * Fintype.card
      (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt) ≤ Fintype.card C := by
    rcases L.hexact σ with ⟨_, _, _, _, hc, _⟩
    exact hc
  change max 0 (((L.FD σ).kchal : ℚ) *
    Fintype.card (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt) * T) ≤
    max 0 ((Fintype.card C : ℚ) * T)
  simpa only [Nat.cast_mul, mul_assoc] using
    Lfzk.ZkPotentialBalance.max_zero_nat_mul_le hbal T

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- The residual query budget enjoys the same uniformity, with no
challenge/query threshold. -/
theorem terminalPotential_queryBudget_le
    (σ : Sig D C X Enc)
    (ψ : LigeroFamily.PotentialProfile.Curve R.params.row.n) :
    (L.terminalPotential σ ψ).queryBudget ≤
      max 0 ((Fintype.card C : ℚ) *
        ψ.queryCost (fun a => hypergeometricRatio a R.params.row.n
          R.params.row.openings)) := by
  have hbal : (L.FD σ).kq * Fintype.card
      (LigeroV1LayerStep.Qry R.params.row) ≤ Fintype.card C := by
    rcases L.hexact σ with ⟨_, _, _, _, _, hq⟩
    exact hq
  change max 0 (((L.FD σ).kq : ℚ) *
    Fintype.card (LigeroV1LayerStep.Qry R.params.row) *
      ψ.queryCost (fun a => hypergeometricRatio a R.params.row.n
        R.params.row.openings)) ≤ _
  simpa only [Nat.cast_mul, mul_assoc] using
    Lfzk.ZkPotentialBalance.max_zero_nat_mul_le hbal
      (ψ.queryCost (fun a => hypergeometricRatio a R.params.row.n
        R.params.row.openings))

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- The challenge budget is bounded by the shared row-and-curve density.
This is the adapter used by concrete numerical certificates. -/
theorem terminalPotential_challengeBudget_le_density
    (σ : Sig D C X Enc)
    (ψ : LigeroFamily.PotentialProfile.Curve R.params.row.n) :
    (L.terminalPotential σ ψ).challengeBudget ≤
      max 0 ((Fintype.card C : ℚ) * Lfzk.GradedCost.challenge R ψ) := by
  simpa only [Lfzk.GradedCost.challenge, L.hF,
    Lfzk.LigeroV1Rows.Row.arithProfile] using
    L.terminalPotential_challengeBudget_le σ ψ

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- The residual-query budget uses the same shared density interface. -/
theorem terminalPotential_queryBudget_le_density
    (σ : Sig D C X Enc)
    (ψ : LigeroFamily.PotentialProfile.Curve R.params.row.n) :
    (L.terminalPotential σ ψ).queryBudget ≤
      max 0 ((Fintype.card C : ℚ) * Lfzk.GradedCost.query R ψ) := by
  simpa only [Lfzk.GradedCost.query] using
    L.terminalPotential_queryBudget_le σ ψ

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- Any checked challenge-density upper bound lifts to the compiled
hash-answer budget, including non-power-of-two answer alphabets. -/
theorem terminalPotential_challengeBudget_le_bound
    (σ : Sig D C X Enc)
    (ψ : LigeroFamily.PotentialProfile.Curve R.params.row.n)
    (b : ℚ) (hb : Lfzk.GradedCost.challenge R ψ ≤ b) :
    (L.terminalPotential σ ψ).challengeBudget ≤
      max 0 ((Fintype.card C : ℚ) * b) := by
  exact (L.terminalPotential_challengeBudget_le_density σ ψ).trans
    (max_le_max_left 0 (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)))

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/-- The analogous lift for the residual query density. -/
theorem terminalPotential_queryBudget_le_bound
    (σ : Sig D C X Enc)
    (ψ : LigeroFamily.PotentialProfile.Curve R.params.row.n)
    (b : ℚ) (hb : Lfzk.GradedCost.query R ψ ≤ b) :
    (L.terminalPotential σ ψ).queryBudget ≤
      max 0 ((Fintype.card C : ℚ) * b) := by
  exact (L.terminalPotential_queryBudget_le_density σ ψ).trans
    (max_le_max_left 0 (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)))

end Lfzk.CompiledZk.CompiledZkSide
