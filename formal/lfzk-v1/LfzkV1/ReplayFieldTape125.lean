import LfzkV1.ReplayDecode125
import LfzkV1.ResidualReplay125Run

/-! The grouped field draws of a fixed legacy v1 transcript as polynomial variables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.ReplayFieldTape125

open LfzkV1.ReplayView125 LfzkV1.ReplayDecode125 LfzkV1.ResidualReplay125
open LfzkV1.TwoFieldV1Rows LfzkV1.RbrZkLongfellow Merkle.RandomOracle
open LfzkV1.NizkGrinding (indexEquiv_symm_index)
open LfzkV1.Arith LfzkV1.ZkArithProfile LfzkV1.CompiledZk
open MvPolynomial
open scoped Classical

variable {C F : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable {nl logv : ℕ} {w : ℕ → ℕ}

def roleWidth (logv : ℕ) : Rounds.Role nl w → ℕ
  | .layerPair ly => if ly.val = 0 then logv + 2 else 2
  | .sumcheck _ _ | .inputBind => 1
  | .ligeroChallenge | .ligeroQuery => 0

private def noScalar : ExactDecoder C (Fin 0 → F) where
  decode _ i := i.elim0
  k := Fintype.card C
  hbal _ := Finset.card_le_univ _
  hexact := by simp

noncomputable def roleDecoder (init : ExactDecoder C ((Fin logv → F) × F × F))
    (pair : ExactDecoder C (F × F)) (scalar : ExactDecoder C F)
    (r : Rounds.Role nl w) : ExactDecoder C (Fin (roleWidth logv r) → F) :=
  match r with
  | .layerPair ly =>
    if h : ly.val = 0 then reindex (initDecoder init)
      ((finCongr (by simp [roleWidth, h])).arrowCongr (Equiv.refl F))
    else reindex (pairDecoder pair)
      ((finCongr (by simp [roleWidth, h])).arrowCongr (Equiv.refl F))
  | .sumcheck _ _ | .inputBind => scalarDecoder scalar
  | .ligeroChallenge | .ligeroQuery => noScalar

variable {Q Out : Type} {fuel k : ℕ}
variable {tree : Tree Q C Out fuel} {lookups : Out → List Q} {H : Q → C}
variable (address : Rounds.Role nl w ↪ Q)
variable (init : ExactDecoder C ((Fin logv → F) × F × F))
variable (pair : ExactDecoder C (F × F)) (scalar : ExactDecoder C F)
variable (index : (Σ i : HiddenRole (tree := tree) (lookups := lookups) (H := H) address,
  Fin (roleWidth logv i.val)) ≃ Fin k)

private noncomputable def atRole (r : Rounds.Role nl w) (j : Fin (roleWidth logv r)) :=
  replayCoordinate address (roleDecoder init pair scalar) index r j

private def initialIndex (ly : Fin nl) (h : ly.val = 0) (j : Fin (logv + 2)) :
    Fin (roleWidth logv (Rounds.Role.layerPair (w := w) ly)) :=
  j.cast (by simp [roleWidth, h])

private def pairIndex (ly : Fin nl) (h : ly.val ≠ 0) (j : Fin 2) :
    Fin (roleWidth logv (Rounds.Role.layerPair (w := w) ly)) :=
  j.cast (by simp [roleWidth, h])

/-- The only variables in this tape correspond to actual unseen field draws. -/
noncomputable def fieldTape (hpos : 0 < nl) : FieldTape (Fin k) F nl w logv where
  G j := atRole address init pair scalar index (.layerPair ⟨0, hpos⟩)
    (initialIndex ⟨0, hpos⟩ rfl (Fin.castAdd 2 j))
  beta ly := if h : ly.val = 0 then
    atRole address init pair scalar index (.layerPair ly)
      (initialIndex ly h (Fin.natAdd logv (0 : Fin 2)))
    else atRole address init pair scalar index (.layerPair ly) (pairIndex ly h 0)
  alpha ly := if h : ly.val = 0 then
    atRole address init pair scalar index (.layerPair ly)
      (initialIndex ly h (Fin.natAdd logv (1 : Fin 2)))
    else atRole address init pair scalar index (.layerPair ly) (pairIndex ly h 1)
  round ly j := atRole address init pair scalar index (.sumcheck ly j) (0 : Fin 1)
  inputAlpha := atRole address init pair scalar index .inputBind (0 : Fin 1)

theorem fieldTape_bounded (hpos : 0 < nl) :
    (fieldTape address init pair scalar index hpos).Bounded := by
  have h (r : Rounds.Role nl w) (j : Fin (roleWidth logv r)) :
      (atRole address init pair scalar index r j).totalDegree ≤ 1 :=
    replayCoordinate_degree _ _ _ _ _
  constructor
  · intro j; exact h _ _
  · intro ly; simp only [fieldTape]; split <;> exact h _ _
  · intro ly; simp only [fieldTape]; split <;> exact h _ _
  · intro ly j; exact h _ _
  · exact h _ _

omit [Field F] in
private theorem decode_initialIndex (ly : Fin nl) (h : ly.val = 0) (j : Fin (logv + 2)) (c : C) :
    (roleDecoder init pair scalar (.layerPair (w := w) ly)).decode c (initialIndex ly h j) =
      (initDecoder init).decode c j := by
  simp [roleDecoder, h, reindex, Equiv.arrowCongr_apply, initialIndex]

omit [Field F] in
private theorem decode_pairIndex (ly : Fin nl) (h : ly.val ≠ 0) (j : Fin 2) (c : C) :
    (roleDecoder init pair scalar (.layerPair (w := w) ly)).decode c (pairIndex ly h j) =
      (pairDecoder pair).decode c j := by
  simp [roleDecoder, h, reindex, Equiv.arrowCongr_apply, pairIndex]

variable {X Qry Msg : Type} {M ninp L : ℕ}

/-- Evaluating the coordinate tape in a fixed view reproduces the actual
verifier decoders on every scheduled field role. -/
theorem fieldTape_matches (V : ZkCode C F X Qry Msg (Fin logv → F) M ninp L 0)
    (hinit : init.decode = V.decodeInit) (hpair : pair.decode = V.decodePair)
    (hscalar : scalar.decode = V.decodeF) (hpos : 0 < nl) (H' : ViewFiber tree lookups H) :
    (fieldTape address init pair scalar index hpos).Matches V
      (flatten index fun h => (roleDecoder init pair scalar h.val).decode (H'.val (address h.val)))
      (fun j => H'.val (address (Rounds.Role.indexEquiv.symm j))) := by
  let values := flatten index fun h =>
    (roleDecoder init pair scalar h.val).decode (H'.val (address h.val))
  have he (r : Rounds.Role nl w) (j : Fin (roleWidth logv r)) :
      eval values (atRole address init pair scalar index r j) =
        (roleDecoder init pair scalar r).decode (H'.val (address r)) j :=
    replayCoordinate_eval _ _ _ H' _ _
  let P := fieldTape address init pair scalar index hpos
  constructor
  · intro ly hl
    have hly : ly = ⟨0, hpos⟩ := Fin.ext hl
    change V.decodeInit (H'.val (address (Rounds.Role.indexEquiv.symm (Rounds.Role.index (.layerPair ly))))) =
      (fun j => eval values (P.G j), eval values (P.beta ly), eval values (P.alpha ly))
    rw [indexEquiv_symm_index, hly]
    simp [P, fieldTape, he, decode_initialIndex, hinit]
  · intro ly hl
    change V.decodePair (H'.val (address (Rounds.Role.indexEquiv.symm (Rounds.Role.index (.layerPair ly))))) =
      (eval values (P.beta ly), eval values (P.alpha ly))
    rw [indexEquiv_symm_index]
    simp only [P, fieldTape, dif_neg hl, he,
      decode_pairIndex, pairDecoder_zero, pairDecoder_one, hpair]
  · intro ly j
    change V.decodeF (H'.val (address (Rounds.Role.indexEquiv.symm (Rounds.Role.index (.sumcheck ly j))))) =
      eval values (P.round ly j)
    rw [indexEquiv_symm_index]
    simp only [P, fieldTape, he, roleDecoder, scalarDecoder_apply, hscalar]
  · change V.decodeF (H'.val (address (Rounds.Role.indexEquiv.symm (Rounds.Role.index .inputBind)))) =
      eval values P.inputAlpha
    rw [indexEquiv_symm_index]
    simp only [P, fieldTape, he, roleDecoder, scalarDecoder_apply, hscalar]

section System

variable [SumcheckV1Interp F] {c : QuadCircuit F}

/-- One degree-81 system describes the actual compiled field run throughout
the fixed view. A successful original run fixes the tableau-fit guard. -/
theorem system_of_view
    (points : Rounds.Role c.nl w ↪ Q)
    (indices : (Σ i : HiddenRole (tree := tree) (lookups := lookups) (H := H) points,
      Fin (roleWidth logv i.val)) ≃ Fin k)
    (V : ZkCode C F X Qry Msg (Fin logv → F) M c.ninp L 0) (ms : ℕ → Msg)
    (hinit : init.decode = V.decodeInit) (hpair : pair.decode = V.decodePair)
    (hscalar : scalar.decode = V.decodeF) (pub : Fin c.ninp → F)
    (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (hpos : 0 < c.nl) {R : LfzkV1.CertifiedV1.Row} (hR : V7HashProfile R)
    (hnl : c.nl = R.params.nl) (hw : w = R.params.rounds) (hlogv : logv ≤ 5)
    (hBuilt : ∃ sys, zkBuilt (w := w) V ms
      (fun j => H (points (Rounds.Role.indexEquiv.symm j))) = some sys) :
    ∃ S : ResidualReplay125.System (Fin k) F c.ninp M, S.Bounded 81 ∧
      ∀ H' : ViewFiber tree lookups H,
        let values := flatten indices fun h =>
          (roleDecoder init pair scalar h.val).decode (H'.val (points h.val))
        zkBuilt (w := w) V ms (fun j => H'.val (points (Rounds.Role.indexEquiv.symm j))) =
          some (S.eval values) := by
  let P := fieldTape points init pair scalar indices hpos
  let S := P.system V ms pub hpos
  have hfit : c.nl + 1 ≤ V.nlin ∧ c.nl ≤ V.nt := by
    by_contra hn
    obtain ⟨sys, hs⟩ := hBuilt
    let orig : ViewFiber tree lookups H := ⟨H, rfl⟩
    have hm := fieldTape_matches points init pair scalar indices V hinit hpair hscalar hpos orig
    have hh := FieldTape.zkBuilt_eq_if V ms P hV hst0 _ _ hm hpos
    rw [if_neg hn, hs] at hh
    contradiction
  refine ⟨S, FieldTape.system_bounded81 V ms P pub hpos hR hnl hw hlogv ?_, ?_⟩
  · exact fieldTape_bounded points init pair scalar indices hpos
  · intro H'
    exact FieldTape.zkBuilt_eq V ms P hV hst0 _ _
      (fieldTape_matches points init pair scalar indices V hinit hpair hscalar hpos H') hpos hfit.1 hfit.2

end System

end LfzkV1.ReplayFieldTape125
