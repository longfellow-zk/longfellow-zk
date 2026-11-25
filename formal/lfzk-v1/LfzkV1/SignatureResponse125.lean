import LfzkV1.SignatureBudget125
import LfzkV1.ResponseDecode125
import LfzkV1.CompiledZkPotential
import LfzkV1.CompiledZkProfileRows
import LfzkV1.ZkPotentialBalance
import Bcs.PotentialChain
import Ligero.V1.PotentialExtraction

/-! The signature terminal budget for failure on the actual v1 response. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace LfzkV1.SignatureResponse125

open Finset LigeroFamily LfzkV1.CertifiedV1
open LfzkV1.ZkPotentialBalance
open scoped Classical

section Terminal

variable {F E Answer : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E] [Fintype Answer]
variable {r w n nw nq e g : ℕ}
variable (C : MultiplicativeCode F r w n)
variable (oracle : Ligero.V1.Oracle F nw nq n 1)
variable (statement : ConstraintSystem F nw nq w E)

local notation "Chal" => Ligero.V1.Challenge F nw nq 1 E
local notation "Reply" => LigeroFamily.Response F r w n 1
local notation "v1policy" => SchemeVerifier.policy (Equations := E)
  (nw := nw) (nq := nq) (repetitions := 1) C Ligero.V1.scheme

/-- The existing scalar-gap failure predicate at this response. Its finite
choice is used here only as a predicate on analysis candidates. -/
def terminalFailure (challenge : Chal) (response : Reply) : Prop :=
  ScalarGapExtraction.extract (e := e) (g := g) v1policy
    (fun (x : SchemeLiftCandidate C oracle (e + g)) => x.decodedMessages)
    statement challenge response = none

/-- The budget with the original graded potential applies to failure of the
actual response even when a different candidate satisfies the statement. -/
theorem query_charge_le
    (ψ : PotentialProfile.Curve n) (challenge : Chal) (response : Reply)
    (decode : Answer → QuerySet n r) (b : ℕ)
    (hbalance : ∀ q, (univ.filter fun c : Answer => decode c = q).card ≤ b)
    (hn : Nonempty (QuerySet n r)) :
    let X := policyMaxResponseAgreement (Ligero.V1.potentialFailedPolicy (e := e) (g := g) C oracle)
      oracle statement challenge
    (∑ c : Answer, if terminalFailure (e := e) (g := g) C oracle statement challenge response ∧
        (v1policy).accepts statement challenge response (decode c) (openSchemeOracle oracle (decode c)) then
      1 - ψ.value X else 0) ≤
      b * Fintype.card (QuerySet n r) * ψ.queryCost (fun a => hypergeometricRatio a n r) := by
  letI : Nonempty (QuerySet n r) := hn
  let X := policyMaxResponseAgreement (Ligero.V1.potentialFailedPolicy (e := e) (g := g) C oracle)
    oracle statement challenge
  have hx : X ≤ n := policyMaxResponseAgreement_le
    (policy := Ligero.V1.potentialFailedPolicy (e := e) (g := g) C oracle)
    (oracle := oracle) (statement := statement) challenge
  have hw : 0 ≤ 1 - ψ.value X := sub_nonneg.mpr (ψ.le_one X hx)
  apply decoded_query_charge_le decode
    (fun q => terminalFailure (e := e) (g := g) C oracle statement challenge response ∧
      (v1policy).accepts statement challenge response q (openSchemeOracle oracle q))
    (1 - ψ.value X) hw b hbalance
  rw [QuerySet.fintype_card]
  rw [show (univ.filter fun q : QuerySet n r =>
      terminalFailure (e := e) (g := g) C oracle statement challenge response ∧
      (v1policy).accepts statement challenge response q (openSchemeOracle oracle q)) =
    (univ.filter fun q : QuerySet n r =>
      (v1policy).accepts statement challenge response q (openSchemeOracle oracle q) ∧
      terminalFailure (e := e) (g := g) C oracle statement challenge response) by
      ext q
      simp only [mem_filter, mem_univ, true_and, and_comm]]
  convert Ligero.V1.scalarGap_query_potential_le (e := e) (g := g)
    C oracle statement ψ challenge response using 4
  apply congrArg Finset.card
  ext q
  simp only [mem_filter, mem_univ, true_and, terminalFailure]

/-- An analysis lift compatible with the claimed proximity response has
enough matching positions to recover it row by row at the punctured radius. -/
theorem recover_of_scalar_gap_success (challenge : Chal) (response : Reply)
    (hk : C.k + 2 * g + (e + g) ≤ n)
    (x : SchemeLiftCandidate C oracle (e + g))
    (h : ScalarGapExtraction.extract v1policy
      (fun (y : SchemeLiftCandidate C oracle (e + g)) => y.decodedMessages)
      statement challenge response = some x) :
    ResponseDecode125.decode C oracle (challenge 0).proximity (response.proximity 0) g (e + g) =
      some x := by
  classical
  obtain ⟨⟨hrow, hrem⟩, _⟩ := ScalarGapExtraction.extract_valid v1policy
    (fun (y : SchemeLiftCandidate C oracle (e + g)) => y.decodedMessages)
    statement challenge response x h
  let S := schemeProximityAgreement oracle (challenge 0).proximity (response.proximity 0)
  have hs : x.badColumnsᶜ ⊆ S := by
    intro j hj
    have hgood := mem_compl.mp hj
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change x.proximityRow (challenge 0).proximity = response.proximity 0 at hrow
    rw [← hrow]
    simp only [SchemeLiftCandidate.proximityRow, schemeProximityObserved, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [SchemeLiftCandidate.offset_eq_of_not_bad x j hgood, add_comm]
    congr 1
    exact sum_congr rfl fun row _ =>
      congrArg ((challenge 0).proximity row * ·) (SchemeLiftCandidate.row_eq_of_not_bad x row j hgood).symm
  have hS := card_le_card hs
  rw [card_compl, Fintype.card_fin] at hS
  have hbad := x.badColumns_card
  have hsize : C.k + 2 * g ≤ S.card := by omega
  exact ResponseDecode125.decode_eq_some C oracle (challenge 0).proximity (response.proximity 0)
    g (e + g) x hsize hrem

end Terminal

section Compiled

open Merkle.MH LfzkV1.CompiledZk LfzkV1.CompiledLongfellowAdaptive
  LfzkV1.CompiledLongfellow LfzkV1.ZkLigeroV1 LfzkV1.RbrZkLongfellow

variable {C F Msg D Enc Salt X : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckV1Interp F] [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
  {M nt nlin : ℕ} {hR : v7SigHahn.Valid}
  {codec : Codec Salt (Col F v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
  {dec : RoleDecoders codec}
variable (S : CircuitSide v7SigHahn hR v7SigHahn_openings_pos 8 C F Msg M nt nlin X dec Prod.snd)

local notation "SigTape" =>
  (Fin (Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds) → C)
local notation "SigCode" => v7SigHahn.params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR)
local notation "SigOracle" σ => extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR)
  v7SigHahn_openings_pos dec (Prod.snd (Prod.fst (Prod.fst σ)), Prod.snd (Prod.fst σ))
private def signatureChallenge (σ : Sig D C X Enc) (tape : SigTape) :
    ZkLigeroV1.Chal F v7SigHahn.params.nw v7SigHahn.params.nq nlin nt :=
  (S.Vc σ.2.1 σ.2.2).decodeChal (tape ligIdx)
local notation "SigResponse" msgs =>
  S.respOf (msgs (Rounds.Role.layerBase v7SigHahn.params.rounds v7SigHahn.params.nl + 2))

/-- Decode the signature tableau from the response's proximity-agreement
columns, then verify the reconstructed input against the original circuit. -/
noncomputable def signatureResponseWitness (σ : Sig D C X Enc) (msgs : ℕ → Msg) (tape : SigTape) :
    Option (Fin S.c.ninp → F) := by
  classical
  exact (ResponseDecode125.decode SigCode (SigOracle σ) ((signatureChallenge S σ tape) 0).proximity
      ((SigResponse msgs).proximity 0) v7SigHahn.params.row.g
      (v7SigHahn.params.row.e + v7SigHahn.params.row.g)).bind fun x =>
    let a := (asgOf S.pl x).1
    if S.c.Satisfied (S.pubIn σ.2.1 σ.2.2) a then some a else none

/-- Any successful signature decoding gives a valid circuit input amongst
the close tableaux used by the soundness proof. -/
theorem signatureResponseWitness_good [DecidableEq Msg] [Inhabited Msg]
    (σ : Sig D C X Enc) (msgs : ℕ → Msg) (tape : SigTape)
    (a : Fin S.c.ninp → F) (h : signatureResponseWitness S σ msgs tape = some a) :
    S.toSide.Good σ a := by
  unfold signatureResponseWitness at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨x, _, h⟩ := h
  dsimp only at h
  split_ifs at h with hp
  exact (S.toSide_good σ a).mpr ⟨x, hp, Option.some.inj h⟩

/-- Extraction can fail either in the terminal Ligero response or because
its unique decoded assignment satisfies the built system but fails the circuit. -/
theorem signatureResponseWitness_none_cases
    (σ : Sig D C X Enc) (msgs : ℕ → Msg) (tape : SigTape)
    (sys : LigeroSystem S.c.ninp M F) (hf : Fits (S.Vc σ.2.1 σ.2.2) sys)
    (hn : signatureResponseWitness S σ msgs tape = none) :
    terminalFailure (e := v7SigHahn.params.row.e) (g := v7SigHahn.params.row.g)
        SigCode (SigOracle σ) (stmtOf S.pl nlin sys) (signatureChallenge S σ tape) (SigResponse msgs) ∨
      ∃ x : sideLift hR v7SigHahn_openings_pos nlin nt S.dom dec Prod.snd σ,
        sys.Sat (asgOf S.pl x).1 (asgOf S.pl x).2 ∧
        ¬ S.c.Satisfied (S.pubIn σ.2.1 σ.2.2) (asgOf S.pl x).1 := by
  let O := SigOracle σ
  let stmt := stmtOf S.pl nlin sys
  let ch := signatureChallenge S σ tape
  let u := SigResponse msgs
  let legacy := ScalarGapExtraction.extract
    (e := v7SigHahn.params.row.e) (g := v7SigHahn.params.row.g)
    (SchemeVerifier.policy SigCode Ligero.V1.scheme)
    (fun (y : sideLift hR v7SigHahn_openings_pos nlin nt S.dom dec Prod.snd σ) => y.decodedMessages)
    stmt ch u
  cases h : legacy with
  | none => exact Or.inl h
  | some x =>
      right
      have hk : (SigCode).k + 2 * v7SigHahn.params.row.g +
          (v7SigHahn.params.row.e + v7SigHahn.params.row.g) ≤ v7SigHahn.params.row.n := by
        rw [(SigCode).k_eq, Row.hkrow hR]
        decide +kernel
      have hd := recover_of_scalar_gap_success SigCode O stmt ch u hk x h
      have hs := (ScalarGapExtraction.extract_valid _ _ stmt ch u x h).2
      have hfit₁ := hf.1
      have hfit₂ := hf.2
      rw [S.hnlin] at hfit₁
      rw [S.hnt] at hfit₂
      refine ⟨x, Encode.sat_decode_encodeLig S.pl hfit₁ hfit₂ _ hs, ?_⟩
      intro ha
      unfold signatureResponseWitness at hn
      change ((ResponseDecode125.decode SigCode O (ch 0).proximity (u.proximity 0)
        v7SigHahn.params.row.g (v7SigHahn.params.row.e + v7SigHahn.params.row.g)).bind _) = none at hn
      rw [hd] at hn
      simp [ha] at hn

end Compiled

section Field

open LfzkV1.RbrZkLongfellow LfzkV1.RbrZkSplit LfzkV1.RbrLayerStepS
  LfzkV1.RbrZkFlat LfzkV1.CompiledLongfellow

variable {C F X Q Msg Gpt Lift : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckV1Interp F] [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Lift]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc} {H : ZkHonest F Lift logw logc}
variable {asg : Lift → LigeroAssignment ninp M F} {Sat : Lift → Prop}

/-- A particular candidate goes from wrong to right. Another candidate may
already have been correct, including at the start of the verifier. -/
def candidateEscape {T : ℕ} {A S : Type} (ch : Bcs.ClaimChain C T S A)
    (i : Fin T) (pref : Fin i.val → C) (coin : C) : Prop :=
  ∃ a, ch.Wrong a (ch.state i.val pref) ∧
    ¬ ch.Wrong a (ch.state (i.val + 1) (Bcs.extend pref coin))

private theorem candidateEscape_card_le {T : ℕ} {A S : Type} [Fintype A]
    (ch : Bcs.ClaimChain C T S A) (weight : A → ℕ) (b : ℕ)
    (i : Fin T) (pref : Fin i.val → C)
    (bound : ∀ a, ch.Wrong a (ch.state i.val pref) →
      (univ.filter fun c => ¬ ch.Wrong a (ch.step i pref c (ch.state i.val pref))).card ≤ weight a * b) :
    (univ.filter fun c : C => candidateEscape ch i pref c).card ≤ (∑ a, weight a) * b := by
  classical
  let wrong := univ.filter fun a => ch.Wrong a (ch.state i.val pref)
  let escape := fun a => univ.filter fun c : C => ¬ ch.Wrong a (ch.step i pref c (ch.state i.val pref))
  have hs : (univ.filter fun c : C => candidateEscape ch i pref c) ⊆ wrong.biUnion escape := by
    intro c hc
    obtain ⟨a, hw, ha⟩ := (mem_filter.mp hc).2
    rw [Bcs.ClaimChain.state_extend] at ha
    exact mem_biUnion.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, hw⟩, mem_filter.mpr ⟨mem_univ _, ha⟩⟩
  calc
    _ ≤ (wrong.biUnion escape).card := card_le_card hs
    _ ≤ ∑ a ∈ wrong, (escape a).card := card_biUnion_le
    _ ≤ ∑ a ∈ wrong, weight a * b := sum_le_sum fun a ha => bound a (mem_filter.mp ha).2
    _ ≤ ∑ a, weight a * b := sum_le_sum_of_subset (subset_univ _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The signature's original per-field-role budget applies to any candidate
escape, with the same list-cardinality factor used in the analysis. -/
theorem candidate_field_card_le
    (FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat)
    (LD : ZkLigeroData C X Q Msg V asg)
    {bpair bround bin blig bquery : ℕ} (hb : ZkBudgets FD LD bpair bround bin blig bquery)
    (ms : ℕ → Msg) (i : Fin (Rounds.Role.length nl w)) (pref : Fin i.val → C)
    (hfield : i.val < Rounds.Role.layerBase w nl + 1) :
    (univ.filter fun c : C => candidateEscape
      (chain (nl := nl) (w := w) V H asg Sat LD ms) i pref c).card ≤
      mixedBudget (nl := nl) (w := w) (Fintype.card Lift) bpair bround bin 0 0
        (Rounds.Role.indexEquiv.symm i) := by
  have hslot : (Rounds.Role.indexEquiv.symm i).slot = i.val := by
    exact congrArg Fin.val (Rounds.Role.indexEquiv.apply_symm_apply i)
  cases hrole : Rounds.Role.indexEquiv.symm i with
  | layerPair ly =>
      simp only [mixedBudget, LfzkV1.RbrLayerStep.classBudget, ← sum_wt (Lift := Lift)]
      apply candidateEscape_card_le _ wt bpair i pref
      intro a ha
      simpa only [chain, layerStepChainS, stepAtS, hrole] using FD.budget_pair LD hb ms ly i.val pref a _ ha
  | sumcheck ly j =>
      simp only [mixedBudget, LfzkV1.RbrLayerStep.classBudget, ← sum_wt (Lift := Lift)]
      apply candidateEscape_card_le _ wt bround i pref
      intro a ha
      simpa only [chain, layerStepChainS, stepAtS, hrole] using FD.budget_round LD hb ms ly j i.val pref a _ ha
  | inputBind =>
      simp only [mixedBudget, LfzkV1.RbrLayerStep.classBudget, ← sum_wt (Lift := Lift)]
      apply candidateEscape_card_le _ wt bin i pref
      intro a ha
      simpa only [chain, layerStepChainS, stepAtS, hrole] using FD.budget_in LD hb ms i.val pref a _ ha
  | ligeroChallenge =>
      rw [hrole] at hslot
      simp only [Rounds.Role.slot] at hslot
      omega
  | ligeroQuery =>
      rw [hrole] at hslot
      simp only [Rounds.Role.slot] at hslot
      omega

/-- A circuit-invalid candidate satisfying the final built constraints has
a first wrong-to-right field transition on the actual verifier prefix. -/
theorem candidate_field_escape_of_built
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C) (x : Lift)
    (hwrong : ¬ Sat x) (sys : LigeroSystem ninp M F)
    (hb : (chain (nl := nl) (w := w) V H asg Sat LD ms).state
      (Rounds.Role.layerBase w nl + 1) (Bcs.trunc tape _ fieldLen_le) = .built sys)
    (hsat : sys.Sat (asg x).1 (asg x).2) :
    ∃ i : Fin (Rounds.Role.length nl w), i.val < Rounds.Role.layerBase w nl + 1 ∧
      candidateEscape (chain (nl := nl) (w := w) V H asg Sat LD ms) i
        (SumcheckV1.extract_prefix tape i) (tape i) := by
  let ch := chain (nl := nl) (w := w) V H asg Sat LD ms
  let u := Rounds.Role.layerBase w nl + 1
  let wrong (j : ℕ) :=
    if h : j ≤ Rounds.Role.length nl w then ch.Wrong (some x) (ch.state j (Bcs.trunc tape j h))
    else False
  have h0 : wrong 0 := by
    simp only [wrong, dif_pos (Nat.zero_le _)]
    exact hwrong
  have hu : ¬wrong u := by
    intro hw
    simp only [wrong, dif_pos (show u ≤ Rounds.Role.length nl w from fieldLen_le)] at hw
    change (chain (nl := nl) (w := w) V H asg Sat LD ms).Wrong (some x)
      ((chain (nl := nl) (w := w) V H asg Sat LD ms).state u (Bcs.trunc tape _ fieldLen_le)) at hw
    rw [hb] at hw
    exact hw.2 hsat
  obtain ⟨j, hj, hbad, hgood⟩ := Bcs.PotentialChain.field_escape_before u wrong h0 hu
  let i : Fin (Rounds.Role.length nl w) := ⟨j, lt_of_lt_of_le hj fieldLen_le⟩
  refine ⟨i, hj, some x, ?_, ?_⟩
  · rw [← Bcs.trunc_eq_extract_prefix]
    simpa only [wrong, dif_pos (show j ≤ Rounds.Role.length nl w from Nat.le_of_lt i.isLt)] using hbad
  · rw [← Bcs.trunc_succ]
    simpa only [wrong, dif_pos (show j + 1 ≤ Rounds.Role.length nl w from Nat.succ_le_of_lt i.isLt)] using hgood

end Field

section Point

open Merkle.MH LfzkV1.CompiledZk LfzkV1.CompiledLongfellowAdaptive LfzkV1.CompiledLongfellow
  LfzkV1.ZkLigeroV1 LfzkV1.RbrZkLongfellow LfzkV1.RbrZkSplit LfzkV1.RbrZkFlat
  LfzkV1.RbrLayerStepS LfzkV1.NizkDeployedHash LfzkV1.NizkZk

variable {C F Msg D Enc Salt X Ctx : Type} [Fintype C] [DecidableEq C]
  [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
  [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt] [DecidableEq Msg] [Inhabited Msg]
  {M nt nlin : ℕ} {hR : v7SigHahn.Valid}
  {codec : Codec Salt (Col F v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
  {dec : RoleDecoders codec}
variable (S : CircuitSide v7SigHahn hR v7SigHahn_openings_pos 8 C F Msg M nt nlin X dec Prod.snd)

private abbrev sigFieldSlots : ℕ :=
  Rounds.Role.layerBase v7SigHahn.params.rounds v7SigHahn.params.nl + 1

private abbrev SigPoint (Ctx Msg : Type) :=
  MPoint Ctx Msg v7SigHahn.params.nl v7SigHahn.params.rounds

private noncomputable abbrev sigChain (σ : Sig D C X Enc) (msgs : ℕ → Msg) :=
  let L := S.toSide.toZkSide
  chain (nl := v7SigHahn.params.nl) (w := v7SigHahn.params.rounds)
    (L.V σ) (L.H σ) (L.asg σ) (L.Sat σ) (flatData (L.LD σ)) msgs

private noncomputable abbrev sigPotential (σ : Sig D C X Enc) :=
  S.toSide.terminalPotential σ LfzkV1.GradedSignature.curve

def failedAt (σ : Sig D C X Enc) (sys : LigeroSystem S.c.ninp M F)
    (ch : ZkLigeroV1.Chal F v7SigHahn.params.nw v7SigHahn.params.nq nlin nt) (msg : Msg) : Prop :=
  terminalFailure (e := v7SigHahn.params.row.e) (g := v7SigHahn.params.row.g)
    (v7SigHahn.params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR))
    (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) v7SigHahn_openings_pos dec
      (σ.1.1.2, σ.1.2)) (stmtOf S.pl nlin sys) ch (S.respOf msg)

noncomputable def pointCharge (σ : Sig D C X Enc) (p : SigPoint Ctx Msg)
    (pref : Fin p.role.slot → C) (coin : C) : ℚ :=
  if hfield : p.role.slot < sigFieldSlots then
    if candidateEscape (sigChain S σ p.msgFn) p.role.index pref coin then 1 else 0
  else
    match (sigChain S σ p.msgFn).state sigFieldSlots (Bcs.trunc pref sigFieldSlots (by omega)) with
    | .built sys =>
      if batch : p.role.slot = sigFieldSlots then
        (sigPotential S σ).weight sys ((S.toSide.toZkSide.V σ).decodeChal coin)
      else
        let ch := (S.toSide.toZkSide.V σ).decodeChal (pref ⟨sigFieldSlots, by omega⟩)
        let msg := p.msgFn p.role.slot
        if failedAt S σ sys ch msg ∧
            (S.toSide.toZkSide.V σ).decodeQuery coin ∈ (S.toSide.toZkSide.LD σ).accepting p.role.slot pref msg sys ch
        then 1 - (sigPotential S σ).weight sys ch else 0
    | _ => 0

private theorem pointCharge_field (σ : Sig D C X Enc) (p : SigPoint Ctx Msg)
    (pref : Fin p.role.slot → C) (coin : C) (hfield : p.role.slot < sigFieldSlots) :
    pointCharge S σ p pref coin =
      if candidateEscape (sigChain S σ p.msgFn) p.role.index pref coin then 1 else 0 := by
  unfold pointCharge
  rw [dif_pos hfield]

theorem pointCharge_field_of (σ : Sig D C X Enc) (p : SigPoint Ctx Msg)
    (pref : Fin p.role.slot → C) (coin : C) (hfield : p.role.slot < sigFieldSlots)
    (hesc : candidateEscape (sigChain S σ p.msgFn) p.role.index pref coin) :
    pointCharge S σ p pref coin = 1 := by
  rw [pointCharge_field S σ p pref coin hfield, if_pos hesc]

theorem pointCharge_batch_eq (σ : Sig D C X Enc) (p : SigPoint Ctx Msg)
    (pref : Fin p.role.slot → C) (coin : C) (sys : LigeroSystem S.c.ninp M F)
    (hrole : p.role.slot = sigFieldSlots)
    (hstate : (sigChain S σ p.msgFn).state sigFieldSlots (Bcs.trunc pref sigFieldSlots hrole.ge) = .built sys) :
    pointCharge S σ p pref coin = (sigPotential S σ).weight sys ((S.toSide.toZkSide.V σ).decodeChal coin) := by
  unfold pointCharge
  rw [dif_neg (show ¬p.role.slot < sigFieldSlots by omega), hstate]
  dsimp only
  rw [dif_pos hrole]

private theorem pointCharge_opening (σ : Sig D C X Enc) (p : SigPoint Ctx Msg)
    (pref : Fin p.role.slot → C) (coin : C) (sys : LigeroSystem S.c.ninp M F)
    (hrole : sigFieldSlots < p.role.slot)
    (hstate : (sigChain S σ p.msgFn).state sigFieldSlots (Bcs.trunc pref sigFieldSlots hrole.le) = .built sys) :
    let ch := (S.toSide.toZkSide.V σ).decodeChal (pref ⟨sigFieldSlots, hrole⟩)
    let m := p.msgFn p.role.slot
    pointCharge S σ p pref coin =
      if failedAt S σ sys ch m ∧
          (S.toSide.toZkSide.V σ).decodeQuery coin ∈
            (S.toSide.toZkSide.LD σ).accepting p.role.slot pref m sys ch
      then 1 - (sigPotential S σ).weight sys ch else 0 := by
  unfold pointCharge
  rw [dif_neg (show ¬p.role.slot < sigFieldSlots by omega), hstate]
  dsimp only
  rw [dif_neg hrole.ne']

theorem pointCharge_opening_eq (σ : Sig D C X Enc) (p : SigPoint Ctx Msg)
    (pref : Fin p.role.slot → C) (coin : C) (sys : LigeroSystem S.c.ninp M F)
    (hrole : sigFieldSlots < p.role.slot)
    (hstate : (sigChain S σ p.msgFn).state sigFieldSlots (Bcs.trunc pref sigFieldSlots hrole.le) = .built sys)
    (hfailed : failedAt S σ sys ((S.toSide.toZkSide.V σ).decodeChal (pref ⟨sigFieldSlots, hrole⟩)) (p.msgFn p.role.slot))
    (hacc : (S.toSide.toZkSide.V σ).decodeQuery coin ∈ (S.toSide.toZkSide.LD σ).accepting p.role.slot pref (p.msgFn p.role.slot)
        sys ((S.toSide.toZkSide.V σ).decodeChal (pref ⟨sigFieldSlots, hrole⟩))) :
    pointCharge S σ p pref coin = 1 - (sigPotential S σ).weight sys ((S.toSide.toZkSide.V σ).decodeChal (pref ⟨sigFieldSlots, hrole⟩)) := by
  rw [pointCharge_opening S σ p pref coin sys hrole hstate]
  exact if_pos ⟨hfailed, hacc⟩

private theorem pointCharge_zero (σ : Sig D C X Enc) (p : SigPoint Ctx Msg)
    (pref : Fin p.role.slot → C) (coin : C) (hfield : sigFieldSlots ≤ p.role.slot)
    (hstate : ∀ sys, (sigChain S σ p.msgFn).state sigFieldSlots
      (Bcs.trunc pref sigFieldSlots hfield) ≠ .built sys) :
    pointCharge S σ p pref coin = 0 := by
  unfold pointCharge
  rw [dif_neg (Nat.not_lt.mpr hfield)]
  cases hs : (sigChain S σ p.msgFn).state sigFieldSlots (Bcs.trunc pref sigFieldSlots hfield) with
  | built sys => exact (hstate sys hs).elim
  | _ => rfl

theorem pointCharge_nonneg (σ : Sig D C X Enc) (p : SigPoint Ctx Msg)
    (pref : Fin p.role.slot → C) (coin : C) : 0 ≤ pointCharge S σ p pref coin := by
  by_cases hf : p.role.slot < sigFieldSlots
  · rw [pointCharge_field S σ p pref coin hf]
    split_ifs <;> positivity
  · have hl := Nat.le_of_not_gt hf
    by_cases hb : ∃ sys, (sigChain S σ p.msgFn).state sigFieldSlots
        (Bcs.trunc pref sigFieldSlots hl) = .built sys
    · obtain ⟨sys, hsys⟩ := hb
      rcases hl.eq_or_lt with he | ht
      · rw [pointCharge_batch_eq S σ p pref coin sys he.symm hsys]
        exact (sigPotential S σ).nonneg _ _
      · rw [pointCharge_opening S σ p pref coin sys ht hsys]
        split_ifs
        · exact sub_nonneg.mpr ((sigPotential S σ).le_one _ _)
        · exact le_rfl
    · rw [pointCharge_zero S σ p pref coin hl (not_exists.mp hb)]

theorem pointCharge_local (σ : Sig D C X Enc) (p : SigPoint Ctx Msg)
    (pref : Fin p.role.slot → C) :
    (∑ coin : C, pointCharge S σ p pref coin) ≤ SignatureBudget125.roleBudget C p.role := by
  let V := S.toSide.toZkSide.V σ
  let LD := S.toSide.toZkSide.LD σ
  let FD := S.toSide.toZkSide.FD σ
  let β := (Fintype.card C : ℚ) * (v7SigHahn.params.row.fail + v7SigHahn.params.row.arith)
  let γ := (Fintype.card C : ℚ) * v7SigHahn.params.row.cover
  have hβ : 0 ≤ β := mul_nonneg (Nat.cast_nonneg _) (add_nonneg
    (LigeroV1LayerStep.fail_nonneg v7SigHahn.params.row)
    (LigeroV1LayerStep.arith_nonneg v7SigHahn.params.row))
  have hγ : 0 ≤ γ := mul_nonneg (Nat.cast_nonneg _) (LigeroV1LayerStep.cover_nonneg v7SigHahn.params.row)
  have hc := (S.toSide.terminalPotential_challengeBudget_le_bound σ LfzkV1.GradedSignature.curve _
    SignatureBudget125.curve_challenge_le).trans_eq (max_eq_right hβ)
  have hq := (S.toSide.terminalPotential_queryBudget_le_bound σ LfzkV1.GradedSignature.curve _
    SignatureBudget125.curve_query_le).trans_eq (max_eq_right hγ)
  unfold SignatureBudget125.roleBudget sideUniformRoleBudget
  by_cases hfield : p.role.slot < sigFieldSlots
  · rw [if_pos hfield]
    have hsum : (∑ a : C, pointCharge S σ p pref a) =
        ((univ.filter fun c : C => candidateEscape (sigChain S σ p.msgFn) p.role.index pref c).card : ℚ) := by
      simp_rw [pointCharge_field S σ p pref _ hfield]
      rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [hsum]
    have hb := candidate_field_card_le FD (flatData LD) (flatBudgets (FD := FD) LD (S.toSide.toZkSide.budgets S.hF σ))
      p.msgFn p.role.index pref hfield
    rw [LfzkV1.NizkGrinding.indexEquiv_symm_index] at hb
    exact_mod_cast hb.trans (mixedBudget_mono (S.toSide.toZkSide.hcand σ) _ _ _ _ _ p.role)
  · rw [if_neg hfield]
    have hl := Nat.le_of_not_gt hfield
    by_cases hx : ∃ sys, (sigChain S σ p.msgFn).state sigFieldSlots
        (Bcs.trunc pref sigFieldSlots hl) = .built sys
    · obtain ⟨sys, hstate⟩ := hx
      by_cases hb : p.role.slot = sigFieldSlots
      · rw [if_pos hb]
        simp_rw [pointCharge_batch_eq S σ p pref _ sys hb hstate]
        have h := S.toSide.potential_challenge_hash_charge_le σ sys LfzkV1.GradedSignature.curve
          V.decodeChal FD.kchal FD.hbalChal
        exact h.trans ((le_max_right _ ( _ : ℚ)).trans hc)
      · rw [if_neg hb]
        have ht : sigFieldSlots < p.role.slot := by omega
        simp_rw [pointCharge_opening S σ p pref _ sys ht hstate]
        let ch := V.decodeChal (pref ⟨sigFieldSlots, by omega⟩)
        let msg := p.msgFn p.role.slot
        have h := query_charge_le (C := v7SigHahn.params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR))
          (oracle := extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) v7SigHahn_openings_pos dec
            (σ.1.1.2, σ.1.2)) (statement := stmtOf S.pl nlin sys)
          (e := v7SigHahn.params.row.e) (g := v7SigHahn.params.row.g) LfzkV1.GradedSignature.curve
          ch (S.respOf msg) V.decodeQuery FD.kq FD.hbalQuery
          (QuerySet.nonempty (LigeroV1Rows.Row.openings_le (Row.rowValid hR)))
        have he := (S.toSide.LD_acc σ)
        simp only [CompiledZkSide.toZkSide] at he ⊢
        rw [he]
        simp only [accZ, acceptingR, mem_filter, mem_univ, true_and]
        exact h.trans ((le_max_right _ (_ : ℚ)).trans hq)
    · simp_rw [pointCharge_zero S σ p pref _ hl (not_exists.mp hx)]
      rw [sum_const_zero]
      split_ifs
      · exact hβ
      · exact hγ

end Point

end LfzkV1.SignatureResponse125
