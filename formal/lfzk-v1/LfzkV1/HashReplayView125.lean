import LfzkV1.ReplayFieldTape125
import LfzkV1.ResidualReplay125Ligero

/-! The fixed-view replay split for the scheduled v1 hash side and its actual Ligero verifier. -/

open Finset LigeroFamily CodingTheory SumcheckV1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.HashReplayView125

open LfzkV1.ReplayView125 LfzkV1.ReplayDecode125 LfzkV1.ReplayFieldTape125
open LfzkV1.ResidualReplay125 LfzkV1.TwoFieldV1Rows
open LfzkV1.RbrZkLongfellow LfzkV1.Arith LfzkV1.ZkArithProfile LfzkV1.CompiledZk
open LfzkV1.CompiledLongfellow (ligIdx qryIdx)
open LfzkV1.NizkGrinding (indexEquiv_symm_index)
open Merkle.RandomOracle
open scoped Classical

section Fiber

attribute [local instance 10000] Classical.propDecidable

/-- A remaining accepted sample supplies the fixed replay data for its fiber. All remaining
accepts in that fiber pass the same selected assignment. For an identity replay, the good
completions are covered even if the other samples' full acceptance events differ. -/
theorem fiber_cover_or_replay {Sample View : Type} [Fintype Sample] [DecidableEq View]
    (observe : Sample → View) (v : View) (event covered : Sample → Prop)
    (error δ : ℚ) (herr : 0 ≤ error) (hδ : δ ≤ 1)
    (hrep : ∀ s : Sample, observe s = v → event s → ¬ covered s →
      ∃ passes hiddenBad : Sample → Prop,
        (∀ t, observe t = v → event t → ¬ covered t → passes t) ∧
        (((∀ t, observe t = v → passes t) ∧
          ((univ.filter fun t => observe t = v ∧ hiddenBad t).card : ℚ) ≤
            δ * (univ.filter fun t => observe t = v).card ∧
          (∀ t, observe t = v → passes t → ¬ hiddenBad t → covered t)) ∨
          ((univ.filter fun t => observe t = v ∧ passes t).card : ℚ) ≤
            error * (univ.filter fun t => observe t = v).card)) :
    ((univ.filter fun t => observe t = v ∧ event t ∧ ¬ covered t).card : ℚ) ≤
        error * (univ.filter fun t => observe t = v).card ∨
      (1 - δ) * ((univ.filter fun t => observe t = v ∧ event t).card : ℚ) ≤
        (univ.filter fun t => observe t = v ∧ covered t).card := by
  let fiber := univ.filter fun t => observe t = v
  let remaining := univ.filter fun t => observe t = v ∧ event t ∧ ¬ covered t
  change ((remaining.card : ℚ) ≤ error * fiber.card) ∨ _
  by_cases h : remaining.Nonempty
  · obtain ⟨s, hs⟩ := h
    obtain ⟨hview, he, hn⟩ := (mem_filter.mp hs).2
    obtain ⟨passes, bad, hpasses, hsplit⟩ := hrep s hview he hn
    rcases hsplit with ⟨hidem, hbad, hcover⟩ | hnon
    · right
      let badF := univ.filter fun t => observe t = v ∧ bad t
      let coveredF := univ.filter fun t => observe t = v ∧ covered t
      let eventF := univ.filter fun t => observe t = v ∧ event t
      have hsub : fiber ⊆ badF ∪ coveredF := by
        intro t ht
        have hv : observe t = v := (mem_filter.mp ht).2
        by_cases hb : bad t
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hv, hb⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hv, hcover t hv (hidem t hv) hb⟩)
      have hsum : (fiber.card : ℚ) ≤ badF.card + coveredF.card := by
        exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
      have hb : (badF.card : ℚ) ≤ δ * fiber.card := hbad
      have hsurv : (1 - δ) * (fiber.card : ℚ) ≤ coveredF.card := by linarith
      have hevent : (eventF.card : ℚ) ≤ fiber.card := by
        exact_mod_cast card_le_card (show eventF ⊆ fiber from
          fun t ht => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ht).2.1⟩)
      exact (mul_le_mul_of_nonneg_left hevent (sub_nonneg.mpr hδ)).trans hsurv
    · left
      have hsub : remaining ⊆ univ.filter (fun t => observe t = v ∧ passes t) := by
        intro t ht
        obtain ⟨hv, he, hn⟩ := (mem_filter.mp ht).2
        exact mem_filter.mpr ⟨mem_univ _, hv, hpasses t hv he hn⟩
      exact (by exact_mod_cast card_le_card hsub :
        (remaining.card : ℚ) ≤ (univ.filter fun t => observe t = v ∧ passes t).card).trans hnon
  · left
    have hz : remaining.card = 0 := by rw [card_eq_zero]; exact not_nonempty_iff_eq_empty.mp h
    simp [hz, mul_nonneg herr (Nat.cast_nonneg _)]

end Fiber

variable {C F Point Out Msg : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable [SumcheckV1Interp F] {fuel k : ℕ}
variable {c : QuadCircuit F} {M L logv : ℕ} {w : ℕ → ℕ}
variable {r qw n nw nq nlin nt : ℕ}
variable {tree : Tree Point C Out fuel} {lookups : Out → List Point} {H : Point → C}

local notation "Role" => Rounds.Role c.nl w
local notation "Tape" => Fin (Rounds.Role.length c.nl w) → C
local notation "Challenge" => Ligero.V1.Challenge F nw nq 1 (Equations nlin nt)
local notation "Query" => QuerySet n r
local notation "V1Oracle" => Ligero.V1.Oracle F nw nq n 1
local notation "Code" => ZkCode C F Challenge Query Msg (Fin logv → F) M c.ninp L 0

noncomputable def roleTape (points : Role → Point) (U : Point → C) : Tape :=
  fun j => U (points (Rounds.Role.indexEquiv.symm j))

omit [Fintype C] [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F] in
@[simp] theorem roleTape_index (points : Role → Point) (U : Point → C) (rl : Role) :
    roleTape points U rl.index = U (points rl) := by
  simp only [roleTape, indexEquiv_symm_index]

/-- The scheduled field build and the V1 verifier at the opened columns of the frozen oracle. -/
def Pass (V : Code) (ms : ℕ → Msg) (tape : Tape)
    (code : MultiplicativeCode F r qw n) (pl : Encode.Placement c.ninp M qw nw nq nt)
    (oracle : V1Oracle) (response : Response F r qw n 1)
    (assignment : LigeroAssignment c.ninp M F) : Prop :=
  ∃ sys, zkBuilt (w := w) V ms tape = some sys ∧ sys.Sat assignment.1 assignment.2 ∧
    let query := V.decodeQuery (tape qryIdx)
    SchemeVerifier.Accepts code Ligero.V1.scheme (Encode.encodeLig pl nlin sys)
      (V.decodeChal (tape ligIdx)) response query (openSchemeOracle oracle query)

variable (points : Rounds.Role c.nl w ↪ Point)
variable (indices : (Σ i : HiddenRole (tree := tree) (lookups := lookups) (H := H) points,
  Fin (roleWidth logv i.val)) ≃ Fin k)
variable (V : ZkCode C F (Ligero.V1.Challenge F nw nq 1 (Equations nlin nt))
  (QuerySet n r) Msg (Fin logv → F) M c.ninp L 0) (ms : ℕ → Msg)
variable (init : ExactDecoder C ((Fin logv → F) × F × F))
variable (pair : ExactDecoder C (F × F)) (scalar : ExactDecoder C F)

open Classical in
include indices in
/-- In a view freezing both terminal answers, the selected assignment either
passes identically throughout the view or pays one degree-81 residual. -/
theorem fixed_selected_view_split [Fintype Point]
    (hinit : init.decode = V.decodeInit) (hpair : pair.decode = V.decodePair)
    (hscalar : scalar.decode = V.decodeF) (pub : Fin c.ninp → F)
    (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (hpos : 0 < c.nl) {R : CertifiedV1.Row} (hR : V7HashProfile R)
    (hnl : c.nl = R.params.nl) (hw : w = R.params.rounds) (hlogv : logv ≤ 5)
    (hbatch : points .ligeroChallenge ∈ revealed tree lookups H)
    (hquery : points .ligeroQuery ∈ revealed tree lookups H)
    (code : MultiplicativeCode F r qw n) (pl : Encode.Placement c.ninp M qw nw nq nt)
    (oracle : V1Oracle) (response : Response F r qw n 1)
    (assignment : LigeroAssignment c.ninp M F)
    (hBuilt : ∃ sys, zkBuilt (w := w) V ms (roleTape points H) = some sys) :
    let pass := fun U : Point → C => Pass V ms (roleTape points U) code pl oracle response assignment
    (∀ U : Point → C, view tree lookups U = view tree lookups H → (pass U ↔ pass H)) ∨
      ((univ.filter fun U : Point → C =>
        view tree lookups U = view tree lookups H ∧ pass U).card : ℚ) ≤
        (81 / Fintype.card F) *
          ((univ.filter fun U : Point → C => view tree lookups U = view tree lookups H).card : ℚ) := by
  obtain ⟨S, hS, hRun⟩ :=
    system_of_view init pair scalar points indices V ms hinit hpair hscalar pub hV hst0
      hpos hR hnl hw hlogv hBuilt
  dsimp only
  let batch := V.decodeChal (H (points .ligeroChallenge))
  let query := V.decodeQuery (H (points .ligeroQuery))
  let opened := openSchemeOracle oracle query
  let d := fun i : HiddenRole (tree := tree) (lookups := lookups) (H := H) points =>
    roleDecoder init pair scalar i.val
  let coords (U : Point → C) := flatten indices fun i => (d i).decode (U (points i.val))
  let replayPass (U : Point → C) :=
    (S.eval (coords U)).Sat assignment.1 assignment.2 ∧
      SchemeVerifier.Accepts code Ligero.V1.scheme (Encode.encodeLig pl nlin (S.eval (coords U)))
        batch response query opened
  have hP (U : Point → C) (hview : view tree lookups U = view tree lookups H) :
      Pass V ms (roleTape points U) code pl oracle response assignment ↔ replayPass U := by
    have hf := (view_eq_iff tree lookups H U).mp hview
    have hU : zkBuilt (w := w) V ms (roleTape points U) = some (S.eval (coords U)) := hRun ⟨U, hview⟩
    have hb : V.decodeChal (roleTape points U ligIdx) = batch := by
      rw [roleTape_index, hf _ hbatch]
    have hq : V.decodeQuery (roleTape points U qryIdx) = query := by
      rw [roleTape_index, hf _ hquery]
    simp only [Pass, hU, hb, replayPass, Option.some.injEq, exists_eq_left']
    exact and_congr_right fun _ =>
      Iff.of_eq (congrArg (fun q =>
        SchemeVerifier.Accepts code Ligero.V1.scheme (Encode.encodeLig pl nlin (S.eval (coords U)))
          batch response q (openSchemeOracle oracle q)) hq)
  obtain ⟨_, hp⟩ | hb := fixed_opening_view_split (hiddenAddress points) d indices code
    Ligero.V1.scheme pl hS batch response query opened assignment.1 assignment.2
  · exact Or.inl fun U hview => (hP U hview).trans ((hp U).trans ((hp H).symm.trans (hP H rfl).symm))
  · right
    have hs : (univ.filter fun U : Point → C =>
          view tree lookups U = view tree lookups H ∧
            Pass V ms (roleTape points U) code pl oracle response assignment) =
        univ.filter fun U : Point → C => view tree lookups U = view tree lookups H ∧ replayPass U := by
      ext U
      simp only [mem_filter, mem_univ, true_and]
      exact and_congr_right (hP U)
    rw [hs]
    exact hb

end LfzkV1.HashReplayView125
