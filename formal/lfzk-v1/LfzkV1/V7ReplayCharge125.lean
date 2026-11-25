import LfzkV1.HashCircuitReplay125

/-! Charge a frozen v7 verifier replay by one residual or its healthy
completions. The selected lift and transcript addresses come from the
representative accepted proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.V7ReplayCharge125

open Bcs.TotalOracle Finset Merkle.MH Merkle.RandomOracle
open LfzkV1.CompiledZk LfzkV1.CertifiedV1 LfzkV1.SoundnessAudit
open LfzkV1.CompiledLongfellow (Col qryIdx)
open LfzkV1.CompiledLongfellowAdaptive (Sig)
open LfzkV1.NizkDeployedHash LfzkV1.ReplayView125 LfzkV1.ReplayDecode125 LfzkV1.ReplayFieldTape125
open LfzkV1.HashCircuitReplay125
open LfzkV1.LiftOpening125 (Compatible)
open scoped Classical

variable {C F Msg Enc D Salt X Ctx Point Out : Type}
variable [Fintype C] [Nonempty C] [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
variable [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt] [Inhabited Msg]
variable [Fintype Point] [DecidableEq Point]
variable {M nt nlin fuel : ℕ} {i : Fin 4}
variable {hR : (v7HashRow i).Valid} {hr : 0 < (v7HashRow i).params.row.openings}
variable {codec : Codec Salt (Col F (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {dec : RoleDecoders codec} {rootOfKey : D × D → D}
variable (side : CircuitSide (v7HashRow i) hR hr (v7HashLogv i) C F Msg M nt nlin X dec rootOfKey)

local notation "R" => v7HashRow i
local notation "Lift" => sideLiftAt side (HashCut125.radius i)

variable (tree : Tree Point C Out fuel) (lookups : Out → List Point)
variable (embed : HashFieldProfile125.HashPoint i Ctx Msg ↪ Point)
variable (ctx : Out → Ctx) (message : Out → ℕ → Msg)
variable (sig : (Point → C) → Sig D C X Enc)

noncomputable abbrev sampleCount {A : Type} [Fintype A] (event : A → Prop) : ℚ :=
  (@Finset.filter A event (fun x => Classical.propDecidable (event x)) univ).card

/-- The selected v7 replay uses one lift for every remaining acceptance in
a view. Every persistent healthy run is covered by an observed field
point or the ordered canonical-secondary cases. -/
theorem view_split_le [DecidableEq Out] [DecidableEq C]
    (event covered : (Point → C) → Prop)
    (hterminal : ∀ H, let out := (tree.run H).1
      let points := addresses embed (ctx out) (message out)
      points .ligeroChallenge ∈ revealed tree lookups H ∧
        points .ligeroQuery ∈ revealed tree lookups H)
    (hlookup : ∀ out j, j < Rounds.Role.layerBase (R).params.rounds (R).params.nl + 1 →
      embed (msgPoint (ctx out) message out j) ∉ lookups out)
    (hfrozen : ∀ H U, view tree lookups U = view tree lookups H → sig U = sig H)
    (hclassify : ∀ H, event H → ¬ covered H →
      let out := (tree.run H).1
      let tape := roleTape (addresses embed (ctx out) (message out)) H
      let query := (side.Vc (sig H).2.1 (sig H).2.2).decodeQuery (tape qryIdx)
      ∃ lift : Lift (sig H), ¬ (HashCut125.side side).Sat (sig H) lift ∧
        accepts side (sig H) (message out) tape lift ∧
        Compatible lift query (OpeningGeometry125.result i).certificate.g ∧
        ∀ y : Lift (sig H), Compatible y query (OpeningGeometry125.result i).certificate.g → lift = y)
    (hfield : ∀ H U, view tree lookups U = view tree lookups H →
      let out := (tree.run H).1
      (∃ j : Fin (Rounds.Role.length (R).params.nl (R).params.rounds),
        let p := msgPoint (ctx out) message out j.val
        embed p ∈ queried tree H ∧ HashFieldProfile125.bad side (sig H) p
          (mpoints.chal (U ∘ embed) p) (U (embed p))) → covered U)
    (hsecondary : ∀ H U, view tree lookups U = view tree lookups H →
      let out := (tree.run H).1
      let points := addresses embed (ctx out) (message out)
      ∀ lift, accepts side (sig H) (message out) (roleTape points U) lift →
        Compatible lift ((side.Vc (sig H).2.1 (sig H).2.2).decodeQuery (roleTape points U qryIdx))
          (OpeningGeometry125.result i).certificate.g →
        embed (msgPoint (ctx out) message out 0) ∈ queried tree H →
        HashFieldProfile125.canonicalSecondary side (sig H) (message out)
          (HashFieldProfile125.pointTape (ctx out) (U ∘ embed) (message out)) lift →
        covered U)
    (v : (Out × List (Point × C)) × List C) :
    sampleCount (fun U => view tree lookups U = v ∧ event U ∧ ¬ covered U) ≤
        (81 / 2^128) * (univ.filter fun U : Point → C => view tree lookups U = v).card ∨
      (1 - 2^14 / 2^128) *
        sampleCount (fun U => view tree lookups U = v ∧ event U) ≤
        sampleCount (fun U => view tree lookups U = v ∧ covered U) := by
  classical
  apply HashReplayView125.fiber_cover_or_replay (view tree lookups) v event covered
    (81 / 2^128) (2^14 / 2^128) (by norm_num) (by norm_num)
  intro H hview he hn
  let out := (tree.run H).1
  let points := addresses embed (ctx out) (message out)
  obtain ⟨lift, hf, hpass, hcomp, huniq⟩ := hclassify H he hn
  let passes (U : Point → C) := accepts side (sig H) (message out) (roleTape points U) lift
  let hidden (U : Point → C) :=
    hiddenFieldBad side (sig H) embed (ctx out) (message out) (revealed tree lookups H) U
  have ht := hterminal H
  refine ⟨passes, hidden, ?_, ?_⟩
  · intro U hv hU hUc
    have hv' := hv.trans hview.symm
    have hout : (tree.run U).1 = out := congrArg (fun x => x.1.1) hv'
    have hcut := hfrozen H U hv'
    have hu := hclassify U hU hUc
    dsimp only at hu
    rw [hout, hcut] at hu
    obtain ⟨lift', _, hp, hc, _⟩ := hu
    have hcq : roleTape points U qryIdx = roleTape points H qryIdx :=
      roleTape_eq_of_view points .ligeroQuery ht.2 hv'
    rw [hcq] at hc
    obtain rfl := huniq lift' hc
    exact hp
  let indices := Fintype.equivFin (Σ j : HiddenRole (tree := tree) (lookups := lookups) (H := H) points,
    Fin (roleWidth (v7HashLogv i) j.val))
  have hs := selected_view_split (tree := tree) (lookups := lookups) (H := H) side (sig H)
    (message out) points indices ht.1 ht.2 lift hpass
  rcases hs with hs | hs
  · left
    refine ⟨fun U hv => hs U (hv.trans hview.symm), ?_, ?_⟩
    · have hh := hidden_field_count_le (tree := tree) (lookups := lookups) (H := H)
        side (sig H) embed (ctx out) (message out)
      have hlen : Rounds.Role.length (R).params.nl (R).params.rounds ≤ 1200 := by
        fin_cases i <;> decide
      have hrate : (((Rounds.Role.length (R).params.nl (R).params.rounds : ℚ) + 1) *
          (7 / 2^128)) ≤ 2^14 / 2^128 := by
        have hsize : (Rounds.Role.length (R).params.nl (R).params.rounds : ℚ) ≤ 1200 :=
          by exact_mod_cast hlen
        linarith
      rw [← hview]
      convert hh.trans (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg _)) using 2
      all_goals first
        | rfl
        | apply congrArg (fun s : Finset (Point → C) => (s.card : ℚ))
          ext U
          simp
    · intro U hv hp hh
      have hv' := hv.trans hview.symm
      rcases healthy_pass_cover (tree := tree) (lookups := lookups) (H := H)
          side (sig H) embed (ctx out) (message out) U lift hf hp (hlookup out) hh with
        hbad | ⟨hinit, hcanon⟩
      · exact hfield H U hv' hbad
      · have hq : roleTape points U qryIdx = roleTape points H qryIdx :=
          roleTape_eq_of_view points .ligeroQuery ht.2 hv'
        apply hsecondary H U hv' lift hp _ hinit hcanon
        change Compatible lift ((side.Vc (sig H).2.1 (sig H).2.2).decodeQuery (roleTape points U qryIdx)) _
        rw [hq]
        exact hcomp
  · right
    have hq : Fintype.card F = 2^128 := by
      rw [side.hF]
      fin_cases i <;> rfl
    rw [← hview]
    simp only [hq, Nat.cast_pow, Nat.cast_ofNat] at hs
    convert hs using 2
    all_goals first
      | rfl
      | apply congrArg (Finset.card (α := Point → C))
        ext U
        simp [passes]
      | apply congrArg (fun s : Finset (Point → C) => (s.card : ℚ))
        ext U
        simp

end LfzkV1.V7ReplayCharge125
