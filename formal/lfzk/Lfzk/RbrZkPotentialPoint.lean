import Lfzk.RbrZkPotentialData
import Lfzk.NizkDeployedHash
import Lfzk.NizkZkDeployedHash
import Lfzk.CompiledZk

/-!
# The graded charge at a deployed Longfellow side hash input

An input carries its role and all prover messages through that role.  Its
ancestor answers give the preceding verifier transcript.  The field roles
charge a doom escape; the combination challenge receives its agreement
potential; the last query receives the residual if its opened columns pass.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkFlat

open Finset Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.RbrLayerStepS
  Lfzk.NizkGrinding Lfzk.NizkDeployedHash Lfzk.CompiledZk
  Lfzk.CompiledLongfellow
open scoped Classical

variable {C F X Q Msg Gpt Lift Ctx : Type} [Fintype C] [Field F]
  [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Inhabited Msg]
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc}
variable {H : ZkHonest F Lift logw logc}
variable {asg : Lift → LigeroAssignment ninp M F} {Sat : Lift → Prop}

/-- The pointwise rational charge.  A field escape costs one.  The two
terminal roles use the same potential of the system built before the
combination challenge, with the last role paying only for an accepting
query.  The `Fits ∧ NoSat` guard makes both terminal local budgets apply. -/
noncomputable def sidePointCharge
    (LD : ZkLigeroData C X Q Msg V asg)
    (P : TerminalPotential LD)
    (p : MPoint Ctx Msg nl w)
    (pref : Fin (mpoints.slot p) → C) (c : C) : ℚ :=
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) p.msgFn
  let u := Rounds.Role.layerBase w nl + 1
  if hfield : p.role.slot < u then
    if ch.doomed p.role.slot pref ∧
        ¬ ch.doomed (p.role.slot + 1) (Bcs.extend pref c) then 1 else 0
  else if hchallenge : p.role.slot = u then
    match ch.state u (Bcs.trunc pref u (by change u ≤ p.role.slot; omega)) with
    | .built sys =>
        if Fits V sys ∧ NoSat asg sys then P.weight sys (V.decodeChal c) else 0
    | _ => 0
  else
    match ch.state u (Bcs.trunc pref u (by change u ≤ p.role.slot; omega)) with
    | .built sys =>
        if Fits V sys ∧ NoSat asg sys ∧
            V.decodeQuery c ∈ LD.accepting p.role.slot pref
              (p.msgFn p.role.slot) sys
              (V.decodeChal (pref ⟨u, by change u < p.role.slot; omega⟩)) then
          1 - P.weight sys (V.decodeChal
            (pref ⟨u, by change u < p.role.slot; omega⟩))
        else 0
    | _ => 0

omit [Fintype F] [DecidableEq F] [Fintype Gpt] [DecidableEq Gpt]
  [DecidableEq X] in
theorem sidePointCharge_nonneg
    (LD : ZkLigeroData C X Q Msg V asg)
    (P : TerminalPotential LD)
    (p : MPoint Ctx Msg nl w)
    (pref : Fin (mpoints.slot p) → C) (c : C) :
    0 ≤ sidePointCharge (H := H) (Sat := Sat) LD P p pref c := by
  unfold sidePointCharge
  dsimp
  split_ifs <;> try positivity
  all_goals try (split <;> try split_ifs)
  all_goals
    first
    | positivity
    | exact P.nonneg _ _
    | exact sub_nonneg.mpr (P.le_one _ _)

/-- Exact local answer sum for the point charge.  The field roles retain the
existing list-scaled sumcheck budget; the final two roles use the full
agreement-tail and residual-query budgets from `TerminalPotential`. -/
theorem sidePointCharge_local [Fintype Lift]
    (FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat)
    (LD : ZkLigeroData C X Q Msg V asg)
    (P : TerminalPotential LD)
    {bpair bround bin blig bquery : ℕ}
    (hB : ZkBudgets FD LD bpair bround bin blig bquery)
    (p : MPoint Ctx Msg nl w) (pref : Fin (mpoints.slot p) → C) :
    (∑ c : C, sidePointCharge (H := H) (Sat := Sat) LD P p pref c) ≤
      if p.role.slot < Rounds.Role.layerBase w nl + 1 then
        (mixedBudget (nl := nl) (w := w) (Fintype.card Lift)
          bpair bround bin 0 (FD.kq * Fintype.card Q) p.role : ℚ)
      else if p.role.slot = Rounds.Role.layerBase w nl + 1 then
        P.challengeBudget else P.queryBudget := by
  classical
  let u := Rounds.Role.layerBase w nl + 1
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) p.msgFn
  by_cases hfield : p.role.slot < Rounds.Role.layerBase w nl + 1
  · rw [if_pos hfield]
    by_cases hd : ch.doomed p.role.slot pref
    · have hflat := flatBudgets (FD := FD) LD hB
      let i : Fin (Rounds.Role.length nl w) := p.role.index
      have hcnt := FD.doom_preserved_chain (flatData LD) hflat p.msgFn i pref hd
      rw [indexEquiv_symm_index] at hcnt
      have hcnt' : ((univ.filter fun c : C =>
          ¬ ch.doomed (p.role.slot + 1) (Bcs.extend pref c)).card : ℚ) ≤
          (mixedBudget (nl := nl) (w := w) (Fintype.card Lift)
            bpair bround bin 0 (FD.kq * Fintype.card Q) p.role : ℚ) := by
        exact_mod_cast hcnt
      simpa [sidePointCharge, hfield, hd, ch, Finset.sum_ite] using hcnt'
    · change ¬ (chain (nl := nl) (w := w) V H asg Sat
        (flatData LD) p.msgFn).doomed p.role.slot pref at hd
      simp [sidePointCharge, hfield, hd]
  · rw [if_neg hfield]
    by_cases hchallenge : p.role.slot = Rounds.Role.layerBase w nl + 1
    · rw [if_pos hchallenge]
      cases hs : ch.state u (Bcs.trunc pref u (by change u ≤ p.role.slot; omega)) with
      | built sys =>
        by_cases hg : Fits V sys ∧ NoSat asg sys
        · simpa [sidePointCharge, hfield, hchallenge, hs, ch, u, hg] using
            (P.challenge_le sys hg.1 hg.2)
        · simpa [sidePointCharge, hfield, hchallenge, hs, ch, u, hg] using
            P.challengeBudget_nonneg
      | start => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.challengeBudget_nonneg
      | running zs => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.challengeBudget_nonneg
      | challenged sys x => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.challengeBudget_nonneg
      | accepted => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.challengeBudget_nonneg
      | failed => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.challengeBudget_nonneg
    · rw [if_neg hchallenge]
      cases hs : ch.state u (Bcs.trunc pref u (by change u ≤ p.role.slot; omega)) with
      | built sys =>
        by_cases hg : Fits V sys ∧ NoSat asg sys
        · have hq := P.query_le p.role.slot pref (p.msgFn p.role.slot) sys
            (V.decodeChal (pref ⟨u, by change u < p.role.slot; omega⟩))
            hg.1 hg.2
          simpa [sidePointCharge, hfield, hchallenge, hs, ch, u, hg] using hq
        · have hz : ∀ c : C, ¬ (Fits V sys ∧ NoSat asg sys ∧
              V.decodeQuery c ∈ LD.accepting p.role.slot pref
                (p.msgFn p.role.slot) sys
                (V.decodeChal (pref ⟨u, by change u < p.role.slot; omega⟩))) := by
            intro c h
            exact hg ⟨h.1, h.2.1⟩
          simpa [sidePointCharge, hfield, hchallenge, hs, ch, u, hz] using
            P.queryBudget_nonneg
      | start => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.queryBudget_nonneg
      | running zs => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.queryBudget_nonneg
      | challenged sys x => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.queryBudget_nonneg
      | accepted => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.queryBudget_nonneg
      | failed => simpa [sidePointCharge, hfield, hchallenge, hs, ch, u] using
          P.queryBudget_nonneg

omit [Fintype F] [DecidableEq F] [Fintype Gpt] [DecidableEq Gpt]
  [DecidableEq X] in
/-- A field-round escape on the verifier's actual message schedule makes
the corresponding deployed hash point pay one unit.  This uses the existing
causal message-prefix transfer, so a prover may have queried that point
earlier without changing the charge. -/
theorem sidePointCharge_field_escape
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (k : Fin (Rounds.Role.length nl w))
    (hk : k.val < Rounds.Role.layerBase w nl + 1)
    (hd : (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
      (msgOf out)).doomed k.val
        (Sumcheck.extract_prefix
          (fun i : Fin (Rounds.Role.length nl w) =>
            ro (msgPoint ctx msgOf out i.val)) k))
    (he : ¬ (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
      (msgOf out)).doomed (k.val + 1)
        (Bcs.extend (Sumcheck.extract_prefix
          (fun i : Fin (Rounds.Role.length nl w) =>
            ro (msgPoint ctx msgOf out i.val)) k)
          (ro (msgPoint ctx msgOf out k.val)))) :
    1 ≤ sidePointCharge (H := H) (Sat := Sat) LD P
      (msgPoint ctx msgOf out k.val)
      (mpoints.chal ro (msgPoint ctx msgOf out k.val))
      (ro (msgPoint ctx msgOf out k.val)) := by
  have hsh := shed_at_msgPoint_of
    (fun ms j pref =>
      (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).doomed j pref)
    (fun ms ms' j h pref =>
      Lfzk.NizkZkDeployedHash.zkChain_doomed_congr
        V H asg Sat (flatData LD) ms ms' j h pref)
    ctx msgOf out ro k hd he
  have hs := slot_msgPoint ctx msgOf out k.isLt
  let pt := msgPoint (nl := nl) (w := w) ctx msgOf out k.val
  have hs' : pt.role.slot = k.val := hs
  have hf : pt.role.slot ≤ Rounds.Role.layerBase w nl := by omega
  have hdo : (chain (nl := nl) (w := w) V H asg Sat
      (flatData LD) pt.msgFn).doomed pt.role.slot (mpoints.chal ro pt) := hsh.1
  have hno : ¬ (chain (nl := nl) (w := w) V H asg Sat
      (flatData LD) pt.msgFn).doomed (pt.role.slot + 1)
        (Bcs.extend (mpoints.chal ro pt) (ro pt)) := hsh.2
  simp [sidePointCharge, hf, hdo, hno, pt]

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] in
/-- The built system before Ligero's combination challenge is the same at
the full verifier tape and at either terminal deployed hash point.  The
point contains every earlier message and every earlier challenge answer. -/
theorem sidePoint_built_state_of_verifier
    (LD : ZkLigeroData C X Q Msg V asg)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (k : Fin (Rounds.Role.length nl w))
    (hk : Rounds.Role.layerBase w nl + 1 ≤ k.val)
    (sys : LigeroSystem ninp M F)
    (hstate :
      let tape : Fin (Rounds.Role.length nl w) → C :=
        fun i => ro (msgPoint ctx msgOf out i.val)
      (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
        (msgOf out)).state (Rounds.Role.layerBase w nl + 1)
          (Bcs.trunc tape (Rounds.Role.layerBase w nl + 1) (by omega)) = .built sys) :
    let p := msgPoint (nl := nl) (w := w) ctx msgOf out k.val
    (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
      p.msgFn).state (Rounds.Role.layerBase w nl + 1)
        (Bcs.trunc (mpoints.chal ro p) (Rounds.Role.layerBase w nl + 1)
          (by rw [slot_msgPoint ctx msgOf out k.isLt]; exact hk)) = .built sys := by
  let u := Rounds.Role.layerBase w nl + 1
  let p := msgPoint (nl := nl) (w := w) ctx msgOf out k.val
  let tape : Fin (Rounds.Role.length nl w) → C :=
    fun i => ro (msgPoint ctx msgOf out i.val)
  have hpre : Bcs.trunc (mpoints.chal ro p) u
      (by rw [slot_msgPoint ctx msgOf out k.isLt]; exact hk) =
      Bcs.trunc tape u (by omega) := by
    funext j
    change ro (mpoints.anc p j.val) =
      ro (msgPoint ctx msgOf out j.val)
    exact congrArg ro (anc_msgPoint ctx msgOf out (by omega) k.isLt)
  have hmsg : ∀ i, i < u → p.msgFn i = msgOf out i := by
    intro i hi
    exact msgFn_msgPoint ctx msgOf out k.isLt (by omega)
  change (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
    p.msgFn).state u (Bcs.trunc (mpoints.chal ro p) u
      (by rw [slot_msgPoint ctx msgOf out k.isLt]; exact hk)) = .built sys
  calc
    _ = (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
          p.msgFn).state u (Bcs.trunc tape u (by omega)) := by rw [hpre]
    _ = (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
          (msgOf out)).state u (Bcs.trunc tape u (by omega)) :=
      Lfzk.NizkZk.state_congrG
        (Lfzk.NizkZk.zkChain_msgLocal V H asg Sat (flatData LD))
        u hmsg (Bcs.trunc tape u (by omega))
    _ = .built sys := hstate

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [Inhabited Msg] in
/-- Acceptance gives the built system at the exact prefix read by the
potential, together with the final opened-column test.  The terminal-pair
doom marker changes neither verifier transition nor this state. -/
theorem accepted_built_and_query
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C)
    (hacc : ZkLayerStepAccepts .accepted .start
      (steps (nl := nl) (w := w) V LD ms) tape) :
    ∃ sys : LigeroSystem ninp M F,
      (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).state
        (Rounds.Role.layerBase w nl + 1)
        (Bcs.trunc tape (Rounds.Role.layerBase w nl + 1) fieldLen_le) = .built sys ∧
      V.decodeQuery (tape qryIdx) ∈
        LD.accepting (Rounds.Role.layerBase w nl + 2)
          (Bcs.trunc tape _ queryLen_le) (ms (Rounds.Role.layerBase w nl + 2))
          sys (V.decodeChal (tape ligIdx)) := by
  let acc : ∀ m : ℕ, (Fin m → C) → LigeroSystem ninp M F → X → Finset Q :=
    fun m pref => LD.accepting m pref (ms m)
  have ha : ZkLayerStepAccepts .accepted .start
      (zkSteps nl w V ms acc) tape := hacc
  obtain ⟨sys, hb, hq⟩ := (zkAccepts_iff V ms acc tape).mp ha
  refine ⟨sys, ?_, hq⟩
  have hb' := builtOf_eq_some.mp hb
  let pref := Bcs.trunc tape (Rounds.Role.layerBase w nl + 1) fieldLen_le
  calc
    (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).state
        (Rounds.Role.layerBase w nl + 1) pref =
      (zkRun (nl := nl) (w := w) V ms acc).state
        (Rounds.Role.layerBase w nl + 1) pref :=
      state_eq_of (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms)
        (zkRun (nl := nl) (w := w) V ms acc) rfl rfl _ pref
    _ = (zkRun (nl := nl) (w := w) V ms (fun _ _ _ _ => ∅)).state
        (Rounds.Role.layerBase w nl + 1) pref :=
      zk_state_acc_congr V ms acc (fun _ _ _ _ => ∅)
        _ (by omega) pref
    _ = .built sys := hb'

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [Inhabited Msg] in
/-- A doomed accepted terminal prefix is precisely a built system which
fits the code and has no satisfying decoded candidate. -/
theorem accepted_doomed_terminal
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C)
    (hacc : ZkLayerStepAccepts .accepted .start
      (steps (nl := nl) (w := w) V LD ms) tape)
    (hdoom : (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).doomed
      (Rounds.Role.layerBase w nl + 1)
      (Bcs.trunc tape (Rounds.Role.layerBase w nl + 1) fieldLen_le)) :
    ∃ sys : LigeroSystem ninp M F,
      (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).state
        (Rounds.Role.layerBase w nl + 1)
        (Bcs.trunc tape (Rounds.Role.layerBase w nl + 1) fieldLen_le) = .built sys ∧
      Fits V sys ∧ NoSat asg sys ∧
      V.decodeQuery (tape qryIdx) ∈
        LD.accepting (Rounds.Role.layerBase w nl + 2)
          (Bcs.trunc tape _ queryLen_le) (ms (Rounds.Role.layerBase w nl + 2))
          sys (V.decodeChal (tape ligIdx)) := by
  obtain ⟨sys, hs, hq⟩ := accepted_built_and_query (H := H) (Sat := Sat)
    LD ms tape hacc
  refine ⟨sys, hs, ?_⟩
  have hd : ∀ cand : Option Lift,
      ZkWrong V H asg Sat (flatData LD).LigDoomed cand (.built sys) := by
    intro cand
    have hd' := hdoom cand
    change ZkWrong V H asg Sat (flatData LD).LigDoomed cand
      ((chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).state
        (Rounds.Role.layerBase w nl + 1)
        (Bcs.trunc tape (Rounds.Role.layerBase w nl + 1) fieldLen_le)) at hd'
    rw [hs] at hd'
    exact hd'
  obtain ⟨hf, hn⟩ := (doomed_built_iff V H asg Sat (flatData LD).LigDoomed sys).mp hd
  exact ⟨hf, hn, hq⟩

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [Inhabited Msg] in
/-- Flat extraction's concrete event inclusion: an accepted bad transcript
either loses doom at a field role or reaches a built `Fits ∧ NoSat` system
whose final Ligero query passes.  The challenge and query remain a joint
terminal event for the subsequent probability bound. -/
theorem accepted_field_escape_or_noSat_query
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C)
    (hfalse : ∀ ℓ : Lift, ¬ Sat ℓ)
    (hacc : ZkLayerStepAccepts .accepted .start
      (steps (nl := nl) (w := w) V LD ms) tape) :
    let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
    let u := Rounds.Role.layerBase w nl + 1
    (∃ i < u, prefixDoom ch tape i ∧ ¬ prefixDoom ch tape (i + 1)) ∨
      ∃ sys : LigeroSystem ninp M F,
        ch.state u (Bcs.trunc tape u fieldLen_le) = .built sys ∧
        Fits V sys ∧ NoSat asg sys ∧
        V.decodeQuery (tape qryIdx) ∈
          LD.accepting (u + 1) (Bcs.trunc tape _ queryLen_le)
            (ms (u + 1)) sys (V.decodeChal (tape ligIdx)) := by
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  let u := Rounds.Role.layerBase w nl + 1
  have h0 : prefixDoom ch tape 0 := by
    simp only [prefixDoom, dif_pos (Nat.zero_le _)]
    intro cand
    cases cand with
    | none => trivial
    | some ℓ => exact hfalse ℓ
  by_cases hu : prefixDoom ch tape u
  · right
    have hdu : ch.doomed u (Bcs.trunc tape u fieldLen_le) := by
      dsimp only [prefixDoom] at hu
      split at hu
      · exact hu
      · have hlen : u ≤ Rounds.Role.length nl w := fieldLen_le
        omega
    simpa only [ch, u] using
      (accepted_doomed_terminal (H := H) (Sat := Sat) LD ms tape hacc hdu)
  · left
    exact Bcs.PotentialChain.field_escape_before u (prefixDoom ch tape) h0 hu

omit [Fintype F] [DecidableEq F] [Fintype Gpt] [DecidableEq Gpt]
  [DecidableEq X] in
/-- At the combination-challenge point of a doomed built system, the
pointwise charge is exactly its full agreement potential. -/
theorem sidePointCharge_challenge_eq
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    (p : MPoint Ctx Msg nl w)
    (hrole : p.role.slot = Rounds.Role.layerBase w nl + 1)
    (pref : Fin (mpoints.slot p) → C) (c : C)
    (sys : LigeroSystem ninp M F)
    (hstate : (chain (nl := nl) (w := w) V H asg Sat
      (flatData LD) p.msgFn).state
        (Rounds.Role.layerBase w nl + 1)
        (Bcs.trunc pref (Rounds.Role.layerBase w nl + 1)
          (by change Rounds.Role.layerBase w nl + 1 ≤ p.role.slot; omega)) = .built sys)
    (hf : Fits V sys) (hn : NoSat asg sys) :
    sidePointCharge (H := H) (Sat := Sat) LD P p pref c =
      P.weight sys (V.decodeChal c) := by
  simp [sidePointCharge, hrole, hstate, hf, hn]

omit [Fintype F] [DecidableEq F] [Fintype Gpt] [DecidableEq Gpt]
  [DecidableEq X] in
/-- At the final query point, a passing opened-column test pays the
residual potential of the same built system and preceding challenge. -/
theorem sidePointCharge_query_eq
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    (p : MPoint Ctx Msg nl w)
    (hrole : p.role.slot = Rounds.Role.layerBase w nl + 2)
    (pref : Fin (mpoints.slot p) → C) (c : C)
    (sys : LigeroSystem ninp M F)
    (hstate : (chain (nl := nl) (w := w) V H asg Sat
      (flatData LD) p.msgFn).state
        (Rounds.Role.layerBase w nl + 1)
        (Bcs.trunc pref (Rounds.Role.layerBase w nl + 1)
          (by change Rounds.Role.layerBase w nl + 1 ≤ p.role.slot; omega)) = .built sys)
    (hf : Fits V sys) (hn : NoSat asg sys)
    (hq : V.decodeQuery c ∈ LD.accepting p.role.slot pref
      (p.msgFn p.role.slot) sys
      (V.decodeChal (pref ⟨Rounds.Role.layerBase w nl + 1,
        by change Rounds.Role.layerBase w nl + 1 < p.role.slot; omega⟩))) :
    sidePointCharge (H := H) (Sat := Sat) LD P p pref c =
      1 - P.weight sys
        (V.decodeChal (pref ⟨Rounds.Role.layerBase w nl + 1,
          by change Rounds.Role.layerBase w nl + 1 < p.role.slot; omega⟩)) := by
  have hfield : ¬ p.role.slot < Rounds.Role.layerBase w nl + 1 := by omega
  have hchallenge : ¬ p.role.slot = Rounds.Role.layerBase w nl + 1 := by omega
  simp [sidePointCharge, hfield, hchallenge, hstate, hf, hn, hq]

end Lfzk.RbrZkFlat
