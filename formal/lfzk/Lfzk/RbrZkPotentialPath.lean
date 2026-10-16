import Lfzk.RbrZkFlatTape

/-!
# A graded potential on an accepted deployed Longfellow side transcript

The extraction-failure event pays one unit on its actual verifier path.  A
field escape pays the unit at one field hash input.  If the field state
remains doomed, the actual combination challenge pays its agreement weight
and the accepted column query pays the residual.  This is a pathwise theorem;
the oracle-grinding bound is applied separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkFlat

open Finset Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit
  Lfzk.CompiledZk Lfzk.CompiledLongfellow Lfzk.NizkDeployedHash
open scoped Classical

private theorem accepting_eq_of_prefix
    {C Msg S X Q : Type}
    (acc : ∀ m : ℕ, (Fin m → C) → Msg → S → X → Finset Q)
    {m n : ℕ} (hm : m = n) (p : Fin m → C) (q : Fin n → C)
    (hp : ∀ i, p i = q (Fin.cast hm i))
    {msg msg' : Msg} (hmsg : msg = msg') (s : S)
    {x x' : X} (hx : x = x') :
    acc m p msg s x = acc n q msg' s x' := by
  subst n
  have hp' : p = q := by
    funext i
    simpa using hp i
  subst p
  subst msg'
  subst x'
  rfl

variable {C F X Q Msg Gpt Lift Ctx : Type} [Fintype C] [Field F]
  [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Inhabited Msg]
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc}
variable {H : ZkHonest F Lift logw logc}
variable {asg : Lift → LigeroAssignment ninp M F} {Sat : Lift → Prop}

noncomputable def sideTraceCharge
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (i : Fin (Rounds.Role.length nl w)) : ℚ :=
  let p := msgPoint (nl := nl) (w := w) ctx msgOf out i.val
  sidePointCharge (H := H) (Sat := Sat) LD P p (mpoints.chal ro p) (ro p)

omit [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] in
theorem sideTraceCharge_nonneg
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (i : Fin (Rounds.Role.length nl w)) :
    0 ≤ sideTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro i :=
  sidePointCharge_nonneg LD P _ _ _

omit [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] in
/-- A field-prefix escape pays on a field slot alone.  This isolates the
part of the path argument that does not use either terminal Ligero answer. -/
theorem field_escape_sideTrace_pays
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (hfield :
      let tape : Fin (Rounds.Role.length nl w) → C :=
        fun i => ro (msgPoint ctx msgOf out i.val)
      let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) (msgOf out)
      ∃ i : Fin (Rounds.Role.layerBase w nl + 1),
        ch.doomed i.val (Bcs.trunc tape i.val
          (by dsimp [Rounds.Role.length]; omega)) ∧
        ¬ ch.doomed (i.val + 1) (Bcs.trunc tape (i.val + 1)
          (by dsimp [Rounds.Role.length]; omega))) :
    1 ≤ ∑ i : Fin (Rounds.Role.length nl w),
      sideTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro i := by
  dsimp only at hfield
  obtain ⟨k, hd, he⟩ := hfield
  let tape : Fin (Rounds.Role.length nl w) → C :=
    fun i => ro (msgPoint ctx msgOf out i.val)
  have hd' :
      (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
        (msgOf out)).doomed k.val
        (Sumcheck.extract_prefix tape
          (⟨k.val, by dsimp [Rounds.Role.length]; omega⟩ :
            Fin (Rounds.Role.length nl w))) := by
    rw [← Bcs.trunc_eq_extract_prefix]
    exact hd
  have he' :
      ¬ (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
        (msgOf out)).doomed (k.val + 1)
        (Bcs.extend (Sumcheck.extract_prefix tape
          (⟨k.val, by dsimp [Rounds.Role.length]; omega⟩ :
            Fin (Rounds.Role.length nl w)))
          (tape ⟨k.val, by dsimp [Rounds.Role.length]; omega⟩)) := by
    rw [← Bcs.trunc_succ]
    exact he
  have hpay := sidePointCharge_field_escape (H := H) (Sat := Sat)
    LD P ctx msgOf out ro
    (⟨k.val, by dsimp [Rounds.Role.length]; omega⟩ :
      Fin (Rounds.Role.length nl w)) k.isLt hd' he'
  apply Bcs.PotentialChain.one_or_two_slots_pay
    (sideTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro)
    (sideTraceCharge_nonneg LD P ctx msgOf out ro)
  left
  exact ⟨⟨k.val, by dsimp [Rounds.Role.length]; omega⟩, hpay⟩

/-- The hash-side charge used when its terminal event is bounded directly. -/
noncomputable def sideFieldTraceCharge
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (i : Fin (Rounds.Role.length nl w)) : ℚ :=
  if i.val < Rounds.Role.layerBase w nl + 1 then
    sideTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro i
  else 0

/-- The corresponding pointwise charge for the adaptive-oracle compiler. -/
noncomputable def sideFieldPointCharge
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    (p : MPoint Ctx Msg nl w)
    (pref : Fin (mpoints.slot p) → C) (c : C) : ℚ :=
  if p.role.slot < Rounds.Role.layerBase w nl + 1 then
    sidePointCharge (H := H) (Sat := Sat) LD P p pref c
  else 0

omit [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] in
theorem sideFieldPointCharge_nonneg
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    (p : MPoint Ctx Msg nl w)
    (pref : Fin (mpoints.slot p) → C) (c : C) :
    0 ≤ sideFieldPointCharge (H := H) (Sat := Sat) LD P p pref c := by
  unfold sideFieldPointCharge
  split_ifs
  · exact sidePointCharge_nonneg LD P p pref c
  · exact le_refl _

omit [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] in
theorem sideFieldTraceCharge_eq_point
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (i : Fin (Rounds.Role.length nl w)) :
    sideFieldTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro i =
      let p := msgPoint ctx msgOf out i.val
      sideFieldPointCharge (H := H) (Sat := Sat) LD P p
        (mpoints.chal ro p) (ro p) := by
  simp only [sideFieldTraceCharge, sideFieldPointCharge, sideTraceCharge]
  have hs : (msgPoint (nl := nl) (w := w) ctx msgOf out i.val).role.slot = i.val := by
    exact slot_msgPoint ctx msgOf out i.isLt
  rw [hs]

omit [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] in
theorem sideFieldTraceCharge_nonneg
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (i : Fin (Rounds.Role.length nl w)) :
    0 ≤ sideFieldTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro i := by
  unfold sideFieldTraceCharge
  split_ifs
  · exact sideTraceCharge_nonneg LD P ctx msgOf out ro i
  · exact le_refl _

omit [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] in
/-- An escape pays after both terminal slots have been set to zero. -/
theorem field_escape_sideFieldTrace_pays
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (hfield :
      let tape : Fin (Rounds.Role.length nl w) → C :=
        fun i => ro (msgPoint ctx msgOf out i.val)
      let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) (msgOf out)
      ∃ i : Fin (Rounds.Role.layerBase w nl + 1),
        ch.doomed i.val (Bcs.trunc tape i.val
          (by dsimp [Rounds.Role.length]; omega)) ∧
        ¬ ch.doomed (i.val + 1) (Bcs.trunc tape (i.val + 1)
          (by dsimp [Rounds.Role.length]; omega))) :
    1 ≤ ∑ i : Fin (Rounds.Role.length nl w),
      sideFieldTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro i := by
  dsimp only at hfield
  obtain ⟨k, hd, he⟩ := hfield
  let i : Fin (Rounds.Role.length nl w) :=
    ⟨k.val, by dsimp [Rounds.Role.length]; omega⟩
  have hd' :
      (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
        (msgOf out)).doomed i.val (Sumcheck.extract_prefix
          (fun j : Fin (Rounds.Role.length nl w) =>
            ro (msgPoint ctx msgOf out j.val)) i) := by
    rw [← Bcs.trunc_eq_extract_prefix]
    exact hd
  have he' :
      ¬ (chain (nl := nl) (w := w) V H asg Sat (flatData LD)
        (msgOf out)).doomed (i.val + 1)
        (Bcs.extend (Sumcheck.extract_prefix
          (fun j : Fin (Rounds.Role.length nl w) =>
            ro (msgPoint ctx msgOf out j.val)) i)
          (ro (msgPoint ctx msgOf out i.val))) := by
    rw [← Bcs.trunc_succ]
    exact he
  have hpay := sidePointCharge_field_escape (H := H) (Sat := Sat)
    LD P ctx msgOf out ro i k.isLt hd' he'
  apply Bcs.PotentialChain.one_or_two_slots_pay
    (sideFieldTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro)
    (sideFieldTraceCharge_nonneg LD P ctx msgOf out ro)
  left
  refine ⟨i, ?_⟩
  simpa [sideFieldTraceCharge, sideTraceCharge, show i.val <
    Rounds.Role.layerBase w nl + 1 from k.isLt] using hpay

omit [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] in
/-- The field escape used by the flat terminal-pair split has precisely the
field-only charge required by the hybrid FS compiler. -/
theorem fieldPrefixEscape_sideFieldTrace_pays
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (hfield :
      let tape : Fin (Rounds.Role.length nl w) → C :=
        fun i => ro (msgPoint ctx msgOf out i.val)
      fieldPrefixEscape (H := H) (Sat := Sat) LD (msgOf out)
        (Bcs.trunc tape (Rounds.Role.layerBase w nl + 1) fieldLen_le)) :
    1 ≤ ∑ i : Fin (Rounds.Role.length nl w),
      sideFieldTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro i := by
  apply field_escape_sideFieldTrace_pays LD P ctx msgOf out ro
  dsimp only [fieldPrefixEscape] at hfield
  obtain ⟨i, hd, he⟩ := hfield
  refine ⟨i, ?_, ?_⟩
  · exact hd
  · exact he

omit [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] in
/-- Exact extraction-first path charge, before oracle counting. -/
theorem accepted_noSat_sideTrace_pays
    (LD : ZkLigeroData C X Q Msg V asg) (P : TerminalPotential LD)
    {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (hfalse : ∀ ℓ : Lift, ¬ Sat ℓ)
    (hacc :
      let tape : Fin (Rounds.Role.length nl w) → C :=
        fun i => ro (msgPoint ctx msgOf out i.val)
      ZkLayerStepAccepts .accepted .start
        (steps (nl := nl) (w := w) V LD (msgOf out)) tape) :
    1 ≤ ∑ i : Fin (Rounds.Role.length nl w),
      sideTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro i := by
  let tape : Fin (Rounds.Role.length nl w) → C :=
    fun i => ro (msgPoint ctx msgOf out i.val)
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) (msgOf out)
  let u := Rounds.Role.layerBase w nl + 1
  have hT : u ≤ Rounds.Role.length nl w := fieldLen_le
  have h0 : prefixDoom ch tape 0 := by
    simp only [prefixDoom, dif_pos (Nat.zero_le _)]
    intro cand
    cases cand with
    | none => trivial
    | some ℓ => exact hfalse ℓ
  by_cases hu : prefixDoom ch tape u
  · have hdu : ch.doomed u (Bcs.trunc tape u hT) := by
      simpa only [prefixDoom, dif_pos hT] using hu
    obtain ⟨sys, hs, hf, hn, hq⟩ := accepted_doomed_terminal
      (H := H) (Sat := Sat) LD (msgOf out) tape hacc hdu
    let ic : Fin (Rounds.Role.length nl w) := ligIdx
    let iq : Fin (Rounds.Role.length nl w) := qryIdx
    have hic : ic.val = u := rfl
    have hiq : iq.val = u + 1 := rfl
    let pc := msgPoint (nl := nl) (w := w) ctx msgOf out ic.val
    let pq := msgPoint (nl := nl) (w := w) ctx msgOf out iq.val
    have hsc : pc.role.slot = u := by
      change mpoints.slot (msgPoint ctx msgOf out ic.val) = u
      rw [slot_msgPoint ctx msgOf out ic.isLt]
      exact hic
    have hsq : pq.role.slot = u + 1 := by
      change mpoints.slot (msgPoint ctx msgOf out iq.val) = u + 1
      rw [slot_msgPoint ctx msgOf out iq.isLt]
      exact hiq
    have hpc := sidePoint_built_state_of_verifier
      (H := H) (Sat := Sat) LD ctx msgOf out ro ic
      (by omega) sys hs
    have hpq := sidePoint_built_state_of_verifier
      (H := H) (Sat := Sat) LD ctx msgOf out ro iq
      (by omega) sys hs
    have hprefix : ∀ j : Fin pq.role.slot,
        mpoints.chal ro pq j =
          Bcs.trunc tape (u + 1) queryLen_le (Fin.cast hsq j) := by
      intro j
      change ro (mpoints.anc pq j.val) = ro (msgPoint ctx msgOf out j.val)
      have hj : j.val < pq.role.slot := j.isLt
      exact congrArg ro (anc_msgPoint ctx msgOf out (by omega) iq.isLt)
    have hmsgq : pq.msgFn pq.role.slot = msgOf out (u + 1) := by
      rw [hsq]
      exact msgFn_msgPoint ctx msgOf out iq.isLt (by omega)
    have hchall : (mpoints.chal ro pq) ⟨u, by
          change u < pq.role.slot
          omega⟩ = tape ic := by
      have h := hprefix ⟨u, by omega⟩
      convert h using 1
      · rfl
      · change tape ic = tape ⟨u, by omega⟩
        exact congrArg tape (Fin.ext hic)
    have hq' : V.decodeQuery (ro pq) ∈ LD.accepting pq.role.slot
        (mpoints.chal ro pq) (pq.msgFn pq.role.slot) sys
        (V.decodeChal ((mpoints.chal ro pq) ⟨u, by
          change u < pq.role.slot
          omega⟩)) := by
      have hset := accepting_eq_of_prefix LD.accepting hsq
        (mpoints.chal ro pq) (Bcs.trunc tape (u + 1) queryLen_le)
        hprefix hmsgq sys (congrArg V.decodeChal hchall)
      rw [hset]
      exact hq
    have hc : sideTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro ic =
        P.weight sys (V.decodeChal (tape ic)) := by
      change sidePointCharge (H := H) (Sat := Sat) LD P pc
        (mpoints.chal ro pc) (ro pc) = _
      rw [sidePointCharge_challenge_eq LD P pc hsc _ _ sys hpc hf hn]
    have hqcharge : sideTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro iq =
        1 - P.weight sys (V.decodeChal (tape ic)) := by
      change sidePointCharge (H := H) (Sat := Sat) LD P pq
        (mpoints.chal ro pq) (ro pq) = _
      rw [sidePointCharge_query_eq LD P pq hsq _ _ sys hpq hf hn hq']
      rw [hchall]
    apply Bcs.PotentialChain.one_or_two_slots_pay
      (sideTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro)
      (sideTraceCharge_nonneg LD P ctx msgOf out ro)
    right
    refine ⟨ic, iq, ?_, ?_⟩
    · intro heq
      have heq' := congrArg Fin.val heq
      change u = u + 1 at heq'
      omega
    · rw [hc, hqcharge]
      norm_num
  · obtain ⟨i, hi, hdi, hei⟩ :=
      Bcs.PotentialChain.field_escape_before u (prefixDoom ch tape) h0 hu
    let k : Fin (Rounds.Role.length nl w) := ⟨i, by omega⟩
    have hdi' : ch.doomed k.val (Sumcheck.extract_prefix tape k) := by
      have hd : ch.doomed i (Bcs.trunc tape i (by omega)) := by
        simpa only [prefixDoom, dif_pos (by omega : i ≤ Rounds.Role.length nl w)] using hdi
      rw [← Bcs.trunc_eq_extract_prefix tape k]
      exact hd
    have hei' : ¬ ch.doomed (k.val + 1)
        (Bcs.extend (Sumcheck.extract_prefix tape k) (tape k)) := by
      have he : ¬ ch.doomed (i + 1) (Bcs.trunc tape (i + 1) (by omega)) := by
        simpa only [prefixDoom, dif_pos (by omega : i + 1 ≤ Rounds.Role.length nl w)]
          using hei
      rw [← Bcs.trunc_succ tape k]
      exact he
    have hk : k.val < u := hi
    have hpay := sidePointCharge_field_escape (H := H) (Sat := Sat)
      LD P ctx msgOf out ro k hk hdi' hei'
    apply Bcs.PotentialChain.one_or_two_slots_pay
      (sideTraceCharge (H := H) (Sat := Sat) LD P ctx msgOf out ro)
      (sideTraceCharge_nonneg LD P ctx msgOf out ro)
    left
    exact ⟨k, hpay⟩

end Lfzk.RbrZkFlat
