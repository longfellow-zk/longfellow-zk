import Lfzk.RbrZkPotentialPoint
import Bcs.TerminalPairTape

/-!
# The accepted Longfellow path at the flat terminal-pair interface

The deterministic extraction split is expressed on a field prefix followed
by the raw Ligero challenge and query answers.  This is the event shape
consumed by `Bcs.terminalPair_event_ratio_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkFlat

open Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.RbrLayerStepS
  Lfzk.CompiledLongfellow
open scoped Classical

variable {C F X Q Msg Gpt Lift : Type} [Fintype C] [Field F]
  [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Inhabited Msg]
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc}
variable {H : ZkHonest F Lift logw logc}
variable {asg : Lift → LigeroAssignment ninp M F} {Sat : Lift → Prop}

/-- The field-prefix escape event, before either terminal Ligero answer is
drawn. -/
def fieldPrefixEscape
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (pref : Fin (Rounds.Role.layerBase w nl + 1) → C) : Prop :=
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  ∃ i : Fin (Rounds.Role.layerBase w nl + 1),
    ch.doomed i.val (Bcs.trunc pref i.val (by omega)) ∧
    ¬ ch.doomed (i.val + 1) (Bcs.trunc pref (i.val + 1) (by omega))

/-- The final accepted query event at a built system with no satisfying
candidate.  Its first raw answer selects the challenge and may affect the
response; its second raw answer selects the opened columns. -/
def terminalPairAccept
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (pref : Fin (Rounds.Role.layerBase w nl + 1) → C) (c d : C) : Prop :=
  let u := Rounds.Role.layerBase w nl + 1
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  ∃ sys : LigeroSystem ninp M F,
    ch.state u pref = .built sys ∧ Fits V sys ∧ NoSat asg sys ∧
    V.decodeQuery d ∈ LD.accepting (u + 1) (Bcs.extend pref c)
      (ms (u + 1)) sys (V.decodeChal c)

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [Inhabited Msg] in
/-- Every accepted path with no satisfying candidate either escapes during
the field prefix, or reaches a built `Fits ∧ NoSat` system whose *joint*
terminal challenge/query answers pass the V1 query test. -/
theorem accepted_field_or_terminal_pair
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C)
    (hfalse : ∀ ℓ : Lift, ¬ Sat ℓ)
    (hacc : ZkLayerStepAccepts .accepted .start
      (steps (nl := nl) (w := w) V LD ms) tape) :
    let u := Rounds.Role.layerBase w nl + 1
    let p := Bcs.terminalPairEquiv u tape
    let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
    (∃ i : Fin u,
      ch.doomed i.val (Bcs.trunc p.1 i.val (by omega)) ∧
      ¬ ch.doomed (i.val + 1) (Bcs.trunc p.1 (i.val + 1) (by omega))) ∨
      ∃ sys : LigeroSystem ninp M F,
        ch.state u p.1 = .built sys ∧ Fits V sys ∧ NoSat asg sys ∧
        V.decodeQuery p.2.2 ∈
          LD.accepting (u + 1) (Bcs.extend p.1 p.2.1)
            (ms (u + 1)) sys (V.decodeChal p.2.1) := by
  let u := Rounds.Role.layerBase w nl + 1
  let p := Bcs.terminalPairEquiv u tape
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  have hqueryPrefix : Bcs.trunc tape (u + 1) queryLen_le =
      Bcs.extend p.1 p.2.1 := by
    funext j
    by_cases hj : j.val < u
    · simp [Bcs.trunc, Bcs.extend, Bcs.terminalPairEquiv, p, hj]
    · have heq : j.val = u := by omega
      simp [Bcs.trunc, Bcs.extend, Bcs.terminalPairEquiv, p, heq]
  have hsplit := accepted_field_escape_or_noSat_query
    (H := H) (Sat := Sat) LD ms tape hfalse hacc
  dsimp only at hsplit
  rcases hsplit with ⟨i, hi, hd, hnext⟩ | ⟨sys, hs, hf, hn, hq⟩
  · left
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · change ch.doomed i (Bcs.trunc tape i
        (by dsimp [Rounds.Role.length, u]; omega))
      simpa only [prefixDoom,
        dif_pos (by dsimp [Rounds.Role.length, u]; omega : i ≤ Rounds.Role.length nl w)] using hd
    · change ¬ ch.doomed (i + 1) (Bcs.trunc tape (i + 1)
        (by dsimp [Rounds.Role.length, u]; omega))
      simpa only [prefixDoom,
        dif_pos (by dsimp [Rounds.Role.length, u]; omega : i + 1 ≤ Rounds.Role.length nl w)]
        using hnext
  · right
    refine ⟨sys, ?_, hf, hn, ?_⟩
    · change ch.state u (Bcs.trunc tape u fieldLen_le) = .built sys
      exact hs
    · change V.decodeQuery (tape qryIdx) ∈
        LD.accepting (u + 1) (Bcs.extend p.1 p.2.1)
          (ms (u + 1)) sys (V.decodeChal (tape ligIdx))
      rw [← hqueryPrefix]
      exact hq

omit [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [Inhabited Msg] in
/-- Interactive accepted-path extraction at a fixed commitment and message
schedule.  A field-prefix bound and a conditional flat terminal-pair bound
compose additively; no challenge/query threshold or extra pair factor is
introduced by the tape accounting. -/
theorem accepted_ratio_le_field_plus_terminal [Nonempty C]
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (hfalse : ∀ ℓ : Lift, ¬ Sat ℓ)
    (fieldBound terminalBound : ℚ)
    (hfield :
      ((Finset.univ.filter fun pref : Fin (Rounds.Role.layerBase w nl + 1) → C =>
        fieldPrefixEscape (H := H) (Sat := Sat) LD ms pref).card : ℚ) /
          Fintype.card (Fin (Rounds.Role.layerBase w nl + 1) → C) ≤ fieldBound)
    (hterminal : ∀ pref : Fin (Rounds.Role.layerBase w nl + 1) → C,
      ((Finset.univ.filter fun pair : C × C =>
        terminalPairAccept (H := H) (Sat := Sat) LD ms pref pair.1 pair.2).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ terminalBound) :
    ((Finset.univ.filter fun tape : Fin (Rounds.Role.length nl w) → C =>
      ZkLayerStepAccepts .accepted .start
        (steps (nl := nl) (w := w) V LD ms) tape).card : ℚ) /
        (Fintype.card C : ℚ) ^ Rounds.Role.length nl w ≤
          fieldBound + terminalBound := by
  classical
  let u := Rounds.Role.layerBase w nl + 1
  have h := Bcs.terminalPair_event_ratio_le u
    (fun tape : Fin (u + 2) → C =>
      ZkLayerStepAccepts .accepted .start
        (steps (nl := nl) (w := w) V LD ms) tape)
    (fieldPrefixEscape (H := H) (Sat := Sat) LD ms)
    (terminalPairAccept (H := H) (Sat := Sat) LD ms)
    (by
      intro tape hacc
      have hp := accepted_field_or_terminal_pair
        (H := H) (Sat := Sat) LD ms tape hfalse hacc
      simpa only [fieldPrefixEscape, terminalPairAccept] using hp)
    fieldBound terminalBound hfield hterminal
  exact h

omit [Inhabited Msg] in
/-- The field-prefix escape has exactly the old list-scaled sumcheck cost,
now on the candidate list chosen for the flat certificate.  The terminal
challenge and query do not appear in this sum. -/
theorem fieldPrefixEscape_ratio_le [Fintype Lift] [Nonempty C]
    (FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat)
    (LD : ZkLigeroData C X Q Msg V asg)
    {bpair bround bin blig bquery : ℕ}
    (hB : ZkBudgets FD LD bpair bround bin blig bquery)
    (ms : ℕ → Msg) :
    let u := Rounds.Role.layerBase w nl + 1
    ((Finset.univ.filter fun pref : Fin u → C =>
      fieldPrefixEscape (H := H) (Sat := Sat) LD ms pref).card : ℚ) /
        Fintype.card (Fin u → C) ≤
      ((∑ i : Fin u,
        mixedBudget (nl := nl) (w := w) (Fintype.card Lift)
          bpair bround bin 0 (FD.kq * Fintype.card Q)
          (Rounds.Role.indexEquiv.symm
            (⟨i.val, by dsimp [Rounds.Role.length]; omega⟩ :
              Fin (Rounds.Role.length nl w))) : ℕ) : ℚ) /
        Fintype.card C := by
  classical
  let u := Rounds.Role.layerBase w nl + 1
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  let budget (i : Fin u) : ℕ :=
    mixedBudget (nl := nl) (w := w) (Fintype.card Lift)
      bpair bround bin 0 (FD.kq * Fintype.card Q)
      (Rounds.Role.indexEquiv.symm
        (⟨i.val, by dsimp [Rounds.Role.length, u]; omega⟩ :
          Fin (Rounds.Role.length nl w)))
  let bad (i : Fin u) (pref : Fin i.val → C) (c : C) : Prop :=
    ch.doomed i.val pref ∧
      ¬ ch.doomed (i.val + 1) (Bcs.extend pref c)
  have hlocal (i : Fin u) (pref : Fin i.val → C) :
      (Finset.univ.filter fun c : C => bad i pref c).card ≤ budget i := by
    by_cases hd : ch.doomed i.val pref
    · have hp := FD.doom_preserved_chain (flatData LD) (flatBudgets LD hB) ms
        (⟨i.val, by dsimp [Rounds.Role.length, u]; omega⟩ :
          Fin (Rounds.Role.length nl w)) pref hd
      simpa only [bad, hd, true_and, budget] using hp
    · simp [bad, hd]
  have hcover (pref : Fin u → C)
      (he : fieldPrefixEscape (H := H) (Sat := Sat) LD ms pref) :
      ∃ i : Fin u, bad i (Sumcheck.extract_prefix pref i) (pref i) := by
    obtain ⟨i, hd, hnext⟩ := he
    refine ⟨i, ?_, ?_⟩
    · change ch.doomed i.val (Sumcheck.extract_prefix pref i)
      simpa only [Bcs.trunc_eq_extract_prefix] using hd
    · change ¬ ch.doomed (i.val + 1)
        (Bcs.extend (Sumcheck.extract_prefix pref i) (pref i))
      simpa only [Bcs.trunc_succ, Bcs.trunc_eq_extract_prefix] using hnext
  have hratio := Bcs.weighted_tape_ratio_le
    (fun pref : Fin u → C => fieldPrefixEscape (H := H) (Sat := Sat) LD ms pref)
    bad hcover (fun i _ => budget i) (by
      intro i pref
      simpa only [bad] using hlocal i pref)
    (∑ i : Fin u, budget i) (by intro pref; rfl)
  simpa only [u, budget, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow] using hratio

end Lfzk.RbrZkFlat
