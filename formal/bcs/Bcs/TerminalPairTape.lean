import Bcs.Counting

/-!
# A fresh terminal challenge/query pair on a finite verifier tape

The last two answers are separated from the preceding field-round tape by
an exact equivalence.  This lets a flat Ligero pair bound be averaged over
every field prefix while retaining the existing field-escape charge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset
open scoped Classical

/-- Split a tape into its first `u` answers, terminal challenge, and final
query.  No independence premise is needed: this is a bijection of finite
sample spaces. -/
def terminalPairEquiv {C : Type} (u : ℕ) :
    (Fin (u + 2) → C) ≃ (Fin u → C) × (C × C) where
  toFun tape :=
    (fun i => tape ⟨i.val, by omega⟩,
      tape ⟨u, by omega⟩, tape ⟨u + 1, by omega⟩)
  invFun p j :=
    if h : j.val < u then p.1 ⟨j.val, h⟩
    else if j.val = u then p.2.1 else p.2.2
  left_inv tape := by
    funext j
    by_cases h : j.val < u
    · simp [h]
    · by_cases heq : j.val = u
      · dsimp
        simp only [if_neg h, if_pos heq]
        exact congrArg tape (Fin.ext heq.symm)
      · have hlast : j.val = u + 1 := by omega
        dsimp
        simp only [if_neg h, if_neg heq]
        exact congrArg tape (Fin.ext hlast.symm)
  right_inv p := by
    apply Prod.ext
    · funext j
      simp
    · apply Prod.ext <;> simp

@[simp] theorem terminalPairEquiv_prefix {C : Type} (u : ℕ)
    (tape : Fin (u + 2) → C) :
    (terminalPairEquiv u tape).1 = fun i => tape ⟨i.val, by omega⟩ := rfl

@[simp] theorem terminalPairEquiv_challenge {C : Type} (u : ℕ)
    (tape : Fin (u + 2) → C) :
    (terminalPairEquiv u tape).2.1 = tape ⟨u, by omega⟩ := rfl

@[simp] theorem terminalPairEquiv_query {C : Type} (u : ℕ)
    (tape : Fin (u + 2) → C) :
    (terminalPairEquiv u tape).2.2 = tape ⟨u + 1, by omega⟩ := rfl

/-- Field-prefix escape plus a flat terminal-pair bound, with no extra
challenge/query factor.  The terminal pair may be tested by a response
depending on its first raw answer, provided its conditional pair estimate
holds at every prefix. -/
theorem terminalPair_tape_ratio_le {C : Type} [Fintype C] [Nonempty C]
    (u : ℕ) (fieldEscape : (Fin u → C) → Prop)
    (terminal : (Fin u → C) → C → C → Prop)
    [DecidablePred fieldEscape]
    [∀ pref, DecidablePred (fun pair : C × C => terminal pref pair.1 pair.2)]
    (fieldBound terminalBound : ℚ)
    (hfield : ((univ.filter fieldEscape).card : ℚ) /
      Fintype.card (Fin u → C) ≤ fieldBound)
    (hterminal : ∀ pref,
      ((univ.filter fun pair : C × C =>
        terminal pref pair.1 pair.2).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ terminalBound) :
    ((univ.filter fun tape : Fin (u + 2) → C =>
      let p := terminalPairEquiv u tape
      fieldEscape p.1 ∨ terminal p.1 p.2.1 p.2.2).card : ℚ) /
        (Fintype.card C : ℚ) ^ (u + 2) ≤
          fieldBound + terminalBound := by
  classical
  let e := terminalPairEquiv (C := C) u
  have hterm' (pref : Fin u → C) :
      ((univ.filter fun pair : C × C => terminal pref pair.1 pair.2).card : ℚ) /
          Fintype.card (C × C) ≤ terminalBound := by
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hterminal pref
  have h := prefix_or_terminal_ratio_le fieldEscape
    (fun pref (pair : C × C) => terminal pref pair.1 pair.2)
    fieldBound terminalBound hfield hterm'
  have hnum :
      (univ.filter fun tape : Fin (u + 2) → C =>
        let p := terminalPairEquiv u tape
        fieldEscape p.1 ∨ terminal p.1 p.2.1 p.2.2).card =
      (univ.filter fun p : (Fin u → C) × (C × C) =>
        fieldEscape p.1 ∨ terminal p.1 p.2.1 p.2.2).card := by
    simp only [Finset.card_filter]
    exact Fintype.sum_equiv e _ _ (by intro tape; rfl)
  have hden : (Fintype.card C : ℚ) ^ (u + 2) =
      Fintype.card ((Fin u → C) × (C × C)) := by
    calc
      (Fintype.card C : ℚ) ^ (u + 2) =
          Fintype.card (Fin (u + 2) → C) := by simp
      _ = Fintype.card ((Fin u → C) × (C × C)) := by
        exact_mod_cast Fintype.card_congr e
  rw [hnum, hden]
  exact h

/-- Event-inclusion form of the flat terminal-pair compiler.  A protocol
proof supplies the pathwise statement that every bad accepted tape either
escaped during the field prefix or passed its joint terminal test. -/
theorem terminalPair_event_ratio_le {C : Type} [Fintype C] [Nonempty C]
    (u : ℕ) (event : (Fin (u + 2) → C) → Prop)
    (fieldEscape : (Fin u → C) → Prop)
    (terminal : (Fin u → C) → C → C → Prop)
    [DecidablePred event] [DecidablePred fieldEscape]
    [∀ pref, DecidablePred (fun pair : C × C => terminal pref pair.1 pair.2)]
    (hcover : ∀ tape, event tape →
      let p := terminalPairEquiv u tape
      fieldEscape p.1 ∨ terminal p.1 p.2.1 p.2.2)
    (fieldBound terminalBound : ℚ)
    (hfield : ((univ.filter fieldEscape).card : ℚ) /
      Fintype.card (Fin u → C) ≤ fieldBound)
    (hterminal : ∀ pref,
      ((univ.filter fun pair : C × C =>
        terminal pref pair.1 pair.2).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ terminalBound) :
    ((univ.filter event).card : ℚ) /
        (Fintype.card C : ℚ) ^ (u + 2) ≤
          fieldBound + terminalBound := by
  classical
  have hsub : (univ.filter event) ⊆
      (univ.filter fun tape : Fin (u + 2) → C =>
        let p := terminalPairEquiv u tape
        fieldEscape p.1 ∨ terminal p.1 p.2.1 p.2.2) := by
    intro tape htape
    exact Finset.mem_filter.mpr
      ⟨mem_univ _, hcover tape (Finset.mem_filter.mp htape).2⟩
  have hC : (0 : ℚ) < Fintype.card C := by
    exact_mod_cast Fintype.card_pos
  have hcard : ((univ.filter event).card : ℚ) ≤
      ((univ.filter fun tape : Fin (u + 2) → C =>
        let p := terminalPairEquiv u tape
        fieldEscape p.1 ∨ terminal p.1 p.2.1 p.2.2).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact (div_le_div_of_nonneg_right hcard
      (le_of_lt (pow_pos hC _))).trans
    (terminalPair_tape_ratio_le u fieldEscape terminal
      fieldBound terminalBound hfield hterminal)

end Bcs
