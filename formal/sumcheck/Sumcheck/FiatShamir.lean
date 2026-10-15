import Sumcheck.Multi
import Sumcheck.Grinding

/-!
# The Fiat--Shamir counting bound

How often a *non-adaptive* prover — one whose round-`i` polynomial is fixed before challenge `i`
is drawn — can survive a whole run by luck.  The answer is a root count and needs no random
oracle: at most `n · deg · |F|^(n-1)` of the `|F|^n` challenge sequences are lucky, so the error
is `n · deg / |F|`.

The counting itself is not here: `Sumcheck.Grinding` proves it for an arbitrary challenge type
and an arbitrary per-slot bad set, since nothing in the fiber decomposition ever needed the
field.  This file supplies the one sumcheck-specific ingredient — `bad_round_roots`, the per-round
root count — and reads off the two corollaries.

`deg` bounds the *true* round polynomial's degree; `d` is the degree of what the prover
transmits.  The hypothesis relating them is `d ≤ deg`, and it is not cosmetic: the challenge must
be a root of a difference of degree up to `max d deg`.  The original development wrote this as
`2 ≤ deg`, which is the same statement with `d = 2` inlined — and which a degree-3 copy round
would have silently under-charged.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Classical

namespace Sumcheck

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {d : ℕ} [Interp F d]


abbrev ProverStrategy (F : Type) [Field F] (d n : ℕ) := ∀ i : Fin n, Prefix F i.val → RoundPoly F d

abbrev TruePolyStrategy (F : Type) [Field F] (n : ℕ) := ∀ i : Fin n, Prefix F i.val → Polynomial F


def bad_event_at {F : Type} [Field F] {d : ℕ} [Interp F d] (n : ℕ) (P_func : TruePolyStrategy F n) (p_func : ProverStrategy F d n) (cs : Fin n → F) (i : Fin n) : Prop :=
  BadRoundEvent (P_func i (extract_prefix cs i)) (p_func i (extract_prefix cs i)) (cs i)

def any_bad_event {F : Type} [Field F] {d : ℕ} [Interp F d] (n : ℕ) (P_func : TruePolyStrategy F n) (p_func : ProverStrategy F d n) (cs : Fin n → F) : Prop :=
  ∃ i : Fin n, bad_event_at n P_func p_func cs i

lemma bad_round_roots {F : Type} [Field F] [Fintype F] [DecidableEq F] {d : ℕ} [Interp F d] (P_true_poly : Polynomial F) (poly : RoundPoly F d) (deg : ℕ) (hd : P_true_poly.natDegree ≤ deg) (h2 : d ≤ deg) :
    (Finset.filter (fun r => BadRoundEvent P_true_poly poly r) Finset.univ).card ≤ deg := by
  by_cases h_diff : poly.eval0 ≠ P_true_poly.eval 0 ∨ poly.eval1 ≠ P_true_poly.eval 1
  · have h_sz := RoundPoly.univariate_roots_bound P_true_poly poly deg hd h_diff
    have h_max : max d deg = deg := max_eq_right h2
    rw [h_max] at h_sz
    have h_Q_neq_0 : poly.toPoly - P_true_poly ≠ 0 :=
      RoundPoly.toPoly_sub_ne_zero P_true_poly poly h_diff
    have h_subset : Finset.filter (fun r => BadRoundEvent P_true_poly poly r) Finset.univ ⊆
        (Polynomial.roots (poly.toPoly - P_true_poly)).toFinset := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Multiset.mem_toFinset]
      have h_root : (poly.toPoly - P_true_poly).IsRoot r := by
        dsimp [Polynomial.IsRoot]
        rw [Polynomial.eval_sub, RoundPoly.eval_toPoly]
        dsimp [BadRoundEvent] at hr
        rw [hr.right, sub_self]
      exact (Polynomial.mem_roots h_Q_neq_0).mpr h_root
    have h_card_subset := Finset.card_le_card h_subset
    have h_card_toFinset :
        (Polynomial.roots (poly.toPoly - P_true_poly)).toFinset.card
          ≤ (Polynomial.roots (poly.toPoly - P_true_poly)).card := Multiset.toFinset_card_le _
    exact le_trans h_card_subset (le_trans h_card_toFinset h_sz)
  · have h_empty : Finset.filter (fun r => BadRoundEvent P_true_poly poly r) Finset.univ = ∅ := by
      ext r
      simp
      intro hr
      dsimp [BadRoundEvent] at hr
      exact h_diff hr.left
    rw [h_empty]
    simp

/--
**One round.**  At most `deg * |F|^(n-1)` challenge sequences are bad at round `i`.

`Sumcheck.slot_bad_card_le` at `beta = deg`: `bad_event_at` reads the challenge prefix and the
round's own challenge and nothing else, which is what its type says, and `bad_round_roots` is the
per-prefix root count.
-/
lemma combinatorial_fs_level (n deg : ℕ) (P_func : TruePolyStrategy F n) (p_func : ProverStrategy F d n)
    (hd : ∀ (i : Fin n) (pref : Prefix F i.val), (P_func i pref).natDegree ≤ deg) (h2 : d ≤ deg) (i : Fin n) :
    (Finset.filter (fun cs : Fin n → F => bad_event_at n P_func p_func cs i) Finset.univ).card ≤ deg * (Fintype.card F)^(n - 1) :=
  slot_bad_card_le i deg
    (fun pref r => BadRoundEvent (P_func i pref) (p_func i pref) r)
    (fun pref => bad_round_roots (P_func i pref) (p_func i pref) deg (hd i pref) h2)

/--
**A whole run.**  At most `n * deg * |F|^(n-1)` of the `|F|^n` challenge sequences let a
non-adaptive prover through some round — an `n * deg / |F|` fraction, the textbook sumcheck error.

`Sumcheck.tape_bad_card_le_const` at `beta = deg`; the union over rounds is done there.
-/
lemma combinatorial_fiat_shamir (n deg : ℕ) (P_func : TruePolyStrategy F n) (p_func : ProverStrategy F d n)
    (hd : ∀ (i : Fin n) (pref : Prefix F i.val), (P_func i pref).natDegree ≤ deg) (h2 : d ≤ deg) :
    (Finset.filter (fun cs : Fin n → F => any_bad_event n P_func p_func cs) Finset.univ).card ≤ n * deg * (Fintype.card F)^(n - 1) := by
  have h_unfold : Finset.filter (fun cs : Fin n → F => any_bad_event n P_func p_func cs) Finset.univ
      = Finset.filter (fun cs : Fin n → F => ∃ i : Fin n,
          BadRoundEvent (P_func i (extract_prefix cs i)) (p_func i (extract_prefix cs i)) (cs i))
        Finset.univ := by
    ext cs
    simp [any_bad_event, bad_event_at]
  rw [h_unfold]
  exact tape_bad_card_le_const deg
    (fun i pref r => BadRoundEvent (P_func i pref) (p_func i pref) r)
    (fun i pref => bad_round_roots (P_func i pref) (p_func i pref) deg (hd i pref) h2)

end Sumcheck