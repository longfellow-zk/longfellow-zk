import Lfzk.Types
import Bcs.Counting

/-!
# The output point, counted: multilinear Schwartz–Zippel and the layer-0 slot

The deployed verifier draws the output-layer point `G` from the transcript after the commitment
(`zk_common.h:L59` `tss.begin_circuit(ch.q, ch.g)`, `transcript_sumcheck.h:L49`), sets both claims
to zero and both points to `G`, and then `begin_layer` draws `(alpha₀, beta₀)`.  No prover message
separates those draws: they are consecutive outputs of one transcript state.  So the Fiat–Shamir
oracle answer of layer 0's pair slot carries **all three** — `G`, `beta₀` and `alpha₀` — and the
slot's escape count is a count over `(Fin logv → F) × F × F`.

The honest claim layer 0 starts from is `V₀^β(G) + alpha · V₀^β(G)` (`claim[0] + alpha·claim[1]`
with both points `G`), where `V₀^β` is the output layer's multilinear extension at `beta₀ = β`.  If
the candidate witness does not satisfy the circuit, some output wire is non-zero for `β = 0` or
`β = 1` — a statement about the **Boolean-cube** outputs — so `V₀^β` is a non-zero multilinear
polynomial for that `β`.  `init_bad_card` counts the escapes:

```text
#{ (G, β, α) : V₀^β(G) + α·V₀^β(G) = 0 }  ≤  (logv + 2) · |F|^(logv + 1)
```

— the multilinear Schwartz–Zippel term `logv/|F|` for `G` (`mlin_zero_card`, `G` in the common zero
set of `V₀^0` and `V₀^1`) plus the bilinear term `2/|F|` for `(β, α)` (`bilinear_zero_card`, at every
other `G`).  This replaces the fixed-point assumption that an adversary choosing the committed
witness could violate (`V₀ ≠ 0` but `V₀(G) = 0` at a fixed `G`).

`MLin`, `mlinLo`, `mlinSlope`, `mlin_split`, `mlinLo_mlin`, `mlinSlope_mlin`, `card_cons_split_le`
and `mlin_zero_card` are copied from `proofs/lfzk/Lfzk/Multilinear.lean` (namespaced here).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkMultilinear

open Finset
open scoped Classical

variable {F : Type} [Field F]

/-- Multilinear: freezing every coordinate but one leaves an affine function. -/
def MLin {n : ℕ} (h : (Fin n → F) → F) : Prop :=
  ∀ (v : Fin n → F) (j : Fin n), ∃ a b : F, ∀ X : F, h (Function.update v j X) = a + b * X

/-- `h` with its first variable set to `0`. -/
def mlinLo {n : ℕ} (h : (Fin (n + 1) → F) → F) : (Fin n → F) → F :=
  fun v' => h (Fin.cons 0 v')

/-- The slope of `h` in its first variable. -/
def mlinSlope {n : ℕ} (h : (Fin (n + 1) → F) → F) : (Fin n → F) → F :=
  fun v' => h (Fin.cons 1 v') - h (Fin.cons 0 v')

/-- **A multilinear function is affine in its first variable, with these two halves.** -/
lemma mlin_split {n : ℕ} (h : (Fin (n + 1) → F) → F) (H : MLin h) (v' : Fin n → F) (X : F) :
    h (Fin.cons X v') = mlinLo h v' + mlinSlope h v' * X := by
  obtain ⟨a, b, hab⟩ := H (Fin.cons 0 v') 0
  have hupd : ∀ Y : F, Function.update (Fin.cons (0 : F) v' : Fin (n+1) → F) 0 Y
      = (Fin.cons Y v' : Fin (n+1) → F) := by
    intro Y
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro k; simp
  have h0 : h (Fin.cons (0 : F) v') = a := by
    have := hab 0
    rw [hupd 0] at this
    rw [this]; ring
  have h1 : h (Fin.cons (1 : F) v') = a + b := by
    have := hab 1
    rw [hupd 1] at this
    rw [this]; ring
  have hX := hab X
  rw [hupd X] at hX
  rw [hX, mlinLo, mlinSlope, h0, h1]
  ring

omit [Field F] in
/-- Freezing a later coordinate of `h` is freezing a coordinate of each half. -/
lemma cons_update_succ {n : ℕ} (v' : Fin n → F) (X Y : F) (j : Fin n) :
    Function.update (Fin.cons X v' : Fin (n+1) → F) j.succ Y
      = (Fin.cons X (Function.update v' j Y) : Fin (n+1) → F) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]
  · intro k
    by_cases hk : k = j
    · subst hk; simp
    · rw [Function.update_of_ne (by simpa using hk), Fin.cons_succ, Fin.cons_succ,
        Function.update_of_ne hk]

/-- Both halves of a multilinear function are multilinear. -/
lemma mlinLo_mlin {n : ℕ} (h : (Fin (n + 1) → F) → F) (H : MLin h) : MLin (mlinLo h) := by
  intro v' j
  obtain ⟨a, b, hab⟩ := H (Fin.cons 0 v') j.succ
  refine ⟨a, b, fun X => ?_⟩
  have hx := hab X
  rw [cons_update_succ] at hx
  exact hx

lemma mlinSlope_mlin {n : ℕ} (h : (Fin (n + 1) → F) → F) (H : MLin h) :
    MLin (mlinSlope h) := by
  intro v' j
  obtain ⟨a1, b1, h1⟩ := H (Fin.cons 1 v') j.succ
  obtain ⟨a0, b0, h0⟩ := H (Fin.cons 0 v') j.succ
  refine ⟨a1 - a0, b1 - b0, fun X => ?_⟩
  have e1 := h1 X
  have e0 := h0 X
  rw [cons_update_succ] at e1 e0
  show h (Fin.cons 1 (Function.update v' j X)) - h (Fin.cons 0 (Function.update v' j X)) = _
  rw [e1, e0]; ring

variable [Fintype F] [DecidableEq F]

omit [Field F] in
/-- Counting over `Fin (n+1) → F` by splitting off the first coordinate. -/
lemma card_cons_split_le {n : ℕ} (P : (Fin (n + 1) → F) → Prop) [DecidablePred P]
    (g : (Fin n → F) → ℕ)
    (hg : ∀ v' : Fin n → F,
      (Finset.univ.filter (fun X : F => P (Fin.cons X v'))).card ≤ g v') :
    (Finset.univ.filter P).card ≤ ∑ v' : Fin n → F, g v' := by
  classical
  have hfib : (Finset.univ.filter P).card
      = ∑ v' : Fin n → F,
          ((Finset.univ.filter P).filter (fun v => Fin.tail v = v')).card :=
    Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ _)
  rw [hfib]
  refine Finset.sum_le_sum (fun v' _ => ?_)
  refine le_trans (Finset.card_le_card_of_injOn (fun v => v 0) ?_ ?_) (hg v')
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨hP, ht⟩ := hv
    rw [← ht, show Fin.cons (v 0) (Fin.tail v) = v from Fin.cons_self_tail v]
    exact hP
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hab0 : a 0 = b 0 := hab
    rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, hab0, ha.2, hb.2]

/--
**Multilinear Schwartz–Zippel.**  A multilinear function of `n` variables that is not identically
zero vanishes on at most `n · |F|^(n-1)` of the `|F|^n` points.
-/
theorem mlin_zero_card : ∀ (n : ℕ) (h : (Fin n → F) → F), MLin h → (∃ v, h v ≠ 0) →
    (Finset.univ.filter (fun v : Fin n → F => h v = 0)).card
      ≤ n * (Fintype.card F) ^ (n - 1) := by
  intro n
  induction n with
  | zero =>
    intro h _ hne
    obtain ⟨v, hv⟩ := hne
    have hempty : Finset.univ.filter (fun w : Fin 0 → F => h w = 0) = ∅ := by
      refine Finset.filter_false_of_mem (fun w _ => ?_)
      have hwv : w = v := funext (fun i => absurd i.isLt (by omega))
      rw [hwv]; exact hv
    rw [hempty]; simp
  | succ k ih =>
    intro h H hne
    classical
    set Z : Finset (Fin k → F) :=
      Finset.univ.filter (fun v' => mlinLo h v' = 0 ∧ mlinSlope h v' = 0) with hZ
    have hterm : ∀ v' : Fin k → F,
        (Finset.univ.filter (fun X : F => h (Fin.cons X v') = 0)).card
          ≤ (if v' ∈ Z then Fintype.card F else 1) := by
      intro v'
      by_cases hmem : v' ∈ Z
      · rw [if_pos hmem]; exact le_trans (Finset.card_filter_le _ _) (le_of_eq (by simp))
      · rw [if_neg hmem]
        simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        rw [mlin_split h H v' a] at ha
        rw [mlin_split h H v' b] at hb
        by_cases hs : mlinSlope h v' = 0
        · exfalso
          rw [hs] at ha
          simp only [zero_mul, add_zero] at ha
          exact hmem ⟨ha, hs⟩
        · exact mul_left_cancel₀ hs (by linear_combination ha - hb)
    have hhalf : (∃ v', mlinLo h v' ≠ 0) ∨ (∃ v', mlinSlope h v' ≠ 0) := by
      obtain ⟨v, hv⟩ := hne
      by_contra hc
      push Not at hc
      obtain ⟨hlo, hsl⟩ := hc
      refine hv ?_
      rw [← Fin.cons_self_tail v, mlin_split h H (Fin.tail v) (v 0), hlo, hsl]
      ring
    have hZcard : Z.card ≤ k * (Fintype.card F) ^ (k - 1) := by
      rcases hhalf with ⟨v', hv'⟩ | ⟨v', hv'⟩
      · refine le_trans (Finset.card_le_card ?_) (ih (mlinLo h) (mlinLo_mlin h H) ⟨v', hv'⟩)
        intro x hx
        simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.1
      · refine le_trans (Finset.card_le_card ?_)
          (ih (mlinSlope h) (mlinSlope_mlin h H) ⟨v', hv'⟩)
        intro x hx
        simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.2
    refine le_trans (card_cons_split_le (P := fun v : Fin (k+1) → F => h v = 0)
      (fun v' => if v' ∈ Z then Fintype.card F else 1) hterm) ?_
    calc ∑ v' : Fin k → F, (if v' ∈ Z then Fintype.card F else 1)
        ≤ ∑ v' : Fin k → F, ((if v' ∈ Z then Fintype.card F else 0) + 1) :=
          Finset.sum_le_sum (fun v' _ => by by_cases hv : v' ∈ Z <;> simp [hv])
      _ = Z.card * Fintype.card F + Fintype.card (Fin k → F) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
            Finset.sum_const, Finset.sum_const, Finset.card_univ]
          simp [mul_comm]
      _ ≤ (k * (Fintype.card F) ^ (k - 1)) * Fintype.card F + (Fintype.card F) ^ k := by
          have hc : Fintype.card (Fin k → F) = (Fintype.card F) ^ k := by simp
          rw [hc]
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hZcard) _
      _ = (k + 1) * (Fintype.card F) ^ (k + 1 - 1) := by
          cases k with
          | zero => simp
          | succ m =>
            rw [Nat.succ_sub_one, Nat.add_sub_cancel, mul_assoc, ← pow_succ]
            ring

/-! ## Layer 0's pair slot, with the output point -/

/-- `n · |F|^(n-1) · |F|² ≤ n · |F|^(n+1)`, with equality for `n ≥ 1`. -/
lemma mul_pow_pred_le (n f : ℕ) : n * f ^ (n - 1) * f ^ 2 ≤ n * f ^ (n + 1) := by
  rcases n with _ | m
  · simp
  · rw [Nat.add_sub_cancel, mul_assoc, ← pow_add]

/--
**Layer 0's slot, counted over `(G, β, α)`.**

`out β` is the output layer's multilinear extension at `beta₀ = β`, multilinear in the point
(`hml`) and affine in `β` (`haff`, `prep_v`); the claim layer 0 starts from at `(G, β, α)` is
`out β G + α · out β G`.  If `out` is not identically zero (`hne` — for an unsatisfied circuit some
Boolean-cube output wire is non-zero at `β = 0` or `β = 1`), the claim vanishes on at most
`(n + 2) · |F|^(n + 1)` of the `|F|^(n + 2)` triples: `n/|F|` for the point, `2/|F|` for the pair.
-/
theorem init_bad_card {n : ℕ} (out : F → (Fin n → F) → F)
    (hml : ∀ b : F, MLin (out b))
    (haff : ∀ (b : F) (G : Fin n → F), out b G = out 0 G + b * (out 1 G - out 0 G))
    (hne : ∃ (b : F) (G : Fin n → F), out b G ≠ 0) :
    (univ.filter fun p : (Fin n → F) × F × F =>
        out p.2.1 p.1 + p.2.2 * out p.2.1 p.1 = 0).card
      ≤ (n + 2) * Fintype.card F ^ (n + 1) := by
  classical
  set f := Fintype.card F
  -- the common zero set of the two endpoints, counted by Schwartz–Zippel
  set Z : Finset (Fin n → F) := univ.filter fun G => out 0 G = 0 ∧ out 1 G = 0 with hZ
  have hZcard : Z.card ≤ n * f ^ (n - 1) := by
    obtain ⟨b, G, hbG⟩ := hne
    have hend : out 0 G ≠ 0 ∨ out 1 G ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hbG (by rw [haff b G, hc.1, hc.2]; ring)
    rcases hend with h0 | h1
    · refine le_trans (Finset.card_le_card ?_) (mlin_zero_card n (out 0) (hml 0) ⟨G, h0⟩)
      intro x hx
      simp only [hZ, mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.1
    · refine le_trans (Finset.card_le_card ?_) (mlin_zero_card n (out 1) (hml 1) ⟨G, h1⟩)
      intro x hx
      simp only [hZ, mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.2
  -- per point: all pairs on `Z`, at most `2|F|` off it
  have hfib : ∀ G : Fin n → F,
      (univ.filter fun q : F × F => out q.1 G + q.2 * out q.1 G = 0).card
        ≤ (if G ∈ Z then f ^ 2 else 2 * f) := by
    intro G
    by_cases hG : G ∈ Z
    · rw [if_pos hG]
      refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
      simp [f, sq]
    · rw [if_neg hG]
      have hS : ∀ b a : F, out b G + a * out b G
          = out 0 G + a * out 0 G + b * (out 1 G - out 0 G)
            + a * b * (out 1 G - out 0 G) := by
        intro b a
        rw [haff b G]
        ring
      refine bilinear_zero_card (fun b a => out b G + a * out b G) (out 0 G) (out 0 G)
        (out 1 G - out 0 G) (out 1 G - out 0 G) hS ?_
      rintro ⟨h00, -, h01, -⟩
      refine hG ?_
      simp only [hZ, mem_filter, mem_univ, true_and]
      exact ⟨h00, by linear_combination h01 + h00⟩
  rw [Bcs.card_filter_prod_fst]
  calc ∑ G : Fin n → F, (univ.filter fun q : F × F =>
          out (G, q).2.1 (G, q).1 + (G, q).2.2 * out (G, q).2.1 (G, q).1 = 0).card
      ≤ ∑ G : Fin n → F, ((if G ∈ Z then f ^ 2 else 0) + 2 * f) :=
        Finset.sum_le_sum fun G _ => le_trans (hfib G) (by split_ifs <;> omega)
    _ = Z.card * f ^ 2 + f ^ n * (2 * f) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          Finset.sum_const, Finset.card_univ, smul_eq_mul, smul_eq_mul]
        simp [f]
    _ ≤ n * f ^ (n - 1) * f ^ 2 + f ^ n * (2 * f) :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hZcard) _
    _ ≤ n * f ^ (n + 1) + 2 * f ^ (n + 1) :=
        Nat.add_le_add (mul_pow_pred_le n f) (le_of_eq (by ring))
    _ = (n + 2) * f ^ (n + 1) := by ring

/--
**Layer 0's slot at every beta schedule.**  `out Xs G` is the output layer's multilinear extension
at the beta schedule `Xs` and the point `G`: multilinear in `G` (`hml`) and affine in `beta₀ = Xs 0`
(`haff`, `prep_v`).  If it is not identically zero as a function of the schedule and the point —
for an unsatisfied circuit, some Boolean-cube output wire is non-zero at some schedule — then the
triples `(G, β, α)` at which the starting claim vanishes **at every schedule with `Xs 0 = β`** number
at most `(n + 2) · |F|^(n + 1)`.  Fix a schedule `Xs₀` at which `out` is non-zero somewhere and
vary only its coordinate `0`: that is `init_bad_card`.
-/
theorem init_bad_card_sched {n : ℕ} (out : (ℕ → F) → (Fin n → F) → F)
    (hml : ∀ Xs : ℕ → F, MLin (out Xs))
    (haff : ∀ (Xs : ℕ → F) (b : F) (G : Fin n → F),
      out (Function.update Xs 0 b) G = out (Function.update Xs 0 0) G
        + b * (out (Function.update Xs 0 1) G - out (Function.update Xs 0 0) G))
    (hne : ∃ (Xs : ℕ → F) (G : Fin n → F), out Xs G ≠ 0) :
    (univ.filter fun p : (Fin n → F) × F × F =>
        ∀ Xs : ℕ → F, Xs 0 = p.2.1 → out Xs p.1 + p.2.2 * out Xs p.1 = 0).card
      ≤ (n + 2) * Fintype.card F ^ (n + 1) := by
  classical
  obtain ⟨Xs0, G0, hG0⟩ := hne
  refine le_trans (Finset.card_le_card ?_) (init_bad_card
    (fun b G => out (Function.update Xs0 0 b) G) (fun b => hml _)
    (fun b G => haff Xs0 b G) ⟨Xs0 0, G0, by simpa only [Function.update_eq_self] using hG0⟩)
  intro p hp
  simp only [mem_filter, mem_univ, true_and] at hp ⊢
  exact hp _ (Function.update_self _ _ _)

end Lfzk.ZkMultilinear
