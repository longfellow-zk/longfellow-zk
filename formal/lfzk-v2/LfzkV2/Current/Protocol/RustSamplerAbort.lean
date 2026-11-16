import LfzkV2.Current.Protocol.RustSamplerReader
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.SetTheory.Cardinal.NatCard

/-! Availability of the byte reader: the fraction of buffers on which a
program of draws aborts because its buffer runs out.

Rust's reader never aborts; it reads further PRF blocks until every draw
accepts, and panics only when the PRF counter is exhausted
(`Prf::next_block` in `rust/src/runtime/v2/transcript/strand.rs`). The model
caps the buffer, so a program can abort; this module bounds how often. The
bound is proved once in continuation-passing form, like uniformity: a draw
that rejects a fraction `reject` of its attempts, given `j` attempts' worth of
bytes, adds at most `reject^j` to its continuation's abort fraction
(`then_bound`). A program then aborts on at most `abortSum j` of all buffers
(`Prog.read_abort`), and on at most `draws * (1/2)^j` when every draw rejects
at most half of its attempts (`Prog.abortSum_le_halving`). -/
noncomputable section
namespace LfzkV2.Current.Protocol.RustSampler
open Finset

/-- Abort fraction of a parser at length `L`. -/
def abortRate {X : Type} (f : List Byte → Option X) (L : ℕ) : ℚ :=
  (Nat.card {s : Fin L → Byte // f (List.ofFn s) = none} : ℚ) / 256 ^ L

theorem abortRate_nonneg {X : Type} (f : List Byte → Option X) (L : ℕ) : 0 ≤ abortRate f L := by
  unfold abortRate; positivity

theorem abortRate_le_one {X : Type} (f : List Byte → Option X) (L : ℕ) : abortRate f L ≤ 1 := by
  unfold abortRate
  rw [div_le_one (by positivity)]
  have h : Nat.card {s : Fin L → Byte // f (List.ofFn s) = none} ≤ 256 ^ L := by
    calc Nat.card {s : Fin L → Byte // f (List.ofFn s) = none} ≤ Nat.card (Fin L → Byte) :=
          Finite.card_subtype_le _
      _ = 256 ^ L := by simp
  exact_mod_cast h

section Attempt
variable {A : Type} (w : ℕ) (pos : 0 < w) (dec : (Fin w → Byte) → Option A)

/-- Exact abort recurrence of one draw followed by a continuation. -/
theorem card_abort_succ {X : Type} (g : List Byte → Option X) (m : ℕ) :
    Nat.card {s : Fin (w + m) → Byte // then_ w pos dec g (List.ofFn s) = none} =
      (256 ^ w - Nat.card {c // dec c = none}) * Nat.card {s : Fin m → Byte // g (List.ofFn s) = none} +
        Nat.card {c // dec c = none} * Nat.card {s : Fin m → Byte // then_ w pos dec g (List.ofFn s) = none} := by
  classical
  rw [card_split w m (fun s => then_ w pos dec g s = none)]
  have pointwise : ∀ c : Fin w → Byte,
      Nat.card {s : Fin m → Byte // then_ w pos dec g (List.ofFn c ++ List.ofFn s) = none} =
        (if dec c = none then 0 else Nat.card {s : Fin m → Byte // g (List.ofFn s) = none}) +
        (if dec c = none then Nat.card {s : Fin m → Byte // then_ w pos dec g (List.ofFn s) = none} else 0) := by
    intro c
    simp only [then_, attempt_append]
    rcases hdc : dec c with _ | a
    · simp
    · simp only [reduceCtorEq, if_false, add_zero]
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro s
      show ((g (List.ofFn s)).map fun y => (a, y)) = none ↔ g (List.ofFn s) = none
      generalize g (List.ofFn s) = o
      cases o <;> simp
  simp only [pointwise, sum_add_distrib, sum_ite_card]
  have hsplit : ∑ c : Fin w → Byte, (if dec c = none then 0 else Nat.card {s : Fin m → Byte // g (List.ofFn s) = none}) =
      (256 ^ w - Nat.card {c // dec c = none}) * Nat.card {s : Fin m → Byte // g (List.ofFn s) = none} := by
    have h1 := sum_ite_card (fun c : Fin w → Byte => ¬ dec c = none) (Nat.card {s : Fin m → Byte // g (List.ofFn s) = none})
    have h2 : Nat.card {c : Fin w → Byte // ¬ dec c = none} = 256 ^ w - Nat.card {c // dec c = none} := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      simp
    rw [← h2, ← h1]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : dec c = none <;> simp [h]
  rw [hsplit]

/-- Rejected fraction of one attempt. -/
def reject : ℚ := (Nat.card {c // dec c = none} : ℚ) / 256 ^ w

theorem reject_le_one : reject w dec ≤ 1 := by
  unfold reject
  rw [div_le_one (by positivity)]
  have : Nat.card {c // dec c = none} ≤ 256 ^ w := by
    calc Nat.card {c // dec c = none} ≤ Nat.card (Fin w → Byte) := Finite.card_subtype_le _
      _ = 256 ^ w := by simp
  exact_mod_cast this

theorem abortRate_succ {X : Type} (g : List Byte → Option X) (m : ℕ) :
    abortRate (then_ w pos dec g) (w + m) =
      (1 - reject w dec) * abortRate g m + reject w dec * abortRate (then_ w pos dec g) m := by
  have hρ : Nat.card {c // dec c = none} ≤ 256 ^ w := by
    calc Nat.card {c // dec c = none} ≤ Nat.card (Fin w → Byte) := Finite.card_subtype_le _
      _ = 256 ^ w := by simp
  unfold abortRate reject
  rw [card_abort_succ w pos dec g m]
  push_cast [hρ]
  rw [pow_add]
  field_simp

theorem abortRate_short {X : Type} (g : List Byte → Option X) (L : ℕ) (h : L < w) :
    abortRate (then_ w pos dec g) L = 1 := by
  unfold abortRate
  have : Nat.card {s : Fin L → Byte // then_ w pos dec g (List.ofFn s) = none} = 256 ^ L := by
    rw [show (256 : ℕ) ^ L = Nat.card (Fin L → Byte) by simp]
    apply Nat.card_congr
    exact Equiv.subtypeUnivEquiv fun s => by
      show (attempt w pos dec (List.ofFn s)).bind _ = none
      rw [attempt_short w pos dec _ (by simp; omega)]
      rfl
  rw [this]; push_cast; field_simp

/-- The continuation's abort fraction does not grow with more bytes. -/
def Antitone' {X : Type} (g : List Byte → Option X) : Prop := ∀ L, abortRate g (L + 1) ≤ abortRate g L

theorem then_antitone {X : Type} (g : List Byte → Option X) (hg : Antitone' g) :
    Antitone' (then_ w pos dec g) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    by_cases h : L + 1 < w
    · rw [abortRate_short w pos dec g _ h, abortRate_short w pos dec g _ (by omega)]
    · by_cases h' : L < w
      · rw [abortRate_short w pos dec g _ h']
        exact abortRate_le_one _ _
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h')
        rw [show w + m + 1 = w + (m + 1) by ring, abortRate_succ, abortRate_succ]
        have r1 := reject_le_one w dec
        have r0 : 0 ≤ reject w dec := by unfold reject; positivity
        have := ih m (by omega)
        have := hg m
        nlinarith

theorem antitone_le {X : Type} (g : List Byte → Option X) (hg : Antitone' g) {a b : ℕ} (h : a ≤ b) :
    abortRate g b ≤ abortRate g a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp
  | succ k ih => exact (hg _).trans (by simpa [Nat.add_assoc] using ih (by omega))

/-- `j` attempts' worth of bytes: abort adds at most `reject^j`. -/
theorem then_bound {X : Type} (g : List Byte → Option X) (hg : Antitone' g) (j L : ℕ) :
    abortRate (then_ w pos dec g) (L + j * w) ≤ reject w dec ^ j + abortRate g L := by
  induction j generalizing L with
  | zero => simpa using abortRate_le_one (then_ w pos dec g) L |>.trans (by
      have := abortRate_nonneg g L; linarith)
  | succ j ih =>
    rw [show L + (j + 1) * w = w + (L + j * w) by ring, abortRate_succ]
    have r1 := reject_le_one w dec
    have r0 : 0 ≤ reject w dec := by unfold reject; positivity
    have hih := ih L
    have hmono : abortRate g (L + j * w) ≤ abortRate g L := antitone_le g hg (by omega)
    have := abortRate_nonneg g L
    rw [pow_succ]
    nlinarith

end Attempt

theorem abortRate_congr {X Y : Type} (f : List Byte → Option X) (f' : List Byte → Option Y)
    (h : ∀ s, f s = none ↔ f' s = none) (L : ℕ) : abortRate f L = abortRate f' L := by
  unfold abortRate
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight fun s => h _)

theorem antitone_congr {X Y : Type} (f : List Byte → Option X) (f' : List Byte → Option Y)
    (h : ∀ s, f s = none ↔ f' s = none) (hf : Antitone' f) : Antitone' f' := by
  intro L
  rw [← abortRate_congr f f' h, ← abortRate_congr f f' h]
  exact hf L

/-- Sum over the draws of `reject^j`. -/
def Prog.abortSum (j : ℕ) : {V : Type} → Prog V → ℚ
  | _, .unit => 0
  | _, .draw w _ dec => reject w dec ^ j
  | _, .seq p q => p.abortSum j + q.abortSum j
  | _, .map p _ => p.abortSum j

/-- The composite of a program with a continuation. -/
abbrev Prog.andThen {V X : Type} (p : Prog V) (g : List Byte → Option X) (s : List Byte) : Option (V × X) :=
  (p.parse s).bind fun r => (g r.2).map fun x => (r.1, x)

theorem Prog.avail (j : ℕ) : {V : Type} → (p : Prog V) → ∀ (X : Type) (g : List Byte → Option X),
    Antitone' g → Antitone' (p.andThen g) ∧
      ∀ L, abortRate (p.andThen g) (L + j * p.width) ≤ p.abortSum j + abortRate g L
  | _, .unit, X, g, hg => by
      have same : ∀ s, g s = none ↔ (Prog.unit.andThen g) s = none := by
        intro s; simp only [Prog.andThen, Prog.parse, Option.bind_some]
        cases g s <;> simp
      refine ⟨antitone_congr _ _ same hg, fun L => ?_⟩
      rw [← abortRate_congr _ _ same]
      simp [Prog.width, Prog.abortSum]
  | _, .draw w pos dec, X, g, hg =>
      ⟨then_antitone w pos dec g hg, fun L => then_bound w pos dec g hg j L⟩
  | _, .seq (V := V) (W := W) p q, X, g, hg => by
      obtain ⟨hq, bq⟩ := q.avail j X g hg
      obtain ⟨hp, bp⟩ := p.avail j _ (q.andThen g) hq
      have same : ∀ s, (p.andThen (q.andThen g)) s = none ↔ ((Prog.seq p q).andThen g) s = none := by
        intro s
        simp only [Prog.andThen, Prog.parse]
        cases p.parse s with
        | none => simp
        | some r =>
          simp only [Option.bind_some]
          cases q.parse r.2 with
          | none => simp
          | some t =>
            simp only [Option.bind_some, Option.map_some]
            cases g t.2 <;> simp
      refine ⟨antitone_congr _ _ same hp, fun L => ?_⟩
      rw [← abortRate_congr _ _ same, show L + j * (Prog.seq p q).width = (L + j * q.width) + j * p.width by
        simp only [Prog.width]; ring]
      have := bp (L + j * q.width)
      have := bq L
      simp only [Prog.abortSum]
      linarith
  | _, .map p e, X, g, hg => by
      obtain ⟨hp, bp⟩ := p.avail j X g hg
      have same : ∀ s, (p.andThen g) s = none ↔ ((Prog.map p e).andThen g) s = none := by
        intro s
        simp only [Prog.andThen, Prog.parse]
        cases p.parse s with
        | none => simp
        | some r =>
          simp only [Option.bind_some, Option.map_some]
          cases g r.2 <;> simp
      refine ⟨antitone_congr _ _ same hp, fun L => ?_⟩
      rw [← abortRate_congr _ _ same]
      simpa [Prog.width, Prog.abortSum] using bp L

/-- A program given `j` attempts per draw aborts on at most `abortSum j` of
all buffers, and on less with more bytes. -/
theorem Prog.read_abort {V : Type} (p : Prog V) (j L : ℕ) (wide : j * p.width ≤ L) :
    abortRate p.read L ≤ p.abortSum j := by
  have never : Antitone' (fun _ : List Byte => (some () : Option Unit)) := by
    intro L; simp [abortRate]
  obtain ⟨anti, bound⟩ := p.avail j Unit (fun _ => some ()) never
  have same : ∀ s, (p.andThen fun _ => some ()) s = none ↔ p.read s = none := by
    intro s; simp only [Prog.andThen, Prog.read]; cases p.parse s <;> simp
  have zero : abortRate (fun _ : List Byte => (some () : Option Unit)) 0 = 0 := by simp [abortRate]
  rw [← abortRate_congr _ _ same]
  calc abortRate (p.andThen fun _ => some ()) L
      ≤ abortRate (p.andThen fun _ => some ()) (0 + j * p.width) := antitone_le _ anti (by omega)
    _ ≤ p.abortSum j + 0 := zero ▸ bound 0
    _ = p.abortSum j := add_zero _

/-! ## Rejection counts of the Rust draws -/

/-- A balanced decoder rejects all encodings not used by its values. -/
theorem reject_card {A : Type} [Fintype A] (w : ℕ) (dec : (Fin w → Byte) → Option A) (k : ℕ)
    (hk : ∀ a, Nat.card {c // dec c = some a} = k) :
    Nat.card {c // dec c = none} + Fintype.card A * k = 256 ^ w := by
  have split : (Fin w → Byte) ≃ Σ o : Option A, {c // dec c = o} :=
    (Equiv.sigmaFiberEquiv dec).symm
  have total : Nat.card (Fin w → Byte) = 256 ^ w := by simp
  rw [← total, Nat.card_congr split, Nat.card_sigma, Fintype.sum_option]
  simp [hk]


/-! ## Draw counts -/

/-- The number of draws of a program. -/
def Prog.draws : {V : Type} → Prog V → ℕ
  | _, .unit => 0
  | _, .draw .. => 1
  | _, .seq p q => p.draws + q.draws
  | _, .map p _ => p.draws

/-- Every draw rejects at most half of its attempts. -/
def Prog.Halving : {V : Type} → Prog V → Prop
  | _, .unit => True
  | _, .draw w _ dec => reject w dec ≤ 1 / 2
  | _, .seq p q => p.Halving ∧ q.Halving
  | _, .map p _ => p.Halving

/-- With `j` attempts per draw, a halving program aborts on at most
`draws * (1/2)^j` of all buffers' worth of draws. -/
theorem Prog.abortSum_le_halving (j : ℕ) : {V : Type} → (p : Prog V) → p.Halving →
    p.abortSum j ≤ p.draws * (1 / 2 : ℚ) ^ j
  | _, .unit, _ => by simp [Prog.abortSum, Prog.draws]
  | _, .draw w _ dec, h => by
      simp only [Prog.abortSum, Prog.draws, Nat.cast_one, one_mul]
      exact pow_le_pow_left₀ (by unfold reject; positivity) h j
  | _, .seq p q, h => by
      have hp := p.abortSum_le_halving j h.1
      have hq := q.abortSum_le_halving j h.2
      simp only [Prog.abortSum, Prog.draws, Nat.cast_add]
      linarith
  | _, .map p _, h => p.abortSum_le_halving j h

theorem Prog.draws_le_width : {V : Type} → (p : Prog V) → p.draws ≤ p.width
  | _, .unit => le_refl _
  | _, .draw _ pos _ => pos
  | _, .seq p q => Nat.add_le_add (p.draws_le_width) (q.draws_le_width)
  | _, .map p _ => p.draws_le_width

theorem Prog.vec_draws {A : Type} (p : Prog A) : (n : ℕ) → (p.vec n).draws = n * p.draws
  | 0 => by simp [Prog.vec, Prog.draws]
  | n + 1 => by simp [Prog.vec, Prog.draws, Prog.vec_draws p n]; ring

theorem Prog.vec_halving {A : Type} (p : Prog A) (h : p.Halving) : (n : ℕ) → (p.vec n).Halving
  | 0 => trivial
  | n + 1 => ⟨h, p.vec_halving h n⟩

end LfzkV2.Current.Protocol.RustSampler
