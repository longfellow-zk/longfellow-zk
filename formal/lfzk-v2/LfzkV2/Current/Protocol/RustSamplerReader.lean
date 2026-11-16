import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring
import TranscriptV2.Framing

/-! The byte reader of the v2 Rust transcript, as fixed programs of
fixed-width rejection draws over one byte buffer.

Every Rust draw (`Reading::elt_field`, `nonzero`, `choose` and its `nat`
offsets in `rust/src/runtime/v2/transcript/session.rs`) reads a fixed number
of bytes per attempt from the round's byte cursor (`Reader::read` in
`rust/src/runtime/v2/transcript/strand.rs`), decodes them, and on rejection
reads the same width again. Which attempt is accepted depends on the bytes,
but no attempt's width does, and the shape of a round's draws never depends
on drawn values. `Prog` models exactly such a round; `Prog.parse` consumes a
prefix of the buffer and returns the rest, as the cursor does.

The one law the soundness endpoints need, that every value has the same
number of preimages (`Uniform`), is proved once, in continuation-passing
form (`Good`): a balanced draw followed by any uniform continuation is
uniform. Counting uses `Nat.card`, so no decidability instance enters the
statements. Nondegeneracy (`Prog.read_exists`) and the lazy reader's
prefix property (`Prog.read_extend`) are proved here too. -/
noncomputable section
namespace LfzkV2.Current.Protocol.RustSampler
open Finset

abbrev Byte := TranscriptV2.Framing.Byte

/-! ## Uniform byte parsers -/

/-- Byte strings of length `L` on which `f` returns `x`. -/
abbrev Fiber {X : Type} (f : List Byte → Option X) (L : ℕ) (x : X) : Type :=
  {s : Fin L → Byte // f (List.ofFn s) = some x}

/-- All values have equally many byte strings of each length. -/
def Uniform {X : Type} (f : List Byte → Option X) : Prop :=
  ∀ (L : ℕ) (x y : X), Nat.card (Fiber f L x) = Nat.card (Fiber f L y)

theorem uniform_map {X Y : Type} (f : List Byte → Option X) (e : X ≃ Y) (hf : Uniform f) :
    Uniform (fun s => (f s).map e) := by
  intro L x y
  have key : ∀ z : Y, Nat.card (Fiber (fun s => (f s).map e) L z) = Nat.card (Fiber f L (e.symm z)) := by
    intro z
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro s
    show (f (List.ofFn s)).map e = some z ↔ f (List.ofFn s) = some (e.symm z)
    generalize f (List.ofFn s) = o
    cases o <;> simp [Equiv.eq_symm_apply, eq_comm]
  rw [key, key]
  exact hf L _ _

/-- A parser consumes a prefix and returns the rest. It is good when every
uniform continuation stays uniform after it. -/
def Good {V : Type} (p : List Byte → Option (V × List Byte)) : Prop :=
  ∀ (X : Type) (g : List Byte → Option X), Uniform g →
    Uniform (fun s => (p s).bind fun r => (g r.2).map fun x => (r.1, x))

/-- Split a byte string at `w`. -/
theorem card_split (w m : ℕ) (P : List Byte → Prop) :
    Nat.card {s : Fin (w + m) → Byte // P (List.ofFn s)} =
      ∑ c : Fin w → Byte, Nat.card {s : Fin m → Byte // P (List.ofFn c ++ List.ofFn s)} := by
  rw [← Nat.card_sigma]
  apply Nat.card_congr
  refine ((Equiv.subtypeEquiv (Fin.appendEquiv w m) ?_).symm).trans
    (Equiv.subtypeProdEquivSigmaSubtype fun c s => P (List.ofFn c ++ List.ofFn s))
  intro cs
  rw [show (Fin.appendEquiv w m) cs = Fin.append cs.1 cs.2 from rfl, List.ofFn_fin_append]

theorem sum_ite_card {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] (G : ℕ) :
    (∑ c, if p c then G else 0) = Nat.card {c // p c} * G := by
  rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ## One rejection draw -/

section Attempt
variable {A : Type} (w : ℕ) (pos : 0 < w) (dec : (Fin w → Byte) → Option A)

/-- Rust's loop: read `w` bytes, decode, and on rejection read `w` more.
It fails only when the buffer, the model's block cap, runs out. -/
def attempt (w : ℕ) (pos : 0 < w) (dec : (Fin w → Byte) → Option A) (s : List Byte) :
    Option (A × List Byte) :=
  if h : w ≤ s.length then
    match dec (fun i => s.get ⟨i, lt_of_lt_of_le i.isLt h⟩) with
    | some a => some (a, s.drop w)
    | none => attempt w pos dec (s.drop w)
  else none
termination_by s.length
decreasing_by simp only [List.length_drop]; omega

theorem attempt_short (s : List Byte) (h : s.length < w) : attempt w pos dec s = none := by
  rw [attempt, dif_neg (by omega)]

theorem attempt_append (c : Fin w → Byte) (rest : List Byte) :
    attempt w pos dec (List.ofFn c ++ rest) =
      match dec c with
      | some a => some (a, rest)
      | none => attempt w pos dec rest := by
  rw [attempt, dif_pos (by simp)]
  have hc : (fun i : Fin w => (List.ofFn c ++ rest).get
      ⟨i, lt_of_lt_of_le i.isLt (by simp)⟩) = c := by
    funext i
    simp [List.getElem_append_left]
  have hd : (List.ofFn c ++ rest).drop w = rest := by simp
  rw [hc, hd]

/-- Decoder balance: every value has `k` encodings. -/
def Balanced : Prop := ∃ k, ∀ a, Nat.card {c // dec c = some a} = k

/-- One rejection draw followed by a continuation. -/
abbrev then_ {X : Type} (g : List Byte → Option X) (s : List Byte) : Option (A × X) :=
  (attempt w pos dec s).bind fun r => (g r.2).map fun y => (r.1, y)

/-- The recurrence for one rejection draw followed by a continuation. -/
theorem card_attempt_succ {X : Type} (g : List Byte → Option X) (m : ℕ) (a : A) (x : X) :
    Nat.card (Fiber (then_ w pos dec g) (w + m) (a, x)) =
      Nat.card {c // dec c = some a} * Nat.card (Fiber g m x) +
        Nat.card {c // dec c = none} * Nat.card (Fiber (then_ w pos dec g) m (a, x)) := by
  classical
  rw [Fiber, card_split w m (fun s => then_ w pos dec g s = some (a, x))]
  have pointwise : ∀ c : Fin w → Byte,
      Nat.card {s : Fin m → Byte // then_ w pos dec g (List.ofFn c ++ List.ofFn s) = some (a, x)} =
        (if dec c = some a then Nat.card (Fiber g m x) else 0) +
        (if dec c = none then Nat.card (Fiber (then_ w pos dec g) m (a, x)) else 0) := by
    intro c
    simp only [then_, attempt_append]
    rcases hdc : dec c with _ | a'
    · simp
    · by_cases ha : a' = a
      · subst ha
        simp only [if_true, reduceCtorEq, if_false, add_zero]
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro s
        show ((g (List.ofFn s)).map fun y => (a', y)) = some (a', x) ↔ g (List.ofFn s) = some x
        generalize g (List.ofFn s) = o
        cases o <;> simp
      · have none : IsEmpty {s : Fin m → Byte //
            ((some (a', List.ofFn s) : Option (A × List Byte)).bind
              fun r => (g r.2).map fun y => (r.1, y)) = some (a, x)} := by
          constructor
          rintro ⟨s, hs⟩
          revert hs
          cases g (List.ofFn s) <;> simp [ha]
        simp [ha]
  simp only [pointwise, sum_add_distrib, sum_ite_card]

theorem attempt_good (balanced : Balanced w dec) : Good (attempt w pos dec) := by
  obtain ⟨k, hk⟩ := balanced
  intro X g hg L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rintro ⟨a, x⟩ ⟨b, y⟩
    change Nat.card (Fiber (then_ w pos dec g) L (a, x)) = Nat.card (Fiber (then_ w pos dec g) L (b, y))
    by_cases hL : w ≤ L
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hL
      rw [card_attempt_succ, card_attempt_succ, hk a, hk b, hg m x y,
        ih m (by omega) (a, x) (b, y)]
    · have empty : ∀ z : A × X, IsEmpty (Fiber (then_ w pos dec g) L z) := by
        intro z
        constructor
        rintro ⟨s, hs⟩
        rw [then_, attempt_short w pos dec _ (by simp; omega)] at hs
        simp at hs
      rw [Nat.card_of_isEmpty (α := Fiber (then_ w pos dec g) L (a, x)),
        Nat.card_of_isEmpty (α := Fiber (then_ w pos dec g) L (b, y))]

end Attempt

/-! ## Programs of draws -/

/-- A fixed, value-independent sequence of draws. Its shape never depends
on drawn values, as in every v2 round. -/
inductive Prog : Type → Type 1 where
  | unit : Prog Unit
  | draw {A : Type} (w : ℕ) (pos : 0 < w) (dec : (Fin w → Byte) → Option A) : Prog A
  | seq {V W : Type} : Prog V → Prog W → Prog (V × W)
  | map {V W : Type} : Prog V → (V ≃ W) → Prog W

def Prog.parse : {V : Type} → Prog V → List Byte → Option (V × List Byte)
  | _, .unit, s => some ((), s)
  | _, .draw w pos dec, s => attempt w pos dec s
  | _, .seq p q, s => (p.parse s).bind fun r => (q.parse r.2).map fun t => ((r.1, t.1), t.2)
  | _, .map p e, s => (p.parse s).map fun r => (e r.1, r.2)

/-- Every draw's decoder is balanced. -/
def Prog.Lawful : {V : Type} → Prog V → Prop
  | _, .unit => True
  | _, .draw _ _ dec => Balanced _ dec
  | _, .seq p q => p.Lawful ∧ q.Lawful
  | _, .map p _ => p.Lawful

theorem Prog.good : {V : Type} → (p : Prog V) → p.Lawful → Good p.parse
  | _, .unit, _ => by
      intro X g hg
      have h := uniform_map g ⟨fun x => ((), x), Prod.snd, fun _ => rfl, fun _ => rfl⟩ hg
      convert h using 2 with s
      simp only [Prog.parse, Option.bind_some]
      rfl
  | _, .draw w pos dec, h => attempt_good w pos dec h
  | _, .seq (V := V) (W := W) p q, h => by
      intro X g hg
      have inner := q.good h.2 X g hg
      have outer := p.good h.1 _ _ inner
      have reassoc := uniform_map _ (Equiv.prodAssoc V W X).symm outer
      convert reassoc using 2 with s
      simp only [Prog.parse]
      cases p.parse s with
      | none => rfl
      | some r =>
        simp only [Option.bind_some]
        cases q.parse r.2 with
        | none => rfl
        | some t =>
          simp only [Option.map_some, Option.bind_some]
          cases g t.2 <;> rfl
  | _, .map (V := V) (W := W) p e, h => by
      intro X g hg
      have base := p.good h X g hg
      have mapped := uniform_map _ (Equiv.prodCongr e (Equiv.refl X)) base
      convert mapped using 2 with s
      simp only [Prog.parse]
      cases p.parse s with
      | none => rfl
      | some r =>
        simp only [Option.map_some, Option.bind_some]
        cases g r.2 <;> rfl

/-- The value a program reads from a buffer, discarding unread bytes. -/
def Prog.read {V : Type} (p : Prog V) (s : List Byte) : Option V := (p.parse s).map Prod.fst

theorem Prog.uniform {V : Type} (p : Prog V) (h : p.Lawful) : Uniform p.read := by
  have := uniform_map _ (Equiv.prodPUnit V) (p.good h Unit (fun _ => some ()) (by
    intro L x y; cases x; cases y; rfl))
  convert this using 2 with s
  simp only [Prog.read]
  cases p.parse s <;> rfl
/-! ## Composite draws -/

/-- `Reading::elements`: `n` draws in index order. -/
def Prog.vec {A : Type} (p : Prog A) : (n : ℕ) → Prog (Fin n → A)
  | 0 => .map .unit ⟨fun _ => Fin.elim0, fun _ => (), fun _ => rfl, fun _ => funext fun i => Fin.elim0 i⟩
  | n + 1 => .map (.seq p (p.vec n)) (Fin.consEquiv fun _ : Fin (n + 1) => A)

theorem Prog.vec_lawful {A : Type} (p : Prog A) (h : p.Lawful) : (n : ℕ) → (p.vec n).Lawful
  | 0 => trivial
  | n + 1 => ⟨h, p.vec_lawful h n⟩
/-! ## Availability: positive fibers -/

/-- Bytes read when no draw rejects. -/
def Prog.width : {V : Type} → Prog V → ℕ
  | _, .unit => 0
  | _, .draw w _ _ => w
  | _, .seq p q => p.width + q.width
  | _, .map p _ => p.width

/-- Every value has an accepted encoding. -/
def Prog.Onto : {V : Type} → Prog V → Prop
  | _, .unit => True
  | _, .draw _ _ dec => ∀ a, ∃ c, dec c = some a
  | _, .seq p q => p.Onto ∧ q.Onto
  | _, .map p _ => p.Onto

theorem Prog.encode : {V : Type} → (p : Prog V) → p.Onto → ∀ (v : V) (rest : List Byte),
    ∃ u : List Byte, u.length = p.width ∧ p.parse (u ++ rest) = some (v, rest)
  | _, .unit, _, v, rest => ⟨[], rfl, rfl⟩
  | _, .draw w pos dec, h, v, rest => by
      obtain ⟨c, hc⟩ := h v
      refine ⟨List.ofFn c, by simp [Prog.width], ?_⟩
      simp only [Prog.parse, attempt_append, hc]
  | _, .seq p q, h, v, rest => by
      obtain ⟨u₂, hl₂, hu₂⟩ := q.encode h.2 v.2 rest
      obtain ⟨u₁, hl₁, hu₁⟩ := p.encode h.1 v.1 (u₂ ++ rest)
      refine ⟨u₁ ++ u₂, by simp [Prog.width, hl₁, hl₂], ?_⟩
      simp [Prog.parse, List.append_assoc, hu₁, hu₂]
  | _, .map p e, h, v, rest => by
      obtain ⟨u, hl, hu⟩ := p.encode h (e.symm v) rest
      exact ⟨u, hl, by simp [Prog.parse, hu]⟩

/-- With at least `width` bytes, every value is read from some buffer. -/
theorem Prog.read_exists {V : Type} (p : Prog V) (h : p.Onto) (L : ℕ) (wide : p.width ≤ L) (v : V) :
    ∃ s : Fin L → Byte, p.read (List.ofFn s) = some v := by
  obtain ⟨u, hl, hu⟩ := p.encode h v (List.replicate (L - p.width) 0)
  have hlen : (u ++ List.replicate (L - p.width) 0).length = L := by simp [hl]; omega
  refine ⟨fun i => (u ++ List.replicate (L - p.width) 0)[i.val]'(by omega), ?_⟩
  have : List.ofFn (fun i : Fin L => (u ++ List.replicate (L - p.width) 0)[i.val]'(by omega)) =
      u ++ List.replicate (L - p.width) 0 := by
    apply List.ext_getElem <;> simp [hlen]
  rw [this, Prog.read, hu]
  rfl

theorem Prog.vec_onto {A : Type} (p : Prog A) (h : p.Onto) : (n : ℕ) → (p.vec n).Onto
  | 0 => trivial
  | n + 1 => ⟨h, p.vec_onto h n⟩

theorem Prog.vec_width {A : Type} (p : Prog A) : (n : ℕ) → (p.vec n).width = n * p.width
  | 0 => by simp [Prog.vec, Prog.width]
  | n + 1 => by simp [Prog.vec, Prog.width, Prog.vec_width p n]; ring

/-! ## Prefixes

A parse that succeeds on a buffer succeeds on every extension with the
same value and the extension as its rest. This is what makes reading
blocks lazily, as Rust does, equal to reading them eagerly. -/

section Attempt
variable {A : Type} (w : ℕ) (pos : 0 < w) (dec : (Fin w → Byte) → Option A)

theorem attempt_extend (s t : List Byte) (a : A) (r : List Byte)
    (h : attempt w pos dec s = some (a, r)) : attempt w pos dec (s ++ t) = some (a, r ++ t) := by
  induction hn : s.length using Nat.strong_induction_on generalizing s a r with
  | _ n ih =>
    rw [attempt] at h
    split at h
    · next hw =>
      rw [attempt, dif_pos (by simp; omega)]
      have hc : (fun i : Fin w => (s ++ t).get ⟨i, lt_of_lt_of_le i.isLt (by simp; omega)⟩) =
          (fun i : Fin w => s.get ⟨i, lt_of_lt_of_le i.isLt hw⟩) := by
        funext i; simp [List.getElem_append_left (lt_of_lt_of_le i.isLt hw)]
      have hd : (s ++ t).drop w = s.drop w ++ t := List.drop_append_of_le_length hw
      rw [hc, hd]
      split at h
      · next a' ha =>
        rw [ha]
        simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
      · next ha =>
        rw [ha]
        exact ih (s.drop w).length (by simp; omega) (s.drop w) a r h rfl
    · cases h

end Attempt

theorem Prog.parse_extend : {V : Type} → (p : Prog V) → ∀ (s t : List Byte) (v : V) (r : List Byte),
    p.parse s = some (v, r) → p.parse (s ++ t) = some (v, r ++ t)
  | _, .unit, s, t, v, r, h => by
      simp only [Prog.parse, Option.some.injEq] at h ⊢
      cases h; rfl
  | _, .draw w pos dec, s, t, v, r, h => attempt_extend w pos dec s t v r h
  | _, .seq p q, s, t, v, r, h => by
      simp only [Prog.parse] at h ⊢
      cases hp : p.parse s with
      | none => rw [hp] at h; cases h
      | some x =>
        rw [hp] at h
        simp only [Option.bind_some] at h
        rw [p.parse_extend s t x.1 x.2 hp]
        simp only [Option.bind_some]
        cases hq : q.parse x.2 with
        | none => rw [hq] at h; cases h
        | some y =>
          rw [hq] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [q.parse_extend x.2 t y.1 y.2 hq]
          cases h; rfl
  | _, .map p e, s, t, v, r, h => by
      simp only [Prog.parse] at h ⊢
      cases hp : p.parse s with
      | none => rw [hp] at h; cases h
      | some x =>
        rw [hp] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [p.parse_extend s t x.1 x.2 hp]
        cases h; rfl

theorem Prog.read_extend {V : Type} (p : Prog V) (s t : List Byte) (v : V) (h : p.read s = some v) :
    p.read (s ++ t) = some v := by
  unfold Prog.read at h ⊢
  cases hp : p.parse s with
  | none => rw [hp] at h; cases h
  | some x =>
    rw [hp] at h
    rw [p.parse_extend s t x.1 x.2 hp]
    exact h

end LfzkV2.Current.Protocol.RustSampler
