import LfzkV2.Current.Protocol.RustSamplerAbort
import TranscriptV2.StrandEncoding
import Merkle.TreeCompose

/-! A round's draws read from its PRF stream, `Word → Digest`: block
`counter` is the answer to `Input.prf id parent counter`
(`Prf::next_block` in `rust/src/runtime/v2/transcript/strand.rs`), and the
round's byte cursor (`Reader`) concatenates the blocks in counter order.

`lazySampler` is the reader as Rust runs it: it queries the next block only
when the bytes buffered so far do not finish the round's draws, and stops
after `blocks` blocks. Rust's counter is a `u64` checked before each block,
so a round reads at most `2^64 - 1` blocks (`rustBlocks`) and panics past
that point where the model returns `none`. `eagerSampler` reads the first `blocks`
blocks eagerly and parses them; both return the same value on every stream
(`lazySampler_run`), so the laws below are proved for the eager form.

Over total streams, each value of a lawful program is read by equally many
streams (`lazySampler_uniform`), every value is read by some stream when the
cap covers the reject-free width (`lazySampler_exists`), and the fraction of
streams on which a round aborts is the abort fraction of its parse
(`lazySampler_abort`). -/
noncomputable section
namespace LfzkV2.Current.Protocol.RustSampler
open Merkle.RandomOracle TranscriptV2

abbrev Word := Strand.Word
abbrev Digest := Strand.Digest

/-- Rust's PRF counter limit: `Prf::next_block` refuses counter `2^64 - 1`. -/
def rustBlocks : ℕ := 2 ^ 64 - 1

theorem rustBlocks_fits : rustBlocks ≤ 2 ^ 64 := by unfold rustBlocks; omega

def readBlocks : (n start : ℕ) → start + n ≤ 2 ^ 64 → Tree Word Digest (List Digest) n
  | 0, _, _ => .done []
  | n + 1, start, h => .query ⟨start, by omega⟩ fun d =>
      (readBlocks n (start + 1) (by omega)).map (d :: ·)

theorem readBlocks_run (H : Word → Digest) : (n start : ℕ) → (h : start + n ≤ 2 ^ 64) →
    ((readBlocks n start h).run H).1 = List.ofFn fun i : Fin n => H ⟨start + i, by omega⟩
  | 0, _, _ => rfl
  | n + 1, start, h => by
      rw [readBlocks, Tree.run_query]
      simp only [Tree.run_map, readBlocks_run H n (start + 1) (by omega), List.ofFn_succ]
      congr 2
      funext i
      congr 2
      simp only [Fin.val_succ]
      omega

/-- The eagerSampler for one round: read `blocks` counters, then parse. -/
def eagerSampler {V : Type} (p : Prog V) (blocks : ℕ) (fits : blocks ≤ 2 ^ 64) :
    Tree Word Digest (Option V) blocks :=
  (readBlocks blocks 0 (by omega)).map fun digests => p.read (digests.map List.ofFn).flatten

/-- Blocks to bytes, in stream order. -/
def bytesEquiv (n : ℕ) : (Fin n → Digest) ≃ (Fin (n * 32) → Byte) :=
  (Equiv.curry (Fin n) (Fin 32) Byte).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Byte))

theorem bytesEquiv_ofFn (n : ℕ) (pre : Fin n → Digest) :
    ((List.ofFn pre).map List.ofFn).flatten = List.ofFn (bytesEquiv n pre) := by
  rw [List.ofFn_mul, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, bytesEquiv, Equiv.trans_apply, Equiv.arrowCongr_apply,
    Equiv.coe_refl, Function.comp_apply, id]
  have : finProdFinEquiv.symm (⟨i * 32 + j, by omega⟩ : Fin (n * 32)) = (i, j) := by
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [this]
  rfl

/-- Restricting a total stream to its first `n` counters. -/
def prefixEquiv (n : ℕ) (fits : n ≤ 2 ^ 64) : Fin n ≃ {w : Word // w.val < n} where
  toFun i := ⟨⟨i.val, by omega⟩, i.isLt⟩
  invFun w := ⟨w.1.val, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_restrict {Q D : Type} (p : Q → Prop) [DecidablePred p]
    (P : ({x // p x} → D) → Prop) :
    Nat.card {H : Q → D // P (fun x => H x)} =
      Nat.card {pre // P pre} * Nat.card ({x // ¬ p x} → D) := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact ((Equiv.piEquivPiSubtypeProd p fun _ => D).subtypeEquiv fun _ => Iff.rfl).trans
    Equiv.prodSubtypeFstEquivSubtypeProd

/-- The endpoint law, for one round: every value has the same number of
total counter streams. -/
theorem eagerSampler_uniform {V : Type} (p : Prog V) (h : p.Lawful) (blocks : ℕ)
    (fits : blocks ≤ 2 ^ 64) (v v' : V) :
    Nat.card {H : Word → Digest // ((eagerSampler p blocks fits).run H).1 = some v} =
      Nat.card {H : Word → Digest // ((eagerSampler p blocks fits).run H).1 = some v'} := by
  have key : ∀ x : V, Nat.card {H : Word → Digest // ((eagerSampler p blocks fits).run H).1 = some x} =
      Nat.card (Fiber p.read (blocks * 32) x) *
        Nat.card ({w : Word // ¬ w.val < blocks} → Digest) := by
    intro x
    have hrun : ∀ H : Word → Digest, ((eagerSampler p blocks fits).run H).1 =
        p.read (List.ofFn (bytesEquiv blocks fun i => H ⟨i.val, by omega⟩)) := by
      intro H
      rw [eagerSampler, Tree.run_map, readBlocks_run H blocks 0 (by omega), ← bytesEquiv_ofFn]
      simp only [Nat.zero_add]
    simp only [hrun]
    refine (card_restrict (fun w : Word => w.val < blocks)
      (fun r => p.read (List.ofFn (bytesEquiv blocks fun i => r (prefixEquiv blocks fits i))) = some x)).trans ?_
    congr 1
    apply Nat.card_congr
    exact (((prefixEquiv blocks fits).arrowCongr (Equiv.refl Digest)).symm.trans
      (bytesEquiv blocks)).subtypeEquiv fun r => by
        rfl
  rw [key, key, p.uniform h]

theorem eagerSampler_run {V : Type} (p : Prog V) (blocks : ℕ) (fits : blocks ≤ 2 ^ 64) (H : Word → Digest) :
    ((eagerSampler p blocks fits).run H).1 =
      p.read (List.ofFn (bytesEquiv blocks fun i => H ⟨i.val, by omega⟩)) := by
  rw [eagerSampler, Tree.run_map, readBlocks_run H blocks 0 (by omega), ← bytesEquiv_ofFn]
  simp only [Nat.zero_add]

/-- Nonvacuity: when the cap covers the reject-free width, every value has a
stream, so the endpoint's fiber is positive. -/
theorem eagerSampler_exists {V : Type} (p : Prog V) (h : p.Onto) (blocks : ℕ) (fits : blocks ≤ 2 ^ 64)
    (wide : p.width ≤ blocks * 32) (v : V) :
    ∃ H : Word → Digest, ((eagerSampler p blocks fits).run H).1 = some v := by
  obtain ⟨s, hs⟩ := p.read_exists h (blocks * 32) wide v
  let pre := (bytesEquiv blocks).symm s
  refine ⟨fun w => if hw : w.val < blocks then pre ⟨w.val, hw⟩ else 0, ?_⟩
  rw [eagerSampler_run]
  convert hs
  rw [← (bytesEquiv blocks).apply_symm_apply s]
  congr 2
  funext i
  simp [pre, i.isLt]

/-! ## Abort fractions over streams -/

/-- Streams split into the first `blocks` counters, read as bytes, and the rest. -/
theorem eagerSampler_card {V : Type} (p : Prog V) (blocks : ℕ) (fits : blocks ≤ 2 ^ 64) (o : Option V) :
    Nat.card {H : Word → Digest // ((eagerSampler p blocks fits).run H).1 = o} =
      Nat.card {s : Fin (blocks * 32) → Byte // p.read (List.ofFn s) = o} *
        Nat.card ({w : Word // ¬ w.val < blocks} → Digest) := by
  simp only [eagerSampler_run]
  refine (card_restrict (fun w : Word => w.val < blocks)
    (fun r => p.read (List.ofFn (bytesEquiv blocks fun i => r (prefixEquiv blocks fits i))) = o)).trans ?_
  congr 1
  apply Nat.card_congr
  exact (((prefixEquiv blocks fits).arrowCongr (Equiv.refl Digest)).symm.trans
    (bytesEquiv blocks)).subtypeEquiv fun r => by rfl

/-- Over total PRF streams, a round aborts exactly as often as its parse
aborts on `32 * blocks` uniform bytes. -/
theorem eagerSampler_abort {V : Type} (p : Prog V) (blocks : ℕ) (fits : blocks ≤ 2 ^ 64) :
    (Nat.card {H : Word → Digest // ((eagerSampler p blocks fits).run H).1 = none} : ℚ) /
        Nat.card (Word → Digest) = abortRate p.read (blocks * 32) := by
  have total : Nat.card (Word → Digest) =
      Nat.card (Fin (blocks * 32) → Byte) * Nat.card ({w : Word // ¬ w.val < blocks} → Digest) := by
    have := eagerSampler_card (Prog.unit) blocks fits (some ())
    have all : ∀ H : Word → Digest, ((eagerSampler Prog.unit blocks fits).run H).1 = some () := by
      intro H; rw [eagerSampler_run]; rfl
    have all' : ∀ s : Fin (blocks * 32) → Byte, Prog.unit.read (List.ofFn s) = some () := fun _ => rfl
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv all), Nat.card_congr (Equiv.subtypeUnivEquiv all')] at this
    exact this
  rw [eagerSampler_card, total, abortRate]
  have hrest : (0 : ℚ) < Nat.card ({w : Word // ¬ w.val < blocks} → Digest) := by
    exact_mod_cast Nat.card_pos
  push_cast
  rw [show ((Nat.card (Fin (blocks * 32) → Byte) : ℕ) : ℚ) = 256 ^ (blocks * 32) by simp]
  field_simp

/-! ## The lazy reader -/

/-- Read the next block only while the parse needs more bytes. -/
def lazyAux {V : Type} (p : Prog V) : (n start : ℕ) → List Byte → start + n ≤ 2 ^ 64 →
    Tree Word Digest (Option V) n
  | 0, _, acc, _ => .done (p.read acc)
  | n + 1, start, acc, h =>
      match p.read acc with
      | some v => .done (some v)
      | none => .query ⟨start, by omega⟩ fun d => lazyAux p n (start + 1) (acc ++ List.ofFn d) (by omega)

def lazySampler {V : Type} (p : Prog V) (blocks : ℕ) (fits : blocks ≤ 2 ^ 64) :
    Tree Word Digest (Option V) blocks :=
  lazyAux p blocks 0 [] (by omega)

theorem lazyAux_run {V : Type} (p : Prog V) (H : Word → Digest) : (n start : ℕ) → (acc : List Byte) →
    (h : start + n ≤ 2 ^ 64) →
    ((lazyAux p n start acc h).run H).1 =
      p.read (acc ++ ((List.ofFn fun i : Fin n => H ⟨start + i, by omega⟩).map List.ofFn).flatten)
  | 0, _, acc, _ => by simp [lazyAux]
  | n + 1, start, acc, h => by
      rw [lazyAux]
      cases hr : p.read acc with
      | some v =>
        simp only [Tree.run_done]
        exact (p.read_extend acc _ v hr).symm
      | none =>
        simp only [Tree.run_query]
        rw [lazyAux_run p H n (start + 1) (acc ++ List.ofFn (H ⟨start, by omega⟩)) (by omega)]
        congr 1
        have key : (List.ofFn fun i : Fin (n + 1) => H ⟨start + i, by omega⟩) =
            H ⟨start, by omega⟩ :: List.ofFn fun i : Fin n => H ⟨start + 1 + i, by omega⟩ := by
          rw [List.ofFn_succ]
          congr 2
          funext i
          congr 2
          simp only [Fin.val_succ]
          omega
        rw [key, List.map_cons, List.flatten_cons, List.append_assoc]

/-- The lazy reader and the eager model return the same value on every stream. -/
theorem lazySampler_run {V : Type} (p : Prog V) (blocks : ℕ) (fits : blocks ≤ 2 ^ 64) (H : Word → Digest) :
    ((lazySampler p blocks fits).run H).1 = ((eagerSampler p blocks fits).run H).1 := by
  rw [lazySampler, lazyAux_run, eagerSampler, Tree.run_map, readBlocks_run]
  simp


theorem lazySampler_uniform {V : Type} (p : Prog V) (h : p.Lawful) (blocks : ℕ)
    (fits : blocks ≤ 2 ^ 64) (v v' : V) :
    Nat.card {H : Word → Digest // ((lazySampler p blocks fits).run H).1 = some v} =
      Nat.card {H : Word → Digest // ((lazySampler p blocks fits).run H).1 = some v'} := by
  simp only [lazySampler_run]
  exact eagerSampler_uniform p h blocks fits v v'

theorem lazySampler_exists {V : Type} (p : Prog V) (h : p.Onto) (blocks : ℕ) (fits : blocks ≤ 2 ^ 64)
    (wide : p.width ≤ blocks * 32) (v : V) :
    ∃ H : Word → Digest, ((lazySampler p blocks fits).run H).1 = some v := by
  simp only [lazySampler_run]
  exact eagerSampler_exists p h blocks fits wide v

theorem lazySampler_abort {V : Type} (p : Prog V) (blocks : ℕ) (fits : blocks ≤ 2 ^ 64) :
    (Nat.card {H : Word → Digest // ((lazySampler p blocks fits).run H).1 = none} : ℚ) /
        Nat.card (Word → Digest) = abortRate p.read (blocks * 32) := by
  simp only [lazySampler_run]
  exact eagerSampler_abort p blocks fits

end LfzkV2.Current.Protocol.RustSampler
