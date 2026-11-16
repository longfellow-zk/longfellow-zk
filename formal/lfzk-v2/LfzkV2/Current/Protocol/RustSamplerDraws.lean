import LfzkV2.Current.Protocol.RustSamplerAbort
import LfzkV2.Current.OpeningFisherYates
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.Positivity

/-! The elementary draws of the v2 Rust reader, with their exact widths,
their balance, every value's reachability and their rejection rates.

* `gf`: `Gf2_128Field::sample` (`rust/src/runtime/algebra/gf2_128.rs`) reads
  16 bytes as `u128::from_le_bytes` and never rejects. Bit `i` of that
  integer is the coefficient of the `i`th packing basis vector, which Rust's
  `native_basis` defines as `Gf2_128::from(1u128 << i)`
  (`rust/src/runtime/algebra/packing/binary.rs`); `gfBits` is this map.
* `fp`: `FpGenericField::sample` (`rust/src/runtime/algebra/fp_generic.rs`)
  for a 256-bit modulus reads `sample_byte_count = 32` bytes, masks the top
  byte with `sample_high_mask = 0xff` (no bit cleared), reads the limbs little
  endian (`bytes_to_element`) and rejects values at or above the modulus.
* `gfNonzero`, `fpNonzero`: `Reading::nonzero`
  (`rust/src/runtime/v2/transcript/session.rs`) repeats `elt_field` until the
  value is not zero. Since a rejected prime attempt also restarts with a fresh
  32-byte read, one attempt of either loop reads one element width and
  accepts exactly the nonzero field elements.
* `natDec`: `Reading::nat(n)` reads `len = ceil(bits/8)` bytes, where `bits`
  is the bit length of `n-1`, masks them to `bits` bits and rejects at or
  above `n`; `nat(1)` reads nothing. For `n = 2443` this is two bytes with
  mask `0xfff`.
* `Prog.choices`: `Reading::choose(out, n, ..)` draws the offsets
  `nat(n), nat(n-1), ...`, one per output, and applies the partial
  Fisher-Yates swap that `OpeningFisherYates.ordered` already models. -/
noncomputable section
namespace LfzkV2.Current.Protocol.RustSampler
open Finset

/-- Little-endian bytes as an index (`u128::from_le_bytes`, `Limb::from_le_bytes`). -/
def le (w : ℕ) : (Fin w → Byte) ≃ Fin (256 ^ w) := finFunctionFinEquiv

theorem balanced_of_index {A : Type} (w N : ℕ) (e : (Fin w → Byte) ≃ Fin N)
    (g : Fin N → Option A) (k : ℕ) (hg : ∀ a, Nat.card {n // g n = some a} = k) :
    Balanced w (fun c => g (e c)) :=
  ⟨k, fun a => (Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)).trans (hg a)⟩

theorem card_one {N : Type} {A : Type} (g : N → Option A) (a : A) (n : N) (hn : g n = some a)
    (unique : ∀ m, g m = some a → m = n) : Nat.card {m // g m = some a} = 1 :=
  Nat.card_eq_one_iff_exists.mpr ⟨⟨n, hn⟩, fun m => Subtype.ext (unique m.1 m.2)⟩

/-- The rejection rate of a decoder from its count of values. -/
theorem reject_eq {A : Type} [Fintype A] (w : ℕ) (dec : (Fin w → Byte) → Option A) (k : ℕ)
    (hk : ∀ a, Nat.card {c // dec c = some a} = k) :
    reject w dec = 1 - (Fintype.card A * k : ℚ) / 256 ^ w := by
  have h := reject_card w dec k hk
  unfold reject
  have hpos : (0 : ℚ) < 256 ^ w := by positivity
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast h

/-! ## GF(2^128) -/

/-- The Rust bit order of a GF(2^128) sample: little-endian bytes, and bit
`i` of the integer is the coefficient of `basis i`. -/
def gfBits {B : Type} [AddCommGroup B] [Module (ZMod 2) B]
    (basis : Module.Basis (Fin 128) (ZMod 2) B) : Fin (256 ^ 16) ≃ B :=
  (finCongr (by norm_num : 256 ^ 16 = 2 ^ 128)).trans
    (finFunctionFinEquiv.symm.trans basis.equivFun.symm.toEquiv)

/-- The little-endian index of `w` bytes: byte `i` has weight `256^i`. -/
theorem le_val (w : ℕ) (c : Fin w → Byte) : ((le w) c).val = ∑ i, (c i).val * 256 ^ i.val :=
  finFunctionFinEquiv_apply c

/-- Bit `i` of a sample is the coefficient of `basis i`: Rust's
`Gf2_128::from(u128)` on the packing basis `native_basis`. -/
theorem gfBits_repr {B : Type} [AddCommGroup B] [Module (ZMod 2) B]
    (basis : Module.Basis (Fin 128) (ZMod 2) B) (n : Fin (256 ^ 16)) (i : Fin 128) :
    (basis.repr (gfBits basis n) i).val = n.val / 2 ^ i.val % 2 := by
  have h := finFunctionFinEquiv_symm_apply_val (finCongr (by norm_num : 256 ^ 16 = 2 ^ 128) n) i
  change (basis.equivFun (basis.equivFun.symm (finFunctionFinEquiv.symm
    (finCongr (by norm_num : 256 ^ 16 = 2 ^ 128) n))) i).val = _
  rw [LinearEquiv.apply_symm_apply]
  exact h

/-- `Gf2_128Field::sample`: 16 bytes, no rejection. -/
def gf {B : Type} (bits : Fin (256 ^ 16) ≃ B) (n : Fin (256 ^ 16)) : Option B := some (bits n)

theorem gf_card {B : Type} (bits : Fin (256 ^ 16) ≃ B) (b : B) :
    Nat.card {n // gf bits n = some b} = 1 :=
  card_one _ b (bits.symm b) (by simp [gf]) (by
    intro m hm
    simp only [gf, Option.some.injEq] at hm
    rw [← hm, Equiv.symm_apply_apply])

theorem gf_balanced {B : Type} (bits : Fin (256 ^ 16) ≃ B) :
    Balanced 16 (fun c => gf bits (le 16 c)) :=
  balanced_of_index 16 _ (le 16) (gf bits) 1 (gf_card bits)

/-- The binary `nonzero`: reject the zero element. -/
def gfNonzero {B : Type} [Zero B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B) (n : Fin (256 ^ 16)) :
    Option {z : B // z ≠ 0} :=
  if h : bits n ≠ 0 then some ⟨bits n, h⟩ else none

theorem gfNonzero_card {B : Type} [Zero B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B)
    (b : {z : B // z ≠ 0}) : Nat.card {n // gfNonzero bits n = some b} = 1 :=
  card_one _ b (bits.symm b.1) (by simp [gfNonzero, b.2]) (by
    intro m hm
    unfold gfNonzero at hm
    split at hm
    · simp only [Option.some.injEq] at hm
      rw [← hm, Equiv.symm_apply_apply]
    · cases hm)

theorem gfNonzero_balanced {B : Type} [Zero B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B) :
    Balanced 16 (fun c => gfNonzero bits (le 16 c)) :=
  balanced_of_index 16 _ (le 16) (gfNonzero bits) 1 (gfNonzero_card bits)

theorem gf_onto {B : Type} (bits : Fin (256 ^ 16) ≃ B) (b : B) :
    ∃ c, gf bits (le 16 c) = some b :=
  ⟨(le 16).symm (bits.symm b), by simp [gf]⟩

theorem gfNonzero_onto {B : Type} [Zero B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B)
    (b : {z : B // z ≠ 0}) : ∃ c, gfNonzero bits (le 16 c) = some b :=
  ⟨(le 16).symm (bits.symm b.1), by simp [gfNonzero, b.2]⟩

theorem gf_reject {B : Type} (bits : Fin (256 ^ 16) ≃ B) :
    reject 16 (fun c => gf bits (le 16 c)) = 0 := by
  unfold reject
  have : IsEmpty {c // gf bits (le 16 c) = none} := ⟨fun ⟨c, hc⟩ => by simp [gf] at hc⟩
  rw [Nat.card_of_isEmpty]
  simp

theorem gfNonzero_reject {B : Type} [Zero B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B) :
    reject 16 (fun c => gfNonzero bits (le 16 c)) = 1 / 256 ^ 16 := by
  unfold reject
  have one : Nat.card {c // gfNonzero bits (le 16 c) = none} = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨(le 16).symm (bits.symm 0), by simp [gfNonzero]⟩, fun c => Subtype.ext ?_⟩
    have hc := c.2
    unfold gfNonzero at hc
    split at hc
    · cases hc
    · next h =>
      rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply]
      exact (not_not.mp h)
  rw [one]
  norm_num

/-! ## Prime fields -/

section Prime
variable (p : ℕ) [NeZero p] (fits : p ≤ 256 ^ 32)

/-- `FpGenericField::sample` for a 256-bit modulus: 32 bytes, high mask
`0xff`, rejected at or above the modulus. -/
def fp (n : Fin (256 ^ 32)) : Option (ZMod p) :=
  if h : n.val < p then some (ZMod.finEquiv p ⟨n.val, h⟩) else none

include fits in
theorem fp_card (a : ZMod p) : Nat.card {n // fp p n = some a} = 1 :=
  let i := (ZMod.finEquiv p).symm a
  card_one _ a ⟨i.val, lt_of_lt_of_le i.isLt fits⟩ (by simp [fp, i]) (by
    intro m hm
    unfold fp at hm
    split at hm
    · simp only [Option.some.injEq] at hm
      apply Fin.ext
      change m.val = ((ZMod.finEquiv p).symm a).val
      rw [← hm, RingEquiv.symm_apply_apply]
    · cases hm)

include fits in
theorem fp_balanced : Balanced 32 (fun c => fp p (le 32 c)) :=
  balanced_of_index 32 _ (le 32) (fp p) 1 (fp_card p fits)

/-- `Reading::nonzero` on a prime field: the element loop and the zero
loop together reject exactly indices `0` and `≥ p`, 32 bytes per attempt. -/
def fpNonzero (n : Fin (256 ^ 32)) : Option {z : ZMod p // z ≠ 0} :=
  if h : n.val < p then
    if hz : ZMod.finEquiv p ⟨n.val, h⟩ ≠ 0 then some ⟨_, hz⟩ else none
  else none

include fits in
theorem fpNonzero_card (a : {z : ZMod p // z ≠ 0}) : Nat.card {n // fpNonzero p n = some a} = 1 :=
  let i := (ZMod.finEquiv p).symm a.1
  card_one _ a ⟨i.val, lt_of_lt_of_le i.isLt fits⟩ (by simp [fpNonzero, i, a.2]) (by
    intro m hm
    unfold fpNonzero at hm
    split at hm
    · split at hm
      · simp only [Option.some.injEq] at hm
        apply Fin.ext
        change m.val = ((ZMod.finEquiv p).symm a.1).val
        rw [← hm, RingEquiv.symm_apply_apply]
      · cases hm
    · cases hm)

include fits in
theorem fpNonzero_balanced : Balanced 32 (fun c => fpNonzero p (le 32 c)) :=
  balanced_of_index 32 _ (le 32) (fpNonzero p) 1 (fpNonzero_card p fits)

include fits in
theorem fp_onto (a : ZMod p) : ∃ c, fp p (le 32 c) = some a :=
  ⟨(le 32).symm ⟨((ZMod.finEquiv p).symm a).val, lt_of_lt_of_le (Fin.isLt _) fits⟩, by simp [fp]⟩

include fits in
theorem fpNonzero_onto (a : {z : ZMod p // z ≠ 0}) : ∃ c, fpNonzero p (le 32 c) = some a :=
  ⟨(le 32).symm ⟨((ZMod.finEquiv p).symm a.1).val, lt_of_lt_of_le (Fin.isLt _) fits⟩,
    by simp [fpNonzero, a.2]⟩

include fits in
theorem fp_reject : reject 32 (fun c => fp p (le 32 c)) = 1 - (p : ℚ) / 256 ^ 32 := by
  rw [reject_eq 32 _ 1 fun a => (Nat.card_congr ((le 32).subtypeEquiv fun _ => Iff.rfl)).trans
    (fp_card p fits a), ZMod.card]
  push_cast
  ring

include fits in
theorem fpNonzero_reject :
    reject 32 (fun c => fpNonzero p (le 32 c)) = 1 - ((p : ℚ) - 1) / 256 ^ 32 := by
  rw [reject_eq 32 _ 1 fun a => (Nat.card_congr ((le 32).subtypeEquiv fun _ => Iff.rfl)).trans
    (fpNonzero_card p fits a)]
  have hcard : Fintype.card {z : ZMod p // z ≠ 0} = p - 1 := by
    have := Fintype.card_subtype_compl (fun z : ZMod p => z = 0)
    simp only [Fintype.card_subtype_eq, ZMod.card] at this
    exact this
  rw [hcard, Nat.cast_sub (NeZero.one_le)]
  push_cast
  ring

end Prime

/-! ## Bounded integers -/

/-- `usize::BITS - (n-1).leading_zeros()`, the bit length of `n-1`. -/
def natBits (n : ℕ) : ℕ := Nat.size (n - 1)

/-- `bits.div_ceil(8)`. -/
def natLen (n : ℕ) : ℕ := (natBits n + 7) / 8

theorem natBits_le (n : ℕ) : natBits n ≤ 8 * natLen n := by
  unfold natLen; omega

theorem le_two_pow_natBits (n : ℕ) (h : 0 < n) : n ≤ 2 ^ natBits n := by
  unfold natBits
  have := Nat.lt_size_self (n - 1)
  omega

/-- Below the bound, the mask cuts at most half of its range. -/
theorem two_pow_natBits_le (n : ℕ) (h : 1 < n) : 2 ^ natBits n ≤ 2 * n := by
  unfold natBits
  have hpos : 0 < Nat.size (n - 1) := Nat.size_pos.mpr (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hpos
  have hle : 2 ^ k ≤ n - 1 := Nat.lt_size.mp (by omega)
  rw [hk, show 0 + k + 1 = k + 1 by omega, pow_succ]
  omega

/-- One attempt of `nat(n)`, `n ≥ 2`: the masked low `natBits n` bits,
rejected at or above `n`. -/
def natDec (n : ℕ) (x : Fin (256 ^ natLen n)) : Option (Fin n) :=
  if h : x.val % 2 ^ natBits n < n then some ⟨x.val % 2 ^ natBits n, h⟩ else none

theorem pow_split (n : ℕ) : 256 ^ natLen n = 2 ^ (8 * natLen n - natBits n) * 2 ^ natBits n := by
  rw [← pow_add, Nat.sub_add_cancel (natBits_le n), pow_mul]
  norm_num

/-- Every accepted offset has one encoding per value of the masked-off bits. -/
theorem natDec_card (n : ℕ) (a : Fin n) :
    Nat.card {x // natDec n x = some a} = 2 ^ (8 * natLen n - natBits n) := by
  have ha : a.val < 2 ^ natBits n := lt_of_lt_of_le a.isLt (le_two_pow_natBits n (by have := a.isLt; omega))
  have hpos : 0 < 2 ^ natBits n := by positivity
  set M := 2 ^ natBits n
  set Q := 2 ^ (8 * natLen n - natBits n)
  have split : 256 ^ natLen n = Q * M := pow_split n
  have e : {x // natDec n x = some a} ≃ Fin Q := {
    toFun x := ⟨x.1.val / M, by
      have : x.1.val < M * Q := by rw [Nat.mul_comm, ← split]; exact x.1.isLt
      exact Nat.div_lt_of_lt_mul this⟩
    invFun q := ⟨⟨a.val + M * q.val, by
      rw [split]
      have := q.isLt
      calc a.val + M * q.val < M + M * q.val := by omega
        _ = M * (q.val + 1) := by ring
        _ ≤ M * Q := Nat.mul_le_mul_left _ this
        _ = Q * M := Nat.mul_comm _ _⟩, by
      simp only [natDec]
      have hm : (a.val + M * q.val) % M = a.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      rw [dif_pos (by rw [hm]; exact a.isLt)]
      exact congrArg some (Fin.ext hm)⟩
    left_inv x := by
      obtain ⟨x, hx⟩ := x
      apply Subtype.ext; apply Fin.ext
      simp only [natDec] at hx
      split at hx
      · simp only [Option.some.injEq] at hx
        have h1 := congrArg Fin.val hx
        simp only at h1 ⊢
        rw [← h1]
        exact Nat.mod_add_div x.val M
      · cases hx
    right_inv q := by
      apply Fin.ext
      simp only
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, Nat.zero_add] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem natLen_pos (n : ℕ) (h : 1 < n) : 0 < natLen n := by
  have : 1 ≤ natBits n := by
    unfold natBits; exact Nat.size_pos.mpr (by omega)
  unfold natLen; omega

/-- `Reading::nat(n)` as a program: no read for `n = 1`. -/
def Prog.nat (n : ℕ) (h : 0 < n) : Prog (Fin n) :=
  if h1 : n = 1 then .map .unit ⟨fun _ => ⟨0, h⟩, fun _ => (), fun _ => rfl,
    fun x => Fin.ext (by have := x.isLt; omega)⟩
  else .draw (natLen n) (natLen_pos n (by omega)) fun c => natDec n (le _ c)

theorem Prog.nat_lawful (n : ℕ) (h : 0 < n) : (Prog.nat n h).Lawful := by
  unfold Prog.nat
  split
  · trivial
  · exact balanced_of_index _ _ (le _) (natDec n) _ (natDec_card n)

theorem Prog.nat_onto (n : ℕ) (h : 0 < n) : (Prog.nat n h).Onto := by
  unfold Prog.nat
  split
  · trivial
  · intro a
    have ha : a.val < 2 ^ natBits n := lt_of_lt_of_le a.isLt (le_two_pow_natBits n h)
    refine ⟨(le _).symm ⟨a.val, lt_of_lt_of_le ha ?_⟩, ?_⟩
    · rw [pow_split n]; exact Nat.le_mul_of_pos_left _ (by positivity)
    · simp [natDec, Nat.mod_eq_of_lt ha]

theorem natDec_reject (n : ℕ) :
    reject (natLen n) (fun c => natDec n (le _ c)) = 1 - (n : ℚ) / 2 ^ natBits n := by
  rw [reject_eq _ _ _ fun a => (Nat.card_congr ((le _).subtypeEquiv fun _ => Iff.rfl)).trans
    (natDec_card n a), Fintype.card_fin]
  have hs : (256 : ℚ) ^ natLen n = 2 ^ (8 * natLen n - natBits n) * 2 ^ natBits n := by
    exact_mod_cast pow_split n
  rw [hs]
  push_cast
  have : (2 : ℚ) ^ (8 * natLen n - natBits n) ≠ 0 := by positivity
  field_simp

theorem Prog.nat_halving (n : ℕ) (h : 0 < n) : (Prog.nat n h).Halving := by
  unfold Prog.nat
  split
  · trivial
  · next h1 =>
    show reject _ _ ≤ 1 / 2
    rw [natDec_reject n]
    have h2 : (2 : ℚ) ^ natBits n ≤ 2 * n := by exact_mod_cast two_pow_natBits_le n (by omega)
    have hp : (0 : ℚ) < 2 ^ natBits n := by positivity
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hp]
    linarith

theorem Prog.nat_draws_le (n : ℕ) (h : 0 < n) : (Prog.nat n h).draws ≤ 1 := by
  unfold Prog.nat
  split <;> simp [Prog.draws]

/-! ## Ordered openings -/

open LfzkV2.Current.OpeningFisherYates

/-- `Reading::choose` with `out.len() = t`: the offsets `nat(n), nat(n-1),
...`, `t` of them. `choose` asserts `t ≤ n`; with `t > n` there is no
opening and no attempt accepts. -/
def Prog.choices : (n t : ℕ) → Prog (Choices n t)
  | _, 0 => .unit
  | 0, _ + 1 => .draw 1 (by decide) fun _ => none
  | n + 1, t + 1 => .seq (Prog.nat (n + 1) (Nat.succ_pos n)) (Prog.choices n t)
termination_by structural _ t => t

theorem Prog.choices_lawful : (n t : ℕ) → (Prog.choices n t).Lawful
  | _, 0 => trivial
  | 0, _ + 1 => ⟨0, fun e => Empty.elim e⟩
  | n + 1, t + 1 => ⟨Prog.nat_lawful (n + 1) _, Prog.choices_lawful n t⟩

theorem Prog.choices_onto : (n t : ℕ) → t ≤ n → (Prog.choices n t).Onto
  | _, 0, _ => trivial
  | 0, _ + 1, h => by omega
  | n + 1, t + 1, h => ⟨Prog.nat_onto (n + 1) _, Prog.choices_onto n t (by omega)⟩

theorem Prog.choices_halving : (n t : ℕ) → t ≤ n → (Prog.choices n t).Halving
  | _, 0, _ => trivial
  | 0, _ + 1, h => by omega
  | n + 1, t + 1, h => ⟨Prog.nat_halving (n + 1) _, Prog.choices_halving n t (by omega)⟩

theorem Prog.choices_draws_le : (n t : ℕ) → t ≤ n → (Prog.choices n t).draws ≤ t
  | _, 0, _ => le_refl _
  | 0, _ + 1, h => by omega
  | n + 1, t + 1, h => by
      have := Prog.nat_draws_le (n + 1) (Nat.succ_pos n)
      have := Prog.choices_draws_le n t (by omega)
      simp only [Prog.choices, Prog.draws]
      omega

/-- An ordered opening: the offsets, then the partial Fisher-Yates swap. -/
def Prog.opening (n t : ℕ) : Prog (Fin t ↪ Fin n) :=
  .map (Prog.choices n t) (ordered n t)

theorem Prog.opening_lawful (n t : ℕ) : (Prog.opening n t).Lawful :=
  Prog.choices_lawful n t

theorem Prog.opening_onto (n t : ℕ) (h : t ≤ n) : (Prog.opening n t).Onto :=
  Prog.choices_onto n t h

theorem Prog.opening_halving (n t : ℕ) (h : t ≤ n) : (Prog.opening n t).Halving :=
  Prog.choices_halving n t h

/-! ## The deployed opening

`choose(2443, 84)` reads two bytes per attempt with mask `0xfff`, and its
offsets reject at most `1736/4096` of their attempts. -/

theorem natBits_twelve (n : ℕ) (lo : 2048 < n) (hi : n ≤ 4096) : natBits n = 12 := by
  unfold natBits
  apply le_antisymm
  · exact Nat.size_le.mpr (by norm_num; omega)
  · exact Nat.lt_size.mpr (by norm_num; omega)

theorem natLen_two (n : ℕ) (lo : 2048 < n) (hi : n ≤ 4096) : natLen n = 2 := by
  unfold natLen; rw [natBits_twelve n lo hi]

theorem choices_abortSum (j : ℕ) : (n t : ℕ) → t ≤ n → 2048 < n + 1 - t → n ≤ 4096 →
    (Prog.choices n t).abortSum j ≤ t * (((4096 : ℚ) - ((n + 1 - t : ℕ) : ℚ)) / 4096) ^ j
  | _, 0, _, _, _ => by simp [Prog.choices, Prog.abortSum]
  | 0, _ + 1, h, _, _ => by omega
  | n + 1, t + 1, h, lo, hi => by
      have ih := choices_abortSum j n t (by omega) (by omega) (by omega)
      have h1 : n + 1 ≠ 1 := by omega
      simp only [Prog.choices, Prog.abortSum, Prog.nat, dif_neg h1]
      rw [natDec_reject (n + 1), natBits_twelve (n + 1) (by omega) hi]
      have base0 : 0 ≤ 1 - ((n + 1 : ℕ) : ℚ) / 2 ^ 12 := by
        have : ((n + 1 : ℕ) : ℚ) ≤ 4096 := by exact_mod_cast hi
        rw [sub_nonneg, div_le_one (by norm_num)]; push_cast at this ⊢; linarith
      have mono : (1 - ((n + 1 : ℕ) : ℚ) / 2 ^ 12) ^ j ≤
          (((4096 : ℚ) - ((n + 1 + 1 - (t + 1) : ℕ) : ℚ)) / 4096) ^ j := by
        apply pow_le_pow_left₀ base0
        have : ((n + 1 + 1 - (t + 1) : ℕ) : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega)
        rw [show (2 : ℚ) ^ 12 = 4096 by norm_num, one_sub_div (by norm_num : (4096 : ℚ) ≠ 0)]
        apply div_le_div_of_nonneg_right _ (by norm_num)
        push_cast at this ⊢
        linarith
      have same : ((n + 1 - t : ℕ) : ℚ) = ((n + 1 + 1 - (t + 1) : ℕ) : ℚ) := by congr 1; omega
      rw [same] at ih
      push_cast at ih mono ⊢
      have := add_le_add mono ih
      linarith [show ((t : ℚ) + 1) * (((4096 : ℚ) - ((n + 1 - t : ℕ) : ℚ)) / 4096) ^ j =
        (((4096 : ℚ) - ((n + 1 - t : ℕ) : ℚ)) / 4096) ^ j + t * (((4096 : ℚ) - ((n + 1 - t : ℕ) : ℚ)) / 4096) ^ j by ring]

/-- `choose(2443, 84)` with `j` attempts per offset aborts on at most
`84 (1736/4096)^j` of all byte buffers. -/
theorem opening_abort (j L : ℕ) (wide : j * 168 ≤ L) :
    abortRate (Prog.opening 2443 84).read L ≤ 84 * ((1736 : ℚ) / 4096) ^ j := by
  have width : (Prog.opening 2443 84).width = 168 := by decide +kernel
  have h := (Prog.opening 2443 84).read_abort j L (by rw [width]; exact wide)
  have hs := choices_abortSum j 2443 84 (by decide) (by decide) (by decide)
  refine h.trans (le_of_eq_of_le rfl (hs.trans (le_of_eq ?_)))
  norm_num

end LfzkV2.Current.Protocol.RustSampler
