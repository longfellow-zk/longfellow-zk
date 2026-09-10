import Mathlib
import Heap
import Binding
import Hiding

/-!
# Concrete fixed-width encodings and 256-bit parameter arithmetic

The Rust implementation hashes raw concatenations: 32 nonce bytes followed by
caller-supplied leaf bytes, and two 32-byte digests for an internal node.  We
model a fixed caller leaf length `ell`; this is the strongest faithful theorem
available because the Rust callback is intentionally variable-length.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

/-- One byte and a fixed-width byte string. -/
abbrev Byte := Fin 256
abbrev Bytes (n : ℕ) := Fin n → Byte

/-- The concrete 32-byte type used for both nonces and digests. -/
abbrev Bits256 := Bytes 32

@[simp] theorem card_Bits256 : Fintype.card Bits256 = 2 ^ 256 := by
  simp [Bits256, Bytes, Byte]

/-- Untagged fixed-width concatenation into the common SHA-256 input type. -/
def concatEncoding {n m : ℕ} (p : Bytes n × Bytes m) : List Byte :=
  List.ofFn p.1 ++ List.ofFn p.2

/-- The concrete leaf encoding for a fixed caller-supplied leaf length. -/
def concreteLeafEncoding (ell : ℕ) : Bits256 × Bytes ell → List Byte :=
  concatEncoding

/-- The concrete internal-node encoding is exactly 64 bytes. -/
def concreteNodeEncoding : Bits256 × Bits256 → List Byte :=
  concatEncoding

/-- Fixed-width raw concatenation is injective. -/
theorem concatEncoding_injective {n m : ℕ} :
    Function.Injective (@concatEncoding n m) := by
  intro a b h
  have hp := List.append_inj h (by simp)
  apply Prod.ext
  · exact List.ofFn_injective hp.1
  · exact List.ofFn_injective hp.2

theorem concreteLeafEncoding_injective (ell : ℕ) :
    Function.Injective (concreteLeafEncoding ell) :=
  concatEncoding_injective

theorem concreteNodeEncoding_injective :
    Function.Injective concreteNodeEncoding :=
  concatEncoding_injective

/-- The concrete untagged codec: 32-byte salt ‖ `ell`-byte payload at leaves,
32-byte ‖ 32-byte at internal nodes, both into the same `List Byte`. -/
def concreteCodec (ell : ℕ) : Codec Bits256 (Bytes ell) Bits256 (List Byte) where
  leafEnc := concreteLeafEncoding ell
  nodeEnc := concreteNodeEncoding

theorem concreteCodec_inj (ell : ℕ) : (concreteCodec ell).Inj :=
  ⟨concreteLeafEncoding_injective ell, concreteNodeEncoding_injective⟩

/-- For a fixed leaf payload, distinct 32-byte salts give distinct raw oracle
inputs.  This is the concrete no-heavy-fiber fact used by `salt_hit_card_le`. -/
theorem concreteLeafEncoding_salt_injective (ell : ℕ) (m : Bytes ell) :
    Function.Injective (fun salt : Bits256 =>
      concreteLeafEncoding ell (salt, m)) := by
  intro salt₀ salt₁ h
  exact congrArg Prod.fst (concreteLeafEncoding_injective ell h)

/-- Fixing either child leaves an injective node-input coordinate. -/
theorem concreteNodeEncoding_left_injective (right : Bits256) :
    Function.Injective (fun left : Bits256 =>
      concreteNodeEncoding (left, right)) := by
  intro left₀ left₁ h
  exact congrArg Prod.fst (concreteNodeEncoding_injective h)

theorem concreteNodeEncoding_right_injective (left : Bits256) :
    Function.Injective (fun right : Bits256 =>
      concreteNodeEncoding (left, right)) := by
  intro right₀ right₁ h
  exact congrArg Prod.snd (concreteNodeEncoding_injective h)

/-- The untagged leaf and node ranges overlap exactly for 32-byte leaf data.
This records the implementation's real aliasing boundary rather than
silently replacing raw bytes by disjoint constructors. -/
theorem concrete_ranges_overlap_iff (ell : ℕ) :
    (∃ leaf : Bits256 × Bytes ell, ∃ node : Bits256 × Bits256,
      concreteLeafEncoding ell leaf = concreteNodeEncoding node) ↔
      ell = 32 := by
  constructor
  · rintro ⟨leaf, node, heq⟩
    have hlen := congrArg List.length heq
    simp [concreteLeafEncoding, concreteNodeEncoding, concatEncoding] at hlen
    omega
  · intro hell
    subst ell
    let z : Bits256 := fun _ => 0
    exact ⟨(z, z), (z, z), rfl⟩

/-- Away from 32-byte leaf data, leaf and internal inputs are disjoint merely
because their raw byte lengths differ. -/
theorem concrete_ranges_disjoint_of_ne (ell : ℕ) (h : ell ≠ 32) :
    Set.range (concreteLeafEncoding ell) ∩
      Set.range concreteNodeEncoding = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro ⟨leaf, hleaf⟩ hnode
  rcases hnode with ⟨node, hnode⟩
  apply h
  rw [← concrete_ranges_overlap_iff ell]
  exact ⟨leaf, node, hleaf.trans hnode.symm⟩

/-- A `2^16`-leaf heap has maximum depth 16.  Proved from the defining
bracket of `Nat.log`, not by `native_decide`: the latter would add
`Lean.ofReduceBool` to the axiom set of every downstream concrete bound. -/
theorem heapDepth_65536 : Heap.heapDepth (2 ^ 16) = 16 := by
  rw [Heap.heapDepth, Nat.log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)

/-- With 256-bit salt and digest spaces, the common-denominator basic hiding
numerator simplifies to `(t+t²)·2^256`. -/
theorem basicHidingNumerator_256 (t : ℕ) :
    basicHidingNumerator (2 ^ 256) (2 ^ 256) t =
      (t + t ^ 2) * 2 ^ 256 := by
  simp [basicHidingNumerator]
  ring

/-- The query-aware binding numerator at `n=2^16` (so `dmax+1=17`) is the
birthday numerator plus `17²`. -/
theorem bindingNumerator_65536 (t : ℕ) :
    t * (t - 1) / 2 + (Heap.heapDepth (2 ^ 16) + 1) ^ 2 =
      t * (t - 1) / 2 + 17 ^ 2 := by
  rw [heapDepth_65536]

/-- Concrete query-sized binding count for 65,536 leaves and 256-bit
digests.  The tape has `2^(256*T)` elements; the numerator is the advertised
birthday term plus `17^2`. -/
theorem mh_binding_bound_rom_65536_256
    (ell T t : ℕ)
    (game : ROMBindingGame (concreteCodec ell) (2 ^ 16) T t 16)
    [DecidablePred game.Bad] :
    (Finset.filter game.Bad Finset.univ).card ≤
      (t * (t - 1) / 2 + 17 ^ 2) * (2 ^ 256) ^ (T - 1) := by
  simpa using mh_binding_bound_rom (concreteCodec_inj ell) (2 ^ 16) T t 16 game

/-- For 256-bit salts and digests the common hiding denominator is `2^512`. -/
theorem hidingDenominator_256 : (2 ^ 256) * (2 ^ 256) = 2 ^ 512 := by
  set_option exponentiation.threshold 1024 in
    calc
      (2 ^ 256) * (2 ^ 256) = 2 ^ (256 + 256) := by
        exact (Nat.pow_add 2 256 256).symm
      _ = 2 ^ 512 := by congr

/-- Concrete normalized root-hiding corollary. -/
theorem mh_root_hiding_rom_256
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    {V : Type*} [DecidableEq V]
    (ell n t : ℕ)
    (game : RootHidingGame (concreteCodec ell)
      Omega V n (2 ^ 256) (2 ^ 256) t) :
    RandomOracle.CountingCloseRatio
      (n * ((t + t ^ 2) * 2 ^ 256)) (2 ^ 512)
      (fun omega => game.observe omega (game.realOracle omega)
        (root ((concreteCodec ell).withOracle (game.realOracle omega)) n
          (game.nonce omega) game.message))
      (fun omega => game.observe omega (game.simulatedOracle omega)
        (game.simulatedRoot omega)) := by
  have h := mh_root_hiding_rom (concreteCodec ell) n (2 ^ 256) (2 ^ 256) t game
  rw [basicHidingNumerator_256, hidingDenominator_256] at h
  exact h

/-- Concrete normalized opening-hiding corollary. -/
theorem mh_opening_hiding_rom_256
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    {V : Type*} [DecidableEq V]
    (ell n t : ℕ) (I : Finset (Fin n)) (hn : 0 < n) (hI : I.Nonempty)
    (game : OpeningHidingGame (concreteCodec ell)
      Omega V n I (2 ^ 256) (2 ^ 256) t) :
    RandomOracle.CountingCloseRatio
      ((n - I.card) * ((t + t ^ 2) * 2 ^ 256)) (2 ^ 512)
      (fun omega => game.observe omega (game.realOracle omega)
        (realOpeningView ((concreteCodec ell).withOracle
          (game.realOracle omega)) n I (game.nonce omega) game.message))
      (fun omega => game.observe omega (game.simulatedOracle omega)
        (simulatedOpeningView ((concreteCodec ell).withOracle
          (game.simulatedOracle omega)) n I game.message
          (game.simulatorCoins omega))) := by
  have h := mh_opening_hiding_rom (concreteCodec ell) n I hn hI
      (2 ^ 256) (2 ^ 256) t game
  rw [basicHidingNumerator_256, hidingDenominator_256] at h
  exact h

end MH

end Merkle
