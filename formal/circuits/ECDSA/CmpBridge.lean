import ECDSA.BitTable
import ECDSA.BitLt

/-!
# From the comparator's fold to `natR … < order`

`BitLt.lt_of_foldStL` turns the circuit's comparator into `bval a < bval b` over `Bool` lists.
Two gaps remain between that and `hrlt` / `hslt`, which `soundness_of_v2` states as
`natR ((us.map bitrev3).map val3) < order`:

* the comparator's leaves are the *same* wires the bit-sums use, so `digitBit` identifies them --
  but `BitLt` needs `enc` of a `Bool`, not a field element that happens to be `0` or `1`.
  `digitBitB` is the `Bool`, and `digitBit_eq_enc` is unconditional: it does not need `IsDigit`,
  because `digitBit` is already defined by a decidable test on `val3 (bitrev3 u)`;

* `bval` is least-significant-first over `Bool`s while `natR` is a most-significant-first `Nat`
  fold over digits. That is the same reversal `reconstructE_digitBit` handles on the field side,
  redone in `Nat`.

Nothing here touches the circuit; it is all specification-side bookkeeping.
-/

namespace ECDSA2

variable {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)]
  [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)]

/-- The digit's `e`/`r`/`s` bit as a `Bool`. `digitBit` is its `enc`. -/
noncomputable def digitBitB (sel : Nat) (u : F) : Bool :=
  decide ((val3 (bitrev3 u) / sel) % 2 = 1)

omit [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)] in
theorem digitBit_eq_enc (sel : Nat) (u : F) :
    digitBit sel u = BitLt.enc (digitBitB (F := F) sel u) := by
  simp only [digitBit, digitBitB, BitLt.enc, decide_eq_true_eq]

/-! ### The `Nat` side of the weighting bridge -/

/-- Least-significant-first value of a list of `Nat` bits. -/
def natLE : List Nat → Nat
  | [] => 0
  | b :: bs => b + 2 * natLE bs

theorem bval_eq_natLE (bs : List Bool) :
    BitLt.bval bs = natLE (bs.map (fun b => if b then 1 else 0)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [BitLt.bval, List.map_cons, natLE, ih]

theorem natfold_reverse (l : List Nat) :
    l.reverse.foldl (fun acc v => acc * 2 + v) 0 = natLE l := by
  have key : ∀ (l : List Nat) (a : Nat),
      l.reverse.foldl (fun acc v => acc * 2 + v) a = a * 2 ^ l.length + natLE l := by
    intro l
    induction l with
    | nil => intro a; simp [natLE]
    | cons b bs ih =>
        intro a
        simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.length_cons, natLE, ih]
        ring
  simpa using key l 0

omit [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)] in
private theorem natrec (us : List F) (sel : Nat) (mux : Nat → Nat)
    (hf : ∀ u : F, mux (val3 (bitrev3 u)) = (if digitBitB (F := F) sel u then 1 else 0)) :
    natReconstruct ((us.map bitrev3).map val3) mux
      = BitLt.bval (us.reverse.map (digitBitB (F := F) sel)) := by
  have hmap : ((us.map bitrev3).map val3).map mux
      = (us.reverse.map (fun u => mux (val3 (bitrev3 u)))).reverse := by
    simp [List.map_map, List.map_reverse, Function.comp_def]
  -- `← List.foldl_map` on its own is higher-order: Lean will not guess to split
  -- `fun acc v => acc * 2 + mux v` into a fold and a map. Stating the instance is enough.
  have hfm : ∀ l : List Nat, l.foldl (fun acc v => acc * 2 + mux v) 0
      = (l.map mux).foldl (fun acc v => acc * 2 + v) 0 := by
    intro l; rw [List.foldl_map]
  rw [natReconstruct, hfm, hmap, natfold_reverse, bval_eq_natLE, List.map_map]
  simp only [Function.comp_def, hf]

omit [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)] in
theorem natE_bval (us : List F) :
    natE ((us.map bitrev3).map val3) = BitLt.bval (us.reverse.map (digitBitB (F := F) 1)) := by
  unfold natE
  refine natrec us 1 muxE fun u => ?_
  simp only [muxE, digitBitB, decide_eq_true_eq, Nat.div_one]
  split <;> omega

omit [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)] in
theorem natR_bval (us : List F) :
    natR ((us.map bitrev3).map val3) = BitLt.bval (us.reverse.map (digitBitB (F := F) 2)) := by
  unfold natR
  refine natrec us 2 muxR fun u => ?_
  simp only [muxR, digitBitB, decide_eq_true_eq]
  split <;> omega

omit [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)] in
theorem natS_bval (us : List F) :
    natS ((us.map bitrev3).map val3) = BitLt.bval (us.reverse.map (digitBitB (F := F) 4)) := by
  unfold natS
  refine natrec us 4 muxS fun u => ?_
  simp only [muxS, digitBitB, decide_eq_true_eq]
  split <;> omega

end ECDSA2
