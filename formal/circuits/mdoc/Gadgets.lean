/-
# The circuit's own gadgets, and why they compute what `Asserted` says

`Assertions.lean` states every clause through an abstract `Gadgets`, so nothing in the meaning
layer can assume a barrel shifter, a comparator or a chunked equality is correct. This file
builds the *circuit's* instance — the actual routing-network output, the actual `lt` fold, the
actual per-chunk field equations — and proves `GadgetsOk` of it.

That is the threading. Before it, `mdoc/Compare.lean` and `mdoc/ChunkEq.lean` were true and
unused; `meaning_of_circuit` at the bottom cannot be stated without them.

## What each field is

| field | circuit | proof |
|---|---|---|
| `rd` | `routing::shift_bitvec`'s output | `Shift.reads_gateRead` |
| `lt` | `arithmetic::lt`'s wire, `tree_fold2` of `lt_base`/`lt_reduce` | `BitLt.foldStL_enc` + `bfold_spec` |
| `eqw` | the *first* component of the same fold — `arithmetic::eqb` | `bfold_spec`'s first half |
| `eqc` | `arithmetic::assert_eq`'s `⌈n / dim⌉` field equations | `ChunkEq.eq_of_chunks` |
| `eqcB` | the same, on the `V256` `assert_key` packs from a byte window | plus `Mux.beVal_inj` |

`lt` and `eqw` come from one fold because in the circuit they do: `lt_reduce` carries a pair, and
`eqb` reads `.1` where `lt` reads `.2`. Stating them as separate gadgets would have been less
faithful, not more.

## Where the bit-packing convention enters

`Asserted` is about `Nat`s; the gadgets are about `List Bool`. `Mux.toBits` is the bridge, and
`Mux.bval_toBits` / `Mux.toBits_bval` are why it is a *bridge* and not a hypothesis: a wire
vector's bits are a function of the number it carries, once `is_boolean` says they are bits. That
is the correction recorded in `mdoc/Mux.lean`'s header, cashed in here.

## What is still assumed

* **`Separates c dim`** — that the packing is injective on `≤ dim`-bit vectors.
  `ChunkEq.separates_gf128` proves it for GF(2¹²⁸) from `GF128.eval_injOn`, and
  `ChunkEq.separates_prime` for 𝔽ₚ. Which one applies is which field the circuit compiles to.
* **`c` is `pseudo_basis`** — that GF(2¹²⁸)'s `1 <<< i` is `α ^ i` and 𝔽ₚ's `2 ^ i mod p` is
  `(2 : F) ^ i`. Read off `compile/algebra/{gf2_128,fp}.rs`, one line each.
* **`Chains hashIndexBits rs`** — that the shifter's schedule chains, which
  `Shift.chains_call_sites` checks for every mdoc call site.
* **Booleanity**, as `Widths` — see `Assertions.lean`.
-/

import Mathlib
import mdoc.Assertions
import mdoc.Shift
import mdoc.Compare
import mdoc.ChunkEq
import mdoc.Mux
import mdoc.SigAssertions
import GF128.Irred

set_option maxRecDepth 4000

namespace MDoc
namespace Gadget

open ECDSA2.BitLt

/-! ## The comparator and the equality wire

`arithmetic::lt` folds `lt_base` states with `lt_reduce`, and the fold is `util::array::tree_fold2`
— a balanced binary tree, not a left fold. `Compare.balancedFold` is that recursion,
`balancedFold_eq` says its value is the linear fold's, and `Compare.leaves_le_one` says the fuel
is enough that it really is the tree. -/

variable {F : Type} [Field F]

/-- `tree_fold2`'s depth on `n` leaves: enough halvings to reach singletons. Fixed here rather
    than left as a parameter, so that `circuitGadgets` cannot be instantiated at a fuel where
    `balancedFold` degenerates to the linear fold. -/
def treeDepth (n : Nat) : Nat := Nat.log2 n + 1

/-- The fuel suffices: `Compare.leaves_le_one` needs exactly this. -/
theorem treeDepth_enough (n : Nat) : n ≤ 2 ^ treeDepth n :=
  Nat.le_of_lt Nat.lt_log2_self

/-- The pair of wires the fold produces on the bit vectors carrying `x` and `y`, over
    `tree_fold2`'s own splitting. -/
def cmpFold (n x y : Nat) : St F :=
  Compare.balancedFold (treeDepth n) (Compare.states (F := F) (Mux.toBits n x) (Mux.toBits n y))

/-- **The tree bottoms out at `lt_base`.** Every slice `cmpFold` reaches is a single bit pair, so
    the model is the balanced tree and not the linear fold wearing its name. -/
theorem cmpFold_leaves (n x y : Nat) :
    ∀ p ∈ Compare.leaves (treeDepth n) (Compare.states (F := F) (Mux.toBits n x) (Mux.toBits n y)),
      p.length ≤ 1 := by
  refine Compare.leaves_le_one _ _ ?_
  simp only [Compare.states, List.length_map, List.length_zip, Mux.toBits_length, Nat.min_self]
  exact treeDepth_enough n

/-- `arithmetic::lt`: the second component, asserted true. -/
def ltWire (n x y : Nat) : Prop := (cmpFold (F := F) n x y).2 = 1

/-- `arithmetic::eqb`: the first component of the *same* fold, asserted true. -/
def eqWire (n x y : Nat) : Prop := (cmpFold (F := F) n x y).1 = 1

private theorem cmpFold_enc (n x y : Nat) :
    cmpFold (F := F) n x y
      = (enc (bfold (Mux.toBits n x) (Mux.toBits n y)).1,
         enc (bfold (Mux.toBits n x) (Mux.toBits n y)).2) := by
  simp only [cmpFold, Compare.balancedFold_eq, Compare.states]
  exact foldStL_enc _ _ (by simp)

/-- **The comparator computes `<`.** Both directions: the wire *equals* the comparison, so a
    `lt` asserted true gives `<` and a `leq` — which asserts the wire false — gives `≤`. -/
theorem ltWire_iff (n x y : Nat) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    ltWire (F := F) n x y ↔ x < y := by
  have hbx := Mux.bval_toBits n x hx
  have hby := Mux.bval_toBits n y hy
  obtain ⟨-, h2⟩ := bfold_spec (Mux.toBits n x) (Mux.toBits n y) (by simp)
  rw [ltWire, cmpFold_enc, h2, hbx, hby]
  cases hd : decide (x < y) <;> simp_all

/-- **The equality wire computes `=`.** `bfold`'s first component is `a == b`, and equal-length
    bit vectors are equal exactly when the numbers they carry are. -/
theorem eqWire_iff (n x y : Nat) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    eqWire (F := F) n x y ↔ x = y := by
  have hbx := Mux.bval_toBits n x hx
  have hby := Mux.bval_toBits n y hy
  obtain ⟨h1, -⟩ := bfold_spec (Mux.toBits n x) (Mux.toBits n y) (by simp)
  rw [eqWire, cmpFold_enc, h1]
  constructor
  · intro h
    have hb : (Mux.toBits n x == Mux.toBits n y) = true := by
      cases hd : (Mux.toBits n x == Mux.toBits n y) <;> simp_all
    have := congrArg bval (by simpa using hb : Mux.toBits n x = Mux.toBits n y)
    rwa [hbx, hby] at this
  · rintro rfl; simp

/-! ## Chunked equality

`assert_eq` splits the vector into `⌈n / dim⌉ ` pieces and asserts one field equation each.
`ChunkEq.chunkSizes` is the Rust loop's sizes; `chunksOf` is the split itself. -/

/-- Cut a bit list into consecutive pieces of the given sizes. -/
def chunksOf : List Nat → List Bool → List (List Bool)
  | [], _ => []
  | n :: ns, l => l.take n :: chunksOf ns (l.drop n)

@[simp] theorem chunksOf_length : ∀ (sizes : List Nat) (l : List Bool),
    (chunksOf sizes l).length = sizes.length
  | [], _ => rfl
  | n :: ns, l => by simp [chunksOf, chunksOf_length ns (l.drop n)]

/-- The pieces tile the list. -/
theorem chunksOf_flatten : ∀ (sizes : List Nat) (l : List Bool), sizes.sum = l.length →
    (chunksOf sizes l).flatten = l
  | [], l, h => by simpa [chunksOf] using (List.eq_nil_of_length_eq_zero h.symm).symm
  | n :: ns, l, h => by
      have hn : n ≤ l.length := by simp only [List.sum_cons] at h; omega
      have hrest : ns.sum = (l.drop n).length := by
        simp only [List.sum_cons] at h; simp only [List.length_drop]; omega
      simp only [chunksOf, List.flatten_cons, chunksOf_flatten ns (l.drop n) hrest,
        List.take_append_drop]

/-- ... and each piece has the size it was given. -/
theorem chunksOf_getD : ∀ (sizes : List Nat) (l : List Bool), sizes.sum = l.length →
    ∀ i, i < sizes.length → ((chunksOf sizes l).getD i []).length = sizes.getD i 0
  | [], _, _, i, hi => by simp at hi
  | n :: ns, l, h, 0, _ => by
      have hn : n ≤ l.length := by simp only [List.sum_cons] at h; omega
      simp [chunksOf, hn]
  | n :: ns, l, h, i + 1, hi => by
      have hrest : ns.sum = (l.drop n).length := by
        simp only [List.sum_cons] at h; simp only [List.length_drop]; omega
      simpa [chunksOf] using chunksOf_getD ns (l.drop n) hrest i (by simpa using hi)

variable {G : Type*} [CommRing G]

/-- The sizes `arithmetic::assert_eq` uses on an `n`-bit vector: `k = ⌈n / dim⌉` rounds of
    `remaining_n / remaining_k`. -/
def sizes (dim n : Nat) : List Nat := ChunkEq.chunkSizes n ((n + dim - 1) / dim)

/-- **`arithmetic::assert_eq`**: one field equation per chunk. -/
def eqChunked (c : Nat → G) (dim n x y : Nat) : Prop :=
  ∀ i, i < (sizes dim n).length →
    ChunkEq.eltSum c 0 ((chunksOf (sizes dim n) (Mux.toBits n x)).getD i [])
      = ChunkEq.eltSum c 0 ((chunksOf (sizes dim n) (Mux.toBits n y)).getD i [])

private theorem sizes_sum (dim n : Nat) (hdim : 0 < dim) : (sizes dim n).sum = n := by
  refine ChunkEq.chunkSizes_sum _ n ?_
  intro hk
  by_contra hn
  have hge : dim ≤ n + dim - 1 := by omega
  have : 1 ≤ (n + dim - 1) / dim := (Nat.one_le_div_iff hdim).mpr hge
  omega

private theorem sizes_le (dim n : Nat) (hdim : 0 < dim) : ∀ s ∈ sizes dim n, s ≤ dim := by
  refine ChunkEq.chunkSizes_le _ n dim ?_
  -- `⌈n / dim⌉ * dim ≥ n`, from the division identity
  have hdm := Nat.div_add_mod (n + dim - 1) dim
  have hmod : (n + dim - 1) % dim < dim := Nat.mod_lt _ hdim
  rw [Nat.mul_comm]
  omega

/-- **Chunked equality is equality.** `eq_of_chunks` does the work; `chunkSizes_le` is what says
    no chunk exceeds `dim`, and `Mux.bval_toBits` is what turns bit lists back into numbers. -/
theorem eqChunked_iff (c : Nat → G) (dim : Nat) (hdim : 0 < dim)
    (hsep : ChunkEq.Separates c dim) (n x y : Nat) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    eqChunked c dim n x y ↔ x = y := by
  constructor
  · intro h
    have hsx : (sizes dim n).sum = (Mux.toBits n x).length := by
      rw [Mux.toBits_length]; exact sizes_sum dim n hdim
    have hsy : (sizes dim n).sum = (Mux.toBits n y).length := by
      rw [Mux.toBits_length]; exact sizes_sum dim n hdim
    have hflat := ChunkEq.eq_of_chunks c dim hsep
      (chunksOf (sizes dim n) (Mux.toBits n x)) (chunksOf (sizes dim n) (Mux.toBits n y))
      (by simp) (fun i hi => by
        rw [chunksOf_length] at hi
        rw [chunksOf_getD _ _ hsx i hi, chunksOf_getD _ _ hsy i hi]
        refine ⟨rfl, sizes_le dim n hdim _ ?_⟩
        have hget : (sizes dim n).getD i 0 = (sizes dim n)[i] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
        rw [hget]
        exact List.getElem_mem hi)
      (fun i hi => h i (by rwa [chunksOf_length] at hi))
    rw [chunksOf_flatten _ _ hsx, chunksOf_flatten _ _ hsy] at hflat
    have := congrArg bval hflat
    rwa [Mux.bval_toBits n x hx, Mux.bval_toBits n y hy] at this
  · rintro rfl; intro i _; rfl

/-- **`assert_key`**: the same `assert_eq`, on the `V256` the circuit packs from a byte window
    most-significant byte first — whose value is `beVal`. -/
def eqBytes (c : Nat → G) (dim : Nat) (x y : List Nat) : Prop :=
  eqChunked c dim (8 * x.length) (beVal x) (beVal y)

theorem eqBytes_iff (c : Nat → G) (dim : Nat) (hdim : 0 < dim)
    (hsep : ChunkEq.Separates c dim) (x y : List Nat) (hlen : x.length = y.length)
    (hxb : ∀ v ∈ x, v < 256) (hyb : ∀ v ∈ y, v < 256) :
    eqBytes c dim x y ↔ x = y := by
  rw [eqBytes, eqChunked_iff c dim hdim hsep _ _ _ (beVal_lt_two_pow x hxb)
    (by rw [hlen]; exact beVal_lt_two_pow y hyb)]
  constructor
  · exact fun h => Mux.beVal_inj x y hlen hxb hyb h
  · rintro rfl; rfl

/-- **The obligation, as `Assertions.Equates` states it.** The signature circuit uses only this
    field of the bundle — it has no barrel shifter, and its `lt` wires land on `soundness_of_v2`'s
    own vocabulary rather than on the meaning layer. -/
theorem equates_eqChunked (c : Nat → G) (dim : Nat) (hdim : 0 < dim)
    (hsep : ChunkEq.Separates c dim) : Equates (eqChunked c dim) :=
  fun n x y hx hy => eqChunked_iff c dim hdim hsep n x y hx hy

/-- **The deployed signature circuit's `assert_eq`.** `pseudo_basis(i) = 2 ^ i mod p` and
    `dim = pseudo_dimension = bits(p) − 1`, and `2 ^ dim ≤ p` is exactly what keeps a chunk's
    value below the characteristic so the cast cannot wrap. -/
theorem equates_prime (p dim : Nat) [CharP G p] (hdim : 0 < dim) (hle : 2 ^ dim ≤ p) :
    Equates (eqChunked (fun j => (2 : G) ^ j) dim) :=
  equates_eqChunked _ dim hdim (ChunkEq.separates_prime p dim hle)

/-! ## The bundle -/

/-- **The circuit's gadgets.** `rs` is the routing schedule, `c` the field's `pseudo_basis` and
    `dim` its `pseudo_dimension`. -/
def circuitGadgets (rs : List (Nat × Nat)) (c : Nat → F) (dim : Nat) : Gadgets where
  rd := Shift.gateRead rs
  lt := ltWire (F := F)
  eqw := eqWire (F := F)
  eqc := eqChunked c dim
  eqcB := eqBytes c dim

/-- **The obligation, discharged.** Every field of `GadgetsOk` on the circuit's own gadgets, from
    the three gadget lemmas and the bit-packing round trip. -/
theorem gadgetsOk_circuit (rs : List (Nat × Nat)) (hch : Shift.Chains hashIndexBits rs)
    (c : Nat → F) (dim : Nat) (hdim : 0 < dim) (hsep : ChunkEq.Separates c dim) :
    GadgetsOk (circuitGadgets (F := F) rs c dim) where
  reads := Shift.reads_gateRead hashIndexBits rs hch
  cmp := fun n x y hx hy => ltWire_iff (F := F) n x y hx hy
  eqWire := fun n x y hx hy => eqWire_iff (F := F) n x y hx hy
  eqChunk := equates_eqChunked c dim hdim hsep
  eqBytes := fun x y hlen hxb hyb => eqBytes_iff c dim hdim hsep x y hlen hxb hyb

/-- **Meaning, over the circuit's own gadgets.** The end of the chain: the assertions as they are
    actually made — about a routing network's outputs, a comparator's wire and a set of per-chunk
    field equations — imply the specification.

    Nothing here assumes a gadget is correct. `Shift`, `Compare` and `ChunkEq` are all
    load-bearing: delete any one of the three lemmas and this stops typechecking. -/
theorem meaning_of_circuit (rs : List (Nat × Nat)) (hch : Shift.Chains hashIndexBits rs)
    (c : Nat → F) (dim : Nat) (hdim : 0 < dim) (hsep : ChunkEq.Separates c dim)
    (s : Statement) (w : Witness)
    (hwd : Widths s w) (hwf : WellFormed s)
    (hsha : sha256 w.preimage w.nblocks = w.e)
    (hshaAttr : ∀ i, i < s.attrId.length →
      sha256 (w.attrs.getD i default).preimage attrShaBlocks
        = window w.preimage ((w.attrs.getD i default).digestOff + tag32.length) 32)
    (h : Asserted (circuitGadgets (F := F) rs c dim) s w) :
    ValidPresentation s :=
  meaning _ s w (gadgetsOk_circuit rs hch c dim hdim hsep) hwd hwf hsha hshaAttr h

/-! ## The two fields

Which `Separates` applies is which field the circuit compiles to. The hash circuit is GF(2¹²⁸);
the signature circuit is 𝔽ₚ₂₅₆. -/

/-- **The deployed hash circuit.** `pseudo_basis(i) = 1 <<< i` is `α ^ i`, and `dim = 128`. The
    only hypothesis on the field is that `α` is a root of the reduction polynomial
    `x¹²⁸ + x⁷ + x² + x + 1` — `gf2_128.rs`'s own constant. `GF128.isGen_of_root` is what makes
    that enough, on the strength of `GF128/Irred.lean`'s irreducibility proof. -/
theorem meaning_gf128 {K : Type} [Field K] [CharP K 2] (α : K)
    (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1)
    (rs : List (Nat × Nat)) (hch : Shift.Chains hashIndexBits rs)
    (s : Statement) (w : Witness)
    (hwd : Widths s w) (hwf : WellFormed s)
    (hsha : sha256 w.preimage w.nblocks = w.e)
    (hshaAttr : ∀ i, i < s.attrId.length →
      sha256 (w.attrs.getD i default).preimage attrShaBlocks
        = window w.preimage ((w.attrs.getD i default).digestOff + tag32.length) 32)
    (h : Asserted (circuitGadgets (F := K) rs (fun i => α ^ i) 128) s w) :
    ValidPresentation s :=
  meaning_of_circuit rs hch _ 128 (by omega)
    (ChunkEq.separates_gf128 α (GF128.isGen_of_root α hroot)) s w hwd hwf hsha hshaAttr h

/-! ## Both halves, over the circuits' own gadgets

The capstone. The hash circuit compiles to GF(2¹²⁸) and the signature circuit to 𝔽ₚ₂₅₆, so the two
`assert_eq`s are packings in *different* fields with different `pseudo_basis` and different
`dim` — which is why `ChunkEq.lean` proves `Separates` twice and why this takes two field
arguments. -/

/-- **`ValidPresentationFull`, from the two assertion sets as the circuits actually emit them.**

    Every gadget is discharged: the hash half's shifter, comparator, `eqb` wire and chunked
    equality by `gadgetsOk_circuit`, and the signature half's chunked equality by `equates_prime`.
    What is left as hypotheses is exactly what `Assertions.lean` and `SigAssertions.lean` list as
    residual — the SHA-256 block arithmetic, booleanity as `Widths`/`SigWidths`, the curve facts,
    `WellFormed`, and the MAC seam. -/
theorem full_meaning_of_circuit
    [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)]
    [NeZero (7 : F)]
    {K : Type} [Field K] [CharP K 2] (α : K)
    (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1)
    (rs : List (Nat × Nat)) (hch : Shift.Chains hashIndexBits rs)
    (p : Nat) [CharP F p] (hp : 2 ^ 255 ≤ p)
    (hs : Statement) (s : SigStatement F) (params : CurveParameters F)
    [(params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (order : Nat) [Fact (Nat.Prime order)]
    (wh : Witness) (macPad : List (Nat × Nat))
    (iss dev : EcdsaWires F) (issPk devPk : AffinePoint F) (eIss eDev : F)
    (hwf : WellFormed hs)
    (hsha : sha256 wh.preimage wh.nblocks = wh.e)
    (hshaAttr : ∀ i, i < hs.attrId.length →
      sha256 (wh.attrs.getD i default).preimage attrShaBlocks
        = window wh.preimage ((wh.attrs.getD i default).digestOff + tag32.length) 32)
    (hwd : Widths hs wh)
    (hh : Asserted (circuitGadgets (F := K) rs (fun i => α ^ i) 128) hs wh)
    (hkb : params.kBits = 256)
    (hw : SigWidths s wh.e wh.dpkX wh.dpkY macPad)
    (hci : CurveFacts params order issPk iss.rx iss.ry)
    (hcd : CurveFacts params order devPk dev.rx dev.ry)
    (hsig : AssertedSig (eqChunked (fun j => (2 : F) ^ j) 255) s order params
      wh.e wh.dpkX wh.dpkY macPad iss dev issPk devPk eIss eDev)
    (hshared : SharedMacs hs s) :
    ValidPresentationFull hs s order params :=
  full_meaning hs s params order wh _ _ macPad iss dev issPk devPk eIss eDev hwf hsha hshaAttr
    (gadgetsOk_circuit rs hch _ 128 (by omega) (ChunkEq.separates_gf128 α
      (GF128.isGen_of_root α hroot)))
    hwd hh hkb (equates_prime p 255 (by omega) hp) hw hci hcd hsig hshared

/-! ## Residual

What this file does not close, beyond the three bullets in the header.

* **`memcmp::arrange`.** `AssertedValidity` states `cmp_from`/`cmp_until` on `beVal`s, which is
  what `Compare.bval_arranged` says the arranged bit vector carries. Here that appears as
  `ltWire (8 * timestampLen)` on those values, so the reversal is in the *statement* rather than
  in this file's proof; `Compare.bval_arranged` is what licenses it.
-/

end Gadget
end MDoc
