import quadcert.Core.Check
import quadcert.Gen.Sha256Gf2.Sha256Gf2OkCheck
import quadcert.Gen.Sha256Gf2.Sha256Gf2InvCheck
import quadcert.Gen.Sha256Gf2.Sha256Gf2SumLocal
import quadcert.Gen.Sha256Gf2.Sha256Gf2Backed
import quadcert.Gen.Sha256Gf2.Sha256Gf2Zero
import quadcert.Bridge.Sha256Gf2.Gf2Cone
import quadcert.Bridge.Sha256Gf2.Gf2Artifact

/-!
# GF(2^128) SHA-256: committed bytes to named assertions

The structural half, mirroring `Bridge/Sha256/S2Sound.lean` clause for clause. Everything in
`Core/Check.lean` is parametric in `consts : Nat → F` with no constraint on it, and every
generated check (`ok_check`, `inv_check`, `perm_all`, `hom_all`, `corr_check`, `backed_check`) is
a `Bool` fact about `Nat` data — so the whole structural certificate transfers to the binary
field unchanged.

**One line does not.** The p256 bridge reads the constant table with `fun i => (constNat i : F)`.
In characteristic 2 a `Nat` cast reaches only `0` and `1`, while this artifact's table holds
16-byte elements: `constNat 2 = 0x3`, which is `α + 1`. So `consts` goes through `GF128.eval`,
which is what that function exists for.

Two further differences worth naming, both consequences of `segment_circuit` sorting the
constant table by frequency: `zeroConst` is `1` here and `3` in the p256 artifact, and the
circuit has 12 layers rather than 6.

## The constant table, tied to the cone lemmas

`GF128.injConsts` and `GF128.constPowers` were stated over transcribed literals. `constNat_inj`
and `constNat_window` below restate them over `constNat` itself, by kernel reduction, so
`Gf2Cone`'s `hci` and `hcj` hypotheses are discharged from the artifact rather than from a list
someone copied.
-/

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2

variable {F : Type} [Field F] [CharP F 2]

/-- The artifact's constant table, read into the field as polynomials in `α`. -/
noncomputable def consts (α : F) : Nat → F := fun i => GF128.eval α (constNat i)

theorem consts_zero (α : F) : consts α zeroConst = 0 := by
  show GF128.eval α (constNat 1) = 0
  rw [show constNat 1 = 0 from rfl, GF128.eval_zero]

theorem consts_one (α : F) : consts α 0 = 1 := by
  show GF128.eval α (constNat 0) = 1
  rw [show constNat 0 = 1 from rfl, GF128.eval_one]

/-! ### The two coefficient families, from the artifact's own table -/

/-- Indices 2 … 33 hold `α^(2^i) − 1`, in order. -/
theorem constNat_inj : (List.range 32).all (fun i => constNat (2 + i) == GF128.injConst i) = true := by
  decide +kernel

/-- Constant index of the `j`-th window multiplier `α^(j·2^32)`. `j = 0` reuses the shared `1`. -/
def windowIdx (j : Nat) : Nat := if j = 0 then 0 else 33 + j

/-- …and those indices hold the powers. `j` stops at 6 because the widest wrapping sum has
    seven addends. -/
theorem constNat_window :
    (List.range 7).all (fun j => constNat (windowIdx j) == GF128.windowConst j) = true := by
  decide +kernel

theorem consts_inj (α : F) (h : GF128.IsGen α) (i : Nat) (hi : i < 32) :
    consts α (2 + i) = α ^ 2 ^ i - 1 := by
  have hb := constNat_inj
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hb
  exact GF128.const_eq_injBasis α h (hb i hi) hi

theorem consts_window (α : F) (h : GF128.IsGen α) (j : Nat) (hj : j < 7) :
    consts α (windowIdx j) = (α ^ 2 ^ 32) ^ j := by
  have hb := constNat_window
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hb
  exact GF128.const_eq_alpha_pow α h (hb j hj) (by omega)

/-- The 64 SHA-256 round constants, `Kₜ = ⌊2^32 · frac(∛pₜ)⌋`. -/
def shaK : List Nat :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- **Indices 40 … 103 hold `α^(Kₜ)`, in round order.** `algsimp` folds the round constant into a
    product node rather than injecting it bit by bit, so this is the form in which the deployed
    circuit carries it — and checking it here is what ties the artifact to *SHA-256's* constants
    rather than to sixty-four arbitrary field elements.

    With `constNat_inj` and `constNat_window` the artifact's 104-entry constant table is now
    completely accounted for: `1`, `0`, the 32 injection coefficients, the 6 window multipliers,
    and these. -/
theorem constNat_round :
    (List.range 64).all (fun t => constNat (40 + t) == GF128.pow GF128.alpha (shaK.getD t 0))
      = true := by
  decide +kernel

theorem consts_round (α : F) (h : GF128.IsGen α) (t : Nat) (ht : t < 64) :
    consts α (40 + t) = α ^ (shaK.getD t 0) := by
  have hb := constNat_round
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hb
  refine GF128.const_eq_pow α h (hb t ht) ?_
  have : shaK.getD t 0 < 2 ^ 32 := by
    have : t < 64 := ht
    interval_cases t <;> decide
  exact lt_trans this (by norm_num)

/-- A folded product row whose coefficient is the shared `1`. -/
theorem consts_one_pow (α : F) : consts α 0 = α ^ 0 := by
  simpa using consts_one α

/-! ### The structural certificate -/

/-- The compiled circuit, over `F`. -/
@[reducible] noncomputable def circuit (α : F) : QuadCircuitData F := raw.toQuad (consts α)

/-- All eight `ValidScheduling` fields, from the generated checks alone. -/
theorem valid (α : F) (inputs : Nat → F) :
    ValidScheduling (circuit α) (raw.toDag (consts α)) raw.toWireMap inputs :=
  validScheduling_of_raw raw (consts α) inputs wireInv groupOf gbound
    ok_check inv_check wireFn_lt perm_all hom_all corr_check

/-- **Soundness bridge.** An accepting assignment zeroes every named assertion. -/
theorem assertions_zero (α : F) (inputs : Nat → F) (hacc : Accepts (circuit α) inputs) :
    ∀ r ∈ raw.toRecs, interpDag (raw.toDag (consts α)) inputs r.assertedNode = 0 :=
  assertions_zero_of_accepts (circuit α) (raw.toDag (consts α)) raw.toWireMap inputs
    (valid α inputs) raw.toRecs
    (all_backed_of_rawWith raw (consts α) zeroConst (consts_zero α) azt azt_sub backed_check)
    (by rw [toQuad_layers_length]; show 0 < 12; norm_num) hacc

/-- **The same, from the committed bytes.** Whatever the pinned LFC3 pages decode to, extended
    by the sidecar's four advice fields, *is* `raw`. -/
theorem assertions_zero_of_bytes (α : F) (c : Lfc2.DecodedCircuit)
    (hdec : Lfc2.decode Lfc2.gf2_128 packedInput deltaTrees = .ok c)
    (inputs : Nat → F) (hacc : Accepts ((c.toRaw advice).toQuad (consts α)) inputs) :
    ∀ r ∈ (c.toRaw advice).toRecs,
      interpDag ((c.toRaw advice).toDag (consts α)) inputs r.assertedNode = 0 := by
  rw [raw_from_bytes c hdec] at hacc ⊢
  exact assertions_zero α inputs hacc

/-- **Committed bytes, and only `P(α) = 0`.** The commitment root, and every named assertion
    zero — with no hypothesis on `F` beyond being a field of characteristic 2 in which the
    deployed reduction polynomial has a root. -/
theorem certified_bytes_assertions_zero (α : F)
    (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1)
    (c : Lfc2.DecodedCircuit)
    (hdec : Lfc2.decode Lfc2.gf2_128 packedInput deltaTrees = .ok c)
    (inputs : Nat → F) (hacc : Accepts ((c.toRaw advice).toQuad (consts α)) inputs) :
    QuadCert.CircuitCommitment.rootOfPacked Quadcert.Gen.Sha256Gf2.packedInput
        = Quadcert.Gen.Sha256Gf2.formalRoot
      ∧ ∀ r ∈ (c.toRaw advice).toRecs,
          interpDag ((c.toRaw advice).toDag (consts α)) inputs r.assertedNode = 0 :=
  ⟨packedInput_root, assertions_zero_of_bytes α c hdec inputs hacc⟩

end Sha256Gf2
