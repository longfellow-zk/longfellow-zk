/-
# What the signature circuit asserts, and why that is the spec

The companion to `mdoc/Assertions.lean`, for the other half. `ASSERTIONS-SIG.txt` is the census
of `assert_signatures_and_macs` on a real credential: **2,108 assertions in 25 families** — nine
times smaller than the hash circuit, and three quarters of it is the two ECDSA scalar
multiplications.

## What was already done

Almost all of the mathematical content. `ECDSA/EcdsaV2.lean::soundness_of_v2` is stated directly
against the deployed Rust circuit — its hypotheses are annotated with the census's own family
names — and carries them to `StandardEcdsaVerify` through `ecdsa_circuit_soundness`. It already
absorbs the three ways `circuits/ecdsa2/src/circuit.rs` differs from the C++ model
`EcdsaCircuit.lean` was written against:

* the three-bit digit is packed in the opposite order (`bitrev3`);
* Rust stores all 256 accumulators where `EcdsaLoopConstraintsF` uses 255 and computes the last
  (`LoopFull` and `loopFull_split`);
* Rust iterates `i = 255 … 0`.

So this file is assembly, not new mathematics: group the 25 families into `soundness_of_v2`'s
hypothesis list, add the six wiring assertions and the six MAC assertions that are mdoc's rather
than ECDSA's, and land on `MDoc.ValidSignatures`.

## The family map

| family | count | lands on |
|---|---:|---|
| `ecdsa/range_check[]/valid_index` | 512 | `hdig : ∀ u ∈ us, IsDigit u` |
| `slice_wx`, `slice_wy`, `slice_wz` | 1,536 | `hloop : LoopFull …` |
| `slice_x`, `slice_y` | 16 | `hpre : ValidPreComputationExact …` |
| `ecdsa/is_on_curve` | 12 | `hpkc`, `hrc`; the four on the precomputed points are unused |
| `ecdsa/ax_zero`, `ecdsa/az_zero` | 4 | `hax`, `haz` |
| `ecdsa/e_eq`, `ecdsa/rx_eq` | 4 | `he`, `hr` |
| `ecdsa/rxinv`, `ecdsa/nmsinv`, `ecdsa/pkxinv` | 6 | `hrxi`, `hsi`, `hpki` |
| `ecdsa/rx_lt_order`, `ecdsa/nms_lt_order` | 4 | `hrlt`, `hslt` |
| `ecdsa/yinv` | 2 | **nothing** — see below |
| `issuer_e_eq`, `issuer_pkx_eq`, `issuer_pky_eq` | 3 | `AssertedWiring` |
| `device_e_eq`, `device_pkx_eq`, `device_pky_eq` | 3 | `AssertedWiring` |
| `assert_mac/msg0_eq[]/chunk_eq`, `msg1_eq[]/chunk_eq` | 6 | `AssertedSigMacs`, through `Eqc` |

That is 25 families and 2,108 assertions, all of them.

`yinv` is the one family that lands nowhere: the circuit asserts the final accumulator's `Y` is
invertible, and `ValidEcdsaWitness` does not ask for it. That is safe in the direction that
matters — an unused hypothesis only makes the soundness theorem stronger — and it is recorded
here rather than silently dropped, because the opposite mistake (a *needed* assertion that no
Lean hypothesis mentions) looks identical from the Lean side.

## The chunked equality is threaded

`assert_mac`'s two `bv.assert_eq`s go through `Assertions.Eqc`, so nothing here assumes
`arithmetic::assert_eq` is correct; `Gadget.equates_prime` discharges it from
`ChunkEq.separates_prime`. Note that this is *not* the hash circuit's MAC: `mac_gf128` calls
`as_eltw_field` first and then `logic.assert_eq` on the field elements — one equation, no chunking
— which is why `MDoc.AssertedMacs` is a plain equality and `AssertedSigMacs` is not. The census
spells the difference out: `msg0_eq` there, `msg0_eq[]/chunk_eq` here.

`SigWidths` is the new hypothesis this costs, for the same reason `Widths` is on the hash side:
`Equates` compares `n`-bit vectors, so the key, the tags and the pads have to fit their
`MacElt128` wires. The right-hand side does *not* — `GF128.mul_lt` proves its range, because it is
a computed value rather than a wire the prover fills.

## Residual

Same shape as the hash side, and shorter.

* **`IsDigit` and the lookup encoding.** `range_check`'s polynomial vanishes exactly on the eight
  lookup *nodes* `-8, -6, …, 6`; `EcdsaV2.IsDigit` says so, and that the assertion has those
  roots is `RangeCert.lean`'s business, not this file's.
* **The comparison and bit-sum gadgets.** `soundness_of_v2`'s `he`, `hr`, `hsi`, `hrlt`, `hslt`
  are in Lean's `reconstructE`/`natR` vocabulary. Deriving them from the circuit's actual bit-sum
  and `lt` networks is the same gadget obligation the hash side has, and `CmpBridge.lean` is the
  start of it. This is the *only* gadget this file still takes on faith: the six `chunk_eq`
  assertions are threaded through `Assertions.Eqc`, discharged by `Gadget.equates_prime`.
* **Curve facts.** `soundness_of_v2` takes `h_G_on`, `h_pk_order`, `h_G_order`, `h_R_order` — that
  the generator is on the curve and that `n · P = O` for the key, the generator and `R`. For P-256
  the last three are free because the group has prime order `n` and cofactor 1, but `#E(𝔽ₚ) = n`
  is not proved in this tree. They stay hypotheses here too.
* **`AgreesModP`.** As in `SigSpec.lean`: `as_eltw_unsafe` reads 256 bits into `Fₚ`, so the wiring
  assertions equate the MAC'd byte string and the ECDSA scalar *modulo p*.
-/

import mdoc.Assertions
import mdoc.SigSpec
import ECDSA.EcdsaV2
import GF128.Field

set_option maxRecDepth 4000

namespace MDoc

open ECDSA2

/-! ## Two bounds

`AgreesModP` asks for `< 2 ^ 256`, on both sides of the wiring assertions: the byte string the MAC
covers, and the scalar the digits reconstruct. Both are the same accumulator induction. -/

/-- A left fold that multiplies by `b` and adds a digit below `b` stays below `(s + 1) * b ^ n`.
    Stated over the accumulator because that is what makes the induction go through. -/
private theorem foldl_bound (b : Nat) (_hb : 0 < b) :
    ∀ (l : List Nat), (∀ x ∈ l, x < b) → ∀ s : Nat,
      l.foldl (fun acc d => acc * b + d) s < (s + 1) * b ^ l.length := by
  intro l
  induction l with
  | nil => intro _ s; simp
  | cons d ds ih =>
      intro hall s
      have hd : d < b := hall d (by simp)
      have hds : ∀ x ∈ ds, x < b := fun x hx => hall x (by simp [hx])
      have hrec := ih hds (s * b + d)
      have hstep : (s * b + d + 1) * b ^ ds.length ≤ (s + 1) * b ^ (ds.length + 1) := by
        have : s * b + d + 1 ≤ (s + 1) * b := by
          have : s * b + b = (s + 1) * b := by ring
          omega
        calc (s * b + d + 1) * b ^ ds.length
            ≤ ((s + 1) * b) * b ^ ds.length := Nat.mul_le_mul_right _ this
          _ = (s + 1) * b ^ (ds.length + 1) := by ring
      simpa [List.foldl_cons, List.length_cons] using Nat.lt_of_lt_of_le hrec hstep

/-- Thirty-two bytes fit in 256 bits. `beVal_lt` is in `Assertions.lean`, where the hash side
    needs the same bound at 64 and 160 bits. -/
theorem beVal_lt_256 (bs : List Nat) (hlen : bs.length = 32) (h : ∀ x ∈ bs, x < 256) :
    beVal bs < 2 ^ 256 := by
  have := beVal_lt bs h
  rw [hlen] at this
  simpa [show (256 : Nat) ^ 32 = 2 ^ 256 by norm_num] using this

/-- The same for a digit reconstruction: `natE`, `natR` and `natS` all weight by 2. -/
theorem natReconstruct_lt (mux : Nat → Nat) (hm : ∀ v, mux v < 2) (bi : List Nat) :
    natReconstruct bi mux < 2 ^ bi.length := by
  have hfm : bi.foldl (fun acc v => acc * 2 + mux v) 0
      = (bi.map mux).foldl (fun acc v => acc * 2 + v) 0 := by rw [List.foldl_map]
  have hlen : (bi.map mux).length = bi.length := by simp
  have := foldl_bound 2 (by omega) (bi.map mux) (by
    intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact hm v) 0
  rw [hlen] at this
  simpa [natReconstruct, hfm] using this

theorem natE_lt (bi : List Nat) : natE bi < 2 ^ bi.length :=
  natReconstruct_lt muxE (fun v => by simp only [muxE]; omega) bi

section Sig

variable {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)]
  [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)]

/-! ## One ECDSA instance

The witness the circuit allocates, and the thirteen assertion families over it. -/

/-- `allocate_given_wires` and `allocate_derived_wires`, as data. No proofs; the assertions are
    `AssertedEcdsa`. -/
structure EcdsaWires (F : Type) where
  /-- `ers`: 256 lookup-node digits. -/
  us : List F
  /-- `slicing.round[…]`, all but the last, split by coordinate. -/
  wxs : List F
  wys : List F
  wzs : List F
  /-- The last stored accumulator, which `ax_zero` / `az_zero` constrain. -/
  lx : F
  ly : F
  lz : F
  /-- `slicing.{g_pk, g_r, pk_r, g_pk_r}`, flattened. -/
  pre : List F
  /-- `rxy`: the signature point. -/
  rx : F
  ry : F
  /-- The three witnessed inverses. -/
  rxinv : F
  nmsinv : F
  pkxinv : F

/-- The digits, in the packing `EcdsaCircuit.lean` uses. -/
noncomputable def EcdsaWires.bi (b : EcdsaWires F) : List Nat := (b.us.map bitrev3).map val3

/-- **The thirteen ECDSA families**, for one of the two instances. Grouped exactly as
    `soundness_of_v2` takes them; the leading four conjuncts are allocator shapes rather than
    assertions, and are marked as such. -/
def AssertedEcdsa (params : CurveParameters F) (order : Nat) (pk : AffinePoint F) (e : F)
    (b : EcdsaWires F) : Prop :=
  -- shapes, from the allocator
  b.us.length = params.kBits ∧ b.wxs.length = params.kBits - 1 ∧
  b.wys.length = params.kBits - 1 ∧ b.wzs.length = params.kBits - 1 ∧ b.pre.length = 8 ∧
  -- range_check[]/valid_index
  (∀ u ∈ b.us, IsDigit u) ∧
  -- slice_wx / slice_wy / slice_wz, all 256 rounds
  LoopFull infinityPoint true b.us (b.wxs ++ [b.lx]) (b.wys ++ [b.ly]) (b.wzs ++ [b.lz])
    pk b.rx b.ry b.pre params ∧
  -- ax_zero, az_zero
  b.lx = 0 ∧ b.lz = 0 ∧
  -- slice_x / slice_y on the four precomputed points
  ValidPreComputationExact pk b.rx b.ry b.pre params ∧
  -- e_eq, rx_eq
  reconstructE b.bi = e ∧ reconstructR b.bi = b.rx ∧
  -- is_on_curve, on the key and on R
  pk.IsOnCurve params ∧ AffinePoint.IsOnCurve ⟨b.rx, b.ry⟩ params ∧
  -- rxinv, nmsinv, pkxinv
  b.rx * b.rxinv = 1 ∧ reconstructS b.bi * b.nmsinv = 1 ∧ pk.X * b.pkxinv = 1 ∧
  -- rx_lt_order, nms_lt_order
  natR b.bi < order ∧ natS b.bi < order

/-- The curve facts `ecdsa_circuit_soundness` needs and the circuit does not assert. Bundled so
    the two instances can share one hypothesis each and so they stay visible. -/
def CurveFacts (params : CurveParameters F) (order : Nat) (pk : AffinePoint F) (rx ry : F) :
    Prop :=
  ProjectivePoint.IsOnCurve ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective
      params ∧
  bsmul (padBits (natToBits order) params.kBits) pk.toProjective params = infinityPoint ∧
  ProjectiveEquiv (bsmul (padBits (natToBits order) params.kBits)
    ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) infinityPoint ∧
  ProjectiveEquiv (bsmul (padBits (natToBits order) params.kBits)
    ({ X := rx, Y := ry : AffinePoint F }).toProjective params) infinityPoint

/-- One instance's families give a valid ECDSA signature on `natE`. Pure repackaging of
    `soundness_of_v2`. -/
theorem ecdsa_of_asserted (params : CurveParameters F) [(params.toMathlib).IsElliptic]
    [CurveHasNoPointsOfOrder2 params] (order : Nat) [Fact (Nat.Prime order)]
    (pk : AffinePoint F) (e : F) (b : EcdsaWires F)
    (hc : CurveFacts params order pk b.rx b.ry)
    (h : AssertedEcdsa params order pk e b) :
    ∃ r s : Nat, StandardEcdsaVerify pk (natE b.bi) r s order params := by
  obtain ⟨hus, hwx, hwy, hwz, hpre8, hdig, hloop, hax, haz, hpre, he, hr, hpkc, hrc,
    hrxi, hsi, hpki, hrlt, hslt⟩ := h
  obtain ⟨hgon, hpko, hgo, hro⟩ := hc
  obtain ⟨r, s, en, _, _, hen, hstd⟩ :=
    soundness_of_v2 params order pk e b.rx b.ry b.rxinv b.nmsinv b.pkxinv
      b.us b.wxs b.wys b.wzs b.pre b.lx b.ly b.lz
      hus hwx hwy hwz hpre8 hdig hloop hax haz hpre he hr hpkc hrc hrxi hsi hpki hrlt hslt
      hgon hpko hgo hro
  exact ⟨r, s, hen ▸ hstd⟩

/-! ## The mdoc-level families

Six `assert_eq`s wiring the two ECDSA instances to the MAC'd values, and six MAC assertions. -/

/-- `issuer_e_eq`, `issuer_pkx_eq`, `issuer_pky_eq`, `device_e_eq`, `device_pkx_eq`,
    `device_pky_eq`. Each is `assert_eq(ecdsa_given.X, as_eltw_unsafe(bits))`, and
    `as_eltw_unsafe` weights bit `i` by `2 ^ i` in `F` — hence the `Nat` cast rather than an
    equality of byte strings. -/
def AssertedWiring (s : SigStatement F) (eBytes dpkXBytes dpkYBytes : List Nat)
    (eIss eDev : F) (devPk : AffinePoint F) (issPk : AffinePoint F) : Prop :=
  -- issuer_e_eq
  eIss = ((beVal eBytes : Nat) : F) ∧
  -- issuer_pkx_eq, issuer_pky_eq
  issPk = s.issuerPk ∧
  -- device_e_eq
  eDev = ((beVal s.deviceSigE : Nat) : F) ∧
  -- device_pkx_eq, device_pky_eq
  devPk.X = ((beVal dpkXBytes : Nat) : F) ∧ devPk.Y = ((beVal dpkYBytes : Nat) : F)

/-- **`mac::assert_mac`, as the circuit emits it.**

    ```rust
    let (msg0, msg1) = self.bv.split::<256, 128, 128>(&given.message);
    self.bv.assert_eq("msg0_eq", &self.bv.xorb(&given.tag[0], &given.mac_ap[0]),
                                &gf2_mul.mul(&given.mac_av, &msg0))
    ```

    Two `bv.assert_eq`s on **128-bit vectors** — so two chunked field equalities, which is why
    the census names them `msg0_eq[]/chunk_eq`. This is where the signature circuit differs from
    the hash circuit: `mac_gf128::assert_mac` calls `as_eltw_field` first and then
    `logic.assert_eq` on the *field elements*, one equation and no chunking, which is why
    `MDoc.AssertedMacs` is a plain equality and this is not. -/
def MacAsserted (eqc : Eqc) (α : Nat) (tag pad : Nat × Nat) (msg : List Nat) : Prop :=
  eqc 128 (GF128.add tag.1 pad.1) (GF128.mul α (macLo msg)) ∧
  eqc 128 (GF128.add tag.2 pad.2) (GF128.mul α (macHi msg))

/-- `assert_mac/msg0_eq[]/chunk_eq` and `msg1_eq[]/chunk_eq`, three messages. -/
def AssertedSigMacs (eqc : Eqc) (s : SigStatement F) (eBytes dpkXBytes dpkYBytes : List Nat)
    (macPad : List (Nat × Nat)) : Prop :=
  MacAsserted eqc s.macKey s.macE (macPad.getD 0 (0, 0)) eBytes ∧
  MacAsserted eqc s.macKey s.macDpkX (macPad.getD 1 (0, 0)) dpkXBytes ∧
  MacAsserted eqc s.macKey s.macDpkY (macPad.getD 2 (0, 0)) dpkYBytes

/-- The wire widths the allocator and booleanity give: each MAC'd value is 32 bytes of bytes, and
    every MAC wire — the key, the three tags, the three pads — is a 128-bit `MacElt128`. Not
    assertions; the signature circuit's analogue of `MDoc.Widths`, and needed for the same reason:
    `Equates` compares `n`-bit vectors, so its operands have to fit.

    The right-hand side of each `assert_eq` is `GF128.mul`, whose range is *proved*
    (`GF128.mul_lt`) rather than assumed — it is a computed value, not a wire the prover fills. -/
def SigWidths (s : SigStatement F) (eBytes dpkXBytes dpkYBytes : List Nat)
    (macPad : List (Nat × Nat)) : Prop :=
  (eBytes.length = 32 ∧ ∀ x ∈ eBytes, x < 256) ∧
  (dpkXBytes.length = 32 ∧ ∀ x ∈ dpkXBytes, x < 256) ∧
  (dpkYBytes.length = 32 ∧ ∀ x ∈ dpkYBytes, x < 256) ∧
  s.macKey < 2 ^ 128 ∧
  (∀ k, k < 3 → (macPad.getD k (0, 0)).1 < 2 ^ 128 ∧ (macPad.getD k (0, 0)).2 < 2 ^ 128) ∧
  (s.macE.1 < 2 ^ 128 ∧ s.macE.2 < 2 ^ 128) ∧
  (s.macDpkX.1 < 2 ^ 128 ∧ s.macDpkX.2 < 2 ^ 128) ∧
  (s.macDpkY.1 < 2 ^ 128 ∧ s.macDpkY.2 < 2 ^ 128)

/-- **The MAC assertion means the MAC equation.** `Equates` at width 128, on operands that fit:
    the left side is an xor of two wires, the right a `GF128.mul` whose range is proved. -/
private theorem gf_add_lt {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) :
    GF128.add a b < 2 ^ 128 := Nat.xor_lt_two_pow ha hb

theorem macOk_of_asserted {eqc : Eqc} (heq : Equates eqc) {α : Nat} {tag pad : Nat × Nat}
    {msg : List Nat} (hα : α < 2 ^ 128)
    (ht : tag.1 < 2 ^ 128 ∧ tag.2 < 2 ^ 128) (hp : pad.1 < 2 ^ 128 ∧ pad.2 < 2 ^ 128)
    (h : MacAsserted eqc α tag pad msg) : MacOk α tag pad msg :=
  ⟨(heq 128 _ _ (gf_add_lt ht.1 hp.1) (GF128.mul_lt hα _)).mp h.1,
    (heq 128 _ _ (gf_add_lt ht.2 hp.2) (GF128.mul_lt hα _)).mp h.2⟩

/-- **Every assertion `assert_signatures_and_macs` emits.** -/
def AssertedSig (eqc : Eqc) (s : SigStatement F) (order : Nat) (params : CurveParameters F)
    (eBytes dpkXBytes dpkYBytes : List Nat) (macPad : List (Nat × Nat))
    (iss dev : EcdsaWires F) (issPk devPk : AffinePoint F) (eIss eDev : F) : Prop :=
  AssertedEcdsa params order issPk eIss iss ∧
  AssertedEcdsa params order devPk eDev dev ∧
  AssertedWiring s eBytes dpkXBytes dpkYBytes eIss eDev devPk issPk ∧
  AssertedSigMacs eqc s eBytes dpkXBytes dpkYBytes macPad

/-! ## The theorem -/

/-- **Meaning, signature half.** The assertions the mDOC signature circuit emits imply
    `ValidSignatures`.

    Hypotheses beyond the assertions, each named for what discharges it: `hkb` is the curve's bit
    width (256 for P-256, from `CurveParameters`), `hw` is the allocator's byte widths plus
    booleanity, and `hci`/`hcd` are the four curve facts per instance that the circuit does not
    assert. Everything else is proved. -/
theorem sig_meaning_parts (eqc : Eqc) (s : SigStatement F) (params : CurveParameters F)
    [(params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (order : Nat) [Fact (Nat.Prime order)]
    (eBytes dpkXBytes dpkYBytes : List Nat) (macPad : List (Nat × Nat))
    (iss dev : EcdsaWires F) (issPk devPk : AffinePoint F) (eIss eDev : F)
    (hkb : params.kBits = 256)
    (heq : Equates eqc)
    (hw : SigWidths s eBytes dpkXBytes dpkYBytes macPad)
    (hci : CurveFacts params order issPk iss.rx iss.ry)
    (hcd : CurveFacts params order devPk dev.rx dev.ry)
    (h : AssertedSig eqc s order params eBytes dpkXBytes dpkYBytes macPad iss dev issPk devPk
      eIss eDev) :
    ∃ ws : SigWitness,
      ws.e = eBytes ∧ ws.dpkX = dpkXBytes ∧ ws.dpkY = dpkYBytes ∧
      IssuerSignature s ws order params ∧ DeviceSignature s ws order params ∧
      SigMacTags s ws := by
  obtain ⟨hi, hd, ⟨wIssE, wIssPk, wDevE, wDevX, wDevY⟩, hmac⟩ := h
  obtain ⟨⟨hel, heb⟩, ⟨hxl, hxb⟩, ⟨hyl, hyb⟩, hkey, hpad, htE, htX, htY⟩ := hw
  -- the three MAC assertions, read through the chunked equality
  have hm0 := macOk_of_asserted heq hkey htE (hpad 0 (by omega)) hmac.1
  have hm1 := macOk_of_asserted heq hkey htX (hpad 1 (by omega)) hmac.2.1
  have hm2 := macOk_of_asserted heq hkey htY (hpad 2 (by omega)) hmac.2.2
  -- the digit lists are 256 long, so both reconstructions are 256-bit
  have hbiIss : iss.bi.length = 256 := by
    simp only [EcdsaWires.bi, List.length_map]; rw [hi.1, hkb]
  have hbiDev : dev.bi.length = 256 := by
    simp only [EcdsaWires.bi, List.length_map]; rw [hd.1, hkb]
  obtain ⟨ri, si, hstdI⟩ := ecdsa_of_asserted params order issPk eIss iss hci hi
  obtain ⟨rd, sd, hstdD⟩ := ecdsa_of_asserted params order devPk eDev dev hcd hd
  -- `e_eq` composed with `issuer_e_eq` identifies the two `e`s in `F`
  have hIssCast : ((natE iss.bi : Nat) : F) = ((beVal eBytes : Nat) : F) := by
    rw [← reconstructE_eq_natE, hi.2.2.2.2.2.2.2.2.2.2.1, wIssE]
  have hDevCast : ((natE dev.bi : Nat) : F) = ((beVal s.deviceSigE : Nat) : F) := by
    rw [← reconstructE_eq_natE, hd.2.2.2.2.2.2.2.2.2.2.1, wDevE]
  refine ⟨{ e := eBytes, dpkX := dpkXBytes, dpkY := dpkYBytes,
            issuerR := ri, issuerS := si, deviceR := rd, deviceS := sd, macPad := macPad },
          rfl, rfl, rfl,
          ⟨natE iss.bi, ⟨?_, hIssCast⟩, ?_⟩, ⟨natE dev.bi, beVal dpkXBytes, beVal dpkYBytes,
            ⟨?_, hDevCast⟩, ⟨?_, rfl⟩, ⟨?_, rfl⟩, ?_⟩, hm0, hm1, hm2⟩
  · simpa [hbiIss] using natE_lt iss.bi
  · rw [wIssPk] at hstdI; exact hstdI
  · simpa [hbiDev] using natE_lt dev.bi
  · exact beVal_lt_256 dpkXBytes hxl hxb
  · exact beVal_lt_256 dpkYBytes hyl hyb
  · have : ({ X := ((beVal dpkXBytes : Nat) : F), Y := ((beVal dpkYBytes : Nat) : F) } :
        AffinePoint F) = devPk := by
      rw [← wDevX, ← wDevY]
    rw [this]; exact hstdD

/-- The same, in the shape `SigSpec` states. -/
theorem sig_meaning (eqc : Eqc) (s : SigStatement F) (params : CurveParameters F)
    [(params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (order : Nat) [Fact (Nat.Prime order)]
    (eBytes dpkXBytes dpkYBytes : List Nat) (macPad : List (Nat × Nat))
    (iss dev : EcdsaWires F) (issPk devPk : AffinePoint F) (eIss eDev : F)
    (hkb : params.kBits = 256)
    (heq : Equates eqc)
    (hw : SigWidths s eBytes dpkXBytes dpkYBytes macPad)
    (hci : CurveFacts params order issPk iss.rx iss.ry)
    (hcd : CurveFacts params order devPk dev.rx dev.ry)
    (h : AssertedSig eqc s order params eBytes dpkXBytes dpkYBytes macPad iss dev issPk devPk
      eIss eDev) :
    ValidSignatures s order params := by
  obtain ⟨ws, _, _, _, hi, hd, hm⟩ :=
    sig_meaning_parts eqc s params order eBytes dpkXBytes dpkYBytes macPad iss dev issPk devPk
      eIss eDev hkb heq hw hci hcd h
  exact ⟨ws, hi, hd, hm⟩

/-! ## Not vacuous

The ECDSA half of `AssertedEcdsa` cannot be vacuous by construction: `ecdsa_of_asserted`
destructures it into nineteen components and passes them *positionally* to `soundness_of_v2`, so
if any conjunct were stated differently the application would not typecheck. `AssertedEcdsa` is
therefore exactly that theorem's hypothesis list — no weaker, no stronger — and inherits its
satisfiability from the ECDSA development.

The parts written here are the two mdoc-level groups, and those need their own check. This is the
analogue of `GoldenAsserted.lean`; the signature side cannot use a decided golden vector, because
`LoopFull` and `ValidPreComputationExact` are noncomputable and 256 rounds of projective
arithmetic over `ZMod p` would not reduce in the kernel anyway. -/

/-- For any byte strings and any MAC key, the wiring and MAC families are jointly satisfiable —
    take the pads the honest prover takes. So neither group is contradictory, and `sig_meaning` is
    not an implication from `False`. -/
theorem mdoc_families_satisfiable (s : SigStatement F)
    (eBytes dpkXBytes dpkYBytes : List Nat) (issPk devPk : AffinePoint F)
    (hdev : devPk = { X := ((beVal dpkXBytes : Nat) : F), Y := ((beVal dpkYBytes : Nat) : F) })
    (hiss : issPk = s.issuerPk)
    (htags : s.macE = (0, 0) ∧ s.macDpkX = (0, 0) ∧ s.macDpkY = (0, 0)) :
    ∃ (eIss eDev : F) (macPad : List (Nat × Nat)),
      AssertedWiring s eBytes dpkXBytes dpkYBytes eIss eDev devPk issPk ∧
      AssertedSigMacs specEqc s eBytes dpkXBytes dpkYBytes macPad := by
  obtain ⟨hE, hX, hY⟩ := htags
  refine ⟨((beVal eBytes : Nat) : F), ((beVal s.deviceSigE : Nat) : F),
    [(GF128.mul s.macKey (macLo eBytes), GF128.mul s.macKey (macHi eBytes)),
     (GF128.mul s.macKey (macLo dpkXBytes), GF128.mul s.macKey (macHi dpkXBytes)),
     (GF128.mul s.macKey (macLo dpkYBytes), GF128.mul s.macKey (macHi dpkYBytes))],
    ⟨rfl, hiss, rfl, by rw [hdev], by rw [hdev]⟩, ?_, ?_, ?_⟩ <;>
  · refine ⟨?_, ?_⟩ <;> simp [MacAsserted, hE, hX, hY, GF128.add, List.getD]

/-! ## Both halves

The capstone: the two circuits' assertion sets together give the full mDOC statement. -/

/-- **The composed statement.** `Asserted` from the hash circuit and `AssertedSig` from the
    signature circuit imply `ValidPresentationFull`.

    `hseam` is the one hypothesis that is not an assertion and cannot be: that the byte strings
    the two circuits MAC are the same. It holds except with probability `2⁻¹²⁸` over the
    Fiat-Shamir challenge, because `mac_ap` is committed in both circuits before `mac_av` is
    drawn — the argument `SigSpec.MacsAgree` records. `SharedMacs` is its checkable half, verified
    by comparing the two circuits' public inputs. -/
theorem full_meaning (hs : Statement) (s : SigStatement F) (params : CurveParameters F)
    [(params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (order : Nat) [Fact (Nat.Prime order)]
    (wh : Witness) (g : Gadgets) (eqc : Eqc) (macPad : List (Nat × Nat))
    (iss dev : EcdsaWires F) (issPk devPk : AffinePoint F) (eIss eDev : F)
    -- the hash half; `g` is the circuit's own gadgets and `GadgetsOk` their obligation
    (hwf : WellFormed hs)
    (hsha : sha256 wh.preimage wh.nblocks = wh.e)
    (hshaAttr : ∀ i, i < hs.attrId.length →
      sha256 (wh.attrs.getD i default).preimage attrShaBlocks
        = window wh.preimage ((wh.attrs.getD i default).digestOff + tag32.length) 32)
    (hg : GadgetsOk g)
    (hwd : Widths hs wh)
    (hh : Asserted g hs wh)
    -- the signature half
    (hkb : params.kBits = 256)
    (heq : Equates eqc)
    (hw : SigWidths s wh.e wh.dpkX wh.dpkY macPad)
    (hci : CurveFacts params order issPk iss.rx iss.ry)
    (hcd : CurveFacts params order devPk dev.rx dev.ry)
    (hsig : AssertedSig eqc s order params wh.e wh.dpkX wh.dpkY macPad iss dev issPk devPk eIss eDev)
    -- the seam
    (hshared : SharedMacs hs s) :
    ValidPresentationFull hs s order params := by
  obtain ⟨ws, hwe, hwx, hwy, hi, hd, hm⟩ :=
    sig_meaning_parts eqc s params order wh.e wh.dpkX wh.dpkY macPad iss dev issPk devPk
      eIss eDev hkb heq hw hci hcd hsig
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := meaning_parts g hs wh hg hwd hwf hsha hshaAttr hh
  exact ⟨wh, ws, hshared, ⟨hwe.symm, hwx.symm, hwy.symm⟩,
    p1, p2, p3, p4, p5, p6, p7, hi, hd, hm⟩

end Sig

end MDoc
