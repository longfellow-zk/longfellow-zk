import SHA.Sigma
import quadcert.Bridge.Sha256Gf2.Gf2Row

/-!
# Lining the binary field's bit forms up with the specification's

`SHA/Spec.lean` states SHA-256 over *bit lists*, and `SHA/Bits.lean` / `SHA/Sigma.lean` supply
the per-bit algebra: `bitAt` inverts `ofBits`, and `σ₀ σ₁ Σ₀ Σ₁ Ch Maj` each reduce to one
identity per output bit. All of that is pure `Nat` — it does not mention a field at all — so the
prime-field bridge's spec layer applies to the binary-field bridge unchanged.

What has to be said once is that the two *spellings* agree. Over a prime field the circuit writes
xor as `a + b − 2ab` (`SHA256.xb`) because that is the only degree-2 polynomial that does it;
over GF(2^128) addition *is* xor. On bits the two coincide, and the same for `Ch` and `Maj`, so
this file is four case analyses and their composition with `Gf2Bits`.

The payoff is that `Gf2Row.Form` — the five functions every injection factor injects — maps onto
`SHA256.xb`, `SHA256.chb` and `SHA256.majb` exactly, and the rotation lemmas
(`sigma0_bits`, `Sigma1_bits`, …) then need no binary-field counterpart.
-/

namespace Sha256Gf2

open SHA256

variable {F : Type} [Field F] [CharP F 2]

/-! ## The `Nat` spellings coincide on bits -/

/-- The prime field's xor and the binary field's are the same function of two bits. -/
theorem xb_eq_xor {a b : Nat} (ha : IsBit a) (hb : IsBit b) : xb a b = a ^^^ b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl

theorem xor_isBit {a b : Nat} (ha : IsBit a) (hb : IsBit b) : IsBit (a ^^^ b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [IsBit]

/-- `Ch` as a selection, which is the shape `Gf2Bits.bitOf_ch` produces. -/
theorem chb_eq_ite {a b c : Nat} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c) :
    chb a b c = if a = 1 then b else c := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl

/-- `Maj` as a threshold, which is the shape `Gf2Bits.bitOf_maj` produces. -/
theorem majb_eq_ite {a b c : Nat} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c) :
    majb a b c = if a + b + c ≤ 1 then 0 else 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl

/-! ## …hence the field's five forms are the specification's

`bitOf` of a row is `IsBit` by construction, so these compose with no side conditions beyond the
booleanity the artifact asserts. -/

theorem bitOf_IsBit (x : F) : IsBit (bitOf x) := bitOf_isBit x

theorem bitOf_xor2_spec {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    bitOf (x + y) = xb (bitOf x) (bitOf y) := by
  rw [bitOf_xor2 hx hy, xb_eq_xor (bitOf_IsBit x) (bitOf_IsBit y)]

theorem bitOf_xor3_spec {x y z : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (hz : z = 0 ∨ z = 1) :
    bitOf (x + y + z) = xb (xb (bitOf x) (bitOf y)) (bitOf z) := by
  rw [bitOf_xor3 hx hy hz, xb_eq_xor (bitOf_IsBit x) (bitOf_IsBit y),
    xb_eq_xor (xor_isBit (bitOf_IsBit x) (bitOf_IsBit y)) (bitOf_IsBit z)]

theorem bitOf_ch_spec {a b c : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) :
    bitOf (a * b + c + a * c) = chb (bitOf a) (bitOf b) (bitOf c) := by
  rw [bitOf_ch ha hb hc,
    chb_eq_ite (bitOf_IsBit a) (bitOf_IsBit b) (bitOf_IsBit c)]

theorem bitOf_maj_spec {a b c : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) :
    bitOf (a * b + b * c + a * c) = majb (bitOf a) (bitOf b) (bitOf c) := by
  rw [bitOf_maj ha hb hc,
    majb_eq_ite (bitOf_IsBit a) (bitOf_IsBit b) (bitOf_IsBit c)]

/-! ## A form's bit, in specification terms

One statement covering all five, so a cone's rows map onto the specification without a case split
at the instance. -/

/-- The `Nat` reading of a form, in the specification's own vocabulary. -/
def Form.spec (bit : Nat → Nat) : Form → Nat
  | .prod => 0
  | .one a => bit a
  | .xor2 a b => xb (bit a) (bit b)
  | .xor3 a b c => xb (xb (bit a) (bit b)) (bit c)
  | .ch a b c => chb (bit a) (bit b) (bit c)
  | .maj a b c => majb (bit a) (bit b) (bit c)

/-- **A row's bit is its form's specification value.** `bitOf ∘ lv` is the bit assignment; the
    hypothesis is the leaf booleanity the `is_boolean` assertions give. -/
theorem Form.bitOf_spec (lv : Nat → F) (hone : lv 0 = 1) :
    ∀ f : Form, (∀ i ∈ f.wires, lv i = 0 ∨ lv i = 1) →
      bitOf (f.pairs.map (fun t => lv t.1 * lv t.2)).sum
        = Form.spec (fun i => bitOf (lv i)) f
  | .prod, _ => by simp [Form.pairs, Form.spec, bitOf_zero]
  | .one a, h => by
      rw [show ((Form.one a).pairs.map (fun t => lv t.1 * lv t.2)).sum = lv a from by
        simp [Form.pairs, hone]]
      rfl
  | .xor2 a b, h => by
      rw [show ((Form.xor2 a b).pairs.map (fun t => lv t.1 * lv t.2)).sum = lv a + lv b from by
        simp [Form.pairs, hone]]
      exact bitOf_xor2_spec (h a (by simp [Form.wires])) (h b (by simp [Form.wires]))
  | .xor3 a b c, h => by
      rw [show ((Form.xor3 a b c).pairs.map (fun t => lv t.1 * lv t.2)).sum
          = lv a + lv b + lv c from by simp [Form.pairs, hone]; ring]
      exact bitOf_xor3_spec (h a (by simp [Form.wires])) (h b (by simp [Form.wires]))
        (h c (by simp [Form.wires]))
  | .ch a b c, h => by
      rw [show ((Form.ch a b c).pairs.map (fun t => lv t.1 * lv t.2)).sum
          = lv a * lv b + lv c + lv a * lv c from by simp [Form.pairs, hone]; ring]
      exact bitOf_ch_spec (h a (by simp [Form.wires])) (h b (by simp [Form.wires]))
        (h c (by simp [Form.wires]))
  | .maj a b c, h => by
      rw [show ((Form.maj a b c).pairs.map (fun t => lv t.1 * lv t.2)).sum
          = lv a * lv b + lv b * lv c + lv a * lv c from by simp [Form.pairs, hone]; ring]
      exact bitOf_maj_spec (h a (by simp [Form.wires])) (h b (by simp [Form.wires]))
        (h c (by simp [Form.wires]))

/-- **Every row of a cone, in specification terms.** The companion of `Gf2Row.rows_isBit`: same
    two decidable inputs, and the conclusion is now about `xb`, `chb` and `majb` rather than about
    field elements. -/
theorem rows_spec (lv : Nat → F) (L M : Nat) (hone : lv 0 = 1)
    (hbl : ∀ i, i < L → i ≠ 0 → lv i = 0 ∨ lv i = 1)
    (ts : Nat → List (Nat × Nat)) (form : Nat → Form)
    (hperm : ∀ j, j < M → ((ts j).map normPair).Perm (((form j).pairs).map normPair))
    (hwire : ∀ j, j < M → ∀ i ∈ (form j).wires, i < L ∧ i ≠ 0) :
    ∀ j, j < M →
      bitOf ((ts j).map (fun t => lv t.1 * lv t.2)).sum
        = Form.spec (fun i => bitOf (lv i)) (form j) := by
  intro j hj
  rw [sum_eq_of_perm lv (ts j) ((form j).pairs) (hperm j hj)]
  exact Form.bitOf_spec lv hone (form j)
    (fun i hi => hbl i (hwire j hj i hi).1 (hwire j hj i hi).2)

end Sha256Gf2
