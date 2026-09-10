/-
# The specification, run against a real credential

`Golden.lean` holds one real `mdoc_hash` input, emitted from the Rust test vector
`mdoc_zk_testcases::vectors::TEST_DATA` — the same one `hash_eval.rs` feeds to the circuit. This
file decides every clause of `mdoc/Spec.lean` on it.

## What this catches that nothing else does

`Spec.lean` was written by reading `circuits/src/hash/circuit.rs` and transcribing. The `rfl`
lemmas in that file check *internal* consistency — that the CBOR decoder agrees with the key
literals — and the `Demo` section checks offset arithmetic against a layout I wrote myself. Both
would survive a clause that misreads the Rust.

This does not. If `MsoDeviceKey` had the y-coordinate at `+ 34` instead of `+ 35`, if `MsoValidity`
compared the window in the wrong direction, if `AttrSegments` expected the slots to start at 4, if
`macLo` and `macHi` were swapped, or if `ShaPadded` disagreed with `assert_nblocks` — the
corresponding `decide` below fails on real bytes.

The negative checks matter as much as the positive ones. A clause that is accidentally trivial
(quantifying over an empty range, say) passes every positive test. Each `_fails` theorem perturbs
one field and requires the clause to notice.

## Regenerating

```
MDOC_LEAN_GOLDEN_OUT=formal/circuits/mdoc/Golden.lean \
  cargo test -p mdoc-zk-circuits --test circuits_tests lean_golden
```
-/

import mdoc.Golden

set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

namespace MDoc
namespace Golden

/-! ## Decidability of the remaining clauses

`Spec.lean` supplies instances for the four small MSO clauses. These are the rest: the attribute
verifier, the SHA padding predicate, and the MAC. Every one is `unfold` then `infer_instance` —
the clauses are already conjunctions of bounded quantifiers over decidable atoms, and the `unfold`
is only needed because instance search will not look inside a `def`. -/

instance : ∀ (n : Nat) (b : List Nat) (m k : Nat), Decidable (ShaPadded n b m k) := by
  intro n b m k; unfold ShaPadded; infer_instance

instance : ∀ (w : Witness), Decidable (MessageHash w) := by
  intro w; unfold MessageHash; infer_instance

instance : ∀ (a : AttrWitness), Decidable (AttrHeader a) := by
  intro a; unfold AttrHeader; infer_instance

instance : ∀ (a : AttrWitness), Decidable (AttrSegments a) := by
  intro a; unfold AttrSegments; infer_instance

instance : ∀ (a : AttrWitness), Decidable (AttrPermutation a) := by
  intro a; unfold AttrPermutation; infer_instance

instance : ∀ (a : AttrWitness) (k : Nat) (key : List Nat) (atom : Bool),
    Decidable (AttrSlotKeyOnly a k key atom) := by
  intro a k key atom; unfold AttrSlotKeyOnly; infer_instance

instance : ∀ (a : AttrWitness) (k : Nat) (key val : List Nat),
    Decidable (AttrSlotKeyValue a k key val) := by
  intro a k key val; unfold AttrSlotKeyValue; infer_instance

instance : ∀ (w : Witness) (a : AttrWitness) (id val : List Nat),
    Decidable (AttrOk w a id val) := by
  intro w a id val; unfold AttrOk; infer_instance

instance : ∀ (s : Statement) (w : Witness), Decidable (Attributes s w) := by
  intro s w; unfold Attributes; infer_instance

instance : ∀ (α : Nat) (t p : Nat × Nat) (m : List Nat), Decidable (MacOk α t p m) := by
  intro α t p m; unfold MacOk; infer_instance

instance : ∀ (s : Statement) (w : Witness), Decidable (MacTags s w) := by
  intro s w; unfold MacTags; infer_instance

instance : ∀ (s : Statement), Decidable (WellFormed s) := by
  intro s; unfold WellFormed; infer_instance

/-! ## The credential, checked

Sanity first: the vector is the one we think it is. -/

/-- 403 bytes of MSO in 7 blocks, two disclosed attributes, and the docType check is live. -/
theorem shape :
    w.msgLen = 403 ∧ w.nblocks = 7 ∧ w.preimage.length = maxShaBlocks * 64 ∧
    st.attrId.length = 2 ∧ st.suppressDocType = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The public statement is well formed by `Spec.lean`'s own predicate, so `ValidPresentation` is
    a faithful reading of the circuit on it. -/
theorem wellFormed : WellFormed st := by decide

/-! ### The seven clauses -/

/-- `assert_message_hash`. The preimage is SHA-padded to 7 blocks and hashes to the `e` the MACs
    bind. This one check exercises `wordsOfBytes`, `blocksOf`, `hashBlocks`, the whole of
    `SHA/Spec.lean`'s compression function, and every conjunct of `assert_nblocks`,
    `assert_length` and `assert_sha_padding`.

    Seven of the eight conjuncts are decided. The eighth — every byte past the active blocks is
    zero — is proved by `byteAt_append_replicate` instead, because deciding it would traverse the
    2560-byte list once per index: 9 minutes of kernel reduction, against 22 seconds for the whole
    of SHA-256. The data is emitted as `active ++ List.replicate 2112 0` precisely so that this
    substitution is available. -/
theorem messageHash : MessageHash w := by
  have hlen : active.length = 448 := by rfl
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, by decide⟩,
    by decide +kernel⟩
  intro i _ hge
  have hnb : (64 : Nat) * w.nblocks = 448 := by rfl
  rw [hnb] at hge
  show byteAt (active ++ List.replicate 2112 0) i = 0
  exact byteAt_append_replicate active 2112 i (by omega)

/-- `assert_mso_doc_type` — including the one/two-byte header branch and the value comparison
    against `org.iso.18013.5.1.mDL`. -/
theorem docType : MsoDocType st w := by decide

/-- `assert_mso_validity`. `2025-04-30` sits inside `[2025-04-28, 2026-04-28]`. -/
theorem validity : MsoValidity st w := by decide

/-- `assert_mso_device_key` — both coordinates, and the `0x22 0x58 0x20` between them. -/
theorem deviceKey : MsoDeviceKey w := by decide

/-- `assert_mso_value_digests`. -/
theorem valueDigests : MsoValueDigests w := by decide

/-- `assert_attributes`. Both `IssuerSignedItem`s: tag-24 header, 4-entry map, the four segments
    tiling the payload, the permutation, the `digestID`/`random` CBOR length checks, the
    `elementIdentifier`/`elementValue` contents, and each item's SHA-256 landing on a `0x58 0x20`
    digest in the MSO. -/
theorem attributes : Attributes st w := by decide +kernel

/-- `assert_mac_tags`. Three GF(2^128) MACs. Independently of the clause, this checks that
    `GF128.mul` in `GF128/Poly.lean` agrees with `circuits/mac/src/concrete.rs::gf2_128_mul` —
    two implementations of the field, written from opposite ends of the ladder. -/
theorem macTags : MacTags st w := by decide

/-- **All seven at once.** `ValidPresentation` is existential in the witness, so this is the
    statement the verifier is entitled to believe about this credential. -/
theorem valid : ValidPresentation st :=
  ⟨w, messageHash, docType, validity, deviceKey, valueDigests, attributes, macTags⟩

/-! ### Negative checks

A clause that always holds would pass everything above. Each of these perturbs exactly one field
and requires the clause to reject. -/

/-- One flipped preimage byte breaks the hash. -/
theorem messageHash_fails_on_flipped_byte :
    ¬ MessageHash { w with preimage := w.preimage.set 10 0 } :=
  fun h => absurd h.2 (by decide +kernel)

/-- Claiming one block fewer breaks `assert_nblocks`. -/
theorem messageHash_fails_on_wrong_nblocks : ¬ MessageHash { w with nblocks := 6 } :=
  fun h => absurd h.1 (by decide)

/-- A verification time after `validUntil` is rejected. -/
theorem validity_fails_when_expired :
    ¬ MsoValidity { st with now := st.now.set 3 (0x36 : Nat) } w := by decide

/-- Offsets are advice, but not free: moving one by a byte breaks the literal check. -/
theorem docType_fails_on_shifted_offset :
    ¬ MsoDocType st { w with docTypeOff := w.docTypeOff + 1 } := by decide

/-- The two device-key coordinates are read from different places. -/
theorem deviceKey_fails_on_swap :
    ¬ MsoDeviceKey { w with dpkX := w.dpkY, dpkY := w.dpkX } := by decide

/-- The MAC is on the digest, not on nothing: one flipped byte of `e` breaks it. -/
theorem macTags_fails_on_flipped_e :
    ¬ MacTags st { w with e := w.e.set 0 0 } := by decide

/-- The two halves of the MAC'd value are not interchangeable — this is the check that would
    have caught `macLo` and `macHi` being swapped. -/
theorem macTags_fails_on_swapped_halves :
    ¬ MacTags st { w with e := w.e.drop 16 ++ w.e.take 16 } := by decide

/-- Slot 0 of the first attribute, with its permutation entry duplicated. -/
def attr0DupPerm : AttrWitness := { w.attrs.getD 0 default with perm := [0, 0, 2, 3] }

def wDupPerm : Witness := { w with attrs := w.attrs.set 0 attr0DupPerm }

/-- Duplicating a slot in the permutation breaks `assert_permutation`. -/
theorem attributes_fails_on_duplicate_perm : ¬ Attributes st wDupPerm := by decide +kernel

/-- Disclosing a different value for the same identifier breaks `assert_item_slot_key_value`. -/
theorem attributes_fails_on_wrong_value :
    ¬ Attributes { st with attrValue := st.attrValue.set 0 [0xF4] } w := by decide +kernel

/-- The first attribute, pointed at the *second* attribute's digest. -/
def attr0OtherDigest : AttrWitness :=
  { w.attrs.getD 0 default with digestOff := (w.attrs.getD 1 default).digestOff }

def wOtherDigest : Witness := { w with attrs := w.attrs.set 0 attr0OtherDigest }

/-- Pointing an attribute at a different `0x58 0x20` in the MSO breaks the digest equality — the
    clause that second-preimage resistance protects in general. Note that the `tag32` header check
    still passes there: locating a digest header is not the same as locating *this* digest, which
    is exactly why `Parsing.lean` needs `NoSecondPreimage`. -/
theorem attributes_fails_on_wrong_digest : ¬ Attributes st wOtherDigest := by decide +kernel

end Golden
end MDoc
