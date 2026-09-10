/-
# The assertion set, run against a real credential

`Assertions.lean` proves `Asserted → ValidPresentation`. An implication is worthless if its
hypothesis is unsatisfiable, and a transcription of 73 assertion families into Lean is exactly
the kind of thing that can be quietly contradictory — one wrong index, one flipped inequality,
and `Asserted` holds of nothing.

So this file decides `Asserted` on the same real credential `GoldenCheck.lean` uses. That
establishes three things at once:

* `Asserted` is satisfiable, so `meaning` is not vacuous;
* the transcription matches the circuit, since the credential is one the circuit accepts
  (`hash_eval.rs` runs `assert_valid_presentation_and_macs` on it and every assertion passes);
* `meaning` reproduces `GoldenCheck.valid`, which was proved independently by deciding the spec
  directly. Two routes to the same conclusion on the same data.

The negative checks at the end are the other half: they show individual families are load-bearing
rather than accidentally true.
-/

import mdoc.Assertions
import mdoc.GoldenCheck

set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

namespace MDoc
namespace Golden

/-! ## Decidability -/

instance : ∀ (w : Witness) (o : Nat), Decidable (AssertedOffset specGadgets w o) := by
  intro w o; unfold AssertedOffset; infer_instance

instance : ∀ (s : Statement) (w : Witness), Decidable (AssertedDocType specGadgets s w) := by
  intro s w; unfold AssertedDocType; infer_instance

instance : ∀ (s : Statement) (w : Witness), Decidable (AssertedValidity specGadgets s w) := by
  intro s w; unfold AssertedValidity; infer_instance

instance : ∀ (w : Witness), Decidable (AssertedDeviceKey specGadgets w) := by
  intro w; unfold AssertedDeviceKey; infer_instance

instance : ∀ (w : Witness), Decidable (AssertedValueDigests specGadgets w) := by
  intro w; unfold AssertedValueDigests; infer_instance

instance : ∀ (n : Nat) (b : List Nat) (m k : Nat),
    Decidable (AssertedPadding specGadgets n b m k) := by
  intro n b m k; unfold AssertedPadding; infer_instance

instance : ∀ (a : AttrWitness), Decidable (AssertedAttrHeader specGadgets a) := by
  intro a; unfold AssertedAttrHeader; infer_instance

instance : ∀ (a : AttrWitness), Decidable (AssertedAttrSegments specGadgets a) := by
  intro a; unfold AssertedAttrSegments; infer_instance

instance : ∀ (a : AttrWitness), Decidable (AssertedAttrPermutation specGadgets a) := by
  intro a; unfold AssertedAttrPermutation; infer_instance

instance : ∀ (a : AttrWitness) (k : Nat) (key : List Nat) (atom : Bool),
    Decidable (AssertedSlotKeyOnly specGadgets a k key atom) := by
  intro a k key atom; unfold AssertedSlotKeyOnly; infer_instance

instance : ∀ (a : AttrWitness) (k : Nat) (key val : List Nat) (m : Nat),
    Decidable (AssertedSlotKeyValue specGadgets a k key val m) := by
  intro a k key val m; unfold AssertedSlotKeyValue; infer_instance

instance : ∀ (w : Witness) (a : AttrWitness) (id val : List Nat),
    Decidable (AssertedAttr specGadgets w a id val) := by
  intro w a id val; unfold AssertedAttr; infer_instance

instance : ∀ (s : Statement) (w : Witness), Decidable (AssertedMacs s w) := by
  intro s w; unfold AssertedMacs; infer_instance

/-! ## The families, on real bytes

`assert_message_hash`'s padding families are split the same way `GoldenCheck.messageHash` splits
`ShaPadded`: the `beyond_active` family would cost one 2560-element list traversal per index, so
it is proved from `byteAt_append_replicate` while the rest are decided. -/

/-- Split a claim about all 2560 buffer bytes into the 448 active ones, which are decided, and
    the zero tail, which is a lemma. The circuit quantifies over the whole buffer, so a faithful
    transcription has to as well; deciding it directly is one 2560-element list traversal per
    index, which is minutes of kernel time and gigabytes of terms. -/
private theorem split448 {P : Nat → Prop} (hlo : ∀ i, i < 448 → P i)
    (hhi : ∀ i, 448 ≤ i → i < 2560 → P i) : ∀ i, i < 2560 → P i := by
  intro i hi
  by_cases h : i < 448
  · exact hlo i h
  · exact hhi i (by omega) hi

private theorem tail_zero : ∀ i, 448 ≤ i → byteAt w.preimage i = 0 := by
  have hlen : active.length = 448 := by rfl
  intro i hge
  show byteAt (active ++ List.replicate 2112 0) i = 0
  exact byteAt_append_replicate active 2112 i (by omega)

/-- Every wire of the buffer holds a byte. Linear in the buffer, unlike the indexed form. -/
theorem buf_bytes : ∀ v ∈ w.preimage, v < 256 := by
  show ∀ v ∈ active ++ List.replicate 2112 0, v < 256
  intro v hv
  rcases List.mem_append.mp hv with h | h
  · exact (by decide : ∀ u ∈ active, u < 256) v h
  · rw [List.eq_of_mem_replicate h]; omega

/-- Everything `assert_nblocks`, `assert_length` and `assert_sha_padding` emit for the MSO. -/
theorem assertedPadding :
    AssertedPadding specGadgets maxShaBlocks w.preimage w.msgLen w.nblocks := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · -- separator
    exact split448 (P := fun i => i = w.msgLen → byteAt w.preimage i = 0x80)
      (by decide) (fun i hge _ heq => absurd heq (by
        have hm : w.msgLen = 403 := rfl
        omega))
  · -- pad_zero
    exact split448
      (P := fun i => w.msgLen < i → w.nblocks * 64 > i + 8 → byteAt w.preimage i = 0)
      (by decide) (fun i hge _ _ hlt => absurd hlt (by
        have hn : w.nblocks * 64 = 448 := rfl
        omega))
  · -- beyond_active
    exact split448 (P := fun i => w.nblocks * 64 ≤ i → byteAt w.preimage i = 0)
      (fun i hlo hge => absurd hge (by
        have hn : w.nblocks * 64 = 448 := rfl
        omega))
      (fun i hge _ _ => tail_zero i hge)
  · -- every buffer wire is a byte
    exact buf_bytes

theorem assertedDocType : AssertedDocType specGadgets st w := by decide

theorem assertedValidity : AssertedValidity specGadgets st w := by decide

theorem assertedDeviceKey : AssertedDeviceKey specGadgets w := by decide

theorem assertedValueDigests : AssertedValueDigests specGadgets w := by decide

theorem assertedAttrs :
    w.attrs.length = st.attrId.length ∧
    ∀ i, i < st.attrId.length →
      AssertedAttr specGadgets w (w.attrs.getD i default) (st.attrId.getD i []) (st.attrValue.getD i []) := by
  decide

theorem assertedMacs : AssertedMacs st w := by decide

/-- **The assertion set holds on a real credential.** So `Asserted` is satisfiable and `meaning`
    is not an implication from `False`. -/
theorem asserted : Asserted specGadgets st w :=
  ⟨assertedPadding, assertedDocType, assertedValidity, assertedDeviceKey, assertedValueDigests,
    assertedAttrs, assertedMacs⟩

/-- **The wire widths, on real bytes.** `meaning`'s booleanity hypothesis, decided. -/
theorem widths : Widths st w :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## The two routes agree -/

/-- The SHA-256 facts `meaning` takes as hypotheses, here supplied by computation rather than by
    the bridge. On one credential that is a decidable check; in general it is
    `Bridge/Sha256Gf2/`. -/
theorem shaMso : sha256 w.preimage w.nblocks = w.e := by decide +kernel

theorem shaAttrs : ∀ i, i < st.attrId.length →
    sha256 (w.attrs.getD i default).preimage attrShaBlocks
      = window w.preimage ((w.attrs.getD i default).digestOff + tag32.length) 32 := by
  decide +kernel

/-- **End to end through the assertion set.** `GoldenCheck.valid` proved `ValidPresentation st`
    by deciding each spec clause. This proves the same proposition by deciding each *assertion
    family* and then applying `meaning`. The two paths share only the data. -/
theorem valid_via_meaning : ValidPresentation st :=
  meaning specGadgets st w gadgetsOk_spec widths wellFormed shaMso shaAttrs asserted

/-! ## Negative checks

Each perturbation breaks exactly one family. Without these, a conjunct that had been transcribed
as something trivially true would still pass everything above. -/

/-- `shift_preimage_bounds/lt`: an offset at or past the message length is rejected. -/
theorem offset_bound_is_live : ¬ AssertedOffset specGadgets w w.msgLen := by decide

/-- `shift_preimage_bounds/ge_five`: so is one below 5. -/
theorem offset_floor_is_live : ¬ AssertedOffset specGadgets { w with msgLen := 400 } 4 := by decide

/-- `assert_nblocks/limit_upper`: the block count must cover the message plus nine bytes. -/
theorem nblocks_bound_is_live :
    ¬ AssertedPadding specGadgets maxShaBlocks w.preimage w.msgLen 6 := by decide

/-- `assert_length/len_eq`: the encoded length field is checked against `msgLen * 8`, so a
    different `msgLen` with the same buffer fails. -/
theorem length_field_is_live :
    ¬ AssertedPadding specGadgets maxShaBlocks w.preimage 402 w.nblocks := by decide

/-- `cbor_header[]/header_byte`: the `"docType"` literal is really compared. -/
theorem docType_header_is_live :
    ¬ AssertedDocType specGadgets st { w with docTypeOff := w.docTypeOff + 1 } := by decide

/-- `cmp_until`: the validity comparison is not vacuous. -/
theorem validity_cmp_is_live :
    ¬ AssertedValidity specGadgets { st with now := st.now.set 3 (0x36 : Nat) } w := by decide

/-- `key_eq[]/chunk_eq`: the two coordinates are read from different offsets. -/
theorem deviceKey_eq_is_live :
    ¬ AssertedDeviceKey specGadgets { w with dpkX := w.dpkY, dpkY := w.dpkX } := by decide

/-- `assert_permutation[]/perm_neq`: the six pairwise checks bite. -/
private def attrDupPerm : AttrWitness := { w.attrs.getD 0 default with perm := [0, 0, 2, 3] }

theorem perm_is_live : ¬ AssertedAttrPermutation specGadgets attrDupPerm := by decide

/-- `assert_item_slot_key_value/assert_prefix_equal`: the disclosed value is really compared. -/
theorem slotValue_is_live :
    ¬ AssertedSlotKeyValue specGadgets (w.attrs.getD 0 default) 3 elementValueKey [0xF4]
        (elementValueKey.length + 1 + 64) := by decide

/-- `assert_mac/msg0_eq`: the MAC is on the digest. -/
theorem mac_is_live : ¬ AssertedMacs st { w with e := w.e.set 0 0 } := by decide

end Golden
end MDoc
