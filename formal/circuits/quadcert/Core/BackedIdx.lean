/-
# `Backed` by index instead of by scan

`RawGroup.backedRawWith` locates an assertion's backing term with
`(azt a.wireLayer).any (· == ...)` -- a linear scan **per assertion**. The cost is therefore
`Σ_L n_L²` over the per-layer assertion counts, and that is measured, not feared:

| | Σ n_L² | cost |
|---|---|---|
| SHA-256 one block | 44,310,848 | 3,069 s |
| mdoc_hash | **81,149,916,157** | **~205 h ≈ 8.5 days** |

1,831x SHA-256 rather than the 44x a linear projection assumes, and it comes from one fat layer:
mdoc_hash puts **284,741** of its 303,413 assertions on layer 18. Measured scan rate is ~7.6 µs
per comparison.

**The fix is the one this codebase already applies to `wireFn`, `nodeFn` and `groupTree`:** stop
walking a list. Two pieces are needed, and an index alone is *not* enough -- `(azt L).getD k` is
itself an O(k) walk:

* `aztFn : Nat → Nat → RawTerm`, the assertion-term table emitted as a bisection, with an
  agreement lemma proved by one sequential pass per layer (the `nodefn_ok` pattern);
* the backing index `k` carried on each assertion record.

Then `Backed` costs one O(log n) lookup and one comparison per assertion: 303,413 lookups instead
of 81 billion comparisons, about **6 seconds**.

This module is the Lean half. `backedRawWith` is left untouched, so every existing consumer --
`Check.backed_of_rawWith`, `assertions_zero_of_accepts` -- is unaffected; `backedRawWith_of_at`
bridges the cheap check to the one they expect.
-/

import quadcert.Core.RawGroup

namespace Quadcert

/-- `Backed`, located by index through a bisection rather than by scanning. -/
def backedRawAt (r : RawCircuit) (zeroConst : Nat) (aztFn : Nat → Nat → RawTerm)
    (a : RawAssert) (k : Nat) : Bool :=
  (decide (a.wireLayer < r.layers.length) &&
    (match r.wireFn a.assertedNode with
     | some p =>
        (p.1 == a.wireLayer + 1) &&
          (aztFn a.wireLayer k == (⟨a.wireIndex, p.2, p.2, zeroConst⟩ : RawTerm))
     | none => false))
  || (decide (a.wireIndex < r.noutput) && (r.wireFn a.assertedNode == some (0, a.wireIndex)))

/-- A term read out of a list by an in-range index is a member of it. Proved by induction
    rather than via `List.getD_eq_getElem`, which is not reachable from this import set. -/
theorem getD_mem {α : Type} : ∀ (l : List α) (d : α) {k : Nat}, k < l.length → l.getD k d ∈ l
  | [], _, _, hk => absurd hk (by simp)
  | a :: t, d, 0, _ => by simp [List.getD]
  | a :: t, d, k + 1, hk => by
      have : k < t.length := by simpa using hk
      simpa [List.getD] using List.mem_cons_of_mem a (getD_mem t d this)

/-- **The bridge.** The indexed check implies the scanning one, so nothing downstream changes.
    `hfn` is the `aztFn`-agreement obligation: one sequential pass per layer, not per assertion. -/
theorem backedRawWith_of_at (r : RawCircuit) (zeroConst : Nat) (azt : Nat → List RawTerm)
    (aztFn : Nat → Nat → RawTerm)
    (hfn : ∀ L k, k < (azt L).length → aztFn L k = (azt L).getD k ⟨0, 0, 0, 0⟩)
    (a : RawAssert) (k : Nat) (hk : k < (azt a.wireLayer).length)
    (h : backedRawAt r zeroConst aztFn a k = true) :
    backedRawWith r zeroConst azt a = true := by
  -- the two definitions differ in exactly one test; upgrade that and the rest is Bool algebra
  have key : ∀ p : Nat × Nat,
      ((p.1 == a.wireLayer + 1) &&
        (aztFn a.wireLayer k == (⟨a.wireIndex, p.2, p.2, zeroConst⟩ : RawTerm))) = true →
      ((p.1 == a.wireLayer + 1) &&
        (azt a.wireLayer).any
          (fun t => t == (⟨a.wireIndex, p.2, p.2, zeroConst⟩ : RawTerm))) = true := by
    intro p hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [List.any_eq_true]
    refine ⟨(azt a.wireLayer).getD k ⟨0, 0, 0, 0⟩, getD_mem _ _ hk, ?_⟩
    simp only [beq_iff_eq]
    exact (hfn a.wireLayer k hk).symm.trans hp.2
  unfold backedRawAt at h
  unfold backedRawWith
  cases hw : r.wireFn a.assertedNode with
  | none =>
      rw [hw] at h
      simpa using h
  | some p =>
      rw [hw] at h
      simp only []
      rcases Bool.or_eq_true _ _ |>.mp h with hl | hr
      · rw [Bool.or_eq_true]
        refine Or.inl ?_
        rw [Bool.and_eq_true] at hl
        rw [Bool.and_eq_true]
        exact ⟨hl.1, key p hl.2⟩
      · rw [Bool.or_eq_true]
        exact Or.inr hr

end Quadcert
