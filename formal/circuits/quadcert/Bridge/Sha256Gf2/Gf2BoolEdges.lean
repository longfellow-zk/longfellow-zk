import quadcert.Bridge.Sha256Gf2.Gf2BoolE0
import quadcert.Bridge.Sha256Gf2.Gf2BoolE1
import quadcert.Bridge.Sha256Gf2.Gf2BoolE2
import quadcert.Bridge.Sha256Gf2.Gf2BoolE3
import quadcert.Bridge.Sha256Gf2.Gf2BoolE4
import quadcert.Bridge.Sha256Gf2.Gf2BoolE5
import quadcert.Bridge.Sha256Gf2.Gf2BoolE6
import quadcert.Bridge.Sha256Gf2.Gf2BoolE7
import quadcert.Bridge.Sha256Gf2.Gf2BoolE8
import quadcert.Bridge.Sha256Gf2.Gf2BoolE9
import quadcert.Bridge.Sha256Gf2.Gf2BoolE10
import quadcert.Bridge.Sha256Gf2.Gf2BoolE11
import quadcert.Bridge.Sha256Gf2.Gf2BoolE12

/-!
# All 6,656 `is_boolean` assertions as one edge list

The 13 slices are composed by `edgesMatch_of_chunks`; `allBoolBits` then concludes
booleanity for every bit in the circuit from that one structural check plus `tmpl_isBool`.

Together with `Gf2Wrap.lean`'s 184 wrapping-sum cones this is *every* assertion the
artifact makes: 6,656 + 184 = 6,840.

There is no per-assertion module, no per-assertion lemma and no per-assertion algebra.
-/

set_option maxRecDepth 8000000
set_option maxHeartbeats 0

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2

theorem allBoolEdges : edgesMatch nodeFn tnBool mapOfB 6656 = true := by
  -- hoisted: inside `refine` this elaborates against metavariables and blows the interpreter
  have ht : tiles [(0, 512), (512, 512), (1024, 512), (1536, 512), (2048, 512), (2560, 512), (3072, 512), (3584, 512), (4096, 512), (4608, 512), (5120, 512), (5632, 512), (6144, 512)] 0 6656 = true := by decide +kernel
  refine edgesMatch_of_chunks nodeFn tnBool mapOfB [(0, 512), (512, 512), (1024, 512), (1536, 512), (2048, 512), (2560, 512), (3072, 512), (3584, 512), (4096, 512), (4608, 512), (5120, 512), (5632, 512), (6144, 512)] 6656 ht ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · show edgesMatchAt nodeFn tnBool mapOfB 0 512 = true
    exact ec0
  · show edgesMatchAt nodeFn tnBool mapOfB 512 512 = true
    exact ec1
  · show edgesMatchAt nodeFn tnBool mapOfB 1024 512 = true
    exact ec2
  · show edgesMatchAt nodeFn tnBool mapOfB 1536 512 = true
    exact ec3
  · show edgesMatchAt nodeFn tnBool mapOfB 2048 512 = true
    exact ec4
  · show edgesMatchAt nodeFn tnBool mapOfB 2560 512 = true
    exact ec5
  · show edgesMatchAt nodeFn tnBool mapOfB 3072 512 = true
    exact ec6
  · show edgesMatchAt nodeFn tnBool mapOfB 3584 512 = true
    exact ec7
  · show edgesMatchAt nodeFn tnBool mapOfB 4096 512 = true
    exact ec8
  · show edgesMatchAt nodeFn tnBool mapOfB 4608 512 = true
    exact ec9
  · show edgesMatchAt nodeFn tnBool mapOfB 5120 512 = true
    exact ec10
  · show edgesMatchAt nodeFn tnBool mapOfB 5632 512 = true
    exact ec11
  · show edgesMatchAt nodeFn tnBool mapOfB 6144 512 = true
    exact ec12

variable {F : Type} [Field F] [CharP F 2]

/-- **Booleanity of every bit in the circuit, from one edge list.** All the bits every
    injection cone reads, from one structural `decide` and one template lemma. -/
theorem allBoolBits (α : F) (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hz : ∀ e, e < 6656 → interpDag (raw.toDag (consts α)) inputs (assertOfB e) = 0) :
    ∀ e, e < 6656 →
      interpDag (raw.toDag (consts α)) inputs (bitOfB e) = 0
        ∨ interpDag (raw.toDag (consts α)) inputs (bitOfB e) = 1 := by
  intro e he
  have htr := edges_transfer raw (consts α) inputs nodeFn nodefn_ok tnBool mapOfB 6656
    allBoolEdges mapOfB_lt e he
  have hone : (fun h => interpDag (raw.toDag (consts α)) inputs (mapOfB e h)) 0 = 1 := by
    show interpDag (raw.toDag (consts α)) inputs 0 = 1
    exact node0 α inputs hin0
  have hroot : interpDag (tmplDag (consts α) tnBool)
      (fun h => interpDag (raw.toDag (consts α)) inputs (mapOfB e h)) 2 = 0 := by
    rw [← htr 2 (by decide)]
    show interpDag (raw.toDag (consts α)) inputs (assertOfB e) = 0
    exact hz e he
  have hb := tmpl_isBool (consts α)
    (fun h => interpDag (raw.toDag (consts α)) inputs (mapOfB e h)) (consts_one α) hone hroot
  show interpDag (raw.toDag (consts α)) inputs (bitOfB e) = 0
    ∨ interpDag (raw.toDag (consts α)) inputs (bitOfB e) = 1
  exact hb

end Sha256Gf2
