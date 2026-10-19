import Lfzk.V1StrongV7TwoSideCutContext
import Lfzk.Fork.Geometry

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-! The committed cut trace and nonterminal answers form a local V1 state. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Fork.CutContext

open Lfzk.V1StrongV7TwoSideCutContext

open Lfzk.LigeroPairGeometryTwoSide
open scoped Classical

variable {Enc D Coin X Other F Msg₂ Out : Type}
  [DecidableEq Enc] [Inhabited D] [DecidableEq D]
  [Inhabited Other]
  {nl nl₂ block dblock r tA N Lsch TM : ℕ}
  {rounds rounds₂ : ℕ → ℕ}

theorem setup2_context_eq_output_cutState_fst
    [Nonempty Coin] [Inhabited Msg₂]
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Point (D := D) (C := Coin) (X := X) (Other := Other)
        (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
        (block := block) (dblock := dblock) (r := r)
        (w := rounds) (w₂ := rounds₂))
      Coin Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin)
    (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → FirstMessage (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (msgOf₂ : Out → ℕ → Msg₂)
    (mt : Fin TM → D)
    (H : Point (D := D) (C := Coin) (X := X)
      (Other := Other) (F := F) (Msg₂ := Msg₂)
      (nl := nl) (nl₂ := nl₂) (block := block)
      (dblock := dblock) (r := r) (w := rounds)
      (w₂ := rounds₂) → Coin) :
    let S := Lfzk.Fork.Transcript.setup2 body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let out := S.proof mt H
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := nl) (w := rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf
        rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
    S.context mt H = (cutState S mt p H).1 := by
  let S := Lfzk.Fork.Transcript.setup2 body
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  have hkeyForm : ∀ p : Prefix (D := D) (C := Coin) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := rounds),
      S.key (parent (Msg₂ := Msg₂) (nl₂ := nl₂)
        (w₂ := rounds₂) p) = p.1.1 := by
    intro p
    exact Lfzk.LigeroPairGeometryTwoSide.key_parent
      (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p
  have hkeyOut : ∀ out, S.keyOut out = (rootOf₁ out, rootOf₂ out) := by
    intro out
    rfl
  exact context_eq_output_cutState_fst S rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ hkeyForm hkeyOut mt H


end Lfzk.Fork.CutContext
