import Lfzk.LigeroPairGeometryTwoSide
import Bcs.TwoPointContext

/-! The committed cut trace and nonterminal answers form a local V1 state. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.V1StrongV7TwoSideCutContext

open Lfzk.LigeroPairGeometryTwoSide
open scoped Classical

variable {Enc D Coin X Other F Msg₂ Out : Type}
  [DecidableEq Enc] [Inhabited D] [DecidableEq D]
  [Inhabited Other]
  {nl nl₂ block dblock r tA N Lsch TM : ℕ}
  {rounds rounds₂ : ℕ → ℕ}

abbrev State := ((D × D) × List (Enc × D)) ×
  (OutsideTerminal (D := D) (C := Coin) (X := X)
    (Other := Other) (F := F) (Msg₂ := Msg₂)
    (nl := nl) (nl₂ := nl₂) (block := block)
    (dblock := dblock) (r := r) (w := rounds) (w₂ := rounds₂) → Coin)

/-- For each potential V1 parent, retain the committed cut trace of its
key and every oracle answer outside the first side's terminal roles. -/
noncomputable def cutState
    (S : Bcs.TotalOracleCommit.Setup Enc D
      (Point (D := D) (C := Coin) (X := X) (Other := Other) (F := F)
        (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂) (block := block)
        (dblock := dblock) (r := r) (w := rounds) (w₂ := rounds₂))
      Coin Out (D × D) tA N Lsch)
    (mt : Fin TM → D)
    (p : Prefix (D := D) (C := Coin) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := rounds))
    (H : Point (D := D) (C := Coin) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r)
      (w := rounds) (w₂ := rounds₂) → Coin) :
    State (Enc := Enc) (D := D) (Coin := Coin) (X := X)
      (Other := Other) (F := F) (Msg₂ := Msg₂)
      (nl := nl) (nl₂ := nl₂) (block := block)
      (dblock := dblock) (r := r) (rounds := rounds) (rounds₂ := rounds₂) :=
  ((S.atOracle H).ctxAt mt Bcs.TotalOracleCommit.Setup.emptyTape
      (S.key (parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p)),
    outsideTerminal H)

/-- The selected commitment's cut trace is independent of both selected
terminal answers, even if the prover asked the query point first.  Other
terminal answers remain present through the cut trace. -/
theorem cutState_off
    (S : Bcs.TotalOracleCommit.Setup Enc D
      (Point (D := D) (C := Coin) (X := X) (Other := Other) (F := F)
        (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂) (block := block)
        (dblock := dblock) (r := r) (w := rounds) (w₂ := rounds₂))
      Coin Out (D × D) tA N Lsch)
    (hkey : ∀ p response,
      S.key (parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p) =
        S.key (child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p response))
    (mt : Fin TM → D)
    (p : Prefix (D := D) (C := Coin) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := rounds))
    (response : Lfzk.LigeroTranscriptInputs.ResponsePayload F block dblock r)
    (H H' : Point (D := D) (C := Coin) (X := X)
      (Other := Other) (F := F) (Msg₂ := Msg₂)
      (nl := nl) (nl₂ := nl₂) (block := block)
      (dblock := dblock) (r := r) (w := rounds) (w₂ := rounds₂) → Coin)
    (h : ∀ z,
      z ≠ parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p →
      z ≠ child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p response →
      H z = H' z) :
    cutState S mt p H = cutState S mt p H' := by
  apply Prod.ext
  · exact (S.ctxAt_off_two mt H H'
      (parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p)
      (child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p response)
      (hkey p response) h).symm
  · exact outsideTerminal_off p response H H' h

/-- On the verifier's selected commitment, the first component of the
local state is exactly the compiled setup's commitment context. -/
theorem context_eq_cutState_fst
    (S : Bcs.TotalOracleCommit.Setup Enc D
      (Point (D := D) (C := Coin) (X := X) (Other := Other) (F := F)
        (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂) (block := block)
        (dblock := dblock) (r := r) (w := rounds) (w₂ := rounds₂))
      Coin Out (D × D) tA N Lsch)
    (mt : Fin TM → D)
    (H : Point (D := D) (C := Coin) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r)
      (w := rounds) (w₂ := rounds₂) → Coin)
    (p : Prefix (D := D) (C := Coin) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := rounds))
    (hkeySelected :
      S.key (parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p) =
        S.keyOut (S.proof mt H)) :
    S.context mt H = (cutState S mt p H).1 := by
  unfold Bcs.TotalOracleCommit.Setup.context cutState
  exact congrArg (fun key => (S.atOracle H).ctxAt mt
    Bcs.TotalOracleCommit.Setup.emptyTape key) hkeySelected.symm

/-- For a deployed proof's own root pair and message schedule, the local
state is the same cut trace consumed by the compiled side. -/
theorem context_eq_output_cutState_fst
    (S : Bcs.TotalOracleCommit.Setup Enc D
      (Point (D := D) (C := Coin) (X := X) (Other := Other) (F := F)
        (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂) (block := block)
        (dblock := dblock) (r := r) (w := rounds) (w₂ := rounds₂))
      Coin Out (D × D) tA N Lsch)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin)
    (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → FirstMessage (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (hkeyForm : ∀ p : Prefix (D := D) (C := Coin) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := rounds),
      S.key (parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p) = p.1.1)
    (hkeyOut : ∀ out, S.keyOut out = (rootOf₁ out, rootOf₂ out))
    (mt : Fin TM → D)
    (H : Point (D := D) (C := Coin) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r)
      (w := rounds) (w₂ := rounds₂) → Coin) :
    let out := S.proof mt H
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := nl) (w := rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf out)
      (msgOf₁ out)
    S.context mt H = (cutState S mt p H).1 := by
  let out := S.proof mt H
  let p := Lfzk.LigeroPairGeometry.ofMessages
    (nl := nl) (w := rounds)
    (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf out)
    (msgOf₁ out)
  have hp : p.1.1 = (rootOf₁ out, rootOf₂ out) := rfl
  have hk : S.key (parent (Msg₂ := Msg₂) (nl₂ := nl₂)
      (w₂ := rounds₂) p) = S.keyOut out := by
    rw [hkeyForm p, hkeyOut out, hp]
  exact context_eq_cutState_fst S mt H p hk

/-- The deployed two-field setup's selected cut is exactly the first
component of the parent-indexed local state. -/
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
    let S := Lfzk.NizkDeployedHashTwoField.setup2 body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let out := S.proof mt H
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := nl) (w := rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf
        rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
    S.context mt H = (cutState S mt p H).1 := by
  let S := Lfzk.NizkDeployedHashTwoField.setup2 body
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

end Lfzk.V1StrongV7TwoSideCutContext
