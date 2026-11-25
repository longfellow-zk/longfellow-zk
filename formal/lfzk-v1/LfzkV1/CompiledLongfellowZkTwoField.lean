import LfzkV1.CompiledLongfellowZk
import LfzkV1.ZkTwoTape
import LfzkV1.Mac

/-! Shared proof-building primitives and the real two-field experiment.

The hash proof uses both roots. The signature proof also uses the completed
hash proof. The two-field observer sees the tags, both proofs, all challenge
functions, and two independent typed Merkle oracles.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.CompiledLongfellowZkTwoField

open Merkle Merkle.MH LigeroFamily LigeroFamily.ZeroKnowledge
open LfzkV1.ZkAdaptiveV1 LfzkV1.CompiledLongfellowZk LfzkV1.ZkTwoTape LfzkV1.Mac

/-! ## The MAC tag as a translate of the blind -/

section Tag

variable {Fmac : Type} [Field Fmac] {nblk : ℕ}

/-- `mac_ap ↦ av · msg + mac_ap`, a bijection for every `av` and `msg` (`compute_mac` is
`gf2_128_mul(av, msg) ^ ap`). -/
def tagEquiv (av : Fmac) (msg : Fin nblk → Fmac) : (Fin nblk → Fmac) ≃ (Fin nblk → Fmac) where
  toFun ap := macTag av ap msg
  invFun tg := fun j => tg j - av * msg j
  left_inv ap := by funext j; simp [macTag_apply]
  right_inv tg := by funext j; simp [macTag_apply]

@[simp] theorem tagEquiv_apply (av : Fmac) (msg ap : Fin nblk → Fmac) :
    tagEquiv av msg ap = macTag av ap msg := rfl

end Tag

/-! ## One side's public protocol data -/

/-- The public data of one side: the V1 code, the Merkle codec, the Ligero challenge decoders, the
sumcheck front end and the Ligero hash points. -/
structure Side (F : Type) [Field F] (r w n nw nq reps : ℕ) (E : Type)
    (Salt D Enc Coin LQ Ctx Wit B Tr RO : Type) where
  C : MultiplicativeCode F r w n
  Cod : Codec Salt (Col F nw nq reps) D Enc
  dec₁ : Coin → Ligero.V1.Challenge F nw nq reps E
  dec₂ : Coin → QuerySet n r
  FE : Frontend F nw nq w E Ctx Wit B Tr RO
  pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ

section Pieces

variable {F E : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
variable {r w n nw nq reps : ℕ}
variable {Salt D Enc Coin LQ Ctx Wit B Tr RO : Type}
variable [DecidableEq Enc] [Inhabited D] [DecidableEq LQ]

/-- The commitment's labels and seen-list on its own lazy tape. -/
noncomputable def commitOut (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (nonce : Fin n → Salt) (L : Fin n → Col F nw nq reps) {T : ℕ} (τ : Fin T → D) :
    (ℕ → D) × List Enc :=
  ((RandomOracle.lazyRun τ default (commitPass Cod n nonce L (2 * n - 1) fun _ => default) []).1,
   (RandomOracle.lazyRun τ default (commitPass Cod n nonce L (2 * n - 1) fun _ => default) []).2.1)

/-- **One side's real proof**, at commitment labels `vals` and context `κ`. -/
noncomputable def realProof {C : MultiplicativeCode F r w n}
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps E) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w E Ctx Wit B Tr RO) (κ : Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit)
    (ρ : Tape C nw nq reps) (b : B) (nonce : Fin n → Salt) (Gr : RO) (Gl : LQ → Coin)
    (vals : ℕ → D) : LProof F r w n nw nq reps Salt D Tr Coin :=
  let t := FE.transmit wit Gr κ b
  let c := Gl (pts.first κ t)
  let resp := v1Resp (FE.stmt Gr κ t) (FE.msgs wit b) ρ (dec₁ c)
  let i := Gl (pts.second κ t c resp)
  ⟨vals 1, t, c, resp, i, dec₂ i,
    { nonce := fun j => nonce j.val, frontierValue := fun v => vals v.val },
    openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i)⟩

/-- **One side's simulated proof**, at commitment labels `vals` and context `κ`. -/
noncomputable def simProof {C : MultiplicativeCode F r w n}
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps E) (dec₂ : Coin → QuerySet n r)
    (stmt : RO → Ctx → Tr → ConstraintSystem F nw nq w E) (κ : Ctx)
    (ρ' : Tape C nw nq reps) (t : Tr) (c i : Coin) (Gr : RO) (nonce : Fin n → Salt)
    (vals : ℕ → D) : LProof F r w n nw nq reps Salt D Tr Coin :=
  ⟨vals 1, t, c,
    simResp (stmt Gr κ t) (dec₂ i) (dec₁ c) ρ', i, dec₂ i,
    { nonce := fun j => nonce j.val, frontierValue := fun v => vals v.val },
    openSchemeOracle (v1Oracle 0 ρ') (dec₂ i)⟩

/-- The simulator's programmed Ligero oracle for a simulated proof `pf` at context `κ`. -/
noncomputable def simOracle (κ : Ctx) (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ)
    (G₀ : LQ → Coin) (pf : LProof F r w n nw nq reps Salt D Tr Coin) : LQ → Coin :=
  progAt G₀ (pts.first κ pf.transcript) pf.rawChallenge
    (pts.second κ pf.transcript pf.rawChallenge pf.response) pf.rawQuery

end Pieces

/-! ## The two-field experiments -/

section TwoField

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [DecidableEq Enc₁] [DecidableEq Enc₂] [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] {nblk : ℕ}

/-- The tags. -/
abbrev Tag (Fmac : Type) (nblk : ℕ) := Fin nblk → Fmac

/-- **The two-field proof**: the tags and both compiled Longfellow proofs. -/
abbrev TwoProof (F₁ : Type) [Field F₁] (r₁ w₁ n₁ nw₁ nq₁ reps₁ : ℕ) (F₂ : Type) [Field F₂]
    (r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ) (Salt D Tr₁ Tr₂ Coin₁ Coin₂ Fmac : Type) (nblk : ℕ) :=
  Tag Fmac nblk × LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ ×
    LProof F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ Salt D Tr₂ Coin₂

/-- **The challenge oracles**: `av`'s, then each side's round and Ligero oracles. -/
abbrev TwoOracles (D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂ : Type) :=
  (D × D → Fmac) × RO₁ × (LQ₁ → Coin₁) × RO₂ × (LQ₂ → Coin₂)

/-- **A two-field distinguisher**: it receives the proof and every challenge oracle, and makes at
most `f` queries to the two Merkle oracles, interleaved as it likes. -/
abbrev TwoDistinguisher (F₁ : Type) [Field F₁] (r₁ w₁ n₁ nw₁ nq₁ reps₁ : ℕ) (F₂ : Type) [Field F₂]
    (r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ)
    (Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac : Type) (nblk : ℕ) (V : Type)
    (f : ℕ) :=
  TwoProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ Salt D Tr₁ Tr₂ Coin₁ Coin₂ Fmac nblk →
    TwoOracles D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂ → RandomOracle.Tree (Enc₁ ⊕ Enc₂) D V f

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

/-- Side 1's context as a function of its root, at side 2's root `root₂` and blinds `ap`: the tags
are the honest ones at `av = Gav (root₁, root₂)`. -/
def ctxOf₁ (ap : Tag Fmac nblk) (Gav : D × D → Fmac) (root₂ : D) : D → Ctx₁ :=
  fun root₁ => ctx₁ root₁ root₂ (Gav (root₁, root₂)) (macTag (Gav (root₁, root₂)) ap msg)

/-- Side 2's context as a function of its root, after side 1's proof `pf₁`, honest tags. -/
def ctxOf₂ (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (pf₁ : LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁) : D → Ctx₂ :=
  fun root₂ => ctx₂ pf₁.root root₂ (Gav (pf₁.root, root₂))
    (macTag (Gav (pf₁.root, root₂)) ap msg) pf₁

/-- Real side coins: the V1 tape, the blinders, the Merkle coins, the round oracle, the Ligero
challenge oracle. -/
abbrev RealCoins {F : Type} [Field F] {r w n : ℕ} (C : MultiplicativeCode F r w n)
    (nw nq reps : ℕ) (B : Type) (T : ℕ) (Salt D RO LQ Coin : Type) :=
  Tape C nw nq reps × B × HidingSample n T Salt D × RO × (LQ → Coin)

variable {T₁ T₂ f : ℕ}
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f)

/-- **The real two-field run at fixed coins.**  Both commitments are made on their own lazy tapes;
`av` is read at the two roots; side 1 is proved at context `(root₁, root₂, av, tags)`; side 2
after it; the distinguisher runs against both Merkle oracles from the commitments' seen-lists. -/
noncomputable def realCore2 (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁ : Tape P₁.C nw₁ nq₁ reps₁) (b₁ : B₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (Gl₁ : LQ₁ → Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) : V :=
  let O₁ := commitOut P₁.Cod hs₁.1 (colsOf (v1Oracle (P₁.FE.msgs (wit₁ ap) b₁) ρ₁)) hs₁.2
  let O₂ := commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2
  let pf₁ := realProof P₁.dec₁ P₁.dec₂ P₁.FE (ctxOf₁ ctx₁ msg ap Gav (O₂.1 1) (O₁.1 1)) P₁.pts
    (wit₁ ap) ρ₁ b₁ hs₁.1 Gr₁ Gl₁ O₁.1
  let pf₂ := realProof P₂.dec₁ P₂.dec₂ P₂.FE (ctxOf₂ ctx₂ msg ap Gav pf₁ (O₂.1 1)) P₂.pts
    (wit₂ ap) ρ₂ b₂ hs₂.1 Gr₂ Gl₂ O₂.1
  lazyRun2 hs₁.2 hs₂.2 default
    (dist (macTag (Gav (pf₁.root, O₂.1 1)) ap msg, pf₁, pf₂) (Gav, Gr₁, Gl₁, Gr₂, Gl₂)) O₁.2 O₂.2

/-- **The real two-field experiment.**  Coins: the MAC blinds `mac_ap`, `av`'s oracle and each
side's real coins. -/
noncomputable def realExp2 :
    Tag Fmac nblk × (D × D → Fmac) × RealCoins P₁.C nw₁ nq₁ reps₁ B₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      RealCoins P₂.C nw₂ nq₂ reps₂ B₂ T₂ Salt D RO₂ LQ₂ Coin₂ → V :=
  fun ω => realCore2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω.1 ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2

end TwoField
end LfzkV1.CompiledLongfellowZkTwoField
