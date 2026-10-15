import Lfzk.CompiledLongfellowZk
import Lfzk.ZkTwoTape
import Lfzk.Mac

/-!
# Zero knowledge of the two-field mdoc proof (hash over GF(2^128), signature over P-256)

`mdoc_zk`'s prover (`rust/applications/mdoc_zk/runtime/src/prover.rs`) runs two compiled
Longfellow arguments on **one** transcript:

1. commit the hash circuit's witness (root `root₁`), then the signature circuit's (root `root₂`);
2. draw the MAC multiplier `av := tp.u128()` from the transcript — after both commitments;
3. compute the tags `macs = push_modern_macs(issuer_sig_e, device_pk, av, mac_ap)`:
   `tag_j = av · msg_j + mac_ap_j` in GF(2^128) for the six 128-bit blocks `msg` of
   `(issuer_sig_e, device_pk.x, device_pk.y)` (`circuits_mac::concrete::compute_tag`), with the
   blinds `mac_ap : [[u128; 2]; 3]` drawn by the prover (`generate_mac_ap`) and placed in **both**
   witnesses;
4. prove the hash circuit at public input `(…, macs, av)`, then the signature circuit, both on the
   continuing transcript.

`twofield_zk` says the whole proof — tags, both compiled Longfellow proofs — is
`(ε₁ + ε₂)`-close to a witness-free simulation, where `εₖ` is side `k`'s opening-hiding term
(`compiled_longfellow_zk`), against every distinguisher that sees the proof and every challenge
oracle and makes at most `f` queries to the two Merkle oracles (interleaved, adaptively).
**The MAC costs nothing**: once both sides are simulated, the tags enter only as public data, and
`mac_ap ↦ av·msg + mac_ap` is a bijection for every `av` (`tagEquiv`).

## The hybrids

| step | cost | how |
|---|---|---|
| simulate side 1 (hash) | `ε₁` | `compiled_longfellow_zk` at side 1, with side 2, `av`, the MAC and the distinguisher inside its distinguisher (`ZkTwoTape.proj₁`) and side 2's root in its context |
| simulate side 2 (signature) | `ε₂` | `compiled_longfellow_zk` at side 2, with the simulated side 1 inside (`ZkTwoTape.proj₂`); side 1's simulated proof is a function of side 2's root, through `av` and the context |
| sample the tags | **0** | `tagEquiv`: the simulated commitments are tag-independent, so `av` is fixed when `mac_ap` is reparametrised |

The order is forced for the same reason as within one side: the side-1 statement depends on
`root₂` (through `av`, which is absorbed before either sumcheck), and the tags depend on both
roots — they can be resampled only after both commitments are witness-free.

## The model

Everything in `Lfzk.CompiledLongfellowZk` ("The model"), plus:

* **Independent oracles per role.**  The transcript hash is one random oracle on prefixes; side 1's
  prefixes, `av`'s prefix and side 2's prefixes are distinct (side 2's prefixes extend the whole of
  side 1's proof), so it splits exactly into the independent oracles `Gav`, `Gr₁`, `Gl₁`, `Gr₂`,
  `Gl₂`.  The two Merkle trees are modelled as **two independent** lazily sampled oracles
  (`ZkTwoTape.lazyRun2`): the deployed trees both hash raw `nonce ‖ column` and `digest ‖ digest`
  strings with SHA-256 with no domain separation between the trees, so this is an idealisation.
* **Validity** (`hvalid₁`, `hvalid₂`): the honest witnesses — which contain the blinds `mac_ap` —
  are valid for every public input that carries the honestly computed tag.  This is the circuits'
  completeness for the MAC and the rest of the public input, as `Frontend.Valid` asks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Lfzk.CompiledLongfellowZkTwoField

open Merkle Merkle.MH LigeroFamily LigeroFamily.ZeroKnowledge
open Lfzk.ZkAdaptiveV1 Lfzk.CompiledLongfellowZk Lfzk.ZkTwoTape Lfzk.Mac

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
    v1Resp (stmt Gr κ t) (referenceMessages (stmt Gr κ t))
      (coreShift 0 (referenceMessages (stmt Gr κ t)) (dec₂ i) ρ') (dec₁ c), i, dec₂ i,
    { nonce := fun j => nonce j.val, frontierValue := fun v => vals v.val },
    openSchemeOracle (v1Oracle 0 ρ') (dec₂ i)⟩

/-- The simulator's programmed Ligero oracle for a simulated proof `pf` at context `κ`. -/
noncomputable def simOracle (κ : Ctx) (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ)
    (G₀ : LQ → Coin) (pf : LProof F r w n nw nq reps Salt D Tr Coin) : LQ → Coin :=
  progAt G₀ (pts.first κ pf.transcript) pf.rawChallenge
    (pts.second κ pf.transcript pf.rawChallenge pf.response) pf.rawQuery

/-- The simulated commitment's leaves. -/
noncomputable def simLeaves {C : MultiplicativeCode F r w n} (dec₂ : Coin → QuerySet n r)
    (ρ' : Tape C nw nq reps) (i : Coin) : Fin n → Col F nw nq reps :=
  leavesOfOpen (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i))

/-- The single-side real experiment, at fixed coins, as "commit, then run the distinguisher on the
commitment's seen-list". -/
theorem realCore_eq {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps E) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w E Ctx Wit B Tr RO) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit) {T f : ℕ}
    {V : Type} (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ : Tape C nw nq reps) (b : B) (hs : HidingSample n T Salt D) (Gr : RO) (Gl : LQ → Coin) :
    realCore Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr Gl
      = (RandomOracle.lazyRun hs.2 default
          (dist (realProof dec₁ dec₂ FE
            (ctx ((commitOut Cod hs.1 (colsOf (v1Oracle (FE.msgs wit b) ρ)) hs.2).1 1)) pts wit ρ b
            hs.1 Gr Gl (commitOut Cod hs.1 (colsOf (v1Oracle (FE.msgs wit b) ρ)) hs.2).1) Gr Gl)
          (commitOut Cod hs.1 (colsOf (v1Oracle (FE.msgs wit b) ρ)) hs.2).2).1 := by
  simp only [realCore, realRun, commitOut]
  rw [RandomOracle.lazyRun_bind]
  rfl

/-- The single-side simulated experiment, at fixed coins, in the same form. -/
theorem simCore_eq {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps E) (dec₂ : Coin → QuerySet n r)
    (stmt : RO → Ctx → Tr → ConstraintSystem F nw nq w E) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) {T f : ℕ} {V : Type}
    (dist : Distinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V f)
    (ρ' : Tape C nw nq reps) (t : Tr) (hs : HidingSample n T Salt D) (Gr : RO) (G₀ : LQ → Coin)
    (c i : Coin) :
    simCore Cod dec₁ dec₂ stmt ctx pts dist ρ' t hs Gr G₀ c i
      = (RandomOracle.lazyRun hs.2 default
          (dist (simProof dec₁ dec₂ stmt (ctx ((commitOut Cod hs.1 (simLeaves dec₂ ρ' i) hs.2).1 1))
              ρ' t c i Gr hs.1 (commitOut Cod hs.1 (simLeaves dec₂ ρ' i) hs.2).1) Gr
            (simOracle (ctx ((commitOut Cod hs.1 (simLeaves dec₂ ρ' i) hs.2).1 1)) pts G₀
              (simProof dec₁ dec₂ stmt (ctx ((commitOut Cod hs.1 (simLeaves dec₂ ρ' i) hs.2).1 1))
                ρ' t c i Gr hs.1 (commitOut Cod hs.1 (simLeaves dec₂ ρ' i) hs.2).1)))
          (commitOut Cod hs.1 (simLeaves dec₂ ρ' i) hs.2).2).1 := by
  simp only [simCore, hybExp, openingHidingView, openingHidingRun, commitOut]
  rw [RandomOracle.lazyRun_bind]
  rfl

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

/-- Side 1's context at a fixed tag. -/
def ctxOf₁T (tag : Tag Fmac nblk) (Gav : D × D → Fmac) (root₂ : D) : D → Ctx₁ :=
  fun root₁ => ctx₁ root₁ root₂ (Gav (root₁, root₂)) tag

/-- Side 2's context as a function of its root, after side 1's proof `pf₁`, honest tags. -/
def ctxOf₂ (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (pf₁ : LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁) : D → Ctx₂ :=
  fun root₂ => ctx₂ pf₁.root root₂ (Gav (pf₁.root, root₂))
    (macTag (Gav (pf₁.root, root₂)) ap msg) pf₁

/-- Side 2's context at a fixed tag. -/
def ctxOf₂T (tag : Tag Fmac nblk) (Gav : D × D → Fmac)
    (pf₁ : LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁) : D → Ctx₂ :=
  fun root₂ => ctx₂ pf₁.root root₂ (Gav (pf₁.root, root₂)) tag pf₁

/-- Real side coins: the V1 tape, the blinders, the Merkle coins, the round oracle, the Ligero
challenge oracle. -/
abbrev RealCoins {F : Type} [Field F] {r w n : ℕ} (C : MultiplicativeCode F r w n)
    (nw nq reps : ℕ) (B : Type) (T : ℕ) (Salt D RO LQ Coin : Type) :=
  Tape C nw nq reps × B × HidingSample n T Salt D × RO × (LQ → Coin)

/-- Simulated side coins: a V1 tape, a transmission, the Merkle coins, the round oracle, a Ligero
challenge oracle and the two raw challenges. -/
abbrev SimCoins {F : Type} [Field F] {r w n : ℕ} (C : MultiplicativeCode F r w n)
    (nw nq reps : ℕ) (Tr : Type) (T : ℕ) (Salt D RO LQ Coin : Type) :=
  Tape C nw nq reps × Tr × HidingSample n T Salt D × RO × (LQ → Coin) × Coin × Coin

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

/-- Hybrid: side 1 simulated (at the honest tags), side 2 real. -/
noncomputable def midCore2 (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) : V :=
  let O₁ := commitOut P₁.Cod hs₁.1 (simLeaves P₁.dec₂ ρ₁' i₁) hs₁.2
  let O₂ := commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2
  let pf₁ := simProof P₁.dec₁ P₁.dec₂ P₁.FE.stmt (ctxOf₁ ctx₁ msg ap Gav (O₂.1 1) (O₁.1 1)) ρ₁' t₁
    c₁ i₁ Gr₁ hs₁.1 O₁.1
  let pf₂ := realProof P₂.dec₁ P₂.dec₂ P₂.FE (ctxOf₂ ctx₂ msg ap Gav pf₁ (O₂.1 1)) P₂.pts
    (wit₂ ap) ρ₂ b₂ hs₂.1 Gr₂ Gl₂ O₂.1
  lazyRun2 hs₁.2 hs₂.2 default
    (dist (macTag (Gav (pf₁.root, O₂.1 1)) ap msg, pf₁, pf₂)
      (Gav, Gr₁, simOracle (ctxOf₁ ctx₁ msg ap Gav (O₂.1 1) (O₁.1 1)) P₁.pts G₀₁ pf₁, Gr₂, Gl₂))
    O₁.2 O₂.2

/-- Both sides simulated; the tags are `tagOf root₁ root₂`. -/
noncomputable def bothCore2 (tagOf : D → D → Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂' : Tape P₂.C nw₂ nq₂ reps₂) (t₂ : Tr₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (G₀₂ : LQ₂ → Coin₂) (c₂ i₂ : Coin₂) : V :=
  let O₁ := commitOut P₁.Cod hs₁.1 (simLeaves P₁.dec₂ ρ₁' i₁) hs₁.2
  let O₂ := commitOut P₂.Cod hs₂.1 (simLeaves P₂.dec₂ ρ₂' i₂) hs₂.2
  let tag := tagOf (O₁.1 1) (O₂.1 1)
  let pf₁ := simProof P₁.dec₁ P₁.dec₂ P₁.FE.stmt (ctxOf₁T ctx₁ tag Gav (O₂.1 1) (O₁.1 1)) ρ₁' t₁
    c₁ i₁ Gr₁ hs₁.1 O₁.1
  let pf₂ := simProof P₂.dec₁ P₂.dec₂ P₂.FE.stmt (ctxOf₂T ctx₂ tag Gav pf₁ (O₂.1 1)) ρ₂' t₂
    c₂ i₂ Gr₂ hs₂.1 O₂.1
  lazyRun2 hs₁.2 hs₂.2 default
    (dist (tag, pf₁, pf₂)
      (Gav, Gr₁, simOracle (ctxOf₁T ctx₁ tag Gav (O₂.1 1) (O₁.1 1)) P₁.pts G₀₁ pf₁, Gr₂,
        simOracle (ctxOf₂T ctx₂ tag Gav pf₁ (O₂.1 1)) P₂.pts G₀₂ pf₂)) O₁.2 O₂.2

/-- **The real two-field experiment.**  Coins: the MAC blinds `mac_ap`, `av`'s oracle and each
side's real coins. -/
noncomputable def realExp2 :
    Tag Fmac nblk × (D × D → Fmac) × RealCoins P₁.C nw₁ nq₁ reps₁ B₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      RealCoins P₂.C nw₂ nq₂ reps₂ B₂ T₂ Salt D RO₂ LQ₂ Coin₂ → V :=
  fun ω => realCore2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω.1 ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2

/-- **The simulated two-field experiment.**  It never sees a witness or the blinds: the tags are a
uniform coin, and each side is its compiled Longfellow simulator at the public data. -/
noncomputable def simExp2 :
    Tag Fmac nblk × (D × D → Fmac) × SimCoins P₁.C nw₁ nq₁ reps₁ Tr₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      SimCoins P₂.C nw₂ nq₂ reps₂ Tr₂ T₂ Salt D RO₂ LQ₂ Coin₂ → V :=
  fun ω => bothCore2 P₁ P₂ ctx₁ ctx₂ dist (fun _ _ => ω.1) ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2.1
    ω.2.2.1.2.2.2.2.2.1 ω.2.2.1.2.2.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2.1
    ω.2.2.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2.2.2

/-! ## The instances each hybrid applies `compiled_longfellow_zk` to -/

/-- Side 1's distinguisher, at side 2's real coins: run side 2 (on its own commitment) and the
two-field distinguisher, answering side 2's Merkle oracle from its tape. -/
noncomputable def distA (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) : Distinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Enc₁ Tr₁ Coin₁ LQ₁ RO₁ V f :=
  fun pf Gr₁ Gl₁ => proj₁ hs₂.2 default
    (dist (macTag (Gav (pf.root,
        (commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2).1 1)) ap msg,
      pf, realProof P₂.dec₁ P₂.dec₂ P₂.FE (ctxOf₂ ctx₂ msg ap Gav pf
          ((commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2).1 1))
        P₂.pts (wit₂ ap) ρ₂ b₂ hs₂.1
        Gr₂ Gl₂ (commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2).1)
      (Gav, Gr₁, Gl₁, Gr₂, Gl₂))
    (commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2).2

/-- The real two-field run is side 1's real experiment against `distA`. -/
theorem realCore2_eq (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁ : Tape P₁.C nw₁ nq₁ reps₁) (b₁ : B₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (Gl₁ : LQ₁ → Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) :
    realCore2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ap Gav ρ₁ b₁ hs₁ Gr₁ Gl₁ ρ₂ b₂ hs₂ Gr₂ Gl₂
      = realCore P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE
          (ctxOf₁ ctx₁ msg ap Gav
            ((commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2).1 1))
          P₁.pts (wit₁ ap) (distA P₂ ctx₂ wit₂ msg dist ap Gav ρ₂ b₂ hs₂ Gr₂ Gl₂)
          ρ₁ b₁ hs₁ Gr₁ Gl₁ := by
  rw [realCore_eq]
  unfold distA
  rw [lazyRun_proj₁]
  rfl

/-- The side-1-simulated hybrid is side 1's simulated experiment against `distA`. -/
theorem midCore2_eq_sim (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) :
    midCore2 P₁ P₂ ctx₁ ctx₂ wit₂ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁ ρ₂ b₂ hs₂ Gr₂ Gl₂
      = simCore P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE.stmt
          (ctxOf₁ ctx₁ msg ap Gav
            ((commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2).1 1))
          P₁.pts (distA P₂ ctx₂ wit₂ msg dist ap Gav ρ₂ b₂ hs₂ Gr₂ Gl₂)
          ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁ := by
  rw [simCore_eq]
  unfold distA
  rw [lazyRun_proj₁]
  rfl

/-- Side 1's simulated proof as a function of side 2's root. -/
noncomputable def pf₁Of (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (c₁ i₁ : Coin₁) (root₂ : D) : LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ :=
  simProof P₁.dec₁ P₁.dec₂ P₁.FE.stmt
    (ctxOf₁ ctx₁ msg ap Gav root₂ ((commitOut P₁.Cod hs₁.1 (simLeaves P₁.dec₂ ρ₁' i₁) hs₁.2).1 1))
    ρ₁' t₁ c₁ i₁ Gr₁ hs₁.1 (commitOut P₁.Cod hs₁.1 (simLeaves P₁.dec₂ ρ₁' i₁) hs₁.2).1

/-- Side 2's context, at side 1's simulated coins. -/
noncomputable def ctxB (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (c₁ i₁ : Coin₁) : D → Ctx₂ :=
  fun root₂ => ctxOf₂ ctx₂ msg ap Gav (pf₁Of P₁ ctx₁ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁ root₂) root₂

/-- Side 2's distinguisher, at side 1's simulated coins: recompute side 1's simulated proof from
side 2's root, and answer side 1's Merkle oracle from its tape. -/
noncomputable def distB (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁) :
    Distinguisher F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ Salt D Enc₂ Tr₂ Coin₂ LQ₂ RO₂ V f :=
  fun pf Gr₂ Gl₂ => proj₂ hs₁.2 default
    (dist (macTag (Gav ((pf₁Of P₁ ctx₁ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁ pf.root).root, pf.root))
        ap msg, pf₁Of P₁ ctx₁ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁ pf.root, pf)
      (Gav, Gr₁, simOracle (ctxOf₁ ctx₁ msg ap Gav pf.root
          ((commitOut P₁.Cod hs₁.1 (simLeaves P₁.dec₂ ρ₁' i₁) hs₁.2).1 1)) P₁.pts G₀₁
        (pf₁Of P₁ ctx₁ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁ pf.root), Gr₂, Gl₂))
    (commitOut P₁.Cod hs₁.1 (simLeaves P₁.dec₂ ρ₁' i₁) hs₁.2).2

/-- The side-1-simulated hybrid is side 2's real experiment against `distB`. -/
theorem midCore2_eq_real (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) :
    midCore2 P₁ P₂ ctx₁ ctx₂ wit₂ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁ ρ₂ b₂ hs₂ Gr₂ Gl₂
      = realCore P₂.Cod P₂.dec₁ P₂.dec₂ P₂.FE (ctxB P₁ ctx₁ ctx₂ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁)
          P₂.pts (wit₂ ap) (distB P₁ ctx₁ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁)
          ρ₂ b₂ hs₂ Gr₂ Gl₂ := by
  rw [realCore_eq]
  unfold distB
  rw [lazyRun_proj₂]
  rfl

/-- Side 2's simulated experiment against `distB` is the both-simulated hybrid at the honest
tags. -/
theorem simB_eq_both (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂' : Tape P₂.C nw₂ nq₂ reps₂) (t₂ : Tr₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (G₀₂ : LQ₂ → Coin₂) (c₂ i₂ : Coin₂) :
    simCore P₂.Cod P₂.dec₁ P₂.dec₂ P₂.FE.stmt (ctxB P₁ ctx₁ ctx₂ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁)
        P₂.pts (distB P₁ ctx₁ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁) ρ₂' t₂ hs₂ Gr₂ G₀₂ c₂ i₂
      = bothCore2 P₁ P₂ ctx₁ ctx₂ dist (fun r₁ r₂ => macTag (Gav (r₁, r₂)) ap msg) Gav
          ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁ ρ₂' t₂ hs₂ Gr₂ G₀₂ c₂ i₂ := by
  rw [simCore_eq]
  unfold distB
  rw [lazyRun_proj₂]
  rfl

/-- The side-1-simulated hybrid, on its coin space. -/
noncomputable def midExp2 :
    Tag Fmac nblk × (D × D → Fmac) × SimCoins P₁.C nw₁ nq₁ reps₁ Tr₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      RealCoins P₂.C nw₂ nq₂ reps₂ B₂ T₂ Salt D RO₂ LQ₂ Coin₂ → V :=
  fun ω => midCore2 P₁ P₂ ctx₁ ctx₂ wit₂ msg dist ω.1 ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2.1
    ω.2.2.1.2.2.2.2.2.1 ω.2.2.1.2.2.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2

/-- Both sides simulated, at the honest tags `av · msg + mac_ap`. -/
noncomputable def bothExp2 :
    Tag Fmac nblk × (D × D → Fmac) × SimCoins P₁.C nw₁ nq₁ reps₁ Tr₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      SimCoins P₂.C nw₂ nq₂ reps₂ Tr₂ T₂ Salt D RO₂ LQ₂ Coin₂ → V :=
  fun ω => bothCore2 P₁ P₂ ctx₁ ctx₂ dist (fun r₁ r₂ => macTag (ω.2.1 (r₁, r₂)) ω.1 msg) ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2.1
    ω.2.2.1.2.2.2.2.2.1 ω.2.2.1.2.2.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2.1
    ω.2.2.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2.2.2

end TwoField

/-! ## Sample-space bookkeeping -/

/-- Side 1's coins inside. -/
def eA (A G X Y : Type) : (A × G × Y) × X ≃ A × G × X × Y where
  toFun p := (p.1.1, p.1.2.1, p.2, p.1.2.2)
  invFun ω := ((ω.1, ω.2.1, ω.2.2.2), ω.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Side 2's coins inside. -/
def eB (A G X Y : Type) : (A × G × X) × Y ≃ A × G × X × Y where
  toFun p := (p.1.1, p.1.2.1, p.1.2.2, p.2)
  invFun ω := ((ω.1, ω.2.1, ω.2.2.1), ω.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The blinds (resp. the tags) inside. -/
def eC (A G X Y : Type) : (G × X × Y) × A ≃ A × G × X × Y where
  toFun p := (p.2, p.1.1, p.1.2.1, p.1.2.2)
  invFun ω := ((ω.2.1, ω.2.2.1, ω.2.2.2), ω.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## The theorem -/

section Theorem

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [DecidableEq Enc₁] [DecidableEq Enc₂] [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
variable [Fintype Coin₁] [DecidableEq Coin₁] [Nonempty Coin₁] [Fintype Coin₂] [DecidableEq Coin₂]
  [Nonempty Coin₂] [Fintype LQ₁] [Fintype LQ₂] [Fintype B₁] [Fintype B₂] [Fintype Tr₁]
  [Fintype Tr₂] [Fintype RO₁] [Fintype RO₂] [DecidableEq V]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

/--
**Zero knowledge of the two-field mdoc proof at Ligero V1.**

For every pair of witness maps `wit₁ wit₂` (the witnesses as functions of the MAC blinds
`mac_ap`) that are valid at every public input carrying the honest tags (`hvalid₁`, `hvalid₂`),
and every distinguisher that receives the tags, both compiled proofs and every challenge oracle and
makes at most `f` queries to the two Merkle oracles, the real two-field experiment is
`(ε₁ + ε₂)`-close to the witness-free `simExp2`, where `εₖ` is side `k`'s opening-hiding term at
`nₖ` columns, `nₖ − rₖ` of them unopened.
-/
theorem twofield_zk (hinj₁ : P₁.Cod.Inj) (hinj₂ : P₂.Cod.Inj)
    (hvalid₁ : ∀ ap root₁ root₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ root₁ root₂ av (macTag av ap msg)))
    (hvalid₂ : ∀ ap root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ ap) (ctx₂ root₁ root₂ av (macTag av ap msg) pf₁))
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) {T₁ T₂ f : ℕ} (hT₁ : 2 * n₁ - 1 + f ≤ T₁)
    (hT₂ : 2 * n₂ - 1 + f ≤ T₂)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f) :
    StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₁ f T₁ (n₁ - r₁)
          (Fintype.card (HidingSample n₁ T₁ Salt D)) +
        ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₂ f T₂ (n₂ - r₂)
          (Fintype.card (HidingSample n₂ T₂ Salt D)))
      (realExp2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (simExp2 P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist) := by
  classical
  -- Step A: simulate side 1
  have sA : StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₁ f T₁ (n₁ - r₁)
        (Fintype.card (HidingSample n₁ T₁ Salt D)))
      (realExp2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (midExp2 P₁ P₂ ctx₁ ctx₂ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist) := by
    refine statClose_mix_equiv (CompiledLigeroZk.openingEps_nonneg _ _ _ _ _ _ _) _ _ (eA _ _ _ _) (eA _ _ _ _) ?_
    rintro ⟨ap, Gav, ρ₂, b₂, hs₂, Gr₂, Gl₂⟩
    have h := compiled_longfellow_zk P₁.C P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE
      (ctxOf₁ ctx₁ msg ap Gav
        ((commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2).1 1))
      P₁.pts (wit₁ ap) hinj₁ (fun root => hvalid₁ ap root _ _) (n₁ - r₁)
      (fun q => (unopened_card q).le) hn₁ hT₁
      (distA P₂ ctx₂ wit₂ msg dist ap Gav ρ₂ b₂ hs₂ Gr₂ Gl₂)
    have e1 : (fun ω₁ => realExp2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist
          (eA _ _ _ _ ((ap, Gav, ρ₂, b₂, hs₂, Gr₂, Gl₂), ω₁)))
        = realExp P₁.C P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE
          (ctxOf₁ ctx₁ msg ap Gav
            ((commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2).1 1))
          P₁.pts (wit₁ ap) (T := T₁) (distA P₂ ctx₂ wit₂ msg dist ap Gav ρ₂ b₂ hs₂ Gr₂ Gl₂) :=
      funext fun ω₁ => realCore2_eq P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ap Gav ω₁.1 ω₁.2.1
        ω₁.2.2.1 ω₁.2.2.2.1 ω₁.2.2.2.2 ρ₂ b₂ hs₂ Gr₂ Gl₂
    have e2 : (fun ω₁ => midExp2 P₁ P₂ ctx₁ ctx₂ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist
          (eA _ _ _ _ ((ap, Gav, ρ₂, b₂, hs₂, Gr₂, Gl₂), ω₁)))
        = simExp P₁.C P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE.stmt
          (ctxOf₁ ctx₁ msg ap Gav
            ((commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2).1 1))
          P₁.pts (T := T₁) (distA P₂ ctx₂ wit₂ msg dist ap Gav ρ₂ b₂ hs₂ Gr₂ Gl₂) :=
      funext fun ω₁ => midCore2_eq_sim P₁ P₂ ctx₁ ctx₂ wit₂ msg dist ap Gav ω₁.1 ω₁.2.1
        ω₁.2.2.1 ω₁.2.2.2.1 ω₁.2.2.2.2.1 ω₁.2.2.2.2.2.1 ω₁.2.2.2.2.2.2 ρ₂ b₂ hs₂ Gr₂ Gl₂
    rw [e1, e2]
    exact h
  -- Step B: simulate side 2
  have sB : StatClose
      (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₂ f T₂ (n₂ - r₂)
        (Fintype.card (HidingSample n₂ T₂ Salt D)))
      (midExp2 P₁ P₂ ctx₁ ctx₂ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (bothExp2 P₁ P₂ ctx₁ ctx₂ msg (T₁ := T₁) (T₂ := T₂) dist) := by
    refine statClose_mix_equiv (CompiledLigeroZk.openingEps_nonneg _ _ _ _ _ _ _) _ _ (eB _ _ _ _) (eB _ _ _ _) ?_
    rintro ⟨ap, Gav, ρ₁', t₁, hs₁, Gr₁, G₀₁, c₁, i₁⟩
    have h := compiled_longfellow_zk P₂.C P₂.Cod P₂.dec₁ P₂.dec₂ P₂.FE
      (ctxB P₁ ctx₁ ctx₂ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁) P₂.pts (wit₂ ap) hinj₂
      (fun root => hvalid₂ ap _ root _ _) (n₂ - r₂) (fun q => (unopened_card q).le) hn₂ hT₂
      (distB P₁ ctx₁ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁)
    have e1 : (fun ω₂ => midExp2 P₁ P₂ ctx₁ ctx₂ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist
          (eB _ _ _ _ ((ap, Gav, ρ₁', t₁, hs₁, Gr₁, G₀₁, c₁, i₁), ω₂)))
        = realExp P₂.C P₂.Cod P₂.dec₁ P₂.dec₂ P₂.FE
          (ctxB P₁ ctx₁ ctx₂ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁) P₂.pts (wit₂ ap) (T := T₂)
          (distB P₁ ctx₁ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁) :=
      funext fun ω₂ => midCore2_eq_real P₁ P₂ ctx₁ ctx₂ wit₂ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁
        c₁ i₁ ω₂.1 ω₂.2.1 ω₂.2.2.1 ω₂.2.2.2.1 ω₂.2.2.2.2
    have e2 : (fun ω₂ => bothExp2 P₁ P₂ ctx₁ ctx₂ msg (T₁ := T₁) (T₂ := T₂) dist
          (eB _ _ _ _ ((ap, Gav, ρ₁', t₁, hs₁, Gr₁, G₀₁, c₁, i₁), ω₂)))
        = simExp P₂.C P₂.Cod P₂.dec₁ P₂.dec₂ P₂.FE.stmt
          (ctxB P₁ ctx₁ ctx₂ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁) P₂.pts (T := T₂)
          (distB P₁ ctx₁ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁) :=
      funext fun ω₂ => (simB_eq_both P₁ P₂ ctx₁ ctx₂ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁
        ω₂.1 ω₂.2.1 ω₂.2.2.1 ω₂.2.2.2.1 ω₂.2.2.2.2.1 ω₂.2.2.2.2.2.1 ω₂.2.2.2.2.2.2).symm
    rw [e1, e2]
    exact h
  -- Step C: the tags are a translate of the blinds
  have sC : StatClose 0 (bothExp2 P₁ P₂ ctx₁ ctx₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (simExp2 P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist) := by
    refine statClose_mix_equiv le_rfl _ _ (eC _ _ _ _) (eC _ _ _ _) ?_
    rintro ⟨Gav, ω₁, ω₂⟩
    exact statClose_of_equiv_pointwise _ _
      (tagEquiv (Gav ((commitOut P₁.Cod ω₁.2.2.1.1 (simLeaves P₁.dec₂ ω₁.1 ω₁.2.2.2.2.2.2)
          ω₁.2.2.1.2).1 1,
        (commitOut P₂.Cod ω₂.2.2.1.1 (simLeaves P₂.dec₂ ω₂.1 ω₂.2.2.2.2.2.2) ω₂.2.2.1.2).1 1)) msg)
      fun _ => rfl
  have h := sA.trans (sB.trans sC)
  simpa using h


/--
**Two-field witness indistinguishability against query-bounded distinguishers.**  For two choices
of witnesses and common value, both valid, the two honest two-field proofs are
`2 · (ε₁ + ε₂)`-close, against every distinguisher that sees the proof and the challenge oracles and
makes at most `f` Merkle-oracle queries.  The common values may differ: the simulation `simExp2`
reads neither the witnesses nor the MAC'd value.  `twofield_zk` is best read as this corollary: its
simulator is not efficient (see `CompiledLongfellowZk.compiled_longfellow_wi`), and the bound grows
with `f`.
-/
theorem twofield_wi (hinj₁ : P₁.Cod.Inj) (hinj₂ : P₂.Cod.Inj)
    {wit₁' : Tag Fmac nblk → Wit₁} {wit₂' : Tag Fmac nblk → Wit₂} {msg' : Fin nblk → Fmac}
    (hvalid₁ : ∀ ap root₁ root₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ root₁ root₂ av (macTag av ap msg)))
    (hvalid₂ : ∀ ap root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ ap) (ctx₂ root₁ root₂ av (macTag av ap msg) pf₁))
    (hvalid₁' : ∀ ap root₁ root₂ av,
      P₁.FE.Valid (wit₁' ap) (ctx₁ root₁ root₂ av (macTag av ap msg')))
    (hvalid₂' : ∀ ap root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂' ap) (ctx₂ root₁ root₂ av (macTag av ap msg') pf₁))
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) {T₁ T₂ f : ℕ} (hT₁ : 2 * n₁ - 1 + f ≤ T₁)
    (hT₂ : 2 * n₂ - 1 + f ≤ T₂)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f) :
    StatClose
      (2 * (ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₁ f T₁ (n₁ - r₁)
          (Fintype.card (HidingSample n₁ T₁ Salt D)) +
        ZkMerkle.openingEps (Fintype.card Salt) (Fintype.card D) n₂ f T₂ (n₂ - r₂)
          (Fintype.card (HidingSample n₂ T₂ Salt D))))
      (realExp2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (realExp2 P₁ P₂ ctx₁ ctx₂ wit₁' wit₂' msg' (T₁ := T₁) (T₂ := T₂) dist) := by
  have h := twofield_zk P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg hinj₁ hinj₂ hvalid₁ hvalid₂ hn₁ hn₂ hT₁ hT₂
    dist
  have h' := twofield_zk P₁ P₂ ctx₁ ctx₂ wit₁' wit₂' msg' hinj₁ hinj₂ hvalid₁' hvalid₂' hn₁ hn₂ hT₁
    hT₂ dist
  rw [two_mul]
  exact h.trans h'.symm
end Theorem

end Lfzk.CompiledLongfellowZkTwoField
