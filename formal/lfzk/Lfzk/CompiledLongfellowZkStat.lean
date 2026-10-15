import Lfzk.CompiledLongfellowZkV7
import Lfzk.ZkMerkleStat

/-!
# Statistical zero knowledge of compiled Longfellow, against a full view of the Merkle oracle

`Lfzk.CompiledLongfellowZk.compiled_longfellow_zk` bounds a distinguisher that makes `f` queries to
a lazily sampled Merkle oracle; its error `(4n² + 2·d·f)/|Salt| + …` grows with `f`, so it is a
statement about attackers bounded by their hash work.  Here the distinguisher receives the Merkle
oracle `H : Enc → D` **as a whole function**, together with the proof and both challenge oracles:
it is unbounded.  The price is the nonce length.

`compiled_longfellow_zk_stat`: for every valid witness, the real proof is `d · ε`-close to the
explicit simulation `simExpS`, where `d` bounds the unopened columns and

```
|D| ≤ 4 · ε² · |Salt|
```

At 256-bit digests and 542-bit nonces, `ε = 2^-144`; the two-field mdoc proof at the v7
geometries is then `2^-131`-close to its simulation (`v7_twofield_zk_stat542`).  At the deployed
256-bit nonces the hypothesis forces `ε ≥ 1/2`, so the statistical statement says nothing there:
it is a statement about a protocol with longer nonces.

## The simulator

As in `CompiledLongfellowZk` (the zero tableau, the uniform transmission, `ZkAdaptiveV1.simResp`,
the two programmed Ligero points), except for the commitment: the opened leaves are hashed from
their columns and nonces, and the **unopened leaves' digests are fresh uniform values** `u`; the
root and the frontier digests are hashed up from those (`ZkMerkleStat.digestView`).  The
simulator samples `H` itself and hands it to the distinguisher.

## The hybrids

| step | cost | lemma |
|---|---|---|
| program the Ligero points | **0** | `CompiledLigeroZk.statClose_prog` |
| unopened digests ← uniform | `d · ε` | `ZkMerkleStat.view_statClose` (leftover hash lemma, leaf by leaf) |
| explicit V1 response | **0** | `ZkAdaptiveV1.statClose_adaptive` |
| pad reparametrisation | **0** | `Frontend.transmit_bijective` |

The order is the one of `CompiledLongfellowZk`, for the same reasons.  The model is the same too
(programmable random oracles, single session, statement fixed first), with one difference: the
Merkle oracle is a uniformly random **total** function on a finite input space `Enc` (fixed-width
encodings), handed to the distinguisher in full.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Lfzk.CompiledLongfellowZkStat

open Merkle Merkle.MH LigeroFamily LigeroFamily.ZeroKnowledge
open Lfzk.ZkAdaptiveV1 Lfzk.CompiledLigeroZk Lfzk.CompiledLongfellowZk Lfzk.ZkMerkleStat

/-! ## The experiments -/

section Experiments

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq reps : ℕ}
variable {Salt D Enc Coin LQ Ctx Wit Blind Tr RO V : Type}
variable [Inhabited D] [DecidableEq LQ]

/-- **A full-view distinguisher**: it receives the proof, the round oracle, the Ligero challenge
oracle and the Merkle oracle, all as whole functions. -/
abbrev FullDistinguisher (F : Type) [Field F] (r w n nw nq reps : ℕ)
    (Salt D Enc Tr Coin LQ RO V : Type) :=
  LProof F r w n nw nq reps Salt D Tr Coin → RO → (LQ → Coin) → (Enc → D) → V

/-- The real Merkle coins: the nonces and the oracle. -/
abbrev MerkleCoins (n : ℕ) (Salt D Enc : Type) := (Fin n → Salt) × (Enc → D)

/-- The simulated Merkle coins: the nonces, the oracle and the fresh digests. -/
abbrev SimMerkleCoins (n : ℕ) (Salt D Enc : Type) := (Fin n → Salt) × (Enc → D) × (Fin n → D)

/-- **One side's honest proof** at oracle `H` and context `κ`: commit the columns of
`v1Oracle (msgs wit b) ρ` with nonces `nonce` under `H`, run the honest sumcheck, read the two
Ligero challenges off `Gl`, open at the query. -/
noncomputable def realProofS {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc) (H : Enc → D)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (κ : Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit)
    (ρ : Tape C nw nq reps) (b : Blind) (nonce : Fin n → Salt) (Gr : RO) (Gl : LQ → Coin) :
    LProof F r w n nw nq reps Salt D Tr Coin :=
  let t := FE.transmit wit Gr κ b
  let c := Gl (pts.first κ t)
  let resp := v1Resp (FE.stmt Gr κ t) (FE.msgs wit b) ρ (dec₁ c)
  let i := Gl (pts.second κ t c resp)
  ⟨MH.root (Cod.withOracle H) n nonce (colsOf (v1Oracle (FE.msgs wit b) ρ)), t, c, resp, i, dec₂ i,
    MH.openCore (Cod.withOracle H) n (dec₂ i).coordinates nonce
      (colsOf (v1Oracle (FE.msgs wit b) ρ)),
    openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i)⟩

/-- The honest root. -/
noncomputable def realRootS {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc) (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO)
    (wit : Wit) (ρ : Tape C nw nq reps) (b : Blind) (hs : MerkleCoins n Salt D Enc) : D :=
  MH.root (Cod.withOracle hs.2) n hs.1 (colsOf (v1Oracle (FE.msgs wit b) ρ))

/-- The real experiment at fixed coins. -/
noncomputable def realCoreS {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit)
    (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : MerkleCoins n Salt D Enc) (Gr : RO)
    (Gl : LQ → Coin) : V :=
  dist (realProofS Cod hs.2 dec₁ dec₂ FE (ctx (realRootS Cod FE wit ρ b hs)) pts wit ρ b hs.1 Gr Gl)
    Gr Gl hs.2

/--
**The real experiment.**  Coins: the V1 tape, the blinders, the nonces and the Merkle oracle, the
round oracle and the Ligero challenge oracle — all uniform.
-/
noncomputable def realExpS (C : MultiplicativeCode F r w n)
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit)
    (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V) :
    Tape C nw nq reps × Blind × MerkleCoins n Salt D Enc × RO × (LQ → Coin) → V :=
  fun ω => realCoreS Cod dec₁ dec₂ FE ctx pts wit dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2

/-- **The simulated commitment view** at query `q`: the opened leaves `L` hashed with their
nonces, the unopened leaves' digests `u`, hashed up under `H`. -/
noncomputable def hidView (Cod : Codec Salt (Col F nw nq reps) D Enc) (H : Enc → D)
    (q : QuerySet n r) (nonce : Fin n → Salt) (L : Fin n → Col F nw nq reps) (u : Fin n → D) :
    OpeningView n q.coordinates Salt D :=
  digestView Cod H n q.coordinates (fun j => nonce j.1)
    (fun j => if j ∈ q.coordinates then H (Cod.leafEnc (nonce j, L j)) else u j)

omit [DecidableEq LQ] in
/-- The simulated view reads the leaves only where they are opened. -/
theorem hidView_leavesOfOpen (Cod : Codec Salt (Col F nw nq reps) D Enc) (H : Enc → D)
    (q : QuerySet n r) (nonce : Fin n → Salt) (O : Ligero.V1.Oracle F nw nq n reps)
    (u : Fin n → D) :
    hidView Cod H q nonce (leavesOfOpen (openSchemeOracle O q)) u
      = hidView Cod H q nonce (colsOf O) u := by
  unfold hidView
  congr 2
  funext j
  by_cases hj : j ∈ q.coordinates
  · simp only [hj, if_true, leavesOfOpen]
    rfl
  · simp only [hj, if_false]

/-- The hybrids' common shape: at view `ov`, the transmission `tOf root` and response
`respOf root`, raw challenges `c` and `i`, the Ligero oracle `G₀` programmed at the two derived
points, the opening `o`; the distinguisher also gets `H`. -/
noncomputable def hybS (dec₂ : Coin → QuerySet n r) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ)
    (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (i : Coin) (o : Ligero.V1.Opening F nw nq reps n r (dec₂ i)) (tOf : D → Tr)
    (respOf : D → LigeroFamily.Response F r w n reps) (c : Coin) (Gr : RO) (G₀ : LQ → Coin)
    (H : Enc → D) (ov : OpeningView n (dec₂ i).coordinates Salt D) : V :=
  dist ⟨ov.rt, tOf ov.rt, c, respOf ov.rt, i, dec₂ i, ov.proof, o⟩ Gr
    (progAt G₀ (pts.first (ctx ov.rt) (tOf ov.rt)) c
      (pts.second (ctx ov.rt) (tOf ov.rt) c (respOf ov.rt)) i) H

/-- The simulated experiment at fixed coins. -/
noncomputable def simCoreS {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (stmt : RO → Ctx → Tr → ConstraintSystem F nw nq w Equations) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ)
    (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (ρ' : Tape C nw nq reps) (t : Tr) (hs : SimMerkleCoins n Salt D Enc) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) : V :=
  hybS dec₂ ctx pts dist i (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i)) (fun _ => t)
    (simRespAt stmt ctx dec₁ dec₂ ρ' t c i Gr) c Gr G₀ hs.2.1
    (hidView Cod hs.2.1 (dec₂ i) hs.1 (leavesOfOpen (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i)))
      hs.2.2)

/--
**The simulated experiment.**  It never sees a witness.  Coins: a V1 tape, a transmission, the
nonces, the Merkle oracle and the fresh digests, the round oracle, a Ligero challenge oracle and
two raw challenges.
-/
noncomputable def simExpS (C : MultiplicativeCode F r w n)
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
    (stmt : RO → Ctx → Tr → ConstraintSystem F nw nq w Equations) (ctx : D → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ)
    (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V) :
    Tape C nw nq reps × Tr × SimMerkleCoins n Salt D Enc × RO × (LQ → Coin) × Coin × Coin → V :=
  fun ω => simCoreS Cod dec₁ dec₂ stmt ctx pts dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1
    ω.2.2.2.2.2.1 ω.2.2.2.2.2.2

end Experiments

/-! ## The hybrids and the bound -/

section Bound

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq reps : ℕ}
variable {Salt D Enc Coin LQ Ctx Wit Blind Tr RO V : Type}
variable [Fintype Salt] [DecidableEq Salt] [Nonempty Salt] [Fintype D] [DecidableEq D] [Inhabited D]
variable [Fintype Enc] [DecidableEq Enc] [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
variable [Fintype LQ] [DecidableEq LQ] [Fintype Blind] [Fintype Tr] [Fintype RO]

variable (C : MultiplicativeCode F r w n) (Cod : Codec Salt (Col F nw nq reps) D Enc)
  (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations) (dec₂ : Coin → QuerySet n r)
  (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : D → Ctx)
  (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ) (wit : Wit)

/-- Hybrid 1: the real commitment, fresh raw Ligero challenges, the oracle programmed to agree. -/
noncomputable def h1S (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : MerkleCoins n Salt D Enc) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) : V :=
  hybS dec₂ ctx pts dist i (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))
    (fun root => FE.transmit wit Gr (ctx root) b)
    (fun root => v1Resp (FE.stmt Gr (ctx root) (FE.transmit wit Gr (ctx root) b)) (FE.msgs wit b)
      ρ (dec₁ c)) c Gr G₀ hs.2
    ⟨MH.root (Cod.withOracle hs.2) n hs.1 (colsOf (v1Oracle (FE.msgs wit b) ρ)),
      MH.openCore (Cod.withOracle hs.2) n (dec₂ i).coordinates hs.1
        (colsOf (v1Oracle (FE.msgs wit b) ρ))⟩

/-- Hybrid 2: the unopened leaves' digests are fresh. -/
noncomputable def h2S (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : SimMerkleCoins n Salt D Enc) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) : V :=
  hybS dec₂ ctx pts dist i (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))
    (fun root => FE.transmit wit Gr (ctx root) b)
    (fun root => v1Resp (FE.stmt Gr (ctx root) (FE.transmit wit Gr (ctx root) b)) (FE.msgs wit b)
      ρ (dec₁ c)) c Gr G₀ hs.2.1
    (hidView Cod hs.2.1 (dec₂ i) hs.1
      (leavesOfOpen (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))) hs.2.2)

/-- Hybrid 3: the simulator's tableau and response, still the honest transmission. -/
noncomputable def h3S (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (ρ' : Tape C nw nq reps) (b : Blind) (hs : SimMerkleCoins n Salt D Enc) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) : V :=
  hybS dec₂ ctx pts dist i (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i))
    (fun root => FE.transmit wit Gr (ctx root) b)
    (fun root => simRespAt FE.stmt ctx dec₁ dec₂ ρ' (FE.transmit wit Gr (ctx root) b) c i Gr root)
    c Gr G₀ hs.2.1
    (hidView Cod hs.2.1 (dec₂ i) hs.1 (leavesOfOpen (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i)))
      hs.2.2)

/-! ### Step 1: programming the two Ligero points is free -/

theorem realCoreS_prog (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : MerkleCoins n Salt D Enc) (Gr : RO)
    (G₀ : LQ → Coin) (c i : Coin) :
    realCoreS Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr
        (prog (pts.first (ctx (realRootS Cod FE wit ρ b hs))
            (FE.transmit wit Gr (ctx (realRootS Cod FE wit ρ b hs)) b))
          (fun c' => pts.second (ctx (realRootS Cod FE wit ρ b hs))
            (FE.transmit wit Gr (ctx (realRootS Cod FE wit ρ b hs)) b) c'
            (v1Resp (FE.stmt Gr (ctx (realRootS Cod FE wit ρ b hs))
                (FE.transmit wit Gr (ctx (realRootS Cod FE wit ρ b hs)) b))
              (FE.msgs wit b) ρ (dec₁ c')))
          G₀ c i)
      = h1S C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i := by
  simp only [realCoreS, realProofS, h1S, hybS]
  rw [prog_first (fun c' => pts.second_ne_first _ _ _ _), prog_second]
  rfl

theorem stepS_prog (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (ρ : Tape C nw nq reps) (b : Blind) (hs : MerkleCoins n Salt D Enc) (Gr : RO) :
    StatClose 0 (fun G : LQ → Coin => realCoreS Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G)
      (fun x : (LQ → Coin) × (Coin × Coin) =>
        h1S C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr x.1 x.2.1 x.2.2) := by
  have h := statClose_prog
    (pts.first (ctx (realRootS Cod FE wit ρ b hs))
      (FE.transmit wit Gr (ctx (realRootS Cod FE wit ρ b hs)) b))
    (fun c' => pts.second (ctx (realRootS Cod FE wit ρ b hs))
      (FE.transmit wit Gr (ctx (realRootS Cod FE wit ρ b hs)) b) c'
      (v1Resp (FE.stmt Gr (ctx (realRootS Cod FE wit ρ b hs))
          (FE.transmit wit Gr (ctx (realRootS Cod FE wit ρ b hs)) b))
        (FE.msgs wit b) ρ (dec₁ c')))
    (fun c' => pts.second_ne_first _ _ _ _)
    (fun G => realCoreS Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G)
  have hfun : (fun x : (LQ → Coin) × (Coin × Coin) =>
      realCoreS Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr
        (prog (pts.first (ctx (realRootS Cod FE wit ρ b hs))
            (FE.transmit wit Gr (ctx (realRootS Cod FE wit ρ b hs)) b))
          (fun c' => pts.second (ctx (realRootS Cod FE wit ρ b hs))
            (FE.transmit wit Gr (ctx (realRootS Cod FE wit ρ b hs)) b) c'
            (v1Resp (FE.stmt Gr (ctx (realRootS Cod FE wit ρ b hs))
                (FE.transmit wit Gr (ctx (realRootS Cod FE wit ρ b hs)) b))
              (FE.msgs wit b) ρ (dec₁ c')))
          x.1 x.2.1 x.2.2))
      = fun x => h1S C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr x.1 x.2.1 x.2.2 :=
    funext fun x => realCoreS_prog C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr x.1 x.2.1 x.2.2
  rw [hfun] at h
  exact h

/-! ### Step 2: the unopened leaves' digests are statistically uniform -/

theorem stepS_hide (hleaf : Function.Injective Cod.leafEnc) (d : ℕ)
    (hd : ∀ q : QuerySet n r, (Finset.univ \ q.coordinates).card ≤ d) {ε : ℚ} (hε : 0 ≤ ε)
    (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt)
    (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (ρ : Tape C nw nq reps) (b : Blind) (Gr : RO) (G₀ : LQ → Coin) (c i : Coin) :
    StatClose (d * ε)
      (fun hs : MerkleCoins n Salt D Enc => h1S C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i)
      (fun hs : SimMerkleCoins n Salt D Enc =>
        h2S C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i) := by
  have h := view_statClose Cod hleaf (colsOf (v1Oracle (FE.msgs wit b) ρ)) (dec₂ i).coordinates hε
    hD (fun H ov => hybS dec₂ ctx pts dist i (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))
      (fun root => FE.transmit wit Gr (ctx root) b)
      (fun root => v1Resp (FE.stmt Gr (ctx root) (FE.transmit wit Gr (ctx root) b))
        (FE.msgs wit b) ρ (dec₁ c)) c Gr G₀ H ov)
  have e2 : (fun hs : SimMerkleCoins n Salt D Enc =>
      h2S C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i)
      = fun p => hybS dec₂ ctx pts dist i (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))
          (fun root => FE.transmit wit Gr (ctx root) b)
          (fun root => v1Resp (FE.stmt Gr (ctx root) (FE.transmit wit Gr (ctx root) b))
            (FE.msgs wit b) ρ (dec₁ c)) c Gr G₀ p.2.1
          (digestView Cod p.2.1 n (dec₂ i).coordinates (fun j => p.1 j.1)
            (fun j => if j ∈ (dec₂ i).coordinates
              then p.2.1 (Cod.leafEnc (p.1 j, colsOf (v1Oracle (FE.msgs wit b) ρ) j))
              else p.2.2 j)) := by
    funext p
    simp only [h2S]
    rw [hidView_leavesOfOpen]
    rfl
  rw [e2]
  refine h.mono ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd (dec₂ i)) hε

/-! ### Step 3: the explicit V1 response -/

theorem stepS_adaptive (hvalid : ∀ root, FE.Valid wit (ctx root))
    (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (b : Blind) (hs : SimMerkleCoins n Salt D Enc) (Gr : RO) (G₀ : LQ → Coin) (c i : Coin) :
    StatClose 0
      (fun ρ : Tape C nw nq reps => h2S C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i)
      (fun ρ' : Tape C nw nq reps => h3S C Cod dec₁ dec₂ FE ctx pts wit dist ρ' b hs Gr G₀ c i) := by
  let viewOf : Ligero.V1.Opening F nw nq reps n r (dec₂ i) →
      OpeningView n (dec₂ i).coordinates Salt D :=
    fun o => hidView Cod hs.2.1 (dec₂ i) hs.1 (leavesOfOpen o) hs.2.2
  let S : Ligero.V1.Opening F nw nq reps n r (dec₂ i) → ConstraintSystem F nw nq w Equations :=
    fun o => FE.stmt Gr (ctx (viewOf o).rt) (FE.transmit wit Gr (ctx (viewOf o).rt) b)
  have hsat : ∀ o, (S o).Satisfies (FE.msgs wit b) :=
    fun o => FE.honest_sat wit Gr _ b (hvalid _)
  let Ψ : Ligero.V1.Opening F nw nq reps n r (dec₂ i) → LigeroFamily.Response F r w n reps → V :=
    fun o resp => hybS dec₂ ctx pts dist i o (fun root => FE.transmit wit Gr (ctx root) b)
      (fun _ => resp) c Gr G₀ hs.2.1 (viewOf o)
  have h := statClose_adaptive (C := C) (FE.msgs wit b) (dec₂ i) (dec₁ c) S hsat Ψ
  have e1 : (fun ρ => h2S C Cod dec₁ dec₂ FE ctx pts wit dist ρ b hs Gr G₀ c i)
      = fun ρ : Tape C nw nq reps => Ψ (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))
          (v1Resp (S (openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i))) (FE.msgs wit b) ρ
            (dec₁ c)) := rfl
  have e2 : (fun ρ' => h3S C Cod dec₁ dec₂ FE ctx pts wit dist ρ' b hs Gr G₀ c i)
      = fun ρ' : Tape C nw nq reps => Ψ (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i))
          (adaptiveSimResp (dec₂ i) (dec₁ c) S ρ') := rfl
  rw [e1, e2]
  exact h

/-! ### Step 4: the pad makes the transmission uniform -/

theorem stepS_pad (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V)
    (ρ' : Tape C nw nq reps) (hs : SimMerkleCoins n Salt D Enc) (Gr : RO) (G₀ : LQ → Coin)
    (c i : Coin) :
    StatClose 0
      (fun b : Blind => h3S C Cod dec₁ dec₂ FE ctx pts wit dist ρ' b hs Gr G₀ c i)
      (fun t : Tr => simCoreS Cod dec₁ dec₂ FE.stmt ctx pts dist ρ' t hs Gr G₀ c i) := by
  let root₀ := (hidView Cod hs.2.1 (dec₂ i) hs.1
    (leavesOfOpen (openSchemeOracle (v1Oracle 0 ρ') (dec₂ i))) hs.2.2).rt
  let e := Equiv.ofBijective (FE.transmit wit Gr (ctx root₀))
    (FE.transmit_bijective wit Gr (ctx root₀))
  exact statClose_of_equiv_pointwise _ _ e fun b => rfl

/-! ### The theorem -/

/--
**Statistical zero knowledge of compiled Longfellow at Ligero V1, against a full view.**

For every witness valid at every root, and every distinguisher that receives the proof, the round
oracle, the Ligero challenge oracle and the Merkle oracle — all in full — the real experiment is
`d · ε`-close to the witness-free simulation `simExpS`, where `d` bounds the unopened columns and
`|D| ≤ 4 · ε² · |Salt|`.  The leaf encoding must be injective (fixed-width `nonce ‖ column`).
-/
theorem compiled_longfellow_zk_stat (hleaf : Function.Injective Cod.leafEnc)
    (hvalid : ∀ root, FE.Valid wit (ctx root)) (d : ℕ)
    (hd : ∀ q : QuerySet n r, (Finset.univ \ q.coordinates).card ≤ d) {ε : ℚ} (hε : 0 ≤ ε)
    (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt)
    (dist : FullDistinguisher F r w n nw nq reps Salt D Enc Tr Coin LQ RO V) :
    StatClose (d * ε) (realExpS C Cod dec₁ dec₂ FE ctx pts wit dist)
      (simExpS C Cod dec₁ dec₂ FE.stmt ctx pts dist) := by
  classical
  let H1 : Tape C nw nq reps × Blind × MerkleCoins n Salt D Enc × RO × (LQ → Coin) × Coin × Coin →
      V :=
    fun ω => h1S C Cod dec₁ dec₂ FE ctx pts wit dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1
      ω.2.2.2.2.2.1 ω.2.2.2.2.2.2
  let H2 : Tape C nw nq reps × Blind × SimMerkleCoins n Salt D Enc × RO × (LQ → Coin) × Coin ×
      Coin → V :=
    fun ω => h2S C Cod dec₁ dec₂ FE ctx pts wit dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1
      ω.2.2.2.2.2.1 ω.2.2.2.2.2.2
  let H3 : Tape C nw nq reps × Blind × SimMerkleCoins n Salt D Enc × RO × (LQ → Coin) × Coin ×
      Coin → V :=
    fun ω => h3S C Cod dec₁ dec₂ FE ctx pts wit dist ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1
      ω.2.2.2.2.2.1 ω.2.2.2.2.2.2
  have hdε : 0 ≤ (d : ℚ) * ε := mul_nonneg (Nat.cast_nonneg d) hε
  have s1 : StatClose 0 (realExpS C Cod dec₁ dec₂ FE ctx pts wit dist) H1 :=
    statClose_mix_equiv le_rfl _ _ (e1R _ _ _ _ _) (e1S _ _ _ _ _ _ _)
      fun r₁ => stepS_prog C Cod dec₁ dec₂ FE ctx pts wit dist r₁.1 r₁.2.1 r₁.2.2.1 r₁.2.2.2
  have s2 : StatClose (d * ε) H1 H2 :=
    statClose_mix_equiv hdε _ _ (e2 _ _ _ _ _ _ _) (e2 _ _ _ _ _ _ _)
      fun r₁ => stepS_hide C Cod dec₁ dec₂ FE ctx pts wit hleaf d hd hε hD dist r₁.1 r₁.2.1
        r₁.2.2.1 r₁.2.2.2.1 r₁.2.2.2.2.1 r₁.2.2.2.2.2
  have s3 : StatClose 0 H2 H3 :=
    statClose_mix_equiv le_rfl _ _ (e3 _ _ _ _ _ _ _) (e3 _ _ _ _ _ _ _)
      fun r₁ => stepS_adaptive C Cod dec₁ dec₂ FE ctx pts wit hvalid dist r₁.1 r₁.2.1 r₁.2.2.1
        r₁.2.2.2.1 r₁.2.2.2.2.1 r₁.2.2.2.2.2
  have s4 : StatClose 0 H3 (simExpS C Cod dec₁ dec₂ FE.stmt ctx pts dist) :=
    statClose_mix_equiv le_rfl _ _ (e4 _ _ _ _ _ _ _) (e4 _ _ _ _ _ _ _)
      fun r₁ => stepS_pad C Cod dec₁ dec₂ FE ctx pts wit dist r₁.1 r₁.2.1 r₁.2.2.1 r₁.2.2.2.1
        r₁.2.2.2.2.1 r₁.2.2.2.2.2
  have h := s1.trans (s2.trans (s3.trans s4))
  simpa using h

end Bound

/-! ## The two-field mdoc proof -/

open Lfzk.CompiledLongfellowZkTwoField Lfzk.Mac

section TwoField

variable {F E : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
variable {r w n nw nq reps : ℕ}
variable {Salt D Enc Coin LQ Ctx Tr RO V : Type}
variable [Inhabited D] [DecidableEq LQ]

/-- The simulated view of one side, at its coins. -/
noncomputable def simViewS {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc) (dec₂ : Coin → QuerySet n r)
    (ρ' : Tape C nw nq reps) (i : Coin) (hs : SimMerkleCoins n Salt D Enc) :
    OpeningView n (dec₂ i).coordinates Salt D :=
  hidView Cod hs.2.1 (dec₂ i) hs.1 (simLeaves dec₂ ρ' i) hs.2.2

/-- **One side's simulated proof** at context `κ`. -/
noncomputable def simProofS {C : MultiplicativeCode F r w n}
    (Cod : Codec Salt (Col F nw nq reps) D Enc)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps E) (dec₂ : Coin → QuerySet n r)
    (stmt : RO → Ctx → Tr → ConstraintSystem F nw nq w E) (κ : Ctx)
    (ρ' : Tape C nw nq reps) (t : Tr) (c i : Coin) (Gr : RO) (hs : SimMerkleCoins n Salt D Enc) :
    LProof F r w n nw nq reps Salt D Tr Coin :=
  ⟨(simViewS Cod dec₂ ρ' i hs).rt, t, c, simResp (stmt Gr κ t) (dec₂ i) (dec₁ c) ρ', i, dec₂ i,
    (simViewS Cod dec₂ ρ' i hs).proof, openSchemeOracle (v1Oracle 0 ρ') (dec₂ i)⟩

end TwoField

section TwoFieldExp

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] {nblk : ℕ}

/-- **A full-view two-field distinguisher**: the tags, both proofs, every challenge oracle and both
Merkle oracles, all in full. -/
abbrev TwoFullDistinguisher (F₁ : Type) [Field F₁] (r₁ w₁ n₁ nw₁ nq₁ reps₁ : ℕ) (F₂ : Type)
    [Field F₂] (r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ)
    (Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac : Type) (nblk : ℕ) (V : Type) :=
  TwoProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ Salt D Tr₁ Tr₂ Coin₁ Coin₂ Fmac nblk →
    TwoOracles D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂ → (Enc₁ → D) → (Enc₂ → D) → V

/-- Real side coins: the V1 tape, the blinders, the nonces and the Merkle oracle, the round oracle,
the Ligero challenge oracle. -/
abbrev RealCoinsS {F : Type} [Field F] {r w n : ℕ} (C : MultiplicativeCode F r w n)
    (nw nq reps : ℕ) (B Salt D Enc RO LQ Coin : Type) :=
  Tape C nw nq reps × B × MerkleCoins n Salt D Enc × RO × (LQ → Coin)

/-- Simulated side coins: a V1 tape, a transmission, the nonces, the Merkle oracle and the fresh
digests, the round oracle, a Ligero challenge oracle and the two raw challenges. -/
abbrev SimCoinsS {F : Type} [Field F] {r w n : ℕ} (C : MultiplicativeCode F r w n)
    (nw nq reps : ℕ) (Tr Salt D Enc RO LQ Coin : Type) :=
  Tape C nw nq reps × Tr × SimMerkleCoins n Salt D Enc × RO × (LQ → Coin) × Coin × Coin

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
variable (dist : TwoFullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V)

/-- **The real two-field run at fixed coins.**  Both columns are committed under their own oracle;
`av` is read at the two roots; side 1 is proved at context `(root₁, root₂, av, tags)`, side 2
after it; the distinguisher gets both Merkle oracles. -/
noncomputable def realCore2S (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁ : Tape P₁.C nw₁ nq₁ reps₁) (b₁ : B₁) (hs₁ : MerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (Gl₁ : LQ₁ → Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : MerkleCoins n₂ Salt D Enc₂) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) : V :=
  let root₂ := realRootS P₂.Cod P₂.FE (wit₂ ap) ρ₂ b₂ hs₂
  let pf₁ := realProofS P₁.Cod hs₁.2 P₁.dec₁ P₁.dec₂ P₁.FE
    (ctxOf₁ ctx₁ msg ap Gav root₂ (realRootS P₁.Cod P₁.FE (wit₁ ap) ρ₁ b₁ hs₁)) P₁.pts (wit₁ ap)
    ρ₁ b₁ hs₁.1 Gr₁ Gl₁
  let pf₂ := realProofS P₂.Cod hs₂.2 P₂.dec₁ P₂.dec₂ P₂.FE (ctxOf₂ ctx₂ msg ap Gav pf₁ root₂) P₂.pts
    (wit₂ ap) ρ₂ b₂ hs₂.1 Gr₂ Gl₂
  dist (macTag (Gav (pf₁.root, root₂)) ap msg, pf₁, pf₂) (Gav, Gr₁, Gl₁, Gr₂, Gl₂) hs₁.2 hs₂.2

/-- Hybrid: side 1 simulated (at the honest tags), side 2 real. -/
noncomputable def midCore2S (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : SimMerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : MerkleCoins n₂ Salt D Enc₂) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) : V :=
  let root₂ := realRootS P₂.Cod P₂.FE (wit₂ ap) ρ₂ b₂ hs₂
  let κ₁ := ctxOf₁ ctx₁ msg ap Gav root₂ (simViewS P₁.Cod P₁.dec₂ ρ₁' i₁ hs₁).rt
  let pf₁ := simProofS P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE.stmt κ₁ ρ₁' t₁ c₁ i₁ Gr₁ hs₁
  let pf₂ := realProofS P₂.Cod hs₂.2 P₂.dec₁ P₂.dec₂ P₂.FE (ctxOf₂ ctx₂ msg ap Gav pf₁ root₂) P₂.pts
    (wit₂ ap) ρ₂ b₂ hs₂.1 Gr₂ Gl₂
  dist (macTag (Gav (pf₁.root, root₂)) ap msg, pf₁, pf₂)
    (Gav, Gr₁, simOracle κ₁ P₁.pts G₀₁ pf₁, Gr₂, Gl₂) hs₁.2.1 hs₂.2

/-- Both sides simulated; the tags are `tagOf root₁ root₂`. -/
noncomputable def bothCore2S (tagOf : D → D → Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : SimMerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂' : Tape P₂.C nw₂ nq₂ reps₂) (t₂ : Tr₂) (hs₂ : SimMerkleCoins n₂ Salt D Enc₂) (Gr₂ : RO₂)
    (G₀₂ : LQ₂ → Coin₂) (c₂ i₂ : Coin₂) : V :=
  let root₁ := (simViewS P₁.Cod P₁.dec₂ ρ₁' i₁ hs₁).rt
  let root₂ := (simViewS P₂.Cod P₂.dec₂ ρ₂' i₂ hs₂).rt
  let tag := tagOf root₁ root₂
  let κ₁ := ctxOf₁T ctx₁ tag Gav root₂ root₁
  let pf₁ := simProofS P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE.stmt κ₁ ρ₁' t₁ c₁ i₁ Gr₁ hs₁
  let κ₂ := ctxOf₂T ctx₂ tag Gav pf₁ root₂
  let pf₂ := simProofS P₂.Cod P₂.dec₁ P₂.dec₂ P₂.FE.stmt κ₂ ρ₂' t₂ c₂ i₂ Gr₂ hs₂
  dist (tag, pf₁, pf₂)
    (Gav, Gr₁, simOracle κ₁ P₁.pts G₀₁ pf₁, Gr₂, simOracle κ₂ P₂.pts G₀₂ pf₂) hs₁.2.1 hs₂.2.1

/-- **The real two-field experiment.**  Coins: the MAC blinds `mac_ap`, `av`'s oracle and each
side's real coins. -/
noncomputable def realExp2S :
    Tag Fmac nblk × (D × D → Fmac) × RealCoinsS P₁.C nw₁ nq₁ reps₁ B₁ Salt D Enc₁ RO₁ LQ₁ Coin₁ ×
      RealCoinsS P₂.C nw₂ nq₂ reps₂ B₂ Salt D Enc₂ RO₂ LQ₂ Coin₂ → V :=
  fun ω => realCore2S P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω.1 ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2

/-- **The simulated two-field experiment.**  No witness, no blinds: the tags are a uniform coin,
and each side is its full-view simulator at the public data. -/
noncomputable def simExp2S :
    Tag Fmac nblk × (D × D → Fmac) × SimCoinsS P₁.C nw₁ nq₁ reps₁ Tr₁ Salt D Enc₁ RO₁ LQ₁ Coin₁ ×
      SimCoinsS P₂.C nw₂ nq₂ reps₂ Tr₂ Salt D Enc₂ RO₂ LQ₂ Coin₂ → V :=
  fun ω => bothCore2S P₁ P₂ ctx₁ ctx₂ dist (fun _ _ => ω.1) ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2.1
    ω.2.2.1.2.2.2.2.2.1 ω.2.2.1.2.2.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2.1
    ω.2.2.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2.2.2

/-- Side 1's distinguisher, at side 2's real coins: run side 2 and the two-field distinguisher,
handing over side 2's Merkle oracle. -/
noncomputable def distAS (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : MerkleCoins n₂ Salt D Enc₂) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) : FullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Enc₁ Tr₁ Coin₁ LQ₁ RO₁ V :=
  fun pf Gr₁ Gl₁ H₁ =>
    dist (macTag (Gav (pf.root, realRootS P₂.Cod P₂.FE (wit₂ ap) ρ₂ b₂ hs₂)) ap msg, pf,
        realProofS P₂.Cod hs₂.2 P₂.dec₁ P₂.dec₂ P₂.FE
          (ctxOf₂ ctx₂ msg ap Gav pf (realRootS P₂.Cod P₂.FE (wit₂ ap) ρ₂ b₂ hs₂)) P₂.pts (wit₂ ap)
          ρ₂ b₂ hs₂.1 Gr₂ Gl₂)
      (Gav, Gr₁, Gl₁, Gr₂, Gl₂) H₁ hs₂.2

/-- The real two-field run is side 1's real experiment against `distAS`. -/
theorem realCore2S_eq (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁ : Tape P₁.C nw₁ nq₁ reps₁) (b₁ : B₁) (hs₁ : MerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (Gl₁ : LQ₁ → Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : MerkleCoins n₂ Salt D Enc₂) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) :
    realCore2S P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ap Gav ρ₁ b₁ hs₁ Gr₁ Gl₁ ρ₂ b₂ hs₂ Gr₂ Gl₂
      = realCoreS P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE
          (ctxOf₁ ctx₁ msg ap Gav (realRootS P₂.Cod P₂.FE (wit₂ ap) ρ₂ b₂ hs₂)) P₁.pts (wit₁ ap)
          (distAS P₂ ctx₂ wit₂ msg dist ap Gav ρ₂ b₂ hs₂ Gr₂ Gl₂) ρ₁ b₁ hs₁ Gr₁ Gl₁ := rfl

/-- The side-1-simulated hybrid is side 1's simulated experiment against `distAS`. -/
theorem midCore2S_eq_sim (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : SimMerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : MerkleCoins n₂ Salt D Enc₂) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) :
    midCore2S P₁ P₂ ctx₁ ctx₂ wit₂ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁ ρ₂ b₂ hs₂ Gr₂ Gl₂
      = simCoreS P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE.stmt
          (ctxOf₁ ctx₁ msg ap Gav (realRootS P₂.Cod P₂.FE (wit₂ ap) ρ₂ b₂ hs₂)) P₁.pts
          (distAS P₂ ctx₂ wit₂ msg dist ap Gav ρ₂ b₂ hs₂ Gr₂ Gl₂) ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁ := rfl

/-- Side 1's simulated proof as a function of side 2's root. -/
noncomputable def pf₁OfS (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : SimMerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (c₁ i₁ : Coin₁) (root₂ : D) : LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ :=
  simProofS P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE.stmt
    (ctxOf₁ ctx₁ msg ap Gav root₂ (simViewS P₁.Cod P₁.dec₂ ρ₁' i₁ hs₁).rt) ρ₁' t₁ c₁ i₁ Gr₁ hs₁

/-- Side 2's context, at side 1's simulated coins. -/
noncomputable def ctxBS (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : SimMerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (c₁ i₁ : Coin₁) : D → Ctx₂ :=
  fun root₂ => ctxOf₂ ctx₂ msg ap Gav (pf₁OfS P₁ ctx₁ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁ root₂) root₂

/-- Side 2's distinguisher, at side 1's simulated coins: recompute side 1's simulated proof from
side 2's root, and hand over side 1's Merkle oracle. -/
noncomputable def distBS (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : SimMerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁) :
    FullDistinguisher F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ Salt D Enc₂ Tr₂ Coin₂ LQ₂ RO₂ V :=
  fun pf Gr₂ Gl₂ H₂ =>
    dist (macTag (Gav ((pf₁OfS P₁ ctx₁ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁ pf.root).root, pf.root))
        ap msg, pf₁OfS P₁ ctx₁ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁ pf.root, pf)
      (Gav, Gr₁, simOracle (ctxOf₁ ctx₁ msg ap Gav pf.root (simViewS P₁.Cod P₁.dec₂ ρ₁' i₁ hs₁).rt)
          P₁.pts G₀₁ (pf₁OfS P₁ ctx₁ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁ pf.root), Gr₂, Gl₂)
      hs₁.2.1 H₂

/-- The side-1-simulated hybrid is side 2's real experiment against `distBS`. -/
theorem midCore2S_eq_real (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : SimMerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : MerkleCoins n₂ Salt D Enc₂) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) :
    midCore2S P₁ P₂ ctx₁ ctx₂ wit₂ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁ ρ₂ b₂ hs₂ Gr₂ Gl₂
      = realCoreS P₂.Cod P₂.dec₁ P₂.dec₂ P₂.FE (ctxBS P₁ ctx₁ ctx₂ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁)
          P₂.pts (wit₂ ap) (distBS P₁ ctx₁ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁)
          ρ₂ b₂ hs₂ Gr₂ Gl₂ := rfl

/-- Side 2's simulated experiment against `distBS` is the both-simulated hybrid at the honest
tags. -/
theorem simBS_eq_both (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁' : Tape P₁.C nw₁ nq₁ reps₁) (t₁ : Tr₁) (hs₁ : SimMerkleCoins n₁ Salt D Enc₁) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂' : Tape P₂.C nw₂ nq₂ reps₂) (t₂ : Tr₂) (hs₂ : SimMerkleCoins n₂ Salt D Enc₂) (Gr₂ : RO₂)
    (G₀₂ : LQ₂ → Coin₂) (c₂ i₂ : Coin₂) :
    simCoreS P₂.Cod P₂.dec₁ P₂.dec₂ P₂.FE.stmt (ctxBS P₁ ctx₁ ctx₂ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁)
        P₂.pts (distBS P₁ ctx₁ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁) ρ₂' t₂ hs₂ Gr₂ G₀₂ c₂ i₂
      = bothCore2S P₁ P₂ ctx₁ ctx₂ dist (fun r₁ r₂ => macTag (Gav (r₁, r₂)) ap msg) Gav
          ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁ ρ₂' t₂ hs₂ Gr₂ G₀₂ c₂ i₂ := rfl

/-- The side-1-simulated hybrid, on its coin space. -/
noncomputable def midExp2S :
    Tag Fmac nblk × (D × D → Fmac) × SimCoinsS P₁.C nw₁ nq₁ reps₁ Tr₁ Salt D Enc₁ RO₁ LQ₁ Coin₁ ×
      RealCoinsS P₂.C nw₂ nq₂ reps₂ B₂ Salt D Enc₂ RO₂ LQ₂ Coin₂ → V :=
  fun ω => midCore2S P₁ P₂ ctx₁ ctx₂ wit₂ msg dist ω.1 ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2.1
    ω.2.2.1.2.2.2.2.2.1 ω.2.2.1.2.2.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2

/-- Both sides simulated, at the honest tags `av · msg + mac_ap`. -/
noncomputable def bothExp2S :
    Tag Fmac nblk × (D × D → Fmac) × SimCoinsS P₁.C nw₁ nq₁ reps₁ Tr₁ Salt D Enc₁ RO₁ LQ₁ Coin₁ ×
      SimCoinsS P₂.C nw₂ nq₂ reps₂ Tr₂ Salt D Enc₂ RO₂ LQ₂ Coin₂ → V :=
  fun ω => bothCore2S P₁ P₂ ctx₁ ctx₂ dist (fun r₁ r₂ => macTag (ω.2.1 (r₁, r₂)) ω.1 msg) ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2.1
    ω.2.2.1.2.2.2.2.2.1 ω.2.2.1.2.2.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2.1
    ω.2.2.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2.2.2

end TwoFieldExp

section TwoFieldThm

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [Fintype Enc₁] [DecidableEq Enc₁] [Fintype Enc₂] [DecidableEq Enc₂] [Inhabited D]
variable [DecidableEq LQ₁] [DecidableEq LQ₂]
variable [Fintype Salt] [DecidableEq Salt] [Nonempty Salt] [Fintype D] [DecidableEq D]
variable [Fintype Coin₁] [DecidableEq Coin₁] [Nonempty Coin₁] [Fintype Coin₂] [DecidableEq Coin₂]
  [Nonempty Coin₂] [Fintype LQ₁] [Fintype LQ₂] [Fintype B₁] [Fintype B₂] [Fintype Tr₁]
  [Fintype Tr₂] [Fintype RO₁] [Fintype RO₂]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

/--
**Statistical zero knowledge of the two-field mdoc proof, against a full view.**

For witness maps valid at every public input carrying the honest tags, and every distinguisher
that receives the tags, both compiled proofs, every challenge oracle and **both Merkle oracles in
full**, the real two-field experiment is `((n₁ − r₁) + (n₂ − r₂)) · ε`-close to the witness-free
`simExp2S`, whenever `|D| ≤ 4 · ε² · |Salt|`.
-/
theorem twofield_zk_stat (hleaf₁ : Function.Injective P₁.Cod.leafEnc)
    (hleaf₂ : Function.Injective P₂.Cod.leafEnc)
    (hvalid₁ : ∀ ap root₁ root₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ root₁ root₂ av (macTag av ap msg)))
    (hvalid₂ : ∀ ap root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ ap) (ctx₂ root₁ root₂ av (macTag av ap msg) pf₁))
    {ε : ℚ} (hε : 0 ≤ ε) (hD : (Fintype.card D : ℚ) ≤ 4 * ε ^ 2 * Fintype.card Salt)
    (dist : TwoFullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V) :
    StatClose (((n₁ - r₁ : ℕ) : ℚ) * ε + ((n₂ - r₂ : ℕ) : ℚ) * ε)
      (realExp2S P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist)
      (simExp2S P₁ P₂ ctx₁ ctx₂ dist) := by
  classical
  -- Step A: simulate side 1
  have sA : StatClose (((n₁ - r₁ : ℕ) : ℚ) * ε)
      (realExp2S P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist)
      (midExp2S P₁ P₂ ctx₁ ctx₂ wit₂ msg dist) := by
    refine statClose_mix_equiv (mul_nonneg (Nat.cast_nonneg _) hε) _ _ (eA _ _ _ _) (eA _ _ _ _) ?_
    rintro ⟨ap, Gav, ρ₂, b₂, hs₂, Gr₂, Gl₂⟩
    exact compiled_longfellow_zk_stat P₁.C P₁.Cod P₁.dec₁ P₁.dec₂ P₁.FE
      (ctxOf₁ ctx₁ msg ap Gav (realRootS P₂.Cod P₂.FE (wit₂ ap) ρ₂ b₂ hs₂)) P₁.pts (wit₁ ap)
      hleaf₁ (fun root => hvalid₁ ap root _ _) (n₁ - r₁) (fun q => (unopened_card q).le) hε hD
      (distAS P₂ ctx₂ wit₂ msg dist ap Gav ρ₂ b₂ hs₂ Gr₂ Gl₂)
  -- Step B: simulate side 2
  have sB : StatClose (((n₂ - r₂ : ℕ) : ℚ) * ε)
      (midExp2S P₁ P₂ ctx₁ ctx₂ wit₂ msg dist)
      (bothExp2S P₁ P₂ ctx₁ ctx₂ msg dist) := by
    refine statClose_mix_equiv (mul_nonneg (Nat.cast_nonneg _) hε) _ _ (eB _ _ _ _) (eB _ _ _ _) ?_
    rintro ⟨ap, Gav, ρ₁', t₁, hs₁, Gr₁, G₀₁, c₁, i₁⟩
    exact compiled_longfellow_zk_stat P₂.C P₂.Cod P₂.dec₁ P₂.dec₂ P₂.FE
      (ctxBS P₁ ctx₁ ctx₂ msg ap Gav ρ₁' t₁ hs₁ Gr₁ c₁ i₁) P₂.pts (wit₂ ap) hleaf₂
      (fun root => hvalid₂ ap _ root _ _) (n₂ - r₂) (fun q => (unopened_card q).le) hε hD
      (distBS P₁ ctx₁ msg dist ap Gav ρ₁' t₁ hs₁ Gr₁ G₀₁ c₁ i₁)
  -- Step C: the tags are a translate of the blinds
  have sC : StatClose 0 (bothExp2S P₁ P₂ ctx₁ ctx₂ msg dist) (simExp2S P₁ P₂ ctx₁ ctx₂ dist) := by
    refine statClose_mix_equiv le_rfl _ _ (eC _ _ _ _) (eC _ _ _ _) ?_
    rintro ⟨Gav, ω₁, ω₂⟩
    exact statClose_of_equiv_pointwise _ _
      (tagEquiv (Gav ((simViewS P₁.Cod P₁.dec₂ ω₁.1 ω₁.2.2.2.2.2.2 ω₁.2.2.1).rt,
        (simViewS P₂.Cod P₂.dec₂ ω₂.1 ω₂.2.2.2.2.2.2 ω₂.2.2.1).rt)) msg)
      fun _ => rfl
  have h := sA.trans (sB.trans sC)
  simpa using h

end TwoFieldThm

/-! ## At 542-bit nonces -/

/-- `|D| = 2^256 ≤ 4 · (2^-144)² · 2^542`: 542-bit nonces make each unopened leaf `2^-144`-hidden
against a full view. -/
theorem stat542_hD {Salt : Type} [Fintype Salt] (hSalt : Fintype.card Salt = 2 ^ 542) :
    (Fintype.card Bits256 : ℚ) ≤ 4 * (1 / 2 ^ 144) ^ 2 * Fintype.card Salt := by
  have e1 : (2 : ℚ) ^ 542 = 2 ^ 288 * 2 ^ 254 := by rw [← pow_add]
  have e2 : ((1 : ℚ) / 2 ^ 144) ^ 2 = 1 / 2 ^ 288 := by rw [div_pow, one_pow, ← pow_mul]
  have e3 : (4 : ℚ) = 2 ^ 2 := by norm_num
  rw [card_Bits256, hSalt, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, e1, e2, e3, mul_assoc,
    ← mul_assoc (1 / (2 : ℚ) ^ 288), one_div_mul_cancel (pow_ne_zero _ two_ne_zero), one_mul,
    ← pow_add]

section Stat542

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [Fintype Enc₁] [DecidableEq Enc₁] [Fintype Enc₂] [DecidableEq Enc₂]
variable [DecidableEq LQ₁] [DecidableEq LQ₂] [Fintype Salt] [DecidableEq Salt] [Nonempty Salt]
variable [Fintype Coin₁] [DecidableEq Coin₁] [Nonempty Coin₁] [Fintype Coin₂] [DecidableEq Coin₂]
  [Nonempty Coin₂] [Fintype LQ₁] [Fintype LQ₂] [Fintype B₁] [Fintype B₂] [Fintype Tr₁]
  [Fintype Tr₂] [Fintype RO₁] [Fintype RO₂]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}

/--
**The two-field proof with 542-bit nonces is statistically zero knowledge, `≤ 2^-131`**, against
every distinguisher that receives the proof, every challenge oracle and both Merkle oracles in
full — at every pair of geometries with at most `2^12` columns per side, in particular the v7
signature row (`n = 3187`) with any v7 hash row (`n = 3230 … 3436`), 132 openings each
(`CompiledLongfellowZkV7.v7_rows_small`).  Digests stay 256-bit.
-/
theorem v7_twofield_zk_stat542
    (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt Bits256 Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
    (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt Bits256 Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
    (ctx₁ : Bits256 → Bits256 → Fmac → Tag Fmac nblk → Ctx₁)
    (ctx₂ : Bits256 → Bits256 → Fmac → Tag Fmac nblk →
      LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt Bits256 Tr₁ Coin₁ → Ctx₂)
    (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
    (hSalt : Fintype.card Salt = 2 ^ 542)
    (hleaf₁ : Function.Injective P₁.Cod.leafEnc) (hleaf₂ : Function.Injective P₂.Cod.leafEnc)
    (hvalid₁ : ∀ ap root₁ root₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ root₁ root₂ av (macTag av ap msg)))
    (hvalid₂ : ∀ ap root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ ap) (ctx₂ root₁ root₂ av (macTag av ap msg) pf₁))
    (hn₁ : n₁ ≤ 2 ^ 12) (hn₂ : n₂ ≤ 2 ^ 12)
    (dist : TwoFullDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt Bits256 Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V) :
    StatClose (1 / 2 ^ 131)
      (realExp2S P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist)
      (simExp2S P₁ P₂ ctx₁ ctx₂ dist) := by
  have h := twofield_zk_stat P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg hleaf₁ hleaf₂ hvalid₁ hvalid₂
    (by positivity) (stat542_hD hSalt) dist
  refine h.mono ?_
  have h₁ : ((n₁ - r₁ : ℕ) : ℚ) ≤ 2 ^ 12 := by exact_mod_cast (Nat.sub_le n₁ r₁).trans hn₁
  have h₂ : ((n₂ - r₂ : ℕ) : ℚ) ≤ 2 ^ 12 := by exact_mod_cast (Nat.sub_le n₂ r₂).trans hn₂
  have hε : (0 : ℚ) ≤ 1 / 2 ^ 144 := by positivity
  calc ((n₁ - r₁ : ℕ) : ℚ) * (1 / 2 ^ 144) + ((n₂ - r₂ : ℕ) : ℚ) * (1 / 2 ^ 144)
      ≤ 2 ^ 12 * (1 / 2 ^ 144) + 2 ^ 12 * (1 / 2 ^ 144) :=
        add_le_add (mul_le_mul_of_nonneg_right h₁ hε) (mul_le_mul_of_nonneg_right h₂ hε)
    _ = 1 / 2 ^ 131 := by norm_num

end Stat542

end Lfzk.CompiledLongfellowZkStat
