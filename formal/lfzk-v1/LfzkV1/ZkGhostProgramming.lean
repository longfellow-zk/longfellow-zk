import LfzkV1.CompiledLongfellowZkTwoField

/-! Exact pre-sampling of the Ligero answers in the two-field v1 experiment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.ZkGhostProgramming

open Bcs Merkle Merkle.MH LigeroFamily
open LfzkV1.CompiledLongfellowZk LfzkV1.CompiledLongfellowZkTwoField
open LfzkV1.CompiledLigeroZk (prog prog_first prog_second statClose_prog)
open LfzkV1.ZkAdaptiveV1 LfzkV1.ZkTwoTape LfzkV1.Mac

section OneSide

variable {F E : Type} [Field F] [Fintype E]
variable {r w n nw nq reps : ℕ} {C : MultiplicativeCode F r w n}
variable {Salt D Coin LQ Ctx Wit B Tr RO : Type} [DecidableEq LQ]

variable (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps E) (dec₂ : Coin → QuerySet n r)
variable (FE : Frontend F nw nq w E Ctx Wit B Tr RO) (κ : Ctx)
variable (pts : Points Ctx Tr Coin (LigeroFamily.Response F r w n reps) LQ)
variable (wit : Wit) (ρ : Tape C nw nq reps) (b : B) (nonce : Fin n → Salt) (Gr : RO)

private noncomputable def honestResponse (c : Coin) : LigeroFamily.Response F r w n reps :=
  v1Resp (FE.stmt Gr κ (FE.transmit wit Gr κ b)) (FE.msgs wit b) ρ (dec₁ c)

/-- The honest proof with the raw Ligero challenge and query supplied explicitly. -/
noncomputable def honestProofAt (c i : Coin) (vals : ℕ → D) :
    LProof F r w n nw nq reps Salt D Tr Coin :=
  ⟨vals 1, FE.transmit wit Gr κ b, c, honestResponse dec₁ FE κ wit ρ b Gr c, i, dec₂ i,
    { nonce := fun j => nonce j.val, frontierValue := fun v => vals v.val },
    openSchemeOracle (v1Oracle (FE.msgs wit b) ρ) (dec₂ i)⟩

/-- With the commitment fixed, build the honest proof at pre-sampled raw Ligero answers
and program both corresponding transcript addresses. -/
private noncomputable def programmedProof (G₀ : LQ → Coin) (c i : Coin) (vals : ℕ → D) :
    LProof F r w n nw nq reps Salt D Tr Coin × (LQ → Coin) :=
  let pf := honestProofAt dec₁ dec₂ FE κ wit ρ b nonce Gr c i vals
  (pf, simOracle κ pts G₀ pf)

/-- The final table makes the ordinary prover read the pre-sampled answers. -/
private theorem programmedProof_eq_real (G₀ : LQ → Coin) (c i : Coin) (vals : ℕ → D) :
    let result := programmedProof dec₁ dec₂ FE κ pts wit ρ b nonce Gr G₀ c i vals
    (realProof dec₁ dec₂ FE κ pts wit ρ b nonce Gr result.2 vals, result.2) = result := by
  let t := FE.transmit wit Gr κ b
  let p₁ := pts.first κ t
  let p₂ := fun a => pts.second κ t a (honestResponse dec₁ FE κ wit ρ b Gr a)
  have hne (a : Coin) : p₂ a ≠ p₁ := pts.second_ne_first _ _ _ _
  let G := prog p₁ p₂ G₀ c i
  change (honestProofAt dec₁ dec₂ FE κ wit ρ b nonce Gr (G p₁) (G (p₂ (G p₁))) vals, G) =
    (honestProofAt dec₁ dec₂ FE κ wit ρ b nonce Gr c i vals, G)
  have hc : G p₁ = c := prog_first hne G₀ c i
  have hi : G (p₂ c) = i := prog_second p₁ p₂ G₀ c i
  rw [hc, hi]

/-- Sampling the two answers first preserves the joint law of the proof and
the entire challenge table, at every fixed commitment and round table. -/
private theorem proof_pair_statClose [Fintype LQ] [Fintype Coin] [Nonempty Coin] (vals : ℕ → D) :
    StatClose 0
      (fun Gl : LQ → Coin => (realProof dec₁ dec₂ FE κ pts wit ρ b nonce Gr Gl vals, Gl))
      (fun x : (LQ → Coin) × (Coin × Coin) =>
        programmedProof dec₁ dec₂ FE κ pts wit ρ b nonce Gr x.1 x.2.1 x.2.2 vals) := by
  let t := FE.transmit wit Gr κ b
  let p₁ := pts.first κ t
  let p₂ := fun a => pts.second κ t a (honestResponse dec₁ FE κ wit ρ b Gr a)
  have h := statClose_prog p₁ p₂ (fun _ => pts.second_ne_first _ _ _ _)
    (fun Gl => (realProof dec₁ dec₂ FE κ pts wit ρ b nonce Gr Gl vals, Gl))
  have he : (fun x : (LQ → Coin) × (Coin × Coin) =>
      (realProof dec₁ dec₂ FE κ pts wit ρ b nonce Gr (prog p₁ p₂ x.1 x.2.1 x.2.2) vals,
        prog p₁ p₂ x.1 x.2.1 x.2.2)) =
      fun x => programmedProof dec₁ dec₂ FE κ pts wit ρ b nonce Gr x.1 x.2.1 x.2.2 vals := by
    funext x
    exact programmedProof_eq_real dec₁ dec₂ FE κ pts wit ρ b nonce Gr x.1 x.2.1 x.2.2 vals
  exact he ▸ h

end OneSide

private theorem statClose_continue {X X' Y Y' A V : Type}
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (f : X → A) (f' : X' → A) (k : A → Y → V) (k' : A → Y' → V)
    (hf : StatClose 0 f f') (hk : ∀ a, StatClose 0 (k a) (k' a)) :
    StatClose 0 (fun p : X × Y => k (f p.1) p.2) (fun p : X' × Y' => k' (f' p.1) p.2) := by
  have h₁ := statClose_mix_equiv le_rfl (fun p : X × Y => k (f p.1) p.2)
    (fun p : X' × Y => k (f' p.1) p.2) (Equiv.prodComm Y X) (Equiv.prodComm Y X')
    (fun y => statClose_map (fun a => k a y) hf)
  have h₂ := statClose_mix le_rfl (fun x : X' => k (f' x)) (fun x : X' => k' (f' x))
    (fun x => hk (f' x))
  simpa only [zero_add] using h₁.trans h₂

section TwoField

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype E₁] [Field F₂] [Fintype E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [DecidableEq Enc₁] [DecidableEq Enc₂] [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] {nblk T₁ T₂ f : ℕ}

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f)

/-- The honest two-field proof with pre-sampled Ligero answers. Both commitments
are honest. The second side still reads the first side's proof in its context. -/
noncomputable def programmedCore2 (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁ : Tape P₁.C nw₁ nq₁ reps₁) (b₁ : B₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (G₀₁ : LQ₁ → Coin₁) (c₁ i₁ : Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (G₀₂ : LQ₂ → Coin₂) (c₂ i₂ : Coin₂) : V :=
  let O₁ := commitOut P₁.Cod hs₁.1 (colsOf (v1Oracle (P₁.FE.msgs (wit₁ ap) b₁) ρ₁)) hs₁.2
  let O₂ := commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2
  let A₁ := programmedProof P₁.dec₁ P₁.dec₂ P₁.FE
    (ctxOf₁ ctx₁ msg ap Gav (O₂.1 1) (O₁.1 1)) P₁.pts
    (wit₁ ap) ρ₁ b₁ hs₁.1 Gr₁ G₀₁ c₁ i₁ O₁.1
  let A₂ := programmedProof P₂.dec₁ P₂.dec₂ P₂.FE
    (ctxOf₂ ctx₂ msg ap Gav A₁.1 (O₂.1 1)) P₂.pts
    (wit₂ ap) ρ₂ b₂ hs₂.1 Gr₂ G₀₂ c₂ i₂ O₂.1
  lazyRun2 hs₁.2 hs₂.2 default
    (dist (macTag (Gav (A₁.1.root, O₂.1 1)) ap msg, A₁.1, A₂.1) (Gav, Gr₁, A₁.2, Gr₂, A₂.2))
    O₁.2 O₂.2

variable [Fintype LQ₁] [Fintype LQ₂] [Fintype Coin₁] [Fintype Coin₂]
  [Nonempty Coin₁] [Nonempty Coin₂]

/-- The fixed-commitment two-field answer law. The whole first-side view is
carried into the continuation, including its programmed challenge oracle. -/
theorem programmedCore2_statClose (ap : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁ : Tape P₁.C nw₁ nq₁ reps₁) (b₁ : B₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂) :
    StatClose 0
      (fun g : (LQ₁ → Coin₁) × (LQ₂ → Coin₂) =>
        realCore2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ap Gav ρ₁ b₁ hs₁ Gr₁ g.1 ρ₂ b₂ hs₂ Gr₂ g.2)
      (fun g : ((LQ₁ → Coin₁) × (Coin₁ × Coin₁)) × ((LQ₂ → Coin₂) × (Coin₂ × Coin₂)) =>
        programmedCore2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ap Gav
          ρ₁ b₁ hs₁ Gr₁ g.1.1 g.1.2.1 g.1.2.2 ρ₂ b₂ hs₂ Gr₂ g.2.1 g.2.2.1 g.2.2.2) := by
  let O₁ := commitOut P₁.Cod hs₁.1 (colsOf (v1Oracle (P₁.FE.msgs (wit₁ ap) b₁) ρ₁)) hs₁.2
  let O₂ := commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ ap) b₂) ρ₂)) hs₂.2
  let κ₁ := ctxOf₁ ctx₁ msg ap Gav (O₂.1 1) (O₁.1 1)
  let κ₂ := fun p : LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ =>
    ctxOf₂ ctx₂ msg ap Gav p (O₂.1 1)
  let observe (A₁ : LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ × (LQ₁ → Coin₁))
      (A₂ : LProof F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ Salt D Tr₂ Coin₂ × (LQ₂ → Coin₂)) :=
    lazyRun2 hs₁.2 hs₂.2 default
      (dist (macTag (Gav (A₁.1.root, O₂.1 1)) ap msg, A₁.1, A₂.1) (Gav, Gr₁, A₁.2, Gr₂, A₂.2)) O₁.2 O₂.2
  let real₁ (G : LQ₁ → Coin₁) :=
    (realProof P₁.dec₁ P₁.dec₂ P₁.FE κ₁ P₁.pts (wit₁ ap) ρ₁ b₁ hs₁.1 Gr₁ G O₁.1, G)
  let prog₁ (x : (LQ₁ → Coin₁) × Coin₁ × Coin₁) :=
    programmedProof P₁.dec₁ P₁.dec₂ P₁.FE κ₁ P₁.pts (wit₁ ap) ρ₁ b₁ hs₁.1 Gr₁
      x.1 x.2.1 x.2.2 O₁.1
  let real₂ := fun A₁ (G : LQ₂ → Coin₂) => observe A₁
    (realProof P₂.dec₁ P₂.dec₂ P₂.FE (κ₂ A₁.1) P₂.pts (wit₂ ap) ρ₂ b₂ hs₂.1 Gr₂ G O₂.1, G)
  let prog₂ := fun A₁ (x : (LQ₂ → Coin₂) × Coin₂ × Coin₂) => observe A₁
    (programmedProof P₂.dec₁ P₂.dec₂ P₂.FE (κ₂ A₁.1) P₂.pts
      (wit₂ ap) ρ₂ b₂ hs₂.1 Gr₂ x.1 x.2.1 x.2.2 O₂.1)
  have h₁ : StatClose 0 real₁ prog₁ :=
    proof_pair_statClose P₁.dec₁ P₁.dec₂ P₁.FE κ₁ P₁.pts (wit₁ ap) ρ₁ b₁ hs₁.1 Gr₁ O₁.1
  have h₂ : ∀ A₁, StatClose 0 (real₂ A₁) (prog₂ A₁) := fun A₁ =>
    statClose_map (observe A₁)
      (proof_pair_statClose P₂.dec₁ P₂.dec₂ P₂.FE (κ₂ A₁.1) P₂.pts (wit₂ ap) ρ₂ b₂ hs₂.1 Gr₂ O₂.1)
  change StatClose 0 (fun g : (LQ₁ → Coin₁) × (LQ₂ → Coin₂) => real₂ (real₁ g.1) g.2)
    (fun g : ((LQ₁ → Coin₁) × (Coin₁ × Coin₁)) × ((LQ₂ → Coin₂) × (Coin₂ × Coin₂)) =>
      prog₂ (prog₁ g.1) g.2)
  exact statClose_continue real₁ prog₁ real₂ prog₂ h₁ h₂

end TwoField

end LfzkV1.ZkGhostProgramming
