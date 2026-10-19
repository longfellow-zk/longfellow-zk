import Bcs.AffineBlock
import Lfzk.V1StrongV7TranscriptOutsideFinal
import Lfzk.FlatV7Headline

/-! Existing Ligero and LFZK extraction theorems as affine block certificates.
These adapters retain the original hypotheses and total resource budgets.
They do not assert a new per-domain query-count bound. In a composition,
these budgets must be allocated, not each identified with the same total N.
The new generic interface adds no axioms; existing numerical certificates
retain their original native-reduction trust base. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.AffineBlockInstances
open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

def ligeroRate (i : Fin 4) : Bcs.AffineBlock.Rate :=
  Bcs.AffineBlock.Rate.diagonal (density i) (by
    unfold density
    apply add_nonneg _ (highMass_nonneg i)
    unfold cover hypergeometricRatio
    positivity)

theorem ligero_affine_certificate (i : Fin 4)
    {F : Type} {Equations : Type*} {Ctx Other Coin Out : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype Ctx] [DecidableEq Ctx]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Coin] [Nonempty Coin]
    {w nw nq nl N : ℕ} {rounds : ℕ → ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (tree : Tree
      (Lfzk.V1StrongV7TranscriptTerminal.Point i Ctx Other F nl rounds)
      Coin Out N)
    (selected : Out →
      Lfzk.V1StrongV7TranscriptTerminal.Prefix i Ctx Other F nl rounds ×
      Lfzk.V1StrongV7Terminal.Payload i F)
    (oracle : (Lfzk.LigeroPairGeometry.OutsideTerminal
      (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (w := rounds) → Coin) → Lfzk.V1StrongV7TranscriptTerminal.Prefix
      i Ctx Other F nl rounds →
      Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : (Lfzk.LigeroPairGeometry.OutsideTerminal
      (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (w := rounds) → Coin) → Lfzk.V1StrongV7TranscriptTerminal.Prefix
      i Ctx Other F nl rounds →
      ConstraintSystem F nw nq w Equations)
    (decodeChallenge : Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : Coin => decodeChallenge c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : Coin => decodeQuery c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card
      (Ligero.V1.Challenge F nw nq 1 Equations) ≤ Fintype.card Coin)
    (hkquery : kquery * Fintype.card
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin) :
    let parent := Lfzk.LigeroPairGeometry.parent
      (Ctx := Ctx) (Other := Other) (F := F) (nl := nl)
      (block := (row i).k) (dblock := 2 * (row i).k - 1)
      (r := (row i).openings) (w := rounds)
    let child := Lfzk.LigeroPairGeometry.child
      (Ctx := Ctx) (Other := Other) (F := F) (nl := nl)
      (block := (row i).k) (dblock := 2 * (row i).k - 1)
      (r := (row i).openings) (w := rounds)
    let failure := fun H :
        Lfzk.V1StrongV7TranscriptTerminal.Point
          i Ctx Other F nl rounds → Coin =>
      let pr := selected (tree.run H).1
      Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
        (oracle (Lfzk.LigeroPairGeometry.outsideTerminal H) pr.1)
        (statement (Lfzk.LigeroPairGeometry.outsideTerminal H) pr.1) (decodeChallenge (H (parent pr.1)))
        pr.2 (decodeQuery (H (child pr.1 pr.2)))
    Bcs.AffineBlock.Certificate failure (fun _ => (N : ℚ)) (ligeroRate i) := by
  dsimp only
  apply Bcs.AffineBlock.Certificate.of_budget _ _ (N : ℚ) (by positivity)
  have h := Lfzk.V1StrongV7TranscriptOutsideFinal.v7_v1_transcript_outside_final_le i
    hrows hfield D hkrow baseNodes responseNodes tree selected
    oracle statement decodeChallenge decodeQuery kchal kquery
    hchal hqueryBalance hkchal hkquery
  dsimp only at h
  convert h using 1 <;>
    simp only [Bcs.FiniteProbability.density, ligeroRate, Bcs.AffineBlock.Rate.diagonal,
      Fintype.card_fun, Nat.cast_pow, Nat.cast_add, Nat.cast_one]; ring

end Lfzk.AffineBlockInstances

namespace Lfzk.CompiledZk.AffineBlockInstances

open Finset Merkle.MH Lfzk.CompiledZk Lfzk.CertifiedV1
  Lfzk.NizkDeployedHashTwoField Lfzk.CompiledZk.FlatV7Deployed
open Lfzk.CompiledLongfellow (Col)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2)
open Lfzk.NizkAdaptiveTwoField (check2)
open scoped Classical

variable {C D Enc X Out Salt₁ Salt₂ : Type}
  [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype D] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
  [Fintype X] [Inhabited Salt₁] [Inhabited Salt₂]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {F₁ Msg₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁]
  [SumcheckInterp F₁] [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁]
variable {M₁ nt₁ nlin₁ : ℕ}
variable {codec₁ : Codec Salt₁ (Col F₁ v7Hash1.params.nw v7Hash1.params.nq) D Enc}
  {dec₁ : RoleDecoders codec₁}
variable {F₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂]
  [DecidableEq F₂] [SumcheckInterp F₂] [DecidableEq Msg₂]
  [Inhabited Msg₂] [Fintype Msg₂]
variable {M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ : ℕ}
variable {codec₂ : Codec Salt₂ (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
  {dec₂ : RoleDecoders codec₂}

def lfzkRate : Bcs.AffineBlock.Rate :=
  Bcs.AffineBlock.Rate.diagonal (1 / 2^116) (by positivity)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
theorem lfzk_affine_certificate
    [Nonempty X] {nblk tA N TM : ℕ}
    (hD : Fintype.card D = 2 ^ 256)
    (hC : Fintype.card C = 2 ^ 256)
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    (H : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F₁ v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin H.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (mac₁ : (Fin H.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin S₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : C => decode c = x).card ≤ 2 ^ 128)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (hrowSat₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : Fin H.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      H.c.Satisfied (H.pubIn (avOf out) (pubOf out)) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (hrowSat₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
          v7Hash1.params.rounds v7SigHahn.params.rounds → C)
        (a : (Fin S₂.c.ninp → F₂)),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      S₂.c.Satisfied (S₂.pubIn (avOf out) (pubOf out)) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf out)) = tagOf out)
    (htape : 2 * v7SigHahn.params.row.n +
      2 * v7Hash1.params.row.n + tA ≤ TM)
    (hTM : 0 < TM)
    (dummy : Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
      v7Hash1.params.rounds v7SigHahn.params.rounds → C) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    Bcs.AffineBlock.Certificate (fun ω : (Fin TM → D) ×
      (Pt2 D C X Msg₁ Msg₂ v7Hash1.params.nl v7SigHahn.params.nl
        v7Hash1.params.rounds v7SigHahn.params.rounds → C) =>
      v7Hash1_flatEvent H S₂.toSide rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (S.context ω.1 ω.2) (S.merkleOracle check ω.1 ω.2)
        (S.proof ω.1 ω.2) (S.challenges ω.1 ω.2))
      (fun _ => (N + tA : ℚ)) lfzkRate := by
  dsimp only
  apply Bcs.AffineBlock.Certificate.of_budget _ _ (N + tA : ℚ) (by positivity)
  have h := Lfzk.CompiledZk.FlatV7Headline.v7Hash1_deployed_fs_extraction_116_circuit
    hD hC hFmac H S₂ body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ claimOf₁ claimOf₂ aP decode tagOf common₁ common₂
    mac₁ mac₂ hbal hcoll hrowSat₁ hrowSat₂ htape hTM dummy
  dsimp only at h
  convert h using 1 <;>
    simp only [Bcs.FiniteProbability.density, lfzkRate, Bcs.AffineBlock.Rate.diagonal,
      Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]; ring

end Lfzk.CompiledZk.AffineBlockInstances
