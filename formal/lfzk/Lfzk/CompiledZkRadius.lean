import Lfzk.CompiledZkProfileRows
import Lfzk.RbrZkLift

/-!
# A circuit side at the optimized V1 extraction radius

The deployed verifier, code, messages, and field checks are unchanged.  The
analysis may enlarge only the lift list.  `zkFieldDataP` is polymorphic in
that list, and the old Ligero query classifier transfers because no
satisfying large-radius candidate implies no satisfying old-radius candidate.
The candidate-count premise must come from a checked certificate at the
chosen radius.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZk

open Merkle.MH LigeroFamily Lfzk.NizkZkTwoField
  Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.ZkLigeroV1
  Lfzk.CertifiedV1 Lfzk.Arith Lfzk.ZkArithProfile
open Finset
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F]
variable {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D]
  [DecidableEq Enc] [Inhabited Salt]
variable {X : Type} {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}

/-- The committed candidate list at an arbitrary analysis radius. -/
abbrev sideLiftAt
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ) (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) : Type :=
  SchemeLiftCandidate
    (R.params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR))
    (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR)
      hr dec (rootOfKey σ.1.1, σ.1.2)) radius

/-- Reuse the deployed circuit's field analysis with the candidate list at
`radius`.  The Ligero classifier is transported from the existing row;
the separate flat certificate will sharpen its terminal-pair count. -/
noncomputable def CircuitSide.toZkSideAt
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ) (hradius : R.params.row.e + R.params.row.g ≤ radius)
    (hcard : ∀ σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc,
      Fintype.card (sideLiftAt S radius σ) ≤ R.cardCand) :
    ZkSide R logv (Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) C F
      (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin S.c.ninp → F)
      M S.c.ninp S.L 0 where
  V σ := S.Vc σ.2.1 σ.2.2
  Lift σ := sideLiftAt S radius σ
  fin _ := inferInstance
  hcand σ := hcard σ
  H σ := zkHonestP S.hwf (S.pubIn σ.2.1 σ.2.2)
    (fun ℓ => (asgAt S.pl radius ℓ).1)
    (cPendP S.c (S.pubIn σ.2.1 σ.2.2) S.L R.params.logw
      (fun ℓ => (asgAt S.pl radius ℓ).1))
  asg _ := asgAt S.pl radius
  wit _ ℓ := (asgAt S.pl radius ℓ).1
  Sat σ ℓ := S.c.Satisfied (S.pubIn σ.2.1 σ.2.2)
    (asgAt S.pl radius ℓ).1
  FD σ := zkFieldDataP S.hwf (S.pubIn σ.2.1 σ.2.2)
    S.hiso S.hde (S.Vc σ.2.1 σ.2.2) (S.hV _ _) (S.hst0 _ _)
    (fun ℓ => (asgAt S.pl radius ℓ).1) (asgAt S.pl radius)
    (fun _ _ _ => rfl) S.kinit S.kpair S.k S.kchal S.kq
    (S.hbalInit _ _) (S.hbalPair _ _) (S.hbalF _ _)
    (S.hbalChal _ _) (S.hbalQuery _ _) S.hnl
  hexact σ := zkFieldDataP_exactAt S.hwf (S.pubIn σ.2.1 σ.2.2)
    S.hiso S.hde (S.Vc σ.2.1 σ.2.2) (S.hV _ _) (S.hst0 _ _)
    (fun ℓ => (asgAt S.pl radius ℓ).1) (asgAt S.pl radius)
    (fun _ _ _ => rfl) S.kinit S.kpair S.k S.kchal S.kq
    (S.hbalInit _ _) (S.hbalPair _ _) (S.hbalF _ _)
    (S.hbalChal _ _) (S.hbalQuery _ _) S.hnl
    S.hkinit S.hkpair S.hk S.hkchal S.hkq
  LD σ := (S.toSide.LD σ).changeCandidates
    (fun sys hn => ZkLigeroV1.noSat_of_larger_radius S.pl hradius sys hn)
  hesc σ sys hf hn := S.toSide.LD_esc σ sys hf
    (ZkLigeroV1.noSat_of_larger_radius S.pl hradius sys hn)
  hbq σ := (S.toSide.LD_bq σ).le
  hQ := by simp [LigeroV1LayerStep.Qry]

/-- Changing the extraction radius does not change any verifier transition
or accepting query.  This connects the deployed side's acceptance predicate
to the flat-radius analysis side. -/
theorem CircuitSide.toZkSideAt_accept_iff
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ) (hradius : R.params.row.e + R.params.row.g ≤ radius)
    (hcard : ∀ σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc,
      Fintype.card (sideLiftAt S radius σ) ≤ R.cardCand)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) :
    ZkLayerStepAccepts .accepted .start
      (steps (nl := R.params.nl) (w := R.params.rounds)
        ((S.toZkSideAt radius hradius hcard).V σ)
        ((S.toZkSideAt radius hradius hcard).LD σ) ms) tape ↔
    ZkLayerStepAccepts .accepted .start
      (steps (nl := R.params.nl) (w := R.params.rounds)
        (S.toSide.toZkSide.V σ) (S.toSide.toZkSide.LD σ) ms) tape := by
  rfl

/-- A deployed compiled-side acceptance with an explained Merkle opening
accepts on the same verifier tape at any certified analysis radius. -/
theorem CircuitSide.toZkSideAt_acceptsDH
    (Hside : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ) (hradius : R.params.row.e + R.params.row.g ≤ radius)
    (hcard : ∀ σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc,
      Fintype.card (sideLiftAt Hside radius σ) ≤ R.cardCand)
    {Pt Out : Type} [DecidableEq Pt]
    {tA N Lsch fc TM : ℕ}
    (Ssetup : Bcs.TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N Lsch)
    (check : Out → Merkle.RandomOracle.Tree Enc D Unit fc)
    (rootOf : Out → D)
    (hroot : ∀ out, rootOfKey (Ssetup.keyOut out) = rootOf out)
    (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt
      (Col F R.params.nw R.params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (sl : (Fin Lsch → C) →
      Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ro : Pt → C)
    (hacc : Hside.toSide.acceptsDH Ssetup check rootOf msgOf claimOf
      avOf pubOf sl mt ro)
    (hexp : Ssetup.Explains dec rootOfKey claimOf mt ro) :
    ZkLayerStepAccepts .accepted .start
      (steps (nl := R.params.nl) (w := R.params.rounds)
        ((Hside.toZkSideAt radius hradius hcard).V
          (Lfzk.NizkDeployedHashTwoField.sideCtx Ssetup avOf pubOf mt ro))
        ((Hside.toZkSideAt radius hradius hcard).LD
          (Lfzk.NizkDeployedHashTwoField.sideCtx Ssetup avOf pubOf mt ro))
        (msgOf (Ssetup.proof mt ro)))
      (sl (Ssetup.challenges mt ro)) := by
  apply (Hside.toZkSideAt_accept_iff radius hradius hcard
    (Lfzk.NizkDeployedHashTwoField.sideCtx Ssetup avOf pubOf mt ro)
    (msgOf (Ssetup.proof mt ro)) (sl (Ssetup.challenges mt ro))).mpr
  exact Hside.toSide.hrightDH_of_accepts Ssetup check rootOf hroot
    msgOf claimOf avOf pubOf sl mt ro hacc hexp

/-- The enlarged side extracts the committed witness of a satisfying
candidate at the certificate's actual radius. -/
theorem CircuitSide.toZkSideAt_good
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ) (hradius : R.params.row.e + R.params.row.g ≤ radius)
    (hcard : ∀ σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc,
      Fintype.card (sideLiftAt S radius σ) ≤ R.cardCand)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (a : Fin S.c.ninp → F) :
    (S.toZkSideAt radius hradius hcard).Good σ a ↔
      ∃ ℓ : sideLiftAt S radius σ,
        S.c.Satisfied (S.pubIn σ.2.1 σ.2.2)
          (asgAt S.pl radius ℓ).1 ∧
        (asgAt S.pl radius ℓ).1 = a := Iff.rfl

/-- Every satisfying witness found by the deployed extraction radius is
also found at a larger analysis radius, with the same decoded assignment. -/
theorem CircuitSide.toZkSideAt_good_of_deployed
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ) (hradius : R.params.row.e + R.params.row.g ≤ radius)
    (hcard : ∀ σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc,
      Fintype.card (sideLiftAt S radius σ) ≤ R.cardCand)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (a : Fin S.c.ninp → F)
    (h : S.toSide.toZkSide.Good σ a) :
    (S.toZkSideAt radius hradius hcard).Good σ a := by
  obtain ⟨ℓ, hs, heq⟩ := h
  refine ⟨ℓ.widen hradius, ?_, ?_⟩
  · change S.c.Satisfied (S.pubIn σ.2.1 σ.2.2)
      (asgAt S.pl radius (ℓ.widen hradius)).1
    rw [ZkLigeroV1.asgAt_widen]
    exact hs
  · change (asgAt S.pl radius (ℓ.widen hradius)).1 = a
    rw [ZkLigeroV1.asgAt_widen]
    exact heq

/-- A MAC-row fact stated for every satisfying circuit witness transfers to
the enlarged extraction radius.  A premise restricted to the old lift list
would not suffice here: the analysis radius changes the candidate set. -/
theorem CircuitSide.toZkSideAt_good_property
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ) (hradius : R.params.row.e + R.params.row.g ≤ radius)
    (hcard : ∀ σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc,
      Fintype.card (sideLiftAt S radius σ) ≤ R.cardCand)
    (P : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc →
      (Fin S.c.ninp → F) → Prop)
    (hrow : ∀ σ a, S.c.Satisfied (S.pubIn σ.2.1 σ.2.2) a → P σ a)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (a : Fin S.c.ninp → F)
    (h : (S.toZkSideAt radius hradius hcard).Good σ a) : P σ a := by
  obtain ⟨ℓ, hs, rfl⟩ :=
    (S.toZkSideAt_good radius hradius hcard σ a).mp h
  exact hrow σ _ hs

/-- A property of every satisfying circuit assignment holds for every
deployed-radius extraction candidate.  The enlarged-radius analogue above
uses the same circuit fact. -/
theorem CircuitSide.toSide_good_property
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (P : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc →
      (Fin S.c.ninp → F) → Prop)
    (hrow : ∀ σ a, S.c.Satisfied (S.pubIn σ.2.1 σ.2.2) a → P σ a)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (a : Fin S.c.ninp → F)
    (h : S.toSide.Good σ a) : P σ a := by
  obtain ⟨ℓ, hs, rfl⟩ := (S.toSide_good σ a).mp h
  exact hrow σ _ hs

/-- The MAC candidates at an analysis radius are fixed by the commitment
context, before the key answer.  This is the list appropriate to the
enlarged-radius extractor; the verifier itself remains unchanged. -/
noncomputable def CircuitSide.candsAt
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ) (κ : (D × D) × List (Enc × D)) :
    Finset (Fin S.c.ninp → F) :=
  univ.image fun ℓ : SchemeLiftCandidate
      (R.params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR))
      (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec
        (rootOfKey κ.1, κ.2)) radius =>
    (asgAt S.pl radius ℓ).1

/-- The new key-point list has the same checked cardinality as the enlarged
lift list, with no additional witness multiplicity. -/
theorem CircuitSide.candsAt_card_le
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ)
    (hcard : ∀ κ : (D × D) × List (Enc × D),
      Fintype.card (SchemeLiftCandidate
        (R.params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR))
        (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec
          (rootOfKey κ.1, κ.2)) radius) ≤ R.cardCand)
    (κ : (D × D) × List (Enc × D)) :
    (S.candsAt radius κ).card ≤ R.cardCand :=
  card_image_le.trans ((card_univ.trans_le (hcard κ)))

/-- A side certificate uniform over public inputs also bounds the candidate
set fixed at each commitment context. -/
theorem CircuitSide.candsAt_card_le_of_side [Nonempty C] [Nonempty X]
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ)
    (hcard : ∀ σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc,
      Fintype.card (sideLiftAt S radius σ) ≤ R.cardCand)
    (κ : (D × D) × List (Enc × D)) :
    (S.candsAt radius κ).card ≤ R.cardCand := by
  apply S.candsAt_card_le radius (fun κ' => ?_) κ
  let σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc :=
    (κ', Classical.choice inferInstance, Classical.choice inferInstance)
  exact hcard σ

/-- Every satisfying enlarged-radius lift is included in the committed
candidate list used by the MAC key collision count. -/
theorem CircuitSide.good_mem_candsAt
    (S : CircuitSide R hR hr logv C F Msg M nt nlin X dec rootOfKey)
    (radius : ℕ) (hradius : R.params.row.e + R.params.row.g ≤ radius)
    (hcard : ∀ σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc,
      Fintype.card (sideLiftAt S radius σ) ≤ R.cardCand)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (a : Fin S.c.ninp → F)
    (h : (S.toZkSideAt radius hradius hcard).Good σ a) :
    a ∈ S.candsAt radius σ.1 := by
  obtain ⟨ℓ, _, rfl⟩ := h
  exact mem_image_of_mem _ (mem_univ ℓ)

end Lfzk.CompiledZk
