import Lfzk.CompiledZkRadius
import Lfzk.FlatV1NoSat
import Lfzk.RbrZkFlatSide
import examples.Ligero.Longfellow.OptimizedIOPCertificates

/-!
# Checked flat V1 radii for the deployed v7 hash circuits

This separate target imports the expensive optimized Hahn certificates.  It
connects their larger analysis radii and list bounds to the committed lift
lists of the deployed circuit sides.  Routine Longfellow builds need not
replay those numerical checks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace Lfzk.CompiledZk.FlatV7Radius

open Merkle.MH LigeroFamily Lfzk.CompiledZk Lfzk.CertifiedV1 Lfzk.ZkLigeroV1
  Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.CompiledLongfellowAdaptive
  Ligero.Examples.Grid.LongfellowProfiledExtraction
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F]
variable {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D]
  [DecidableEq Enc] [Inhabited Salt]
variable {X : Type}

section Hash1

variable {codec : Codec Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}

/-- At the optimized hash1 radius, the actual committed candidate list
still has at most the deployed row's two candidates. -/
theorem v7Hash1_flat_lift_card {logv : ℕ}
    (S : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) :
    Fintype.card (sideLiftAt S
      (Optimized.v7Hash1_v1.certificate.e +
        Optimized.v7Hash1_v1.certificate.g) σ) ≤ v7Hash1.cardCand := by
  have hdim : Optimized.v7Hash1_v1.certificate.openings + v7Hash1.params.q =
      Optimized.v7Hash1_v1.certificate.k := by decide
  have hkn : Optimized.v7Hash1_v1.certificate.openings + v7Hash1.params.q ≤
      Optimized.v7Hash1_v1.certificate.n := by decide
  have hfield : Fintype.card F = Optimized.v7Hash1_v1.certificate.fieldSize := S.hF
  have hlist := Result.v1_lift_card_le Optimized.v7Hash1_v1
    Optimized.v7Hash1_v1_parameters hfield hdim S.dom hkn
    (extOracle nlin nt (Row.rowValid v7Hash1_valid) S.dom
      (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
      (rootOfKey σ.1.1, σ.1.2))
  have hcode : Optimized.v7Hash1_v1.code S.dom hkn =
      v7Hash1.params.row.code (Row.rowValid v7Hash1_valid) S.dom
        (Row.hkrow v7Hash1_valid) := by
    rfl
  have hside :
      Fintype.card (sideLiftAt S
        (Optimized.v7Hash1_v1.certificate.e +
          Optimized.v7Hash1_v1.certificate.g) σ) ≤
        Optimized.v7Hash1_v1.certificate.listSize := by
    have htype :
        SchemeLiftCandidate (Optimized.v7Hash1_v1.code S.dom hkn)
          (extOracle nlin nt (Row.rowValid v7Hash1_valid) S.dom
            (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          (Optimized.v7Hash1_v1.certificate.e +
            Optimized.v7Hash1_v1.certificate.g) =
        sideLiftAt S
          (Optimized.v7Hash1_v1.certificate.e +
            Optimized.v7Hash1_v1.certificate.g) σ := by
      rw [sideLiftAt, ← hcode]
      rfl
    calc
      _ = Fintype.card (SchemeLiftCandidate
          (Optimized.v7Hash1_v1.code S.dom hkn)
          (extOracle nlin nt (Row.rowValid v7Hash1_valid) S.dom
            (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          (Optimized.v7Hash1_v1.certificate.e +
            Optimized.v7Hash1_v1.certificate.g)) :=
          (Fintype.card_congr (Equiv.cast htype)).symm
      _ ≤ _ := hlist
  have htwo := Optimized.v7Hash_v1_flat_listSize_two.1
  exact hside.trans (htwo.trans_eq (by decide : (2 : ℕ) = v7Hash1.cardCand))

/-- The deployed hash1 circuit with its field proof run against the flat
certificate's larger candidate list. -/
noncomputable def v7Hash1_flatSide {logv : ℕ}
    (S : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey) :=
  S.toZkSideAt
    (Optimized.v7Hash1_v1.certificate.e + Optimized.v7Hash1_v1.certificate.g)
    (by decide) (v7Hash1_flat_lift_card S)

/-- The optimized hash1 extractor's committed MAC list still contains at
most two witnesses, even at its larger checked radius. -/
theorem v7Hash1_flat_cands_card_le [Nonempty C] [Nonempty X] {logv : ℕ}
    (S : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (κ : (D × D) × List (Enc × D)) :
    (S.candsAt
      (Optimized.v7Hash1_v1.certificate.e + Optimized.v7Hash1_v1.certificate.g)
      κ).card ≤ v7Hash1.cardCand :=
  S.candsAt_card_le_of_side _ (v7Hash1_flat_lift_card S) κ

/-- Every satisfying candidate extracted at the optimized radius is in
the commitment-fixed MAC list charged at the key answer. -/
theorem v7Hash1_flat_good_mem_cands {logv : ℕ}
    (S : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (a : Fin S.c.ninp → F)
    (h : (v7Hash1_flatSide S).Good σ a) :
    a ∈ S.candsAt
      (Optimized.v7Hash1_v1.certificate.e + Optimized.v7Hash1_v1.certificate.g)
      σ.1 :=
  S.good_mem_candsAt _ (by decide) (v7Hash1_flat_lift_card S) σ a h

/-- Enlarging the analysis lift list leaves the deployed query test exactly
the same V1 policy on the committed oracle. -/
theorem v7Hash1_flatSide_accepting {logv : ℕ}
    (S : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) :
    ((v7Hash1_flatSide S).LD σ).accepting =
      accZ (Row.rowValid v7Hash1_valid) S.dom
        (Row.hkrow v7Hash1_valid) S.pl nlin
        (extOracle nlin nt (Row.rowValid v7Hash1_valid) S.dom
          (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
          (rootOfKey σ.1.1, σ.1.2)) S.respOf := by
  exact (S.toSide.LD_acc σ)

/-- The enlarged circuit side's no-satisfying-lift predicate is exactly the
premise of the checked flat V1 certificate at the same radius. -/
theorem v7Hash1_noSat_at_certificate {logv : ℕ}
    (S : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (sys : LigeroSystem S.c.ninp M F)
    (hkn : Optimized.v7Hash1_v1.certificate.openings + v7Hash1.params.q ≤
      Optimized.v7Hash1_v1.certificate.n)
    (hn : NoSat (fun ℓ : sideLiftAt S
      (Optimized.v7Hash1_v1.certificate.e +
        Optimized.v7Hash1_v1.certificate.g) σ =>
        asgAt S.pl
          (Optimized.v7Hash1_v1.certificate.e +
            Optimized.v7Hash1_v1.certificate.g) ℓ) sys) :
    NoSat (fun ℓ : SchemeLiftCandidate
      (Optimized.v7Hash1_v1.code S.dom hkn)
      (extOracle nlin nt (Row.rowValid v7Hash1_valid) S.dom
        (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
        (rootOfKey σ.1.1, σ.1.2))
      (Optimized.v7Hash1_v1.certificate.e +
        Optimized.v7Hash1_v1.certificate.g) =>
        Encode.decode S.pl ℓ.decodedMessages) sys := by
  change NoSat (fun ℓ : sideLiftAt S
    (Optimized.v7Hash1_v1.certificate.e +
      Optimized.v7Hash1_v1.certificate.g) σ =>
      asgAt S.pl
        (Optimized.v7Hash1_v1.certificate.e +
          Optimized.v7Hash1_v1.certificate.g) ℓ) sys
  exact hn

/-- The optimized hash1 V1 certificate bounds the two fresh raw answers at
any built system for which the enlarged side has no satisfying lift. -/
theorem v7Hash1_flat_pair_bound [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (sys : LigeroSystem S.c.ninp M F)
    (msg : Msg)
    (hf : Fits (S.Vc σ.2.1 σ.2.2) sys)
    (hn : NoSat (fun ℓ : sideLiftAt S
      (Optimized.v7Hash1_v1.certificate.e +
        Optimized.v7Hash1_v1.certificate.g) σ =>
        asgAt S.pl
          (Optimized.v7Hash1_v1.certificate.e +
            Optimized.v7Hash1_v1.certificate.g) ℓ) sys) :
    ((Finset.univ.filter fun p : C × C =>
      (SchemeVerifier.policy
        (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (nw := v7Hash1.params.nw) (nq := v7Hash1.params.nq)
        (repetitions := 1)
        (Optimized.v7Hash1_v1.code S.dom (by decide))
        Ligero.V1.scheme).accepts
        (Encode.encodeLig S.pl nlin sys)
        ((S.Vc σ.2.1 σ.2.2).decodeChal p.1)
        (S.respOf msg)
        ((S.Vc σ.2.1 σ.2.2).decodeQuery p.2)
        (openSchemeOracle
          (extOracle nlin nt (Row.rowValid v7Hash1_valid) S.dom
            (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          ((S.Vc σ.2.1 σ.2.2).decodeQuery p.2))).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2 ≤ (1 : ℚ) / 2 ^ 125 := by
  have hdim : Optimized.v7Hash1_v1.certificate.openings + v7Hash1.params.q =
      Optimized.v7Hash1_v1.certificate.k := by decide
  have hkn : Optimized.v7Hash1_v1.certificate.openings + v7Hash1.params.q ≤
      Optimized.v7Hash1_v1.certificate.n := by decide
  have hfield : Fintype.card F = Optimized.v7Hash1_v1.certificate.fieldSize := S.hF
  have hno := v7Hash1_noSat_at_certificate S σ sys hkn hn
  have hlin : sys.linear.length ≤ nlin := by
    simpa only [Fits, S.hnlin σ.2.1 σ.2.2] using hf.1
  have hquad : sys.quad.length ≤ nt := by
    simpa only [Fits, S.hnt σ.2.1 σ.2.2] using hf.2
  exact Result.v1_hash_pair_acceptance_le_target Optimized.v7Hash1_v1
    Optimized.v7Hash1_v1_parameters (by rfl) hfield hdim S.dom hkn
    (Row.coreRows v7Hash1_valid) S.pl
    (extOracle nlin nt (Row.rowValid v7Hash1_valid) S.dom
      (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
      (rootOfKey σ.1.1, σ.1.2))
    sys hlin hquad hno Optimized.v7Hash1_v1_bound
    (S.Vc σ.2.1 σ.2.2).decodeChal
    (S.Vc σ.2.1 σ.2.2).decodeQuery
    (fun _ => S.respOf msg) S.kchal S.kq
    (S.hbalChal σ.2.1 σ.2.2) (S.hbalQuery σ.2.1 σ.2.2)
    S.hkchal S.hkq

/-- The terminal event of the enlarged hash1 circuit side is bounded by
the response-uniform flat V1 certificate, conditional on every field prefix. -/
theorem v7Hash1_terminalPair_ratio_le [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (ms : ℕ → Msg) :
    let T := v7Hash1_flatSide S
    ∀ pref : Fin
      (Lfzk.Rounds.Role.layerBase v7Hash1.params.rounds v7Hash1.params.nl + 1) → C,
      ((Finset.univ.filter fun pair : C × C =>
        Lfzk.RbrZkFlat.terminalPairAccept
          (H := T.H σ) (Sat := T.Sat σ)
          (T.LD σ) ms pref pair.1 pair.2).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ (1 : ℚ) / 2 ^ 125 := by
  let T := v7Hash1_flatSide S
  apply Lfzk.RbrZkFlat.ZkSide.terminalPairAccept_ratio_le_of_built
    T σ ms ((1 : ℚ) / 2 ^ 125) (by positivity)
  intro pref sys _ hf hn
  have hpair := v7Hash1_flat_pair_bound S σ sys
    (ms (Lfzk.Rounds.Role.layerBase v7Hash1.params.rounds v7Hash1.params.nl + 2))
    hf hn
  have hcode : Optimized.v7Hash1_v1.code S.dom (by decide) =
      v7Hash1.params.row.code (Row.rowValid v7Hash1_valid) S.dom
        (Row.hkrow v7Hash1_valid) := by rfl
  have hV : (v7Hash1_flatSide S).V σ = S.Vc σ.2.1 σ.2.2 := rfl
  convert hpair using 1
  congr 1
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [v7Hash1_flatSide_accepting S σ]
  simp only [accZ, acceptingR, LigeroV1LayerStep.code, stmtOf,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hV, ← hcode]
  rfl

/-- Hash1's interactive extraction-failure term pays the ordinary field
rounds plus the flat 125-bit V1 terminal envelope. -/
theorem v7Hash1_flat_iop_extraction_le [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (ms : ℕ → Msg)
    (hfalse : ∀ ℓ : (v7Hash1_flatSide S).Lift σ,
      ¬ (v7Hash1_flatSide S).Sat σ ℓ) :
    ((Finset.univ.filter fun tape : Fin
      (Lfzk.Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds) → C =>
        ZkLayerStepAccepts .accepted .start
          (steps (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
            ((v7Hash1_flatSide S).V σ)
            ((v7Hash1_flatSide S).LD σ) ms) tape).card : ℚ) /
      (Fintype.card C : ℚ) ^
        Lfzk.Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds ≤
      (v7Hash1.cardCand : ℚ) * Lfzk.NizkZk.zkFieldDensity v7Hash1 logv +
        (1 : ℚ) / 2 ^ 125 := by
  exact Lfzk.RbrZkFlat.ZkSide.accepted_ratio_le_field_plus_terminal_density
    (v7Hash1_flatSide S) S.hF σ ms hfalse ((1 : ℚ) / 2 ^ 125)
    (v7Hash1_terminalPair_ratio_le S σ ms)

end Hash1

section Hash2

variable {codec : Codec Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}

/-- At the optimized hash2 radius, the actual committed candidate list
still has at most the deployed row's two candidates. -/
theorem v7Hash2_flat_lift_card {logv : ℕ}
    (S : CircuitSide v7Hash2 v7Hash2_valid v7Hash2_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) :
    Fintype.card (sideLiftAt S
      (Optimized.v7Hash2_v1.certificate.e +
        Optimized.v7Hash2_v1.certificate.g) σ) ≤ v7Hash2.cardCand := by
  have hdim : Optimized.v7Hash2_v1.certificate.openings + v7Hash2.params.q =
      Optimized.v7Hash2_v1.certificate.k := by decide
  have hkn : Optimized.v7Hash2_v1.certificate.openings + v7Hash2.params.q ≤
      Optimized.v7Hash2_v1.certificate.n := by decide
  have hfield : Fintype.card F = Optimized.v7Hash2_v1.certificate.fieldSize := S.hF
  have hlist := Result.v1_lift_card_le Optimized.v7Hash2_v1
    Optimized.v7Hash2_v1_parameters hfield hdim S.dom hkn
    (extOracle nlin nt (Row.rowValid v7Hash2_valid) S.dom
      (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec
      (rootOfKey σ.1.1, σ.1.2))
  have hcode : Optimized.v7Hash2_v1.code S.dom hkn =
      v7Hash2.params.row.code (Row.rowValid v7Hash2_valid) S.dom
        (Row.hkrow v7Hash2_valid) := by
    rfl
  have hside :
      Fintype.card (sideLiftAt S
        (Optimized.v7Hash2_v1.certificate.e +
          Optimized.v7Hash2_v1.certificate.g) σ) ≤
        Optimized.v7Hash2_v1.certificate.listSize := by
    have htype :
        SchemeLiftCandidate (Optimized.v7Hash2_v1.code S.dom hkn)
          (extOracle nlin nt (Row.rowValid v7Hash2_valid) S.dom
            (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          (Optimized.v7Hash2_v1.certificate.e +
            Optimized.v7Hash2_v1.certificate.g) =
        sideLiftAt S
          (Optimized.v7Hash2_v1.certificate.e +
            Optimized.v7Hash2_v1.certificate.g) σ := by
      rw [sideLiftAt, ← hcode]
      rfl
    calc
      _ = Fintype.card (SchemeLiftCandidate
          (Optimized.v7Hash2_v1.code S.dom hkn)
          (extOracle nlin nt (Row.rowValid v7Hash2_valid) S.dom
            (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          (Optimized.v7Hash2_v1.certificate.e +
            Optimized.v7Hash2_v1.certificate.g)) :=
          (Fintype.card_congr (Equiv.cast htype)).symm
      _ ≤ _ := hlist
  have htwo := Optimized.v7Hash_v1_flat_listSize_two.2.1
  exact hside.trans (htwo.trans_eq (by decide : (2 : ℕ) = v7Hash2.cardCand))

/-- The deployed hash2 circuit analyzed at its flat V1 radius. -/
noncomputable def v7Hash2_flatSide {logv : ℕ}
    (S : CircuitSide v7Hash2 v7Hash2_valid v7Hash2_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey) :=
  S.toZkSideAt
    (Optimized.v7Hash2_v1.certificate.e + Optimized.v7Hash2_v1.certificate.g)
    (by decide) (v7Hash2_flat_lift_card S)

theorem v7Hash2_flat_cands_card_le [Nonempty C] [Nonempty X] {logv : ℕ}
    (S : CircuitSide v7Hash2 v7Hash2_valid v7Hash2_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (κ : (D × D) × List (Enc × D)) :
    (S.candsAt
      (Optimized.v7Hash2_v1.certificate.e + Optimized.v7Hash2_v1.certificate.g)
      κ).card ≤ v7Hash2.cardCand :=
  S.candsAt_card_le_of_side _ (v7Hash2_flat_lift_card S) κ

theorem v7Hash2_flat_good_mem_cands {logv : ℕ}
    (S : CircuitSide v7Hash2 v7Hash2_valid v7Hash2_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (a : Fin S.c.ninp → F)
    (h : (v7Hash2_flatSide S).Good σ a) :
    a ∈ S.candsAt
      (Optimized.v7Hash2_v1.certificate.e + Optimized.v7Hash2_v1.certificate.g)
      σ.1 :=
  S.good_mem_candsAt _ (by decide) (v7Hash2_flat_lift_card S) σ a h

/-- Enlarging the analysis lift list leaves the deployed query test exactly
the same V1 policy on the committed oracle. -/
theorem v7Hash2_flatSide_accepting {logv : ℕ}
    (S : CircuitSide v7Hash2 v7Hash2_valid v7Hash2_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) :
    ((v7Hash2_flatSide S).LD σ).accepting =
      accZ (Row.rowValid v7Hash2_valid) S.dom
        (Row.hkrow v7Hash2_valid) S.pl nlin
        (extOracle nlin nt (Row.rowValid v7Hash2_valid) S.dom
          (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec
          (rootOfKey σ.1.1, σ.1.2)) S.respOf := by
  exact (S.toSide.LD_acc σ)

/-- The enlarged circuit side's no-satisfying-lift predicate is exactly the
premise of the checked flat V1 certificate at the same radius. -/
theorem v7Hash2_noSat_at_certificate {logv : ℕ}
    (S : CircuitSide v7Hash2 v7Hash2_valid v7Hash2_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (sys : LigeroSystem S.c.ninp M F)
    (hkn : Optimized.v7Hash2_v1.certificate.openings + v7Hash2.params.q ≤
      Optimized.v7Hash2_v1.certificate.n)
    (hn : NoSat (fun ℓ : sideLiftAt S
      (Optimized.v7Hash2_v1.certificate.e +
        Optimized.v7Hash2_v1.certificate.g) σ =>
        asgAt S.pl
          (Optimized.v7Hash2_v1.certificate.e +
            Optimized.v7Hash2_v1.certificate.g) ℓ) sys) :
    NoSat (fun ℓ : SchemeLiftCandidate
      (Optimized.v7Hash2_v1.code S.dom hkn)
      (extOracle nlin nt (Row.rowValid v7Hash2_valid) S.dom
        (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec
        (rootOfKey σ.1.1, σ.1.2))
      (Optimized.v7Hash2_v1.certificate.e +
        Optimized.v7Hash2_v1.certificate.g) =>
        Encode.decode S.pl ℓ.decodedMessages) sys := by
  change NoSat (fun ℓ : sideLiftAt S
    (Optimized.v7Hash2_v1.certificate.e +
      Optimized.v7Hash2_v1.certificate.g) σ =>
      asgAt S.pl
        (Optimized.v7Hash2_v1.certificate.e +
          Optimized.v7Hash2_v1.certificate.g) ℓ) sys
  exact hn

/-- The optimized hash2 V1 certificate bounds the two fresh raw answers at
any built system for which the enlarged side has no satisfying lift. -/
theorem v7Hash2_flat_pair_bound [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash2 v7Hash2_valid v7Hash2_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (sys : LigeroSystem S.c.ninp M F)
    (msg : Msg)
    (hf : Fits (S.Vc σ.2.1 σ.2.2) sys)
    (hn : NoSat (fun ℓ : sideLiftAt S
      (Optimized.v7Hash2_v1.certificate.e +
        Optimized.v7Hash2_v1.certificate.g) σ =>
        asgAt S.pl
          (Optimized.v7Hash2_v1.certificate.e +
            Optimized.v7Hash2_v1.certificate.g) ℓ) sys) :
    ((Finset.univ.filter fun p : C × C =>
      (SchemeVerifier.policy
        (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (nw := v7Hash2.params.nw) (nq := v7Hash2.params.nq)
        (repetitions := 1)
        (Optimized.v7Hash2_v1.code S.dom (by decide))
        Ligero.V1.scheme).accepts
        (Encode.encodeLig S.pl nlin sys)
        ((S.Vc σ.2.1 σ.2.2).decodeChal p.1)
        (S.respOf msg)
        ((S.Vc σ.2.1 σ.2.2).decodeQuery p.2)
        (openSchemeOracle
          (extOracle nlin nt (Row.rowValid v7Hash2_valid) S.dom
            (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          ((S.Vc σ.2.1 σ.2.2).decodeQuery p.2))).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2 ≤ (1 : ℚ) / 2 ^ 125 := by
  have hdim : Optimized.v7Hash2_v1.certificate.openings + v7Hash2.params.q =
      Optimized.v7Hash2_v1.certificate.k := by decide
  have hkn : Optimized.v7Hash2_v1.certificate.openings + v7Hash2.params.q ≤
      Optimized.v7Hash2_v1.certificate.n := by decide
  have hfield : Fintype.card F = Optimized.v7Hash2_v1.certificate.fieldSize := S.hF
  have hno := v7Hash2_noSat_at_certificate S σ sys hkn hn
  have hlin : sys.linear.length ≤ nlin := by
    simpa only [Fits, S.hnlin σ.2.1 σ.2.2] using hf.1
  have hquad : sys.quad.length ≤ nt := by
    simpa only [Fits, S.hnt σ.2.1 σ.2.2] using hf.2
  exact Result.v1_hash_pair_acceptance_le_target Optimized.v7Hash2_v1
    Optimized.v7Hash2_v1_parameters (by rfl) hfield hdim S.dom hkn
    (Row.coreRows v7Hash2_valid) S.pl
    (extOracle nlin nt (Row.rowValid v7Hash2_valid) S.dom
      (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec
      (rootOfKey σ.1.1, σ.1.2))
    sys hlin hquad hno Optimized.v7Hash2_v1_bound
    (S.Vc σ.2.1 σ.2.2).decodeChal
    (S.Vc σ.2.1 σ.2.2).decodeQuery
    (fun _ => S.respOf msg) S.kchal S.kq
    (S.hbalChal σ.2.1 σ.2.2) (S.hbalQuery σ.2.1 σ.2.2)
    S.hkchal S.hkq

/-- The terminal event of the enlarged hash2 circuit side is bounded by
the response-uniform flat V1 certificate, conditional on every field prefix. -/
theorem v7Hash2_terminalPair_ratio_le [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash2 v7Hash2_valid v7Hash2_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (ms : ℕ → Msg) :
    let T := v7Hash2_flatSide S
    ∀ pref : Fin
      (Lfzk.Rounds.Role.layerBase v7Hash2.params.rounds v7Hash2.params.nl + 1) → C,
      ((Finset.univ.filter fun pair : C × C =>
        Lfzk.RbrZkFlat.terminalPairAccept
          (H := T.H σ) (Sat := T.Sat σ)
          (T.LD σ) ms pref pair.1 pair.2).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ (1 : ℚ) / 2 ^ 125 := by
  let T := v7Hash2_flatSide S
  apply Lfzk.RbrZkFlat.ZkSide.terminalPairAccept_ratio_le_of_built
    T σ ms ((1 : ℚ) / 2 ^ 125) (by positivity)
  intro pref sys _ hf hn
  have hpair := v7Hash2_flat_pair_bound S σ sys
    (ms (Lfzk.Rounds.Role.layerBase v7Hash2.params.rounds v7Hash2.params.nl + 2))
    hf hn
  have hcode : Optimized.v7Hash2_v1.code S.dom (by decide) =
      v7Hash2.params.row.code (Row.rowValid v7Hash2_valid) S.dom
        (Row.hkrow v7Hash2_valid) := by rfl
  have hV : (v7Hash2_flatSide S).V σ = S.Vc σ.2.1 σ.2.2 := rfl
  convert hpair using 1
  congr 1
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [v7Hash2_flatSide_accepting S σ]
  simp only [accZ, acceptingR, LigeroV1LayerStep.code, stmtOf,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hV, ← hcode]
  rfl

/-- Hash1's interactive extraction-failure term pays the ordinary field
rounds plus the flat 125-bit V1 terminal envelope. -/
theorem v7Hash2_flat_iop_extraction_le [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash2 v7Hash2_valid v7Hash2_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (ms : ℕ → Msg)
    (hfalse : ∀ ℓ : (v7Hash2_flatSide S).Lift σ,
      ¬ (v7Hash2_flatSide S).Sat σ ℓ) :
    ((Finset.univ.filter fun tape : Fin
      (Lfzk.Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds) → C =>
        ZkLayerStepAccepts .accepted .start
          (steps (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
            ((v7Hash2_flatSide S).V σ)
            ((v7Hash2_flatSide S).LD σ) ms) tape).card : ℚ) /
      (Fintype.card C : ℚ) ^
        Lfzk.Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds ≤
      (v7Hash2.cardCand : ℚ) * Lfzk.NizkZk.zkFieldDensity v7Hash2 logv +
        (1 : ℚ) / 2 ^ 125 := by
  exact Lfzk.RbrZkFlat.ZkSide.accepted_ratio_le_field_plus_terminal_density
    (v7Hash2_flatSide S) S.hF σ ms hfalse ((1 : ℚ) / 2 ^ 125)
    (v7Hash2_terminalPair_ratio_le S σ ms)

end Hash2

section Hash3

variable {codec : Codec Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}

/-- At the optimized hash3 radius, the actual committed candidate list
still has at most the deployed row's two candidates. -/
theorem v7Hash3_flat_lift_card {logv : ℕ}
    (S : CircuitSide v7Hash3 v7Hash3_valid v7Hash3_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) :
    Fintype.card (sideLiftAt S
      (Optimized.v7Hash3_v1.certificate.e +
        Optimized.v7Hash3_v1.certificate.g) σ) ≤ v7Hash3.cardCand := by
  have hdim : Optimized.v7Hash3_v1.certificate.openings + v7Hash3.params.q =
      Optimized.v7Hash3_v1.certificate.k := by decide
  have hkn : Optimized.v7Hash3_v1.certificate.openings + v7Hash3.params.q ≤
      Optimized.v7Hash3_v1.certificate.n := by decide
  have hfield : Fintype.card F = Optimized.v7Hash3_v1.certificate.fieldSize := S.hF
  have hlist := Result.v1_lift_card_le Optimized.v7Hash3_v1
    Optimized.v7Hash3_v1_parameters hfield hdim S.dom hkn
    (extOracle nlin nt (Row.rowValid v7Hash3_valid) S.dom
      (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec
      (rootOfKey σ.1.1, σ.1.2))
  have hcode : Optimized.v7Hash3_v1.code S.dom hkn =
      v7Hash3.params.row.code (Row.rowValid v7Hash3_valid) S.dom
        (Row.hkrow v7Hash3_valid) := by
    rfl
  have hside :
      Fintype.card (sideLiftAt S
        (Optimized.v7Hash3_v1.certificate.e +
          Optimized.v7Hash3_v1.certificate.g) σ) ≤
        Optimized.v7Hash3_v1.certificate.listSize := by
    have htype :
        SchemeLiftCandidate (Optimized.v7Hash3_v1.code S.dom hkn)
          (extOracle nlin nt (Row.rowValid v7Hash3_valid) S.dom
            (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          (Optimized.v7Hash3_v1.certificate.e +
            Optimized.v7Hash3_v1.certificate.g) =
        sideLiftAt S
          (Optimized.v7Hash3_v1.certificate.e +
            Optimized.v7Hash3_v1.certificate.g) σ := by
      rw [sideLiftAt, ← hcode]
      rfl
    calc
      _ = Fintype.card (SchemeLiftCandidate
          (Optimized.v7Hash3_v1.code S.dom hkn)
          (extOracle nlin nt (Row.rowValid v7Hash3_valid) S.dom
            (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          (Optimized.v7Hash3_v1.certificate.e +
            Optimized.v7Hash3_v1.certificate.g)) :=
          (Fintype.card_congr (Equiv.cast htype)).symm
      _ ≤ _ := hlist
  have htwo := Optimized.v7Hash_v1_flat_listSize_two.2.2.1
  exact hside.trans (htwo.trans_eq (by decide : (2 : ℕ) = v7Hash3.cardCand))

/-- The deployed hash3 circuit analyzed at its flat V1 radius. -/
noncomputable def v7Hash3_flatSide {logv : ℕ}
    (S : CircuitSide v7Hash3 v7Hash3_valid v7Hash3_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey) :=
  S.toZkSideAt
    (Optimized.v7Hash3_v1.certificate.e + Optimized.v7Hash3_v1.certificate.g)
    (by decide) (v7Hash3_flat_lift_card S)

theorem v7Hash3_flat_cands_card_le [Nonempty C] [Nonempty X] {logv : ℕ}
    (S : CircuitSide v7Hash3 v7Hash3_valid v7Hash3_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (κ : (D × D) × List (Enc × D)) :
    (S.candsAt
      (Optimized.v7Hash3_v1.certificate.e + Optimized.v7Hash3_v1.certificate.g)
      κ).card ≤ v7Hash3.cardCand :=
  S.candsAt_card_le_of_side _ (v7Hash3_flat_lift_card S) κ

theorem v7Hash3_flat_good_mem_cands {logv : ℕ}
    (S : CircuitSide v7Hash3 v7Hash3_valid v7Hash3_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (a : Fin S.c.ninp → F)
    (h : (v7Hash3_flatSide S).Good σ a) :
    a ∈ S.candsAt
      (Optimized.v7Hash3_v1.certificate.e + Optimized.v7Hash3_v1.certificate.g)
      σ.1 :=
  S.good_mem_candsAt _ (by decide) (v7Hash3_flat_lift_card S) σ a h

/-- Enlarging the analysis lift list leaves the deployed query test exactly
the same V1 policy on the committed oracle. -/
theorem v7Hash3_flatSide_accepting {logv : ℕ}
    (S : CircuitSide v7Hash3 v7Hash3_valid v7Hash3_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) :
    ((v7Hash3_flatSide S).LD σ).accepting =
      accZ (Row.rowValid v7Hash3_valid) S.dom
        (Row.hkrow v7Hash3_valid) S.pl nlin
        (extOracle nlin nt (Row.rowValid v7Hash3_valid) S.dom
          (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec
          (rootOfKey σ.1.1, σ.1.2)) S.respOf := by
  exact (S.toSide.LD_acc σ)

/-- The enlarged circuit side's no-satisfying-lift predicate is exactly the
premise of the checked flat V1 certificate at the same radius. -/
theorem v7Hash3_noSat_at_certificate {logv : ℕ}
    (S : CircuitSide v7Hash3 v7Hash3_valid v7Hash3_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (sys : LigeroSystem S.c.ninp M F)
    (hkn : Optimized.v7Hash3_v1.certificate.openings + v7Hash3.params.q ≤
      Optimized.v7Hash3_v1.certificate.n)
    (hn : NoSat (fun ℓ : sideLiftAt S
      (Optimized.v7Hash3_v1.certificate.e +
        Optimized.v7Hash3_v1.certificate.g) σ =>
        asgAt S.pl
          (Optimized.v7Hash3_v1.certificate.e +
            Optimized.v7Hash3_v1.certificate.g) ℓ) sys) :
    NoSat (fun ℓ : SchemeLiftCandidate
      (Optimized.v7Hash3_v1.code S.dom hkn)
      (extOracle nlin nt (Row.rowValid v7Hash3_valid) S.dom
        (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec
        (rootOfKey σ.1.1, σ.1.2))
      (Optimized.v7Hash3_v1.certificate.e +
        Optimized.v7Hash3_v1.certificate.g) =>
        Encode.decode S.pl ℓ.decodedMessages) sys := by
  change NoSat (fun ℓ : sideLiftAt S
    (Optimized.v7Hash3_v1.certificate.e +
      Optimized.v7Hash3_v1.certificate.g) σ =>
      asgAt S.pl
        (Optimized.v7Hash3_v1.certificate.e +
          Optimized.v7Hash3_v1.certificate.g) ℓ) sys
  exact hn

/-- The optimized hash3 V1 certificate bounds the two fresh raw answers at
any built system for which the enlarged side has no satisfying lift. -/
theorem v7Hash3_flat_pair_bound [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash3 v7Hash3_valid v7Hash3_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (sys : LigeroSystem S.c.ninp M F)
    (msg : Msg)
    (hf : Fits (S.Vc σ.2.1 σ.2.2) sys)
    (hn : NoSat (fun ℓ : sideLiftAt S
      (Optimized.v7Hash3_v1.certificate.e +
        Optimized.v7Hash3_v1.certificate.g) σ =>
        asgAt S.pl
          (Optimized.v7Hash3_v1.certificate.e +
            Optimized.v7Hash3_v1.certificate.g) ℓ) sys) :
    ((Finset.univ.filter fun p : C × C =>
      (SchemeVerifier.policy
        (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (nw := v7Hash3.params.nw) (nq := v7Hash3.params.nq)
        (repetitions := 1)
        (Optimized.v7Hash3_v1.code S.dom (by decide))
        Ligero.V1.scheme).accepts
        (Encode.encodeLig S.pl nlin sys)
        ((S.Vc σ.2.1 σ.2.2).decodeChal p.1)
        (S.respOf msg)
        ((S.Vc σ.2.1 σ.2.2).decodeQuery p.2)
        (openSchemeOracle
          (extOracle nlin nt (Row.rowValid v7Hash3_valid) S.dom
            (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          ((S.Vc σ.2.1 σ.2.2).decodeQuery p.2))).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2 ≤ (1 : ℚ) / 2 ^ 125 := by
  have hdim : Optimized.v7Hash3_v1.certificate.openings + v7Hash3.params.q =
      Optimized.v7Hash3_v1.certificate.k := by decide
  have hkn : Optimized.v7Hash3_v1.certificate.openings + v7Hash3.params.q ≤
      Optimized.v7Hash3_v1.certificate.n := by decide
  have hfield : Fintype.card F = Optimized.v7Hash3_v1.certificate.fieldSize := S.hF
  have hno := v7Hash3_noSat_at_certificate S σ sys hkn hn
  have hlin : sys.linear.length ≤ nlin := by
    simpa only [Fits, S.hnlin σ.2.1 σ.2.2] using hf.1
  have hquad : sys.quad.length ≤ nt := by
    simpa only [Fits, S.hnt σ.2.1 σ.2.2] using hf.2
  exact Result.v1_hash_pair_acceptance_le_target Optimized.v7Hash3_v1
    Optimized.v7Hash3_v1_parameters (by rfl) hfield hdim S.dom hkn
    (Row.coreRows v7Hash3_valid) S.pl
    (extOracle nlin nt (Row.rowValid v7Hash3_valid) S.dom
      (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec
      (rootOfKey σ.1.1, σ.1.2))
    sys hlin hquad hno Optimized.v7Hash3_v1_bound
    (S.Vc σ.2.1 σ.2.2).decodeChal
    (S.Vc σ.2.1 σ.2.2).decodeQuery
    (fun _ => S.respOf msg) S.kchal S.kq
    (S.hbalChal σ.2.1 σ.2.2) (S.hbalQuery σ.2.1 σ.2.2)
    S.hkchal S.hkq

/-- The terminal event of the enlarged hash3 circuit side is bounded by
the response-uniform flat V1 certificate, conditional on every field prefix. -/
theorem v7Hash3_terminalPair_ratio_le [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash3 v7Hash3_valid v7Hash3_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (ms : ℕ → Msg) :
    let T := v7Hash3_flatSide S
    ∀ pref : Fin
      (Lfzk.Rounds.Role.layerBase v7Hash3.params.rounds v7Hash3.params.nl + 1) → C,
      ((Finset.univ.filter fun pair : C × C =>
        Lfzk.RbrZkFlat.terminalPairAccept
          (H := T.H σ) (Sat := T.Sat σ)
          (T.LD σ) ms pref pair.1 pair.2).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ (1 : ℚ) / 2 ^ 125 := by
  let T := v7Hash3_flatSide S
  apply Lfzk.RbrZkFlat.ZkSide.terminalPairAccept_ratio_le_of_built
    T σ ms ((1 : ℚ) / 2 ^ 125) (by positivity)
  intro pref sys _ hf hn
  have hpair := v7Hash3_flat_pair_bound S σ sys
    (ms (Lfzk.Rounds.Role.layerBase v7Hash3.params.rounds v7Hash3.params.nl + 2))
    hf hn
  have hcode : Optimized.v7Hash3_v1.code S.dom (by decide) =
      v7Hash3.params.row.code (Row.rowValid v7Hash3_valid) S.dom
        (Row.hkrow v7Hash3_valid) := by rfl
  have hV : (v7Hash3_flatSide S).V σ = S.Vc σ.2.1 σ.2.2 := rfl
  convert hpair using 1
  congr 1
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [v7Hash3_flatSide_accepting S σ]
  simp only [accZ, acceptingR, LigeroV1LayerStep.code, stmtOf,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hV, ← hcode]
  rfl

/-- Hash1's interactive extraction-failure term pays the ordinary field
rounds plus the flat 125-bit V1 terminal envelope. -/
theorem v7Hash3_flat_iop_extraction_le [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash3 v7Hash3_valid v7Hash3_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (ms : ℕ → Msg)
    (hfalse : ∀ ℓ : (v7Hash3_flatSide S).Lift σ,
      ¬ (v7Hash3_flatSide S).Sat σ ℓ) :
    ((Finset.univ.filter fun tape : Fin
      (Lfzk.Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds) → C =>
        ZkLayerStepAccepts .accepted .start
          (steps (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
            ((v7Hash3_flatSide S).V σ)
            ((v7Hash3_flatSide S).LD σ) ms) tape).card : ℚ) /
      (Fintype.card C : ℚ) ^
        Lfzk.Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds ≤
      (v7Hash3.cardCand : ℚ) * Lfzk.NizkZk.zkFieldDensity v7Hash3 logv +
        (1 : ℚ) / 2 ^ 125 := by
  exact Lfzk.RbrZkFlat.ZkSide.accepted_ratio_le_field_plus_terminal_density
    (v7Hash3_flatSide S) S.hF σ ms hfalse ((1 : ℚ) / 2 ^ 125)
    (v7Hash3_terminalPair_ratio_le S σ ms)

end Hash3

section Hash4

variable {codec : Codec Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}

/-- At the optimized hash4 radius, the actual committed candidate list
still has at most the deployed row's two candidates. -/
theorem v7Hash4_flat_lift_card {logv : ℕ}
    (S : CircuitSide v7Hash4 v7Hash4_valid v7Hash4_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) :
    Fintype.card (sideLiftAt S
      (Optimized.v7Hash4_v1.certificate.e +
        Optimized.v7Hash4_v1.certificate.g) σ) ≤ v7Hash4.cardCand := by
  have hdim : Optimized.v7Hash4_v1.certificate.openings + v7Hash4.params.q =
      Optimized.v7Hash4_v1.certificate.k := by decide
  have hkn : Optimized.v7Hash4_v1.certificate.openings + v7Hash4.params.q ≤
      Optimized.v7Hash4_v1.certificate.n := by decide
  have hfield : Fintype.card F = Optimized.v7Hash4_v1.certificate.fieldSize := S.hF
  have hlist := Result.v1_lift_card_le Optimized.v7Hash4_v1
    Optimized.v7Hash4_v1_parameters hfield hdim S.dom hkn
    (extOracle nlin nt (Row.rowValid v7Hash4_valid) S.dom
      (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec
      (rootOfKey σ.1.1, σ.1.2))
  have hcode : Optimized.v7Hash4_v1.code S.dom hkn =
      v7Hash4.params.row.code (Row.rowValid v7Hash4_valid) S.dom
        (Row.hkrow v7Hash4_valid) := by
    rfl
  have hside :
      Fintype.card (sideLiftAt S
        (Optimized.v7Hash4_v1.certificate.e +
          Optimized.v7Hash4_v1.certificate.g) σ) ≤
        Optimized.v7Hash4_v1.certificate.listSize := by
    have htype :
        SchemeLiftCandidate (Optimized.v7Hash4_v1.code S.dom hkn)
          (extOracle nlin nt (Row.rowValid v7Hash4_valid) S.dom
            (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          (Optimized.v7Hash4_v1.certificate.e +
            Optimized.v7Hash4_v1.certificate.g) =
        sideLiftAt S
          (Optimized.v7Hash4_v1.certificate.e +
            Optimized.v7Hash4_v1.certificate.g) σ := by
      rw [sideLiftAt, ← hcode]
      rfl
    calc
      _ = Fintype.card (SchemeLiftCandidate
          (Optimized.v7Hash4_v1.code S.dom hkn)
          (extOracle nlin nt (Row.rowValid v7Hash4_valid) S.dom
            (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          (Optimized.v7Hash4_v1.certificate.e +
            Optimized.v7Hash4_v1.certificate.g)) :=
          (Fintype.card_congr (Equiv.cast htype)).symm
      _ ≤ _ := hlist
  have htwo := Optimized.v7Hash_v1_flat_listSize_two.2.2.2
  exact hside.trans (htwo.trans_eq (by decide : (2 : ℕ) = v7Hash4.cardCand))

/-- The deployed hash4 circuit analyzed at its flat V1 radius. -/
noncomputable def v7Hash4_flatSide {logv : ℕ}
    (S : CircuitSide v7Hash4 v7Hash4_valid v7Hash4_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey) :=
  S.toZkSideAt
    (Optimized.v7Hash4_v1.certificate.e + Optimized.v7Hash4_v1.certificate.g)
    (by decide) (v7Hash4_flat_lift_card S)

theorem v7Hash4_flat_cands_card_le [Nonempty C] [Nonempty X] {logv : ℕ}
    (S : CircuitSide v7Hash4 v7Hash4_valid v7Hash4_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (κ : (D × D) × List (Enc × D)) :
    (S.candsAt
      (Optimized.v7Hash4_v1.certificate.e + Optimized.v7Hash4_v1.certificate.g)
      κ).card ≤ v7Hash4.cardCand :=
  S.candsAt_card_le_of_side _ (v7Hash4_flat_lift_card S) κ

theorem v7Hash4_flat_good_mem_cands {logv : ℕ}
    (S : CircuitSide v7Hash4 v7Hash4_valid v7Hash4_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (a : Fin S.c.ninp → F)
    (h : (v7Hash4_flatSide S).Good σ a) :
    a ∈ S.candsAt
      (Optimized.v7Hash4_v1.certificate.e + Optimized.v7Hash4_v1.certificate.g)
      σ.1 :=
  S.good_mem_candsAt _ (by decide) (v7Hash4_flat_lift_card S) σ a h

/-- Enlarging the analysis lift list leaves the deployed query test exactly
the same V1 policy on the committed oracle. -/
theorem v7Hash4_flatSide_accepting {logv : ℕ}
    (S : CircuitSide v7Hash4 v7Hash4_valid v7Hash4_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc) :
    ((v7Hash4_flatSide S).LD σ).accepting =
      accZ (Row.rowValid v7Hash4_valid) S.dom
        (Row.hkrow v7Hash4_valid) S.pl nlin
        (extOracle nlin nt (Row.rowValid v7Hash4_valid) S.dom
          (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec
          (rootOfKey σ.1.1, σ.1.2)) S.respOf := by
  exact (S.toSide.LD_acc σ)

/-- The enlarged circuit side's no-satisfying-lift predicate is exactly the
premise of the checked flat V1 certificate at the same radius. -/
theorem v7Hash4_noSat_at_certificate {logv : ℕ}
    (S : CircuitSide v7Hash4 v7Hash4_valid v7Hash4_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (sys : LigeroSystem S.c.ninp M F)
    (hkn : Optimized.v7Hash4_v1.certificate.openings + v7Hash4.params.q ≤
      Optimized.v7Hash4_v1.certificate.n)
    (hn : NoSat (fun ℓ : sideLiftAt S
      (Optimized.v7Hash4_v1.certificate.e +
        Optimized.v7Hash4_v1.certificate.g) σ =>
        asgAt S.pl
          (Optimized.v7Hash4_v1.certificate.e +
            Optimized.v7Hash4_v1.certificate.g) ℓ) sys) :
    NoSat (fun ℓ : SchemeLiftCandidate
      (Optimized.v7Hash4_v1.code S.dom hkn)
      (extOracle nlin nt (Row.rowValid v7Hash4_valid) S.dom
        (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec
        (rootOfKey σ.1.1, σ.1.2))
      (Optimized.v7Hash4_v1.certificate.e +
        Optimized.v7Hash4_v1.certificate.g) =>
        Encode.decode S.pl ℓ.decodedMessages) sys := by
  change NoSat (fun ℓ : sideLiftAt S
    (Optimized.v7Hash4_v1.certificate.e +
      Optimized.v7Hash4_v1.certificate.g) σ =>
      asgAt S.pl
        (Optimized.v7Hash4_v1.certificate.e +
          Optimized.v7Hash4_v1.certificate.g) ℓ) sys
  exact hn

/-- The optimized hash4 V1 certificate bounds the two fresh raw answers at
any built system for which the enlarged side has no satisfying lift. -/
theorem v7Hash4_flat_pair_bound [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash4 v7Hash4_valid v7Hash4_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (sys : LigeroSystem S.c.ninp M F)
    (msg : Msg)
    (hf : Fits (S.Vc σ.2.1 σ.2.2) sys)
    (hn : NoSat (fun ℓ : sideLiftAt S
      (Optimized.v7Hash4_v1.certificate.e +
        Optimized.v7Hash4_v1.certificate.g) σ =>
        asgAt S.pl
          (Optimized.v7Hash4_v1.certificate.e +
            Optimized.v7Hash4_v1.certificate.g) ℓ) sys) :
    ((Finset.univ.filter fun p : C × C =>
      (SchemeVerifier.policy
        (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (nw := v7Hash4.params.nw) (nq := v7Hash4.params.nq)
        (repetitions := 1)
        (Optimized.v7Hash4_v1.code S.dom (by decide))
        Ligero.V1.scheme).accepts
        (Encode.encodeLig S.pl nlin sys)
        ((S.Vc σ.2.1 σ.2.2).decodeChal p.1)
        (S.respOf msg)
        ((S.Vc σ.2.1 σ.2.2).decodeQuery p.2)
        (openSchemeOracle
          (extOracle nlin nt (Row.rowValid v7Hash4_valid) S.dom
            (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec
            (rootOfKey σ.1.1, σ.1.2))
          ((S.Vc σ.2.1 σ.2.2).decodeQuery p.2))).card : ℚ) /
        (Fintype.card C : ℚ) ^ 2 ≤ (1 : ℚ) / 2 ^ 125 := by
  have hdim : Optimized.v7Hash4_v1.certificate.openings + v7Hash4.params.q =
      Optimized.v7Hash4_v1.certificate.k := by decide
  have hkn : Optimized.v7Hash4_v1.certificate.openings + v7Hash4.params.q ≤
      Optimized.v7Hash4_v1.certificate.n := by decide
  have hfield : Fintype.card F = Optimized.v7Hash4_v1.certificate.fieldSize := S.hF
  have hno := v7Hash4_noSat_at_certificate S σ sys hkn hn
  have hlin : sys.linear.length ≤ nlin := by
    simpa only [Fits, S.hnlin σ.2.1 σ.2.2] using hf.1
  have hquad : sys.quad.length ≤ nt := by
    simpa only [Fits, S.hnt σ.2.1 σ.2.2] using hf.2
  exact Result.v1_hash_pair_acceptance_le_target Optimized.v7Hash4_v1
    Optimized.v7Hash4_v1_parameters (by rfl) hfield hdim S.dom hkn
    (Row.coreRows v7Hash4_valid) S.pl
    (extOracle nlin nt (Row.rowValid v7Hash4_valid) S.dom
      (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec
      (rootOfKey σ.1.1, σ.1.2))
    sys hlin hquad hno Optimized.v7Hash4_v1_bound
    (S.Vc σ.2.1 σ.2.2).decodeChal
    (S.Vc σ.2.1 σ.2.2).decodeQuery
    (fun _ => S.respOf msg) S.kchal S.kq
    (S.hbalChal σ.2.1 σ.2.2) (S.hbalQuery σ.2.1 σ.2.2)
    S.hkchal S.hkq

/-- The terminal event of the enlarged hash4 circuit side is bounded by
the response-uniform flat V1 certificate, conditional on every field prefix. -/
theorem v7Hash4_terminalPair_ratio_le [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash4 v7Hash4_valid v7Hash4_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (ms : ℕ → Msg) :
    let T := v7Hash4_flatSide S
    ∀ pref : Fin
      (Lfzk.Rounds.Role.layerBase v7Hash4.params.rounds v7Hash4.params.nl + 1) → C,
      ((Finset.univ.filter fun pair : C × C =>
        Lfzk.RbrZkFlat.terminalPairAccept
          (H := T.H σ) (Sat := T.Sat σ)
          (T.LD σ) ms pref pair.1 pair.2).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ (1 : ℚ) / 2 ^ 125 := by
  let T := v7Hash4_flatSide S
  apply Lfzk.RbrZkFlat.ZkSide.terminalPairAccept_ratio_le_of_built
    T σ ms ((1 : ℚ) / 2 ^ 125) (by positivity)
  intro pref sys _ hf hn
  have hpair := v7Hash4_flat_pair_bound S σ sys
    (ms (Lfzk.Rounds.Role.layerBase v7Hash4.params.rounds v7Hash4.params.nl + 2))
    hf hn
  have hcode : Optimized.v7Hash4_v1.code S.dom (by decide) =
      v7Hash4.params.row.code (Row.rowValid v7Hash4_valid) S.dom
        (Row.hkrow v7Hash4_valid) := by rfl
  have hV : (v7Hash4_flatSide S).V σ = S.Vc σ.2.1 σ.2.2 := rfl
  convert hpair using 1
  congr 1
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [v7Hash4_flatSide_accepting S σ]
  simp only [accZ, acceptingR, LigeroV1LayerStep.code, stmtOf,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hV, ← hcode]
  rfl

/-- Hash1's interactive extraction-failure term pays the ordinary field
rounds plus the flat 125-bit V1 terminal envelope. -/
theorem v7Hash4_flat_iop_extraction_le [Nonempty C] {logv : ℕ}
    (S : CircuitSide v7Hash4 v7Hash4_valid v7Hash4_openings_pos
      logv C F Msg M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D C X Enc)
    (ms : ℕ → Msg)
    (hfalse : ∀ ℓ : (v7Hash4_flatSide S).Lift σ,
      ¬ (v7Hash4_flatSide S).Sat σ ℓ) :
    ((Finset.univ.filter fun tape : Fin
      (Lfzk.Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds) → C =>
        ZkLayerStepAccepts .accepted .start
          (steps (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
            ((v7Hash4_flatSide S).V σ)
            ((v7Hash4_flatSide S).LD σ) ms) tape).card : ℚ) /
      (Fintype.card C : ℚ) ^
        Lfzk.Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds ≤
      (v7Hash4.cardCand : ℚ) * Lfzk.NizkZk.zkFieldDensity v7Hash4 logv +
        (1 : ℚ) / 2 ^ 125 := by
  exact Lfzk.RbrZkFlat.ZkSide.accepted_ratio_le_field_plus_terminal_density
    (v7Hash4_flatSide S) S.hF σ ms hfalse ((1 : ℚ) / 2 ^ 125)
    (v7Hash4_terminalPair_ratio_le S σ ms)

end Hash4

end Lfzk.CompiledZk.FlatV7Radius
