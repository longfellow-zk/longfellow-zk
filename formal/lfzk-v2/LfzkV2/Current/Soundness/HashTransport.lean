import LfzkV2.Current.Soundness.Coordinates
import LfzkV2.Current.ByteOracleTransport
import TranscriptV2.StrandCharging

/-! Hash charges retain exactly the ordered digest observations through
coordinate changes and stopping. Challenge coordinates are unrestricted. -/
noncomputable section
namespace LfzkV2.Current.Soundness.HashTransport
open Finset Merkle.RandomOracle TranscriptV2 Bcs.TotalOracle
open scoped Classical

variable {P D C C' Out Out' : Type} [DecidableEq P] [DecidableEq D]

theorem receiving_congr {fuel extra : ℕ} (receives : P → Prop) (claims : P → Finset D)
    (first : Tree P (D × C) Out fuel) (second : Tree P (D × C') Out' extra)
    (H : P → D × C) (H' : P → D × C')
    (queries : queried first H = queried second H') (digests : ∀ p, (H p).1 = (H' p).1) :
    DigestProjection.receivingCharge receives claims first H =
      DigestProjection.receivingCharge receives claims second H' := by
  have seenEq : seen first H = seen second H' := congrArg List.toFinset queries
  have beforeEq p : before first H p = before second H' p := by
    rw [before_eq_takeWhile, before_eq_takeWhile, queries]
  unfold DigestProjection.receivingCharge
  rw [seenEq]
  apply sum_congr rfl
  intro point _
  have same : DigestProjection.bad claims first point H (H point) ↔
      DigestProjection.bad claims second point H' (H' point) := by
    simp only [DigestProjection.bad, DigestCharging.targets, seenEq, beforeEq, digests]
  rw [same]

section Coordinates
variable {Q Raw Extra Challenge Residual : Type} [DecidableEq Q]
variable (encode : P → Q) (injective : Function.Injective encode)
variable (split : Q → (Raw × Extra) ≃ Challenge × Residual) (residual : Q → Residual)
variable {fuel : ℕ} (tree : Tree P (D × Raw) Out fuel)
local notation "changed" => LfzkV2.Current.StrandSampling.reindex split residual
  (mapQueries encode (LfzkV2.Current.Soundness.Coordinates.pad (Extra := Extra) tree))
local notation "restored" => Equiv.symm (LfzkV2.Current.StrandSampling.oracleEquiv (Link := D) split)

include injective in
theorem coordinates_receiving (receives : Q → Prop) (claims : Q → Finset D) (H : Q → D × Challenge) :
    DigestProjection.receivingCharge receives claims changed H =
      DigestProjection.receivingCharge (receives ∘ encode) (claims ∘ encode) tree
        (LfzkV2.Current.Soundness.Coordinates.drop (restored (H,residual) ∘ encode)) := by
  have indexed := receiving_congr receives claims changed
    (mapQueries encode (LfzkV2.Current.Soundness.Coordinates.pad (Extra := Extra) tree)) H (restored (H,residual))
    (LfzkV2.Current.StrandSampling.reindex_run split residual _ H).2 (fun _ => rfl)
  rw [indexed, DigestProjection.receivingCharge_mapQueries encode injective]
  exact receiving_congr (receives ∘ encode) (claims ∘ encode)
    (LfzkV2.Current.Soundness.Coordinates.pad (Extra := Extra) tree) tree
    (restored (H,residual) ∘ encode) (LfzkV2.Current.Soundness.Coordinates.drop (restored (H,residual) ∘ encode))
    (LfzkV2.Current.Soundness.Coordinates.pad_run tree _).2 (fun _ => rfl)
end Coordinates

section Lift
variable {Logical Raw : Type} {valid : Logical → Prop}
variable (names : LfzkV2.Current.ByteOracleTransport.Codec Logical Raw valid)

def liftClaims (claims : Raw → Finset D) (point : Logical ⊕ Raw) : Finset D :=
  match names.untag point with | some raw => claims raw | none => ∅

def liftPredicate (predicate : Raw → Prop) (point : Logical ⊕ Raw) : Prop :=
  ∃ raw, names.untag point = some raw ∧ predicate raw

def auxiliary : Logical ⊕ Raw → Prop
  | .inl _ => False
  | .inr _ => True

omit [DecidableEq D] in
theorem liftClaims_tag (claims : Raw → Finset D) : liftClaims names claims ∘ names.tag = claims := by
  funext raw
  simp only [liftClaims, Function.comp_apply, names.untag_tag]

theorem liftPredicate_tag (predicate : Raw → Prop) : liftPredicate names predicate ∘ names.tag = predicate := by
  funext raw
  apply propext
  simp only [liftPredicate, Function.comp_apply, names.untag_tag, Option.some.injEq]
  constructor
  · rintro ⟨other,same,allowed⟩
    exact same.symm ▸ allowed
  · intro allowed
    exact ⟨raw,rfl,allowed⟩

theorem lifted_auxiliary (predicate : Raw → Prop)
    (eligible : ∀ raw, predicate raw → names.decode raw = none)
    (point : Logical ⊕ Raw) (present : liftPredicate names predicate point) : auxiliary point := by
  rcases present with ⟨raw,source,allowed⟩
  cases point with
  | inr _ => trivial
  | inl point =>
      simp only [LfzkV2.Current.ByteOracleTransport.Codec.untag] at source
      split_ifs at source with good
      · have equal := Option.some.inj source
        have decoded := names.decode_encode ⟨point,good⟩
        rw [equal, eligible raw allowed] at decoded
        cases decoded


omit [DecidableEq D] in
theorem liftClaims_card (claims : Raw → Finset D) (bound : ∀ raw, (claims raw).card ≤ 2)
    (point : Logical ⊕ Raw) : (liftClaims names claims point).card ≤ 2 := by
  cases source : names.untag point with
  | none => simp only [liftClaims, source, card_empty, Nat.zero_le]
  | some raw => simpa only [liftClaims, source] using bound raw

variable [DecidableEq Logical] [DecidableEq Raw] [Fintype Logical] [Fintype Raw]
variable [Fintype D] [Nonempty D] {Challenge : Type} [Fintype Challenge] [Nonempty Challenge]

omit [DecidableEq Logical] [DecidableEq Raw] in
theorem hash_sum_le [queryDecidable : DecidableEq (Logical ⊕ Raw)] (strand merkle : Raw → Finset D) (receives : Raw → Prop)
    (strandAuxiliary : ∀ raw, (strand raw).Nonempty → names.decode raw = none)
    (receiveAuxiliary : ∀ raw, receives raw → names.decode raw = none)
    (disjoint : ∀ raw, receives raw → strand raw = ∅)
    (strandBound : ∀ raw, (strand raw).card ≤ 1) (merkleBound : ∀ raw, (merkle raw).card ≤ 2)
    {fuel Q : ℕ} (tree : Tree (Logical ⊕ Raw) (D × Challenge) Out fuel)
    (queries : ∀ H, (seen tree H).card ≤ Q) :
    (∑ H, (DigestProjection.charge (liftClaims names strand) tree H +
      DigestProjection.receivingCharge (liftPredicate names receives) (liftClaims names merkle) tree H)) ≤
      ∑ H, ∑ p ∈ seen tree H, if auxiliary p then (2*Q : ℚ)/Fintype.card D else 0 := by
  let plants := fun p => (liftClaims names strand p).Nonempty
  have plantAuxiliary p (planted : plants p) : auxiliary p := by
    apply lifted_auxiliary names (fun raw => (strand raw).Nonempty) strandAuxiliary p
    cases source : names.untag p with
    | none => simp only [plants, liftClaims, source, Finset.not_nonempty_empty] at planted
    | some raw => exact ⟨raw,source,by simpa only [plants, liftClaims, source] using planted⟩
  have noReceiving p (planted : plants p) : ¬liftPredicate names receives p := by
    rintro ⟨raw,source,received⟩
    simp only [plants, liftClaims, source, disjoint raw received, Finset.not_nonempty_empty] at planted
  have strandCard p : (liftClaims names strand p).card ≤ if plants p then 1 else 0 := by
    by_cases planted : plants p
    · rw [if_pos planted]
      cases source : names.untag p with
      | none => simp only [liftClaims, source, card_empty, Nat.zero_le]
      | some raw => simpa only [liftClaims, source] using strandBound raw
    · rw [if_neg planted, not_nonempty_iff_eq_empty.mp planted]
      exact le_rfl
  exact StrandCharging.disjoint_hash_sum_le tree queries plants (liftPredicate names receives)
    auxiliary plantAuxiliary (lifted_auxiliary names receives receiveAuxiliary) noReceiving
    (liftClaims names strand) (liftClaims names merkle) (fun p => by
      by_cases hp : plants p
      · simpa only [if_pos hp] using strandCard p
      · simpa only [if_neg hp] using strandCard p) (liftClaims_card names merkle merkleBound)

end Lift
end LfzkV2.Current.Soundness.HashTransport
