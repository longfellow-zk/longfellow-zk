import LfzkV2.Current.RuntimeAdaptiveMerkle
import TranscriptV2.MemoizeCommit

/-! The one-tree Merkle composition for a single adaptive request-family
experiment. Only the digest remainder pays verifier replay. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveMerkle
open Application ApplicationSetup ApplicationOracle RecursivePolygero SumcheckV2 Finset
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request)
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R cfg earlier
local notation "E" => RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg

variable [DecidableEq Enc] [DecidableEq Key]
variable [Fintype Key] [Fintype Base] [Fintype Advice] [∀ side, Fintype (fields side)]
variable [Nonempty C]
variable {calls tA Q TM : ℕ} (dflt : Digest × C)
variable (body : TwoOracleTree Enc Digest
  (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))
  (Digest × C) (RuntimeAdaptiveVerifier.Output (g := g) (fields := fields)
    (Advice := Advice) (Request := Request)) tA calls)
local notation "Setup" => setup binary prime P R cfg earlier dflt body
local notation "Ann" => Annotated (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Request := Request)

/-- Caching preserves the original adaptive output and its first-context
cut. The leading FS term uses original distinct queries; only the one-tree
explanation sees the ordinary verifier replay. -/
theorem ratio_le_support
    (hsupport : ∀ (mt : Fin TM → Digest) (H : Point → Digest × C),
      (TranscriptV2.seen (fixLeft mt default body []) H).card ≤ Q)
    {Leaf : Type} [Inhabited Salt] [Inhabited Leaf] {columns fc : ℕ}
    (codec : Codec Salt Leaf Digest Enc) (dec : RoleDecoders codec)
    (check : Ann → Tree Enc Digest Unit fc) (rootOf : Key → Digest)
    (claimOf : Ann → OpeningClaim columns Salt Leaf Digest)
    (hcheck : ∀ (H : Enc → Digest) (out : Ann),
      ∀ qa ∈ ((checkPass codec columns (claimOf out).I (claimOf out).a
          (claimOf out).pf (2*columns) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (ht : tA ≤ TM) (hF : fc+tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc Fails : (Fin TM → Digest) → (Point → Digest × C) → Prop)
    (hacc : ∀ mt H, Acc mt H → (Setup).MerkleAccepts codec check rootOf claimOf mt H)
    (ideal : (Fin TM → Digest) → Output → (Point → Digest × C) → Prop)
    (hbridge : ∀ mt H, Acc mt H → (Setup).Explains dec rootOf claimOf mt H →
      Fails mt H → ideal mt ((Setup).proof mt H).1 H)
    (bound : ℚ)
    (hfs : ∀ mt : Fin TM → Digest,
      ((univ.filter fun H : Point → Digest × C =>
        ideal mt ((fixLeft mt default body []).run H).1 H).card : ℚ) /
        (Fintype.card (Digest × C) : ℚ)^Fintype.card Point ≤ bound) :
    ((univ.filter fun ω : (Fin TM → Digest) × (Point → Digest × C) =>
        Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ) /
      ((Fintype.card Digest : ℚ)^TM*(Fintype.card (Digest × C) : ℚ)^Fintype.card Point) ≤
      bound+(Bcs.AdaptiveCommit.adaptiveNumerator fc tA (1+g.roles.length+Q) : ℚ)/Fintype.card Digest := by
  rw [Nat.add_assoc]
  let S := Setup
  let fallback := S.proof (fun _ : Fin TM => default) (fun _ => dflt)
  have hsup : ∀ (mt : Fin TM → Digest) (H : Point → Digest × C),
      (TranscriptV2.seen (fixLeft mt default S.body []) H).card ≤ g.roles.length+Q := by
    intro mt H
    change (TranscriptV2.seen (fixLeft mt default (body.bindRight (M).recompute) []) H).card ≤ _
    rw [fixLeft_bindRight]
    simpa only [Nat.add_comm] using TranscriptV2.Memoize.seen_bind_card_le
      (fixLeft mt default body []) (M).recompute H (hsupport mt H)
  apply TranscriptV2.Memoize.ratio_le_from_potential_support S fallback hsup
    codec dec check rootOf claimOf hcheck (by decide) ht hF hTM Acc Fails hacc bound
  intro mt
  have hcount :
      (univ.filter fun H : Point → Digest × C =>
        Acc mt H ∧ S.Explains dec rootOf claimOf mt H ∧ Fails mt H).card ≤
      (univ.filter fun H : Point → Digest × C => ideal mt ((fixLeft mt default body []).run H).1 H).card := by
    apply card_le_card
    intro H h
    simp only [mem_filter,mem_univ,true_and] at h ⊢
    have hi := hbridge mt H h.1 h.2.1 h.2.2
    rw [proof_eq] at hi
    exact hi
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hcount) (by positivity)).trans (hfs mt)

end LfzkV2.Current.RuntimeAdaptiveMerkle
