import TranscriptV2.StrandSealCharging
import Bcs.FiniteProbability
import TranscriptV2.Strand
import TranscriptV2.StrandRecovery

/-! One fresh-query charge per numbered strand position. Targets come from
the original query table and submitted seal, not from verifier replay. The
finite address window is an exact representation of the reached inputs;
its cardinality is not charged as adversarial work. -/
namespace TranscriptV2.StrandMissingQueries
open Strand Framing Merkle.RandomOracle Bcs.TotalOracle Bcs.FiniteProbability
open scoped Classical

variable {P Out : Type} [DecidableEq P]
variable (encode : P → Bytes) (decode : Bytes → P)
variable (messages : Out → ℕ → Bytes) (finalSeal : Out → Digest) (rounds : ℕ)

def address (out : Out) (H : P → Digest) (index : ℕ) : P :=
  decode (StrandLinear.replay (messages out) (H ∘ decode) index).input.encode

def rawTrace (result : Out × List (P × Digest)) : StrandRecovery.Trace :=
  result.2.map fun entry => (encode entry.1,entry.2)

def target (result : Out × List (P × Digest)) (index : ℕ) : Option Digest :=
  StrandRecovery.sealTarget (rawTrace encode result) rounds (finalSeal result.1) index

variable {fuel : ℕ} (program : Tree P Digest Out fuel)

/-- A position's actual node is missing from the original trace, and its
fresh answer hits that position's one recovered target. -/
def Hit (index : Fin (rounds+1)) (H : P → Digest) : Prop :=
  let result := program.run H
  let point := address decode messages result.1 H index.val
  point ∉ seen program H ∧ target encode finalSeal rounds result index.val = some (H point)

/-- Authentication of the terminal node uses the actual counter-zero PRF
input, with the same numbered node id as ordinary challenge expansion. -/
def sealInput (out : Out) (H : P → Digest) : Bytes :=
  let final := StrandLinear.replay (messages out) (H ∘ decode) rounds
  (Input.prf final.id (H (decode final.input.encode)) 0).encode

theorem rawTrace_queried (H : P → Digest) (point : P) (queried : point ∈ seen program H) :
    (encode point,H point) ∈ rawTrace encode (program.run H) := by
  obtain ⟨⟨raw,answer⟩,member,same⟩ := List.mem_map.mp (List.mem_toFinset.mp queried)
  change raw = point at same
  subst raw
  have value := Tree.trace_sound program H (point,answer) member
  change answer = H point at value
  rw [value] at member
  exact List.mem_map.mpr ⟨(point,H point),member,rfl⟩

variable (inverse : ∀ point, decode (encode point) = point)

include inverse in
theorem queried_of_rawTrace (H : P → Digest) (raw : Bytes) (digest : Digest)
    (member : (raw,digest) ∈ rawTrace encode (program.run H)) : decode raw ∈ seen program H := by
  obtain ⟨⟨point,answer⟩,member,equal⟩ := List.mem_map.mp member
  have same : encode point = raw := congrArg Prod.fst equal
  have decoded : point = decode raw := (inverse point).symm.trans (congrArg decode same)
  rw [← decoded]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(point,answer),member,rfl⟩)

variable (fits : rounds < 2^64)
variable (covered : ∀ out H i, i ≤ rounds →
  encode (address decode messages out H i) =
    (StrandLinear.replay (messages out) (H ∘ decode) i).input.encode)

include fits inverse covered in
/-- Deterministic failure cover. Either all node queries are present, or
one position hits the fixed target recovered from the original trace.
The only collision premise is uniqueness inside that original trace. -/
theorem missing_covered (H : P → Digest)
    (unique : Merkle.MH.CollisionFree (rawTrace encode (program.run H)))
    (terminal : (sealInput decode messages rounds (program.run H).1 H,
      finalSeal (program.run H).1) ∈ rawTrace encode (program.run H))
    (missing : ∃ index : Fin (rounds+1),
      address decode messages (program.run H).1 H index.val ∉ seen program H) :
    ∃ index, Hit encode decode messages finalSeal rounds program index H := by
  let out := (program.run H).1
  let trace := rawTrace encode (program.run H)
  obtain ⟨index,absent⟩ := missing
  have missingRaw : ∃ i ≤ rounds,
      ((StrandLinear.replay (messages out) (H ∘ decode) i).input.encode,
        (H ∘ decode) (StrandLinear.replay (messages out) (H ∘ decode) i).input.encode) ∉ trace := by
    refine ⟨index.val,by have := index.isLt; omega,?_⟩
    intro present
    exact absent (queried_of_rawTrace encode decode program inverse H _ _ present)
  obtain ⟨i,within,absentRaw,hit⟩ :=
    StrandRecovery.missing_node trace unique (messages out) (H ∘ decode) rounds fits missingRaw
  refine ⟨⟨i,by omega⟩,?_,?_⟩
  · intro present
    have pair := rawTrace_queried encode program H _ present
    rw [covered out H i within] at pair
    exact absentRaw pair
  · change StrandRecovery.sealTarget trace rounds (finalSeal out) i = _
    rw [StrandRecovery.sealTarget_of_mem trace unique (messages out) (H ∘ decode) rounds fits
      (finalSeal out) terminal i]
    exact hit

variable [Fintype P]

include fits covered in
theorem hit_density_le (index : Fin (rounds+1)) :
    density (Hit encode decode messages finalSeal rounds program index) ≤ 1 / (2^256 : ℚ) := by
  let point := fun (result : Out × List (P × Digest)) (H : P → Digest) =>
    address decode messages result.1 H index.val
  let provided := fun (result : Out × List (P × Digest)) =>
    (target encode finalSeal rounds result index.val).getD 0
  have independent : ∀ result H H', AgreeOff (point result H) H H' →
      point result H = point result H' := by
    intro result H H' agree
    have same := StrandLinear.replay_restrict_off decode encode (messages result.1) H H'
      index.val (by have := index.isLt; omega)
      (fun i within => covered result.1 H i (by have := index.isLt; omega)) agree
    exact congrArg (fun history : History => decode history.input.encode) same
  have bound := StrandSealCharging.unqueriedSeal_density_le point provided independent (recordTrace program)
  have cover : ∀ H, Hit encode decode messages finalSeal rounds program index H →
      StrandSealCharging.UnqueriedSeal point provided (recordTrace program) H := by
    intro H hit
    change address decode messages (program.run H).1 H index.val ∉ seen program H ∧
      target encode finalSeal rounds (program.run H) index.val =
        some (H (address decode messages (program.run H).1 H index.val)) at hit
    simp only [StrandSealCharging.UnqueriedSeal,run_recordTrace,point,provided]
    constructor
    · simpa only [seen,queried,run_recordTrace] using hit.1
    · rw [hit.2]
      rfl
  have size : (Fintype.card Digest : ℚ) = 2^256 := by
    rw [digest_card,Nat.cast_pow,Nat.cast_ofNat]
  exact (density_mono cover).trans (by simpa only [size] using bound)

include fits covered in
/-- The coefficient is the number of positions, not its square and not
the product of positions with all labels encountered during replay. -/
theorem any_hit_density_le :
    density (fun H => ∃ index, Hit encode decode messages finalSeal rounds program index H) ≤
      (rounds+1 : ℚ) / 2^256 := by
  calc
    _ ≤ ∑ index, density (Hit encode decode messages finalSeal rounds program index) :=
      density_union_le _ _ (fun _ hit => hit)
    _ ≤ ∑ _index : Fin (rounds+1), (1 / (2^256 : ℚ)) := by
      apply Finset.sum_le_sum
      intro index _
      exact hit_density_le encode decode messages finalSeal rounds program fits covered index
    _ = _ := by simp [div_eq_mul_inv,Nat.cast_add]

include fits inverse covered in
theorem missing_density_le :
    density (fun H =>
      Merkle.MH.CollisionFree (rawTrace encode (program.run H)) ∧
      (sealInput decode messages rounds (program.run H).1 H,finalSeal (program.run H).1) ∈
        rawTrace encode (program.run H) ∧
      ∃ index : Fin (rounds+1), address decode messages (program.run H).1 H index.val ∉
        seen program H) ≤ (rounds+1 : ℚ) / 2^256 := by
  apply le_trans _ (any_hit_density_le encode decode messages finalSeal rounds program fits covered)
  apply density_mono
  rintro H ⟨unique,terminal,missing⟩
  exact missing_covered encode decode messages finalSeal rounds program inverse fits covered
    H unique terminal missing

end TranscriptV2.StrandMissingQueries
