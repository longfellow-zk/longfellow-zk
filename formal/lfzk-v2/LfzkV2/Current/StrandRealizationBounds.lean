import LfzkV2.Current.StrandRealization
import LfzkV2.Current.StrandOriginalSeal
import TranscriptV2.StrandMissingQueries
import TranscriptV2.DigestCollision

/-! Original-query bounds for the actual numbered SHA verifier. Original
collisions are charged once. A missing transcript node pays one fresh target
per position; verifier replay is never added to the original query budget. -/
noncomputable section
namespace LfzkV2.Current.StrandRealizationBounds
open Application ApplicationSetup CanonicalPrefix QueryRuntime
open Finset Merkle.RandomOracle TranscriptV2 Bcs.FiniteProbability
open scoped Classical

/-- One original-query birthday allowance, one target per transcript node,
and one guess of the complete-proof final seal. -/
def delta (queries rounds : ℕ) : ℚ :=
  ((((queries*(queries-1)/2 : ℕ) : ℚ)) + rounds + 2) / 2^256

private theorem density_collision_le {X D Out : Type} [DecidableEq X]
    [Fintype X] [Fintype D] [Nonempty D] {fuel Q : ℕ}
    (tree : Tree X D Out fuel) (budget : ∀ H, (seen tree H).card ≤ Q) :
    density (DigestCollision.Collision id tree) ≤ (((Q*(Q-1)/2 : ℕ) : ℚ)) / Fintype.card D := by
  simpa only [density,Fintype.card_fun,Nat.cast_pow] using DigestCollision.ratio_le tree budget

variable {g : Geometry} {fields : Fields} {Advice C B Salt Enc : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits k s n t blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Salt))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)
variable (fits : g.roles.length < 2^64)
variable (independent : CanonicalRequest.ChallengeIndependent shape binary.nPublic metadata)
variable (sample : QueryRuntime.Runtime.Point repr shape setup binary.nPublic →
  Tree Strand.Word Digest (Option C) blocks)
variable [Inhabited Salt]
variable [Inhabited (RuntimeVerifier.Family binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf]
variable (codec : Merkle.Indexed.Codec Salt (RuntimeVerifier.Family binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf Digest Enc)
variable (merkleInput : Enc → Bytes)
variable {fuel Q : ℕ} (program : Tree Bytes Digest (CanonicalRuntime.Output (Advice := Advice) binary shape) fuel)
variable (queries : ∀ SHA, (seen program SHA).card ≤ Q)

local notation "W" => CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg
local notation "Earlier" => CanonicalRuntime.earlier binary prime P R repr shape setup cfg binaryCount metadata
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R (W) (Earlier)
local notation "Value" => QueryRuntime.Runtime.Value repr shape setup binary.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape
local notation "bodyCodec" => ProofBodyCodec.codec repr g
local notation "schema" => StrandRuntime.Runtime.schema repr shape setup binary.nPublic
local notation "history" => StrandRuntime.history bodyCodec
local notation "beforeSeal" => TranscriptV2.StrandVerifier.beforeSeal history sample cfg.fallback (M)
local notation "fullReplay" => StrandAuthentication.replay binary prime P R (W) (Earlier) bodyCodec sample codec merkleInput
local notation "O" => StrandRealization.other binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "Node" => StrandWindow.Node (O)
local notation "Raw" => StrandWindow.Point (O)
local notation "fallbackNode" => StrandRealization.fallback binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "decodeRaw" => StrandWindow.decode (O) fallbackNode
local notation "Name" => StrandSearch.Name Node Value
local notation "Answer" => StrandCoupling.Sample Digest Strand.Word
local notation "compiled" => mapQueries decodeRaw program
local notation "compiledReplay" => fun output : Output => mapQueries decodeRaw (fullReplay output)
local notation "searchTree" => StrandReplay.search (schema) bytes compiled
local notation "resumeTree" => StrandReplay.resume (schema) bytes compiledReplay
local notation "completed" => StrandRealization.completion binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "SHAof" => StrandRealization.rawSHA binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "messages" => fun output : Output =>
  StrandLinearReplay.packets bodyCodec (Earlier (RuntimeAdaptive.Output.request output)) cfg.fallback (RuntimeAdaptive.Output.proof output)
local notation "ordinaryOracle" => TranscriptV2.StrandVerifier.oracle history sample cfg.fallback
local notation "rawException" => StrandRealization.rawException binary prime P R repr shape setup cfg
  binaryCount metadata fits sample codec merkleInput program
local notation "address" => StrandVerifier.finalSealAddress binary prime P R (W) (Earlier) bodyCodec sample

include queries in
/-- The finite compiler cannot increase the original raw query budget. -/
theorem compiled_budget (G : Raw → Digest) : (seen compiled G).card ≤ Q := by
  rw [TranscriptV2.seen_mapQueries]
  exact Finset.card_image_le.trans (queries _)

include bodyFits independent in
/-- Every actual numbered history is a canonical runtime input in the
finite window, even if that input was not queried by the original prover. -/
theorem linear_covered (output : Output) (G : Raw → Digest) (i : ℕ)
    (within : i ≤ g.roles.length) :
    StrandWindow.encode (StrandMissingQueries.address decodeRaw messages output G i) =
      (StrandLinear.replay (messages output) (SHAof G) i).input.encode := by
  let value := StrandAcceptedPath.value binary prime P R repr shape setup cfg binaryCount metadata
    bodyFits fits sample output (SHAof G) i
  let node := StrandRealization.locate binary prime P R repr shape setup cfg binaryCount metadata
    fits sample codec merkleInput program value
  have same : ((schema).encode value).input.encode =
      (StrandLinear.replay (messages output) (SHAof G) i).input.encode :=
    congrArg (fun h : Strand.History => h.input.encode)
      ((StrandAcceptedPath.value_history binary prime P R repr shape setup cfg binaryCount metadata
        bodyFits fits sample output (SHAof G) i within).trans
        (StrandSealIndependence.runtime_history_replay binary prime P R repr shape setup cfg
          binaryCount metadata independent sample output (SHAof G) i within))
  change StrandWindow.encode (decodeRaw (StrandLinear.replay (messages output) (SHAof G) i).input.encode) = _
  rw [← same]
  exact congrArg StrandWindow.encode (StrandWindow.decode_encode (O) fallbackNode (.inl node))

/-- The finite trace encodes exactly the original raw query table. -/
theorem rawTrace_original (G : Raw → Digest) :
    StrandMissingQueries.rawTrace StrandWindow.encode ((compiled).run G) =
      (program.run (SHAof G)).2 :=
  congrArg Prod.snd (StrandRealization.original_actual binary prime P R repr shape setup cfg
    binaryCount metadata fits sample codec merkleInput program G)

/-- A collision in the original byte trace is already in the original
finite query set. No replay input, dummy digest, or unused cache row is added. -/
theorem collision_covered (G : Raw → Digest)
    (bad : ¬Merkle.MH.CollisionFree (program.run (SHAof G)).2) :
    DigestCollision.Collision id compiled G := by
  rw [← rawTrace_original binary prime P R repr shape setup cfg binaryCount metadata fits
    sample codec merkleInput program G] at bad
  by_contra absent
  apply bad
  intro a ha b hb equal
  obtain ⟨⟨pa,da⟩,leftMember,rfl⟩ := (List.mem_map.mp ha :
    ∃ qa ∈ ((compiled).run G).2, (StrandWindow.encode qa.1,qa.2) = a)
  obtain ⟨⟨pb,db⟩,rightMember,rfl⟩ := (List.mem_map.mp hb :
    ∃ qa ∈ ((compiled).run G).2, (StrandWindow.encode qa.1,qa.2) = b)
  change da = db at equal
  by_cases same : pa = pb
  · exact congrArg StrandWindow.encode same
  · apply False.elim
    apply absent
    refine ⟨pa,?_,pb,?_,same,?_⟩
    · exact List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) leftMember)
    · exact List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) rightMember)
    · exact (Tree.trace_sound compiled G _ leftMember).symm.trans
        (equal.trans (Tree.trace_sound compiled G _ rightMember))

include queries in
theorem actual_collision_ratio_le :
    density (fun G : Raw → Digest => ¬Merkle.MH.CollisionFree (program.run (SHAof G)).2) ≤
      (((Q*(Q-1)/2 : ℕ) : ℚ)) / 2^256 := by
  have bound := density_collision_le compiled
    (compiled_budget binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program queries)
  have card : (Fintype.card Digest : ℚ) = 2^256 := by
    rw [Strand.digest_card,Nat.cast_pow,Nat.cast_ofNat]
  rw [card] at bound
  exact (density_mono (collision_covered binary prime P R repr shape setup cfg binaryCount metadata
    fits sample codec merkleInput program)).trans bound

/-- A correct final seal that was absent from the original query table. -/
def sealEvent (G : Raw → Digest) : Prop :=
  StrandSealCharging.UnqueriedSeal address (fun output => output.proof.finalSeal)
    program (SHAof G)

include independent in
theorem seal_ratio_le :
    density (sealEvent binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program) ≤ 1 / (2^256 : ℚ) :=
  StrandOriginalSeal.original_ratio_le binary prime P R repr shape setup cfg binaryCount metadata
    independent sample (O) fallbackNode program

/-- The seal was queried, the original table is collision-free, but some
numbered transcript node was omitted. These conditions define a joint event;
we do not condition the oracle distribution on collision freedom. -/
def missingEvent (G : Raw → Digest) : Prop :=
  let SHA := SHAof G
  let output := (program.run SHA).1
  Merkle.MH.CollisionFree (program.run SHA).2 ∧
    (address output SHA,output.proof.finalSeal) ∈ (program.run SHA).2 ∧
    ¬∀ i ≤ g.roles.length, Merkle.QueryTable.Known (program.run SHA).2
      (history ((M).point output (ordinaryOracle SHA) i)).input.encode

include independent in
/-- Fixed-packet replay and runtime replay produce the same terminal PRF
address. This equality does not depend on any queried-set hypothesis. -/
theorem sealInput_eq (output : Output) (G : Raw → Digest) :
    StrandMissingQueries.sealInput decodeRaw messages g.roles.length output G =
      address output (SHAof G) := by
  exact (congrArg (fun h : Strand.History =>
    (Strand.Input.prf h.id ((SHAof G) h.input.encode) 0).encode)
    (StrandSealIndependence.runtime_history_replay binary prime P R repr shape setup cfg
      binaryCount metadata independent sample output (SHAof G) g.roles.length le_rfl)).symm

include bodyFits independent in
/-- Concrete replay supplies the finite missing-query theorem's event.
Address representation and probability counting are separated so neither
proof needs to unfold the full verifier while reasoning about the other. -/
theorem missing_covered (G : Raw → Digest)
    (bad : missingEvent binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program G) :
    Merkle.MH.CollisionFree (StrandMissingQueries.rawTrace StrandWindow.encode ((compiled).run G)) ∧
      (StrandMissingQueries.sealInput decodeRaw messages g.roles.length ((compiled).run G).1 G,
        ((compiled).run G).1.proof.finalSeal) ∈
          StrandMissingQueries.rawTrace StrandWindow.encode ((compiled).run G) ∧
      ∃ i : Fin (g.roles.length+1),
        StrandMissingQueries.address decodeRaw messages ((compiled).run G).1 G i.val ∉ seen compiled G := by
  let output := (program.run (SHAof G)).1
  have trace := rawTrace_original binary prime P R repr shape setup cfg binaryCount metadata fits
    sample codec merkleInput program G
  have outputEq : ((compiled).run G).1 = output :=
    congrArg Prod.fst (StrandRealization.original_actual binary prime P R repr shape setup cfg
      binaryCount metadata fits sample codec merkleInput program G)
  refine ⟨?_,?_,?_⟩
  · simpa only [trace] using bad.1
  · rw [trace,outputEq,sealInput_eq binary prime P R repr shape setup cfg binaryCount metadata fits
      independent sample codec merkleInput program output G]
    exact bad.2.1
  · obtain ⟨i,missing⟩ := not_forall.mp bad.2.2
    obtain ⟨within,missing⟩ := Classical.not_imp.mp missing
    refine ⟨⟨i,Nat.lt_succ_of_le within⟩,?_⟩
    intro present
    apply missing
    have member := StrandMissingQueries.rawTrace_queried StrandWindow.encode compiled G _ present
    rw [trace,outputEq,linear_covered binary prime P R repr shape setup cfg binaryCount metadata
      bodyFits fits independent sample codec merkleInput program output G i within] at member
    rw [← StrandSealIndependence.runtime_history_replay binary prime P R repr shape setup cfg
      binaryCount metadata independent sample output (SHAof G) i within] at member
    exact ⟨_,member⟩

include bodyFits independent in
theorem missing_ratio_le :
    density (missingEvent binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program) ≤ (g.roles.length+1 : ℚ) / 2^256 := by
  exact (density_mono (missing_covered binary prime P R repr shape setup cfg binaryCount metadata
    bodyFits fits independent sample codec merkleInput program)).trans
    (StrandMissingQueries.missing_density_le StrandWindow.encode decodeRaw messages
      (fun output => output.proof.finalSeal) g.roles.length compiled
      (StrandWindow.decode_encode (O) fallbackNode) fits
      (linear_covered binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits
        independent sample codec merkleInput program))

include bodyFits independent queries in
/-- The actual raw exception is bounded before passing to grouped answers.
Only the adversary's original Q queries enter the birthday term. -/
theorem raw_exception_ratio_le : density rawException ≤ delta Q g.roles.length := by
  let collisionPiece := fun G : Raw → Digest => ¬Merkle.MH.CollisionFree (program.run (SHAof G)).2
  let sealPiece := sealEvent binary prime P R repr shape setup cfg binaryCount metadata fits
    sample codec merkleInput program
  let missingPiece := missingEvent binary prime P R repr shape setup cfg binaryCount metadata fits
    sample codec merkleInput program
  let pieces : Fin 3 → (Raw → Digest) → Prop := fun i =>
    if i = 0 then collisionPiece else if i = 1 then sealPiece else missingPiece
  have union := density_union_le rawException pieces (by
    intro G bad
    rcases bad with ⟨valid,collision | missing⟩
    · exact ⟨0,by simpa only [pieces,if_pos rfl] using collision⟩
    · let SHA := SHAof G
      let output := (program.run SHA).1
      change SHA (address output SHA) = output.proof.finalSeal at valid
      by_cases collision : collisionPiece G
      · exact ⟨0,by simpa only [pieces,if_pos rfl] using collision⟩
      · by_cases queried : address output SHA ∈ seen program SHA
        · refine ⟨2,?_⟩
          simp only [pieces,show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide,if_false]
          refine ⟨Classical.not_not.mp collision,?_,missing⟩
          obtain ⟨⟨raw,digest⟩,member,same⟩ := List.mem_map.mp (List.mem_toFinset.mp queried)
          change raw = address output SHA at same
          subst raw
          have value := Tree.trace_sound program SHA _ member
          change digest = SHA (address output SHA) at value
          rw [value,valid] at member
          exact member
        · refine ⟨1,?_⟩
          simp only [pieces,show (1 : Fin 3) ≠ 0 by decide,if_false]
          exact ⟨queried,valid⟩)
  have collisionBound := actual_collision_ratio_le binary prime P R repr shape setup cfg binaryCount metadata fits
    sample codec merkleInput program queries
  have sealBound := seal_ratio_le binary prime P R repr shape setup cfg binaryCount metadata fits independent
    sample codec merkleInput program
  have missingBound := missing_ratio_le binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits independent
    sample codec merkleInput program
  have sumBound := add_le_add (add_le_add collisionBound sealBound) missingBound
  have union' : density rawException ≤ density collisionPiece + density sealPiece + density missingPiece := by
    simpa only [Fin.sum_univ_three,pieces,ite_true,show (1 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide,if_false] using union
  exact union'.trans (sumBound.trans_eq (by unfold delta; ring))

include bodyFits independent queries in
/-- The same explicit bound holds in the grouped experiment by the exact
original-table observation law. No uniformity assumption about a completed
cache, no execution certificate, and no replay query budget is required. -/
theorem exception_ratio_le :
    letI : Fintype Value := Fintype.ofInjective
      (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
      (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
    letI : Fintype Name := inferInstance
    letI : Fintype Answer := inferInstance
    density (StrandRealization.exception binary prime P R repr shape setup cfg binaryCount metadata
      fits sample codec merkleInput program) ≤ delta Q g.roles.length := by
  letI : Fintype Value := Fintype.ofInjective
    (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
    (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
  letI : Fintype Name := inferInstance
  letI : Fintype Answer := inferInstance
  rw [← StrandRealization.exception_law binary prime P R repr shape setup cfg binaryCount metadata fits
    sample codec merkleInput program]
  exact raw_exception_ratio_le binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits
    independent sample codec merkleInput program queries

end LfzkV2.Current.StrandRealizationBounds
