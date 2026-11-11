import LfzkV2.Current.StrandAuthentication
import LfzkV2.Current.StrandSampling

/-! A successful physical role sampler fills exactly one factor of the
common runtime answer. Resetting the unused coordinates to the same fixed
fallback therefore preserves the complete answer, not merely its marginal
distribution. The existing replay and decoder congruence lemmas then apply.
-/
noncomputable section
namespace LfzkV2.Current.StrandDecoder
open Application ApplicationSetup CanonicalPrefix Merkle.RandomOracle TranscriptV2
open scoped Classical

section Answers
variable {Point Answer : Type} {Values Unused : Point → Type}
variable (factor : (point : Point) → Answer ≃ Values point × Unused point) (fallback : Answer)

def normalizedOracle (H : Point → Digest × Answer) (point : Point) : Digest × Answer :=
  ((H point).1,StrandSampling.normalize (factor point) fallback (H point).2)

variable {blocks : ℕ}
variable (history : Point → Strand.History)
variable (sample : (point : Point) → Tree Strand.Word Digest (Option (Values point)) blocks)

/-- Both link and complete embedded answer are preserved. The only random
oracle premise is the identified raw PRF row; the sampler's joint uniformity
is the separate approved ideal-sampling assumption. -/
theorem oracle_eq [∀ point, Fintype (Values point)] [∀ point, Nonempty (Values point)]
    (SHA : Strand.Oracle) (H : Point → Digest × Answer) (point : Point)
    (fiber : ℕ) (uniform : ∀ value,
      (Finset.univ.filter fun stream => ((sample point).run stream).1 = some value).card = fiber)
    (residual : Fin (Fintype.card (Strand.Word → Digest)))
    (link : SHA (history point).input.encode = (H point).1)
    (row : (fun counter => SHA (Strand.Input.prf (history point).id
        (SHA (history point).input.encode) counter).encode) =
      ((StrandSampling.componentEquiv (factor point) (fun stream => ((sample point).run stream).1)
        fiber uniform).symm ((H point).2,residual)).1)
    (success : TranscriptV2.StrandVerifier.sampled history
      (fun p => StrandSampling.read (factor p) fallback (sample p)) SHA point) :
    TranscriptV2.StrandVerifier.oracle history
        (fun p => StrandSampling.read (factor p) fallback (sample p)) fallback SHA point =
      normalizedOracle factor fallback H point := by
  have actual := StrandSampling.oracle_on_success history fallback factor sample SHA point fiber uniform
    (H point).2 residual row success
  rw [link] at actual
  exact actual

end Answers

section Runtime
variable {g : Geometry} {fields : Fields} {Advice Key C B Salt Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t capacity blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) (C := C) (Salt := Salt))
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key)
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields)
  (Advice := Advice) (Request := Request)
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := BoundedBytes capacity)) C)
variable (bodyCodec : PrefixCodec (Body g fields Advice (RuntimeVerifier.Authentication (g := g))))
variable {Values Unused : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) → Type}
variable (factor : (point : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key)) → C ≃ Values point × Unused point)
variable [∀ point, Fintype (Values point)] [∀ point, Nonempty (Values point)]
variable (sample : (point : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key)) → Tree Strand.Word Digest (Option (Values point)) blocks)
variable (fiber : (point : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key)) → ℕ)
variable (uniform : ∀ point value,
  (Finset.univ.filter fun stream => ((sample point).run stream).1 = some value).card = fiber point)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : BoundedBytes capacity → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]
local notation "history" => StrandRuntime.history bodyCodec
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R cfg earlier
local notation "read" => fun point => StrandSampling.read (factor point) cfg.fallback (sample point)
local notation "physical" => StrandVerifier.oracle binary prime P R cfg bodyCodec read

/-- Equality of the actual requested rows on successful reads suffices for
the complete runtime decoder and every replay point, including the final-seal
input. No statement parser, plan congruence, or execution certificate is added
as a premise. The supplied row identities are deterministic coupling facts. -/
theorem decode_and_path (output : Output) (SHA : Strand.Oracle) (H : Point → Digest × C)
    (residual : Point → Fin (Fintype.card (Strand.Word → Digest)))
    (links : ∀ i : Fin g.roles.length,
      let point := (M).point output (physical SHA) i.val
      SHA (history point).input.encode = (H point).1)
    (rows : ∀ i : Fin g.roles.length,
      let point := (M).point output (physical SHA) i.val
      (fun counter => SHA (Strand.Input.prf (history point).id
        (SHA (history point).input.encode) counter).encode) =
        ((StrandSampling.componentEquiv (factor point) (fun stream => ((sample point).run stream).1)
          (fiber point) (uniform point)).symm ((H point).2,residual point)).1)
    (success : StrandVerifier.samplersSucceeded binary prime P R cfg earlier bodyCodec read output SHA) :
    RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output (physical SHA) =
        RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output
          (normalizedOracle factor cfg.fallback H) ∧
      ∀ index ≤ g.roles.length, (M).point output (physical SHA) index =
        (M).point output (normalizedOracle factor cfg.fallback H) index := by
  have answers index (within : index < g.roles.length) :
      physical SHA ((M).point output (physical SHA) index) =
        normalizedOracle factor cfg.fallback H ((M).point output (physical SHA) index) :=
    oracle_eq factor cfg.fallback history sample SHA H _ _ (uniform _)
      (residual ((M).point output (physical SHA) index))
      (links ⟨index,within⟩) (rows ⟨index,within⟩) (success ⟨index,within⟩)
  refine ⟨StrandAuthentication.decode_congr binary prime P R cfg earlier hashPublic decodePublic draw
    output (physical SHA) (normalizedOracle factor cfg.fallback H) answers,?_⟩
  intro index within
  apply congrArg (M).input
  exact (M).replay_congr_prefix output (physical SHA) (normalizedOracle factor cfg.fallback H) index
    (fun j before => answers j (by omega))

end Runtime
end LfzkV2.Current.StrandDecoder
