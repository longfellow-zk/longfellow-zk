import TranscriptV2.StrandSampling
import TranscriptV2.StrandVerifier

/-! A closed, nondegenerate physical sampler. It issues a numbered PRF
read, succeeds on every stream, and has strictly positive equal successful
fibers. Thus the partial-sampler model admits useful readers independently
of its legitimate rejecting-reader instances. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandSamplerNonvacuity
open TranscriptV2 Merkle.RandomOracle
open scoped Classical

def readDigest : Tree Strand.Word Strand.Digest (Option Strand.Digest) 1 :=
  .query 0 fun digest => .done (some digest)

@[simp] theorem readDigest_run (stream : Strand.Word → Strand.Digest) :
    (readDigest.run stream).1 = some (stream 0) := rfl

abbrev residual := {counter : Strand.Word // counter ≠ 0} → Strand.Digest

def successFiber (value : Strand.Digest) :
    {stream : Strand.Word → Strand.Digest // stream 0 = value} ≃ residual where
  toFun stream counter := stream.val counter.val
  invFun rest := ⟨fun counter => if h : counter = 0 then value else rest ⟨counter,h⟩,
    by simp⟩
  left_inv stream := by
    apply Subtype.ext
    funext counter
    by_cases zero : counter = 0
    · subst counter
      simpa using stream.property.symm
    · simp only [dif_neg zero]
  right_inv rest := by
    funext counter
    simp only [dif_neg counter.property]

theorem balanced (value : Strand.Digest) :
    (Finset.univ.filter fun stream => (readDigest.run stream).1 = some value).card =
      Fintype.card residual := by
  simp only [readDigest_run,Option.some.injEq]
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (successFiber value)

theorem positive_fiber : 0 < Fintype.card residual := Fintype.card_pos

theorem every_value_succeeds (value : Strand.Digest) :
    ∃ stream, (readDigest.run stream).1 = some value :=
  ⟨fun _ => value,rfl⟩

theorem two_different_successes :
    ∃ first second : Strand.Word → Strand.Digest,
      (readDigest.run first).1 ≠ (readDigest.run second).1 := by
  refine ⟨fun _ _ => 0,fun _ _ => 1,?_⟩
  intro equal
  have bytes := congrFun (Option.some.inj equal) 0
  exact (by decide : (0 : Fin 256) ≠ 1) bytes

theorem sampled {Point : Type} (history : Point → Strand.History)
    (SHA : Strand.Oracle) (point : Point) :
    TranscriptV2.StrandVerifier.sampled history (fun _ => readDigest) SHA point := by
  rfl

end LfzkV2.Current.ZeroKnowledge.StrandSamplerNonvacuity
