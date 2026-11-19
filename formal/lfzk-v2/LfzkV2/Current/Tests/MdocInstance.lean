import LfzkV2.Current.Mdoc.Rust
import LfzkV2.Current.Tests.ProofAudit
import Mathlib.FieldTheory.Finite.GaloisField

/-! A canonical toy mdoc instance: every premise of the deployed soundness
endpoint `Mdoc.Soundness.averaged_ratio_le_rust` is discharged with concrete
values, at the Rust reader, and every boundary fiber of that reader is
positive. The circuits are toys: a hash circuit with empty fragments and an
input-only signature circuit. The binary field is an abstract GF(2^128)
(`GaloisField 2 128`), not Rust's `x^128+x^7+x^2+x+1` representation; the
premises need only some field of that size with a basis. -/
noncomputable section
namespace LfzkV2.Current.Tests.MdocInstance
open LfzkV2.Current LfzkV2.Current.ConcreteSetup
open scoped Classical
open SumcheckV2

/-! ### The field -/

abbrev GF := GaloisField 2 128
instance : Fintype GF := Fintype.ofFinite _

def cantor : Module.Basis (Fin 128) (ZMod 2) GF :=
  Module.finBasisOfFinrankEq _ _ (GaloisField.finrank 2 (by decide))

/-! ### Codecs from byte bijections -/

def codecOf {F : Type} (w : ℕ) (pos : 0 < w) (small : w ≤ 128) (e : F ≃ (Fin w → TranscriptV2.Framing.Byte)) :
    TranscriptV2.Framing.FieldCodec F where
  width := w
  positive := pos
  buffer := small
  encode v := List.ofFn (e v)
  decode bytes := if h : bytes.length = w then some (e.symm fun i => bytes.get ⟨i.val, by rw [h]; exact i.isLt⟩) else none
  length _ := List.length_ofFn
  inverse v := by
    rw [dif_pos (List.length_ofFn)]
    congr 1
    rw [Equiv.symm_apply_eq]
    funext i
    simp
  canonical payload v h := by
    split at h
    next hp =>
      cases Option.some.inj h
      apply List.ext_getElem
      · simp [hp]
      · intro i _ _
        simp
    next => cases h

/-! ### Toy circuits -/

def emptyQuads (O W F : Type) : Layered.QuadFragment O W F :=
  ⟨0, 0, Fin.elim0, Fin.elim0, []⟩

def emptyLocal (O W F : Type) : ConcreteAdapterTopology.Local O W F :=
  ⟨0, 0, emptyQuads O W F, [], []⟩

def emptyFragment (out mid : ℕ) (F : Type) : ConcreteTopology.Fragment out mid F :=
  ⟨0, 0, emptyQuads _ _ F, [], []⟩

theorem two_mul_le (n : ℕ) : 2 * n ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h2 : 2 ≤ 2 ^ (n + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ]; omega

/-- Wire `(side, i)` at cube index `side + 2 i`, inside `n+1` variables. -/
def layout : Adapter.Fragment.Layout where
  log n := n + 1
  index n := ((finProdFinEquiv.trans (finCongr (Nat.mul_comm 2 n))).toEmbedding.trans
    (Fin.castLEEmb (by rw [Nat.mul_comm]; exact two_mul_le n))).trans (cubeIndex (n + 1)).symm.toEmbedding

def output : Fin 2 ↪ Cube 1 := (cubeIndex 1).symm.toEmbedding

/-- `depth` complete hash layers above the adapter, each with one empty
fragment of component zero. -/
def above (F : Type) : (depth : ℕ) → ConcreteAdapterTopology.Above F 1 1
  | 0 => .hole
  | depth + 1 => .layer [emptyFragment 1 1 F] (above F depth)

def binary (depth : ℕ) : BinaryCircuit GF where
  input := 12
  nPublic := 0
  hashPrivate := 768
  final := 1
  out := 1
  upper := 1
  basis := cantor
  inputCapacity := by decide
  hashCapacity := le_refl _
  publicBits := Fin.elim0
  layout := layout
  output := output
  others := {
    first := ⟨[emptyLocal _ _ _]⟩
    pair := fun _ => ⟨[emptyLocal _ _ _]⟩
    final := ⟨[emptyLocal _ _ _]⟩ }
  carry := fun _ => none
  above := above GF depth

def prime : PrimeCircuit where
  out := 10
  input := 10
  nPublic := 0
  remaining := 0
  topology := .input
  inputCapacity := by decide
  publicInputs := Fin.elim0

def bounds : MdocIdentifiers.Bounds (binary 1) prime where
  inputFits := by decide +kernel
  privateFits := by decide +kernel
  padsFit := by decide +kernel
  binaryCellsFit := by decide +kernel
  primeCellsFit := by decide +kernel
  layerFits := by decide +kernel
  primeLayerFits := by decide +kernel
  committedFit := by decide +kernel
  hashDepthFit := by decide +kernel
  adapterDepth_lt_hashDepth := by decide +kernel
  primeDepthFit := by decide +kernel
  adapterDepthFit := by decide +kernel
  binaryRowsFit := by decide +kernel
  primeRowsFit := by decide +kernel

/-! ### Codecs, identifiers -/

/-- A codec from an injective fixed-width encoding; decoding inverts it on
its range and rejects everything else. -/
def codecOfEmbedding {F : Type} (w : ℕ) (pos : 0 < w) (small : w ≤ 128)
    (e : F ↪ (Fin w → TranscriptV2.Framing.Byte)) : TranscriptV2.Framing.FieldCodec F where
  width := w
  positive := pos
  buffer := small
  encode v := List.ofFn (e v)
  decode bytes := if h : ∃ v, List.ofFn (e v) = bytes then some (Classical.choose h) else none
  length _ := List.length_ofFn
  inverse v := by
    have h : ∃ x, List.ofFn (e x) = List.ofFn (e v) := ⟨v, rfl⟩
    rw [dif_pos h]
    congr 1
    exact e.injective (List.ofFn_injective (Classical.choose_spec h))
  canonical payload v h := by
    split at h
    next hp =>
      cases Option.some.inj h
      exact Classical.choose_spec hp
    next => cases h

def primeEmbedding : MdocRuntime.Prime ↪ (Fin 32 → TranscriptV2.Framing.Byte) where
  toFun a := (Protocol.RustSampler.le 32).symm ⟨((ZMod.finEquiv _).symm a).val,
    lt_of_lt_of_le (Fin.isLt _) Protocol.RustSampler.primeOrder_fits⟩
  inj' a b h := by
    have := congrArg Fin.val ((Protocol.RustSampler.le 32).symm.injective h)
    exact (ZMod.finEquiv _).symm.injective (Fin.ext this)

def scalars : MdocRuntime.Scalars GF where
  binary := codecOf 16 (by decide) (by decide) ((Protocol.RustSampler.gfBits cantor).symm.trans (Protocol.RustSampler.le 16).symm)
  prime := codecOfEmbedding 32 (by decide) (by decide) primeEmbedding
  binaryWidth := rfl
  primeWidth := rfl

def ids : MdocIdentifiers.Identifiers := ⟨fun _ => 0, [], [], fun _ _ => 0⟩

/-! ### Remaining structural premises -/

theorem fits : (MdocRuntime.geometry (binary 1).description prime.description (binary 1).plan prime.plan).roles.length < 2 ^ 64 := by
  decide +kernel

theorem bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
    (MdocRuntime.geometry (binary 1).description prime.description (binary 1).plan prime.plan) ≤
      CanonicalPrefix.maxLength := by
  decide +kernel

/-! ### A trivial adversary -/

def request : Mdoc.RuntimeSoundness.Request (binary 1) prime bounds :=
  ⟨⟨[], by decide⟩, Fin.elim0, fun _ => 0⟩

def adversary : Unit → Merkle.RandomOracle.Tree TranscriptV2.Framing.Bytes Digest
    (Mdoc.RuntimeSoundness.Request (binary 1) prime bounds × TranscriptV2.Framing.Bytes) 0 :=
  fun _ => .done (request, [])

theorem queryBound : ∀ coin oracle, (TranscriptV2.seen (adversary coin) oracle).card ≤ 0 := by
  intro coin oracle
  exact le_of_eq rfl

/-- Every premise of the deployed soundness endpoint, inhabited. -/
def soundness :=
  Mdoc.Soundness.averaged_ratio_le_rust (binary 1) prime cantor scalars ids bounds
    fits bodyFits (Omega := Unit) (fun _ _ => 0) adversary queryBound (by decide)

/-! ### Nondegeneracy -/

/-- The setup the endpoint is stated at, for the one external coin. -/
abbrev runtime := Mdoc.Setup.runtime (binary 1) prime cantor scalars
  (Mdoc.OracleSoundness.identifiers ids fun _ => 0) bounds

/-- The toy geometry has boundaries, so the fibers below are not vacuous. -/
theorem roles_pos : 0 < (MdocRuntime.geometry (binary 1).description prime.description (binary 1).plan
    prime.plan).roles.length := by
  decide +kernel

theorem setupWidth_le : Protocol.RustSampler.setupWidth runtime.protocol ≤ 2 ^ 40 := by
  decide +kernel

/-- Every boundary fiber of the Rust reader at the endpoint's setup is
positive: every challenge value is read by some PRF stream. -/
theorem fiber_pos (index history block) :
    0 < runtime.rustSampler.laws.fiber (.round index history block) :=
  Protocol.RustSampler.fiber_pos runtime.protocol rfl (by decide)
    (setupWidth_le.trans (by unfold Protocol.RustSampler.rustBlocks; norm_num)) index history block

run_cmd ProofAudit.standardAxioms #[``soundness, ``fiber_pos, ``roles_pos]

end LfzkV2.Current.Tests.MdocInstance
