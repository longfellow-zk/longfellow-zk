import LfzkV2.Current.Protocol.Sampling
import LfzkV2.Current.Protocol.RustSamplerDraws
import LfzkV2.Current.Protocol.RustSamplerStream

/-! The v2 Rust challenge reader as one fixed `Protocol.Sampler` for every
setup whose binary field is GF(2^128).

At each ordinary boundary the reader runs the draws of the boundary's role
(`roleProg`) on the boundary's PRF stream, lazily and capped at Rust's
counter limit (`RustSamplerStream`). The final seal point samples nothing:
the seal is a raw PRF block, not a field challenge. The laws are proved once
for all setups: every value of a boundary has the same number of streams
(`sampler`), each value has at least one when the reject-free width fits the
cap (`fiber_pos`), and a boundary aborts on a vanishing fraction of streams
(`round_abort_le`).

## Draw order

Uniformity does not depend on the order of draws; the correspondence with
Rust does. Each role reads, in order (`Kind` is `StrandRoleSampling.Kind`):

* `binary count`, `prime count`: `count` elements by `Reading::elt_field`;
  coordinate `i` is the `i`th draw (`Prog.vec_parse_succ`). These are the frontend's round
  challenges, layer alphas and stage weights
  (`rust/src/runtime/v2/sumcheck/transcript.rs`: `round_challenge`,
  `end_layer`, `draw_top`, `draw_stage`, `input_assertions`) and the packing
  challenge (`rust/src/runtime/v2/dual_packing/transcript.rs`), in the
  coordinate order of `FrontendSchedule`.
* `primeEta count`: the coordinates, then `eta` by `Reading::nonzero`, read
  further from the same answer (`eta` in
  `rust/src/runtime/v2/zk/split/transcript.rs`).
* `binaryNonzero`, `primeNonzero`: one `Reading::nonzero`
  (`terminal_challenge`).
* `conversion`: two `Reading::nonzero` over P-256, the pair in order
  (`draw_pair` in `rust/src/runtime/v2/foreign/adapter/p256/transcript.rs`).
* `fingerprints`: for the host GF(2^128) participant, then the split P-256
  participant (`Fields` in `rust/src/runtime/v2/foreign/compose.rs`), two
  vectors of `cells` elements each (`field_coefficients` in
  `rust/src/runtime/v2/witness_selection/transcript.rs`), coordinate `w` of
  vector `j` the `w`th draw of that vector. Rust pairs vector `j` with mask
  cell `n + j` (`authenticate` in `rust/src/runtime/v2/witness_selection.rs`);
  `WitnessSelection.fingerprint` pairs the first Lean coin with the first
  mask and the second with the second, so Lean's
  `((binary₀, binary₁), (prime₀, prime₁))` is Rust's draw order.
* `batching`: for the host, then the split participant
  (`challenges` in `rust/src/runtime/v2/polygero/participant.rs`), one weight
  per equation, then `s+1` evaluations per batched row
  (`challenges` in `rust/src/runtime/v2/polygero/transcript.rs`); this is the
  flat order of `BackendChallenges.coordinate`.
* `opening`: `Reading::choose(out, n, ..)` with `out.len() = t`
  (`queries` in `rust/src/runtime/v2/polygero/transcript.rs`).

A GF(2^128) element's bit `i` is the coefficient of the setup's `i`th packing
basis vector (`gfBits_repr`), which is Rust's `native_basis` (see
`RustSamplerDraws`). The correspondence takes three facts from the model
rather than from Rust: the packing basis is the field representation's, each
frontend role's coordinates follow `FrontendSchedule`, and each
participant's `cells` is its original cell count in `CellLayout`. -/
noncomputable section
namespace LfzkV2.Current.Protocol.RustSampler
open Merkle.RandomOracle TranscriptV2 StrandRoleSampling
open scoped Classical

local notation "N" => ZMod Adapter.Mdoc.primeOrder

instance primeOrder_neZero : NeZero Adapter.Mdoc.primeOrder :=
  ⟨by unfold Adapter.Mdoc.primeOrder; decide⟩

theorem primeOrder_fits : Adapter.Mdoc.primeOrder ≤ 256 ^ 32 := by
  unfold Adapter.Mdoc.primeOrder; decide

/-- P-256 rejects fewer than half of its 32-byte attempts. -/
theorem primeOrder_large : 256 ^ 32 ≤ 2 * (Adapter.Mdoc.primeOrder - 1) := by
  unfold Adapter.Mdoc.primeOrder; decide

/-! ## Elementary draws -/

def gfDraw {B : Type} (bits : Fin (256 ^ 16) ≃ B) : Prog B :=
  .draw 16 (by decide) fun c => gf bits (le 16 c)

def gfNonzeroDraw {B : Type} [Zero B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B) :
    Prog (Linear.TerminalSampling.Nonzero B) :=
  .draw 16 (by decide) fun c => gfNonzero bits (le 16 c)

def fpDraw : Prog N := .draw 32 (by decide) fun c => fp _ (le 32 c)

def fpNonzeroDraw : Prog (Linear.TerminalSampling.Nonzero N) :=
  .draw 32 (by decide) fun c => fpNonzero _ (le 32 c)

theorem fpDraw_halving : fpDraw.Halving := by
  show reject _ _ ≤ 1 / 2
  rw [fp_reject _ primeOrder_fits]
  have h : ((256 ^ 32 : ℕ) : ℚ) ≤ 2 * ((Adapter.Mdoc.primeOrder - 1 : ℕ) : ℚ) := by
    exact_mod_cast primeOrder_large
  have h1 : ((Adapter.Mdoc.primeOrder - 1 : ℕ) : ℚ) ≤ Adapter.Mdoc.primeOrder := by
    exact_mod_cast Nat.sub_le _ _
  push_cast at h
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
  linarith

theorem fpNonzeroDraw_halving : fpNonzeroDraw.Halving := by
  show reject _ _ ≤ 1 / 2
  rw [fpNonzero_reject _ primeOrder_fits]
  have h : ((256 ^ 32 : ℕ) : ℚ) ≤ 2 * ((Adapter.Mdoc.primeOrder - 1 : ℕ) : ℚ) := by
    exact_mod_cast primeOrder_large
  rw [Nat.cast_sub (NeZero.one_le)] at h
  push_cast at h
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
  linarith

theorem gfDraw_halving {B : Type} (bits : Fin (256 ^ 16) ≃ B) : (gfDraw bits).Halving := by
  show reject _ _ ≤ 1 / 2
  rw [gf_reject]; norm_num

theorem gfNonzeroDraw_halving {B : Type} [Zero B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B) :
    (gfNonzeroDraw bits).Halving := by
  show reject _ _ ≤ 1 / 2
  rw [gfNonzero_reject]; norm_num

/-! ## Role programs -/

/-- The draws of one role, in Rust's order (see the module documentation).
`nb` and `np` are the participants' original cell counts, `kb` and `kp`
their batching sample counts, and the opening chooses `t` of `n` columns. -/
def kindProg {B : Type} [Field B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B)
    (nb np kb kp n t : ℕ) :
    (kind : Kind) → Prog (Value B N (Fin nb) (Fin np) (Fin kb → B) (Fin kp → N) (Fin t ↪ Fin n) kind)
  | .binary count => (gfDraw bits).vec count
  | .binaryNonzero => gfNonzeroDraw bits
  | .prime count => fpDraw.vec count
  | .primeEta count => .seq (fpDraw.vec count) fpNonzeroDraw
  | .primeNonzero => fpNonzeroDraw
  | .conversion => .seq fpNonzeroDraw fpNonzeroDraw
  | .fingerprints => .seq (.seq ((gfDraw bits).vec nb) ((gfDraw bits).vec nb))
      (.seq (fpDraw.vec np) (fpDraw.vec np))
  | .batching => .seq ((gfDraw bits).vec kb) (fpDraw.vec kp)
  | .opening => Prog.opening n t

section Kind
variable {B : Type} [Field B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B) (nb np kb kp n t : ℕ)

theorem kindProg_lawful (kind : Kind) : (kindProg bits nb np kb kp n t kind).Lawful := by
  have gfL : (gfDraw bits).Lawful := gf_balanced bits
  have gfNL : (gfNonzeroDraw bits).Lawful := gfNonzero_balanced bits
  have fpL : fpDraw.Lawful := fp_balanced _ primeOrder_fits
  have fpNL : fpNonzeroDraw.Lawful := fpNonzero_balanced _ primeOrder_fits
  cases kind with
  | binary count => exact (gfDraw bits).vec_lawful gfL count
  | binaryNonzero => exact gfNL
  | prime count => exact fpDraw.vec_lawful fpL count
  | primeEta count => exact ⟨fpDraw.vec_lawful fpL count, fpNL⟩
  | primeNonzero => exact fpNL
  | conversion => exact ⟨fpNL, fpNL⟩
  | fingerprints =>
      exact ⟨⟨(gfDraw bits).vec_lawful gfL nb, (gfDraw bits).vec_lawful gfL nb⟩,
        ⟨fpDraw.vec_lawful fpL np, fpDraw.vec_lawful fpL np⟩⟩
  | batching => exact ⟨(gfDraw bits).vec_lawful gfL kb, fpDraw.vec_lawful fpL kp⟩
  | opening => exact Prog.opening_lawful n t

theorem kindProg_onto (queries : t ≤ n) (kind : Kind) : (kindProg bits nb np kb kp n t kind).Onto := by
  have gfO : (gfDraw bits).Onto := gf_onto bits
  have gfNO : (gfNonzeroDraw bits).Onto := gfNonzero_onto bits
  have fpO : fpDraw.Onto := fp_onto _ primeOrder_fits
  have fpNO : fpNonzeroDraw.Onto := fpNonzero_onto _ primeOrder_fits
  cases kind with
  | binary count => exact (gfDraw bits).vec_onto gfO count
  | binaryNonzero => exact gfNO
  | prime count => exact fpDraw.vec_onto fpO count
  | primeEta count => exact ⟨fpDraw.vec_onto fpO count, fpNO⟩
  | primeNonzero => exact fpNO
  | conversion => exact ⟨fpNO, fpNO⟩
  | fingerprints =>
      exact ⟨⟨(gfDraw bits).vec_onto gfO nb, (gfDraw bits).vec_onto gfO nb⟩,
        ⟨fpDraw.vec_onto fpO np, fpDraw.vec_onto fpO np⟩⟩
  | batching => exact ⟨(gfDraw bits).vec_onto gfO kb, fpDraw.vec_onto fpO kp⟩
  | opening => exact Prog.opening_onto n t queries

theorem kindProg_halving (queries : t ≤ n) (kind : Kind) :
    (kindProg bits nb np kb kp n t kind).Halving := by
  have gfH := gfDraw_halving bits
  have gfNH := gfNonzeroDraw_halving bits
  cases kind with
  | binary count => exact (gfDraw bits).vec_halving gfH count
  | binaryNonzero => exact gfNH
  | prime count => exact fpDraw.vec_halving fpDraw_halving count
  | primeEta count => exact ⟨fpDraw.vec_halving fpDraw_halving count, fpNonzeroDraw_halving⟩
  | primeNonzero => exact fpNonzeroDraw_halving
  | conversion => exact ⟨fpNonzeroDraw_halving, fpNonzeroDraw_halving⟩
  | fingerprints =>
      exact ⟨⟨(gfDraw bits).vec_halving gfH nb, (gfDraw bits).vec_halving gfH nb⟩,
        ⟨fpDraw.vec_halving fpDraw_halving np, fpDraw.vec_halving fpDraw_halving np⟩⟩
  | batching => exact ⟨(gfDraw bits).vec_halving gfH kb, fpDraw.vec_halving fpDraw_halving kp⟩
  | opening => exact Prog.opening_halving n t queries

theorem natLen_le (m : ℕ) (h : 0 < m) : natLen m ≤ m := by
  have hs : Nat.size (m - 1) ≤ m - 1 := Nat.size_le.mpr (Nat.lt_two_pow_self)
  unfold natLen natBits
  omega

theorem Prog.nat_width_le (m : ℕ) (h : 0 < m) : (Prog.nat m h).width ≤ m := by
  unfold Prog.nat
  split
  · exact Nat.zero_le _
  · exact natLen_le m h

theorem Prog.choices_width_le : (m s : ℕ) → s ≤ m → (Prog.choices m s).width ≤ s * m
  | _, 0, _ => by simp [Prog.choices, Prog.width]
  | 0, _ + 1, h => by omega
  | m + 1, s + 1, h => by
      have := Prog.nat_width_le (m + 1) (Nat.succ_pos m)
      have := Prog.choices_width_le m s (by omega)
      simp only [Prog.choices, Prog.width]
      nlinarith

/-- A bound on every role's reject-free width, from the role's capacities. -/
def widthBound (nb np kb kp n t binaryCapacity primeCapacity : ℕ) : ℕ :=
  16 * binaryCapacity + 32 * primeCapacity + 64 + 32 * nb + 64 * np + 16 * kb + 32 * kp + t * n

theorem kindProg_width_le (binaryCapacity primeCapacity : ℕ) (queries : t ≤ n) (kind : Kind)
    (fits : Fits binaryCapacity primeCapacity kind) :
    (kindProg bits nb np kb kp n t kind).width ≤
      widthBound nb np kb kp n t binaryCapacity primeCapacity := by
  unfold widthBound
  cases kind with
  | binary count =>
      have : count ≤ binaryCapacity := fits
      change ((gfDraw bits).vec count).width ≤ _
      rw [Prog.vec_width]; change count * 16 ≤ _; nlinarith
  | binaryNonzero => simp only [kindProg, gfNonzeroDraw, Prog.width]; omega
  | prime count =>
      have : count ≤ primeCapacity := fits
      change (fpDraw.vec count).width ≤ _
      rw [Prog.vec_width]; change count * 32 ≤ _; nlinarith
  | primeEta count =>
      have : count ≤ primeCapacity := fits
      change (fpDraw.vec count).width + 32 ≤ _
      rw [Prog.vec_width]; change count * 32 + 32 ≤ _; nlinarith
  | primeNonzero => simp only [kindProg, fpNonzeroDraw, Prog.width]; omega
  | conversion => simp only [kindProg, fpNonzeroDraw, Prog.width]; omega
  | fingerprints =>
      change ((gfDraw bits).vec nb).width + ((gfDraw bits).vec nb).width +
        ((fpDraw.vec np).width + (fpDraw.vec np).width) ≤ _
      simp only [Prog.vec_width]; change nb * 16 + nb * 16 + (np * 32 + np * 32) ≤ _; nlinarith
  | batching =>
      change ((gfDraw bits).vec kb).width + (fpDraw.vec kp).width ≤ _
      simp only [Prog.vec_width]; change kb * 16 + kp * 32 ≤ _; nlinarith
  | opening =>
      have := Prog.choices_width_le n t queries
      simp only [kindProg, Prog.opening, Prog.width]
      nlinarith

theorem kindProg_draws_le (kind : Kind) :
    (kindProg bits nb np kb kp n t kind).draws ≤ (kindProg bits nb np kb kp n t kind).width :=
  Prog.draws_le_width _

omit [DecidableEq B] in
theorem valueNonempty (queries : t ≤ n) (kind : Kind) :
    Nonempty (Value B N (Fin nb) (Fin np) (Fin kb → B) (Fin kp → N) (Fin t ↪ Fin n) kind) := by
  have nz : ∀ (F : Type) [Field F], Nonempty (Linear.TerminalSampling.Nonzero F) :=
    fun F _ => ⟨⟨1, one_ne_zero⟩⟩
  cases kind <;> simp only [Value] <;>
    first
    | exact nz _
    | exact ⟨Fin.castLEEmb queries⟩
    | exact inferInstance

end Kind

/-! ## The sampler of a setup -/

variable {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))
variable (degree : S.binary.degree = 128)

/-- The binary bit order: Rust's `native_basis` is the setup's packing basis. -/
def bits : Fin (256 ^ 16) ≃ B := gfBits (S.binary.basis.reindex (finCongr degree))

/-- The draws of the boundary at `index`. -/
def roleProg (index : Fin g.roles.length) :
    Prog (Value B N S.binary.Original S.prime.Original (IdealRuntime.RawBinary S.P S.countBinary)
      (IdealRuntime.RawPrime S.R S.countPrime) (Fin c.t ↪ Fin c.n)
      (roleKind S.binary.degree (S.prime.circuit.layers + 1) (g.roles.get index))) :=
  kindProg (bits S degree) _ _ _ _ _ _
    (roleKind S.binary.degree (S.prime.circuit.layers + 1) (g.roles.get index))

/-- The reader at every point: a boundary's draws, lazily, at Rust's cap. -/
def data : SamplerData S rustBlocks where
  sample
    | .round index _ _ => lazySampler (roleProg S degree index)
        rustBlocks rustBlocks_fits
    | .finalSeal _ _ => .done none

/-- Fibers of a sampler that is uniform over its values: the count at any
value, or zero for an empty value type. -/
def fiberOf {V : Type} {n : ℕ} (t : Tree Strand.Word Strand.Digest (Option V) n) : ℕ :=
  if h : Nonempty V then Nat.card {H : Strand.Word → Strand.Digest // (t.run H).1 = some (Classical.choice h)} else 0

theorem filter_card {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = Nat.card {x // P x} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem balanced_of_uniform {V : Type} {n : ℕ} (t : Tree Strand.Word Strand.Digest (Option V) n)
    (uniform : ∀ v v' : V, Nat.card {H : Strand.Word → Strand.Digest // (t.run H).1 = some v} =
      Nat.card {H : Strand.Word → Strand.Digest // (t.run H).1 = some v'})
    (v : V) [DecidablePred fun H : Strand.Word → Strand.Digest => (t.run H).1 = some v] :
    (Finset.univ.filter fun H : Strand.Word → Strand.Digest => (t.run H).1 = some v).card = fiberOf t := by
  rw [filter_card, fiberOf, dif_pos ⟨v⟩]
  exact uniform _ _

theorem data_uniform (point : S.Point) (v v' : S.RoleValue point) :
    Nat.card {H : Strand.Word → Strand.Digest // (((data S degree).sample point).run H).1 = some v} =
      Nat.card {H : Strand.Word → Strand.Digest // (((data S degree).sample point).run H).1 = some v'} := by
  cases point with
  | round index history block =>
      exact lazySampler_uniform _ (kindProg_lawful _ _ _ _ _ _ _ _) _ rustBlocks_fits v v'
  | finalSeal history body =>
      have empty : ∀ x, Nat.card {H : Strand.Word → Strand.Digest //
          (((data S degree).sample (.finalSeal history body)).run H).1 = some x} = 0 := by
        intro x
        rw [Nat.card_eq_zero]
        left
        constructor
        rintro ⟨H, h⟩
        cases h
      rw [empty, empty]

/-- The Rust challenge reader of the setup, with its proved laws. -/
def sampler : Sampler S rustBlocks where
  data := data S degree
  laws := {
    fiber := fun point => fiberOf ((data S degree).sample point)
    uniform := fun point value => balanced_of_uniform _ (data_uniform S degree point) value }

theorem sampler_sample_round (index : Fin g.roles.length) (history block) :
    (sampler S degree).data.sample (.round index history block) =
      lazySampler (roleProg S degree index) rustBlocks rustBlocks_fits :=
  rfl

/-- The reject-free width of every boundary of the setup is at most this. -/
def setupWidth : ℕ :=
  widthBound S.binary.cells (CellLayout.Prime.cells S.prime.remaining S.prime.pads)
    (BackendChallenges.size S.countBinary S.P.backend.nw S.P.backend.s)
    (BackendChallenges.size S.countPrime S.R.backend.nw S.R.backend.s) c.n c.t
    S.binaryCapacity S.primeCapacity

theorem roleProg_width_le (queries : c.t ≤ c.n) (index : Fin g.roles.length) :
    (roleProg S degree index).width ≤ setupWidth S :=
  kindProg_width_le _ _ _ _ _ _ _ _ _ queries _ (S.roleFits index)

/-- Nondegeneracy: when the setup's widths fit Rust's cap, every boundary
value is read by some stream, so every boundary fiber is positive. -/
theorem fiber_pos (queries : c.t ≤ c.n) (wide : setupWidth S ≤ rustBlocks * 32)
    (index : Fin g.roles.length) (history block) :
    0 < (sampler S degree).laws.fiber (.round index history block) := by
  change 0 < fiberOf _
  have ne : Nonempty (S.RoleValue (.round index history block)) := valueNonempty _ _ _ _ _ _ queries _
  unfold fiberOf
  rw [dif_pos ne]
  obtain ⟨H, hH⟩ := lazySampler_exists _ (kindProg_onto _ _ _ _ _ _ _ queries _) rustBlocks
    rustBlocks_fits ((roleProg_width_le S degree queries index).trans wide)
    (Classical.choice ne)
  have : Nonempty {H : Strand.Word → Strand.Digest //
      (((data S degree).sample (.round index history block)).run H).1 = some (Classical.choice ne)} :=
    ⟨⟨H, hH⟩⟩
  exact Nat.card_pos

/-! ## Availability -/

/-- A boundary aborts on at most `width * (1/2)^j` of all PRF streams, for
every `j` with `j` attempts' worth of each draw within the cap. -/
theorem roleProg_abort_le (queries : c.t ≤ c.n) (index : Fin g.roles.length) (j : ℕ)
    (wide : j * (roleProg S degree index).width ≤ rustBlocks * 32) :
    (Nat.card {H : Strand.Word → Strand.Digest //
        ((lazySampler (roleProg S degree index) rustBlocks rustBlocks_fits).run H).1 = none} : ℚ) /
        Nat.card (Strand.Word → Strand.Digest) ≤
      (roleProg S degree index).width * (1 / 2 : ℚ) ^ j := by
  refine (le_of_eq (lazySampler_abort _ _ _)).trans ?_
  refine ((Prog.read_abort _ j _ wide).trans
    (Prog.abortSum_le_halving j _ (kindProg_halving _ _ _ _ _ _ _ queries _))).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Prog.draws_le_width _

theorem round_abort_le (queries : c.t ≤ c.n) (index : Fin g.roles.length) (history block) (j : ℕ)
    (wide : j * (roleProg S degree index).width ≤ rustBlocks * 32) :
    (Nat.card {H : Strand.Word → Strand.Digest //
        (((sampler S degree).data.sample (.round index history block)).run H).1 = none} : ℚ) /
        Nat.card (Strand.Word → Strand.Digest) ≤
      (roleProg S degree index).width * (1 / 2 : ℚ) ^ j :=
  roleProg_abort_le S degree queries index j wide

/-- A concrete bound: when every boundary's reject-free width is at most
`2^40` bytes, each boundary aborts on at most `2^-128` of its PRF streams. -/
theorem round_abort_le_concrete (queries : c.t ≤ c.n) (small : setupWidth S ≤ 2 ^ 40)
    (index : Fin g.roles.length) (history block) :
    (Nat.card {H : Strand.Word → Strand.Digest //
        (((sampler S degree).data.sample (.round index history block)).run H).1 = none} : ℚ) /
        Nat.card (Strand.Word → Strand.Digest) ≤ 1 / 2 ^ 128 := by
  have hw := (roleProg_width_le S degree queries index).trans small
  have bound := round_abort_le S degree queries index history block (2 ^ 20) (by
    unfold rustBlocks
    calc 2 ^ 20 * _ ≤ 2 ^ 20 * 2 ^ 40 := Nat.mul_le_mul_left _ hw
      _ ≤ (2 ^ 64 - 1) * 32 := by norm_num)
  refine bound.trans ?_
  have hw' : ((roleProg S degree index).width : ℚ) ≤ 2 ^ 40 := by
    exact_mod_cast hw
  have hp : (1 / 2 : ℚ) ^ (2 ^ 20) ≤ (1 / 2) ^ 168 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  calc _ ≤ (2 : ℚ) ^ 40 * (1 / 2) ^ 168 :=
        mul_le_mul hw' hp (by positivity) (by positivity)
    _ = 1 / 2 ^ 128 := by norm_num

end LfzkV2.Current.Protocol.RustSampler
