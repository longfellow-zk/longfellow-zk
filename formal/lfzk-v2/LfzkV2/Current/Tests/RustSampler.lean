import LfzkV2.Current.Protocol.RustSampler
import LfzkV2.Current.Tests.ProofAudit
import WitnessSelection.Algebra

/-! The Rust reader's draw widths, against `Reading::nat`, `elt_field` and
`choose` in `rust/src/runtime/v2/transcript/session.rs`. -/
namespace LfzkV2.Current.Tests.RustSampler
open LfzkV2.Current.Protocol.RustSampler

-- `nat(2443)`: `bits = 12`, two bytes, mask `0xfff`.
example : natBits 2443 = 12 := by decide
example : natLen 2443 = 2 := by decide
example : 2 ^ natBits 2443 - 1 = 0xfff := by decide
-- One byte up to 256, two from 257; `nat(1)` reads nothing.
example : natLen 256 = 1 := by decide
example : natLen 257 = 2 := by decide
example : (Prog.nat 1 (by decide)).width = 0 := rfl
example : (Prog.nat 2 (by decide)).width = 1 := rfl
-- Field elements: 16 bytes for GF(2^128), 32 for P-256.
example {B : Type} (bits : Fin (256 ^ 16) ≃ B) : (gfDraw bits).width = 16 := rfl
example : fpDraw.width = 32 := rfl
-- `choose(2443, 84)`: 84 offsets of two bytes each, reject-free.
example : (Prog.opening 2443 84).width = 168 := by decide +kernel
example : (Prog.opening 2443 84).draws = 84 := by decide +kernel
-- Rust's PRF counter stops before `2^64 - 1`.
example : rustBlocks = 18446744073709551615 := by decide

-- Draw order. A fingerprint round reads the host field's two coefficient
-- vectors, then the split field's (`Fields` in foreign/compose.rs and
-- `field_coefficients` in witness_selection/transcript.rs)...
example {B : Type} [Field B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B) (nb np kb kp n t : ℕ) :
    kindProg bits nb np kb kp n t .fingerprints =
      .seq (.seq ((gfDraw bits).vec nb) ((gfDraw bits).vec nb)) (.seq (fpDraw.vec np) (fpDraw.vec np)) :=
  rfl
-- ... and Lean's first coefficient vector pairs with the first mask cell, as
-- Rust's vector `j` pairs with mask cell `n + j` (`authenticate` in
-- witness_selection.rs).
example {F ι : Type} [Field F] [Fintype ι] (a : WitnessSelection.Coins F ι)
    (w : WitnessSelection.Candidate F ι) :
    WitnessSelection.fingerprint a w = (w.2.1 + WitnessSelection.dot a.1 w.1, w.2.2 + WitnessSelection.dot a.2 w.1) :=
  rfl
-- Batching reads the host's weights and evaluations, then the split field's.
example {B : Type} [Field B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B) (nb np kb kp n t : ℕ) :
    kindProg bits nb np kb kp n t .batching = .seq ((gfDraw bits).vec kb) (fpDraw.vec kp) := rfl
-- `eta` follows the prime frontend's coordinates in the same answer.
example {B : Type} [Field B] [DecidableEq B] (bits : Fin (256 ^ 16) ≃ B) (nb np kb kp n t count : ℕ) :
    kindProg bits nb np kb kp n t (.primeEta count) = .seq (fpDraw.vec count) fpNonzeroDraw := rfl

run_cmd ProofAudit.standardAxioms #[``sampler, ``data_uniform, ``fiber_pos, ``round_abort_le,
  ``round_abort_le_concrete, ``opening_abort, ``gfBits_repr, ``lazySampler_run,
  ``lazySampler_uniform, ``lazySampler_exists, ``lazySampler_abort, ``Prog.vec_parse_succ]

end LfzkV2.Current.Tests.RustSampler
