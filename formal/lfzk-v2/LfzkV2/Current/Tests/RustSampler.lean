import LfzkV2.Current.Protocol.RustSampler
import LfzkV2.Current.Tests.ProofAudit

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

run_cmd ProofAudit.standardAxioms #[``sampler, ``data_uniform, ``fiber_pos, ``round_abort_le,
  ``round_abort_le_concrete, ``opening_abort, ``gfBits_repr, ``lazySampler_run,
  ``lazySampler_uniform, ``lazySampler_exists, ``lazySampler_abort]

end LfzkV2.Current.Tests.RustSampler
