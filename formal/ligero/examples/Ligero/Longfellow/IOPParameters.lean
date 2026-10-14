import examples.Ligero.Certificate
import LigeroFamily.Soundness.ExtractionRate

/-! Protocol tags and the actual Reed--Solomon instance bridge shared by the
coarse and profiled scalar IOP certificates for all three variants. -/
namespace Ligero.Examples.Grid.LongfellowIOP
open LigeroFamily CodingTheory

inductive Variant where
  | v1 | v2 | v3
  deriving DecidableEq, Repr

inductive Route where
  | triples | johnson
  deriving DecidableEq, Repr

noncomputable def certificateCode (c : Certificate) {F : Type*} [Field F] [DecidableEq F] {w : ℕ}
    (D : ReedSolomon.Domain F c.openings w c.n)
    (hkn : c.openings + w ≤ c.n) := ReedSolomon.multiplicativeCode D hkn

theorem certificateCodeFacts (c : Certificate)
    (hk : 0 < c.k) (hd : c.d = c.n - c.k + 1)
    {F : Type*} [Field F] [DecidableEq F] {w : ℕ}
    (hdim : c.openings + w = c.k)
    (D : ReedSolomon.Domain F c.openings w c.n)
    (hkn : c.openings + w ≤ c.n) :
    (certificateCode c D hkn).k = c.k ∧
    HasMinimumDistanceAtLeast (certificateCode c D hkn).baseCode c.d ∧
    Nonempty (JBAgreement.RSPresentation c.n c.k (certificateCode c D hkn).baseCode) := by
  have hpos : 1 ≤ c.openings + w := by omega
  refine ⟨by simpa [certificateCode, MultiplicativeCode.k_eq] using hdim, ?_, ?_⟩
  · simpa [certificateCode, hdim, hd] using ReedSolomon.baseCode_minimum_distance D hpos hkn
  · simpa [certificateCode, hdim] using
      (show Nonempty (JBAgreement.RSPresentation c.n (c.openings + w)
        (ReedSolomon.multiplicativeCode D hkn).baseCode) from ⟨JBAgreement.rsPresentation D hpos hkn⟩)

end Ligero.Examples.Grid.LongfellowIOP
