import polygero.Local.Parameters
import polygero.Recursion.Protocol

/-! A checked local parameter certificate for each recursive invocation. -/

namespace RecursivePolygero
open Finset ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Local error certificates at every invocation. -/
inductive Protocol.ProfileProof : {I : Instance F} →
    (protocol : Protocol I) → ProfileCertificate I → Type 1
  | terminal {I : Instance F} (p : ProfileCertificate I) : ProfileProof (.terminal I) p
  | step {I : Instance F} {child : Child I} {tail : Protocol child.instance}
      (p : ProfileCertificate I) {childParameters : ProfileCertificate child.instance}
      (rest : ProfileProof tail childParameters) : ProfileProof (.step child tail) p

/-- Local Hahn/Delsarte error certificates at every recursive invocation. -/
inductive Protocol.HahnProfileProof : {I : Instance F} →
    (protocol : Protocol I) → HahnSystemCertificate I → Type 1
  | terminal {I : Instance F} (p : HahnSystemCertificate I) : HahnProfileProof (.terminal I) p
  | step {I : Instance F} {child : Child I} {tail : Protocol child.instance}
      (p : HahnSystemCertificate I) {childParameters : HahnSystemCertificate child.instance}
      (rest : HahnProfileProof tail childParameters) : HahnProfileProof (.step child tail) p

/-- Canonical lifting of a `ProfileProof` to a `HahnProfileProof`. -/
noncomputable def Protocol.ProfileProof.toHahnProfileProof :
    {I : Instance F} → {protocol : Protocol I} → {p : ProfileCertificate I} →
    protocol.ProfileProof p → protocol.HahnProfileProof p.toHahnSystemCertificate
  | _, _, _, .terminal p => .terminal p.toHahnSystemCertificate
  | _, _, _, .step p rest => .step p.toHahnSystemCertificate rest.toHahnProfileProof

end RecursivePolygero
