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

end RecursivePolygero
