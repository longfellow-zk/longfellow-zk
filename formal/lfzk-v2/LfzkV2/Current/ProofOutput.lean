import LfzkV2.Current.CanonicalPrefix
import LfzkV2.Current.RuntimeAdaptive
import LfzkV2.Current.ByteOracleTransport

/-! Normalize arbitrary serialized proof outputs through the actual complete
proof parser. This is a pure output map: it preserves every adversary query,
answer and Merkle slot. Malformed output is rejected separately; its unused
fallback proof needs no correctness or rejection property. -/
noncomputable section
namespace LfzkV2.Current.ProofOutput
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

section Map
variable {QL DL QR DR Out Result : Type}

def map (f : Out → Result) : {left right : ℕ} →
    TwoOracleTree QL DL QR DR Out left right → TwoOracleTree QL DL QR DR Result left right
  | _, _, .done output => .done (f output)
  | _, _, .queryLeft query next => .queryLeft query fun answer => map f (next answer)
  | _, _, .queryRight query next => .queryRight query fun answer => map f (next answer)

theorem fixLeft_map [DecidableEq QL] (f : Out → Result) {left right size : ℕ}
    (body : TwoOracleTree QL DL QR DR Out left right) (tape : Fin size → DL)
    (dflt : DL) (seen : List QL) :
    fixLeft tape dflt (map f body) seen = (fixLeft tape dflt body seen).map f := by
  induction body generalizing seen with
  | done _ => rfl
  | queryLeft query next ih => exact ih _ _
  | queryRight query next ih =>
      simp only [map,fixLeft,Merkle.RandomOracle.Tree.map]
      exact congrArg (Tree.query query) (funext fun answer => ih answer seen)

theorem run_map [DecidableEq QL] (f : Out → Result) {left right size : ℕ}
    (body : TwoOracleTree QL DL QR DR Out left right) (tape : Fin size → DL)
    (dflt : DL) (seen : List QL) (H : QR → DR) :
    (fixLeft tape dflt (map f body) seen).run H =
      (f ((fixLeft tape dflt body seen).run H).1,((fixLeft tape dflt body seen).run H).2) := by
  rw [fixLeft_map,Merkle.RandomOracle.Tree.run_map]

end Map

variable {g : Geometry} {fields : Fields} {Advice Request : Type}
variable (complete : WholeCodec (Proof g fields Advice (OpeningBody.Authentication g)))

/-- The complete-proof parser of a format: the body and its seal block. -/
def read (bytes : Bytes) : Option (Proof g fields Advice (OpeningBody.Authentication g)) :=
  complete.decode bytes

theorem read_encode (proof : Proof g fields Advice (OpeningBody.Authentication g)) :
    read complete (complete.encode proof) = some proof :=
  complete.inverse proof

/-- A successful output parser accounts for the complete original stream,
including its final seal and with no ignored trailing bytes. -/
theorem read_canonical (bytes : Bytes) (proof : Proof g fields Advice (OpeningBody.Authentication g))
    (h : read complete bytes = some proof) : complete.encode proof = bytes :=
  (complete.canonical bytes proof h).symm

def decode (fallback : Proof g fields Advice (OpeningBody.Authentication g)) (raw : Request × Bytes) :
    RuntimeAdaptive.Output (g := g) (fields := fields) (Advice := Advice)
      (Auth := OpeningBody.Authentication g) (Request := Request) :=
  ⟨raw.1,(read complete raw.2).getD fallback⟩

end LfzkV2.Current.ProofOutput
