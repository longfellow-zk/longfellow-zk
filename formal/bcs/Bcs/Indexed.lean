import Bcs.Compiled
import Merkle.Indexed.Codec

/-! The algebraic compiler's locality is independent of the hash encoding.
This verifier uses indexed authentication and the existing opening checks. -/
namespace Bcs.Compiler

variable {Statement Oracle Challenge Response Query : Type*}
variable {Opening : Query → Type*} {Salt M D Enc : Type*} {n : ℕ}

def AcceptsIndexed [Inhabited D]
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (S : Merkle.Indexed.Scheme Salt M D Enc) (statement : Statement) (root : D)
    (challenge : Challenge) (response : Response) (query : Query)
    (claim : Merkle.MH.OpeningClaim n Salt M D) : Prop :=
  claim.I = K.indices query ∧
    Merkle.Indexed.Accepts S n root claim.I claim.a claim.pf ∧
    K.protocol.verify statement challenge response query
      (K.protocol.openOracle (K.oracleOfClaim claim.a) query) = true

theorem verify_of_acceptsIndexed [Inhabited D]
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (S : Merkle.Indexed.Scheme Salt M D Enc) (statement : Statement) (root : D)
    (challenge : Challenge) (response : Response) (query : Query)
    (claim : Merkle.MH.OpeningClaim n Salt M D) (oracle : Oracle)
    (agree : ∀ i ∈ claim.I, K.columns oracle i = claim.a i)
    (accepted : K.AcceptsIndexed S statement root challenge response query claim) :
    K.protocol.verify statement challenge response query (K.protocol.openOracle oracle query) = true := by
  obtain ⟨indices,_,verified⟩ := accepted
  have same := K.open_congr oracle (K.oracleOfClaim claim.a) query (by
    intro i member
    rw [columns_oracleOfClaim]
    exact agree i (indices.symm ▸ member))
  rw [same]
  exact verified

end Bcs.Compiler
