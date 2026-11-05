import LfzkV2.Joint.Backend
import LfzkV2.Joint.Replay

/-! The mdoc tuple is the two-position instance of the ordered typed family.
Its leaf and opening remain a single family object. -/

namespace LfzkV2.Joint.Pair

open RecursivePolygero LigeroFamily Merkle Merkle.MH Replay
open scoped Classical

variable {k s n t : ℕ} (P₁ P₂ : Participant k s n t)

def family : Family k s n t where
  count := 2
  nonempty := by decide
  participant := Fin.cons P₁ (Fin.cons P₂ Fin.elim0)

def statementEquiv : (family P₁ P₂).Statement ≃ P₁.Statement × P₂.Statement :=
  piFinTwoEquiv _

def oracleEquiv : (family P₁ P₂).Oracle ≃ P₁.Oracle × P₂.Oracle := piFinTwoEquiv _
def coinEquiv : (family P₁ P₂).Coin ≃ P₁.Coin × P₂.Coin := piFinTwoEquiv _
def responseEquiv : (family P₁ P₂).Response ≃ P₁.Response × P₂.Response := piFinTwoEquiv _

theorem verify_iff (σ : P₁.Statement × P₂.Statement) (W : (family P₁ P₂).Oracle)
    (coins : P₁.Coin × P₂.Coin) (responses : P₁.Response × P₂.Response) (Q : QuerySet n t) :
    (family P₁ P₂).Verify ((statementEquiv P₁ P₂).symm σ) W
      ((coinEquiv P₁ P₂).symm coins) ((responseEquiv P₁ P₂).symm responses) Q ↔
    P₁.backend.layer.verify σ.1 (oracleEquiv P₁ P₂ W).1 coins.1 responses.1 (P₁.localQuery Q) ∧
    P₂.backend.layer.verify σ.2 (oracleEquiv P₁ P₂ W).2 coins.2 responses.2 (P₂.localQuery Q) := by
  change (∀ i : Fin 2, _) ↔ _
  rw [Fin.forall_fin_two]
  rfl

variable {Key C Public : Type} [Fintype C]
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Native.Circuit P₁.Carrier out₁ input₁}
variable {circuit₂ : Native.Circuit P₂.Carrier out₂ input₂}
variable (S₁ : Linear.Runtime.CompiledSide P₁.Carrier C (Context Key C Public) circuit₁ P₁.backend)
variable (S₂ : Linear.Runtime.CompiledSide P₂.Carrier C (Side.Frontend S₁) circuit₂ P₂.backend)
variable (decodeQuery : C → QuerySet n t)

noncomputable def statements (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂) :
    (family P₁ P₂).Statement :=
  (statementEquiv P₁ P₂).symm
    (S₁.statementAt (firstOracle S₁ S₂ H proof) (selectedOne S₁ S₂ proof),
     S₂.statementAt (secondOracle S₁ S₂ H proof) (selectedTwo S₁ S₂ proof))

def coins (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂) : (family P₁ P₂).Coin :=
  (coinEquiv P₁ P₂).symm
    (S₁.decodeCoin (H (hashInput S₁ S₂ proof (backendStart S₁ S₂))),
     S₂.decodeCoin (H (hashInput S₁ S₂ proof (backendStart S₁ S₂+1))))

def responses (proof : Proof S₁ S₂) : (family P₁ P₂).Response :=
  (responseEquiv P₁ P₂).symm proof.2

def query (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂) : QuerySet n t :=
  decodeQuery (H (hashInput S₁ S₂ proof (backendStart S₁ S₂+2)))

noncomputable def CompiledAccepts {Salt D Enc : Type} [Inhabited D] (ht : 0 < t)
    (scheme : Scheme Salt (family P₁ P₂).Leaf D Enc) (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) (root : D) (claim : OpeningClaim n Salt (family P₁ P₂).Leaf D) : Prop :=
  S₁.precheck (firstFrontend S₁ S₂ proof).1 ∧ S₂.precheck proof.1.1 ∧
    ((family P₁ P₂).compiler ht).Accepts scheme (statements P₁ P₂ S₁ S₂ H proof) root
      (coins P₁ P₂ S₁ S₂ H proof) (responses P₁ P₂ S₁ S₂ proof)
      (query P₁ P₂ S₁ S₂ decodeQuery H proof) claim

theorem accepts_of_verify (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂)
    (W : (family P₁ P₂).Oracle)
    (hqueryOne : ∀ c, S₁.decodeQuery c = P₁.localQuery (decodeQuery c))
    (hqueryTwo : ∀ c, S₂.decodeQuery c = P₂.localQuery (decodeQuery c))
    (hpreOne : S₁.precheck (firstFrontend S₁ S₂ proof).1)
    (hpreTwo : S₂.precheck proof.1.1)
    (hv : (family P₁ P₂).Verify (statements P₁ P₂ S₁ S₂ H proof) W
      (coins P₁ P₂ S₁ S₂ H proof) (responses P₁ P₂ S₁ S₂ proof)
      (query P₁ P₂ S₁ S₂ decodeQuery H proof)) :
    S₁.Accepts (oracleEquiv P₁ P₂ W).1 (firstOracle S₁ S₂ H proof) (selectedOne S₁ S₂ proof) ∧
    S₂.Accepts (oracleEquiv P₁ P₂ W).2 (secondOracle S₁ S₂ H proof) (selectedTwo S₁ S₂ proof) := by
  obtain ⟨hv₁,hv₂⟩ := (verify_iff P₁ P₂ _ W _ _ _).mp hv
  constructor
  · refine ⟨hpreOne,?_⟩
    simpa [Linear.Runtime.CompiledSide.Accepts, firstOracle, firstSlot, Side.steps,
      Linear.Runtime.CompiledSide.points, Linear.Runtime.Replay.points,
      Linear.Runtime.Replay.backend, Linear.Runtime.Replay.opening, hqueryOne, query,
      selectedOne, firstFrontend] using hv₁
  · refine ⟨hpreTwo,?_⟩
    simpa [Linear.Runtime.CompiledSide.Accepts, secondOracle, secondSlot, Side.steps,
      Linear.Runtime.CompiledSide.points, Linear.Runtime.Replay.points,
      Linear.Runtime.Replay.backend, Linear.Runtime.Replay.opening, hqueryTwo, query,
      selectedTwo] using hv₂

theorem accepts_of_extraction {Salt D Enc : Type}
    [DecidableEq D] [Inhabited D] [Inhabited Salt] [Inhabited (family P₁ P₂).Leaf]
    (ht : 0 < t) {codec : Codec Salt (family P₁ P₂).Leaf D Enc} (dec : RoleDecoders codec)
    (scheme : Scheme Salt (family P₁ P₂).Leaf D Enc) (H : Domain S₁ S₂ → C)
    (proof : Proof S₁ S₂) (root : D) (trace : List (Enc × D))
    (claim : OpeningClaim n Salt (family P₁ P₂).Leaf D)
    (e : Extracted n Salt (family P₁ P₂).Leaf D)
    (hext : extract dec n root trace = some e)
    (hagree : ∀ j ∈ claim.I, e.message j = claim.a j)
    (hqueryOne : ∀ c, S₁.decodeQuery c = P₁.localQuery (decodeQuery c))
    (hqueryTwo : ∀ c, S₂.decodeQuery c = P₂.localQuery (decodeQuery c))
    (ha : CompiledAccepts P₁ P₂ S₁ S₂ decodeQuery ht scheme H proof root claim) :
    let W := oracleEquiv P₁ P₂ ((family P₁ P₂).extractedOracle dec root trace)
    S₁.Accepts W.1 (firstOracle S₁ S₂ H proof) (selectedOne S₁ S₂ proof) ∧
    S₂.Accepts W.2 (secondOracle S₁ S₂ H proof) (selectedTwo S₁ S₂ proof) := by
  exact accepts_of_verify P₁ P₂ S₁ S₂ decodeQuery H proof _ hqueryOne hqueryTwo ha.1 ha.2.1
    ((family P₁ P₂).verify_of_extraction ht dec scheme _ root trace _ _ _ claim e hext hagree ha.2.2)

end LfzkV2.Joint.Pair
