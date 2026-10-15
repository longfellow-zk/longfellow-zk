import Bcs.Transcript
import Bcs.Reduction

/-!
# The compiled experiment, and the extractor it induces

One tape, one lazy execution, external coins.  `CompiledAccepts` is the compiled verifier's decision
on that execution, written entirely in projections that `Bcs/Transcript.lean` has shown depend on
nothing drawn later than they are: the root and trace on the tape alone, the response on the tape
and the challenge.

`extractedOracle` is `Merkle`'s extractor composed with `Compiler.oracleOfClaim`.  It reads the
commitment trace and the root, so it is a function of the tape — no challenge, no query, no
statement.  That is exactly the interface an oracle-only IOP extractor
(`Ligero.V3.witness_extractor`) is stated against, and `protocol_accepts_of_compiled` is the
statement the counting layer applies it through.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open LigeroFamily Merkle Merkle.MH Merkle.RandomOracle

variable {Statement Oracle Challenge Response Query : Type*}
variable {Opening : Query → Type*}
variable {Enc D Salt M Aux Aux' : Type*}
variable {n commitFuel respondFuel revealFuel T : ℕ}

/-! ## The compiled experiment -/

/-- **The compiled verifier's decision**, on one answer tape and one coin pair.  Every argument is a
projection of the single lazy execution `Adversary.run`. -/
def CompiledAccepts [Inhabited D] [DecidableEq Enc]
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (C : Codec Salt M D Enc) (statement : Statement)
    (challenge : Challenge) (query : Query) (answers : Fin T → D) : Prop :=
  K.Accepts
    (C.withOracle (extractionOracle C n commitFuel (revealFuel + respondFuel) T A.commit
      (A.openingStage challenge query) answers))
    statement (A.rootOf answers) challenge (A.responseOf challenge answers) query
    (openingClaim C n commitFuel (revealFuel + respondFuel) T A.commit
      (A.openingStage challenge query) answers)

/-! ## The extractor -/

/-- The leaves `Merkle`'s extractor recovers from the commitment trace, defaulted where it fails. -/
noncomputable def extractedMessages [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] [Inhabited M] {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel) (answers : Fin T → D) : Fin n → M :=
  ((extract dec n (A.rootOf answers) (A.traceOf answers)).map Extracted.message).getD default

/-- **The extracted commitment.**  A function of the answer tape and nothing else. -/
noncomputable def extractedOracle [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] [Inhabited M] {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel) (answers : Fin T → D) : Oracle :=
  K.oracleOfClaim (extractedMessages dec A answers)

theorem extractedMessages_eq [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] [Inhabited M] {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel) (answers : Fin T → D)
    (out : Extracted n Salt M D)
    (hout : extract dec n (A.rootOf answers) (A.traceOf answers) = some out) :
    extractedMessages dec A answers = out.message := by
  rw [extractedMessages, hout]
  rfl

/-! ## The reduction, in the shape the counting uses -/

/-- **From a compiled acceptance to an IPCP acceptance.**  On a tape where the commitment-stage
extraction explains the opening, the compiled verifier's acceptance at coins `(challenge, query)` is
an acceptance of the underlying IPCP by the prover that commits `extractedOracle` — which the coins
do not touch.

`ExtractionExplains` is `Merkle`'s own conclusion, so nothing here re-derives it; the counting layer
supplies the tapes where it holds. -/
theorem protocol_accepts_of_compiled [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] [Inhabited M] {C : Codec Salt M D Enc} (dec : RoleDecoders C)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (statement : Statement) (challenge : Challenge) (query : Query) (answers : Fin T → D)
    (hexplains : ExtractionExplains C dec n commitFuel (revealFuel + respondFuel) T A.commit
      (A.openingStage challenge query) answers)
    (hacc : CompiledAccepts K A C statement challenge query answers) :
    K.protocol.accepts
        (K.prover (extractedOracle dec K A answers) fun c ↦ A.responseOf c answers)
        statement (challenge, query) = true := by
  obtain ⟨out, hextract, hmessages, -⟩ := hexplains
  rw [A.commitRoot_eq C challenge query answers,
    A.commitTrace_eq' C challenge query answers] at hextract
  have hmsg : extractedMessages dec A answers = out.message :=
    extractedMessages_eq dec A answers out hextract
  rw [extractedOracle, hmsg]
  exact K.protocol_accepts_of_accepts _ statement (A.rootOf answers) challenge query _
    out.message (fun c ↦ A.responseOf c answers) hmessages hacc

end Bcs
