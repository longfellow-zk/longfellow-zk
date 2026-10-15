import Bcs.IdealCodec
import LigeroFamily.Protocol.IPCP
import Merkle.ExtractionROM

/-!
# Compiling a public-coin IPCP with a Merkle commitment

The BCS transform, at the granularity `merkle/` and `ligero/` already meet.  A `Compiler` is the
data identifying an IPCP's committed oracle with a family of `n` leaf messages, plus the one
property that makes the compilation sound in the deterministic layer:

* **locality** — what the verifier reads depends only on the leaves the query opens.

For every protocol in the Ligero family locality is a theorem, not an assumption
(`LigeroFamily.openSchemeOracle_congr`); see `Bcs/SchemeCompiler.lean`.

What this file proves is the deterministic half of the reduction: *a compiled acceptance whose
claimed leaves agree with a message family on the opened set is an acceptance of the underlying
IPCP, by the prover that commits the oracle those leaves denote.*  The message family will be
`Merkle.MH.Extracted.message`, and the agreement hypothesis is literally the conclusion of
`mh_extract_explains_of_trace_subset`.  Nothing probabilistic happens here; the counting is the
next layer.

The last section records the shape of a compiled adversary and observes that at **fixed coins** it
is exactly a `Merkle.MH.extractionRun` — a commitment stage followed by an opening stage.  That is
what lets the ROM extraction bound be applied per coin pair while the extractor, which reads the
commitment trace only, stays coin-independent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open LigeroFamily Merkle Merkle.RandomOracle

/-! ## The compilation data -/

/-- The data compiling a public-coin IPCP into a Merkle-committed argument: the committed oracle is
a family of `n` leaf messages, a query opens a nonempty set of them, and the verifier's view
depends on nothing else. -/
structure Compiler (Statement Oracle Challenge Response Query : Type*)
    (Opening : Query → Type*) (M : Type*) (n : ℕ) where
  /-- The oracle protocol being compiled. -/
  protocol : PublicCoinIPCP Statement Oracle Challenge Response Query Opening
  /-- **A commitment is its leaves.**  One leaf per committed position. -/
  columns : Oracle ≃ (Fin n → M)
  /-- The leaves a query opens. -/
  indices : Query → Finset (Fin n)
  /-- A query opens something: the Merkle check rejects an empty set. -/
  indices_nonempty : ∀ query : Query, (indices query).Nonempty
  /-- **Locality.**  Two commitments agreeing on the opened leaves are opened identically, so no
  predicate on the opening can separate them. -/
  open_congr : ∀ (first second : Oracle) (query : Query),
    (∀ i ∈ indices query, columns first i = columns second i) →
    protocol.openOracle first query = protocol.openOracle second query

namespace Compiler

variable {Statement Oracle Challenge Response Query : Type*}
variable {Opening : Query → Type*}
variable {Salt M D Enc : Type*} {n : ℕ}

/-- The commitment a claimed leaf family denotes. -/
def oracleOfClaim (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (a : Fin n → M) : Oracle :=
  K.columns.symm a

@[simp] theorem columns_oracleOfClaim
    (K : Compiler Statement Oracle Challenge Response Query Opening M n) (a : Fin n → M) :
    K.columns (K.oracleOfClaim a) = a :=
  K.columns.apply_symm_apply a

/-- **The compiled verifier.**  It checks the query set it drew was the one opened, that the Merkle
opening reconstructs the claimed root, and then runs the IPCP verifier on the opened leaves. -/
def Accepts [Inhabited D]
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (S : MH.Scheme Salt M D Enc) (statement : Statement) (root : D)
    (challenge : Challenge) (response : Response) (query : Query)
    (claim : MH.OpeningClaim n Salt M D) : Prop :=
  claim.I = K.indices query ∧
    MH.Accepts S n root claim.I claim.a claim.pf ∧
    K.protocol.verify statement challenge response query
      (K.protocol.openOracle (K.oracleOfClaim claim.a) query) = true

/-! ## The deterministic reduction -/

/-- **Locality, at the point of use.**  A commitment agreeing with the claimed leaves on the opened
set is accepted by the IPCP verifier exactly where the compiled verifier accepted. -/
theorem verify_of_accepts [Inhabited D]
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (S : MH.Scheme Salt M D Enc) (statement : Statement) (root : D)
    (challenge : Challenge) (response : Response) (query : Query)
    (claim : MH.OpeningClaim n Salt M D) (oracle : Oracle)
    (hagree : ∀ i ∈ claim.I, K.columns oracle i = claim.a i)
    (hacc : K.Accepts S statement root challenge response query claim) :
    K.protocol.verify statement challenge response query
      (K.protocol.openOracle oracle query) = true := by
  obtain ⟨hI, -, hverify⟩ := hacc
  have hopen : K.protocol.openOracle oracle query =
      K.protocol.openOracle (K.oracleOfClaim claim.a) query := by
    refine K.open_congr oracle (K.oracleOfClaim claim.a) query fun i hi ↦ ?_
    have hi' : i ∈ claim.I := by rw [hI]; exact hi
    rw [columns_oracleOfClaim]
    exact hagree i hi'
  rw [hopen]
  exact hverify

/-- The IPCP prover an extraction produces.  `commit` ignores the statement: the extracted oracle is
a function of the commitment stage alone, which is exactly what an oracle-only extractor
(`Ligero.V3.witness_extractor`) is stated against. -/
def prover (_K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (oracle : Oracle) (response : Challenge → Response) :
    IPCPProver Statement Oracle Challenge Response where
  commit _ := oracle
  respond _ _ challenge := response challenge

@[simp] theorem prover_commit
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (oracle : Oracle) (response : Challenge → Response) (statement : Statement) :
    (K.prover oracle response).commit statement = oracle := rfl

@[simp] theorem accepts_prover
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (oracle : Oracle) (response : Challenge → Response) (statement : Statement)
    (challenge : Challenge) (query : Query) :
    K.protocol.accepts (K.prover oracle response) statement (challenge, query) =
      K.protocol.verify statement challenge (response challenge) query
        (K.protocol.openOracle oracle query) := rfl

/-- **The compilation bridge.**  This is the deterministic content of the BCS step, and the shape
the ROM counting consumes: `messages` will be `Merkle.MH.Extracted.message` and `hagree` is
verbatim the conclusion of `mh_extract_explains_of_trace_subset`. -/
theorem protocol_accepts_of_accepts [Inhabited D]
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (S : MH.Scheme Salt M D Enc) (statement : Statement) (root : D)
    (challenge : Challenge) (query : Query) (claim : MH.OpeningClaim n Salt M D)
    (messages : Fin n → M) (response : Challenge → Response)
    (hagree : ∀ i ∈ claim.I, messages i = claim.a i)
    (hacc : K.Accepts S statement root challenge (response challenge) query claim) :
    K.protocol.accepts (K.prover (K.oracleOfClaim messages) response) statement
      (challenge, query) = true := by
  rw [accepts_prover]
  refine verify_of_accepts K S statement root challenge (response challenge) query claim _
    ?_ hacc
  intro i hi
  rw [columns_oracleOfClaim]
  exact hagree i hi

end Compiler

/-! ## Compiled adversaries

The scheduling is the IPCP's own: the response is fixed before the query is drawn, so `reveal` is
the only stage that sees it.  Query budgets are syntactic — a stage *is* a `Tree` with a fuel
index — so no stage carries an assumed bound. -/

/-- A compiled-argument adversary: three random-oracle stages, each resumed from the previous
stage's private state. -/
structure Adversary (Enc D Salt M Challenge Response Query : Type*) (Aux Aux' : Type*)
    (n commitFuel respondFuel revealFuel : ℕ) where
  /-- Commit: outputs a root and private state. -/
  commit : Tree Enc D (D × Aux) commitFuel
  /-- Answer the challenge, before any query is drawn. -/
  respond : Challenge → Aux → Tree Enc D (Response × Aux') respondFuel
  /-- Open the queried leaves. -/
  reveal : Query → Aux' → Tree Enc D (MH.OpeningClaim n Salt M D) revealFuel

namespace Adversary

variable {Enc D Salt M Challenge Response Query Aux Aux' : Type*}
variable {n commitFuel respondFuel revealFuel : ℕ}

/-- At fixed coins the last two stages are a single opening stage. -/
def openingStage
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challenge : Challenge) (query : Query) (aux : Aux) :
    Tree Enc D (MH.OpeningClaim n Salt M D) (revealFuel + respondFuel) :=
  (A.respond challenge aux).bind fun ra ↦ A.reveal query ra.2

/-- **A compiled adversary at fixed coins is a Merkle extraction experiment.**  The commitment stage
is untouched by the coins, which is why the extractor — which reads its trace and nothing else —
is coin-independent.  That is the hypothesis `Merkle.MH.mh_extract_rom_card_le` is stated under and
the hypothesis `Ligero.V3.witness_extractor` is stated under, and it is why they compose. -/
def run [Inhabited D] [DecidableEq Enc]
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (C : MH.Codec Salt M D Enc) (challenge : Challenge) (query : Query) :
    Tree Enc D (D × MH.OpeningClaim n Salt M D)
      (2 * n + (revealFuel + respondFuel) + commitFuel) :=
  MH.extractionRun C n commitFuel (revealFuel + respondFuel) A.commit
    (A.openingStage challenge query)

end Adversary

end Bcs
