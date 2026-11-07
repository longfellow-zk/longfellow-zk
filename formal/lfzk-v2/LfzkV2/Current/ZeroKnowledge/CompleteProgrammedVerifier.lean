import LfzkV2.Current.ZeroKnowledge.CompleteProgrammed

/-! The explicit zero-cell simulator is accepted by the actual runtime
verifier after replacing one whole opening answer and computing the final
seal normally. The remaining frontend premise is an exact successful parse
at the base oracle's batching prefix, not a verifier-acceptance premise. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteProgrammedVerifier
open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

variable {g : Geometry} {fields : Fields} {Advice Base Key C Enc Request : Type}
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Fin 2443 × Digest))
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Data" => Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
variable (earlier : Request → Replay.Encoding g fields Advice (OpeningBody.Authentication g) Key
  (Base × ProtocolWrites.Fresh g fields Advice) C)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg)
variable (codec : Codec (Fin 2443 × Digest) (RuntimeVerifier.Family binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg).Leaf Digest Enc)
variable [Inhabited (RuntimeVerifier.Family binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg).Leaf]

omit [Inhabited (RuntimeVerifier.Family binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg).Leaf] in
private theorem parse_congr (p q : Point) (a : Fin p.rank → C) (b : Fin q.rank → C)
    (samePoint : p = q) (sameAnswers : HEq a b) :
    RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic p a =
      RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic q b := by
  subst q
  cases sameAnswers
  rfl

theorem accepts
    (request : Request)
    (e : OracleProgramming.BodyEncoding (g := g) (fields := fields) (Advice := Advice)
      (Authentication := OpeningBody.Authentication g) (Context := Key)
      (Block := Base × ProtocolWrites.Fresh g fields Advice) (C := C))
    (encoded : RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier request = e.encoding)
    (HM : Enc → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (data : Data) (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body) (context : Digest) (H : Point → Digest × C) (answer : Digest × C)
    (chosen : cfg.sample answer.2 = indices)
    (parsed :
      let body := CompleteVerifier.simulatedBody binary prime binaryNodes primeNodes cfg codec
        HM indices nonces tape data.2.statement coin frontend context
      let parent := BackendPath.parent e.encoding cfg.initialLink ⟨body,fun _ => 0⟩ H g.batchingIndex
      RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
        parent.point (parent.point.priorAnswers H) = some data)
    (coinMatches :
      let body := CompleteVerifier.simulatedBody binary prime binaryNodes primeNodes cfg codec
        HM indices nonces tape data.2.statement coin frontend context
      let parent := BackendPath.parent e.encoding cfg.initialLink ⟨body,fun _ => 0⟩ H g.batchingIndex
      RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2 = coin)
    (rootBound :
      let body := CompleteVerifier.simulatedBody binary prime binaryNodes primeNodes cfg codec
        HM indices nonces tape data.2.statement coin frontend context
      cfg.root (e.context body) = body.commitment)
    (contextBound :
      let body := CompleteVerifier.simulatedBody binary prime binaryNodes primeNodes cfg codec
        HM indices nonces tape data.2.statement coin frontend context
      context = cfg.authenticationContext (e.context body))
    (saltBound :
      let body := CompleteVerifier.simulatedBody binary prime binaryNodes primeNodes cfg codec
        HM indices nonces tape data.2.statement coin frontend context
      cfg.bindSalt (e.context body) = fun i nonce => (i,nonce)) :
    let body := CompleteVerifier.simulatedBody binary prime binaryNodes primeNodes cfg codec
      HM indices nonces tape data.2.statement coin frontend context
    let result := OracleProgramming.programAndFinalize e cfg.initialLink body H g.openingIndex answer
    RuntimeAdaptiveVerifier.verify binary prime P R cfg earlier hashPublic decodePublic draw codec HM
      ⟨request,result.1⟩ result.2 = true := by
  let body := CompleteVerifier.simulatedBody binary prime binaryNodes primeNodes cfg codec
    HM indices nonces tape data.2.statement coin frontend context
  let result := OracleProgramming.programAndFinalize e cfg.initialLink body H g.openingIndex answer
  let output : RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice)
      (Request := Request) := ⟨request,result.1⟩
  have before : g.batchingIndex.val < g.openingIndex.val := by rw [g.openingIndex_val]; omega
  have hp := CompleteProgrammed.parent_point e cfg.initialLink body H answer g.batchingIndex before
  have ha := CompleteProgrammed.prior_answers e cfg.initialLink body H answer g.batchingIndex before
  have hc := CompleteProgrammed.parent_answer e cfg.initialLink body H answer g.batchingIndex before
  apply CompleteVerifier.acceptance_of_encoded_simulation binary prime binaryNodes primeNodes cfg earlier
    hashPublic decodePublic draw codec output result.2 HM indices nonces tape data
  · dsimp only
    change RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
      (BackendPath.parent (RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier request)
        cfg.initialLink result.1 result.2 g.batchingIndex).point
      ((BackendPath.parent (RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier request)
        cfg.initialLink result.1 result.2 g.batchingIndex).point.priorAnswers result.2) = some data
    rw [encoded]
    exact (parse_congr binary prime binaryNodes primeNodes cfg hashPublic decodePublic
      _ _ _ _ hp (heq_of_eq ha)).trans parsed
  · dsimp only
    change cfg.sample (result.2 (((RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier request).chain
      cfg.initialLink).point result.1 result.2 g.openingIndex.val)).2 = indices
    rw [encoded,OracleProgramming.programAndFinalize_answer]
    exact chosen
  · dsimp only
    change RuntimeVerifier.responses binary prime P R cfg result.1 =
      CompleteBackend.responses binaryNodes primeNodes binary.cells
        (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime
        (OrderedOpening.query indices) data.2.statement
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw
          (result.2 (BackendPath.parent (RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier request)
            cfg.initialLink result.1 result.2 g.batchingIndex).point).2) tape
    rw [encoded,hc,coinMatches]
    exact CompleteVerifier.simulatedBody_responses binary prime binaryNodes primeNodes cfg codec HM
      indices nonces tape data.2.statement coin frontend context result.1.finalSeal
  · exact CompleteVerifier.simulatedBody_raw binary prime binaryNodes primeNodes cfg codec HM
      indices nonces tape data.2.statement coin frontend context result.1.finalSeal
  · rfl
  · dsimp only
    change cfg.root ((RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier request).context result.1) = _
    rw [encoded]
    exact rootBound
  · dsimp only
    change context = cfg.authenticationContext
      ((RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier request).context result.1)
    rw [encoded]
    exact contextBound
  · dsimp only
    change cfg.bindSalt ((RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier request).context result.1) = _
    rw [encoded]
    exact saltBound
  · rw [RuntimeAdaptiveVerifier.finalSealPoint_eq]
    change (result.2 (((RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier request).chain
      cfg.initialLink).finalSealPoint result.1 result.2)).1 = result.1.finalSeal
    rw [encoded]
    exact OracleProgramming.programAndFinalize_seal e cfg.initialLink body H g.openingIndex answer

end LfzkV2.Current.ZeroKnowledge.CompleteProgrammedVerifier
