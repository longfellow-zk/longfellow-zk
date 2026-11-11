import LfzkV2.Current.StrandRoleSampling
import LfzkV2.Current.IdealRuntime
import LfzkV2.Current.RuntimeAdaptiveCharges

/-! Local algebraic tests only observe the samples prescribed by the public
frontend schedule. Equality of those samples preserves the reconstructed
messages and every failure predicate; unused ideal answer factors do not
become additional physical reads. -/
noncomputable section
namespace LfzkV2.Current.StrandLocalCharges
open SumcheckV2 Linear.Challenges FrontendReplay
open Layered.Replay (LayerRole)

section Samples
variable {F Pad C : Type} [Field F]
variable (decode : C → ℕ → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)

/-- The largest ordinary coordinate used by one retained algebraic test.
An entry may share its block with a layer, or follow a combine coefficient. -/
def usedWidth : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    LayerRole circuit → ℕ → ℕ
  | _,_,.input,role,_ => Fin.elim0 role
  | _,_,.entry count _ rest,role,offset =>
      match role with
      | .inl _ => offset+count
      | .inr role => usedWidth rest role (offset+count)
  | _,_,.layer count _ rest,role,offset =>
      match role with
      | .inl _ => offset+count
      | .inr (.inl _) => 1
      | .inr (.inr (.inl _)) => 0
      | .inr (.inr (.inr (.inl _))) => 1
      | .inr (.inr (.inr (.inr role))) => usedWidth rest role (if hasLayers rest then 0 else 1)

theorem sampleAtRole_eq_of_block {out input : ℕ} (circuit : Layered.Circuit F out input)
    (role : LayerRole circuit) (first second : ℕ → C) (start offset : ℕ)
    (same : ∀ i < usedWidth circuit role offset,
      decode (first (queryIndex circuit role start)) i = decode (second (queryIndex circuit role start)) i)
    (sameNonzero : LayerRole.kind circuit role = .terminal →
      nonzero (first (queryIndex circuit role start)) = nonzero (second (queryIndex circuit role start))) :
    sampleAtRole decode nonzero circuit role first start offset =
      sampleAtRole decode nonzero circuit role second start offset := by
  induction circuit generalizing start offset with
  | input => exact Fin.elim0 role
  | entry count entry rest ih =>
      cases role with
      | inl index =>
          funext i
          exact same _ (by change offset+i.val < offset+count; have h : i.val < count := i.isLt; omega)
      | inr role => exact ih role start (offset+count) same sameNonzero
  | @layer out mid input assertions body rest ih =>
      rcases role with i | i | i | i | role
      · funext j
        exact same _ (by change offset+j.val < offset+assertions; have h : j.val < assertions := j.isLt; omega)
      · funext _
        exact same 0 (by change 0 < 1; decide)
      · exact sameNonzero rfl
      · funext _
        exact same 0 (by change 0 < 1; decide)
      · exact ih role _ _ same sameNonzero

omit [Field F] in
private theorem no_layers_coordinates {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (side : Side) (first : ℕ)
    (none : hasLayers circuit = false) (role : LayerRole circuit) :
    FrontendSchedule.coordinates (plan.locatedRole side first role) =
      (plan.frontend.inputEntries.map Entry.outputs).sum := by
  cases plan with
  | input => exact Fin.elim0 role
  | inputEntry metadata entry =>
      cases role with
      | inl _ => rfl
      | inr role => exact Fin.elim0 role
  | layer | entryLayer => simp only [hasLayers,Bool.true_eq_false] at none

omit [Field F] in
private theorem layer_width_bound {out mid input assertions : ℕ}
    {body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F}
    {rest : Layered.Circuit F mid input} (tail : FrontendSchedule.Plan F rest)
    (metadata : FrontendSchedule.LayerMetadata body) (entering : List Entry)
    (side : Side) (first offset : ℕ)
    (ih : ∀ nextOffset role, usedWidth rest role nextOffset ≤
      FrontendSchedule.coordinates (tail.locatedRole side (first+1) role)+nextOffset)
    (role : LayerRole (.layer assertions body rest)) :
    usedWidth (.layer assertions body rest) role (offset+(entering.map Entry.outputs).sum) ≤
      FrontendSchedule.coordinates (FrontendSchedule.layerLocated side first entering metadata.fragments
        tail.frontend.inputEntries (tail.locatedRole side (first+1)) role)+offset := by
  rcases role with i | i | i | i | role
  · simp only [usedWidth,FrontendSchedule.layerLocated,FrontendSchedule.coordinates,metadata.count]
    omega
  · simp only [usedWidth,FrontendSchedule.layerLocated,FrontendSchedule.coordinates]
    omega
  · exact Nat.zero_le _
  · dsimp only [usedWidth,FrontendSchedule.layerLocated]
    split_ifs <;> simp only [FrontendSchedule.coordinates] <;> omega
  · dsimp only [usedWidth,FrontendSchedule.layerLocated]
    split_ifs with layers
    · exact (ih 0 role).trans (by omega)
    · have none := Bool.eq_false_iff.mpr layers
      have bound := ih 1 role
      rw [no_layers_coordinates tail side (first+1) none role] at bound
      simpa only [FrontendSchedule.coordinates] using bound.trans (by omega)

omit [Field F] in
/-- The public schedule's width covers every actual coordinate read. This
is proved from its circuit annotation, including entry/layer and final
combine/input sharing; it is not a supplied sampler correspondence premise. -/
theorem usedWidth_le {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (side : Side) (first offset : ℕ)
    (role : LayerRole circuit) : usedWidth circuit role offset ≤
      FrontendSchedule.coordinates (plan.locatedRole side first role)+offset := by
  induction plan generalizing first offset with
  | input => exact Fin.elim0 role
  | inputEntry metadata entry =>
      cases role with
      | inl _ => simp only [usedWidth,FrontendSchedule.Plan.locatedRole,FrontendSchedule.coordinates,metadata.count]; omega
      | inr role => exact Fin.elim0 role
  | layer metadata tail ih =>
      simpa only [FrontendSchedule.Plan.locatedRole,List.map_nil,List.sum_nil,Nat.add_zero] using
        layer_width_bound tail metadata [] side first offset (ih (first+1)) role
  | entryLayer entries entry metadata tail ih =>
      cases role with
      | inl _ =>
          simp only [usedWidth,FrontendSchedule.Plan.locatedRole,FrontendSchedule.coordinates,entries.count,metadata.count]
          omega
      | inr role =>
          simpa only [usedWidth,FrontendSchedule.Plan.locatedRole,entries.count] using
            layer_width_bound tail metadata entries.entries side first offset (ih (first+1)) role

omit [Field F] in
private theorem vector_sample {count : ℕ} {first second : Fin count → F}
    (samples : ∀ _ : Fin (LfzkV2.Replay.vectorSlots count), first = second) : first = second := by
  by_cases positive : count = 0
  · subst count
    funext i
    exact Fin.elim0 i
  · exact samples ⟨0,by simp [LfzkV2.Replay.vectorSlots,positive]⟩

/-- The decoder's entire answer type is irrelevant to reconstruction once
the actual per-role samples have been fixed. -/
theorem readFrom_eq_of_samples {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (first second : ℕ → C) (start offset : ℕ)
    (same : ∀ role, sampleAtRole decode nonzero circuit role first start offset =
      sampleAtRole decode nonzero circuit role second start offset) :
    readFrom decode nonzero circuit plan payload first start offset =
      readFrom decode nonzero circuit plan payload second start offset := by
  induction circuit generalizing start offset with
  | input => rfl
  | entry count entry rest ih =>
      have coefficients : (fun i : Fin count => decode (first start) (offset+i.val)) =
          fun i => decode (second start) (offset+i.val) :=
        vector_sample (fun index => same (.inl index))
      have tail := ih plan payload start (offset+count) (fun role => same (.inr role))
      exact Prod.ext coefficients tail
  | @layer out mid input assertions body rest ih =>
      have beta : (fun i : Fin assertions => decode (first start) (offset+i.val)) =
          fun i => decode (second start) (offset+i.val) :=
        vector_sample (fun index => same (.inl index))
      have point : (fun i : Fin mid => decode (first (start+1+i.val)) 0) =
          fun i => decode (second (start+1+i.val)) 0 := by
        funext i
        exact congrFun (same (.inr (.inl i))) 0
      have scale := same (.inr (.inr (.inl 0)))
      have alpha := congrFun (same (.inr (.inr (.inr (.inl 0))))) 0
      have tail := ih plan.2 payload.2
        (if hasLayers rest then start+mid+3 else start+mid+2)
        (if hasLayers rest then 0 else 1)
        (fun role => same (.inr (.inr (.inr (.inr role)))))
      change nonzero (first (start+1+mid)) = nonzero (second (start+1+mid)) at scale
      change decode (first (start+mid+2)) 0 = decode (second (start+mid+2)) 0 at alpha
      simp only [readFrom,beta,point,scale,alpha,tail]

/-- All retained data are functions of the reconstructed messages. This
includes the assertion coefficients shared with the entering-output block. -/
theorem dataAtRole_eq_of_read {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (first second : ℕ → C) (start offset : ℕ)
    (same : readFrom decode nonzero circuit plan payload first start offset =
      readFrom decode nonzero circuit plan payload second start offset)
    (w : Cube input → F) (weights : Cube out → F) (pads : Pad → F) (claim : F)
    (role : LayerRole circuit) :
    dataAtRole decode nonzero circuit plan payload first start offset w weights pads claim role =
      dataAtRole decode nonzero circuit plan payload second start offset w weights pads claim role := by
  induction circuit generalizing start offset claim with
  | input => exact Fin.elim0 role
  | entry count entry rest ih =>
      have head := congrArg Prod.fst same
      have tail := congrArg Prod.snd same
      cases role with
      | inl _ => rfl
      | inr role =>
          dsimp only [dataAtRole]
          change (fun i : Fin count => decode (first start) (offset+i.val)) =
            (fun i => decode (second start) (offset+i.val)) at head
          rw [head]
          exact ih plan payload start (offset+count) tail w _ claim role
  | @layer out mid input assertions body rest ih =>
      have head := congrArg Prod.fst same
      have tail := congrArg Prod.snd same
      rcases role with i | i | i | i | role
      · rfl
      · dsimp only [dataAtRole]; rw [head]
      · dsimp only [dataAtRole]; rw [head]
      · dsimp only [dataAtRole]; rw [head]
      · dsimp only [dataAtRole]
        rw [head]
        exact ih plan.2 payload.2 _ _ tail w _ _ role

theorem badAt_eq_of_samples {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (first second : ℕ → C) (w : Cube input → F) (pads : Pad → F) (query : ℕ)
    (same : ∀ role, sampleAtRole decode nonzero circuit role first 0 0 =
      sampleAtRole decode nonzero circuit role second 0 0) :
    BadAt decode nonzero circuit plan payload first w pads query ↔
      BadAt decode nonzero circuit plan payload second w pads query := by
  have messages := readFrom_eq_of_samples decode nonzero circuit plan payload first second 0 0 same
  unfold BadAt
  apply exists_congr
  intro role
  rw [dataAtRole_eq_of_read decode nonzero circuit plan payload first second 0 0 messages,
    same role]

/-- Resetting unused current-answer coordinates preserves all frontend
samples. The past is fixed and future slots use the same fallback; no causal
order of raw oracle queries is assumed. -/
theorem current_samples {roles : List Role} {Key Block Link Body : Type}
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (shape : FrontendSchedule.Plan F circuit) (side : Side)
    (point : Input roles Key Block Link Body) (H : Input roles Key Block Link Body → Link × C)
    (start : ℕ) (left right fallback : C)
    (located : ∀ role, start+queryIndex circuit role 0 = point.rank →
      point.role = some (shape.locatedRole side 0 role))
    (ordinary : ∀ physical, point.role = some physical →
      ∀ i < FrontendSchedule.coordinates physical, decode left i = decode right i)
    (terminal : ∀ physical, point.role = some physical → physical.domain = .terminal →
      nonzero left = nonzero right) :
    ∀ role, sampleAtRole decode nonzero circuit role
        (fun j => point.answersWith H left fallback (start+j)) 0 0 =
      sampleAtRole decode nonzero circuit role
        (fun j => point.answersWith H right fallback (start+j)) 0 0 := by
  intro role
  apply sampleAtRole_eq_of_block decode nonzero circuit role
  · intro i bound
    by_cases current : start+queryIndex circuit role 0 = point.rank
    · have width := usedWidth_le shape side 0 0 role
      have same := ordinary _ (located role current) i (by omega)
      simpa only [Input.answersWith,completeAnswers,current,lt_self_iff_false,
        ↓reduceDIte,↓reduceIte] using same
    · simp only [Input.answersWith,completeAnswers,current,↓reduceIte]
  · intro kind
    by_cases current : start+queryIndex circuit role 0 = point.rank
    · have domain := shape.locatedRole_domain side 0 role
      rw [kind] at domain
      have same := terminal _ (located role current) domain
      simpa only [Input.answersWith,completeAnswers,current,lt_self_iff_false,
        ↓reduceDIte,↓reduceIte] using same
    · simp only [Input.answersWith,completeAnswers,current,↓reduceIte]

omit [Field F] in
private theorem prime_located {g : Geometry} {fields : Fields} {Advice Base Key : Type}
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (shape : FrontendSchedule.Plan F circuit) (geometry : shape.frontend = g.prime)
    (point : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))
    (role : LayerRole circuit) (current : g.primeStart+queryIndex circuit role 0 = point.rank) :
    point.role = some (shape.locatedRole .prime 0 role) := by
  let index : Fin (g.prime.roles .prime).length := ⟨queryIndex circuit role 0,by
    rw [← geometry]; exact (shape.roleIndex .prime role).isLt⟩
  have indexValue : index.val = queryIndex circuit role 0 := rfl
  have roleGet : (g.prime.roles .prime).get index = shape.locatedRole .prime 0 role := by
    have got := shape.frontend_role_get_queryIndex .prime role
    rw [geometry] at got
    exact Option.some.inj ((List.getElem?_eq_getElem index.isLt).symm.trans got)
  cases point with
  | round i history block =>
      have same : i = g.primeIndex index := by
        apply Fin.ext
        change i.val = g.primeStart+index.val
        simpa only [Input.rank,indexValue] using current.symm
      subst i
      simp only [Input.role,g.prime_role_get,roleGet]
  | finalSeal history body =>
      have bound := (g.primeIndex index).isLt
      change g.primeStart+index.val < g.roles.length at bound
      simp only [Input.rank] at current
      omega

omit [Field F] in
private theorem binary_located {g : Geometry} {fields : Fields} {Advice Base Key : Type}
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (shape : FrontendSchedule.Plan F circuit) (geometry : shape.frontend = g.binary)
    (point : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))
    (role : LayerRole circuit) (current : g.binaryStart+queryIndex circuit role 0 = point.rank) :
    point.role = some (shape.locatedRole .binary 0 role) := by
  let index : Fin (g.binary.roles .binary).length := ⟨queryIndex circuit role 0,by
    rw [← geometry]; exact (shape.roleIndex .binary role).isLt⟩
  have indexValue : index.val = queryIndex circuit role 0 := rfl
  have roleGet : (g.binary.roles .binary).get index = shape.locatedRole .binary 0 role := by
    have got := shape.frontend_role_get_queryIndex .binary role
    rw [geometry] at got
    exact Option.some.inj ((List.getElem?_eq_getElem index.isLt).symm.trans got)
  cases point with
  | round i history block =>
      have same : i = g.binaryIndex index := by
        apply Fin.ext
        change i.val = g.binaryStart+index.val
        simpa only [Input.rank,indexValue] using current.symm
      subst i
      simp only [Input.role,g.binary_role_get,roleGet]
  | finalSeal history body =>
      have bound := (g.binaryIndex index).isLt
      change g.binaryStart+index.val < g.roles.length at bound
      simp only [Input.rank] at current
      omega

end Samples

section FrontendData
open ApplicationCharging ApplicationOracle
variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN F Pad : Type}
variable [Field B] [Field N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN] [Field F]

private theorem frontend_data_answer
    (S : SelectionSource roles Key Block Link Body C Oracle B N IB IN)
    (data : FrontendData F Pad (Selection.Pair B N IB IN) (Input roles Key Block Link Body) C)
    (shape : FrontendSchedule.Plan F data.circuit) (side : Side)
    (point : Input roles Key Block Link Body) (H : Input roles Key Block Link Body → Link × C)
    (left right : C)
    (located : ∀ role, data.start+queryIndex data.circuit role 0 = point.rank →
      point.role = some (shape.locatedRole side 0 role))
    (ordinary : ∀ physical, point.role = some physical →
      ∀ i < FrontendSchedule.coordinates physical, data.decode left i = data.decode right i)
    (terminal : ∀ physical, point.role = some physical → physical.domain = .terminal →
      data.nonzero left = data.nonzero right) :
    data.bad S point H left ↔ data.bad S point H right := by
  unfold FrontendData.bad SelectedFrontendOracle.bad
  apply and_congr_right
  intro _
  apply exists_congr
  intro witness
  apply and_congr_right
  intro _
  exact badAt_eq_of_samples data.decode data.nonzero data.circuit data.plan (data.payload point)
    _ _ _ _ _ (current_samples data.decode data.nonzero shape side point H data.start
      left right data.fallback located ordinary terminal)

end FrontendData

private theorem decoder_cast_eq {F C : Type} [Fintype F] [Fintype C]
    {a b : ℕ} (sameSize : a = b) (decoder : BalancedDecoder C (Fin a → F))
    (left right : C) (same : decoder.decode left = decoder.decode right) :
    (sameSize ▸ decoder : BalancedDecoder C (Fin b → F)).decode left =
      (sameSize ▸ decoder : BalancedDecoder C (Fin b → F)).decode right := by
  cases sameSize
  exact same

section Runtime
open Application ApplicationSetup ApplicationOracle RuntimeAdaptiveCharges
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key B Salt Oracle : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (countBinary countPrime binaryCapacity primeCapacity : ℕ)
local notation "RawB" => IdealRuntime.RawBinary P countBinary
local notation "RawN" => IdealRuntime.RawPrime R countPrime
local notation "Answer" => IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity
local instance answerFintype : Fintype Answer := by
  dsimp only [IdealRuntime.Answer,IdealSamples.Answer]
  infer_instance
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)
local notation "Pair" => Selection.Pair B N binary.Original prime.Original
local notation "factor" => StrandRoleSampling.factor B N binary.Original prime.Original RawB RawN (Fin t ↪ Fin n) binaryCapacity primeCapacity
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
  (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) (Salt := Salt))
variable (S : RuntimeCover.Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  binary prime (Oracle := Oracle))
variable (laws : RuntimeCover.SamplerLaws binary prime P R
  (IdealRuntime.challengePublic (g := g) (fields := fields) (Advice := Advice)
    (Base := Base) (Key := Key) (Salt := Salt)
    binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg) S)
variable (readers : Readers (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  binary prime)
local notation "publicCfg" => IdealRuntime.challengePublic (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (Salt := Salt)
  binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg

private theorem fingerprint_charge_normalize
    (coins : ∀ a : Answer, S.coins a = a .fingerprints)
    (fallback answer : Answer) (point : Point) (H : Point → Digest × Answer) (link : Digest) :
    roleCharge S laws readers .fingerprint point H
      (link,StrandSampling.normalize (factor .fingerprints trivial) fallback answer) =
      roleCharge S laws readers .fingerprint point H (link,answer) := by
  have sample : S.coins (StrandSampling.normalize (factor .fingerprints trivial) fallback answer) =
      S.coins answer := by
    rw [coins,coins]
    exact StrandRoleSampling.normalize_component B N binary.Original prime.Original RawB RawN (Fin t ↪ Fin n)
      binaryCapacity primeCapacity .fingerprints fallback answer
  simp only [roleCharge,SelectionSource.binarySelection,SelectionSource.primeSelection,sample]

private theorem prime_frontend_normalize
    (hashPublic : Key → Option (Fin binary.nPublic → Bool))
    (decodePublic : Base → Option (Fin prime.nPublic → N))
    (shape : FrontendSchedule.Plan N prime.circuit) (geometry : shape.frontend = g.prime)
    (capacity : shape.capacity ≤ laws.primeCapacity)
    (physical : Role) (point : Point) (current : point.role = some physical)
    (side : frontendSide physical = some .prime)
    (fits : StrandRoleSampling.Fits binaryCapacity primeCapacity
      (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) physical))
    (fallback answer : Answer) (H : Point → Digest × Answer) (link : Digest) :
    ApplicationViews.frontendCharge S
      (RuntimeAdaptiveViews.readPrimeView binary prime P R publicCfg S laws hashPublic decodePublic shape capacity)
      point H (link,StrandSampling.normalize
        (factor (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) physical) fits) fallback answer) =
    ApplicationViews.frontendCharge S
      (RuntimeAdaptiveViews.readPrimeView binary prime P R publicCfg S laws hashPublic decodePublic shape capacity)
      point H (link,answer) := by
  unfold ApplicationViews.frontendCharge
  congr 1
  apply propext
  unfold ApplicationViews.frontendBad RuntimeAdaptiveViews.readPrimeView
  cases hp : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic point with
  | none => rfl
  | some values =>
      dsimp only [Bind.bind,Option.bind]
      unfold ApplicationViews.readPrimeView
      split_ifs with starts
      · cases payload : ApplicationViews.PartialMessages.read (RuntimeAdaptive.primeWithInputs prime values.2).circuit
          (ApplicationPrefix.wire point Side.prime (publicCfg).primeField g.primeStart)
          (point.rank-g.primeStart) with
        | none => rfl
        | some payload =>
            dsimp only [Option.map,ApplicationViews.FrontendView.bad]
            apply frontend_data_answer S _ shape .prime point H
            · exact prime_located shape geometry point
            · intro actual same i bound
              have eq := Option.some.inj (same.symm.trans current)
              subst actual
              exact StrandRoleSampling.normalize_prime_role_read B N binary.Original prime.Original RawB RawN
                (Fin t ↪ Fin n) binaryCapacity primeCapacity binary.degree (prime.circuit.layers+1)
                physical fits side fallback answer i bound
            · intro actual same domain
              have eq := Option.some.inj (same.symm.trans current)
              subst actual
              exact StrandRoleSampling.normalize_prime_role_nonzero B N binary.Original prime.Original RawB RawN
                (Fin t ↪ Fin n) binaryCapacity primeCapacity binary.degree (prime.circuit.layers+1)
                physical fits side domain fallback answer
      · rfl

private theorem binary_frontend_normalize
    (hashPublic : Key → Option (Fin binary.nPublic → Bool))
    (decodePublic : Base → Option (Fin prime.nPublic → N))
    (template : FrontendSchedule.Plan B binary.template) (geometry : template.frontend = g.binary)
    (capacity : template.capacity ≤ laws.binaryCapacity)
    (physical : Role) (point : Point) (current : point.role = some physical)
    (side : frontendSide physical = some .binary)
    (fits : StrandRoleSampling.Fits binaryCapacity primeCapacity
      (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) physical))
    (fallback answer : Answer) (H : Point → Digest × Answer) (link : Digest) :
    ApplicationViews.frontendCharge S
      (RuntimeAdaptiveViews.readBinaryView binary prime P R publicCfg S laws hashPublic decodePublic template capacity)
      point H (link,StrandSampling.normalize
        (factor (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) physical) fits) fallback answer) =
    ApplicationViews.frontendCharge S
      (RuntimeAdaptiveViews.readBinaryView binary prime P R publicCfg S laws hashPublic decodePublic template capacity)
      point H (link,answer) := by
  unfold ApplicationViews.frontendCharge
  congr 1
  apply propext
  unfold ApplicationViews.frontendBad RuntimeAdaptiveViews.readBinaryView
  cases hp : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic point with
  | none => rfl
  | some values =>
      dsimp only [Bind.bind,Option.bind]
      unfold ApplicationViews.readBinaryView
      split_ifs with starts
      · cases adapter : ApplicationViews.readAdapter (RuntimeAdaptive.binaryWithBits binary values.1)
          (RuntimeAdaptive.primeWithInputs prime values.2) (publicCfg).primeField
          (publicCfg).primeDecode (publicCfg).primeNonzero (publicCfg).conversion
          (publicCfg).advice (publicCfg).fallback point (point.priorAnswers H) with
        | none => rfl
        | some packet =>
            dsimp only [Bind.bind,Option.bind]
            cases payload : ApplicationViews.PartialMessages.read
                (packet.setup ((publicCfg).generator^Adapter.Mdoc.generatorExponent)).circuit
                (ApplicationPrefix.wire point Side.binary (publicCfg).binaryField g.binaryStart)
                (point.rank-g.binaryStart) with
            | none => rfl
            | some payload =>
                dsimp only [Bind.bind,Option.bind,ApplicationViews.FrontendView.bad]
                let shape := RuntimeShape.binaryPlan (RuntimeAdaptive.binaryWithBits binary values.1)
                  (RuntimeAdaptive.primeWithInputs prime values.2)
                  ((publicCfg).generator^Adapter.Mdoc.generatorExponent) template packet
                apply frontend_data_answer S _ shape .binary point H
                · apply binary_located shape
                  exact (RuntimeShape.binaryPlan_frontend _ _ _ _ _).trans geometry
                · intro actual same i bound
                  have eq := Option.some.inj (same.symm.trans current)
                  subst actual
                  exact StrandRoleSampling.normalize_binary_role_read B N binary.Original prime.Original RawB RawN
                    (Fin t ↪ Fin n) binaryCapacity primeCapacity binary.degree (prime.circuit.layers+1)
                    physical fits side fallback answer i bound
                · intro actual same domain
                  have eq := Option.some.inj (same.symm.trans current)
                  subst actual
                  exact StrandRoleSampling.normalize_binary_role_nonzero B N binary.Original prime.Original RawB RawN
                    (Fin t ↪ Fin n) binaryCapacity primeCapacity binary.degree (prime.circuit.layers+1)
                    physical fits side domain fallback answer
      · rfl

private theorem row_batching_normalize
    (hashPublic : Key → Option (Fin binary.nPublic → Bool))
    (decodePublic : Base → Option (Fin prime.nPublic → N))
    (fits : prime.circuit.layers+1 ≤ primeCapacity)
    (fallback answer : Answer) (point : Point) (H : Point → Digest × Answer) :
    ApplicationViews.batchBad S
      (RuntimeAdaptiveViews.readBatch binary prime P R publicCfg S laws hashPublic decodePublic)
      point H (StrandSampling.normalize (factor (.prime (prime.circuit.layers+1)) fits) fallback answer) ↔
    ApplicationViews.batchBad S
      (RuntimeAdaptiveViews.readBatch binary prime P R publicCfg S laws hashPublic decodePublic)
      point H answer := by
  have sample : laws.batchDecoder.decode
      (StrandSampling.normalize (factor (.prime (prime.circuit.layers+1)) fits) fallback answer) =
      laws.batchDecoder.decode answer := by
    funext i
    rw [laws.batch_agrees,laws.batch_agrees]
    exact StrandRoleSampling.normalize_prime_read B N binary.Original prime.Original RawB RawN
      (Fin t ↪ Fin n) binaryCapacity primeCapacity (prime.circuit.layers+1) fits fallback answer i.val i.isLt
  unfold ApplicationViews.batchBad ApplicationViews.packetBad SelectionSource.test
  apply exists_congr
  intro witness
  apply and_congr_right
  intro _
  unfold RuntimeAdaptiveViews.readBatch
  cases hp : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic point with
  | none => rfl
  | some values =>
      dsimp only [Bind.bind,Option.bind]
      unfold ApplicationViews.readBatchPacket
      cases read : ApplicationViews.readPrimePacket (RuntimeAdaptive.primeWithInputs prime values.2)
          (publicCfg).primeField (publicCfg).fallback point (point.priorAnswers H) with
      | none => rfl
      | some packet =>
          dsimp only [Bind.bind,Option.bind,ApplicationViews.optionBad,BatchPacket.bad]
          apply Iff.of_eq
          congr 1
          exact decoder_cast_eq _ laws.batchDecoder _ _ sample

omit [Fintype B] in
private theorem packet_answer {Data : Type}
    (read : (point : Point) → (Fin point.rank → Answer) → Option Data)
    (bad : Data → Pair → Answer → Prop) (point : Point) (H : Point → Digest × Answer)
    (left right : Answer) (same : ∀ data w, bad data w left ↔ bad data w right) :
    ApplicationViews.packetBad S read bad point H left ↔ ApplicationViews.packetBad S read bad point H right := by
  unfold ApplicationViews.packetBad SelectionSource.test
  apply exists_congr
  intro w
  apply and_congr_right
  intro _
  cases read point (point.priorAnswers H) with
  | none => rfl
  | some data => exact same data w

private theorem rescaling_charge_normalize (fallback answer : Answer) (point : Point)
    (H : Point → Digest × Answer) (link : Digest) :
    roleCharge S laws readers .rescaling point H
      (link,StrandSampling.normalize (factor .primeNonzero trivial) fallback answer) =
      roleCharge S laws readers .rescaling point H (link,answer) := by
  have sample : laws.rescaleDecoder.decode
      (StrandSampling.normalize (factor .primeNonzero trivial) fallback answer) =
      laws.rescaleDecoder.decode answer := by
    rw [laws.rescale_agrees]
    exact StrandRoleSampling.normalize_primeNonzero B N binary.Original prime.Original RawB RawN (Fin t ↪ Fin n)
      binaryCapacity primeCapacity fallback answer
  change RecursivePolygero.indicator (ApplicationViews.rescaleBad S readers.rescaleRead laws.rescaleDecoder
    point H _) = RecursivePolygero.indicator (ApplicationViews.rescaleBad S readers.rescaleRead laws.rescaleDecoder point H answer)
  congr 1
  apply propext
  exact packet_answer binary prime P R countBinary countPrime binaryCapacity primeCapacity S
    readers.rescaleRead (fun data w a => data.bad w (laws.rescaleDecoder.decode a)) point H _ _
    (fun _ _ => by rw [sample])

private theorem conversion_charge_normalize (fallback answer : Answer) (point : Point)
    (H : Point → Digest × Answer) (link : Digest) :
    roleCharge S laws readers .conversion point H
      (link,StrandSampling.normalize (factor .conversion trivial) fallback answer) =
      roleCharge S laws readers .conversion point H (link,answer) := by
  have sample : laws.conversionDecoder.decode
      (StrandSampling.normalize (factor .conversion trivial) fallback answer) =
      laws.conversionDecoder.decode answer := by
    rw [laws.conversion_agrees,laws.conversion_agrees]
    change (StrandSampling.normalize (factor .conversion trivial) fallback answer) .primeNonzero = answer .primeNonzero
    exact StrandRoleSampling.normalize_component B N binary.Original prime.Original RawB RawN (Fin t ↪ Fin n)
      binaryCapacity primeCapacity .primeNonzero fallback answer
  change RecursivePolygero.indicator (ApplicationViews.conversionBad S readers.conversionRead laws.conversionDecoder
    Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound point H _) =
      RecursivePolygero.indicator (ApplicationViews.conversionBad S readers.conversionRead laws.conversionDecoder
        Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound point H answer)
  congr 1
  apply propext
  exact packet_answer binary prime P R countBinary countPrime binaryCapacity primeCapacity S
    readers.conversionRead (fun data w a => data.bad Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound w
      (laws.conversionDecoder.decode a)) point H _ _ (fun _ _ => by rw [sample])

private theorem packing_charge_normalize (fits : binary.degree ≤ binaryCapacity)
    (fallback answer : Answer) (point : Point) (H : Point → Digest × Answer) (link : Digest) :
    roleCharge S laws readers .packing point H
      (link,StrandSampling.normalize (factor (.binary binary.degree) fits) fallback answer) =
      roleCharge S laws readers .packing point H (link,answer) := by
  have sample : laws.packingDecoder.decode
      (StrandSampling.normalize (factor (.binary binary.degree) fits) fallback answer) =
      laws.packingDecoder.decode answer := by
    funext i
    rw [laws.packing_agrees,laws.packing_agrees]
    exact StrandRoleSampling.normalize_binary_read B N binary.Original prime.Original RawB RawN (Fin t ↪ Fin n)
      binaryCapacity primeCapacity binary.degree fits fallback answer i.val i.isLt
  change RecursivePolygero.indicator (ApplicationViews.packingBad S readers.packingRead laws.packingDecoder
    point H _) = RecursivePolygero.indicator (ApplicationViews.packingBad S readers.packingRead laws.packingDecoder point H answer)
  congr 1
  apply propext
  exact packet_answer binary prime P R countBinary countPrime binaryCapacity primeCapacity S
    readers.packingRead (fun data w a => data.bad w (laws.packingDecoder.decode a)) point H _ _
    (fun _ _ => by rw [sample])

/-- Every actual application role reads only its physical factor. Resetting
the rest therefore preserves its existing charge for each explicit answer,
with the selected witness pair and strict-prefix oracle held fixed. -/
theorem application_role_normalize
    (hashPublic : Key → Option (Fin binary.nPublic → Bool))
    (decodePublic : Base → Option (Fin prime.nPublic → N))
    (primeShape : FrontendSchedule.Plan N prime.circuit) (primeGeometry : primeShape.frontend = g.prime)
    (primeFits : primeShape.capacity ≤ laws.primeCapacity)
    (binaryShape : FrontendSchedule.Plan B binary.template) (binaryGeometry : binaryShape.frontend = g.binary)
    (binaryFits : binaryShape.capacity ≤ laws.binaryCapacity)
    (coins : ∀ a : Answer, S.coins a = a .fingerprints)
    (role : Role) (point : Point) (current : point.role = some role)
    (fits : StrandRoleSampling.Fits binaryCapacity primeCapacity
      (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role))
    (fallback answer : Answer) (H : Point → Digest × Answer) (link : Digest) :
    let actual := concreteReaders S laws hashPublic decodePublic primeShape primeFits binaryShape binaryFits
    roleCharge S laws actual role point H
      (link,StrandSampling.normalize
        (factor (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role) fits) fallback answer) =
      roleCharge S laws actual role point H (link,answer) := by
  dsimp only
  have hb := binary_frontend_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg S laws hashPublic decodePublic binaryShape binaryGeometry binaryFits
  have hn := prime_frontend_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg S laws hashPublic decodePublic primeShape primeGeometry primeFits
  cases role with
  | fingerprint =>
      exact fingerprint_charge_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
        cfg S laws _ coins fallback answer point H link
  | inputAssertions side entries =>
      cases side with
      | binary => exact hb _ point current rfl fits fallback answer H link
      | prime => exact hn _ point current rfl fits fallback answer H link
  | assertions side stage entries fragments =>
      cases side with
      | binary => exact hb _ point current rfl fits fallback answer H link
      | prime => exact hn _ point current rfl fits fallback answer H link
  | sumcheck side stage round =>
      cases side with
      | binary => exact hb _ point current rfl fits fallback answer H link
      | prime => exact hn _ point current rfl fits fallback answer H link
  | terminal side stage =>
      cases side with
      | binary => exact hb _ point current rfl fits fallback answer H link
      | prime => exact hn _ point current rfl fits fallback answer H link
  | combine side stage entries =>
      cases side with
      | binary => exact hb _ point current rfl fits fallback answer H link
      | prime => exact hn _ point current rfl fits fallback answer H link
  | rowBatching =>
      change RecursivePolygero.indicator _ = RecursivePolygero.indicator _
      congr 1
      exact propext (row_batching_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
        cfg S laws hashPublic decodePublic fits fallback answer point H)
  | rescaling =>
      exact rescaling_charge_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
        cfg S laws _ fallback answer point H link
  | conversion =>
      exact conversion_charge_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
        cfg S laws _ fallback answer point H link
  | packing =>
      exact packing_charge_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
        cfg S laws _ fits fallback answer point H link
  | batching | opening => rfl

/-- The physical-factor charges retain the existing role budgets. This is
pointwise normalization followed by the original algebraic bound, so it adds
neither a candidate-list multiplier nor a per-frontend query charge. -/
theorem application_role_sum
    (hashPublic : Key → Option (Fin binary.nPublic → Bool))
    (decodePublic : Base → Option (Fin prime.nPublic → N))
    (primeShape : FrontendSchedule.Plan N prime.circuit) (primeGeometry : primeShape.frontend = g.prime)
    (primeFits : primeShape.capacity ≤ laws.primeCapacity)
    (binaryShape : FrontendSchedule.Plan B binary.template) (binaryGeometry : binaryShape.frontend = g.binary)
    (binaryFits : binaryShape.capacity ≤ laws.binaryCapacity)
    (coins : ∀ a : Answer, S.coins a = a .fingerprints)
    (LB LN : ℕ)
    (binaryListBound : ∀ (point : Point) H, (S.lists point.context (S.oracle H point.context)).1.card ≤ LB)
    (primeListBound : ∀ (point : Point) H, (S.lists point.context (S.oracle H point.context)).2.card ≤ LN)
    (role : Role) (point : Point) (current : point.role = some role)
    (fits : StrandRoleSampling.Fits binaryCapacity primeCapacity
      (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role))
    (fallback : Answer) (H : Point → Digest × Answer) :
    let actual := concreteReaders S laws hashPublic decodePublic primeShape primeFits binaryShape binaryFits
    (∑ candidate : Digest × Answer, roleCharge S laws actual role point H
      (candidate.1,StrandSampling.normalize
        (factor (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role) fits) fallback candidate.2)) ≤
      Fintype.card (Digest × Answer)*ApplicationCharging.roundBudget B Adapter.Mdoc.primeOrder
        Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound LB LN role := by
  dsimp only
  simp_rw [application_role_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg S laws hashPublic decodePublic primeShape primeGeometry primeFits binaryShape binaryGeometry binaryFits
    coins role point current fits fallback]
  exact roleCharge_sum S laws _ binaryListBound primeListBound role point H

end Runtime
end LfzkV2.Current.StrandLocalCharges
