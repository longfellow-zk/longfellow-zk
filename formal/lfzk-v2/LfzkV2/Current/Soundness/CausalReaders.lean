import LfzkV2.Current.Soundness.RuntimeCharges

/-! Causal equalities for the actual runtime's local tests. Oracle values
outside the strict ancestor tape may differ, provided the original committed
tuple is the same. These identities justify evaluating local tests from explicit prefix state.
-/
noncomputable section
namespace LfzkV2.Current
open ApplicationOracle ApplicationViews ApplicationCharging
open scoped Classical

section Application
variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN : Type}
variable [Field B] [Field N] [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N]
  [Fintype IB] [Fintype IN] [Fintype C]
local notation "Point" => Input roles Key Block Link Body
variable (S : SelectionSource roles Key Block Link Body C Oracle B N IB IN)

omit [Fintype B] [Fintype N] [Fintype C] in
theorem ApplicationOracle.SelectionSource.selected_prior (point : Point) (H H' : Point → Link × C)
    (prior : point.priorAnswers H = point.priorAnswers H')
    (committed : S.oracle H point.context = S.oracle H' point.context) : S.selected point H = S.selected point H' := by
  unfold SelectionSource.selected Selection.atPoint
  rw [prior, committed]

omit [Fintype B] [Fintype N] [Fintype C] in
theorem ApplicationOracle.SelectionSource.test_prior {D : Type} (point : Point) (H H' : Point → Link × C)
    (prior : point.priorAnswers H = point.priorAnswers H')
    (committed : S.oracle H point.context = S.oracle H' point.context)
    (read : (point : Point) → (Fin point.rank → C) → D)
    (bad : D → Selection.Pair B N IB IN → C → Prop) (answer : C) :
    S.test read bad point H answer ↔ S.test read bad point H' answer := by
  unfold SelectionSource.test
  rw [S.selected_prior point H H' prior committed, prior]

omit [Fintype N] [Fintype C] in
theorem ApplicationOracle.SelectionSource.binarySelection_prior (point : Point) (H H' : Point → Link × C)
    (committed : S.oracle H point.context = S.oracle H' point.context) (answer : C) :
    S.binarySelection point H answer ↔ S.binarySelection point H' answer := by
  unfold SelectionSource.binarySelection
  rw [committed]

omit [Fintype B] [Fintype C] in
theorem ApplicationOracle.SelectionSource.primeSelection_prior (point : Point) (H H' : Point → Link × C)
    (committed : S.oracle H point.context = S.oracle H' point.context) (answer : C) :
    S.primeSelection point H answer ↔ S.primeSelection point H' answer := by
  unfold SelectionSource.primeSelection
  rw [committed]

variable {F Pad : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype B] [Fintype N] in
theorem ApplicationViews.FrontendView.bad_prior (point : Point) (H H' : Point → Link × C)
    (prior : point.priorAnswers H = point.priorAnswers H')
    (committed : S.oracle H point.context = S.oracle H' point.context)
    (view : FrontendView F Pad (Selection.Pair B N IB IN) Point C) (answer : C) :
    view.bad S point H answer ↔ view.bad S point H' answer := by
  unfold FrontendView.bad FrontendData.bad SelectedFrontendOracle.bad
  have selected := S.selected_prior point H H' prior committed
  change Selection.atPoint S.lists S.coins S.responses S.oracle point H =
    Selection.atPoint S.lists S.coins S.responses S.oracle point H' at selected
  rw [selected]
  unfold Input.answersWith
  rw [prior]

omit [Fintype B] [Fintype N] in
theorem ApplicationViews.frontendBad_prior (point : Point) (H H' : Point → Link × C)
    (prior : point.priorAnswers H = point.priorAnswers H')
    (committed : S.oracle H point.context = S.oracle H' point.context)
    (read : (point : Point) → (Fin point.rank → C) →
      Option (FrontendView F Pad (Selection.Pair B N IB IN) Point C)) (answer : C) :
    frontendBad S read point H answer ↔ frontendBad S read point H' answer := by
  unfold frontendBad
  rw [prior]
  cases read point (point.priorAnswers H') with
  | none => rfl
  | some view => exact view.bad_prior S point H H' prior committed answer

omit [Fintype B] [Fintype N] in
theorem ApplicationViews.frontendCharge_prior (point : Point) (H H' : Point → Link × C)
    (prior : point.priorAnswers H = point.priorAnswers H')
    (committed : S.oracle H point.context = S.oracle H' point.context)
    (read : (point : Point) → (Fin point.rank → C) →
      Option (FrontendView F Pad (Selection.Pair B N IB IN) Point C)) (answer : Link × C) :
    frontendCharge S read point H answer = frontendCharge S read point H' answer := by
  unfold frontendCharge
  rw [frontendBad_prior S point H H' prior committed read answer.2]

omit [Fintype B] [Fintype N] [Fintype C] in
theorem ApplicationViews.packetBad_prior {D : Type} (point : Point) (H H' : Point → Link × C)
    (prior : point.priorAnswers H = point.priorAnswers H')
    (committed : S.oracle H point.context = S.oracle H' point.context)
    (read : (point : Point) → (Fin point.rank → C) → Option D)
    (bad : D → Selection.Pair B N IB IN → C → Prop) (answer : C) :
    packetBad S read bad point H answer ↔ packetBad S read bad point H' answer :=
  S.test_prior point H H' prior committed read _ answer

end Application

namespace RuntimeAdaptiveCharges
open Application ApplicationSetup RecursivePolygero
variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Oracle : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable {binary : BinaryPublic B shared maskBits adviceBits} {prime : PrimePublic N shared}
variable {P : FieldBackend B k s n t} {R : FieldBackend N k s n t}
variable {cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt)}
variable (S : RuntimeCover.Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := C) binary prime (Oracle := Oracle))
variable (laws : RuntimeCover.SamplerLaws binary prime P R cfg S)
variable (readers : Readers (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := C) binary prime)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)

theorem roleCharge_prior (role : Role) (point : Point) (H H' : Point → Digest × C)
    (prior : point.priorAnswers H = point.priorAnswers H')
    (committed : S.oracle H point.context = S.oracle H' point.context) (answer : Digest × C) :
    roleCharge S laws readers role point H answer = roleCharge S laws readers role point H' answer := by
  have hb := propext (S.binarySelection_prior point H H' committed answer.2)
  have hn := propext (S.primeSelection_prior point H H' committed answer.2)
  have hbf := frontendCharge_prior S point H H' prior committed readers.binaryRead answer
  have hnf := frontendCharge_prior S point H H' prior committed readers.primeRead answer
  have hbatch := propext (packetBad_prior S point H H' prior committed readers.batchRead
    (fun packet w a => packet.bad w a) answer.2)
  have hs := propext (packetBad_prior S point H H' prior committed readers.rescaleRead
    (fun packet w a => packet.bad w (laws.rescaleDecoder.decode a)) answer.2)
  have hc := propext (packetBad_prior S point H H' prior committed readers.conversionRead
    (fun packet w a => packet.bad Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound w
      (laws.conversionDecoder.decode a)) answer.2)
  have hp := propext (packetBad_prior S point H H' prior committed readers.packingRead
    (fun packet w a => packet.bad w (laws.packingDecoder.decode a)) answer.2)
  cases role with
  | fingerprint => simp only [roleCharge, hb, hn]
  | inputAssertions side entries => cases side <;> first | exact hbf | exact hnf
  | assertions side stage entries fragments => cases side <;> first | exact hbf | exact hnf
  | sumcheck side stage index => cases side <;> first | exact hbf | exact hnf
  | terminal side stage => cases side <;> first | exact hbf | exact hnf
  | combine side stage entries => cases side <;> first | exact hbf | exact hnf
  | rowBatching => simp only [roleCharge, batchBad, hbatch]
  | rescaling => simp only [roleCharge, rescaleBad, hs]
  | conversion => simp only [roleCharge, conversionBad, hc]
  | packing => simp only [roleCharge, packingBad, hp]
  | batching | opening => rfl

theorem single_prior (point : Point) (H H' : Point → Digest × C)
    (prior : point.priorAnswers H = point.priorAnswers H')
    (committed : S.oracle H point.context = S.oracle H' point.context) (answer : Digest × C) :
    single S laws readers point H answer = single S laws readers point H' answer := by
  unfold single
  cases point.role with
  | none => rfl
  | some role => exact roleCharge_prior S laws readers role point H H' prior committed answer

end RuntimeAdaptiveCharges

namespace BackendOracle
open RecursivePolygero
variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {roles : List Role} {Context Block Link Body C : Type}
variable {index : Fin roles.length} (next : index.val+1 < roles.length)
variable (encode : JointResponse.Response P R → Block) (injective : Function.Injective encode)
variable (derive : (LfzkV2.Current.BackendQueries.Parent roles Context Block Link index) → (Fin index.val → C) → JointResponse.Statement P R)
variable (cut : ((LfzkV2.Current.Input roles Context Block Link Body) → Link × C) → Context → JointResponse.Oracle P R)
variable (coin : C → JointResponse.Coin P R) (query : C → LigeroFamily.QuerySet n t)
variable (cutoff : ℕ × ℕ) (epsilon : ℚ)

include injective in
theorem single_prior (point : (LfzkV2.Current.Input roles Context Block Link Body)) (H H' : (LfzkV2.Current.Input roles Context Block Link Body) → Link × C)
    (_prior : point.priorAnswers H = point.priorAnswers H')
    (_committed : ∀ context, cut H context = cut H' context) (answer : Link × C) :
    LfzkV2.Current.BackendOracle.single (i := index) P R next encode derive cut coin query cutoff epsilon point H answer =
      LfzkV2.Current.BackendOracle.single (i := index) P R next encode derive cut coin query cutoff epsilon point H' answer := by
  cases hp : parentOf (i := index) point with
  | some parent =>
      simp only [single, hp, BackendFS.rank, _committed]
  | none =>
      cases hc : childOf P R next encode point with
      | none => simp only [single, hp, hc]
      | some child =>
          have pointEq := childOf_spec P R next encode injective hc
          rw [← pointEq] at _prior
          simp only [BackendQueries.Parent.child_answers] at _prior
          have parentPrior : child.1.point.priorAnswers H = child.1.point.priorAnswers H' := by
            have same := congrArg (fun f : Fin (index.val+1) → C => Fin.init f) _prior
            exact (Fin.init_snoc (α := fun _ => C) (H child.1.point).2
              (child.1.point.priorAnswers H)).symm.trans
              (same.trans (Fin.init_snoc (α := fun _ => C) (H' child.1.point).2
                (child.1.point.priorAnswers H')))
          have parentCoin : (H child.1.point).2 = (H' child.1.point).2 := by
            have same := congrFun _prior (Fin.last index.val)
            simpa only [Fin.snoc_last] using same
          simp only [single, hp, hc, BackendFS.opening, BackendQueries.Parent.statement,
            parentPrior, parentCoin, _committed]

end BackendOracle

end LfzkV2.Current
