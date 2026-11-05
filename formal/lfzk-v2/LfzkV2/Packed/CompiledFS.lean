import LfzkV2.Packed.CompiledSide
import LfzkV2.Packed.Inputs

/-!
# Actual native compiler instances of the staged security interface

The packing source row is built from the final native input claim and weights.
The two packing rows replace that source row on the original committed vector.
Degree one uses the original row directly and has no packing stage.
-/

namespace LfzkV2.Packed.Compiled

open SumcheckV2 RecursivePolygero NonrecursiveFS Finset Module
  DualPacking DualPacking.ArtinSchreier
open scoped Classical

variable {K F Ix Words Pad Slot C Context : Type}
variable [Field K] [Fintype K] [Field F] [Fintype F] [DecidableEq F]
variable [Algebra K F] [Fintype Ix] [DecidableEq Ix] [Fintype Words] [Fintype C]
variable {out input nPublic nPrivate : ℕ}
variable (S : Packed.Statement K F Ix Words Slot) (circuit : Native.Circuit F out input)
variable (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
variable (packedIndex : Fin nPrivate ↪ Words × Ix)
variable (publicInputs : Fin nPublic → F) (coordinate : Pad → Slot)

noncomputable def source (v : Native.Replay.Reconstruction circuit Pad Slot) :
    Packed.Statement K F Ix Words Slot :=
  S.withSource packedIndex v.constraints.inputClaim coordinate
    (fun i => circuit.inputWeights v.messages (monomialWeights v.point) (inputIndex (.inl i)))
    publicInputs
    (fun i => circuit.inputWeights v.messages (monomialWeights v.point) (inputIndex (.inr i)))

noncomputable def rows (v : Native.Replay.Reconstruction circuit Pad Slot) (U delta : Ix → F) (A : F) :
    List (LinearRow Slot F) :=
  v.constraints.layers.map (fun c => compileLayer c coordinate) ++
    (source S circuit inputIndex packedIndex publicInputs coordinate v).rows U delta A

noncomputable def statement (B : Instance F) (primary : Slot → Fin B.nw × Fin B.q)
    (v : Native.Replay.Reconstruction circuit Pad Slot)
    (product : Fin v.constraints.layers.length → Fin B.nq × Fin B.q)
    (U delta : Ix → F) (A : F)
    (eqns : B.Equations ≃ Backend.Equation
      (rows S circuit inputIndex packedIndex publicInputs coordinate v U delta A).length
      v.constraints.layers.length) : B.layer.Statement :=
  Backend.statement (Backend.rows (rows S circuit inputIndex packedIndex publicInputs coordinate v U delta A)
    v.constraints coordinate primary product ∘ eqns)

/-- This is an implication of the actual Polygero constraint system, rather
than an assumed backend-to-frontend transfer. -/
theorem satisfies_frontend_or_bad (B : Instance F) (primary : Slot → Fin B.nw × Fin B.q)
    (v : Native.Replay.Reconstruction circuit Pad Slot)
    (product : Fin v.constraints.layers.length → Fin B.nq × Fin B.q)
    (U delta : Ix → F) (A : F)
    (eqns : B.Equations ≃ Backend.Equation
      (rows S circuit inputIndex packedIndex publicInputs coordinate v U delta A).length
      v.constraints.layers.length)
    (core : B.layer.Witness) (htrace : ∀ k, traceF K (U k) = 0)
    (hsat : B.layer.satisfies
      (statement S circuit inputIndex packedIndex publicInputs coordinate B primary v product U delta A eqns) core) :
    let values := Backend.read core ∘ Backend.linearAddress primary
    Native.ClearAccepts (values ∘ coordinate) 0 (circuit.proof v.messages (monomialWeights v.point))
      (dot (circuit.inputWeights v.messages (monomialWeights v.point))
        (S.inputs inputIndex packedIndex publicInputs values)) ∨
      (source S circuit inputIndex packedIndex publicInputs coordinate v).Bad values U delta := by
  intro values
  have hbase : (Backend.statement (Backend.rows
      (rows S circuit inputIndex packedIndex publicInputs coordinate v U delta A)
      v.constraints coordinate primary product)).Satisfies core := by
    obtain ⟨hl,hp⟩ := (Backend.statement_satisfies_iff _ _).mp hsat
    exact (Backend.statement_satisfies_iff _ _).mpr ⟨fun e => by simpa using hl (eqns.symm e),hp⟩
  have hr := (source S circuit inputIndex packedIndex publicInputs coordinate v).satisfies_rows
    v.constraints coordinate primary product U delta A core htrace hbase
  exact S.frontend_or_bad circuit v.messages v.point v.constraints v.built inputIndex packedIndex
    publicInputs coordinate values U delta A hr.2 hr.1

end LfzkV2.Packed.Compiled

namespace LfzkV2.Packed.Direct

open SumcheckV2 RecursivePolygero NonrecursiveFS Finset
open scoped Classical

variable {F C Context Pad Slot : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input nPublic nPrivate : ℕ}
variable (circuit : Native.Circuit F out input)
variable (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
variable (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
variable (coordinate : Pad → Slot)

noncomputable def rows (v : Native.Replay.Reconstruction circuit Pad Slot) : List (LinearRow Slot F) :=
  compile v.constraints coordinate privateCoordinate
    (fun i => circuit.inputWeights v.messages (monomialWeights v.point) (inputIndex (.inl i))) publicInputs
    (fun i => circuit.inputWeights v.messages (monomialWeights v.point) (inputIndex (.inr i)))

noncomputable def statement (B : Instance F) (primary : Slot → Fin B.nw × Fin B.q)
    (v : Native.Replay.Reconstruction circuit Pad Slot)
    (product : Fin v.constraints.layers.length → Fin B.nq × Fin B.q)
    (eqns : B.Equations ≃ Backend.Equation
      (rows circuit inputIndex publicInputs privateCoordinate coordinate v).length v.constraints.layers.length) :
    B.layer.Statement :=
  Backend.statement (Backend.rows (rows circuit inputIndex publicInputs privateCoordinate coordinate v)
    v.constraints coordinate primary product ∘ eqns)

theorem satisfies_frontend (B : Instance F) (primary : Slot → Fin B.nw × Fin B.q)
    (v : Native.Replay.Reconstruction circuit Pad Slot)
    (product : Fin v.constraints.layers.length → Fin B.nq × Fin B.q)
    (eqns : B.Equations ≃ Backend.Equation
      (rows circuit inputIndex publicInputs privateCoordinate coordinate v).length v.constraints.layers.length)
    (core : B.layer.Witness)
    (hsat : B.layer.satisfies
      (statement circuit inputIndex publicInputs privateCoordinate coordinate B primary v product eqns) core) :
    let values := Backend.read core ∘ Backend.linearAddress primary
    Native.ClearAccepts (values ∘ coordinate) 0 (circuit.proof v.messages (monomialWeights v.point))
      (dot (circuit.inputWeights v.messages (monomialWeights v.point))
        (circuitInputs inputIndex publicInputs privateCoordinate values)) := by
  intro values
  have hbase : (Backend.statement (Backend.rows
      (rows circuit inputIndex publicInputs privateCoordinate coordinate v)
      v.constraints coordinate primary product)).Satisfies core := by
    obtain ⟨hl,hp⟩ := (Backend.statement_satisfies_iff _ _).mp hsat
    exact (Backend.statement_satisfies_iff _ _).mpr ⟨fun e => by simpa using hl (eqns.symm e),hp⟩
  have hr := Backend.satisfies_compiled
    (rows circuit inputIndex publicInputs privateCoordinate coordinate v)
    v.constraints coordinate primary product core hbase
  rw [input_sum]
  exact (Native.compiled_iff_clear (circuit.proof v.messages (monomialWeights v.point))
    v.constraints v.built coordinate privateCoordinate _ publicInputs _ values hr.2).mp hr.1

variable (B : Instance F)
variable (plan : Native.Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
variable (sampling : LfzkV2.Replay.Sampling F C circuit.shape) (dflt : C)
variable (publicOf : Context → Fin nPublic → F)
variable (primary : Slot → Fin B.nw × Fin B.q)
variable (product : (v : Native.Replay.Reconstruction circuit Pad Slot) →
  Fin v.constraints.layers.length → Fin B.nq × Fin B.q)
variable (eqns : ∀ ctx (v : Native.Replay.Reconstruction circuit Pad Slot), B.Equations ≃ Backend.Equation
  (rows circuit inputIndex (publicOf ctx) privateCoordinate coordinate v).length v.constraints.layers.length)
variable (cutoff bound : ℕ) (hcutoff : B.r + B.w - 1 < cutoff)
variable (hlist : CodingTheory.UniformFamilyBound B.n cutoff (B.r + B.w - 1) bound)
variable (decodeCoin : C → B.layer.Coin) (decodeQuery : C → B.layer.Query)
variable (potential : TerminalPotential B cutoff decodeCoin decodeQuery)

/-- Degree-one compiler instance: the source equation is authenticated directly.
The common carrier's unused scalar parameter is fixed to zero by the direct
proof representation; no packing message or challenge is introduced. -/
noncomputable def side : Packed.CompiledSide F C Context circuit B where
  Pad := Pad
  Slot := Slot
  Data := Native.Replay.Payload circuit
  frontend := id
  plan := plan
  sampling := sampling
  dflt := dflt
  packed := false
  cutoff := cutoff
  bound := bound
  cutoff_gt := hcutoff
  packing := hlist
  inputOf ctx g := circuitInputs inputIndex (publicOf ctx) privateCoordinate
    (Backend.read ((Counting.tupleCounts B).witness g) ∘ Backend.linearAddress primary)
  padOf g := (Backend.read ((Counting.tupleCounts B).witness g) ∘ Backend.linearAddress primary) ∘ coordinate
  statement p answers :=
    let v := Native.Replay.reconstructionFromAnswers sampling.decode circuit plan p.1.2 answers
    statement circuit inputIndex (publicOf p.1.1) privateCoordinate coordinate B primary v (product v) (eqns p.1.1 v)
  statement_prefix := by
    intro p first second h
    have hv := Native.Replay.reconstructionFromAnswers_eq_of_prefix sampling.decode circuit plan p.1.2
      first second (by intro j hj; apply h j; simpa [Replay.packingSlots] using hj)
    dsimp only
    rw [hv]
  precheck _ := True
  packingBad _ _ _ _ := False
  packingBudget := 0
  packingBudget_nonneg := le_rfl
  packing_count := by intros; simp [indicator]
  decodeCoin := decodeCoin
  decodeQuery := decodeQuery
  potential := potential
  transfer := by
    intro W H s candidate _ hsat
    let p := s.1.1
    let g := Counting.committedCandidate B W cutoff bound candidate
    let values := Backend.read ((Counting.tupleCounts B).witness g) ∘ Backend.linearAddress primary
    let v := Native.Replay.reconstructionFromAnswers sampling.decode circuit plan p.2
      (Replay.statementAnswers circuit.shape B Prod.fst (id ∘ Prod.snd) H p)
    have hfront := satisfies_frontend circuit inputIndex (publicOf p.1) privateCoordinate coordinate
      B primary v (product v) (eqns p.1 v) ((Counting.tupleCounts B).witness g) hsat
    have hv : v = FiatShamir.frontendView circuit B plan sampling Prod.fst (id ∘ Prod.snd) H p := by
      apply Native.Replay.reconstructionFromAnswers_eq_of_prefix
      intro j hj
      simp [Replay.statementAnswers, hj]
    left
    change Native.ClearAccepts (values ∘ coordinate) 0
      (circuit.proof (FiatShamir.frontendView circuit B plan sampling Prod.fst (id ∘ Prod.snd) H p).messages
        (monomialWeights (FiatShamir.frontendView circuit B plan sampling Prod.fst (id ∘ Prod.snd) H p).point))
      (dot (circuit.inputWeights
        (FiatShamir.frontendView circuit B plan sampling Prod.fst (id ∘ Prod.snd) H p).messages
        (monomialWeights (FiatShamir.frontendView circuit B plan sampling Prod.fst (id ∘ Prod.snd) H p).point))
        (circuitInputs inputIndex (publicOf p.1) privateCoordinate values))
    rw [← hv]
    exact hfront

end LfzkV2.Packed.Direct

namespace LfzkV2.Packed.Compiled

open SumcheckV2 RecursivePolygero NonrecursiveFS Finset Module
  DualPacking DualPacking.ArtinSchreier
open scoped Classical

variable {K F Ix Words Pad Slot C Context : Type}
variable [Field K] [Fintype K] [Field F] [Fintype F] [DecidableEq F]
variable [Algebra K F] [Fintype Ix] [DecidableEq Ix] [Fintype Words] [Fintype C]
variable {out input nPublic nPrivate : ℕ}
variable (S : Packed.Statement K F Ix Words Slot) (circuit : Native.Circuit F out input)
variable (B : Instance F)
variable (plan : Native.Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
variable (sampling : LfzkV2.Replay.Sampling F C circuit.shape) (dflt : C)
variable (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
variable (packedIndex : Fin nPrivate ↪ Words × Ix)
variable (publicOf : Context → Fin nPublic → F) (coordinate : Pad → Slot)
variable (primary : Slot → Fin B.nw × Fin B.q)
variable (product : (v : Native.Replay.Reconstruction circuit Pad Slot) →
  Fin v.constraints.layers.length → Fin B.nq × Fin B.q)
variable (eqns : ∀ ctx (v : Native.Replay.Reconstruction circuit Pad Slot) (U delta : Ix → F) (A : F),
  B.Equations ≃ Backend.Equation
    (rows S circuit inputIndex packedIndex (publicOf ctx) coordinate v U delta A).length v.constraints.layers.length)
variable (cutoff bound : ℕ) (hcutoff : B.r + B.w - 1 < cutoff)
variable (hlist : CodingTheory.UniformFamilyBound B.n cutoff (B.r + B.w - 1) bound)
variable (decodePacking : C → Ix → F) (packingFiber : ℕ)
variable (hpackingFiber : ∀ delta, (univ.filter fun c => decodePacking c = delta).card ≤ packingFiber)
variable (hpackingBalanced : packingFiber * Fintype.card (Ix → F) = Fintype.card C)
variable (decodeCoin : C → B.layer.Coin) (decodeQuery : C → B.layer.Query)
variable (potential : TerminalPotential B cutoff decodeCoin decodeQuery)

/-- Full packed compiler instance. Its transfer and local error bound are
derived from the emitted rows and the trace-pairing theorem. -/
noncomputable def side : Packed.CompiledSide F C Context circuit B where
  Pad := Pad
  Slot := Slot
  Data := Native.Replay.Payload circuit × (Ix → F)
  frontend := Prod.fst
  plan := plan
  sampling := sampling
  dflt := dflt
  packed := true
  cutoff := cutoff
  bound := bound
  cutoff_gt := hcutoff
  packing := hlist
  inputOf ctx g := S.inputs inputIndex packedIndex (publicOf ctx)
    (Backend.read ((Counting.tupleCounts B).witness g) ∘ Backend.linearAddress primary)
  padOf g := (Backend.read ((Counting.tupleCounts B).witness g) ∘ Backend.linearAddress primary) ∘ coordinate
  statement p answers :=
    let v := Native.Replay.reconstructionFromAnswers sampling.decode circuit plan p.1.2.1 answers
    let delta := decodePacking (answers (LfzkV2.Replay.slots circuit.shape))
    statement S circuit inputIndex packedIndex (publicOf p.1.1) coordinate B primary v (product v)
      p.1.2.2 delta p.2 (eqns p.1.1 v p.1.2.2 delta p.2)
  statement_prefix := by
    intro p first second h
    have hv := Native.Replay.reconstructionFromAnswers_eq_of_prefix sampling.decode circuit plan p.1.2.1
      first second (by intro j hj; apply h j; change j < _ + 1; omega)
    have hd := congrArg decodePacking (h (LfzkV2.Replay.slots circuit.shape) (by change _ < _ + 1; omega))
    dsimp only
    rw [hv, hd]
  precheck p := ∀ k, traceF K (p.2.2 k) = 0
  packingBad W p pref c :=
    let v := Native.Replay.reconstructionFromAnswers sampling.decode circuit plan p.2.1
      (LfzkV2.Replay.fillAnswers dflt pref)
    ∃ candidate : Fin bound,
      (source S circuit inputIndex packedIndex (publicOf p.1) coordinate v).Bad
        (Backend.read ((Counting.tupleCounts B).witness
          (Counting.committedCandidate B W cutoff bound candidate)) ∘ Backend.linearAddress primary)
        p.2.2 (decodePacking c)
  packingBudget := (sampling.unitFiber * bound : ℕ)
  packingBudget_nonneg := Nat.cast_nonneg _
  packing_count := by
    classical
    intro W p pref
    let v := Native.Replay.reconstructionFromAnswers sampling.decode circuit plan p.2.1
      (LfzkV2.Replay.fillAnswers dflt pref)
    have h := (source S circuit inputIndex packedIndex (publicOf p.1) coordinate v).sampled_candidates_card_le
      decodePacking hpackingFiber hpackingBalanced sampling.balanced
      (fun candidate : Fin bound => Backend.read ((Counting.tupleCounts B).witness
        (Counting.committedCandidate B W cutoff bound candidate)) ∘ Backend.linearAddress primary) p.2.2
    let event := fun c : C => ∃ candidate : Fin bound,
      (source S circuit inputIndex packedIndex (publicOf p.1) coordinate v).Bad
        (Backend.read ((Counting.tupleCounts B).witness
          (Counting.committedCandidate B W cutoff bound candidate)) ∘ Backend.linearAddress primary)
        p.2.2 (decodePacking c)
    change (∑ c : C, indicator (event c)) ≤ (sampling.unitFiber * bound : ℕ)
    have he : (∑ c : C, indicator (event c)) = ((univ.filter event).card : ℚ) := by
      calc
        _ = ∑ c : C, if event c then (1 : ℚ) else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          by_cases hc : event c <;> simp [indicator, hc]
        _ = _ := Finset.sum_boole event univ
    exact he.le.trans ((Nat.cast_le (α := ℚ)).mpr h)
  decodeCoin := decodeCoin
  decodeQuery := decodeQuery
  potential := potential
  transfer := by
    intro W H s candidate htrace hsat
    let p := s.1.1
    let g := Counting.committedCandidate B W cutoff bound candidate
    let values := Backend.read ((Counting.tupleCounts B).witness g) ∘ Backend.linearAddress primary
    let v := Native.Replay.reconstructionFromAnswers sampling.decode circuit plan p.2.1
      (Replay.statementAnswers circuit.shape B Prod.fst (Prod.fst ∘ Prod.snd) H p)
    let delta := decodePacking (H (Replay.packing circuit.shape B p))
    have hd : decodePacking (Replay.statementAnswers circuit.shape B Prod.fst
        (Prod.fst ∘ Prod.snd) H p (LfzkV2.Replay.slots circuit.shape)) = delta := by
      simp [Replay.statementAnswers, delta]
    change B.layer.satisfies
      (statement S circuit inputIndex packedIndex (publicOf p.1) coordinate B primary v (product v)
        p.2.2 _ s.1.2 (eqns p.1 v p.2.2 _ s.1.2)) ((Counting.tupleCounts B).witness g) at hsat
    rw [hd] at hsat
    have hresult := satisfies_frontend_or_bad S circuit inputIndex packedIndex (publicOf p.1) coordinate
      B primary v (product v) p.2.2 delta s.1.2 (eqns p.1 v p.2.2 delta s.1.2)
      ((Counting.tupleCounts B).witness g) htrace hsat
    have hv : v = FiatShamir.frontendView circuit B plan sampling Prod.fst (Prod.fst ∘ Prod.snd) H p := by
      apply Native.Replay.reconstructionFromAnswers_eq_of_prefix
      intro j hj
      simp [Replay.statementAnswers, hj]
    rcases hresult with hfront | hbad
    · left
      change Native.ClearAccepts (values ∘ coordinate) 0
        (circuit.proof (FiatShamir.frontendView circuit B plan sampling Prod.fst (Prod.fst ∘ Prod.snd) H p).messages
          (monomialWeights (FiatShamir.frontendView circuit B plan sampling Prod.fst (Prod.fst ∘ Prod.snd) H p).point))
        (dot (circuit.inputWeights
          (FiatShamir.frontendView circuit B plan sampling Prod.fst (Prod.fst ∘ Prod.snd) H p).messages
          (monomialWeights (FiatShamir.frontendView circuit B plan sampling Prod.fst (Prod.fst ∘ Prod.snd) H p).point))
          (S.inputs inputIndex packedIndex (publicOf p.1) values))
      rw [← hv]
      exact hfront
    · right
      refine ⟨rfl, candidate, ?_⟩
      have hpref : Native.Replay.reconstructionFromAnswers sampling.decode circuit plan p.2.1
          (LfzkV2.Replay.fillAnswers dflt
            ((Replay.points circuit.shape B true Prod.fst (Prod.fst ∘ Prod.snd)).chal H
              (Replay.packing circuit.shape B p))) = v := by
        apply Native.Replay.reconstructionFromAnswers_eq_of_prefix
        intro j hj
        rw [LfzkV2.Replay.fillAnswers, dif_pos (show j <
          (Replay.points circuit.shape B true Prod.fst (Prod.fst ∘ Prod.snd)).slot
            (Replay.packing circuit.shape B p) from hj)]
        simp [Replay.packing_prefix, Replay.statementAnswers, hj]
      exact hpref.symm ▸ hbad

end LfzkV2.Packed.Compiled
