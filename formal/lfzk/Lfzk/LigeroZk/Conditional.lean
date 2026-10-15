import Lfzk.LigeroZk.Masking
import Lfzk.LigeroZk.Distribution

-- Ported verbatim from `proofs/ligero/LigeroFamily/ZeroKnowledge/Conditional.lean` (only the import paths are rewritten);
-- `formal/ligero/` must not change, so the module lives under `Lfzk.LigeroZk`.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Exact conditional zero knowledge for LigeroFamily responses

The source spaces below are the residual randomness after the verifier has
seen one complete queried column set.  Surjectivity of the two mask maps,
proved from evaluation interpolation in `LigeroFamily.Masking`, turns their
uniform distributions into exact additive one-time pads.
-/

namespace LigeroFamily

open MultiplicativeCode

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {r w n : ℕ}

noncomputable local instance evaluationSubmoduleFintype
    (S : Submodule F (EvaluationRow F r w n)) : Fintype S :=
  Fintype.ofFinite S

/-- Queried code evaluations of one Longfellow row with a fixed witness
suffix and an explicit random prefix. -/
noncomputable def openedRow
    (C : MultiplicativeCode F r w n) (Q : Finset (Fin n))
    (witness : Fin w → F) (padding : Fin r → F) : ↥Q → F :=
  fun j ↦ C.encode padding witness (codePosition j.1)

omit [Fintype F] [DecidableEq F] in
/-- The Longfellow random prefix is in bijection with any `r` opened code
evaluations.  Hence those openings are uniform and witness-independent. -/
theorem longfellow_openings_bijective
    (C : MultiplicativeCode F r w n) (Q : Finset (Fin n))
    (hQ : Q.card = r) (witness : Fin w → F) :
    Function.Bijective (openedRow C Q witness) := by
  classical
  constructor
  · intro first second heq
    let left := C.encode first witness
    let right := C.encode second witness
    have hrows : left = right := by
      apply C.base_unique (C.encode_mem first witness) (C.encode_mem second witness)
        (witnessPositions r w n ∪ codePositions (r := r) (w := w) Q)
      · rw [card_witnessPositions_union_codePositions Q, hQ,
          Nat.add_comm, ← C.k_eq]
      · intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
          simp
        · rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
          exact congrFun heq ⟨j, hj⟩
    funext i
    have := congrFun hrows (randomPosition i)
    simpa [left, right] using this
  · intro opened
    let S := witnessPositions r w n ∪ codePositions (r := r) (w := w) Q
    have hS : S.card ≤ C.k := by
      rw [card_witnessPositions_union_codePositions Q, hQ,
        Nat.add_comm, ← C.k_eq]
    let prescribed : ↥S → F := fun i ↦
      match i.1 with
      | Sum.inl (Sum.inr j) => witness j
      | Sum.inr j => if hj : j ∈ Q then opened ⟨j, hj⟩ else 0
      | _ => 0
    let row := C.interpolateBaseRow S hS prescribed
    have hrow : row ∈ C.base := C.interpolateBaseRow_mem S hS prescribed
    have hprescribed : ∀ i : ↥S, row i.1 = prescribed i :=
      C.interpolateBaseRow_apply S hS prescribed
    let padding := randomValues row
    have hencode : C.encode padding witness = row := by
      apply C.base_unique (C.encode_mem padding witness) hrow
        (messagePositions r w n)
      · simp [C.k_eq]
      · intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
        cases j with
        | inl j =>
            change C.encode padding witness (randomPosition j) =
              row (randomPosition j)
            rw [C.encode_random]
            rfl
        | inr j =>
            have hjS : witnessPosition j ∈ S := by
              apply Finset.mem_union_left
              simp [witnessPositions]
            have hj := hprescribed ⟨witnessPosition j, hjS⟩
            change C.encode padding witness (witnessPosition j) =
              row (witnessPosition j)
            rw [C.encode_witness]
            simpa [prescribed, witnessPosition] using hj.symm
    refine ⟨padding, ?_⟩
    funext j
    have hjS : codePosition j.1 ∈ S := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j.1, j.2, rfl⟩
    have hj := hprescribed ⟨codePosition j.1, hjS⟩
    rw [openedRow, hencode]
    simpa [prescribed, codePosition, j.2] using hj

def baseQueryKernel (C : MultiplicativeCode F r w n)
    (Q : Finset (Fin n)) : Submodule F (EvaluationRow F r w n) where
  carrier := { row | row ∈ C.base ∧ ∀ j ∈ Q, row (codePosition j) = 0 }
  zero_mem' := by simp
  add_mem' := by
    rintro left right ⟨hleft, hleftQ⟩ ⟨hright, hrightQ⟩
    refine ⟨C.base.add_mem hleft hright, ?_⟩
    intro j hj
    simp [hleftQ j hj, hrightQ j hj]
  smul_mem' := by
    rintro scalar row ⟨hrow, hrowQ⟩
    refine ⟨C.base.smul_mem scalar hrow, ?_⟩
    intro j hj
    simp [hrowQ j hj]

def quadraticResponseKernel (C : MultiplicativeCode F r w n)
    (Q : Finset (Fin n)) : Submodule F (EvaluationRow F r w n) where
  carrier := { row | row ∈ C.response ∧
    (∀ i, row (witnessPosition i) = 0) ∧
    ∀ j ∈ Q, row (codePosition j) = 0 }
  zero_mem' := by simp
  add_mem' := by
    rintro left right ⟨hleft, hleftW, hleftQ⟩
      ⟨hright, hrightW, hrightQ⟩
    refine ⟨C.response.add_mem hleft hright, ?_, ?_⟩
    · intro i
      simp [hleftW i, hrightW i]
    · intro j hj
      simp [hleftQ j hj, hrightQ j hj]
  smul_mem' := by
    rintro scalar row ⟨hrow, hrowW, hrowQ⟩
    refine ⟨C.response.smul_mem scalar hrow, ?_, ?_⟩
    · intro i
      simp [hrowW i]
    · intro j hj
      simp [hrowQ j hj]

/-- The two residual mask rows that generate a quadratic response pad. -/
structure QuadraticMaskSource (C : MultiplicativeCode F r w n)
    (Q : Finset (Fin n)) where
  vCoefficient : baseQueryKernel C Q
  zWCoefficient : baseQueryKernel C Q
  deriving DecidableEq

namespace QuadraticMaskSource

variable {C : MultiplicativeCode F r w n} {Q : Finset (Fin n)}

def prodEquiv : QuadraticMaskSource C Q ≃
    baseQueryKernel C Q × baseQueryKernel C Q where
  toFun masks := (masks.vCoefficient, masks.zWCoefficient)
  invFun masks := ⟨masks.1, masks.2⟩
  left_inv masks := by cases masks; rfl
  right_inv masks := by cases masks; rfl

noncomputable instance : Fintype (QuadraticMaskSource C Q) :=
  Fintype.ofEquiv (baseQueryKernel C Q × baseQueryKernel C Q) prodEquiv.symm

instance : Zero (QuadraticMaskSource C Q) := ⟨⟨0, 0⟩⟩
instance : Add (QuadraticMaskSource C Q) :=
  ⟨fun left right ↦ ⟨left.vCoefficient + right.vCoefficient,
    left.zWCoefficient + right.zWCoefficient⟩⟩
instance : Neg (QuadraticMaskSource C Q) :=
  ⟨fun masks ↦ ⟨-masks.vCoefficient, -masks.zWCoefficient⟩⟩
instance : Sub (QuadraticMaskSource C Q) :=
  ⟨fun left right ↦ ⟨left.vCoefficient - right.vCoefficient,
    left.zWCoefficient - right.zWCoefficient⟩⟩
instance : SMul ℕ (QuadraticMaskSource C Q) :=
  ⟨fun scalar masks ↦ ⟨scalar • masks.vCoefficient,
    scalar • masks.zWCoefficient⟩⟩
instance : SMul ℤ (QuadraticMaskSource C Q) :=
  ⟨fun scalar masks ↦ ⟨scalar • masks.vCoefficient,
    scalar • masks.zWCoefficient⟩⟩

instance : AddCommGroup (QuadraticMaskSource C Q) :=
  Function.Injective.addCommGroup
    (fun masks ↦ (masks.vCoefficient, masks.zWCoefficient))
    (by intro left right h; cases left; cases right; cases h; rfl)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem add_vCoefficient (left right : QuadraticMaskSource C Q) :
    (left + right).vCoefficient = left.vCoefficient + right.vCoefficient := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem add_zWCoefficient (left right : QuadraticMaskSource C Q) :
    (left + right).zWCoefficient =
      left.zWCoefficient + right.zWCoefficient := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem neg_vCoefficient (masks : QuadraticMaskSource C Q) :
    (-masks).vCoefficient = -masks.vCoefficient := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem neg_zWCoefficient (masks : QuadraticMaskSource C Q) :
    (-masks).zWCoefficient = -masks.zWCoefficient := rfl

end QuadraticMaskSource

noncomputable def quadraticMaskMap
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : Finset (Fin n)) :
    QuadraticMaskSource C Q → quadraticResponseKernel C Q :=
  fun masks ↦ ⟨rowMul M.vanishing masks.vCoefficient.1 +
      rowMul C.zW masks.zWCoefficient.1, by
    refine ⟨C.response.add_mem (M.vanishing_mul_mem masks.vCoefficient.2.1)
      (C.mul_mem C.zW_mem masks.zWCoefficient.2.1), ?_, ?_⟩
    · intro i
      change M.vanishing (witnessPosition i) *
          masks.vCoefficient.1 (witnessPosition i) +
        C.zW (witnessPosition i) *
          masks.zWCoefficient.1 (witnessPosition i) = 0
      rw [show M.vanishing (witnessPosition i) = 0 from
        M.vanishing_message (Sum.inr i), C.zW_witness i]
      simp
    · intro j hj
      simp [rowMul, masks.vCoefficient.2.2 j hj,
        masks.zWCoefficient.2.2 j hj]⟩

omit [Fintype F] [DecidableEq F] in
theorem quadraticMaskMap_surjective
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : Finset (Fin n)) (hQ : Q.card = r) (hrw : r ≤ w)
    (J : Finset (Fin n)) (hJ : J.card = C.k) :
    Function.Surjective (quadraticMaskMap C M Q) := by
  intro response
  obtain ⟨first, second, hfirst, hsecond, hfirstQ, hsecondQ, heq⟩ :=
    MultiplicativeCode.quadratic_mask_surjective C M Q hQ hrw J hJ response.1
      response.2.1 response.2.2.1 response.2.2.2
  refine ⟨QuadraticMaskSource.mk
    ⟨first, hfirst, hfirstQ⟩ ⟨second, hsecond, hsecondQ⟩, ?_⟩
  apply Subtype.ext
  exact heq.symm

/-- The complete quadratic response is an exact one-time pad even after all
queried values of both mask rows have been fixed. -/
theorem quadratic_response_perfectly_masked
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : Finset (Fin n)) (hQ : Q.card = r) (hrw : r ≤ w)
    (J : Finset (Fin n)) (hJ : J.card = C.k)
    (secret : quadraticResponseKernel C Q) :
    SameDistribution
      (fun masks ↦ secret + quadraticMaskMap C M Q masks)
      (quadraticMaskMap C M Q) := by
  classical
  apply surjective_additive_map_one_time_pad
  · intro first second
    apply Subtype.ext
    funext i
    simp [quadraticMaskMap, rowMul]
    ring
  · intro source
    apply Subtype.ext
    funext i
    simp [quadraticMaskMap, rowMul]
    ring
  · exact quadraticMaskMap_surjective C M Q hQ hrw J hJ

def linearZRCoefficientKernel (C : MultiplicativeCode F r w n)
    (Q : Finset (Fin n)) (Λ : (Fin w → F) →ₗ[F] F) :
    Submodule F (EvaluationRow F r w n) where
  carrier := { row | row ∈ C.base ∧
    (∀ j ∈ Q, row (codePosition j) = 0) ∧
    Λ (witnessValues row) = 0 }
  zero_mem' := by
    refine ⟨C.base.zero_mem, ?_, ?_⟩
    · simp
    · exact Λ.map_zero
  add_mem' := by
    rintro left right ⟨hleft, hleftQ, hleftΛ⟩
      ⟨hright, hrightQ, hrightΛ⟩
    refine ⟨C.base.add_mem hleft hright, ?_, ?_⟩
    · intro j hj
      simp [hleftQ j hj, hrightQ j hj]
    · rw [show witnessValues (left + right) =
          witnessValues left + witnessValues right by rfl,
        map_add, hleftΛ, hrightΛ, add_zero]
  smul_mem' := by
    rintro scalar row ⟨hrow, hrowQ, hrowΛ⟩
    refine ⟨C.base.smul_mem scalar hrow, ?_, ?_⟩
    · intro j hj
      simp [hrowQ j hj]
    · rw [show witnessValues (scalar • row) =
          scalar • witnessValues row by rfl, map_smul, hrowΛ, smul_zero]

/-- Special linear-response differences: response-code rows that vanish on
the random prefix and opened columns and satisfy the permitted witness
functional. -/
def linearResponseKernel (C : MultiplicativeCode F r w n)
    (Q : Finset (Fin n)) (Λ : (Fin w → F) →ₗ[F] F) :
    Submodule F (EvaluationRow F r w n) where
  carrier := { row | row ∈ C.response ∧
    (∀ i, row (randomPosition i) = 0) ∧
    (∀ j ∈ Q, row (codePosition j) = 0) ∧
    Λ (witnessValues row) = 0 }
  zero_mem' := by
    refine ⟨C.response.zero_mem, ?_, ?_, ?_⟩
    · simp
    · simp
    · exact Λ.map_zero
  add_mem' := by
    rintro left right ⟨hleft, hleftR, hleftQ, hleftΛ⟩
      ⟨hright, hrightR, hrightQ, hrightΛ⟩
    refine ⟨C.response.add_mem hleft hright, ?_, ?_, ?_⟩
    · intro i
      simp [hleftR i, hrightR i]
    · intro j hj
      simp [hleftQ j hj, hrightQ j hj]
    · rw [show witnessValues (left + right) =
          witnessValues left + witnessValues right by rfl,
        map_add, hleftΛ, hrightΛ, add_zero]
  smul_mem' := by
    rintro scalar row ⟨hrow, hrowR, hrowQ, hrowΛ⟩
    refine ⟨C.response.smul_mem scalar hrow, ?_, ?_, ?_⟩
    · intro i
      simp [hrowR i]
    · intro j hj
      simp [hrowQ j hj]
    · rw [show witnessValues (scalar • row) =
          scalar • witnessValues row by rfl, map_smul, hrowΛ, smul_zero]

/-- The two residual mask rows that generate a special linear response pad. -/
structure LinearMaskSource (C : MultiplicativeCode F r w n)
    (Q : Finset (Fin n)) (Λ : (Fin w → F) →ₗ[F] F) where
  vCoefficient : baseQueryKernel C Q
  zRCoefficient : linearZRCoefficientKernel C Q Λ
  deriving DecidableEq

namespace LinearMaskSource

variable {C : MultiplicativeCode F r w n} {Q : Finset (Fin n)}
variable {Λ : (Fin w → F) →ₗ[F] F}

def prodEquiv : LinearMaskSource C Q Λ ≃
    baseQueryKernel C Q × linearZRCoefficientKernel C Q Λ where
  toFun masks := (masks.vCoefficient, masks.zRCoefficient)
  invFun masks := ⟨masks.1, masks.2⟩
  left_inv masks := by cases masks; rfl
  right_inv masks := by cases masks; rfl

noncomputable instance : Fintype (LinearMaskSource C Q Λ) :=
  Fintype.ofEquiv
    (baseQueryKernel C Q × linearZRCoefficientKernel C Q Λ) prodEquiv.symm

instance : Zero (LinearMaskSource C Q Λ) := ⟨⟨0, 0⟩⟩
instance : Add (LinearMaskSource C Q Λ) :=
  ⟨fun left right ↦ ⟨left.vCoefficient + right.vCoefficient,
    left.zRCoefficient + right.zRCoefficient⟩⟩
instance : Neg (LinearMaskSource C Q Λ) :=
  ⟨fun masks ↦ ⟨-masks.vCoefficient, -masks.zRCoefficient⟩⟩
instance : Sub (LinearMaskSource C Q Λ) :=
  ⟨fun left right ↦ ⟨left.vCoefficient - right.vCoefficient,
    left.zRCoefficient - right.zRCoefficient⟩⟩
instance : SMul ℕ (LinearMaskSource C Q Λ) :=
  ⟨fun scalar masks ↦ ⟨scalar • masks.vCoefficient,
    scalar • masks.zRCoefficient⟩⟩
instance : SMul ℤ (LinearMaskSource C Q Λ) :=
  ⟨fun scalar masks ↦ ⟨scalar • masks.vCoefficient,
    scalar • masks.zRCoefficient⟩⟩

instance : AddCommGroup (LinearMaskSource C Q Λ) :=
  Function.Injective.addCommGroup
    (fun masks ↦ (masks.vCoefficient, masks.zRCoefficient))
    (by intro left right h; cases left; cases right; cases h; rfl)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem add_vCoefficient (left right : LinearMaskSource C Q Λ) :
    (left + right).vCoefficient = left.vCoefficient + right.vCoefficient := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem add_zRCoefficient (left right : LinearMaskSource C Q Λ) :
    (left + right).zRCoefficient =
      left.zRCoefficient + right.zRCoefficient := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem neg_vCoefficient (masks : LinearMaskSource C Q Λ) :
    (-masks).vCoefficient = -masks.vCoefficient := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem neg_zRCoefficient (masks : LinearMaskSource C Q Λ) :
    (-masks).zRCoefficient = -masks.zRCoefficient := rfl

end LinearMaskSource

noncomputable def linearMaskMap
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : Finset (Fin n)) (Λ : (Fin w → F) →ₗ[F] F) :
    LinearMaskSource C Q Λ → linearResponseKernel C Q Λ :=
  fun masks ↦ ⟨rowMul M.vanishing masks.vCoefficient.1 +
      rowMul C.zR masks.zRCoefficient.1, by
    refine ⟨C.response.add_mem (M.vanishing_mul_mem masks.vCoefficient.2.1)
      (C.mul_mem C.zR_mem masks.zRCoefficient.2.1), ?_, ?_, ?_⟩
    · intro i
      change M.vanishing (randomPosition i) *
          masks.vCoefficient.1 (randomPosition i) +
        C.zR (randomPosition i) *
          masks.zRCoefficient.1 (randomPosition i) = 0
      rw [show M.vanishing (randomPosition i) = 0 from
        M.vanishing_message (Sum.inl i), C.zR_random i]
      simp
    · intro j hj
      simp [rowMul, masks.vCoefficient.2.2 j hj,
        masks.zRCoefficient.2.2.1 j hj]
    · have hwitness : witnessValues
          (rowMul M.vanishing masks.vCoefficient.1 +
            rowMul C.zR masks.zRCoefficient.1) =
            witnessValues masks.zRCoefficient.1 := by
        funext i
        change M.vanishing (witnessPosition i) *
            masks.vCoefficient.1 (witnessPosition i) +
          C.zR (witnessPosition i) *
              masks.zRCoefficient.1 (witnessPosition i) =
            masks.zRCoefficient.1 (witnessPosition i)
        rw [show M.vanishing (witnessPosition i) = 0 from
          M.vanishing_message (Sum.inr i), C.zR_witness i]
        simp
      rw [hwitness, masks.zRCoefficient.2.2.2]⟩

omit [Fintype F] [DecidableEq F] in
theorem linearMaskMap_surjective
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : Finset (Fin n)) (hQ : Q.card = r)
    (J : Finset (Fin n)) (hJ : J.card = C.k)
    (Λ : (Fin w → F) →ₗ[F] F) :
    Function.Surjective (linearMaskMap C M Q Λ) := by
  intro response
  obtain ⟨first, second, hfirst, hsecond, hsecondΛ,
      hfirstQ, hsecondQ, heq⟩ :=
    MultiplicativeCode.linear_mask_surjective C M Q hQ J hJ Λ response.1
      response.2.1 response.2.2.1 response.2.2.2.2 response.2.2.2.1
  refine ⟨LinearMaskSource.mk
    ⟨first, hfirst, hfirstQ⟩ ⟨second, hsecond, hsecondQ, hsecondΛ⟩, ?_⟩
  apply Subtype.ext
  exact heq.symm

/-- Every admissible special linear-response difference is an exact one-time
pad after conditioning on the opened mask values and the permitted witness
functional. -/
theorem linear_response_perfectly_masked
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (Q : Finset (Fin n)) (hQ : Q.card = r)
    (J : Finset (Fin n)) (hJ : J.card = C.k)
    (Λ : (Fin w → F) →ₗ[F] F)
    (secret : linearResponseKernel C Q Λ) :
    SameDistribution
      (fun masks ↦ secret + linearMaskMap C M Q Λ masks)
      (linearMaskMap C M Q Λ) := by
  classical
  apply surjective_additive_map_one_time_pad
  · intro first second
    apply Subtype.ext
    funext i
    simp [linearMaskMap, rowMul]
    ring
  · intro source
    apply Subtype.ext
    funext i
    simp [linearMaskMap, rowMul]
    ring
  · exact linearMaskMap_surjective C M Q hQ J hJ Λ

end LigeroFamily
