import LigeroFamily.Protocol.DirectProduct

/-! Finite response spaces for the ordinary and direct-product verifiers. -/
namespace LigeroFamily
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

private def responseFintypeEquiv {r w repetitions : ℕ} :
    ((Fin repetitions → EvaluationRow F r w n) ×
      (Fin repetitions → EvaluationRow F r w n) ×
      (Fin repetitions → EvaluationRow F r w n)) ≃
        Response F r w n repetitions where
  toFun value := ⟨value.1, value.2.1, value.2.2⟩
  invFun response := (response.proximity, response.linear, response.quadratic)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance responseFintype {r w repetitions : ℕ} :
    Fintype (Response F r w n repetitions) :=
  letI : Fintype (Fin repetitions → EvaluationRow F r w n) := inferInstance
  Fintype.ofEquiv _ responseFintypeEquiv

private def directResponseFintypeEquiv {r w repetitions : ℕ} :
    ((Fin repetitions → EvaluationRow F r w n) ×
      (Fin repetitions → EvaluationRow F r w n)) ≃
        DirectResponse F r w n repetitions where
  toFun value := ⟨value.1, value.2⟩
  invFun response := (response.proximity, response.linear)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance directResponseFintype {r w repetitions : ℕ} :
    Fintype (DirectResponse F r w n repetitions) :=
  letI : Fintype (Fin repetitions → EvaluationRow F r w n) := inferInstance
  Fintype.ofEquiv _ directResponseFintypeEquiv

end LigeroFamily
