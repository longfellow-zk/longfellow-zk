import LfzkV1.LigeroZk.ResponseAdaptiveView

/-! Transport a fixed-query tape equivalence through a response-selected
query. This specializes the existing response-adaptive permutation lemma
to a fixed public context and oracle; no verifier randomness is resampled. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend.Adaptive
open LigeroFamily LigeroFamily.ZeroKnowledge

variable {Tape Response Query : Type} [Fintype Tape]

private def selector (choose : Response → Query) :
    ResponseAdaptiveVerifier Unit Unit Response Query where
  challenge _ := ()
  query _ := choose

/-- Response preservation lets the original adaptive-tape theorem recover
the chosen query from the translated tape, proving a genuine permutation. -/
def selectionEquiv (sourceResponse targetResponse : Tape → Response)
    (choose : Response → Query) (translate : Query → Tape ≃ Tape)
    (preserved : ∀ query tape, targetResponse (translate query tape) = sourceResponse tape) :
    Tape ≃ Tape :=
  ((Equiv.prodUnique Tape Unit).symm.trans
    (responseAdaptiveTapeTranslateEquiv (selector choose)
      (fun tape _ => sourceResponse tape) (fun tape _ => targetResponse tape)
      (fun query _ tape => translate query tape)
      (fun query _ tape => preserved query tape)
      (fun query _ => (translate query).injective))).trans (Equiv.prodUnique Tape Unit)

theorem selectionEquiv_apply (sourceResponse targetResponse : Tape → Response)
    (choose : Response → Query) (translate : Query → Tape ≃ Tape)
    (preserved : ∀ query tape, targetResponse (translate query tape) = sourceResponse tape)
    (tape : Tape) :
    selectionEquiv sourceResponse targetResponse choose translate preserved tape =
      translate (choose (sourceResponse tape)) tape := rfl

end LfzkV2.Current.ZeroKnowledge.Backend.Adaptive
