import LfzkV2.Current.ZeroKnowledge.Observer

/-! A full observer view contains its adaptive public request, proof and
both mixed traces. The prover/compiler may return prepared or refreshed
oracles. Every later observer call uses those returned functions; neither
original oracle table is retained as public advice. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Observer
open Merkle.RandomOracle

variable {QM AM QT AT Request Proof Out : Type}
variable {preM preT postM postT : ℕ}

structure View (QM AM QT AT Request Proof Out : Type) where
  request : Request
  proof : Proof
  before : List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))
  output : Out
  after : List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))

variable (prior : TwoOracleTree QM AM QT AT Request preM preT)
variable (prove : Request → (QM → AM) → (QT → AT) → Proof × ((QM → AM) × (QT → AT)))
variable (after : Request → Proof → TwoOracleTree QM AM QT AT Out postM postT)

/-- The pre-proof observer may query either oracle before choosing Request.
After the prover returns, all calls use its resulting pair of oracle tables.
Only queried coordinates, not those tables, occur in the returned view. -/
def experiment (HM : QM → AM) (HT : QT → AT) : View QM AM QT AT Request Proof Out :=
  let before := run HM HT prior
  let result := prove before.1 HM HT
  let later := run result.2.1 result.2.2 (after before.1 result.1)
  ⟨before.1,result.1,before.2,later.1,later.2⟩

/-- The Merkle-side hybrid conditions on the transcript oracle currently
used in each phase. In particular its post-proof residual uses the refreshed
transcript table returned by the prover, never the original one. -/
def merkleConditioned (HM : QM → AM) (HT : QT → AT) : View QM AM QT AT Request Proof Out :=
  let before := ((fixTranscript HT prior).run HM).1
  let result := prove before.1 HM HT
  let later := ((fixTranscript result.2.2 (after before.1 result.1)).run result.2.1).1
  ⟨before.1,result.1,before.2,later.1,later.2⟩

/-- The opening-refresh hybrid conditions on the Merkle oracle currently
used in each phase. Its post-proof residual uses the resulting prepared
Merkle table, rather than resetting or forgetting the prior table. -/
def transcriptConditioned (HM : QM → AM) (HT : QT → AT) : View QM AM QT AT Request Proof Out :=
  let before := ((fixMerkle HM prior).run HT).1
  let result := prove before.1 HM HT
  let later := ((fixMerkle result.2.1 (after before.1 result.1)).run result.2.2).1
  ⟨before.1,result.1,before.2,later.1,later.2⟩

theorem experiment_merkleConditioned (HM : QM → AM) (HT : QT → AT) :
    experiment prior prove after HM HT = merkleConditioned prior prove after HM HT := by
  simp only [experiment,merkleConditioned,fixTranscript_run]

theorem experiment_transcriptConditioned (HM : QM → AM) (HT : QT → AT) :
    experiment prior prove after HM HT = transcriptConditioned prior prove after HM HT := by
  simp only [experiment,transcriptConditioned,fixMerkle_run]

theorem full_conditionings_agree (HM : QM → AM) (HT : QT → AT) :
    merkleConditioned prior prove after HM HT = transcriptConditioned prior prove after HM HT :=
  (experiment_merkleConditioned prior prove after HM HT).symm.trans
    (experiment_transcriptConditioned prior prove after HM HT)

end LfzkV2.Current.ZeroKnowledge.Observer
