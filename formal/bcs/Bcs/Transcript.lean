import Bcs.Compiled

/-!
# The compiled transcript, and what does not depend on the coins

A compiled adversary is run *once*, lazily, against one answer tape; the verifier's coins are
external and arrive between its stages.  For the reduction to produce an `IPCPProver` — whose
`commit` is a function of nothing and whose `respond` is a function of the challenge alone — two
projections of that single execution must be shown independent of the coins drawn after them:

* the **root and the commitment trace** must not depend on the challenge or the query.  Merkle
  already proves this (`commitRun_eq`): the commitment stage's slots are a prefix of the run's, so
  it reads inside the experiment exactly what it would read alone;
* the **response** must not depend on the query.  This is the new one.  It is the same prefix
  argument one stage later, and `lazyRun_run_eq_of_prefix` is stated against an arbitrary slot list
  precisely so that a phase which is not the run's syntactic first `bind` can use it.

Both are proved here as equalities with *coin-free* definitions (`rootOf`, `traceOf`, `responseOf`),
so downstream the coin-independence is visible in the types rather than argued about.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Merkle Merkle.MH Merkle.RandomOracle

namespace Adversary

variable {Enc D Salt M Challenge Response Query Aux Aux' : Type*}
variable {n commitFuel respondFuel revealFuel T : ℕ}
variable [Inhabited D] [DecidableEq Enc]

/-! ## Coin-free projections -/

/-- The root the commitment stage outputs.  A function of the tape alone — the challenge has not
been drawn yet. -/
def rootOf (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel) (answers : Fin T → D) : D :=
  (lazyRun answers default A.commit []).1.1

/-- The commitment stage's query-answer trace: the extractor's only input. -/
def traceOf (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel) (answers : Fin T → D) : List (Enc × D) :=
  (lazyRun answers default A.commit []).2.2

/-- The commit-and-respond prefix of the execution: everything the adversary does before the query
set is drawn. -/
def respondRun (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel) (challenge : Challenge) :
    Tree Enc D (Response × Aux') (respondFuel + commitFuel) :=
  A.commit.bind fun ra ↦ A.respond challenge ra.2

/-- The response the adversary sends.  A function of the tape and the challenge, and of nothing
else; `responseOf_eq` is what earns that. -/
def responseOf (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel) (challenge : Challenge) (answers : Fin T → D) :
    Response :=
  (lazyRun answers default (A.respondRun challenge) []).1.1

/-! ## The prefix arguments -/

variable (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
  n commitFuel respondFuel revealFuel)

/-- The commit-and-respond prefix occupies a prefix of the whole experiment's slots.  Two
applications of `lazyRun_seen_prefix_bind`: `reveal` sits between it and the verifier's check. -/
theorem respondRun_seen_prefix (C : Codec Salt M D Enc)
    (challenge : Challenge) (query : Query) (answers : Fin T → D) :
    (lazyRun answers default (A.respondRun challenge) []).2.1 <+:
      extractionSlots C n commitFuel (revealFuel + respondFuel) T A.commit
        (A.openingStage challenge query) answers := by
  classical
  set base := (lazyRun answers default A.commit []).2.1 with hbase
  set aux := (lazyRun answers default A.commit []).1.2 with haux
  -- the prefix's slots, after the commitment stage
  have hleft : (lazyRun answers default (A.respondRun challenge) []).2.1 =
      (lazyRun answers default (A.respond challenge aux) base).2.1 := by
    rw [respondRun, lazyRun_bind]
  -- the experiment's slots, after the commitment stage
  have hright : extractionSlots C n commitFuel (revealFuel + respondFuel) T A.commit
        (A.openingStage challenge query) answers =
      (lazyRun answers default
        (((A.respond challenge aux).bind fun ra ↦ A.reveal query ra.2).bind
          fun claim ↦ (checkPass C n claim.I claim.a claim.pf (2 * n)
            fun _ ↦ default).map fun _ ↦
              ((lazyRun answers default A.commit []).1.1, claim)) base).2.1 := by
    rw [extractionSlots, runSlots, extractionRun, lazyRun_bind]
    rfl
  rw [hleft, hright]
  exact (lazyRun_seen_prefix_bind answers default _ _ base).trans
    (lazyRun_seen_prefix_bind answers default _ _ base)

/-- **The response does not depend on the query.**  The commit-and-respond prefix reads inside the
experiment exactly what it reads alone. -/
theorem respondRun_run_eq (C : Codec Salt M D Enc)
    (challenge : Challenge) (query : Query) (answers : Fin T → D) :
    (A.respondRun challenge).run
        (extractionOracle C n commitFuel (revealFuel + respondFuel) T A.commit
          (A.openingStage challenge query) answers) =
      ((lazyRun answers default (A.respondRun challenge) []).1,
        (lazyRun answers default (A.respondRun challenge) []).2.2) :=
  lazyRun_run_eq_of_prefix answers default (A.respondRun challenge) [] _ _
    (fun _ ↦ rfl) (A.respondRun_seen_prefix C challenge query answers)

/-- **Faithfulness of `responseOf`.**  What the respond stage outputs inside the experiment, resumed
from the commitment stage's own private state, is `responseOf`. -/
theorem responseOf_eq (C : Codec Salt M D Enc)
    (challenge : Challenge) (query : Query) (answers : Fin T → D) :
    ((A.respond challenge
          ((A.commit.run (extractionOracle C n commitFuel (revealFuel + respondFuel) T A.commit
            (A.openingStage challenge query) answers)).1.2)).run
        (extractionOracle C n commitFuel (revealFuel + respondFuel) T A.commit
          (A.openingStage challenge query) answers)).1.1 =
      A.responseOf challenge answers := by
  have hrun := A.respondRun_run_eq C challenge query answers
  rw [respondRun, Tree.run_bind] at hrun
  rw [responseOf, respondRun]
  exact congrArg (fun p ↦ p.1.1) hrun

/-! ## The commitment stage, restated -/

/-- The root of the experiment is the coin-free `rootOf`. -/
theorem commitRoot_eq (C : Codec Salt M D Enc)
    (challenge : Challenge) (query : Query) (answers : Fin T → D) :
    commitRoot C n commitFuel (revealFuel + respondFuel) T A.commit
        (A.openingStage challenge query) answers = A.rootOf answers := by
  rw [commitRoot, commitRun_eq, rootOf]

/-- The trace handed to the extractor is the coin-free `traceOf`. -/
theorem commitTrace_eq' (C : Codec Salt M D Enc)
    (challenge : Challenge) (query : Query) (answers : Fin T → D) :
    commitTrace C n commitFuel (revealFuel + respondFuel) T A.commit
        (A.openingStage challenge query) answers = A.traceOf answers := by
  rw [commitTrace_eq, traceOf]

end Adversary

end Bcs
