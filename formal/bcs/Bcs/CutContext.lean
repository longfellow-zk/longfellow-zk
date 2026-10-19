import Bcs.TwoPointContext

/-! A cut context is constant on a whole fiber of commitment-naming inputs. -/
namespace Bcs.TotalOracle
open Finset
open scoped Classical
variable {Q C A : Type} [DecidableEq Q]

theorem invariant_finset (f : (Q → C) → A) (s : Finset Q)
    (hs : ∀ q ∈ s, ∀ H H', AgreeOff q H H' → f H = f H')
    (H H' : Q → C) (ho : ∀ q, q ∉ s → H q = H' q) : f H = f H' := by
  induction s using Finset.induction_on generalizing H H' with
  | empty => congr 1; funext q; exact ho q (by simp)
  | @insert q s hq ih =>
    let mid := Function.update H q (H' q)
    have hm : f H = f mid := hs q (mem_insert_self _ _) _ _ (agreeOff_update _ _ _)
    refine hm.trans (ih (fun x hx => hs x (mem_insert_of_mem hx)) mid H' ?_)
    intro x hx
    by_cases he : x = q
    · subst x; simp [mid]
    · simpa [mid,he] using ho x (by simp [hx,he])

end Bcs.TotalOracle

namespace Bcs.TotalOracleCommit.Setup
open Bcs.TotalOracle Finset
open scoped Classical
variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D]
  [DecidableEq Pt] [DecidableEq Key] {tA N L TM : ℕ}

theorem ctxAt_off_finset (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N L)
    (mt : Fin TM → D) (k : Key) (s : Finset Pt)
    (hk : ∀ x ∈ s, S.key x = k) (H H' : Pt → C)
    (ho : ∀ x, x ∉ s → H x = H' x) :
    (S.atOracle H).ctxAt mt emptyTape k = (S.atOracle H').ctxAt mt emptyTape k := by
  apply invariant_finset (fun G => (S.atOracle G).ctxAt mt emptyTape k) s _ H H' ho
  intro x hx A B hab
  have h := S.ctxAt_off mt A B x hab
  rw [hk x hx] at h
  exact h.symm

end Bcs.TotalOracleCommit.Setup
