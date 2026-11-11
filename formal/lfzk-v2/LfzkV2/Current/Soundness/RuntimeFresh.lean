import LfzkV2.Current.StrandReplay
import LfzkV2.Current.StrandComposition
import TranscriptV2.FreshRenaming

/-! Freshness of the exact runtime coordinate transports. No independent
resampling of the accepted path or the commitment cut is introduced. -/
noncomputable section
namespace Survival.RuntimeFresh
open Merkle.RandomOracle TranscriptV2 Bcs.TotalOracle
open scoped Classical

variable {P Q A Out : Type}

theorem mapQueries_fresh (rename : P → Q) (injective : Function.Injective rename)
    {fuel : ℕ} (tree : Tree P A Out fuel) {known : Q → Prop}
    (fresh : FreshOracle.FreshFrom (fun p => known (rename p)) tree) :
    FreshOracle.FreshFrom known (mapQueries rename tree) := by
  induction tree generalizing known with
  | done _ => trivial
  | query point next ih =>
      refine ⟨fresh.1, fun answer => ?_⟩
      apply ih answer
      simpa only [injective.eq_iff] using fresh.2 answer

theorem pad_fresh {D C Extra : Type} [DecidableEq P] {fuel : ℕ}
    (tree : Tree P (D × C) Out fuel) {known : P → Prop}
    (fresh : FreshOracle.FreshFrom known tree) :
    FreshOracle.FreshFrom known (LfzkV2.Current.StrandComposition.pad (Extra := Extra) tree) := by
  induction tree generalizing known with
  | done _ => trivial
  | query point next ih => exact ⟨fresh.1, fun answer => ih _ (fresh.2 (answer.1,answer.2.1))⟩

theorem reindex_fresh {D Raw Challenge Residual : Type} (split : P → Raw ≃ Challenge × Residual)
    (residual : P → Residual) {fuel : ℕ} (tree : Tree P (D × Raw) Out fuel) {known : P → Prop}
    (fresh : FreshOracle.FreshFrom known tree) :
    FreshOracle.FreshFrom known (LfzkV2.Current.StrandSampling.reindex split residual tree) := by
  induction tree generalizing known with
  | done _ => trivial
  | query point next ih => exact ⟨fresh.1, fun answer => ih _ (fresh.2 _ )⟩

theorem replay_search_fresh {T : Type} [DecidableEq P] (schema : Strand.History.Codec T)
    (bytes : P → Framing.Bytes) {fuel : ℕ}
    (program : Tree (StrandCoupling.Point P Strand.PrfKey Strand.Word) Strand.Digest Out fuel) :
    FreshOracle.FreshFrom (fun _ => False) (LfzkV2.Current.StrandReplay.search schema bytes program) :=
  (LfzkV2.Current.StrandSearch.searchState_fresh schema bytes (recordTrace program)
    StrandCoupling.Cache.empty []).mono (fun _ impossible => impossible.elim)

end Survival.RuntimeFresh
