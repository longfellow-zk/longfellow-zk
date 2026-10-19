import polygero.Benchmarks.FSStoppedSpectrum
import polygero.Benchmarks.FSIntegerAffine
import polygero.Recursion.FSStoppedCharges

/-! Actual stopped parent-query certificates with the full six-response
low baseline. Both rows keep 81 parent and 80 child openings. The second
lowers only the parent's decoding cutoff, leaving the verifier unchanged.
These certificates cover the first two hash roles; child and terminal
roles remain to be composed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RecursivePolygero.Benchmarks.FSBaselinePrice

open ProfileAnalysis ProfileAnalysis.StoppedSpectrum
open FiatShamir FiatShamir.TwoLevel Bcs.AffineBlock
open scoped Classical

inductive Schedule | unchanged | lowerCut

def row : Schedule → FSTwoLevel.Row
  | .unchanged => ⟨81,2714,6,125,2⟩
  | .lowerCut => ⟨81,2655,7,125,2⟩

def coefficient : Schedule → ℚ
  | .unchanged => 553/100
  | .lowerCut => 543/100

def rate (s : Schedule) : ℚ := coefficient s / FSTwoLevel.fieldSize

def baseline (s : Schedule) : ℚ := 6 * FSStoppedSpectrum.theta 81 (row s).cutoff

def shifted (s : Schedule) : ℚ := rate s - baseline s

def tailCut : Fin 7 → ℕ := ![2714,2847,2917,3007,3370,4416,8193]
def level (i : ℕ) : ℚ := FSStoppedSpectrum.theta 81 (tailCut ⟨min i 6, by omega⟩)
def tailBound (i : ℕ) : ℕ := 6-i

private theorem theta_mono (queries : ℕ) : Monotone (FSStoppedSpectrum.theta queries) := by
  intro a b hab
  unfold FSStoppedSpectrum.theta
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_choose queries (Nat.sub_le_sub_right hab 1)

private theorem level_mono : Monotone level := by
  have hm : Monotone tailCut := by decide +kernel
  intro i j hij
  apply theta_mono 81
  apply hm
  exact min_le_min hij le_rfl

private theorem theta_final : FSStoppedSpectrum.theta 81 8193 = 1 := by
  unfold FSStoppedSpectrum.theta
  norm_num only [Nat.reduceSub]
  exact div_self (ne_of_gt (by exact_mod_cast Nat.choose_pos (show 81 ≤ 8192 by decide)))

noncomputable def tailPrice (L : ℕ) (r : ℚ) : ℚ :=
  ((L : ℚ)-6) * price r (FSStoppedSpectrum.theta 81 2714) +
    FSStoppedSpectrum.moment 81 FSStoppedSpectrum.cuts81Fixed r

/-- All comparisons include the full six-response baseline and rank
error, and use ordinary exact kernel arithmetic. -/
theorem checked (s : Schedule) :
    FSIntegerAffine.rowOk (row s) 2 ∧
    0 ≤ rate s ∧ baseline s < rate s ∧
    FSTwoLevel.rankError + tailPrice (row s).list (shifted s) /
      FSTwoLevel.fieldSize ≤ rate s := by
  cases s <;>
    simp only [FSIntegerAffine.rowOk, row, rate, coefficient, baseline, shifted,
      tailPrice, FSStoppedSpectrum.moment, FSStoppedSpectrum.cuts81Fixed,
      FSStoppedSpectrum.theta, price, FSTwoLevel.theta,
      FSTwoLevel.rankError, FSTwoLevel.fieldSize, DiscreteThreshold.candidate,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.choose_eq_fast_choose] <;>
    decide +kernel

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Tail assembly at every nonnegative stopped price. The six- and
seven-system rows reuse the same actual integer-occupancy tails. -/
theorem actual_spectrum_le (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (r : ℚ) (hr : 0 < r)
    (hn : I.n = 8192) (ht : I.t = 81) (hover : p.overlapSize = 639)
    (hsmall : p.listBound < Nat.card F) :
    spectrum I p W r ≤ tailPrice p.listBound r := by
  have hnonneg : 0 ≤ level 0 := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hlast : 1 ≤ level 6 := by
    change 1 ≤ FSStoppedSpectrum.theta 81 8193
    rw [theta_final]
  have ht' (i : ℕ) (hi : i ∈ Finset.range 6) :
      ((highSystems I p W).filter
        (fun d => level i < systemCap I W d)).card ≤ tailBound i := by
    have hip : i < 6 := Finset.mem_range.mp hi
    interval_cases i
    · change ((highSystems I p W).filter
        (fun d => FSStoppedSpectrum.theta 81 2714 < systemCap I W d)).card ≤ 6
      exact FSStoppedSpectrum.actual_tail_card I p W 81 2714 6 hn ht hover
        (by norm_num [FSStoppedSpectrum.tailData81])
    · change ((highSystems I p W).filter
        (fun d => FSStoppedSpectrum.theta 81 2847 < systemCap I W d)).card ≤ 5
      exact FSStoppedSpectrum.actual_tail_card I p W 81 2847 5 hn ht hover
        (by norm_num [FSStoppedSpectrum.tailData81])
    · change ((highSystems I p W).filter
        (fun d => FSStoppedSpectrum.theta 81 2917 < systemCap I W d)).card ≤ 4
      exact FSStoppedSpectrum.actual_tail_card I p W 81 2917 4 hn ht hover
        (by norm_num [FSStoppedSpectrum.tailData81])
    · change ((highSystems I p W).filter
        (fun d => FSStoppedSpectrum.theta 81 3007 < systemCap I W d)).card ≤ 3
      exact FSStoppedSpectrum.actual_tail_card I p W 81 3007 3 hn ht hover
        (by norm_num [FSStoppedSpectrum.tailData81])
    · change ((highSystems I p W).filter
        (fun d => FSStoppedSpectrum.theta 81 3370 < systemCap I W d)).card ≤ 2
      exact FSStoppedSpectrum.actual_tail_card I p W 81 3370 2 hn ht hover
        (by norm_num [FSStoppedSpectrum.tailData81])
    · change ((highSystems I p W).filter
        (fun d => FSStoppedSpectrum.theta 81 4416 < systemCap I W d)).card ≤ 1
      exact FSStoppedSpectrum.actual_tail_card I p W 81 4416 1 hn ht hover
        (by norm_num [FSStoppedSpectrum.tailData81])
  have hmain := spectrum_layers_le I p hsmall W r hr
    level level_mono hnonneg 6 hlast tailBound ht'
  have heq : (p.listBound : ℚ) * price r (level 0) +
      (∑ i ∈ Finset.range 6, (price r (level (i+1)) -
        price r (level i)) * tailBound i) = tailPrice p.listBound r := by
    have h0 : level 0 = FSStoppedSpectrum.theta 81 2714 := rfl
    have h1 : level 1 = FSStoppedSpectrum.theta 81 2847 := rfl
    have h2 : level 2 = FSStoppedSpectrum.theta 81 2917 := rfl
    have h3 : level 3 = FSStoppedSpectrum.theta 81 3007 := rfl
    have h4 : level 4 = FSStoppedSpectrum.theta 81 3370 := rfl
    have h5 : level 5 = FSStoppedSpectrum.theta 81 4416 := rfl
    have h6 : level 6 = 1 := theta_final
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4,
      h5, h6, tailBound, Nat.reduceSub, tailPrice,
      FSStoppedSpectrum.moment, FSStoppedSpectrum.cuts81Fixed,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  rw [heq] at hmain
  exact hmain

/-- The exact capacity-spectrum premise for the first-two-role compiler,
including the recursive list-six baseline. -/
theorem actual_spectrum_premise (s : Schedule) (I : Instance F)
    (p : HahnSystemCertificate I) (W : I.layer.Oracle)
    (hn : I.n = 8192) (ht : I.t = 81) (hover : p.overlapSize = 639)
    (hlist : p.listBound = (row s).list) (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 (row s).cutoff)
    (hmu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    p.toProfileParameters.rankError +
      spectrum I p W (rate s - 6*p.threshold) / Nat.card F ≤ rate s := by
  have hshift : rate s - 6*p.threshold = shifted s := by
    rw [htheta]; rfl
  have hs := actual_spectrum_le I p W (shifted s)
    (sub_pos.mpr (checked s).2.2.1) hn ht hover hsmall
  rw [hlist] at hs
  rw [hshift, hmu, hq]
  exact (add_le_add le_rfl (div_le_div_of_nonneg_right hs (by positivity))).trans
    (checked s).2.2.2

/-- Arbitrary-order actual local-domain certificates at 5.53/q and
5.43/q, with no dropped low-response or rank term. -/
theorem query_oracle_sound (s : Schedule) {I : Instance F} (child : Child I)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (hcp : cp.listBound < Nat.card F) (hcList : cp.listBound = 6)
    (σ : I.layer.Statement)
    (hn : I.n = 8192) (ht : I.t = 81) (hover : p.overlapSize = 639)
    (hlist : p.listBound = (row s).list) (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = FSStoppedSpectrum.theta 81 (row s).cutoff)
    (hmu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    OracleSound (queryBlockDomain child)
      (fun d : Proof child => queryCapacityEvent child cp σ (query d.1 d.2.1))
      ⟨2*rate s, rate s, mul_nonneg (by norm_num) (checked s).2.1, (checked s).2.1⟩ := by
  apply query_stopped_oracle_sound_of_spectrum child p cp hcp σ (rate s)
  · rw [hcList, htheta]
    exact (checked s).2.2.1
  · intro W
    rw [hcList]
    exact actual_spectrum_premise s I p W hn ht hover hlist hsmall htheta hmu hq

end RecursivePolygero.Benchmarks.FSBaselinePrice
