import polygero.Local.StoppedSpectrum
import polygero.Benchmarks.FSTwoLevel
import polygero.Algebra.Counting.IntegerOccupancy

/-! Exact numerical certificates for the exposed-parent stopping model.
These are capacity-spectrum moments, not arbitrary-order ROM FS bounds.
The latter additionally need a query-order bridge and all other failure
roles. The cutoffs are the integer-occupancy tail breakpoints. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace RecursivePolygero.Benchmarks.FSStoppedSpectrum

open ProfileAnalysis.StoppedSpectrum

def theta (queries cutoff : ℕ) : ℚ :=
  (Nat.choose (cutoff-1) queries : ℚ) / Nat.choose 8192 queries

/-- When successive tail list bounds fall by one, discrete layer-cake
summation gives one price at each subsequent cutoff, and one at capacity
one. The initial list bound is `cuts.length + 1`. -/
noncomputable def moment (queries : ℕ) (cuts : List ℕ) (rate : ℚ) : ℚ :=
  (cuts.map (fun a => price rate (theta queries a))).sum + price rate 1

def cuts75 : List ℕ := [2502,2534,2537,2555,2597,2644,2655,2714,2847,2917,3007,3370,4416]
def cuts81 : List ℕ := [2714,2847,2917,3007,3370,4416]
def cuts81Fixed : List ℕ := [2847,2917,3007,3370,4416]
def cuts80 : List ℕ := [2714,2847,2917,3007,3370,4416]

def rate75 : ℚ := (861/100) / FSTwoLevel.fieldSize
def rate81 : ℚ := (541/100) / FSTwoLevel.fieldSize
def rate80 : ℚ := (581/100) / FSTwoLevel.fieldSize


/-- Safe rational coefficients: 8.61 field units for 75 openings, 5.41
for 81 openings, and 5.81 for 80 openings. All comparisons are ordinary
kernel reductions, including the exact binomial capacity fractions. -/
theorem checked :
    moment 75 cuts75 rate75 ≤ (861/100 : ℚ) ∧
    moment 81 cuts81 rate81 ≤ (541/100 : ℚ) ∧
    moment 81 cuts81Fixed rate81 ≤ (541/100 : ℚ) ∧
    moment 80 cuts80 rate80 ≤ (581/100 : ℚ) := by
  simp only [moment, cuts75, cuts81, cuts81Fixed, cuts80, rate75, rate81, rate80,
    theta, price, FSTwoLevel.fieldSize, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.choose_eq_fast_choose]
  decide +kernel

def tailData75 : List (ℕ × ℕ) :=
  [(2487,14),(2502,13),(2534,12),(2537,11),(2555,10),(2597,9),(2644,8),
    (2655,7),(2714,6),(2847,5),(2917,4),(3007,3),(3370,2),(4416,1)]
def tailData81 : List (ℕ × ℕ) :=
  [(2660,7),(2714,6),(2847,5),(2917,4),(3007,3),(3370,2),(4416,1)]
def tailData80 : List (ℕ × ℕ) :=
  [(2713,7),(2714,6),(2847,5),(2917,4),(3007,3),(3370,2),(4416,1)]

def tailGap (a L : ℕ) : Prop :=
  let h := (L+1)*a/8192
  (L+1 : ℤ) * L * 639 + 8192 * h * (h+1) < 2 * h * (L+1) * a

/-- Every tail cutoff used by the moments has an actual combinatorial
uniform-list certificate. This checks the arithmetic at all cutoffs,
not just the scalar moment comparisons. -/
theorem checked_tail_gaps :
    (∀ a L, (a,L) ∈ tailData75 → tailGap a L) ∧
    (∀ a L, (a,L) ∈ tailData81 → tailGap a L) ∧
    (∀ a L, (a,L) ∈ tailData80 → tailGap a L) := by
  simp only [tailData75, tailData81, tailData80, List.mem_cons, List.not_mem_nil,
    Prod.mk.injEq, or_false]
  aesop (add simp [tailGap])

theorem tail_uniformFamilyBound (a L : ℕ)
    (h : (a,L) ∈ tailData75 ∨ (a,L) ∈ tailData81 ∨ (a,L) ∈ tailData80) :
    CodingTheory.UniformFamilyBound 8192 a 639 L := by
  apply CodingTheory.IntegerOccupancy.uniformFamilyBound
    (h := (L+1)*a/8192)
  rcases h with h | h | h
  · exact checked_tail_gaps.1 a L h
  · exact checked_tail_gaps.2.1 a L h
  · exact checked_tail_gaps.2.2 a L h

private theorem tail_cutoff_pos (a L : ℕ)
    (h : (a,L) ∈ tailData75 ∨ (a,L) ∈ tailData81 ∨ (a,L) ∈ tailData80) : 639 < a := by
  simp only [tailData75, tailData81, tailData80, List.mem_cons, List.not_mem_nil,
    Prod.mk.injEq, or_false] at h
  omega

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The numerical tail certificates apply to actual Polygero reduced
systems, including proper systems. -/
theorem actual_tail_card (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (queries a L : ℕ) (hn : I.n = 8192) (ht : I.t = queries)
    (hover : p.overlapSize = 639)
    (hmem : (a,L) ∈ tailData75 ∨ (a,L) ∈ tailData81 ∨ (a,L) ∈ tailData80) :
    ((ProfileAnalysis.highSystems I p W).filter
      (fun d => theta queries a < ProfileAnalysis.systemCap I W d)).card ≤ L := by
  apply systemCap_tail_card_le_of_uniformFamilyBound I p W _ a L
  · rw [hover]
    exact tail_cutoff_pos a L hmem
  · rw [hn, hover]
    exact tail_uniformFamilyBound a L hmem
  · intro d hd
    have h := (Finset.mem_filter.mp hd).2
    simpa only [theta, hn, ht] using h

def fixedCut : Fin 6 → ℕ := ![2847,2917,3007,3370,4416,8193]
def fixedLevel (i : ℕ) : ℚ := theta 81 (fixedCut ⟨min i 5, by omega⟩)
def fixedBound (i : ℕ) : ℕ := 5-i

private theorem theta_mono (queries : ℕ) : Monotone (theta queries) := by
  intro a b hab
  unfold theta
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_choose queries (Nat.sub_le_sub_right hab 1)

private theorem fixedLevel_mono : Monotone fixedLevel := by
  have hm : Monotone fixedCut := by decide +kernel
  intro i j hij
  apply theta_mono 81
  apply hm
  exact min_le_min hij le_rfl

private theorem theta_final : theta 81 8193 = 1 := by
  unfold theta
  norm_num only [Nat.reduceSub]
  exact div_self (ne_of_gt (by exact_mod_cast Nat.choose_pos (show 81 ≤ 8192 by decide)))

set_option maxHeartbeats 1000000 in
/-- Fully assembled local spectrum for the actual fixed 81-opening
instance, with integer-occupancy list six. The reverse-order ROM bridge
and other failure roles are deliberately absent from this local theorem. -/
theorem fixed81_spectrum_le (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (hn : I.n = 8192) (ht : I.t = 81) (hover : p.overlapSize = 639)
    (hlist : p.listBound = 6) (hsmall : p.listBound < Nat.card F) :
    spectrum I p W rate81 ≤ (541/100 : ℚ) := by
  have hnonneg : 0 ≤ fixedLevel 0 := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hlast : 1 ≤ fixedLevel 5 := by
    change 1 ≤ theta 81 8193
    rw [theta_final]
  have ht' (i : ℕ) (hi : i ∈ Finset.range 5) :
      ((ProfileAnalysis.highSystems I p W).filter
        (fun d => fixedLevel i < ProfileAnalysis.systemCap I W d)).card ≤ fixedBound i := by
    have hip : i < 5 := Finset.mem_range.mp hi
    interval_cases i
    · change ((ProfileAnalysis.highSystems I p W).filter
        (fun d => theta 81 2847 < ProfileAnalysis.systemCap I W d)).card ≤ 5
      exact actual_tail_card I p W 81 2847 5 hn ht hover (by norm_num [tailData81])
    · change ((ProfileAnalysis.highSystems I p W).filter
        (fun d => theta 81 2917 < ProfileAnalysis.systemCap I W d)).card ≤ 4
      exact actual_tail_card I p W 81 2917 4 hn ht hover (by norm_num [tailData81])
    · change ((ProfileAnalysis.highSystems I p W).filter
        (fun d => theta 81 3007 < ProfileAnalysis.systemCap I W d)).card ≤ 3
      exact actual_tail_card I p W 81 3007 3 hn ht hover (by norm_num [tailData81])
    · change ((ProfileAnalysis.highSystems I p W).filter
        (fun d => theta 81 3370 < ProfileAnalysis.systemCap I W d)).card ≤ 2
      exact actual_tail_card I p W 81 3370 2 hn ht hover (by norm_num [tailData81])
    · change ((ProfileAnalysis.highSystems I p W).filter
        (fun d => theta 81 4416 < ProfileAnalysis.systemCap I W d)).card ≤ 1
      exact actual_tail_card I p W 81 4416 1 hn ht hover (by norm_num [tailData81])
  have hmain := spectrum_layers_le I p hsmall W rate81 (by norm_num [rate81, FSTwoLevel.fieldSize])
    fixedLevel fixedLevel_mono hnonneg 5 hlast fixedBound ht'
  rw [hlist] at hmain
  have heq : ((6 : ℕ) : ℚ) * price rate81 (fixedLevel 0) +
      (∑ i ∈ Finset.range 5, (price rate81 (fixedLevel (i+1)) -
        price rate81 (fixedLevel i)) * fixedBound i) = moment 81 cuts81Fixed rate81 := by
    have h0 : fixedLevel 0 = theta 81 2847 := rfl
    have h1 : fixedLevel 1 = theta 81 2917 := rfl
    have h2 : fixedLevel 2 = theta 81 3007 := rfl
    have h3 : fixedLevel 3 = theta 81 3370 := rfl
    have h4 : fixedLevel 4 = theta 81 4416 := rfl
    have h5 : fixedLevel 5 = 1 := theta_final
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5,
      fixedBound, Nat.reduceSub, moment, cuts81Fixed, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    ring
  rw [heq] at hmain
  exact hmain.trans checked.2.2.1

private theorem rank_le_fixed_baseline : FSTwoLevel.rankError ≤ theta 81 2714 := by
  simp only [FSTwoLevel.rankError, FSTwoLevel.fieldSize, theta, Nat.choose_eq_fast_choose]
  decide +kernel

/-- Actual local fresh-parent mean including the threshold baseline and
rank failure. The rate is `(5.41/q) + theta_81(2714)`, about `5.612/q`.
This remains a local stopping-model theorem, not an arbitrary-order ROM
FS theorem. -/
theorem fixed81_parent_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (hn : I.n = 8192) (ht : I.t = 81) (hover : p.overlapSize = 639)
    (hlist : p.listBound = 6) (hsmall : p.listBound < Nat.card F)
    (htheta : p.threshold = theta 81 2714)
    (hmu : p.toProfileParameters.rankError = FSTwoLevel.rankError)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    mean (fun coin => Bcs.StoppedPotential.repeatPrice (rate81+p.threshold)
      (conditionalCapacity I p sigma W p.threshold coin)) ≤ rate81+p.threshold := by
  have hr : 0 < rate81 := by norm_num [rate81, FSTwoLevel.fieldSize]
  have hb := conditionalCapacity_repeatPrice_mean_le I p sigma W
    (rate81+p.threshold) p.threshold p.threshold_nonneg (by linarith)
  have he : rate81 + p.threshold - p.threshold = rate81 := by ring
  rw [he, hq, hmu] at hb
  have hs := fixed81_spectrum_le I p W hn ht hover hlist hsmall
  have hm : FSTwoLevel.rankError ≤ p.threshold := by rw [htheta]; exact rank_le_fixed_baseline
  calc
    _ ≤ FSTwoLevel.rankError + spectrum I p W rate81 / FSTwoLevel.fieldSize := hb
    _ ≤ FSTwoLevel.rankError + (541/100) / FSTwoLevel.fieldSize :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hs (by positivity))
    _ ≤ rate81+p.threshold := by
      change FSTwoLevel.rankError + rate81 ≤ rate81+p.threshold
      linarith


end RecursivePolygero.Benchmarks.FSStoppedSpectrum
