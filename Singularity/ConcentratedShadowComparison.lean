import Singularity.BoundedDensityWindows
import Singularity.ShadowMagnitudeComparison
import Mathlib.MeasureTheory.Measure.Real

/-!
# Comparing shadow masses through a bounded-density window

When both measures put at least half the mass of a shadow in the same
bounded-density window, their shadow masses are uniformly comparable.
Relative concentration makes this hold eventually, so a ratio limit is
unnecessary for obtaining bounded magnitude differences along a sequence.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Singularity

/-- A relative error at most one half puts at least half the mass in E. -/
theorem measureReal_le_twice_inter_of_relative_error {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν] {S E : Set B} (hE : MeasurableSet E)
    (hpos : 0 < (ν S).toReal)
    (herr : (ν (S \ E)).toReal / (ν S).toReal ≤ 1 / 2) :
    (ν S).toReal ≤ 2 * (ν (S ∩ E)).toReal := by
  have he := measureReal_inter_add_sdiff (μ := ν) (s := S) hE
  change (ν (S ∩ E)).toReal + (ν (S \ E)).toReal = (ν S).toReal at he
  have hb := (div_le_iff₀ hpos).mp herr
  linarith

/-- Local density comparison and small relative errors control the logarithm
of the full shadow-mass ratio. -/
theorem log_shadow_mass_difference_of_window_concentration
    {B : Type*} [MeasurableSpace B] (ν m : Measure B)
    [IsFiniteMeasure ν] [IsFiniteMeasure m] {S E : Set B} (hE : MeasurableSet E)
    (M : ℝ)
    (hl : ENNReal.ofReal (Real.exp (-M)) • m.restrict E ≤ ν.restrict E)
    (hu : ν.restrict E ≤ ENNReal.ofReal (Real.exp M) • m.restrict E)
    (hpν : 0 < (ν S).toReal) (hpm : 0 < (m S).toReal)
    (hνerr : (ν (S \ E)).toReal / (ν S).toReal ≤ 1 / 2)
    (hmerr : (m (S \ E)).toReal / (m S).toReal ≤ 1 / 2) :
    |Real.log (ν S).toReal - Real.log (m S).toReal| ≤ M + Real.log 2 := by
  have hνhalf := measureReal_le_twice_inter_of_relative_error ν hE hpν hνerr
  have hmhalf := measureReal_le_twice_inter_of_relative_error m hE hpm hmerr
  have hlr := ENNReal.toReal_mono (measure_ne_top (ν.restrict E) S) (hl S)
  have hfinite : (ENNReal.ofReal (Real.exp M) • m.restrict E) S ≠ ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hur := ENNReal.toReal_mono hfinite (hu S)
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hE,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hlr hur
  have hc : Real.exp M * Real.exp (-M) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hrev : (m (S ∩ E)).toReal ≤ Real.exp M * (ν (S ∩ E)).toReal := by
    calc
      _ = Real.exp M * (Real.exp (-M) * (m (S ∩ E)).toReal) := by
        rw [← mul_assoc, hc, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlr (Real.exp_nonneg _)
  have hνsub : (ν (S ∩ E)).toReal ≤ (ν S).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono inter_subset_left)
  have hmsub : (m (S ∩ E)).toReal ≤ (m S).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono inter_subset_left)
  have he : Real.exp (M + Real.log 2) = 2 * Real.exp M := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hv : (ν S).toReal ≤ Real.exp (M + Real.log 2) * (m S).toReal := by
    rw [he]
    calc
      _ ≤ 2 * (ν (S ∩ E)).toReal := hνhalf
      _ ≤ 2 * (Real.exp M * (m (S ∩ E)).toReal) := by gcongr
      _ ≤ 2 * (Real.exp M * (m S).toReal) := by gcongr
      _ = _ := by ring
  have hm' : (m S).toReal ≤ Real.exp (M + Real.log 2) * (ν S).toReal := by
    rw [he]
    calc
      _ ≤ 2 * (m (S ∩ E)).toReal := hmhalf
      _ ≤ 2 * (Real.exp M * (ν (S ∩ E)).toReal) := by gcongr
      _ ≤ 2 * (Real.exp M * (ν S).toReal) := by gcongr
      _ = _ := by ring
  have hvl := Real.log_le_log hpν hv
  have hml := Real.log_le_log hpm hm'
  rw [Real.log_mul (Real.exp_pos _).ne' hpm.ne', Real.log_exp] at hvl
  rw [Real.log_mul (Real.exp_pos _).ne' hpν.ne', Real.log_exp] at hml
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Relative concentration in a common bounded-density window bounds the
magnitude difference eventually; no convergence of the mass ratio is needed. -/
theorem eventually_bounded_magnitude_difference_of_concentration
    {B : Type*} [MeasurableSpace B] (ν m : Measure B)
    [IsFiniteMeasure ν] [IsFiniteMeasure m] {E : Set B} (hE : MeasurableSet E)
    (S : ℕ → Set B) (Dν Dm : ℕ → ℝ) (Cν Cm M : ℝ)
    (hl : ENNReal.ofReal (Real.exp (-M)) • m.restrict E ≤ ν.restrict E)
    (hu : ν.restrict E ≤ ENNReal.ofReal (Real.exp M) • m.restrict E)
    (hνl : ∀ n, ENNReal.ofReal (Real.exp (-Dν n - Cν)) ≤ ν (S n))
    (hνu : ∀ n, ν (S n) ≤ ENNReal.ofReal (Real.exp (-Dν n + Cν)))
    (hml : ∀ n, ENNReal.ofReal (Real.exp (-Dm n - Cm)) ≤ m (S n))
    (hmu : ∀ n, m (S n) ≤ ENNReal.ofReal (Real.exp (-Dm n + Cm)))
    (hνcon : Tendsto (fun n => (ν (S n \ E)).toReal / (ν (S n)).toReal) atTop (𝓝 0))
    (hmcon : Tendsto (fun n => (m (S n \ E)).toReal / (m (S n)).toReal) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, |Dν n - Dm n| ≤ Cν + Cm + M + Real.log 2 := by
  have hνsmall := hνcon.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hmsmall := hmcon.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hνsmall, hmsmall] with n hn hm
  have hpν : 0 < (ν (S n)).toReal := ENNReal.toReal_pos
    ((ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le (hνl n)).ne' (measure_ne_top _ _)
  have hpm : 0 < (m (S n)).toReal := ENNReal.toReal_pos
    ((ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le (hml n)).ne' (measure_ne_top _ _)
  have he := log_shadow_mass_difference_of_window_concentration ν m hE M hl hu hpν hpm hn.le hm.le
  have h1 := log_measure_error_of_exp_bounds ν (S n) (Dν n) Cν (hνl n) (hνu n)
  have h2 := log_measure_error_of_exp_bounds m (S n) (Dm n) Cm (hml n) (hmu n)
  rcases abs_le.mp he with ⟨hel, heu⟩
  rcases abs_le.mp h1 with ⟨h1l, h1u⟩
  rcases abs_le.mp h2 with ⟨h2l, h2u⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A finite initial segment cannot destroy boundedness of a real sequence. -/
theorem bounded_abs_sequence_of_eventually {f : ℕ → ℝ} {C : ℝ}
    (h : ∀ᶠ n in atTop, |f n| ≤ C) : ∃ K : ℝ, ∀ n, |f n| ≤ K := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max C (∑ n ∈ Finset.range N, |f n|), fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_max_left _ _)
  · exact (Finset.single_le_sum (fun i _ => abs_nonneg (f i))
      (Finset.mem_range.mpr (lt_of_not_ge hn))).trans (le_max_right _ _)

end Singularity
