import Singularity.ShadowMagnitudeComparison
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Bounded magnitude difference along a differentiating shadow sequence

A positive finite limit of the ratio of two shadow masses, together with
exponential shadow estimates, bounds the difference of the two magnitudes
along the entire sequence. Establishing such a ratio limit for the hitting
and visual measures remains a geometric differentiation obligation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Singularity

/-- A positive shadow-mass ratio limit supplies the bounded-magnitude sequence
used in the density-rigidity argument. No global density bound is assumed. -/
theorem bounded_magnitude_difference_of_shadow_ratio_limit {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) [IsFiniteMeasure ν] [IsFiniteMeasure m]
    (S : ℕ → Set B) (Dν Dm : ℕ → ℝ) (Cν Cm : ℝ)
    (hνl : ∀ n, ENNReal.ofReal (Real.exp (-Dν n - Cν)) ≤ ν (S n))
    (hνu : ∀ n, ν (S n) ≤ ENNReal.ofReal (Real.exp (-Dν n + Cν)))
    (hml : ∀ n, ENNReal.ofReal (Real.exp (-Dm n - Cm)) ≤ m (S n))
    (hmu : ∀ n, m (S n) ≤ ENNReal.ofReal (Real.exp (-Dm n + Cm)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hratio : Tendsto (fun n => (ν (S n)).toReal / (m (S n)).toReal) atTop (𝓝 ρ)) :
    ∃ C : ℝ, ∀ n : ℕ, |Dν n - Dm n| ≤ C := by
  have hlog := hratio.log hρ.ne'
  obtain ⟨K, hK⟩ := (Metric.isBounded_range_of_tendsto _ hlog).exists_norm_le
  refine ⟨Cν + Cm + K, fun n => ?_⟩
  have hpν : 0 < (ν (S n)).toReal := ENNReal.toReal_pos
    ((ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le (hνl n)).ne' (measure_ne_top _ _)
  have hpm : 0 < (m (S n)).toReal := ENNReal.toReal_pos
    ((ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le (hml n)).ne' (measure_ne_top _ _)
  have h1 := log_measure_error_of_exp_bounds ν (S n) (Dν n) Cν (hνl n) (hνu n)
  have h2 := log_measure_error_of_exp_bounds m (S n) (Dm n) Cm (hml n) (hmu n)
  have h3 := hK _ ⟨n, rfl⟩
  dsimp only at h3
  rw [Real.norm_eq_abs, Real.log_div hpν.ne' hpm.ne'] at h3
  rcases abs_le.mp h1 with ⟨h1l, h1u⟩
  rcases abs_le.mp h2 with ⟨h2l, h2u⟩
  rcases abs_le.mp h3 with ⟨h3l, h3u⟩
  apply abs_le.mpr
  constructor <;> linarith

end Singularity
