import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Uniform absolute continuity of finite measures

These estimates transfer small-set bounds without a bounded density hypothesis.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Singularity

/-- A finite absolutely continuous measure is uniformly small on sets of
sufficiently small reference measure. The sets need not be measurable. -/
theorem finiteMeasure_uniform_absoluteContinuity {X : Type*} [MeasurableSpace X]
    (ν m : Measure X) [IsFiniteMeasure ν] [SigmaFinite m] (hac : ν ≪ m)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ S : Set X, m S < δ → ν S < ε := by
  have hi : ∫⁻ x, ν.rnDeriv m x ∂m ≠ ⊤ := by
    rw [Measure.lintegral_rnDeriv hac]
    exact measure_ne_top _ _
  obtain ⟨δ, hδ, hb⟩ := exists_pos_setLIntegral_lt_of_measure_lt hi hε.ne'
  refine ⟨δ, hδ, fun S hS => ?_⟩
  simpa only [Measure.setLIntegral_rnDeriv hac] using hb S hS

/-- Absolute continuity of a finite measure transfers vanishing masses. -/
theorem finiteMeasure_tendsto_zero_of_absolutelyContinuous {X I : Type*}
    [MeasurableSpace X] (ν m : Measure X) [IsFiniteMeasure ν] [SigmaFinite m]
    (hac : ν ≪ m) (S : I → Set X) {l : Filter I}
    (hS : Tendsto (fun i => m (S i)) l (𝓝 0)) :
    Tendsto (fun i => ν (S i)) l (𝓝 0) := by
  have hi : ∫⁻ x, ν.rnDeriv m x ∂m ≠ ⊤ := by
    rw [Measure.lintegral_rnDeriv hac]
    exact measure_ne_top _ _
  simpa only [Measure.setLIntegral_rnDeriv hac] using tendsto_setLIntegral_zero hi hS

end Singularity
