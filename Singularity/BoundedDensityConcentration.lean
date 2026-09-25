import Singularity.DensityRescaling

/-!
# A finite bounded-density measure concentrates at Lebesgue density points

After rescaling a density-zero set, its intersection with each fixed bounded
window has measure tending to zero. Finiteness makes the mass outside a large
window uniformly small. This proves the analytic concentration statement
needed below, with no pointwise convergence of rescaled indicators assumed.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical Topology ENNReal

namespace Singularity

/-- A finite measure dominated by a constant times Lebesgue measure gives
vanishing mass to a rescaled density-zero set. -/
theorem boundedDensity_rescaled_density_zero (ν : Measure ℝ) [IsFiniteMeasure ν]
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (hdom : ν ≤ c • volume) (S : Set ℝ) (x : ℝ)
    (hdensity : Tendsto (fun r : ℝ => volume (S ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => ν ((fun t : ℝ => x + r * t) ⁻¹' S)) (𝓝[>] 0) (𝓝 0) := by
  have htail : Tendsto (fun R : ℝ => ν (closedBall 0 R)ᶜ) atTop (𝓝 0) := by
    simpa using tendsto_measure_compl_closedBall_of_isTightMeasureSet
      (isTightMeasureSet_singleton (μ := ν)) (0 : ℝ)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨R, hRtail, hR⟩ := ((ENNReal.tendsto_nhds_zero.mp htail (ε / 2) hhalf).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have hlocal := ENNReal.Tendsto.const_mul (density_zero_rescaled_ball S x hdensity R hR) (Or.inr hc)
  simp only [mul_zero] at hlocal
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hlocal (ε / 2) hhalf] with r hr
  let T := (fun t : ℝ => x + r * t) ⁻¹' S
  have hb : ν (T ∩ closedBall 0 R) ≤ ε / 2 := by
    have hh := hdom (T ∩ closedBall 0 R)
    simp only [Measure.smul_apply, smul_eq_mul] at hh
    exact hh.trans hr
  have hcover : T ⊆ (T ∩ closedBall 0 R) ∪ (closedBall 0 R)ᶜ := by
    intro t ht
    by_cases htB : t ∈ closedBall 0 R
    · exact Or.inl ⟨ht, htB⟩
    · exact Or.inr htB
  calc
    _ ≤ ν (T ∩ closedBall 0 R) + ν (closedBall 0 R)ᶜ :=
      (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ ε / 2 + ε / 2 := add_le_add hb hRtail
    _ = ε := ENNReal.add_halves ε

/-- At a density-one point, the complement has vanishing rescaled mass. -/
theorem boundedDensity_rescaled_compl_of_density_one (ν : Measure ℝ) [IsFiniteMeasure ν]
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (hdom : ν ≤ c • volume)
    (S : Set ℝ) (hS : MeasurableSet S) (x : ℝ)
    (hdensity : Tendsto (fun r : ℝ => volume (S ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun r : ℝ => ν ((fun t : ℝ => x + r * t) ⁻¹' Sᶜ)) (𝓝[>] 0) (𝓝 0) :=
  boundedDensity_rescaled_density_zero ν c hc hdom Sᶜ x (density_compl_tendsto_zero S hS x hdensity)

end Singularity
