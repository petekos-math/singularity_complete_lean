import Singularity.BoundedDensityConcentration

/-!
# Vertical Poisson concentration at almost every point of a measurable set

The upper-half-plane Poisson law is an affine image of the standard Cauchy
law. Its bounded density and finite mass let the rescaling argument apply at
Lebesgue density points. Lebesgue's density theorem supplies such points almost
everywhere in any measurable set.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical Topology ENNReal

namespace Singularity

/-- The Poisson law at x+i r is the affine rescaling of the law at i. -/
theorem halfPlanePoissonMeasure_affine (x r : ℝ) (hr : 0 < r) :
    Measure.map (fun t : ℝ => x + r * t) (halfPlanePoissonMeasure 0 1) = halfPlanePoissonMeasure x r := by
  have hs : Measure.map (fun t : ℝ => r * t) (halfPlanePoissonMeasure 0 1) = halfPlanePoissonMeasure 0 r := by
    simpa only [Real.exp_log hr, mul_zero, mul_one] using halfPlanePoissonMeasure_dilation 0 1 (Real.log r)
  calc
    _ = Measure.map (fun t : ℝ => x + t)
        (Measure.map (fun t : ℝ => r * t) (halfPlanePoissonMeasure 0 1)) := by
      have h1 : Measurable (fun t : ℝ => x + t) := by fun_prop
      have h2 : Measurable (fun t : ℝ => r * t) := by fun_prop
      rw [Measure.map_map h1 h2]
      rfl
    _ = Measure.map (fun t : ℝ => x + t) (halfPlanePoissonMeasure 0 r) := by rw [hs]
    _ = _ := by simpa only [add_zero] using halfPlanePoissonMeasure_translate 0 r x

/-- The standard Cauchy law has globally bounded density. -/
theorem halfPlanePoissonMeasure_base_le_volume :
    halfPlanePoissonMeasure 0 1 ≤ ENNReal.ofReal Real.pi⁻¹ • volume := by
  rw [halfPlanePoissonMeasure, ← withDensity_const]
  apply withDensity_mono
  apply Eventually.of_forall
  intro t
  apply ENNReal.ofReal_le_ofReal
  unfold halfPlanePoisson
  simp only [sub_zero, one_pow]
  apply (div_le_iff₀ (show 0 < Real.pi * (t ^ 2 + 1) by positivity)).mpr
  rw [← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  nlinarith [sq_nonneg t]

/-- The Poisson measure of the complement tends to zero at every density-one point. -/
theorem halfPlanePoisson_compl_tendsto_of_density_one (S : Set ℝ) (hS : MeasurableSet S) (x : ℝ)
    (hdensity : Tendsto (fun r : ℝ => volume (S ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun r : ℝ => halfPlanePoissonMeasure x r Sᶜ) (𝓝[>] 0) (𝓝 0) := by
  let := halfPlanePoissonMeasure_probability 0 (by norm_num : (0 : ℝ) < 1)
  have ht := boundedDensity_rescaled_compl_of_density_one (halfPlanePoissonMeasure 0 1)
    (ENNReal.ofReal Real.pi⁻¹) ENNReal.ofReal_ne_top halfPlanePoissonMeasure_base_le_volume S hS x hdensity
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [← halfPlanePoissonMeasure_affine x r hr]
  exact (Measure.map_apply (by fun_prop : Measurable (fun t : ℝ => x + r * t)) hS.compl).symm

/-- Vertical Poisson concentration holds at almost every point of a measurable set. -/
theorem ae_halfPlanePoisson_compl_tendsto (S : Set ℝ) (hS : MeasurableSet S) :
    ∀ᵐ x ∂volume.restrict S,
      Tendsto (fun r : ℝ => halfPlanePoissonMeasure x r Sᶜ) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div volume S 0] with x hx
  apply halfPlanePoisson_compl_tendsto_of_density_one S hS x
  exact hx (fun _ : ℝ => x) id tendsto_id (Eventually.of_forall fun r => by simp)

end Singularity
