import Singularity.VisualShadowDensity

/-!
# Visual cocycle magnitude on inverse shadows

On the inverse image of the explicit shadow of g z, the actual logarithmic
visual Radon–Nikodym cocycle differs from dist(z,g z) by a uniformly bounded
amount. This verifies the visual shadow/cocycle estimate without identifying
any random-walk kernel with the visual kernel.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- Pulling the restricted shadow comparison back to the basepoint controls
the inverse translate of visual measure on the inverse shadow. -/
theorem projective_visualShadow_inverse_restrict_bound (g : PSL(2, ℝ)) (z : ℍ)
    {r : ℝ} (hr : 0 < r) :
    (Measure.map (fun ξ : OnePoint ℝ => g⁻¹ • ξ) (compactPoissonMeasure z)).restrict
        ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r) ≤
      ENNReal.ofReal (verticalShadowFactor r * Real.exp (-dist z (g • z))) • compactPoissonMeasure z := by
  let S := visualShadow z (g • z) r
  let T := (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' S
  have hT : MeasurableSet T := (isOpen_visualShadow _ _ _).measurableSet.preimage (measurable_const_smul g)
  have he : (fun ξ : OnePoint ℝ => g⁻¹ • ξ) ⁻¹' T = S := by
    ext ξ
    simp only [T, mem_preimage, smul_inv_smul]
  have hrestrict := Measure.restrict_map (μ := compactPoissonMeasure z) (measurable_const_smul g⁻¹) hT
  rw [he] at hrestrict
  have h := Measure.map_mono (visualShadow_restrict_bound z (g • z) hr) (measurable_const_smul g⁻¹)
  rw [Measure.map_smul _ (measurable_const_smul g⁻¹).aemeasurable,
    compactPoissonMeasure_projective_covariance, inv_smul_smul] at h
  rw [← hrestrict] at h
  exact h

/-- The visual cocycle has magnitude equal to displacement, up to the explicit
cap-dependent error, almost everywhere on each inverse shadow. -/
theorem projective_visual_logCocycle_shadow_bounds (g : PSL(2, ℝ)) (z : ℍ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ξ ∂compactPoissonMeasure z,
      ξ ∈ (fun η : OnePoint ℝ => g • η) ⁻¹' visualShadow z (g • z) r →
        dist z (g • z) - Real.log (verticalShadowFactor r) ≤
            stationaryLogCocycle (compactPoissonMeasure z) g ξ ∧
          stationaryLogCocycle (compactPoissonMeasure z) g ξ ≤ dist z (g • z) := by
  let := compactPoissonMeasure_probability z
  have hq (a : PSL(2, ℝ)) :
      Measure.map (fun ξ : OnePoint ℝ => a • ξ) (compactPoissonMeasure z) ≪ compactPoissonMeasure z := by
    rw [compactPoissonMeasure_projective_covariance]
    exact Measure.absolutelyContinuous_of_le_smul (compactPoissonMeasure_le_exp_dist_between (a • z) z)
  have hd := real_rnDeriv_le_on_set_of_restrict_le
    (Measure.map (fun ξ : OnePoint ℝ => g⁻¹ • ξ) (compactPoissonMeasure z)) (compactPoissonMeasure z)
    ((isOpen_visualShadow _ _ _).measurableSet.preimage (measurable_const_smul g))
    (verticalShadowFactor r * Real.exp (-dist z (g • z)))
    (mul_nonneg (verticalShadowFactor_pos hr).le (Real.exp_nonneg _))
    (projective_visualShadow_inverse_restrict_bound g z hr)
  filter_upwards [hd, translate_realDensity_pos (compactPoissonMeasure z) hq g⁻¹,
    projective_visual_logCocycle_bound z g] with ξ hξ hp hu hmem
  have hupper := hξ hmem
  change stationaryRealDensity (compactPoissonMeasure z) g⁻¹ ξ ≤ _ at hupper
  have hlog := Real.log_le_log hp hupper
  rw [Real.log_mul (verticalShadowFactor_pos hr).ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  constructor
  · change dist z (g • z) - Real.log (verticalShadowFactor r) ≤
      -Real.log (stationaryRealDensity (compactPoissonMeasure z) g⁻¹ ξ)
    linarith
  · exact (abs_le.mp hu).2

/-- Absolute-error form of the visual shadow/cocycle estimate. -/
theorem projective_visual_logCocycle_shadow_error (g : PSL(2, ℝ)) (z : ℍ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ξ ∂compactPoissonMeasure z,
      ξ ∈ (fun η : OnePoint ℝ => g • η) ⁻¹' visualShadow z (g • z) r →
        |stationaryLogCocycle (compactPoissonMeasure z) g ξ - dist z (g • z)| ≤
          Real.log (verticalShadowFactor r) := by
  filter_upwards [projective_visual_logCocycle_shadow_bounds g z hr] with ξ hξ hmem
  obtain ⟨hl, hu⟩ := hξ hmem
  apply abs_le.mpr
  constructor <;> linarith

end Singularity
