import Singularity.VisualShadows

/-!
# Widening and shrinking of the explicit visual shadows

The inverse image of a shadow has mass tending uniformly to one as its
positive cap parameter tends to zero. For a fixed cap parameter, the visual
mass at the basepoint tends to zero when the centers escape to infinite distance.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- A smaller positive cap parameter enlarges every vertical shadow. -/
theorem verticalVisualShadow_antitone (t : ℝ) : Antitone (verticalVisualShadow t) := by
  intro r R hrR
  apply compl_subset_compl.mpr
  apply image_mono
  apply Icc_subset_Icc
  · exact mul_le_mul_of_nonpos_left hrR (neg_nonpos.mpr (Real.exp_nonneg _))
  · exact mul_le_mul_of_nonneg_left hrR (Real.exp_nonneg _)

/-- Transport preserves the monotonicity in the cap parameter. -/
theorem visualShadow_antitone (z w : ℍ) : Antitone (visualShadow z w) := by
  intro r R hrR
  exact image_mono (verticalVisualShadow_antitone (dist z w) hrR)

/-- The complement of the normalized cap has at most 2r/pi visual mass. -/
theorem verticalShadowMass_compl_bound (r : ℝ) :
    (1 : ℝ≥0∞) - verticalShadowMass r ≤ ENNReal.ofReal (2 * r / Real.pi) := by
  let ν := halfPlanePoissonMeasure 0 1
  let := halfPlanePoissonMeasure_probability 0 (by norm_num : (0 : ℝ) < 1)
  let S := {ξ : ℝ | r < |ξ|}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hc : ν Sᶜ = 1 - verticalShadowMass r := by
    rw [measure_compl hS (measure_ne_top _ _), measure_univ]
    rfl
  have he : Sᶜ = closedBall (0 : ℝ) r := by
    ext ξ
    simp only [S, mem_compl_iff, mem_ofPred_eq, not_lt, mem_closedBall, Real.dist_eq, sub_zero]
  rw [← hc]
  have h := halfPlanePoissonMeasure_base_le_volume Sᶜ
  rw [Measure.smul_apply, smul_eq_mul, he, Real.volume_closedBall,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr Real.pi_pos.le)] at h
  have heq : Real.pi⁻¹ * (2 * r) = 2 * r / Real.pi := by ring
  rw [heq] at h
  simpa only [ν, he] using h

/-- All projective inverse shadows have a uniform quantitative complement bound. -/
theorem projective_visualShadow_preimage_compl_bound (g : PSL(2, ℝ)) (z : ℍ) (r : ℝ) :
    compactPoissonMeasure z
      (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r)ᶜ) ≤
      ENNReal.ofReal (2 * r / Real.pi) := by
  let := compactPoissonMeasure_probability z
  rw [measure_compl ((isOpen_visualShadow _ _ _).measurableSet.preimage (measurable_const_smul g))
    (measure_ne_top _ _), measure_univ, projective_visualShadow_preimage_mass]
  exact verticalShadowMass_compl_bound r

/-- Choosing a sufficiently small cap parameter gives inverse-shadow mass
arbitrarily close to one, simultaneously for every projective element. -/
theorem projective_visualShadow_uniform_full_mass (z : ℍ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ g : PSL(2, ℝ),
      compactPoissonMeasure z
        (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r)ᶜ) < ENNReal.ofReal ε := by
  refine ⟨ε * Real.pi / 4, by positivity, fun g => ?_⟩
  apply (projective_visualShadow_preimage_compl_bound g z _).trans_lt
  have he : 2 * (ε * Real.pi / 4) / Real.pi = ε / 2 := by field_simp; ring
  rw [he]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr (by linarith)

/-- For fixed cap parameter, shadows based at z have mass tending to zero
when their centers escape to infinite hyperbolic distance. -/
theorem visualShadow_mass_tendsto_zero (z : ℍ) (w : ℕ → ℍ) {r : ℝ} (hr : 0 < r)
    (hescape : Tendsto (fun n => dist z (w n)) atTop atTop) :
    Tendsto (fun n => compactPoissonMeasure z (visualShadow z (w n) r)) atTop (𝓝 0) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hescape
  have hC := ENNReal.tendsto_ofReal (he.const_mul (verticalShadowFactor r))
  have htop : verticalShadowMass r ≠ ⊤ := ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (verticalShadowMass_le_one r)
  have hbound := ENNReal.Tendsto.mul_const hC (Or.inr htop)
  simp only [mul_zero, ENNReal.ofReal_zero, zero_mul] at hbound
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => by positivity) (fun n => (visualShadow_mass_bounds z (w n) hr).2)

end Singularity
