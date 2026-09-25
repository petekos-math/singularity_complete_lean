import Singularity.VerticalVisualShadows

/-!
# Exponential visual-measure bounds for vertical shadows

On the cap outside [-exp(t) r, exp(t) r], the Poisson density at i is bounded
by exp(-t) (1+r^2)/r^2 times the density at i exp(t). Combined with the exact
center mass, this gives both sides of the visual shadow lemma.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical UpperHalfPlane ENNReal

namespace Singularity

/-- The explicit finite distortion factor for a normalized visual cap. -/
def verticalShadowFactor (r : ℝ) : ℝ := (r ^ 2 + 1) / r ^ 2

theorem verticalShadowFactor_pos {r : ℝ} (hr : 0 < r) : 0 < verticalShadowFactor r := by
  unfold verticalShadowFactor
  positivity

/-- Pointwise Poisson-density comparison on the vertical shadow. -/
theorem halfPlanePoisson_shadow_bound (t : ℝ) {r : ℝ} (hr : 0 < r) (ξ : ℝ)
    (hξ : Real.exp t * r ≤ |ξ|) :
    halfPlanePoisson 0 1 ξ ≤ verticalShadowFactor r * Real.exp (-t) *
      halfPlanePoisson 0 (Real.exp t) ξ := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hs : Real.exp t ^ 2 * r ^ 2 ≤ ξ ^ 2 := by
    have h := sq_le_sq₀ (by positivity : 0 ≤ Real.exp t * r) (abs_nonneg ξ) |>.mpr hξ
    simpa only [mul_pow, sq_abs] using h
  have hb : ξ ^ 2 + Real.exp t ^ 2 ≤ verticalShadowFactor r * (ξ ^ 2 + 1) := by
    rw [verticalShadowFactor, div_mul_eq_mul_div]
    apply (le_div_iff₀ hr2).mpr
    nlinarith [sq_nonneg r]
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  unfold halfPlanePoisson
  simp only [sub_zero, one_pow]
  rw [show verticalShadowFactor r * Real.exp (-t) *
      (Real.exp t / (Real.pi * (ξ ^ 2 + Real.exp t ^ 2))) =
      verticalShadowFactor r / (Real.pi * (ξ ^ 2 + Real.exp t ^ 2)) by
    rw [← mul_div_assoc, mul_assoc, he, mul_one]]
  apply (div_le_div_iff₀ (by positivity : 0 < Real.pi * (ξ ^ 2 + 1))
    (by positivity : 0 < Real.pi * (ξ ^ 2 + Real.exp t ^ 2))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb Real.pi_pos.le]

/-- Integrating the pointwise comparison gives the cap mass estimate. -/
theorem halfPlanePoissonMeasure_shadow_bound (t : ℝ) {r : ℝ} (hr : 0 < r) :
    halfPlanePoissonMeasure 0 1 {ξ : ℝ | Real.exp t * r < |ξ|} ≤
      ENNReal.ofReal (verticalShadowFactor r * Real.exp (-t)) *
        halfPlanePoissonMeasure 0 (Real.exp t) {ξ : ℝ | Real.exp t * r < |ξ|} := by
  let S := {ξ : ℝ | Real.exp t * r < |ξ|}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hC : 0 ≤ verticalShadowFactor r * Real.exp (-t) :=
    mul_nonneg (verticalShadowFactor_pos hr).le (Real.exp_nonneg _)
  change halfPlanePoissonMeasure 0 1 S ≤ _ * halfPlanePoissonMeasure 0 (Real.exp t) S
  rw [halfPlanePoissonMeasure, halfPlanePoissonMeasure, withDensity_apply _ hS, withDensity_apply _ hS]
  rw [← lintegral_const_mul _ (measurable_halfPlanePoisson 0 (Real.exp t)).ennreal_ofReal]
  apply lintegral_mono_ae
  apply (ae_restrict_iff' hS).mpr
  apply Eventually.of_forall
  intro ξ hξ
  rw [← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (halfPlanePoisson_shadow_bound t hr ξ hξ.le)

/-- The upper bound in the visual shadow lemma has a constant independent of height. -/
theorem verticalVisualShadow_mass_upper (t : ℝ) {r : ℝ} (hr : 0 < r) :
    compactPoissonMeasure UpperHalfPlane.I (verticalVisualShadow t r) ≤
      ENNReal.ofReal (verticalShadowFactor r * Real.exp (-t)) * verticalShadowMass r := by
  have hb := halfPlanePoissonMeasure_shadow_bound t hr
  have hc := verticalVisualShadow_mass_at_center t r
  rw [compactPoissonMeasure_verticalVisualShadow] at hc ⊢
  change halfPlanePoissonMeasure 0 (Real.exp t * 1) {ξ : ℝ | Real.exp t * r < |ξ|} = verticalShadowMass r at hc
  rw [mul_one] at hc
  change halfPlanePoissonMeasure 0 1 {ξ : ℝ | Real.exp t * r < |ξ|} ≤ _
  rwa [hc] at hb

/-- The lower bound follows from visual Harnack comparison and the fixed
positive mass of the cap at its center. -/
theorem verticalVisualShadow_mass_lower {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    ENNReal.ofReal (Real.exp (-t)) * verticalShadowMass r ≤
      compactPoissonMeasure UpperHalfPlane.I (verticalVisualShadow t r) := by
  have h := compactPoissonMeasure_exp_lower UpperHalfPlane.I (verticalHeightRay UpperHalfPlane.I t)
    (verticalVisualShadow t r)
  rw [Measure.smul_apply, smul_eq_mul, verticalVisualShadow_mass_at_center,
    dist_comm (verticalHeightRay UpperHalfPlane.I t) UpperHalfPlane.I,
    verticalHeightRay_dist UpperHalfPlane.I ht] at h
  exact h

/-- Both sides of the visual shadow estimate for every point on the upward ray. -/
theorem verticalVisualShadow_mass_bounds {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    ENNReal.ofReal (Real.exp (-t)) * verticalShadowMass r ≤
        compactPoissonMeasure UpperHalfPlane.I (verticalVisualShadow t r) ∧
      compactPoissonMeasure UpperHalfPlane.I (verticalVisualShadow t r) ≤
        ENNReal.ofReal (verticalShadowFactor r * Real.exp (-t)) * verticalShadowMass r :=
  ⟨verticalVisualShadow_mass_lower ht r, verticalVisualShadow_mass_upper t hr⟩

end Singularity
