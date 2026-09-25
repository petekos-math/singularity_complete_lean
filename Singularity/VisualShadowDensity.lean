import Singularity.VisualShadows

/-!
# Density comparison on visual shadows

The shadow estimate holds for every measurable subset of a cap, not merely
for its total mass. In measure form, the base visual measure restricted to
the shadow is bounded by exp(-distance) times the center visual measure.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- The pointwise Poisson estimate gives domination of the entire restricted measure. -/
theorem halfPlanePoissonMeasure_shadow_restrict_bound (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (halfPlanePoissonMeasure 0 1).restrict {ξ : ℝ | Real.exp t * r < |ξ|} ≤
      ENNReal.ofReal (verticalShadowFactor r * Real.exp (-t)) • halfPlanePoissonMeasure 0 (Real.exp t) := by
  let S := {ξ : ℝ | Real.exp t * r < |ξ|}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hC : 0 ≤ verticalShadowFactor r * Real.exp (-t) := by
    exact mul_nonneg (verticalShadowFactor_pos hr).le (Real.exp_nonneg _)
  rw [smul_halfPlanePoissonMeasure _ _ hC, halfPlanePoissonMeasure, restrict_withDensity hS, ← withDensity_indicator hS]
  apply withDensity_mono
  apply Eventually.of_forall
  intro ξ
  by_cases hξ : ξ ∈ S
  · rw [indicator_of_mem hξ]
    exact ENNReal.ofReal_le_ofReal (halfPlanePoisson_shadow_bound t hr ξ hξ.le)
  · rw [indicator_of_notMem hξ]
    positivity

/-- Compactification preserves the restricted Poisson comparison. -/
theorem verticalVisualShadow_restrict_bound (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (compactPoissonMeasure UpperHalfPlane.I).restrict (verticalVisualShadow t r) ≤
      ENNReal.ofReal (verticalShadowFactor r * Real.exp (-t)) •
        compactPoissonMeasure (verticalHeightRay UpperHalfPlane.I t) := by
  have h := Measure.map_mono (halfPlanePoissonMeasure_shadow_restrict_bound t hr)
    OnePoint.continuous_coe.measurable
  rw [Measure.map_smul _ OnePoint.continuous_coe.measurable.aemeasurable] at h
  have he := Measure.restrict_map (μ := halfPlanePoissonMeasure 0 1)
    OnePoint.continuous_coe.measurable (isOpen_verticalVisualShadow t r).measurableSet
  rw [verticalVisualShadow_real_preimage] at he
  change (compactPoissonMeasure UpperHalfPlane.I).restrict (verticalVisualShadow t r) = _ at he
  rw [he]
  change Measure.map (fun ξ : ℝ => (ξ : OnePoint ℝ))
      ((halfPlanePoissonMeasure 0 1).restrict {ξ : ℝ | Real.exp t * r < |ξ|}) ≤
    ENNReal.ofReal (verticalShadowFactor r * Real.exp (-t)) •
      Measure.map (fun ξ : ℝ => (ξ : OnePoint ℝ)) (halfPlanePoissonMeasure 0 (Real.exp t * 1))
  simpa only [mul_one] using h

/-- Covariance also holds for a restricted visual measure and the transported set. -/
theorem compactPoissonMeasure_map_restrict_image (a : SL(2, ℝ)) (z : ℍ)
    {S : Set (OnePoint ℝ)} (hS : MeasurableSet S) :
    Measure.map (fun ξ : OnePoint ℝ => a • ξ) ((compactPoissonMeasure z).restrict S) =
      (compactPoissonMeasure (a • z)).restrict ((fun ξ : OnePoint ℝ => a • ξ) '' S) := by
  have h := Measure.restrict_map (μ := compactPoissonMeasure z) (measurable_const_smul a)
    ((measurableEmbedding_const_smul (α := OnePoint ℝ) a).measurableSet_image.mpr hS)
  rw [compactPoissonMeasure_covariance,
    preimage_image_eq _ (show Function.Injective (fun ξ : OnePoint ℝ => a • ξ) from
      (MeasurableEquiv.smul a).injective)] at h
  exact h.symm

/-- Uniform restricted-measure comparison on shadows at arbitrary basepoints. -/
theorem visualShadow_restrict_bound (z w : ℍ) {r : ℝ} (hr : 0 < r) :
    (compactPoissonMeasure z).restrict (visualShadow z w r) ≤
      ENNReal.ofReal (verticalShadowFactor r * Real.exp (-dist z w)) • compactPoissonMeasure w := by
  have h := Measure.map_mono (verticalVisualShadow_restrict_bound (dist z w) hr)
    (measurable_const_smul (visualShadowAxis z w))
  rw [compactPoissonMeasure_map_restrict_image _ _ (isOpen_verticalVisualShadow _ _).measurableSet,
    Measure.map_smul _ (measurable_const_smul _).aemeasurable, compactPoissonMeasure_covariance,
    (visualShadowAxis_spec z w).1, (visualShadowAxis_spec z w).2] at h
  exact h

/-- A bound on a restricted measure bounds its original density on that set. -/
theorem real_rnDeriv_le_on_set_of_restrict_le {X : Type*} [MeasurableSpace X]
    (ν m : Measure X) [SigmaFinite ν] [SigmaFinite m]
    {S : Set X} (hS : MeasurableSet S) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ν.restrict S ≤ ENNReal.ofReal C • m) :
    ∀ᵐ x ∂m, x ∈ S → (ν.rnDeriv m x).toReal ≤ C := by
  filter_upwards [real_rnDeriv_le_of_le_smul (ν.restrict S) m C hC hdom,
    Measure.rnDeriv_restrict ν m hS] with x hx he hxS
  rwa [he, indicator_of_mem hxS] at hx

end Singularity
