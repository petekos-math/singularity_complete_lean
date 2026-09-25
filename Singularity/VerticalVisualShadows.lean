import Singularity.VisualLogCocycle
import Singularity.PoissonDensityPoint

/-!
# Explicit visual shadows on the vertical axis

The shadow at height exp(t) excludes the finite interval
[-exp(t) r, exp(t) r]. It is an open neighborhood of infinity. Its visual
mass from the point i exp(t) is independent of t, by exact dilation covariance.
These are actual Poisson-measure computations, not assumptions about hitting laws.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- An open boundary cap around the upward vertical endpoint. -/
def verticalVisualShadow (t r : ℝ) : Set (OnePoint ℝ) :=
  ((fun ξ : ℝ => (ξ : OnePoint ℝ)) '' Icc (-Real.exp t * r) (Real.exp t * r))ᶜ

/-- Vertical shadows are open, including their point at infinity. -/
theorem isOpen_verticalVisualShadow (t r : ℝ) : IsOpen (verticalVisualShadow t r) :=
  (isCompact_Icc.image OnePoint.continuous_coe).isClosed.isOpen_compl

/-- In finite boundary coordinates the shadow is exactly a two-sided tail. -/
theorem verticalVisualShadow_real_preimage (t r : ℝ) :
    (fun ξ : ℝ => (ξ : OnePoint ℝ)) ⁻¹' verticalVisualShadow t r =
      {ξ : ℝ | Real.exp t * r < |ξ|} := by
  rw [verticalVisualShadow, preimage_compl, preimage_image_eq _ OnePoint.coe_injective]
  ext ξ
  simp only [mem_compl_iff, mem_Icc, mem_ofPred_eq]
  rw [show -Real.exp t * r = -(Real.exp t * r) by ring, ← abs_le, not_le]

/-- A shadow's visual mass from any interior point is computed in the real chart. -/
theorem compactPoissonMeasure_verticalVisualShadow (z : ℍ) (t r : ℝ) :
    compactPoissonMeasure z (verticalVisualShadow t r) =
      halfPlanePoissonMeasure z.re z.im {ξ : ℝ | Real.exp t * r < |ξ|} := by
  rw [compactPoissonMeasure, compactRealMeasure, Measure.map_apply OnePoint.continuous_coe.measurable
    (isOpen_verticalVisualShadow t r).measurableSet, verticalVisualShadow_real_preimage]
  rfl

/-- The mass of the normalized cap under the standard visual probability. -/
def verticalShadowMass (r : ℝ) : ℝ≥0∞ :=
  halfPlanePoissonMeasure 0 1 {ξ : ℝ | r < |ξ|}

/-- Every normalized cap has positive visual mass. -/
theorem verticalShadowMass_pos (r : ℝ) : 0 < verticalShadowMass r := by
  let : Measure.IsOpenPosMeasure (halfPlanePoissonMeasure 0 1) :=
    (halfPlanePoissonMeasure_measureClass 0 (by norm_num : (0 : ℝ) < 1)).2.isOpenPosMeasure
  apply pos_iff_ne_zero.mpr
  apply (isOpen_lt continuous_const continuous_abs).measure_ne_zero (halfPlanePoissonMeasure 0 1)
  refine ⟨|r| + 1, ?_⟩
  change r < |(|r| + 1)|
  rw [abs_of_pos (by positivity)]
  linarith [le_abs_self r]

/-- The normalized cap mass is at most one. -/
theorem verticalShadowMass_le_one (r : ℝ) : verticalShadowMass r ≤ 1 := by
  let := halfPlanePoissonMeasure_probability 0 (by norm_num : (0 : ℝ) < 1)
  exact (measure_mono (subset_univ _)).trans_eq (measure_univ : halfPlanePoissonMeasure 0 1 univ = 1)

/-- Dilation transports the normalized cap exactly, so the visual mass at its
center is constant along the vertical ray. -/
theorem verticalVisualShadow_mass_at_center (t r : ℝ) :
    compactPoissonMeasure (verticalHeightRay UpperHalfPlane.I t) (verticalVisualShadow t r) =
      verticalShadowMass r := by
  rw [compactPoissonMeasure_verticalVisualShadow]
  change halfPlanePoissonMeasure 0 (Real.exp t * 1) {ξ : ℝ | Real.exp t * r < |ξ|} = _
  rw [mul_one]
  have hs : MeasurableSet {ξ : ℝ | Real.exp t * r < |ξ|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hd := halfPlanePoissonMeasure_dilation 0 1 t
  simp only [mul_zero, mul_one] at hd
  rw [← hd, Measure.map_apply (by fun_prop) hs]
  congr 1
  ext ξ
  simp only [mem_preimage, mem_ofPred_eq, abs_mul, abs_of_pos (Real.exp_pos t),
    mul_lt_mul_iff_right₀ (Real.exp_pos t)]

end Singularity
