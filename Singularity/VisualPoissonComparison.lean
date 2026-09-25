import Singularity.PoissonDominationDecay

/-!
# Uniform exponential comparison of visual measures

The logarithmic-height Lipschitz estimate bounds every visual Poisson value
by exp(distance). The corresponding measures obey the same domination, and
compact visual measures have full topological support.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped Classical ENNReal UpperHalfPlane
namespace Singularity

/-- Every visual Poisson value is at most the exponential displacement. -/
theorem visualPoisson_le_exp_dist (z : ℍ) (ξ : ℝ) :
    visualPoisson z ξ ≤ Real.exp (dist UpperHalfPlane.I z) := by
  unfold visualPoisson
  apply (div_le_iff₀ (boundaryPoleMatrix ξ • UpperHalfPlane.I).im_pos).mpr
  have h := UpperHalfPlane.im_le_im_mul_exp_dist (boundaryPoleMatrix ξ • z)
    (boundaryPoleMatrix ξ • UpperHalfPlane.I)
  rw [dist_smul, dist_comm z UpperHalfPlane.I] at h
  simpa only [mul_comm] using h

/-- Pointwise comparison of the normalized real-boundary Poisson densities. -/
theorem halfPlanePoisson_le_exp_dist (z : ℍ) (ξ : ℝ) :
    halfPlanePoisson z.re z.im ξ ≤ Real.exp (dist UpperHalfPlane.I z) *
      halfPlanePoisson 0 1 ξ := by
  have h := visualPoisson_le_exp_dist z ξ
  rw [visualPoisson_eq_density] at h
  have hd : 0 < Real.pi * (1 + ξ ^ 2) := by positivity
  have he : (Real.pi * (1 + ξ ^ 2)) * halfPlanePoisson 0 1 ξ = 1 := by
    unfold halfPlanePoisson
    simp only [sub_zero, one_pow]
    field_simp
    ring
  apply (mul_le_mul_iff_right₀ hd).mp
  calc
    _ ≤ Real.exp (dist UpperHalfPlane.I z) := h
    _ = _ := by rw [mul_left_comm _ (Real.exp _), he, mul_one]

/-- The finite-chart visual measure is dominated by exponential displacement
 times the base visual measure. -/
theorem poissonBoundaryMeasure_le_exp_dist (z : ℍ) :
    poissonBoundaryMeasure z ≤ ENNReal.ofReal (Real.exp (dist UpperHalfPlane.I z)) •
      poissonBoundaryMeasure UpperHalfPlane.I := by
  rw [poissonBoundaryMeasure, poissonBoundaryMeasure, UpperHalfPlane.I_re, UpperHalfPlane.I_im,
    smul_halfPlanePoissonMeasure _ _ (Real.exp_pos _).le]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro ξ
  exact ENNReal.ofReal_le_ofReal (halfPlanePoisson_le_exp_dist z ξ)

/-- Exponential visual-measure comparison holds on the entire compact boundary. -/
theorem compactPoissonMeasure_le_exp_dist (z : ℍ) :
    compactPoissonMeasure z ≤ ENNReal.ofReal (Real.exp (dist UpperHalfPlane.I z)) •
      compactPoissonMeasure UpperHalfPlane.I := by
  have h := Measure.map_mono (poissonBoundaryMeasure_le_exp_dist z) OnePoint.continuous_coe.measurable
  rw [Measure.map_smul _ OnePoint.continuous_coe.measurable.aemeasurable] at h
  exact h

/-- Every nonempty compact-boundary open set has positive visual measure. -/
theorem compactPoissonMeasure_isOpenPosMeasure (z : ℍ) :
    Measure.IsOpenPosMeasure (compactPoissonMeasure z) := by
  let : Measure.IsOpenPosMeasure (poissonBoundaryMeasure z) :=
    (halfPlanePoissonMeasure_measureClass z.re z.im_pos).2.isOpenPosMeasure
  refine ⟨fun U hU hne => ?_⟩
  change Measure.map (fun t : ℝ => (t : OnePoint ℝ)) (poissonBoundaryMeasure z) U ≠ 0
  rw [Measure.map_apply OnePoint.continuous_coe.measurable hU.measurableSet]
  exact (hU.preimage OnePoint.continuous_coe).measure_ne_zero _
    (OnePoint.denseRange_coe.exists_mem_open hU hne)

end Singularity
