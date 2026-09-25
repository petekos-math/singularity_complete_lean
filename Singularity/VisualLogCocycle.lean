import Singularity.LogDensityBounds
import Singularity.RadonNikodymCoboundary
import Singularity.VisualPoissonOrbit

/-!
# Hyperbolic displacement bounds for the visual logarithmic cocycle

The bounds apply to the actual Radon–Nikodym derivative of visual measures.
They follow from the proved Poisson measure comparison at arbitrary basepoints.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- The lower half of the exponential comparison between visual measures. -/
theorem compactPoissonMeasure_exp_lower (z w : ℍ) :
    ENNReal.ofReal (Real.exp (-dist w z)) • compactPoissonMeasure w ≤ compactPoissonMeasure z := by
  have h := smul_le_smul_left (ENNReal.ofReal (Real.exp (-dist w z)))
    (compactPoissonMeasure_le_exp_dist_between w z)
  rw [smul_smul, dist_comm z w, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_smul] at h
  exact h

/-- Logarithms of visual Radon–Nikodym derivatives are bounded by the distance
between the basepoints. -/
theorem compactPoissonMeasure_log_rnDeriv_bound (z w : ℍ) :
    ∀ᵐ ξ ∂compactPoissonMeasure w,
      |Real.log (((compactPoissonMeasure z).rnDeriv (compactPoissonMeasure w) ξ).toReal)| ≤ dist w z := by
  let := compactPoissonMeasure_probability z
  let := compactPoissonMeasure_probability w
  exact log_rnDeriv_abs_le_of_exp_comparison _ _ _
    (compactPoissonMeasure_exp_lower z w) (compactPoissonMeasure_le_exp_dist_between z w)

/-- The actual visual logarithmic cocycle is essentially bounded by the
hyperbolic displacement of the projective element. -/
theorem projective_visual_logCocycle_bound (z : ℍ) (g : PSL(2, ℝ)) :
    ∀ᵐ ξ ∂compactPoissonMeasure z,
      |stationaryLogCocycle (compactPoissonMeasure z) g ξ| ≤ dist z (g • z) := by
  have hd : dist z (g⁻¹ • z) = dist z (g • z) := by
    have h := projective_dist_smul g z (g⁻¹ • z)
    rw [smul_inv_smul, dist_comm (g • z) z] at h
    exact h.symm
  simpa only [stationaryLogCocycle, stationaryRealDensity, stationaryDensity,
    compactPoissonMeasure_projective_covariance, abs_neg, hd] using
    compactPoissonMeasure_log_rnDeriv_bound (g⁻¹ • z) z

end Singularity
