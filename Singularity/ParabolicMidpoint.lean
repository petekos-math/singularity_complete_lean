import Singularity.ParabolicOrbitHeight

/-!
# Geodesic midpoints between opposite parabolic translates

The midpoint of z-t and z+t has real part re(z) and height
sqrt(im(z)^2+t^2). The metric segment identity is proved from the hyperbolic
cosine distance formula, so no geodesic description is assumed.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The top of the geodesic semicircle joining two opposite translates. -/
def parabolicMidpoint (z : ℍ) (t : ℝ) : ℍ :=
  ⟨⟨z.re, Real.sqrt (z.im ^ 2 + t ^ 2)⟩, Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_pos z.im_pos, sq_nonneg t])⟩

/-- Squared midpoint height. -/
theorem parabolicMidpoint_im_sq (z : ℍ) (t : ℝ) :
    (parabolicMidpoint z t).im ^ 2 = z.im ^ 2 + t ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Midpoint height grows at least as fast as the translation parameter. -/
theorem abs_le_parabolicMidpoint_im (z : ℍ) (t : ℝ) :
    |t| ≤ (parabolicMidpoint z t).im := by
  have hs := parabolicMidpoint_im_sq z t
  nlinarith [sq_abs t, (parabolicMidpoint z t).im_pos, sq_nonneg z.im]

/-- The cosine of either half-segment length is the height ratio. -/
theorem cosh_dist_parabolicMidpoint (z : ℍ) (t : ℝ) :
    Real.cosh (dist (upperShearMatrix t • z) (parabolicMidpoint z t)) =
      (parabolicMidpoint z t).im / z.im := by
  have hr : (upperShearMatrix t • z).re = z.re + t := by
    have h := congrArg Complex.re (upperShearMatrix_smul_coe t z)
    simpa only [Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re] using h
  have hi : (upperShearMatrix t • z).im = z.im := by
    have h := congrArg Complex.im (upperShearMatrix_smul_coe t z)
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero, UpperHalfPlane.coe_im] using h
  rw [UpperHalfPlane.cosh_dist', hr, hi]
  change ((z.re + t - z.re) ^ 2 + z.im ^ 2 + (parabolicMidpoint z t).im ^ 2) /
    (2 * z.im * (parabolicMidpoint z t).im) = _
  have hs := parabolicMidpoint_im_sq z t
  field_simp
  nlinarith

/-- Reversing the parameter leaves the midpoint unchanged. -/
theorem parabolicMidpoint_neg (z : ℍ) (t : ℝ) :
    parabolicMidpoint z (-t) = parabolicMidpoint z t := by
  apply UpperHalfPlane.ext
  simp [parabolicMidpoint]

/-- The constructed point lies on the metric segment joining the translates. -/
theorem parabolicMidpoint_on_segment (z : ℍ) (t : ℝ) :
    dist (upperShearMatrix (-t) • z) (parabolicMidpoint z t) +
      dist (parabolicMidpoint z t) (upperShearMatrix t • z) =
        dist (upperShearMatrix (-t) • z) (upperShearMatrix t • z) := by
  have hl : Real.cosh (dist (upperShearMatrix (-t) • z) (parabolicMidpoint z t)) =
      (parabolicMidpoint z t).im / z.im := by
    simpa only [parabolicMidpoint_neg] using cosh_dist_parabolicMidpoint z (-t)
  have hr := cosh_dist_parabolicMidpoint z t
  have he : dist (upperShearMatrix (-t) • z) (parabolicMidpoint z t) =
      dist (upperShearMatrix t • z) (parabolicMidpoint z t) :=
    Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg (hl.trans hr.symm)
  rw [dist_comm (parabolicMidpoint z t), he, ← two_mul]
  apply Real.cosh_strictMonoOn.injOn (by exact mul_nonneg (by norm_num) dist_nonneg) dist_nonneg
  rw [Real.cosh_two_mul, Real.sinh_sq, hr, UpperHalfPlane.cosh_dist']
  have hre (v : ℝ) : (upperShearMatrix v • z).re = z.re + v := by
    have h := congrArg Complex.re (upperShearMatrix_smul_coe v z)
    simpa only [Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re] using h
  have him (v : ℝ) : (upperShearMatrix v • z).im = z.im := by
    have h := congrArg Complex.im (upperShearMatrix_smul_coe v z)
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero, UpperHalfPlane.coe_im] using h
  rw [hre, hre, him, him]
  have hs := parabolicMidpoint_im_sq z t
  field_simp
  nlinarith

end Singularity
