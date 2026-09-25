import Singularity.RadialCoordinate
import Singularity.CayleyExcess
import Singularity.AxisBallSeparation

/-!
# Disk separation for whole radial half-planes

Small-radius points have Cayley coordinate near -1, and large-radius points
have Cayley coordinate near +1. This gives bounded triangle excess uniformly
over the entire two radial regions, including points approaching the real axis.
-/

noncomputable section
open scoped UpperHalfPlane
namespace Singularity

/-- Dilation translates the radial coordinate by its logarithmic factor. -/
theorem axisRadialCoordinate_dilation (t : ℝ) (z : ℍ) :
    axisRadialCoordinate (dilationMatrix t • z) = t + axisRadialCoordinate z := by
  rw [axisRadialCoordinate_eq_log_norm, dilationMatrix_smul, UpperHalfPlane.coe_pos_real_smul,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t),
    Real.log_mul (Real.exp_ne_zero t) (norm_pos_iff.mpr z.ne_zero).ne', Real.log_exp,
    axisRadialCoordinate_eq_log_norm]

/-- In the upper half-plane, adding i increases norm and gives norm at least one. -/
theorem cayley_denominator_norm_bounds (z : ℍ) :
    1 ≤ ‖(z : ℂ)+Complex.I‖ ∧ ‖(z : ℂ)‖ ≤ ‖(z : ℂ)+Complex.I‖ := by
  have hi := Complex.abs_im_le_norm ((z : ℂ)+Complex.I)
  simp only [Complex.add_im, UpperHalfPlane.coe_im, Complex.I_im] at hi
  have hs : ‖(z : ℂ)+Complex.I‖^2 = ‖(z : ℂ)‖^2 + 2*z.im+1 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  constructor
  · have hh := le_abs_self (z.im+1)
    linarith [z.im_pos]
  · nlinarith [norm_nonneg (z : ℂ), norm_nonneg ((z : ℂ)+Complex.I), z.im_pos]

/-- Small Euclidean radius gives closeness to the disk endpoint -1. -/
theorem halfPlaneCayley_dist_neg_one_le (z : ℍ) :
    dist (halfPlaneCayley z) (-1 : ℂ) ≤ 2*‖(z : ℂ)‖ := by
  have he : halfPlaneCayley z - (-1 : ℂ) = (2*(z : ℂ))/((z : ℂ)+Complex.I) := by
    unfold halfPlaneCayley
    field_simp [halfPlaneCayley_denominator_ne_zero z]
    ring
  rw [dist_eq_norm, he, norm_div, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  apply (div_le_iff₀ (norm_pos_iff.mpr (halfPlaneCayley_denominator_ne_zero z))).mpr
  have hh := mul_le_mul_of_nonneg_left (cayley_denominator_norm_bounds z).1
    (show 0 ≤ 2*‖(z : ℂ)‖ by positivity)
  simpa only [mul_one] using hh

/-- Large Euclidean radius gives closeness to the disk endpoint +1. -/
theorem halfPlaneCayley_dist_one_le (z : ℍ) :
    dist (halfPlaneCayley z) (1 : ℂ) ≤ 2/‖(z : ℂ)‖ := by
  have he : halfPlaneCayley z - (1 : ℂ) = (-2*Complex.I)/((z : ℂ)+Complex.I) := by
    unfold halfPlaneCayley
    field_simp [halfPlaneCayley_denominator_ne_zero z]
    ring
  rw [dist_eq_norm, he, norm_div, norm_mul]
  norm_num only [norm_neg, Complex.norm_I, mul_one, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) (norm_pos_iff.mpr z.ne_zero)
    (cayley_denominator_norm_bounds z).2

/-- Radial regions on opposite sides of a fixed gap have uniform disk separation. -/
theorem radial_opposite_cayley_separation (z w : ℍ)
    (hz : axisRadialCoordinate z ≤ -Real.log 4)
    (hw : Real.log 4 ≤ axisRadialCoordinate w) :
    1 ≤ dist (halfPlaneCayley z) (halfPlaneCayley w) := by
  have hz' : ‖(z : ℂ)‖ ≤ 1/4 := by
    rw [axisRadialCoordinate_eq_log_norm] at hz
    have hh := (Real.log_le_iff_le_exp (norm_pos_iff.mpr z.ne_zero)).mp hz
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4), one_div] using hh
  have hw' : 4 ≤ ‖(w : ℂ)‖ := by
    rw [axisRadialCoordinate_eq_log_norm] at hw
    have hh := (Real.le_log_iff_exp_le (norm_pos_iff.mpr w.ne_zero)).mp hw
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4)] using hh
  have hsmall : dist (halfPlaneCayley z) (-1 : ℂ) ≤ 1/2 :=
    (halfPlaneCayley_dist_neg_one_le z).trans (by linarith)
  have hlarge : dist (halfPlaneCayley w) (1 : ℂ) ≤ 1/2 := by
    apply (halfPlaneCayley_dist_one_le w).trans
    apply (div_le_iff₀ (norm_pos_iff.mpr w.ne_zero)).mpr
    linarith
  have ht := dist_triangle4 (-1 : ℂ) (halfPlaneCayley z) (halfPlaneCayley w) 1
  have hends : dist (-1 : ℂ) 1 = 2 := by norm_num [dist_eq_norm]
  rw [hends, dist_comm (-1 : ℂ) (halfPlaneCayley z)] at ht
  linarith

/-- Uniform bounded excess for arbitrary points of the two radial regions. -/
theorem radial_opposite_triangle_excess (z w : ℍ)
    (hz : axisRadialCoordinate z ≤ -Real.log 4)
    (hw : Real.log 4 ≤ axisRadialCoordinate w) :
    dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - dist z w ≤ 2*Real.log 4 := by
  simpa only [div_one] using hyperbolic_excess_of_cayley_separation z w 1 (by norm_num)
    (radial_opposite_cayley_separation z w hz hw)

/-- The same radial-region excess bound at every point of the vertical axis. -/
theorem radial_opposite_triangle_excess_at_axis (z w : ℍ) (t : ℝ)
    (hz : axisRadialCoordinate z ≤ t-Real.log 4)
    (hw : t+Real.log 4 ≤ axisRadialCoordinate w) :
    dist z (verticalHeightRay UpperHalfPlane.I t) + dist w (verticalHeightRay UpperHalfPlane.I t) -
      dist z w ≤ 2*Real.log 4 := by
  have hc : dilationMatrix (-t) • verticalHeightRay UpperHalfPlane.I t = UpperHalfPlane.I := by
    rw [verticalHeightRay_I_dilation, neg_add_cancel, verticalHeightRay_zero]
  have hd (v : ℍ) : dist (dilationMatrix (-t) • v) UpperHalfPlane.I =
      dist v (verticalHeightRay UpperHalfPlane.I t) := by
    calc
      _ = dist (dilationMatrix (-t) • v) (dilationMatrix (-t) • verticalHeightRay UpperHalfPlane.I t) := by rw [hc]
      _ = _ := dist_smul _ _ _
  have hh := radial_opposite_triangle_excess (dilationMatrix (-t) • z) (dilationMatrix (-t) • w)
    (by rw [axisRadialCoordinate_dilation]; linarith)
    (by rw [axisRadialCoordinate_dilation]; linarith)
  simpa only [hd, dist_smul] using hh

/-- Moving the center a bounded distance from the axis preserves the uniform
excess bound for the entire radial regions. -/
theorem radial_opposite_triangle_excess_near_axis (z w o : ℍ) (t E : ℝ)
    (hz : axisRadialCoordinate z ≤ t-Real.log 4)
    (hw : t+Real.log 4 ≤ axisRadialCoordinate w)
    (ho : dist o (verticalHeightRay UpperHalfPlane.I t) ≤ E) :
    dist z o + dist w o - dist z w ≤ 2*Real.log 4+2*E := by
  exact triangle_excess_change_center z w (verticalHeightRay UpperHalfPlane.I t) o _ E
    (radial_opposite_triangle_excess_at_axis z w t hz hw) (by simpa only [dist_comm] using ho)

end Singularity
