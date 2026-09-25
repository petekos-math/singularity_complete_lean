import Singularity.GeometricDetour

/-!
# Recovering hyperbolic triangle excess from disk separation

The exact Cayley distance formula bounds disk separation by an exponential
of minus half the triangle excess. A positive disk separation therefore gives
a uniform upper bound on that excess.
-/

noncomputable section
open scoped UpperHalfPlane

namespace Singularity

/-- Disk separation is at most four times the exponential of minus half
the hyperbolic triangle excess at i. -/
theorem halfPlaneCayley_dist_upper_of_excess (z w : ℍ) :
    dist (halfPlaneCayley z) (halfPlaneCayley w) ≤
      4 * Real.exp (-(dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - dist z w) / 2) := by
  have hz := exp_le_two_cosh (dist z UpperHalfPlane.I / 2)
  have hw := exp_le_two_cosh (dist w UpperHalfPlane.I / 2)
  have hden : Real.exp ((dist z UpperHalfPlane.I + dist w UpperHalfPlane.I) / 2) ≤
      4 * (Real.cosh (dist z UpperHalfPlane.I / 2) * Real.cosh (dist w UpperHalfPlane.I / 2)) := by
    rw [add_div, Real.exp_add]
    nlinarith [mul_le_mul hz hw (Real.exp_pos _).le (by positivity)]
  rw [halfPlaneCayley_dist]
  calc
    _ ≤ 4 * Real.exp (dist z w / 2) /
        Real.exp ((dist z UpperHalfPlane.I + dist w UpperHalfPlane.I) / 2) := by
      apply (div_le_div_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)) (Real.exp_pos _)).mpr
      have hnum := mul_le_mul_of_nonneg_right (sinh_le_exp (dist z w / 2))
        (Real.exp_pos ((dist z UpperHalfPlane.I + dist w UpperHalfPlane.I) / 2)).le
      have hd := mul_le_mul_of_nonneg_left hden (Real.exp_pos (dist z w / 2)).le
      nlinarith
    _ = _ := by
      rw [mul_div_assoc, ← Real.exp_sub]
      congr 2
      ring

/-- Positive disk separation bounds the hyperbolic triangle excess. -/
theorem hyperbolic_excess_of_cayley_separation (z w : ℍ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : δ ≤ dist (halfPlaneCayley z) (halfPlaneCayley w)) :
    dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - dist z w ≤ 2 * Real.log (4 / δ) := by
  have hh := hsep.trans (halfPlaneCayley_dist_upper_of_excess z w)
  have hdiv : δ / 4 ≤ Real.exp (-(dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - dist z w) / 2) :=
    (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by simpa only [mul_comm] using hh)
  have hl := Real.log_le_log (div_pos hδ (by norm_num)) hdiv
  rw [Real.log_exp, Real.log_div hδ.ne' (by norm_num)] at hl
  rw [Real.log_div (by norm_num) hδ.ne']
  linarith

/-- Moving the center by at most E increases triangle excess by at most 2E. -/
theorem triangle_excess_change_center {X : Type*} [PseudoMetricSpace X]
    (x y o o' : X) (D E : ℝ)
    (hexcess : dist x o + dist y o - dist x y ≤ D) (hcenter : dist o o' ≤ E) :
    dist x o' + dist y o' - dist x y ≤ D + 2 * E := by
  linarith [dist_triangle x o o', dist_triangle y o o']

end Singularity
