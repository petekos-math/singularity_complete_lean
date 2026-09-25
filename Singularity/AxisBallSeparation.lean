import Singularity.CayleyExcess
import Singularity.DilationGeometry
import Singularity.VisualPoissonRay

/-!
# Uniform separation of balls on opposite sides of an axis point

Balls may have growing radii. What matters is that each radius is smaller
than the distance of its center from the intermediate axis point by log 64.
Their endpoint pairs then have uniformly bounded triangle excess at that point.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Logarithmic height parametrizes the full vertical line isometrically. -/
theorem verticalHeightRay_dist_eq (w : ℍ) (s t : ℝ) :
    dist (verticalHeightRay w s) (verticalHeightRay w t) = |s - t| := by
  rw [UpperHalfPlane.dist_of_re_eq (show (verticalHeightRay w s).re = (verticalHeightRay w t).re from rfl)]
  change dist (Real.log (Real.exp s * w.im)) (Real.log (Real.exp t * w.im)) = _
  rw [Real.log_mul (Real.exp_ne_zero _) w.im_pos.ne', Real.log_mul (Real.exp_ne_zero _) w.im_pos.ne',
    Real.log_exp, Real.log_exp, Real.dist_eq]
  congr 1
  ring

/-- Dilation translates the logarithmic parameter on the axis through i. -/
theorem verticalHeightRay_I_dilation (c t : ℝ) :
    dilationMatrix c • verticalHeightRay UpperHalfPlane.I t = verticalHeightRay UpperHalfPlane.I (c + t) := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change (dilationMatrix c • verticalHeightRay UpperHalfPlane.I t).re = _
    rw [dilationMatrix_smul_re]
    simp [verticalHeightRay]
  · change (dilationMatrix c • verticalHeightRay UpperHalfPlane.I t).im = _
    rw [dilationMatrix_smul_im]
    simp [verticalHeightRay, Real.exp_add]

/-- Points on opposite halves of the axis, each at least distance one from i,
have disk separation at least one quarter. -/
theorem opposite_axis_cayley_separation (a b : ℝ) (ha : a ≤ -1) (hb : 1 ≤ b) :
    1 / 4 ≤ dist (halfPlaneCayley (verticalHeightRay UpperHalfPlane.I a))
      (halfPlaneCayley (verticalHeightRay UpperHalfPlane.I b)) := by
  have hd (t : ℝ) : dist (verticalHeightRay UpperHalfPlane.I t) UpperHalfPlane.I = |t| := by
    simpa only [verticalHeightRay_zero, sub_zero] using verticalHeightRay_dist_eq UpperHalfPlane.I t 0
  have hab : dist (verticalHeightRay UpperHalfPlane.I a) (verticalHeightRay UpperHalfPlane.I b) = b - a := by
    rw [verticalHeightRay_dist_eq, abs_of_nonpos (by linarith)]
    ring
  have he := halfPlaneCayley_dist_lower_of_excess
    (verticalHeightRay UpperHalfPlane.I a) (verticalHeightRay UpperHalfPlane.I b) 0
    (by rw [hab]; linarith) (by rw [hd, hd, hab, abs_of_nonpos (by linarith : a ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ b)]; linarith)
  simpa only [neg_zero, zero_div, Real.exp_zero] using he

/-- A ball whose radius leaves a log 64 margin from i has disk diameter from
its axis center at most one sixteenth. -/
theorem cayley_near_axis_bound (t r : ℝ) (z : ℍ)
    (hz : dist z (verticalHeightRay UpperHalfPlane.I t) ≤ r)
    (hmargin : r + Real.log 64 ≤ |t|) :
    dist (halfPlaneCayley (verticalHeightRay UpperHalfPlane.I t)) (halfPlaneCayley z) ≤ 1 / 16 := by
  have hd : dist (verticalHeightRay UpperHalfPlane.I t) UpperHalfPlane.I = |t| := by
    simpa only [verticalHeightRay_zero, sub_zero] using verticalHeightRay_dist_eq UpperHalfPlane.I t 0
  have hh := halfPlaneCayley_dist_le (verticalHeightRay UpperHalfPlane.I t) z r
    (by simpa only [dist_comm] using hz)
  rw [hd] at hh
  apply hh.trans
  calc
    _ = 4 * Real.exp (r - |t|) := by rw [mul_assoc, ← Real.exp_add]; rfl
    _ ≤ 4 * Real.exp (-Real.log 64) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ = 1 / 16 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 64)]; norm_num

/-- Endpoint balls on opposite sides of i give bounded triangle excess,
even when their radii grow, provided the logarithmic margins hold. -/
theorem opposite_axis_balls_excess (a b r₁ r₂ : ℝ) (x y : ℍ)
    (ha : a ≤ -1) (hb : 1 ≤ b)
    (hx : dist x (verticalHeightRay UpperHalfPlane.I a) ≤ r₁)
    (hy : dist y (verticalHeightRay UpperHalfPlane.I b) ≤ r₂)
    (hm₁ : r₁ + Real.log 64 ≤ -a) (hm₂ : r₂ + Real.log 64 ≤ b) :
    dist x UpperHalfPlane.I + dist y UpperHalfPlane.I - dist x y ≤ 2 * Real.log 32 := by
  have hx' := cayley_near_axis_bound a r₁ x hx (by rwa [abs_of_nonpos (by linarith : a ≤ 0)])
  have hy' := cayley_near_axis_bound b r₂ y hy (by rwa [abs_of_nonneg (by linarith : 0 ≤ b)])
  have hs := opposite_axis_cayley_separation a b ha hb
  have ht := dist_triangle4 (halfPlaneCayley (verticalHeightRay UpperHalfPlane.I a))
    (halfPlaneCayley x) (halfPlaneCayley y) (halfPlaneCayley (verticalHeightRay UpperHalfPlane.I b))
  rw [dist_comm (halfPlaneCayley y)] at ht
  have hsep : (1 / 8 : ℝ) ≤ dist (halfPlaneCayley x) (halfPlaneCayley y) := by linarith
  have he := hyperbolic_excess_of_cayley_separation x y (1 / 8) (by norm_num) hsep
  norm_num only [show (4 : ℝ) / (1 / 8) = 32 by norm_num] at he
  exact he

/-- The same bound at any intermediate point of an isometric image of the axis. -/
theorem axis_balls_excess (g : SL(2, ℝ)) (a c b r₁ r₂ : ℝ) (x y : ℍ)
    (ha : a + 1 ≤ c) (hb : c + 1 ≤ b)
    (hx : dist x (g • verticalHeightRay UpperHalfPlane.I a) ≤ r₁)
    (hy : dist y (g • verticalHeightRay UpperHalfPlane.I b) ≤ r₂)
    (hm₁ : r₁ + Real.log 64 ≤ c - a) (hm₂ : r₂ + Real.log 64 ≤ b - c) :
    dist x (g • verticalHeightRay UpperHalfPlane.I c) +
      dist y (g • verticalHeightRay UpperHalfPlane.I c) - dist x y ≤ 2 * Real.log 32 := by
  let h := g * dilationMatrix c
  have haxis (t : ℝ) : h • verticalHeightRay UpperHalfPlane.I (t - c) =
      g • verticalHeightRay UpperHalfPlane.I t := by
    dsimp [h]
    rw [mul_smul, verticalHeightRay_I_dilation]
    congr 2
    ring
  have hcenter : h • UpperHalfPlane.I = g • verticalHeightRay UpperHalfPlane.I c := by
    simpa only [sub_self, verticalHeightRay_zero] using haxis c
  have hx' : dist (h⁻¹ • x) (verticalHeightRay UpperHalfPlane.I (a - c)) ≤ r₁ := by
    rw [← dist_smul h, smul_inv_smul, haxis]
    exact hx
  have hy' : dist (h⁻¹ • y) (verticalHeightRay UpperHalfPlane.I (b - c)) ≤ r₂ := by
    rw [← dist_smul h, smul_inv_smul, haxis]
    exact hy
  have he := opposite_axis_balls_excess (a - c) (b - c) r₁ r₂ (h⁻¹ • x) (h⁻¹ • y)
    (by linarith) (by linarith) hx' hy' (by linarith) hm₂
  have hd (z : ℍ) : dist (h⁻¹ • z) UpperHalfPlane.I = dist z (g • verticalHeightRay UpperHalfPlane.I c) := by
    rw [← dist_smul h, smul_inv_smul, hcenter]
  simpa only [hd, dist_smul] using he

end Singularity
