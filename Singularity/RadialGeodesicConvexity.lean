import Singularity.RadialCoordinate
import Singularity.HyperbolicAxisNormalization

/-!
# Geodesic convexity of radial half-planes

On an isometric image of the vertical axis, the squared Euclidean radius is
a quotient of two affine functions of exp(2t), with positive denominator.
A lower radius bound at both ends therefore holds throughout the interval.
Thus arbitrary deep endpoints can be joined without losing their radial depth.
-/

noncomputable section
open scoped MatrixGroups UpperHalfPlane
namespace Singularity

/-- Squared norm of a real affine expression on the imaginary axis. -/
theorem axis_real_affine_normSq (u v t : ℝ) :
    Complex.normSq ((u : ℂ) * (verticalHeightRay UpperHalfPlane.I t : ℂ) + (v : ℂ)) =
      u^2 * (Real.exp t)^2 + v^2 := by
  simp [Complex.normSq_apply, verticalHeightRay]
  ring

/-- The denominator in the radius formula is strictly positive. -/
theorem axis_mobius_radius_denominator_pos (g : SL(2, ℝ)) (t : ℝ) :
    0 < (g 1 0)^2 * (Real.exp t)^2 + (g 1 1)^2 := by
  have hh := Complex.normSq_pos.mpr (UpperHalfPlane.denom_ne_zero g (verticalHeightRay UpperHalfPlane.I t))
  change 0 < Complex.normSq ((g 1 0 : ℂ) * (verticalHeightRay UpperHalfPlane.I t : ℂ) + (g 1 1 : ℂ)) at hh
  rwa [axis_real_affine_normSq] at hh

/-- Exact radius along any constructed hyperbolic axis. -/
theorem axis_mobius_normSq (g : SL(2, ℝ)) (t : ℝ) :
    Complex.normSq ((g • verticalHeightRay UpperHalfPlane.I t : ℍ) : ℂ) =
      ((g 0 0)^2 * (Real.exp t)^2 + (g 0 1)^2) /
        ((g 1 0)^2 * (Real.exp t)^2 + (g 1 1)^2) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, Complex.normSq_div]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, axis_real_affine_normSq]

/-- A radial lower bound can be stated as a squared Euclidean-radius bound. -/
theorem axisRadialCoordinate_ge_iff_normSq (z : ℍ) (r : ℝ) :
    r ≤ axisRadialCoordinate z ↔ (Real.exp r)^2 ≤ Complex.normSq (z : ℂ) := by
  rw [axisRadialCoordinate_eq_log_norm, Complex.normSq_eq_norm_sq,
    sq_le_sq₀ (Real.exp_pos r).le (norm_nonneg _),
    Real.le_log_iff_exp_le (norm_pos_iff.mpr z.ne_zero)]

/-- Every point of the axis segment obeys a common endpoint lower-radius bound. -/
theorem axisRadialCoordinate_segment_lower (g : SL(2, ℝ)) (r a b t : ℝ)
    (hat : a ≤ t) (htb : t ≤ b)
    (ha : r ≤ axisRadialCoordinate (g • verticalHeightRay UpperHalfPlane.I a))
    (hb : r ≤ axisRadialCoordinate (g • verticalHeightRay UpperHalfPlane.I b)) :
    r ≤ axisRadialCoordinate (g • verticalHeightRay UpperHalfPlane.I t) := by
  rw [axisRadialCoordinate_ge_iff_normSq, axis_mobius_normSq,
    le_div_iff₀ (axis_mobius_radius_denominator_pos g a)] at ha
  rw [axisRadialCoordinate_ge_iff_normSq, axis_mobius_normSq,
    le_div_iff₀ (axis_mobius_radius_denominator_pos g b)] at hb
  rw [axisRadialCoordinate_ge_iff_normSq, axis_mobius_normSq,
    le_div_iff₀ (axis_mobius_radius_denominator_pos g t)]
  have hat' : (Real.exp a)^2 ≤ (Real.exp t)^2 :=
    pow_le_pow_left₀ (Real.exp_pos a).le (Real.exp_le_exp.mpr hat) 2
  have htb' : (Real.exp t)^2 ≤ (Real.exp b)^2 :=
    pow_le_pow_left₀ (Real.exp_pos t).le (Real.exp_le_exp.mpr htb) 2
  by_cases hsign : 0 ≤ (g 0 0)^2 - (Real.exp r)^2*(g 1 0)^2
  · have hh := mul_le_mul_of_nonneg_left hat' hsign
    nlinarith
  · have hh := mul_le_mul_of_nonpos_left htb' (le_of_not_ge hsign)
    nlinarith

/-- Arbitrary endpoints above a radial level admit a constructed geodesic
segment entirely above that same level, in any isometric chart. -/
theorem exists_radially_deep_geodesic_line (q : SL(2, ℝ)) (z w : ℍ) (r : ℝ)
    (hz : r ≤ axisRadialCoordinate (q • z)) (hw : r ≤ axisRadialCoordinate (q • w)) :
    ∃ c : ℝ → ℍ, Isometry c ∧ c 0 = z ∧ c (dist z w) = w ∧
      ∀ t ∈ Set.Icc 0 (dist z w), r ≤ axisRadialCoordinate (q • c t) := by
  obtain ⟨g,hg,hwg⟩ := exists_oriented_hyperbolic_axis z w
  refine ⟨fun t => g • verticalHeightRay UpperHalfPlane.I t, isometry_hyperbolic_axis g,
    by simpa only [verticalHeightRay_zero] using hg, hwg, ?_⟩
  intro t ht
  change r ≤ axisRadialCoordinate (q • (g • verticalHeightRay UpperHalfPlane.I t))
  rw [← mul_smul]
  apply axisRadialCoordinate_segment_lower (q*g) r 0 (dist z w) t ht.1 ht.2
  · simpa only [mul_smul, verticalHeightRay_zero, hg] using hz
  · simpa only [mul_smul, hwg] using hw

end Singularity
