import Singularity.BoundaryPairTransitivity

/-!
# Interior bounds from two finite endpoint images

If the images of zero and infinity stay in a bounded real interval, the
image of any fixed point of the upper half-plane stays bounded in the complex
plane. This is the elementary estimate used to locate ideal orbit limits in
closed invariant boundary sets.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Bounds on the two numerator coefficients relative to their denominator
coefficients give a uniform Euclidean bound at every fixed interior point. -/
theorem slTwo_interior_norm_bound_of_coefficients (g : SL(2, ℝ)) (z : ℍ)
    {M : ℝ} (hM : 0 ≤ M)
    (ha : |g 0 0| ≤ M * |g 1 0|) (hb : |g 0 1| ≤ M * |g 1 1|) :
    ‖((g • z : ℍ) : ℂ)‖ ≤ M * (1 + 2 * ‖(z : ℂ)‖ / z.im) := by
  let D : ℂ := (g 1 0 : ℂ) * (z : ℂ) + (g 1 1 : ℂ)
  have hD : D ≠ 0 := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  have hc : |g 1 0| * z.im ≤ ‖D‖ := by
    have h := Complex.abs_im_le_norm D
    simpa [D, Complex.mul_im, abs_mul, abs_of_pos z.im_pos] using h
  have hcz : |g 1 0| * ‖(z : ℂ)‖ ≤ ‖D‖ * ‖(z : ℂ)‖ / z.im := by
    apply (le_div_iff₀ z.im_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg (z : ℂ))]
  have hd : |g 1 1| ≤ ‖D‖ + |g 1 0| * ‖(z : ℂ)‖ := by
    have h := norm_sub_le D ((g 1 0 : ℂ) * (z : ℂ))
    simpa only [D, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs] using h
  have hnum : ‖(g 0 0 : ℂ) * (z : ℂ) + (g 0 1 : ℂ)‖ ≤
      M * (1 + 2 * ‖(z : ℂ)‖ / z.im) * ‖D‖ := by
    have h := norm_add_le ((g 0 0 : ℂ) * (z : ℂ)) (g 0 1 : ℂ)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    have hz := mul_le_mul_of_nonneg_right ha (norm_nonneg (z : ℂ))
    have hcz' := mul_le_mul_of_nonneg_left hcz hM
    have hd' := mul_le_mul_of_nonneg_left hd hM
    calc
      _ ≤ M * (‖D‖ + 2 * (‖D‖ * ‖(z : ℂ)‖ / z.im)) := by nlinarith
      _ = _ := by ring
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hD)).mpr hnum

/-- A bounded pair of finite endpoint images controls the interior image. -/
theorem slTwo_interior_norm_bound_of_endpoint_images (g : SL(2, ℝ)) (z : ℍ)
    {M : ℝ} (hM : 0 ≤ M)
    (hinfty : ∃ u : ℝ, |u| ≤ M ∧ g • (∞ : OnePoint ℝ) = (u : OnePoint ℝ))
    (h0 : ∃ v : ℝ, |v| ≤ M ∧ g • ((0 : ℝ) : OnePoint ℝ) = (v : OnePoint ℝ)) :
    ‖((g • z : ℍ) : ℂ)‖ ≤ M * (1 + 2 * ‖(z : ℂ)‖ / z.im) := by
  obtain ⟨u, hu, hgu⟩ := hinfty
  obtain ⟨v, hv, hgv⟩ := h0
  have hc : g 1 0 ≠ 0 := by
    intro hc
    rw [compactBoundary_smul_infty_formula, ite_eq_left hc] at hgu
    exact (OnePoint.infty_ne_coe u) hgu
  have hd : g 1 1 ≠ 0 := by
    intro hd
    rw [compactBoundary_smul_coe_formula] at hgv
    simp [hd] at hgv
  rw [compactBoundary_smul_infty_formula, ite_eq_right hc] at hgu
  rw [compactBoundary_smul_coe_formula] at hgv
  simp only [mul_zero, zero_add, ite_eq_right hd] at hgv
  have ha : g 0 0 = u * g 1 0 := (div_eq_iff hc).mp (OnePoint.coe_injective hgu)
  have hb : g 0 1 = v * g 1 1 := (div_eq_iff hd).mp (OnePoint.coe_injective hgv)
  apply slTwo_interior_norm_bound_of_coefficients g z hM
  · rw [ha, abs_mul]
    exact mul_le_mul_of_nonneg_right hu (abs_nonneg _)
  · rw [hb, abs_mul]
    exact mul_le_mul_of_nonneg_right hv (abs_nonneg _)

end Singularity
