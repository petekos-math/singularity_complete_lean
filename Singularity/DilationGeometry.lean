import Singularity.DilationOrbit
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# The normalized hyperbolic axis

The same diagonal matrices used for the boundary lattice act by dilation on
actual upper-half-plane points. On the vertical axis their displacement is
exactly the absolute value of the parameter.
-/

noncomputable section
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- The diagonal matrix acts by positive real scaling in the upper half plane. -/
theorem dilationMatrix_smul (t : ℝ) (z : ℍ) :
    dilationMatrix t • z = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r}) • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [dilationMatrix, Complex.real_smul]
  rw [mul_right_comm, ← Complex.exp_add]
  congr 2
  ring

/-- Real parts scale by the same factor as the boundary coordinate. -/
theorem dilationMatrix_smul_re (t : ℝ) (z : ℍ) :
    (dilationMatrix t • z).re = Real.exp t * z.re := by
  rw [dilationMatrix_smul, UpperHalfPlane.pos_real_re]

/-- Heights scale by exp(t). -/
theorem dilationMatrix_smul_im (t : ℝ) (z : ℍ) :
    (dilationMatrix t • z).im = Real.exp t * z.im := by
  rw [dilationMatrix_smul, UpperHalfPlane.pos_real_im]

/-- The vertical axis has displacement |t| under the diagonal subgroup. -/
theorem dilationMatrix_axis_dist (t : ℝ) (z : ℍ) (hz : z.re = 0) :
    dist z (dilationMatrix t • z) = |t| := by
  rw [UpperHalfPlane.dist_of_re_eq (by rw [dilationMatrix_smul_re, hz, mul_zero])]
  rw [dilationMatrix_smul_im, Real.log_mul (Real.exp_ne_zero _) z.im_pos.ne', Real.log_exp]
  rw [Real.dist_eq]
  have he : Real.log z.im - (t + Real.log z.im) = -t := by ring
  rw [he, abs_neg]

/-- Integer orbit displacement along the normalized axis. -/
theorem dilationMatrix_zpow_axis_dist (τ : ℝ) (n : ℤ) (z : ℍ) (hz : z.re = 0) :
    dist z (dilationMatrix τ ^ n • z) = |(n : ℝ) * τ| := by
  rw [← dilationMatrix_zpow]
  exact dilationMatrix_axis_dist _ z hz

/-- Dilation leaves the horizontal-to-height ratio unchanged. -/
theorem dilationMatrix_smul_ratio (t : ℝ) (z : ℍ) :
    (dilationMatrix t • z).re / (dilationMatrix t • z).im = z.re / z.im := by
  rw [dilationMatrix_smul_re, dilationMatrix_smul_im]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero t)

/-- Each cyclic orbit has a representative in the half-open height band
[1, exp(τ)). This is the normalization used for a fundamental strip. -/
theorem exists_dilationMatrix_height_band {τ : ℝ} (hτ : 0 < τ) (z : ℍ) :
    ∃ n : ℤ, 1 ≤ (dilationMatrix τ ^ n • z).im ∧
      (dilationMatrix τ ^ n • z).im < Real.exp τ := by
  let k : ℤ := ⌊Real.log z.im / τ⌋
  have hk₀ : (k : ℝ) * τ ≤ Real.log z.im :=
    (le_div_iff₀ hτ).mp (Int.floor_le _)
  have hk₁ : Real.log z.im < ((k : ℝ) + 1) * τ :=
    (div_lt_iff₀ hτ).mp (Int.lt_floor_add_one _)
  refine ⟨-k, ?_, ?_⟩ <;> rw [← dilationMatrix_zpow, dilationMatrix_smul_im]
  · have he : Real.exp (((-k : ℤ) : ℝ) * τ) * z.im =
        Real.exp (-(k : ℝ) * τ + Real.log z.im) := by
      rw [Real.exp_add, Real.exp_log z.im_pos, Int.cast_neg]
    rw [he]
    exact Real.one_le_exp_iff.mpr (by linarith)
  · have he : Real.exp (((-k : ℤ) : ℝ) * τ) * z.im =
        Real.exp (-(k : ℝ) * τ + Real.log z.im) := by
      rw [Real.exp_add, Real.exp_log z.im_pos, Int.cast_neg]
    rw [he]
    apply Real.exp_lt_exp.mpr
    nlinarith

end Singularity
