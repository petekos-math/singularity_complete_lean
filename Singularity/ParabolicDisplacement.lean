import Singularity.ShearContraction
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Sublinear displacement of parabolic powers

Upper unipotent matrices act by horizontal translations. Their powers have
hyperbolic displacement bounded by a logarithm, hence displacement divided by
the exponent tends to zero. The result holds at every basepoint and survives
special-linear conjugation.
-/

noncomputable section
open Filter
open scoped Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- Upper shears add their parameters under multiplication. -/
theorem upperShearMatrix_add (u v : ℝ) :
    upperShearMatrix (u + v) = upperShearMatrix u * upperShearMatrix v := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [upperShearMatrix, add_comm]

/-- The nth power is translation by n times the original parameter. -/
theorem upperShearMatrix_pow (u : ℝ) (n : ℕ) :
    upperShearMatrix u ^ n = upperShearMatrix ((n : ℝ) * u) := by
  induction n with
  | zero => simp [upperShearMatrix_zero]
  | succ n ih => rw [pow_succ, ih, ← upperShearMatrix_add]; congr 1; push_cast; ring

/-- The upper shear acts as horizontal translation on the upper half-plane. -/
theorem upperShearMatrix_smul_coe (u : ℝ) (z : ℍ) :
    ((upperShearMatrix u • z : ℍ) : ℂ) = (z : ℂ) + u := by
  have h := UpperHalfPlane.coe_specialLinearGroup_apply (upperShearMatrix u) z
  simpa [upperShearMatrix] using h

/-- Exact displacement at i. -/
theorem upperShearMatrix_dist_I (u : ℝ) :
    dist UpperHalfPlane.I (upperShearMatrix u • UpperHalfPlane.I) = 2 * Real.arsinh (|u| / 2) := by
  rw [UpperHalfPlane.dist_eq]
  have him : (upperShearMatrix u • UpperHalfPlane.I).im = 1 := by
    change (((upperShearMatrix u • UpperHalfPlane.I : ℍ) : ℂ)).im = 1
    rw [upperShearMatrix_smul_coe]
    simp
  rw [him, UpperHalfPlane.I_im]
  simp only [Real.sqrt_one, mul_one, upperShearMatrix_smul_coe, dist_eq_norm]
  rw [show (UpperHalfPlane.I : ℂ) - ((UpperHalfPlane.I : ℂ) + (u : ℂ)) = -(u : ℂ) by ring,
    norm_neg, Complex.norm_real, Real.norm_eq_abs]

/-- A convenient logarithmic upper bound on inverse hyperbolic sine. -/
theorem arsinh_le_log_two_mul_add_one (x : ℝ) (hx : 0 ≤ x) :
    Real.arsinh x ≤ Real.log (2 * x + 1) := by
  have hs : Real.sqrt (1 + x ^ 2) ≤ x + 1 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  apply Real.log_le_log
  · have hp : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
    linarith
  · linarith

/-- Parabolic translation displacement is bounded logarithmically in its parameter. -/
theorem upperShearMatrix_dist_I_le_log (u : ℝ) :
    dist UpperHalfPlane.I (upperShearMatrix u • UpperHalfPlane.I) ≤ 2 * Real.log (|u| + 1) := by
  rw [upperShearMatrix_dist_I]
  have h := mul_le_mul_of_nonneg_left (arsinh_le_log_two_mul_add_one (|u| / 2) (by positivity))
    (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1
  congr 2
  ring

/-- Logarithmic growth of an affine function of n is sublinear. -/
theorem log_nat_mul_add_one_div_tendsto (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => Real.log (c * n + 1) / (n : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hn
  have hconst : Tendsto (fun n : ℕ => Real.log (c + 1) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero (fun n => div_nonneg (Real.log_nonneg (by nlinarith [mul_nonneg hc (Nat.cast_nonneg (α := ℝ) n)])) (Nat.cast_nonneg n))
    (fun n => ?_) (by simpa only [zero_add] using hconst.add hl)
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [← Real.log_mul (by positivity : c + 1 ≠ 0) (by positivity : (n : ℝ) + 1 ≠ 0)]
  apply Real.log_le_log (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The displacement of the actual parabolic powers, divided by n, tends to zero. -/
theorem upperShearMatrix_displacement_sublinear (u : ℝ) :
    Tendsto (fun n : ℕ => dist UpperHalfPlane.I ((upperShearMatrix u) ^ n • UpperHalfPlane.I) /
      (n : ℝ)) atTop (𝓝 0) := by
  have hlim := (log_nat_mul_add_one_div_tendsto |u| (abs_nonneg u)).const_mul 2
  apply squeeze_zero (fun n => div_nonneg dist_nonneg (Nat.cast_nonneg n)) (fun n => ?_)
    (by simpa only [mul_zero] using hlim)
  rw [upperShearMatrix_pow]
  have h := div_le_div_of_nonneg_right (upperShearMatrix_dist_I_le_log ((n : ℝ) * u))
    (Nat.cast_nonneg n)
  simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), mul_comm (n : ℝ) |u|, mul_div_assoc] using h

/-- Changing the basepoint changes displacement by at most twice their distance. -/
theorem slTwo_displacement_le_change_basepoint (g : SL(2, ℝ)) (z w : ℍ) :
    dist z (g • z) ≤ 2 * dist z w + dist w (g • w) := by
  have h₁ := dist_triangle z w (g • z)
  have h₂ := dist_triangle w (g • w) (g • z)
  have he : dist (g • w) (g • z) = dist w z := dist_smul g w z
  rw [he, dist_comm w z] at h₂
  linarith

/-- Parabolic displacement is sublinear at every basepoint. -/
theorem upperShearMatrix_displacement_sublinear_at (u : ℝ) (z : ℍ) :
    Tendsto (fun n : ℕ => dist z ((upperShearMatrix u) ^ n • z) / (n : ℝ)) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ => (2 * dist z UpperHalfPlane.I) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero (fun n => div_nonneg dist_nonneg (Nat.cast_nonneg n)) (fun n => ?_)
    (by simpa only [zero_add] using hc.add (upperShearMatrix_displacement_sublinear u))
  rw [← add_div]
  exact div_le_div_of_nonneg_right (slTwo_displacement_le_change_basepoint _ z UpperHalfPlane.I)
    (Nat.cast_nonneg n)

/-- Conjugating a parabolic preserves sublinear displacement. -/
theorem conjugate_upperShearMatrix_displacement_sublinear (B : SL(2, ℝ)) (u : ℝ) (z : ℍ) :
    Tendsto (fun n : ℕ => dist z ((B * upperShearMatrix u * B⁻¹) ^ n • z) / (n : ℝ)) atTop (𝓝 0) := by
  have he (n : ℕ) : (B * upperShearMatrix u * B⁻¹) ^ n = B * upperShearMatrix u ^ n * B⁻¹ := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; group
  have hd (n : ℕ) : dist z ((B * upperShearMatrix u * B⁻¹) ^ n • z) =
      dist (B⁻¹ • z) (upperShearMatrix u ^ n • (B⁻¹ • z)) := by
    rw [he, mul_smul, mul_smul, ← dist_smul B (B⁻¹ • z), smul_inv_smul]
  simpa only [hd] using upperShearMatrix_displacement_sublinear_at u (B⁻¹ • z)

end Singularity
