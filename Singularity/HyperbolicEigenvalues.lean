import Singularity.DilationOrbit

/-!
# Positive eigenvalues for a trace greater than two

The roots of X² - T X + 1 are explicit positive reciprocal numbers. Their
larger root determines the positive dilation parameter used for normalization.
-/

noncomputable section
open scoped MatrixGroups

namespace Singularity

/-- The expanding root of the determinant-one characteristic polynomial. -/
def expandingRoot (T : ℝ) : ℝ := (T + Real.sqrt (T ^ 2 - 4)) / 2

/-- The contracting root of the determinant-one characteristic polynomial. -/
def contractingRoot (T : ℝ) : ℝ := (T - Real.sqrt (T ^ 2 - 4)) / 2

theorem hyperbolicRoots_sum (T : ℝ) : expandingRoot T + contractingRoot T = T := by
  unfold expandingRoot contractingRoot
  ring

theorem hyperbolicRoots_mul {T : ℝ} (hT : 2 < T) :
    expandingRoot T * contractingRoot T = 1 := by
  have hs := Real.sq_sqrt (show 0 ≤ T ^ 2 - 4 by nlinarith)
  unfold expandingRoot contractingRoot
  nlinarith

theorem expandingRoot_gt_one {T : ℝ} (hT : 2 < T) : 1 < expandingRoot T := by
  unfold expandingRoot
  nlinarith [Real.sqrt_nonneg (T ^ 2 - 4)]

theorem contractingRoot_pos {T : ℝ} (hT : 2 < T) : 0 < contractingRoot T := by
  have hmul := hyperbolicRoots_mul hT
  have hpos := expandingRoot_gt_one hT
  nlinarith

theorem contractingRoot_eq_inv {T : ℝ} (hT : 2 < T) :
    contractingRoot T = (expandingRoot T)⁻¹ := by
  have hn : expandingRoot T ≠ 0 := ne_of_gt (lt_trans zero_lt_one (expandingRoot_gt_one hT))
  apply (mul_left_cancel₀ hn)
  rw [hyperbolicRoots_mul hT, mul_inv_cancel₀ hn]

theorem hyperbolicRoots_ne {T : ℝ} (hT : 2 < T) : expandingRoot T ≠ contractingRoot T := by
  intro h
  have hmul := hyperbolicRoots_mul hT
  have hpos := expandingRoot_gt_one hT
  rw [← h] at hmul
  nlinarith

/-- The logarithmic parameter of the expanding eigenvalue is positive. -/
theorem hyperbolicParameter_pos {T : ℝ} (hT : 2 < T) : 0 < 2 * Real.log (expandingRoot T) :=
  mul_pos (by norm_num) (Real.log_pos (expandingRoot_gt_one hT))

/-- Converting the expanding eigenvalue to the diagonal matrix parameter. -/
theorem dilationMatrix_log (r : ℝ) (hr : 0 < r) :
    (dilationMatrix (2 * Real.log r) : Matrix (Fin 2) (Fin 2) ℝ) = !![r, 0; 0, r⁻¹] := by
  simp [dilationMatrix, Real.exp_log hr]

end Singularity
