import Singularity.HyperbolicTraceNormalization

/-!
# Negative traces and positive dilation normalization

For determinant-one two-by-two matrices, tr(g²) = tr(g)² - 2. Squaring a
hyperbolic element therefore gives trace > 2 regardless of its original sign.
-/

noncomputable section
open scoped MatrixGroups

namespace Singularity

/-- The two-by-two trace identity for a square in SL(2,ℝ). -/
theorem slTwo_trace_square (g : SL(2, ℝ)) :
    (g ^ 2) 0 0 + (g ^ 2) 1 1 = (g 0 0 + g 1 1) ^ 2 - 2 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith

/-- Either sign of hyperbolic trace gives a square of trace greater than two. -/
theorem slTwo_trace_square_gt_two (g : SL(2, ℝ)) (hg : 2 < |g 0 0 + g 1 1|) :
    2 < (g ^ 2) 0 0 + (g ^ 2) 1 1 := by
  rw [slTwo_trace_square]
  have hs := sq_abs (g 0 0 + g 1 1)
  nlinarith

/-- The square of every real hyperbolic matrix is conjugate to a positive dilation. -/
theorem exists_dilation_conjugacy_of_abs_trace (g : SL(2, ℝ))
    (hg : 2 < |g 0 0 + g 1 1|) :
    ∃ t : ℝ, 0 < t ∧ ∃ B : SL(2, ℝ), g ^ 2 = B * dilationMatrix t * B⁻¹ :=
  exists_dilation_conjugacy_of_trace_gt_two (g ^ 2) (slTwo_trace_square_gt_two g hg)

end Singularity
