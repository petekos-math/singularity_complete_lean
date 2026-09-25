import Singularity.HyperbolicEigenvalues

/-!
# Explicit determinant-one hyperbolic conjugators

When the lower-left entry is nonzero, two explicit eigenvectors form a basis.
Rescaling the expanding eigenvector by the determinant makes the conjugating
matrix belong to SL(2,ℝ), including when the unscaled basis has negative orientation.
-/

noncomputable section
open scoped Classical MatrixGroups

namespace Singularity

/-- A trace-greater-than-two matrix with nonzero lower-left entry is an SL conjugate
of a positive dilation. -/
theorem exists_dilation_conjugacy_of_lowerLeft_ne_zero (g : SL(2, ℝ))
    (hT : 2 < g 0 0 + g 1 1) (hc : g 1 0 ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∃ B : SL(2, ℝ), g = B * dilationMatrix t * B⁻¹ := by
  let r := expandingRoot (g 0 0 + g 1 1)
  let s := contractingRoot (g 0 0 + g 1 1)
  have hr : 1 < r := expandingRoot_gt_one hT
  have hrs : r ≠ s := hyperbolicRoots_ne hT
  have hsum : r + s = g 0 0 + g 1 1 := hyperbolicRoots_sum _
  have hprod : r * s = 1 := hyperbolicRoots_mul hT
  have hs : s = r⁻¹ := contractingRoot_eq_inv hT
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  let D := g 1 0 * (r - s)
  have hD : D ≠ 0 := mul_ne_zero hc (sub_ne_zero.mpr hrs)
  let B : SL(2, ℝ) := ⟨!![(r - g 1 1) / D, s - g 1 1; g 1 0 / D, g 1 0], by
    simp only [Matrix.det_fin_two]
    change (r - g 1 1) / D * g 1 0 - (s - g 1 1) * (g 1 0 / D) = 1
    field_simp [hD]
    dsimp [D]
    ring⟩
  have hdil : (dilationMatrix (2 * Real.log r) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r, 0; 0, s] := by
    rw [dilationMatrix_log r (by linarith), hs]
  have hinter : g * B = B * dilationMatrix (2 * Real.log r) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change ((g : Matrix (Fin 2) (Fin 2) ℝ) * (B : Matrix (Fin 2) (Fin 2) ℝ)) i j =
      ((B : Matrix (Fin 2) (Fin 2) ℝ) * (dilationMatrix (2 * Real.log r) : Matrix (Fin 2) (Fin 2) ℝ)) i j
    rw [hdil]
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two]
    · field_simp [hD]
      nlinarith
    · nlinarith
    · field_simp [hD]
      ring
    · ring
  exact ⟨2 * Real.log r, hyperbolicParameter_pos hT, B, eq_mul_inv_of_mul_eq hinter⟩

end Singularity
