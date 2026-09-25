import Singularity.HyperbolicNormalization

/-!
# Normalization from the trace condition

Two elementary changes of coordinates suffice to make the lower-left entry
nonzero unless it already is. The explicit eigenvector construction then gives
an SL(2,ℝ) conjugacy with a positive dilation for every matrix of trace > 2.
-/

noncomputable section
open scoped Classical MatrixGroups

namespace Singularity

/-- A determinant-one lower triangular shear. -/
def lowerShearMatrix (u : ℝ) : SL(2, ℝ) := ⟨!![1, 0; u, 1], by simp⟩

theorem lowerShearMatrix_add (u v : ℝ) :
    lowerShearMatrix (u + v) = lowerShearMatrix u * lowerShearMatrix v := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [lowerShearMatrix, add_comm]

theorem lowerShearMatrix_inv (u : ℝ) : (lowerShearMatrix u)⁻¹ = lowerShearMatrix (-u) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← lowerShearMatrix_add]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lowerShearMatrix]

/-- Explicit coordinates of the conjugate by a lower triangular shear. -/
theorem lowerShearMatrix_conjugate (u : ℝ) (g : SL(2, ℝ)) :
    ((lowerShearMatrix u * g * (lowerShearMatrix u)⁻¹ : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![g 0 0 - u * g 0 1, g 0 1;
        g 1 0 + u * (g 0 0 - g 1 1) - u ^ 2 * g 0 1, g 1 1 + u * g 0 1] := by
  rw [lowerShearMatrix_inv]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [lowerShearMatrix, add_comm] <;> ring

/-- Shear conjugation preserves the two-by-two trace. -/
theorem lowerShearMatrix_conjugate_trace (u : ℝ) (g : SL(2, ℝ)) :
    (lowerShearMatrix u * g * (lowerShearMatrix u)⁻¹) 0 0 +
      (lowerShearMatrix u * g * (lowerShearMatrix u)⁻¹) 1 1 = g 0 0 + g 1 1 := by
  rw [lowerShearMatrix_conjugate]
  simp

/-- With trace greater than two, one of two fixed shears gives nonzero lower-left entry. -/
theorem exists_shear_lowerLeft_ne_zero (g : SL(2, ℝ)) (hT : 2 < g 0 0 + g 1 1)
    (hc : g 1 0 = 0) :
    ∃ u : ℝ, (lowerShearMatrix u * g * (lowerShearMatrix u)⁻¹) 1 0 ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := h 1
  have h2 := h 2
  rw [lowerShearMatrix_conjugate] at h1 h2
  simp [hc] at h1 h2
  have hb : g 0 1 = 0 := by linarith
  have had : g 0 0 = g 1 1 := by linarith
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  rw [hb, zero_mul, sub_zero, had] at hdet
  nlinarith

/-- Every real determinant-one matrix with trace > 2 is conjugate in SL(2,ℝ)
to the positive dilation matrix. -/
theorem exists_dilation_conjugacy_of_trace_gt_two (g : SL(2, ℝ))
    (hT : 2 < g 0 0 + g 1 1) :
    ∃ t : ℝ, 0 < t ∧ ∃ B : SL(2, ℝ), g = B * dilationMatrix t * B⁻¹ := by
  by_cases hc : g 1 0 = 0
  · obtain ⟨u, hu⟩ := exists_shear_lowerLeft_ne_zero g hT hc
    obtain ⟨t, ht, B, hB⟩ := exists_dilation_conjugacy_of_lowerLeft_ne_zero
      (lowerShearMatrix u * g * (lowerShearMatrix u)⁻¹)
      (by rwa [lowerShearMatrix_conjugate_trace]) hu
    refine ⟨t, ht, (lowerShearMatrix u)⁻¹ * B, ?_⟩
    have hh := congrArg (fun k : SL(2, ℝ) => (lowerShearMatrix u)⁻¹ * k * lowerShearMatrix u) hB
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
  · exact exists_dilation_conjugacy_of_lowerLeft_ne_zero g hT hc

end Singularity
