import Singularity.ConjugateSubgroup
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-!
# Trace identities for elliptic and parabolic elements

An elliptic element fixing `i` is a rotation matrix. Its commutator with any
matrix has trace at least two, with equality only when that matrix also fixes
`i`. These explicit identities will remove cocompactness from the existence
of a hyperbolic element in a nonelementary group.
-/

noncomputable section
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- Trace is unchanged by special-linear conjugation. -/
theorem slTwo_trace_conjugate (g B : SL(2, ℝ)) :
    (B * g * B⁻¹) 0 0 + (B * g * B⁻¹) 1 1 = g 0 0 + g 1 1 := by
  have h := Matrix.trace_mul_cycle (B : Matrix (Fin 2) (Fin 2) ℝ)
    (g : Matrix (Fin 2) (Fin 2) ℝ) (B⁻¹ : SL(2, ℝ))
  simpa only [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, one_mul,
    Matrix.trace_fin_two] using h

/-- The matrices fixing `i` have the usual rotation coordinates. -/
theorem slTwo_fixes_I_iff (g : SL(2, ℝ)) :
    g • UpperHalfPlane.I = UpperHalfPlane.I ↔
      g 0 0 = g 1 1 ∧ g 0 1 = -g 1 0 := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ g) • UpperHalfPlane.I = _ ↔ _
  rw [UpperHalfPlane.gl_smul_eq_self_iff_quadratic (by simp)]
  simp [Complex.ext_iff, UpperHalfPlane.I]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The commutator trace for a matrix fixing `i` is a sum of squares. -/
theorem slTwo_rotation_commutator_trace (a g : SL(2, ℝ))
    (ha : a 0 0 = a 1 1) (hb : a 0 1 = -a 1 0) :
    (a * g * a⁻¹ * g⁻¹) 0 0 + (a * g * a⁻¹ * g⁻¹) 1 1 =
      2 + (a 1 0) ^ 2 * ((g 0 0 - g 1 1) ^ 2 + (g 0 1 + g 1 0) ^ 2) := by
  have hda := a.property
  have hdg := g.property
  simp only [Matrix.det_fin_two, ha, hb] at hda hdg
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ha, hb]
  linear_combination 2 * ((a 1 1) ^ 2 + (a 1 0) ^ 2) * hdg + 2 * hda

/-- A noncentral rotation and a nonhyperbolic commutator force the same fixed point. -/
theorem slTwo_fixes_I_of_commutator_trace_le (a g : SL(2, ℝ))
    (hfix : a • UpperHalfPlane.I = UpperHalfPlane.I) (hc : a 1 0 ≠ 0)
    (htrace : (a * g * a⁻¹ * g⁻¹) 0 0 + (a * g * a⁻¹ * g⁻¹) 1 1 ≤ 2) :
    g • UpperHalfPlane.I = UpperHalfPlane.I := by
  obtain ⟨ha, hb⟩ := (slTwo_fixes_I_iff a).mp hfix
  rw [slTwo_rotation_commutator_trace a g ha hb] at htrace
  have hsq : (g 0 0 - g 1 1) ^ 2 + (g 0 1 + g 1 0) ^ 2 ≤ 0 := by
    nlinarith [sq_pos_of_ne_zero hc]
  apply (slTwo_fixes_I_iff g).mpr
  constructor <;> nlinarith [sq_nonneg (g 0 0 - g 1 1), sq_nonneg (g 0 1 + g 1 0)]

/-- For a triangular parabolic matrix the commutator trace detects movement of infinity. -/
theorem slTwo_parabolic_commutator_trace (a g : SL(2, ℝ))
    (ha : a 0 0 = a 1 1) (hc : a 1 0 = 0) :
    (a * g * a⁻¹ * g⁻¹) 0 0 + (a * g * a⁻¹ * g⁻¹) 1 1 =
      2 + (a 0 1) ^ 2 * (g 1 0) ^ 2 := by
  have hda := a.property
  have hdg := g.property
  simp only [Matrix.det_fin_two, ha, hc] at hda hdg
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ha, hc]
  linear_combination 2 * (a 1 1) ^ 2 * hdg + 2 * hda

end Singularity
