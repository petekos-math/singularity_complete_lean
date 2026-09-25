import Singularity.ParabolicInfiniteOrder
import Singularity.BoundaryPairTransitivity
import Singularity.VisualPoissonRay

/-!
# Parabolic normalization in a prescribed boundary chart

A parabolic fixing infinity is a nontrivial projective upper shear. Thus any
chosen special-linear chart taking infinity to its fixed point normalizes it
as a shear; the chart need not come from its trace classification.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Conjugating a projective parabolic preserves its trace classification. -/
theorem ProjectiveParabolic.conjugate (g : PSL(2, ℝ)) (hg : ProjectiveParabolic g)
    (B : SL(2, ℝ)) : ProjectiveParabolic (slTwoProjective B * g * (slTwoProjective B)⁻¹) := by
  obtain ⟨hne, a, ha, ht⟩ := hg
  refine ⟨?_, B * a * B⁻¹, by simp only [map_mul, map_inv, ha], ?_⟩
  · intro he
    apply hne
    have h := congrArg (fun k : PSL(2, ℝ) => (slTwoProjective B)⁻¹ * k * slTwoProjective B) he
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using h
  · rwa [slTwo_trace_conjugate]

/-- A parabolic fixing infinity is exactly a nonzero projective shear. -/
theorem ProjectiveParabolic.eq_shear_of_fix_infty (g : PSL(2, ℝ)) (hg : ProjectiveParabolic g)
    (hfix : g • (∞ : OnePoint ℝ) = ∞) :
    ∃ u : ℝ, u ≠ 0 ∧ g = slTwoProjective (upperShearMatrix u) := by
  obtain ⟨hne, a, ha, ht⟩ := hg
  have hfixa : a • (∞ : OnePoint ℝ) = ∞ := by
    rw [← slTwoProjective_smul_boundary, ha]
    exact hfix
  have hc := (compactBoundary_fixes_infty_iff a).mp hfixa
  have hdet : a 0 0 * a 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using a.property
  have hd : a 0 0 = a 1 1 := by nlinarith [sq_nonneg (a 0 0 - a 1 1)]
  obtain ⟨u, hu⟩ := slTwo_triangular_projective_shear a hc hd
  refine ⟨u, ?_, ha.symm.trans hu⟩
  intro hz
  apply hne
  rw [← ha, hu, hz, upperShearMatrix_zero, map_one]

/-- Every chart taking infinity to a parabolic fixed point normalizes that
parabolic as a nontrivial shear, including negative-trace lifts. -/
theorem ProjectiveParabolic.shear_in_chart (g : PSL(2, ℝ)) (hg : ProjectiveParabolic g)
    (B : SL(2, ℝ)) (p : OnePoint ℝ) (hB : B • (∞ : OnePoint ℝ) = p)
    (hfix : g • p = p) :
    ∃ u : ℝ, u ≠ 0 ∧ g = slTwoProjective (B * upperShearMatrix u * B⁻¹) := by
  let q := (slTwoProjective B)⁻¹ * g * slTwoProjective B
  have hq : ProjectiveParabolic q := by
    simpa only [map_inv, inv_inv] using hg.conjugate g B⁻¹
  have hqfix : q • (∞ : OnePoint ℝ) = ∞ := by
    dsimp [q]
    rw [mul_smul, mul_smul, slTwoProjective_smul_boundary, hB, hfix, ← hB]
    change (slTwoProjective B)⁻¹ • ((slTwoProjective B) • (∞ : OnePoint ℝ)) = ∞
    exact inv_smul_smul _ _
  obtain ⟨u, hu, he⟩ := hq.eq_shear_of_fix_infty q hqfix
  refine ⟨u, hu, ?_⟩
  have h := congrArg (fun k : PSL(2, ℝ) => slTwoProjective B * k * (slTwoProjective B)⁻¹) he
  simpa only [q, map_mul, map_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, mul_one] using h

/-- The inverse zero-pole chart takes infinity to zero. -/
theorem boundaryPoleMatrix_inv_smul_infty_zero :
    (boundaryPoleMatrix 0)⁻¹ • (∞ : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by
  have h : boundaryPoleMatrix 0 • ((0 : ℝ) : OnePoint ℝ) = (∞ : OnePoint ℝ) := by
    rw [compactBoundary_smul_coe_formula]
    norm_num [boundaryPoleMatrix]
  rw [← h, inv_smul_smul]

end Singularity
