import Singularity.EllipticCommonFixedPoint
import Singularity.CocompactHyperbolic

/-!
# A common ideal fixed point when all traces are nonhyperbolic

A parabolic element with nonzero lower-left entry is explicitly conjugated to
an upper triangular matrix. The parabolic commutator identity then forces all
other elements to fix its ideal fixed point. No compactness hypothesis is used.
-/

noncomputable section
open Set OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- Conjugate a parabolic matrix by a matrix sending infinity to its repeated fixed point. -/
theorem slTwo_parabolic_normalization (g : SL(2, ℝ))
    (htrace : (g 0 0 + g 1 1) ^ 2 = 4) (hc : g 1 0 ≠ 0) :
    ∃ B : SL(2, ℝ), (B⁻¹ * g * B) 1 0 = 0 ∧
      (B⁻¹ * g * B) 0 0 = (B⁻¹ * g * B) 1 1 ∧ (B⁻¹ * g * B) 0 1 ≠ 0 := by
  let p := (g 0 0 - g 1 1) / (2 * g 1 0)
  let B : SL(2, ℝ) := ⟨!![p, -1; 1, 0], by simp⟩
  have he : ((B⁻¹ * g * B : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![g 1 0 * p + g 1 1, -g 1 0;
        g 1 0 * p ^ 2 + (g 1 1 - g 0 0) * p - g 0 1, g 0 0 - g 1 0 * p] := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [B] <;> ring
  have hp : 2 * g 1 0 * p = g 0 0 - g 1 1 := by
    dsimp [p]
    field_simp
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hq : g 1 0 * p ^ 2 + (g 1 1 - g 0 0) * p - g 0 1 = 0 := by
    dsimp [p]
    field_simp
    nlinarith [htrace, hdet]
  refine ⟨B, ?_⟩
  rw [he]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact ⟨hq, by linarith, neg_ne_zero.mpr hc⟩

/-- A parabolic element in a subgroup with no hyperbolic traces gives a common ideal fixed point. -/
theorem exists_common_boundary_fixedPoint_of_parabolic (Γ : Subgroup SL(2, ℝ))
    (hbound : ∀ g : Γ, |(g : SL(2, ℝ)) 0 0 + (g : SL(2, ℝ)) 1 1| ≤ 2)
    (a : Γ) (htrace : ((a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1) ^ 2 = 4)
    (hc : (a : SL(2, ℝ)) 1 0 ≠ 0) :
    ∃ p : OnePoint ℝ, ∀ g : Γ, g • p = p := by
  obtain ⟨B, hzero, hdiag, hne⟩ := slTwo_parabolic_normalization a htrace hc
  let a' := (conjugateSubgroupEquiv Γ B).symm a
  refine ⟨B • (∞ : OnePoint ℝ), fun g => ?_⟩
  let g' := (conjugateSubgroupEquiv Γ B).symm g
  have ht := conjugateSubgroup_trace_bound Γ B hbound (a' * g' * a'⁻¹ * g'⁻¹)
  have hgt : (a' * g' * a'⁻¹ * g'⁻¹ : SL(2, ℝ)) 0 0 +
      (a' * g' * a'⁻¹ * g'⁻¹ : SL(2, ℝ)) 1 1 ≤ 2 := le_trans (le_abs_self _) ht
  change ((a' : SL(2, ℝ)) * (g' : SL(2, ℝ)) * (a' : SL(2, ℝ))⁻¹ *
    (g' : SL(2, ℝ))⁻¹) 0 0 + ((a' : SL(2, ℝ)) * (g' : SL(2, ℝ)) *
    (a' : SL(2, ℝ))⁻¹ * (g' : SL(2, ℝ))⁻¹) 1 1 ≤ 2 at hgt
  rw [slTwo_parabolic_commutator_trace a' g' hdiag hzero] at hgt
  have hgc : (g' : SL(2, ℝ)) 1 0 = 0 := by
    have hp : 0 < (a' : SL(2, ℝ)) 0 1 ^ 2 := sq_pos_of_ne_zero hne
    by_contra hne
    have hpos := mul_pos hp (sq_pos_of_ne_zero hne)
    linarith
  have hfix := (compactBoundary_fixes_infty_iff g').mpr hgc
  have hh := congrArg (fun p : OnePoint ℝ => B • p) hfix
  change B • (g' • (∞ : OnePoint ℝ)) = B • (∞ : OnePoint ℝ) at hh
  rw [conjugateSubgroup_boundary_action] at hh
  simpa [g'] using hh

end Singularity
