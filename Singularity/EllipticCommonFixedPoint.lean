import Singularity.EllipticCommutator

/-!
# A common interior fixed point when all traces are nonhyperbolic

If a subgroup contains an elliptic element and no hyperbolic element, conjugate
the elliptic fixed point to `i`. The sum-of-squares commutator identity forces
every group element to fix `i`, and conjugating back gives a common fixed point.
Neither discreteness nor cocompactness is used.
-/

noncomputable section
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- Absolute trace less than two is the ellipticity condition in determinant one. -/
theorem slTwo_isElliptic_of_abs_trace_lt_two (g : SL(2, ℝ))
    (h : |g 0 0 + g 1 1| < 2) : (Matrix.SpecialLinearGroup.mapGL ℝ g).IsElliptic := by
  change (g : Matrix (Fin 2) (Fin 2) ℝ).discr < 0
  rw [Matrix.discr_fin_two, Matrix.trace_fin_two, g.property]
  nlinarith [sq_abs (g 0 0 + g 1 1), abs_nonneg (g 0 0 + g 1 1)]

/-- The elliptic fixed point is an actual point of the upper half-plane. -/
theorem slTwo_exists_fixedPoint_of_abs_trace_lt_two (g : SL(2, ℝ))
    (h : |g 0 0 + g 1 1| < 2) : ∃ z : ℍ, g • z = z := by
  let he := slTwo_isElliptic_of_abs_trace_lt_two g h
  refine ⟨UpperHalfPlane.fixedPt (Matrix.SpecialLinearGroup.mapGL ℝ g) he, ?_⟩
  exact (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt (by simp) he).mpr rfl

/-- Conjugating a subgroup preserves a bound on all of its traces. -/
theorem conjugateSubgroup_trace_bound (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ))
    (h : ∀ g : Γ, |(g : SL(2, ℝ)) 0 0 + (g : SL(2, ℝ)) 1 1| ≤ 2)
    (g : conjugateSubgroup Γ B) : |(g : SL(2, ℝ)) 0 0 + (g : SL(2, ℝ)) 1 1| ≤ 2 := by
  have ht := h (conjugateSubgroupEquiv Γ B g)
  change |(B * g * B⁻¹) 0 0 + (B * g * B⁻¹) 1 1| ≤ 2 at ht
  rwa [slTwo_trace_conjugate] at ht

/-- An elliptic element in a subgroup with no hyperbolic traces gives a common interior fixed point. -/
theorem exists_common_fixedPoint_of_elliptic (Γ : Subgroup SL(2, ℝ))
    (hbound : ∀ g : Γ, |(g : SL(2, ℝ)) 0 0 + (g : SL(2, ℝ)) 1 1| ≤ 2)
    (a : Γ) (ha : |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1| < 2) :
    ∃ z : ℍ, ∀ g : Γ, g • z = z := by
  obtain ⟨z, hz⟩ := slTwo_exists_fixedPoint_of_abs_trace_lt_two a ha
  change a • z = z at hz
  let B := z.toSL2R
  let a' := (conjugateSubgroupEquiv Γ B).symm a
  have ha' : |(a' : SL(2, ℝ)) 0 0 + (a' : SL(2, ℝ)) 1 1| < 2 := by
    change |(B⁻¹ * a * B) 0 0 + (B⁻¹ * a * B) 1 1| < 2
    rw [show (B⁻¹ * a * B) 0 0 + (B⁻¹ * a * B) 1 1 =
      (a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1 by
        simpa only [inv_inv] using slTwo_trace_conjugate (a : SL(2, ℝ)) B⁻¹]
    exact ha
  have hfix : (a' : SL(2, ℝ)) • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply (MulAction.injective B)
    change B • (a' • UpperHalfPlane.I) = B • UpperHalfPlane.I
    rw [conjugateSubgroup_hyperbolic_action]
    simpa [a', B] using hz
  have hc : (a' : SL(2, ℝ)) 1 0 ≠ 0 :=
    (slTwo_isElliptic_of_abs_trace_lt_two a' ha').c_ne_zero
  refine ⟨z, fun g => ?_⟩
  let g' := (conjugateSubgroupEquiv Γ B).symm g
  have ht := conjugateSubgroup_trace_bound Γ B hbound (a' * g' * a'⁻¹ * g'⁻¹)
  have hgt : (a' * g' * a'⁻¹ * g'⁻¹ : SL(2, ℝ)) 0 0 +
      (a' * g' * a'⁻¹ * g'⁻¹ : SL(2, ℝ)) 1 1 ≤ 2 := le_trans (le_abs_self _) ht
  have hgfix := slTwo_fixes_I_of_commutator_trace_le a' g' hfix hc hgt
  have hh := congrArg (fun w : ℍ => B • w) hgfix
  change B • (g' • UpperHalfPlane.I) = B • UpperHalfPlane.I at hh
  rw [conjugateSubgroup_hyperbolic_action] at hh
  simpa [g', B] using hh

end Singularity
