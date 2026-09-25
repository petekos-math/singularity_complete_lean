import Singularity.ParabolicFixedPointDensity
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Parabolic powers approach their ideal fixed point

The horizontal displacement of powers of a nonzero shear escapes every
Euclidean compact set. Conjugation gives convergence to a prescribed
parabolic fixed point and places every such fixed point in the orbit limit
set. Together with orbit minimality this identifies its closure exactly.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- Positive powers of either sign of nonzero shear converge to infinity
in the compactified upper half-plane. -/
theorem upperShearMatrix_pow_tendsto_infty (u : ℝ) (hu : u ≠ 0) (z : ℍ) :
    Tendsto (fun n : ℕ => hyperbolicCompactEmbedding (upperShearMatrix u ^ n • z))
      atTop (𝓝 (∞ : OnePoint ℂ)) := by
  have hnorm : Tendsto (fun n : ℕ => ‖((upperShearMatrix u ^ n • z : ℍ) : ℂ)‖)
      atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ) * |u| - ‖(z : ℂ)‖)
    · intro n
      rw [upperShearMatrix_pow, upperShearMatrix_smul_coe]
      have h := norm_sub_le ((z : ℂ) + ((n : ℝ) * u : ℝ)) (z : ℂ)
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at h
      linarith
    · simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-‖(z : ℂ)‖)
        (tendsto_natCast_atTop_atTop.atTop_mul_const (abs_pos.mpr hu))
  have hc : Tendsto (fun n : ℕ => ((upperShearMatrix u ^ n • z : ℍ) : ℂ))
      atTop (coclosedCompact ℂ) := by
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      tendsto_norm_atTop_iff_cobounded.mp hnorm
  exact OnePoint.tendsto_coe_infty.comp hc

/-- Every ideal point admits a special-linear chart taking infinity to it. -/
theorem exists_slTwo_chart_at_boundary (p : OnePoint ℝ) :
    ∃ B : SL(2, ℝ), B • (∞ : OnePoint ℝ) = p := by
  cases p with
  | infty => exact ⟨1, one_smul _ _⟩
  | coe r =>
    have h : boundaryPoleMatrix r • (r : OnePoint ℝ) = ∞ := by
      apply compactBoundary_smul_pole
      simp [boundaryPoleMatrix]
    refine ⟨(boundaryPoleMatrix r)⁻¹, ?_⟩
    rw [← h, inv_smul_smul]

/-- Powers of a projective parabolic converge from every interior point to
any prescribed ideal fixed point of that parabolic. -/
theorem ProjectiveParabolic.pow_orbit_tendsto_fixedPoint
    (g : PSL(2, ℝ)) (hg : ProjectiveParabolic g) (p : OnePoint ℝ)
    (hp : g • p = p) (z : ℍ) :
    Tendsto (fun n : ℕ => hyperbolicCompactEmbedding (g ^ n • z)) atTop
      (𝓝 (compactBoundaryEmbedding p)) := by
  obtain ⟨B, hB⟩ := exists_slTwo_chart_at_boundary p
  obtain ⟨u, hu, he⟩ := hg.shear_in_chart g B p hB hp
  have ht := (continuous_const_smul B : Continuous (fun w : OnePoint ℂ => B • w)).tendsto
    (∞ : OnePoint ℂ) |>.comp (upperShearMatrix_pow_tendsto_infty u hu (B⁻¹ • z))
  have hval (n : ℕ) : hyperbolicCompactEmbedding (g ^ n • z) =
      B • hyperbolicCompactEmbedding (upperShearMatrix u ^ n • (B⁻¹ • z)) := by
    rw [he, ← map_pow, conj_pow, slTwoProjective_smul_hyperbolic, mul_smul, mul_smul,
      hyperbolicCompactEmbedding_smul]
  have htarget : B • (∞ : OnePoint ℂ) = compactBoundaryEmbedding p := by
    rw [← hB, compactBoundaryEmbedding_smul]
    rfl
  simpa only [Function.comp_def, ← hval, htarget] using ht

/-- Every parabolic fixed point is in the ideal orbit limit set for every
choice of interior basepoint. -/
theorem projectiveParabolicFixedPoints_subset_limitSet
    (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    projectiveParabolicFixedPoints Γ ⊆ projectiveOrbitLimitSet Γ z := by
  rintro p ⟨g, hg, hp⟩
  apply mem_projectiveOrbitLimitSet_of_tendsto Γ z (fun n => g ^ n) p
  exact hg.pow_orbit_tendsto_fixedPoint (g : PSL(2, ℝ)) p hp z

/-- For a nonelementary group containing a parabolic, the ideal orbit limit
set is exactly the closure of the parabolic fixed points. -/
theorem closure_projectiveParabolicFixedPoints_eq_limitSet
    (Γ : Subgroup PSL(2, ℝ)) (hne : ProjectiveNonelementary Γ) (z : ℍ)
    (hpar : ∃ g : Γ, ProjectiveParabolic (g : PSL(2, ℝ))) :
    closure (projectiveParabolicFixedPoints Γ) = projectiveOrbitLimitSet Γ z := by
  exact subset_antisymm
    (closure_minimal (projectiveParabolicFixedPoints_subset_limitSet Γ z)
      (isClosed_projectiveOrbitLimitSet Γ z))
    (projectiveOrbitLimitSet_subset_closure_parabolicFixedPoints Γ hne z hpar)

end Singularity
