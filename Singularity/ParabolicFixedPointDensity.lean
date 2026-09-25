import Singularity.BoundaryOrbitMinimality

/-!
# Parabolic fixed points accumulate on the entire limit set

If a nonelementary projective group contains one parabolic, conjugates of
that element provide parabolic fixed points arbitrarily close to every
point of the ideal orbit limit set. Density here is relative to the limit
set, not an assertion that the limit set fills the whole boundary.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane Topology
namespace Singularity

/-- The set of boundary points fixed by nonidentity projective parabolics
belonging to the specified subgroup. -/
def projectiveParabolicFixedPoints (Γ : Subgroup PSL(2, ℝ)) : Set (OnePoint ℝ) :=
  {p | ∃ g : Γ, ProjectiveParabolic (g : PSL(2, ℝ)) ∧ g • p = p}

/-- Every projective parabolic fixes an ideal point. -/
theorem ProjectiveParabolic.exists_fixedPoint (g : PSL(2, ℝ)) (hg : ProjectiveParabolic g) :
    ∃ p : OnePoint ℝ, g • p = p := by
  obtain ⟨B, u, _, he⟩ := hg.exists_conjugate_shear g
  refine ⟨B • (∞ : OnePoint ℝ), ?_⟩
  rw [he, slTwoProjective_smul_boundary]
  simp only [mul_smul, inv_smul_smul]
  congr 1
  rw [compactBoundary_smul_infty_formula]
  simp [upperShearMatrix]

/-- Translating a parabolic fixed point yields the fixed point of the
corresponding conjugate parabolic in the same subgroup. -/
theorem projectiveParabolicFixedPoints_smul_mem
    (Γ : Subgroup PSL(2, ℝ)) (t : Γ) (p : OnePoint ℝ)
    (hp : p ∈ projectiveParabolicFixedPoints Γ) :
    t • p ∈ projectiveParabolicFixedPoints Γ := by
  obtain ⟨g, hg, hgp⟩ := hp
  refine ⟨t * g * t⁻¹, ?_, ?_⟩
  · obtain ⟨B, hB⟩ := slTwoProjective_surjective (t : PSL(2, ℝ))
    change ProjectiveParabolic ((t : PSL(2, ℝ)) * (g : PSL(2, ℝ)) * (t : PSL(2, ℝ))⁻¹)
    simpa only [hB] using hg.conjugate (g : PSL(2, ℝ)) B
  · simp only [mul_smul, inv_smul_smul, hgp]

/-- One parabolic suffices for parabolic fixed points to accumulate on every
point of the actual ideal orbit limit set. -/
theorem projectiveOrbitLimitSet_subset_closure_parabolicFixedPoints
    (Γ : Subgroup PSL(2, ℝ)) (hne : ProjectiveNonelementary Γ) (z : ℍ)
    (hpar : ∃ g : Γ, ProjectiveParabolic (g : PSL(2, ℝ))) :
    projectiveOrbitLimitSet Γ z ⊆ closure (projectiveParabolicFixedPoints Γ) := by
  obtain ⟨g, hg⟩ := hpar
  obtain ⟨p, hp⟩ := hg.exists_fixedPoint (g : PSL(2, ℝ))
  apply (projectiveOrbitLimitSet_subset_closure_boundary_orbit Γ hne z p).trans
  apply closure_mono
  rintro q ⟨t, rfl⟩
  exact projectiveParabolicFixedPoints_smul_mem Γ t p ⟨g, hg, hp⟩

end Singularity
