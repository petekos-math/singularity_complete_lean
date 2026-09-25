import Singularity.ParabolicIdealLimits

/-!
# Dense choices of finite-strip endpoints

For a proper ideal limit set, an orbit starting outside it stays outside
and accumulates on the whole limit set. Its complement is therefore dense.
If a parabolic exists, parabolic fixed points are dense in the limit set.
In either case, parabolic points together with the complement give a dense
set on the entire ideal boundary, including across complementary gaps.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- A proper ideal limit set of a nonelementary projective group has dense
complement. This needs no finite-generation or measure-zero theorem. -/
theorem dense_compl_projectiveOrbitLimitSet_of_ne_univ
    (Γ : Subgroup PSL(2, ℝ)) (hne : ProjectiveNonelementary Γ) (z : ℍ)
    (hproper : projectiveOrbitLimitSet Γ z ≠ univ) :
    Dense (projectiveOrbitLimitSet Γ z)ᶜ := by
  have hex : ∃ p : OnePoint ℝ, p ∉ projectiveOrbitLimitSet Γ z := by
    by_contra h
    push Not at h
    exact hproper (Set.eq_univ_of_forall h)
  obtain ⟨p, hp⟩ := hex
  have hsub : MulAction.orbit Γ p ⊆ (projectiveOrbitLimitSet Γ z)ᶜ := by
    rintro _ ⟨g, rfl⟩ hmem
    exact hp ((projectiveOrbitLimitSet_smul_iff Γ z g p).mp hmem)
  have hK := (projectiveOrbitLimitSet_subset_closure_boundary_orbit Γ hne z p).trans
    (closure_mono hsub)
  intro ξ
  by_cases hξ : ξ ∈ projectiveOrbitLimitSet Γ z
  · exact hK hξ
  · exact subset_closure hξ

/-- Parabolic or ordinary endpoints are dense whenever the ideal limit set
is proper or the group contains a parabolic. -/
theorem dense_parabolic_or_ordinary_endpoints
    (Γ : Subgroup PSL(2, ℝ)) (hne : ProjectiveNonelementary Γ) (z : ℍ)
    (hgeom : projectiveOrbitLimitSet Γ z ≠ univ ∨
      ∃ g : Γ, ProjectiveParabolic (g : PSL(2, ℝ))) :
    Dense (projectiveParabolicFixedPoints Γ ∪ (projectiveOrbitLimitSet Γ z)ᶜ) := by
  rcases hgeom with hproper | hpar
  · exact (dense_compl_projectiveOrbitLimitSet_of_ne_univ Γ hne z hproper).mono subset_union_right
  · intro ξ
    by_cases hξ : ξ ∈ projectiveOrbitLimitSet Γ z
    · exact closure_mono subset_union_left
        (projectiveOrbitLimitSet_subset_closure_parabolicFixedPoints Γ hne z hpar hξ)
    · exact subset_closure (Or.inr hξ)

end Singularity
