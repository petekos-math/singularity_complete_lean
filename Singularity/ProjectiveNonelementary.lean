import Singularity.ProjectiveActions
import Mathlib.Algebra.Group.Action.Sum

/-!
# Nonelementarity in the geometric finite-orbit convention

A subgroup is nonelementary if it has no finite orbit in the hyperbolic
plane together with its ideal boundary. The disjoint sum here only describes
that set and its action; no topological sum compactification is asserted.
This is the classical finite-orbit convention (for example Jacques--Short,
"Semigroups of isometries of the hyperbolic plane", §1 and §10,
https://arxiv.org/abs/1609.00576).
-/

noncomputable section
open Set OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- No finite orbit in the hyperbolic plane or its ideal boundary. -/
def ProjectiveNonelementary (Γ : Subgroup PSL(2, ℝ)) : Prop :=
  ¬ ∃ x : ℍ ⊕ OnePoint ℝ, (MulAction.orbit Γ x).Finite

/-- Boundary orbits in the geometric union are the images of the actual boundary orbits. -/
theorem projective_geometric_orbit_inr (Γ : Subgroup PSL(2, ℝ)) (x : OnePoint ℝ) :
    MulAction.orbit Γ (Sum.inr x : ℍ ⊕ OnePoint ℝ) =
      (Sum.inr : OnePoint ℝ → ℍ ⊕ OnePoint ℝ) '' MulAction.orbit Γ x := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g • x, MulAction.mem_orbit x g, rfl⟩
  · rintro ⟨p, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

/-- Interior orbits in the geometric union are likewise the images of the actual orbits. -/
theorem projective_geometric_orbit_inl (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    MulAction.orbit Γ (Sum.inl z : ℍ ⊕ OnePoint ℝ) =
      (Sum.inl : ℍ → ℍ ⊕ OnePoint ℝ) '' MulAction.orbit Γ z := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g • z, MulAction.mem_orbit z g, rfl⟩
  · rintro ⟨p, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

/-- The geometric nonelementarity condition supplies every boundary-orbit hypothesis. -/
theorem ProjectiveNonelementary.infinite_boundary_orbits (Γ : Subgroup PSL(2, ℝ))
    (h : ProjectiveNonelementary Γ) (x : OnePoint ℝ) : (MulAction.orbit Γ x).Infinite := by
  intro hf
  apply h
  refine ⟨Sum.inr x, ?_⟩
  rw [projective_geometric_orbit_inr]
  exact hf.image _

theorem ProjectiveNonelementary.infinite_hyperbolic_orbits (Γ : Subgroup PSL(2, ℝ))
    (h : ProjectiveNonelementary Γ) (z : ℍ) : (MulAction.orbit Γ z).Infinite := by
  intro hf
  apply h
  refine ⟨Sum.inl z, ?_⟩
  rw [projective_geometric_orbit_inl]
  exact hf.image _

/-- The finite-orbit definition is exactly infinitude of all interior and boundary orbits. -/
theorem projectiveNonelementary_iff (Γ : Subgroup PSL(2, ℝ)) :
    ProjectiveNonelementary Γ ↔
      (∀ z : ℍ, (MulAction.orbit Γ z).Infinite) ∧
      (∀ x : OnePoint ℝ, (MulAction.orbit Γ x).Infinite) := by
  constructor
  · intro h
    exact ⟨ProjectiveNonelementary.infinite_hyperbolic_orbits Γ h,
      ProjectiveNonelementary.infinite_boundary_orbits Γ h⟩
  · rintro ⟨hi, hb⟩ ⟨x, hx⟩
    cases x with
    | inl z =>
      rw [projective_geometric_orbit_inl] at hx
      exact hi z (hx.of_finite_image Sum.inl_injective.injOn)
    | inr x =>
      rw [projective_geometric_orbit_inr] at hx
      exact hb x (hx.of_finite_image Sum.inr_injective.injOn)

end Singularity
