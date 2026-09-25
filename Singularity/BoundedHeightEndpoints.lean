import Singularity.ProjectiveEndpointHeight

/-!
# Ideal points with bounded orbit height

An endpoint is usable for finite strips when the orbit has uniformly bounded
height in every chart taking infinity to that endpoint. The set of such
endpoints is invariant under the group. For a nonelementary group of the
first kind, one usable endpoint therefore gives a dense set of them.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Endpoints at which every infinity chart has a bounded-height orbit. -/
def projectiveBoundedHeightEndpoints (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    Set (OnePoint ℝ) :=
  {p | ∀ B : SL(2, ℝ), B • (∞ : OnePoint ℝ) = p →
    ∃ C : ℝ, 0 < C ∧ ∀ g : Γ, (B⁻¹ • (g • z)).im ≤ C}

/-- The bounded-height condition is preserved by every group element. -/
theorem projectiveBoundedHeightEndpoints_smul
    (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (a : Γ) {p : OnePoint ℝ}
    (hp : p ∈ projectiveBoundedHeightEndpoints Γ z) :
    a • p ∈ projectiveBoundedHeightEndpoints Γ z := by
  intro B hB
  obtain ⟨A, hA⟩ := slTwoProjective_surjective (a : PSL(2, ℝ))
  have hbd (q : OnePoint ℝ) : A • q = a • q := by
    rw [← slTwoProjective_smul_boundary, hA]
    rfl
  have hgeo (w : ℍ) : A • w = a • w := by
    rw [← slTwoProjective_smul_hyperbolic, hA]
    rfl
  have hchart : (A⁻¹ * B) • (∞ : OnePoint ℝ) = p := by
    rw [mul_smul, hB, ← hbd, inv_smul_smul]
  obtain ⟨C, hC, hb⟩ := hp (A⁻¹ * B) hchart
  refine ⟨C, hC, fun g => ?_⟩
  have hh := hb (a⁻¹ * g)
  simpa only [mul_inv_rev, inv_inv, mul_smul, hgeo, smul_inv_smul] using hh

/-- The orbit of any usable endpoint consists of usable endpoints. -/
theorem orbit_subset_projectiveBoundedHeightEndpoints
    (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) {p : OnePoint ℝ}
    (hp : p ∈ projectiveBoundedHeightEndpoints Γ z) :
    MulAction.orbit Γ p ⊆ projectiveBoundedHeightEndpoints Γ z := by
  rintro _ ⟨a, rfl⟩
  exact projectiveBoundedHeightEndpoints_smul Γ z a hp

/-- For a full limit set, one bounded-height endpoint suffices for density. -/
theorem dense_projectiveBoundedHeightEndpoints_of_full_limitSet
    (Γ : Subgroup PSL(2, ℝ)) (hne : ProjectiveNonelementary Γ) (z : ℍ)
    (hfull : projectiveOrbitLimitSet Γ z = univ)
    (hp : (projectiveBoundedHeightEndpoints Γ z).Nonempty) :
    Dense (projectiveBoundedHeightEndpoints Γ z) := by
  obtain ⟨p, hp⟩ := hp
  have hsub := projectiveOrbitLimitSet_subset_closure_boundary_orbit Γ hne z p
  rw [hfull] at hsub
  intro q
  exact closure_mono (orbit_subset_projectiveBoundedHeightEndpoints Γ z hp)
    (hsub (mem_univ q))

end Singularity
