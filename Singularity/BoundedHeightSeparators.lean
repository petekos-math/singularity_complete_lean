import Singularity.ProjectiveEndpointStrips
import Singularity.BoundedHeightEndpoints

/-!
# Finite separators from arbitrary bounded-height endpoints

Two orbit-height bounds put a strip in a compact rectangle. The endpoints
need not be parabolic or outside the limit set.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Any two bounded-height endpoints give finite strips. -/
theorem finite_projective_chart_strip_of_bounded_height_endpoints
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (B : SL(2, ℝ))
    (hp : B • (∞ : OnePoint ℝ) ∈ projectiveBoundedHeightEndpoints Γ z)
    (hq : B • ((0 : ℝ) : OnePoint ℝ) ∈ projectiveBoundedHeightEndpoints Γ z)
    {R : ℝ} (hR : 0 ≤ R) :
    {g : Γ | B⁻¹ • (g • z) ∈ axisRatioStrip R}.Finite := by
  obtain ⟨C, _, hC⟩ := hp B rfl
  have he : (B * (boundaryPoleMatrix 0)⁻¹) • (∞ : OnePoint ℝ) =
      B • ((0 : ℝ) : OnePoint ℝ) := by
    rw [mul_smul, boundaryPoleMatrix_inv_smul_infty_zero]
  obtain ⟨D, hD, hDbound⟩ := hq (B * (boundaryPoleMatrix 0)⁻¹) he
  apply finite_projective_chart_strip_of_height_bounds Γ z B hR hD hC
  intro g
  simpa only [mul_inv_rev, inv_inv, mul_smul] using hDbound g

/-- A negative half-plane with bounded-height endpoints has a finite set containing
all starting vertices of supported exits. -/
theorem projective_boundedHeight_chart_finite_exit_set
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (s : Finset Γ) (B : SL(2, ℝ))
    (hp : B • (∞ : OnePoint ℝ) ∈ projectiveBoundedHeightEndpoints Γ z)
    (hq : B • ((0 : ℝ) : OnePoint ℝ) ∈ projectiveBoundedHeightEndpoints Γ z) :
    ∃ T : Finset Γ, ∀ v : Γ, (B⁻¹ • (v • z)).re < 0 → v ∉ (T : Set Γ) →
      ∀ t ∈ s, (B⁻¹ • ((v * t) • z)).re < 0 := by
  let L := ∑ t ∈ s, dist z (t • z)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => dist_nonneg)
  have hfinite := finite_projective_chart_strip_of_bounded_height_endpoints Γ z B hp hq
    (jumpStripRadius_pos hL).le
  let A : Finset Γ := hfinite.toFinset
  obtain ⟨T, _, hT⟩ := exists_finite_exit_enlargement s A
    {v : Γ | (B⁻¹ • (v • z)).re < 0} (by
      intro v hv t ht hvt hneg
      have hvout : B⁻¹ • (v • z) ∉ axisRatioStrip (jumpStripRadius L) := by
        simpa only [A, Set.Finite.coe_toFinset, mem_ofPred_eq] using hv
      have hvtout : B⁻¹ • ((v * t) • z) ∉ axisRatioStrip (jumpStripRadius L) := by
        simpa only [A, Set.Finite.coe_toFinset, mem_ofPred_eq] using hvt
      apply bounded_jump_preserves_negative_side hL _ _ ?_ hvout hvtout hneg
      rw [dist_smul, mul_smul]
      change dist ((v : PSL(2, ℝ)) • z) ((v : PSL(2, ℝ)) • (t • z)) ≤ L
      rw [projective_dist_smul]
      change dist z (t • z) ≤ ∑ a ∈ s, dist z (a • z)
      exact Finset.single_le_sum (f := fun a : Γ => dist z (a • z))
        (fun _ _ => dist_nonneg) ht)
  exact ⟨T, hT⟩

end Singularity
