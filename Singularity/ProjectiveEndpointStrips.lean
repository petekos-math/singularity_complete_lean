import Singularity.ProjectiveEndpointHeight
import Singularity.ProjectiveOrbitSubsequences
import Singularity.FiniteExitEnlargement

/-!
# Finite separators with parabolic or ordinary endpoints

Height bounds at both ends put a fixed chart strip in a compact interior
rectangle. This gives finite sets of projective group vertices and finite
outgoing exit sets for the negative chart half-plane. Endpoints outside the
limit set are allowed, so complementary gaps cause no loss of separators.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Two chart height bounds give finite projective group strips. -/
theorem finite_projective_chart_strip_of_height_bounds
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (B : SL(2, ℝ))
    {R C D : ℝ} (hR : 0 ≤ R) (hD : 0 < D)
    (hinfty : ∀ g : Γ, (B⁻¹ • (g • z)).im ≤ C)
    (hzero : ∀ g : Γ, (boundaryPoleMatrix 0 • (B⁻¹ • (g • z))).im ≤ D) :
    {g : Γ | B⁻¹ • (g • z) ∈ axisRatioStrip R}.Finite := by
  let l := 1 / (D * (R ^ 2 + 1))
  have hl : 0 < l := by dsimp [l]; positivity
  let K := {w : ℍ | |w.re| ≤ R * C ∧ l ≤ w.im ∧ w.im ≤ C}
  have hK : IsCompact K := isCompact_heightBandRectangle (R * C) l C hl
  have hBK : IsCompact ((fun w : ℍ => B • w) '' K) := hK.image (continuous_const_smul B)
  apply (finite_projective_group_vertices_in_compact Γ z hBK).subset
  intro g hg
  refine ⟨B⁻¹ • (g • z), ⟨?_, ?_, hinfty g⟩, smul_inv_smul B (g • z)⟩
  · have hr : |(B⁻¹ • (g • z)).re| ≤ R * (B⁻¹ • (g • z)).im := by
      change |(B⁻¹ • (g • z)).re / (B⁻¹ • (g • z)).im| ≤ R at hg
      rw [abs_div, abs_of_pos (B⁻¹ • (g • z)).im_pos] at hg
      exact (div_le_iff₀ (B⁻¹ • (g • z)).im_pos).mp hg
    exact hr.trans (mul_le_mul_of_nonneg_left (hinfty g) hR)
  · exact axisRatioStrip_height_lower_of_pole_bound hD _ hg (hzero g)

/-- Every strip whose endpoints are parabolic or outside the limit set has
only finitely many group vertices. -/
theorem finite_projective_chart_strip_of_parabolic_or_ordinary_endpoints
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (B : SL(2, ℝ))
    (hp : B • (∞ : OnePoint ℝ) ∈ projectiveParabolicFixedPoints Γ ∪ (projectiveOrbitLimitSet Γ z)ᶜ)
    (hq : B • ((0 : ℝ) : OnePoint ℝ) ∈ projectiveParabolicFixedPoints Γ ∪ (projectiveOrbitLimitSet Γ z)ᶜ)
    {R : ℝ} (hR : 0 ≤ R) :
    {g : Γ | B⁻¹ • (g • z) ∈ axisRatioStrip R}.Finite := by
  obtain ⟨C, _, hC⟩ := projective_chart_height_bound_of_parabolic_or_ordinary Γ z B hp
  have hq' : (B * (boundaryPoleMatrix 0)⁻¹) • (∞ : OnePoint ℝ) ∈
      projectiveParabolicFixedPoints Γ ∪ (projectiveOrbitLimitSet Γ z)ᶜ := by
    simpa only [mul_smul, boundaryPoleMatrix_inv_smul_infty_zero] using hq
  obtain ⟨D, hD, hDbound⟩ := projective_chart_height_bound_of_parabolic_or_ordinary Γ z _ hq'
  apply finite_projective_chart_strip_of_height_bounds Γ z B hR hD hC
  intro g
  simpa only [mul_inv_rev, inv_inv, mul_smul] using hDbound g

/-- A negative half-plane with these endpoints has a finite set containing
all starting vertices of supported exits. -/
theorem projective_endpoint_chart_finite_exit_set
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (s : Finset Γ) (B : SL(2, ℝ))
    (hp : B • (∞ : OnePoint ℝ) ∈ projectiveParabolicFixedPoints Γ ∪ (projectiveOrbitLimitSet Γ z)ᶜ)
    (hq : B • ((0 : ℝ) : OnePoint ℝ) ∈ projectiveParabolicFixedPoints Γ ∪ (projectiveOrbitLimitSet Γ z)ᶜ) :
    ∃ T : Finset Γ, ∀ v : Γ, (B⁻¹ • (v • z)).re < 0 → v ∉ (T : Set Γ) →
      ∀ t ∈ s, (B⁻¹ • ((v * t) • z)).re < 0 := by
  let L := ∑ t ∈ s, dist z (t • z)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => dist_nonneg)
  have hfinite := finite_projective_chart_strip_of_parabolic_or_ordinary_endpoints Γ z B hp hq
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
