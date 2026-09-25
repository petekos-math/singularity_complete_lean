import Singularity.ParabolicIdealLimits
import Singularity.ProjectiveCuspStrips

/-!
# Orbit-height bounds at parabolic and ordinary ideal points

A chart at a parabolic fixed point has bounded orbit height by discreteness.
A chart at a point outside the ideal limit set has a bounded complex orbit:
its compactified orbit closure avoids infinity. Both kinds of points can
therefore serve as endpoints of finite strips.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Outside the ideal limit set, every chart taking infinity to the chosen
point has a uniformly bounded-height orbit. No discreteness is needed. -/
theorem projective_chart_height_bound_of_not_mem_limitSet
    (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (B : SL(2, ℝ))
    (hp : B • (∞ : OnePoint ℝ) ∉ projectiveOrbitLimitSet Γ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Γ, (B⁻¹ • (g • z)).im ≤ C := by
  let K : Set (OnePoint ℂ) := (fun w : OnePoint ℂ => B • w) ⁻¹'
    closure (range (fun g : Γ => hyperbolicCompactEmbedding (g • z)))
  have hK : IsClosed K := isClosed_closure.preimage (continuous_const_smul B)
  have hnot : (∞ : OnePoint ℂ) ∉ K := by
    change B • (∞ : OnePoint ℂ) ∉ closure (range (fun g : Γ => hyperbolicCompactEmbedding (g • z)))
    change compactBoundaryEmbedding (B • (∞ : OnePoint ℝ)) ∉
      closure (range (fun g : Γ => hyperbolicCompactEmbedding (g • z))) at hp
    rwa [compactBoundaryEmbedding_smul] at hp
  have hc := ((OnePoint.isClosed_iff_of_notMem hnot).mp hK).2
  obtain ⟨C, hC, hbound⟩ := hc.isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun g => ?_⟩
  have hmem : (((B⁻¹ • (g • z) : ℍ) : ℂ) : OnePoint ℂ) ∈ K := by
    change B • hyperbolicCompactEmbedding (B⁻¹ • (g • z)) ∈
      closure (range (fun k : Γ => hyperbolicCompactEmbedding (k • z)))
    rw [← hyperbolicCompactEmbedding_smul, smul_inv_smul]
    exact subset_closure (mem_range_self g)
  exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (hbound _ hmem))

/-- A prescribed chart at a parabolic fixed point has bounded orbit height
for a discrete projective group. -/
theorem projective_chart_height_bound_of_parabolic
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ)
    (g : Γ) (hg : ProjectiveParabolic (g : PSL(2, ℝ)))
    (B : SL(2, ℝ)) (hp : g • (B • (∞ : OnePoint ℝ)) = B • (∞ : OnePoint ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : Γ, (B⁻¹ • (k • z)).im ≤ C := by
  obtain ⟨u, hu, hgu⟩ := hg.shear_in_chart (g : PSL(2, ℝ)) B _ rfl hp
  let Λ := projectiveSubgroupLift Γ
  let Δ := conjugateSubgroup Λ B
  let : DiscreteTopology Λ := projectiveSubgroupLift_discrete Γ
  let : DiscreteTopology Δ := conjugateSubgroup_discrete Λ B
  have huΔ : upperShearMatrix u ∈ Δ := by
    change slTwoProjective (B * upperShearMatrix u * B⁻¹) ∈ Γ
    rw [← hgu]
    exact g.property
  obtain ⟨C, hC, hbound⟩ := discrete_upperShear_orbit_height_bound Δ u hu huΔ (B⁻¹ • z)
  refine ⟨C, hC, fun k => ?_⟩
  obtain ⟨a, ha⟩ := projectiveLiftProjection_surjective Γ k
  let b : Δ := (conjugateSubgroupEquiv Λ B).symm a
  have he := congrArg (fun w : ℍ => B⁻¹ • w)
    (conjugateSubgroup_hyperbolic_action Λ B b (B⁻¹ • z))
  have hact : B⁻¹ • (k • z) = b • (B⁻¹ • z) := by
    rw [← ha, projectiveLiftProjection_smul_hyperbolic]
    simpa only [smul_inv_smul, inv_smul_smul, b, MulEquiv.apply_symm_apply] using he.symm
  rw [hact]
  exact hbound b

/-- Both parabolic fixed points and points outside the limit set supply
positive uniform height bounds in any prescribed chart. -/
theorem projective_chart_height_bound_of_parabolic_or_ordinary
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (B : SL(2, ℝ))
    (hp : B • (∞ : OnePoint ℝ) ∈ projectiveParabolicFixedPoints Γ ∪
      (projectiveOrbitLimitSet Γ z)ᶜ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : Γ, (B⁻¹ • (k • z)).im ≤ C := by
  rcases hp with ⟨g, hg, hfix⟩ | hout
  · exact projective_chart_height_bound_of_parabolic Γ z g hg B hfix
  · exact projective_chart_height_bound_of_not_mem_limitSet Γ z B hout

end Singularity
