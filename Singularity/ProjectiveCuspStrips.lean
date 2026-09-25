import Singularity.ParabolicFixedPointCharts
import Singularity.CuspStripFiniteness
import Singularity.ProjectiveSubgroupLift

/-!
# Finite strips between arbitrary parabolic fixed points

Prescribed endpoint charts normalize both parabolics. The full special-linear
lift handles signs, and conjugation reduces strip finiteness to the normalized
cusp-height theorem. Projection returns finite sets of original group vertices.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- A chart carrying infinity and zero to parabolic fixed points has finite
axis strips in the original projective group. No cocompactness is assumed. -/
theorem finite_projective_cusp_strip_in_chart
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ)
    (g h : Γ) (hg : ProjectiveParabolic (g : PSL(2, ℝ)))
    (hh : ProjectiveParabolic (h : PSL(2, ℝ)))
    (p q : OnePoint ℝ) (hgp : g • p = p) (hhq : h • q = q)
    (B : SL(2, ℝ)) (hBp : B • (∞ : OnePoint ℝ) = p)
    (hBq : B • ((0 : ℝ) : OnePoint ℝ) = q)
    {R : ℝ} (hR : 0 ≤ R) :
    {k : Γ | B⁻¹ • (k • z) ∈ axisRatioStrip R}.Finite := by
  obtain ⟨u, hu, hgu⟩ := hg.shear_in_chart (g : PSL(2, ℝ)) B p hBp hgp
  let J := boundaryPoleMatrix 0
  have hBJ : (B * J⁻¹) • (∞ : OnePoint ℝ) = q := by
    rw [mul_smul, boundaryPoleMatrix_inv_smul_infty_zero, hBq]
  obtain ⟨v, hv, hhv⟩ := hh.shear_in_chart (h : PSL(2, ℝ)) (B * J⁻¹) q hBJ hhq
  let Λ := projectiveSubgroupLift Γ
  let Δ := conjugateSubgroup Λ B
  let : DiscreteTopology Λ := projectiveSubgroupLift_discrete Γ
  let : DiscreteTopology Δ := conjugateSubgroup_discrete Λ B
  have huΔ : upperShearMatrix u ∈ Δ := by
    change slTwoProjective (B * upperShearMatrix u * B⁻¹) ∈ Γ
    rw [← hgu]
    exact g.property
  have hvΔ : J⁻¹ * upperShearMatrix v * J ∈ Δ := by
    change slTwoProjective (B * (J⁻¹ * upperShearMatrix v * J) * B⁻¹) ∈ Γ
    have he : B * (J⁻¹ * upperShearMatrix v * J) * B⁻¹ =
        (B * J⁻¹) * upperShearMatrix v * (B * J⁻¹)⁻¹ := by group
    rw [he, ← hhv]
    exact h.property
  have hf := finite_axisRatioStrip_of_two_parabolic_shears Δ (B⁻¹ • z) hR u v hu hv huΔ hvΔ
  let f : Δ → Γ := fun a => projectiveLiftProjection Γ (conjugateSubgroupEquiv Λ B a)
  have hsurj : Function.Surjective f :=
    (projectiveLiftProjection_surjective Γ).comp (conjugateSubgroupEquiv Λ B).surjective
  have hact (a : Δ) : B⁻¹ • (f a • z) = a • (B⁻¹ • z) := by
    have he := congrArg (fun w : ℍ => B⁻¹ • w)
      (conjugateSubgroup_hyperbolic_action Λ B a (B⁻¹ • z))
    change B⁻¹ • (projectiveLiftProjection Γ (conjugateSubgroupEquiv Λ B a) • z) = _
    rw [projectiveLiftProjection_smul_hyperbolic]
    simpa only [smul_inv_smul, inv_smul_smul] using he.symm
  apply (hf.image f).subset
  intro k hk
  obtain ⟨a, rfl⟩ := hsurj k
  change B⁻¹ • (f a • z) ∈ axisRatioStrip R at hk
  rw [hact] at hk
  exact mem_image_of_mem f hk

/-- Any two distinct parabolic fixed points admit a common chart whose
axis strips all contain finitely many original projective group vertices. -/
theorem exists_finite_projective_cusp_strip_chart
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ)
    (g h : Γ) (hg : ProjectiveParabolic (g : PSL(2, ℝ)))
    (hh : ProjectiveParabolic (h : PSL(2, ℝ)))
    (p q : OnePoint ℝ) (hpq : p ≠ q) (hgp : g • p = p) (hhq : h • q = q) :
    ∃ B : SL(2, ℝ), B • (∞ : OnePoint ℝ) = p ∧
      B • ((0 : ℝ) : OnePoint ℝ) = q ∧ ∀ R : ℝ, 0 ≤ R →
        {k : Γ | B⁻¹ • (k • z) ∈ axisRatioStrip R}.Finite := by
  obtain ⟨B, hB⟩ := exists_smul_baseBoundaryPair ⟨(p, q), hpq⟩
  have he := congrArg Subtype.val hB
  change (B • (∞ : OnePoint ℝ), B • ((0 : ℝ) : OnePoint ℝ)) = (p, q) at he
  have hp := congrArg Prod.fst he
  have hq := congrArg Prod.snd he
  exact ⟨B, hp, hq, fun R hR =>
    finite_projective_cusp_strip_in_chart Γ z g h hg hh p q hgp hhq B hp hq hR⟩

end Singularity
