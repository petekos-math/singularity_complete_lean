import Singularity.HyperbolicQuasiconvex
import Singularity.ProjectiveParabolic
import Singularity.CocompactRayApproximation

/-!
# Discrete quasiconvex orbits contain no parabolics

The cusp-height obstruction descends from normalized upper shears to arbitrary
projective parabolics by conjugation and the full sign lift. The resulting
statement requires only discreteness, not finite generation, a finite-index
free subgroup, or a random walk. A future nonsingularity-to-quasiconvexity
rigidity theorem can therefore use this geometric obstruction directly.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Conjugation identifies the entire hyperbolic orbits. -/
theorem conjugateSubgroup_hyperbolic_orbit (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ)) (z : ℍ) :
    (fun w : ℍ => B • w) '' MulAction.orbit (conjugateSubgroup Γ B) z =
      MulAction.orbit Γ (B • z) := by
  ext w
  constructor
  · rintro ⟨v, ⟨a, rfl⟩, rfl⟩
    exact ⟨conjugateSubgroupEquiv Γ B a, (conjugateSubgroup_hyperbolic_action Γ B a z).symm⟩
  · rintro ⟨g, rfl⟩
    let a := (conjugateSubgroupEquiv Γ B).symm g
    refine ⟨a • z, ⟨a, rfl⟩, ?_⟩
    change B • (a • z) = g • (B • z)
    rw [conjugateSubgroup_hyperbolic_action]
    exact congrArg (fun h : Γ => h • (B • z)) ((conjugateSubgroupEquiv Γ B).apply_symm_apply g)

/-- Quasiconvexity is unchanged by conjugating both the group and the basepoint. -/
theorem conjugateSubgroup_quasiconvex_iff (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ)) (z : ℍ) (D : ℝ) :
    HyperbolicQuasiconvex (MulAction.orbit (conjugateSubgroup Γ B) z) D ↔
      HyperbolicQuasiconvex (MulAction.orbit Γ (B • z)) D := by
  rw [← conjugateSubgroup_hyperbolic_orbit]
  exact (hyperbolicQuasiconvex_smul_image_iff _ D B).symm

/-- A discrete projective group containing a parabolic has no quasiconvex orbit. -/
theorem discrete_projective_parabolic_orbit_not_quasiconvex (Γ : Subgroup PSL(2, ℝ))
    [DiscreteTopology Γ] (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ))) (z : ℍ) :
    ¬∃ D : ℝ, HyperbolicQuasiconvex (MulAction.orbit Γ z) D := by
  obtain ⟨B, u, hu, hg⟩ := hpar.exists_conjugate_shear g
  let Λ := projectiveSubgroupLift Γ
  let : DiscreteTopology Λ := projectiveSubgroupLift_discrete Γ
  let : DiscreteTopology (conjugateSubgroup Λ B) := conjugateSubgroup_discrete Λ B
  have hm : upperShearMatrix u ∈ conjugateSubgroup Λ B := by
    change slTwoProjective (B * upperShearMatrix u * B⁻¹) ∈ Γ
    rw [← hg]
    exact g.property
  rintro ⟨D, hD⟩
  have hL : HyperbolicQuasiconvex (MulAction.orbit Λ z) D :=
    (projectiveSubgroupLift_quasiconvex_iff Γ z D).mpr hD
  have hc : HyperbolicQuasiconvex (MulAction.orbit (conjugateSubgroup Λ B) (B⁻¹ • z)) D := by
    apply (conjugateSubgroup_quasiconvex_iff Λ B (B⁻¹ • z) D).mpr
    simpa only [smul_inv_smul] using hL
  exact discrete_upperShear_orbit_not_quasiconvex (conjugateSubgroup Λ B) u hu hm (B⁻¹ • z) ⟨D, hc⟩

/-- Every element of a discrete group with a quasiconvex orbit is nonparabolic. -/
theorem discrete_quasiconvex_orbit_no_parabolic (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    (z : ℍ) (D : ℝ) (hD : HyperbolicQuasiconvex (MulAction.orbit Γ z) D) (g : Γ) :
    ¬ProjectiveParabolic (g : PSL(2, ℝ)) := by
  intro hg
  exact discrete_projective_parabolic_orbit_not_quasiconvex Γ g hg z ⟨D, hD⟩

/-- Cocompactness supplies a quasiconvex orbit, directly from a uniform orbit cover. -/
theorem cocompact_projective_orbit_quasiconvex (Γ : Subgroup PSL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    ∃ D : ℝ, 0 < D ∧ HyperbolicQuasiconvex (MulAction.orbit Γ UpperHalfPlane.I) D := by
  let Λ := projectiveSubgroupLift Γ
  let : CompactSpace (Quotient (MulAction.orbitRel Λ ℍ)) := projectiveSubgroupLift_cocompact Γ
  obtain ⟨D, hD, hcover⟩ := cocompact_orbit_uniform_bound Λ
  refine ⟨D, hD, (projectiveSubgroupLift_quasiconvex_iff Γ UpperHalfPlane.I D).mp ?_⟩
  intro x hx y hy w hw
  obtain ⟨g, hg⟩ := hcover w
  exact ⟨g • UpperHalfPlane.I, ⟨g, rfl⟩, by simpa only [dist_comm] using hg⟩

/-- A discrete cocompact projective group contains no parabolic elements. -/
theorem cocompact_projective_no_parabolic (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] (g : Γ) :
    ¬ProjectiveParabolic (g : PSL(2, ℝ)) := by
  obtain ⟨D, _, hD⟩ := cocompact_projective_orbit_quasiconvex Γ
  exact discrete_quasiconvex_orbit_no_parabolic Γ UpperHalfPlane.I D hD g

end Singularity
