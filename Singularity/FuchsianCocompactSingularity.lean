import Singularity.ProjectiveCocompactSingularity
import Singularity.ProjectiveNonelementary

/-!
# The cocompact Fuchsian singularity theorem in its projective formulation

A nonelementary discrete cocompact subgroup of PSL(2,ℝ), a finite positive
probability support, and semigroup generation imply singularity of the actual
hitting measure. Nonelementarity uses absence of finite geometric orbits.
There is no symmetry, spectral-gap, chosen matrix lift, or separate
infinite-boundary-orbit hypothesis in the final statement.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped MatrixGroups UpperHalfPlane Topology

namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen in
/-- The original projective walk converges almost surely to the named boundary map. -/
theorem cocompact_fuchsian_boundaryMap_tendsto :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (projectiveBoundaryMap Γ s z ω))) :=
  projective_cocompact_boundaryMap_tendsto Γ s μ hpos hmass hgen
    (ProjectiveNonelementary.infinite_boundary_orbits Γ hne) z

include hne hgen in
/-- Singularity for a nonelementary discrete cocompact projective Fuchsian group. -/
theorem cocompact_fuchsian_hittingMeasure_singular :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z :=
  projective_cocompact_hittingMeasure_singular Γ s μ hpos hmass hgen
    (ProjectiveNonelementary.infinite_boundary_orbits Γ hne) z

include hne hgen in
/-- The same conclusion in the real boundary chart is singularity against Lebesgue measure. -/
theorem cocompact_fuchsian_hittingMeasure_singular_lebesgue :
    finiteBoundaryMeasure (projectiveHittingMeasure Γ s z μ hpos hmass) ⟂ₘ volume :=
  (compact_hitting_singularity_iff _ z).mp
    (cocompact_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z)

include hne hgen in
/-- Singularity is independent of the chosen almost-sure version of the hitting map. -/
theorem cocompact_fuchsian_hittingLaw_singular (b : (ℕ → s) → OnePoint ℝ)
    (hb : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (b ω)))) :
    walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b ⟂ₘ compactPoissonMeasure z := by
  have he : walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b =
      projectiveHittingMeasure Γ s z μ hpos hmass := by
    apply Measure.map_congr
    filter_upwards [hb, cocompact_fuchsian_boundaryMap_tendsto Γ hne s μ hpos hmass hgen z] with ω h₁ h₂
    exact compactBoundaryEmbedding_injective (tendsto_nhds_unique h₁ h₂)
  rw [he]
  exact cocompact_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z

end Singularity
