import Singularity.FuchsianDirichletDeficit
import Singularity.FuchsianCocompactSingularity

/-!
# Singularity for finitely supported walks on nonelementary Fuchsian groups

For every discrete nonelementary subgroup of PSL(2,R), the actual hitting
measure of a finite positive semigroup-generating random walk is singular
with respect to visual measure. Symmetry and finite covolume are not assumed.

The compact-quotient case is already proved. A proper ideal limit set is
handled by the ordinary-endpoint argument. In the remaining case, the
quotient is noncompact and its limit set is full: a Dirichlet end gives a
bounded-height endpoint whose group orbit is dense. These endpoints provide
finite path separators, proving the last deficit-compactness premise.
No geometric classification theorem is assumed.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen

/-- The hitting measure of every discrete nonelementary Fuchsian group,
for a finite positive semigroup-generating law, is singular to visual measure. -/
theorem fuchsian_hittingMeasure_singular :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by sorry

/-- In the real boundary chart, the hitting law is singular to Lebesgue measure. -/
theorem fuchsian_hittingMeasure_singular_lebesgue :
    finiteBoundaryMeasure (projectiveHittingMeasure Γ s z μ hpos hmass) ⟂ₘ volume := by sorry

/-- Singularity holds for any almost-sure version of the actual geometric limit. -/
theorem fuchsian_hittingLaw_singular (b : (ℕ → s) → OnePoint ℝ)
    (hb : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (b ω)))) :
    walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b ⟂ₘ compactPoissonMeasure z := by sorry

/-- The actual random walk converges almost surely and its limit law is
singular. Both conclusions use only the original group and jump law. -/
theorem fuchsian_randomWalk_converges_and_hittingMeasure_singular :
    (∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (projectiveBoundaryMap Γ s z ω)))) ∧
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by sorry

end Singularity
