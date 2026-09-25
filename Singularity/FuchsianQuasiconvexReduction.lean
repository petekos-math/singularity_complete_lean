import Singularity.QuasiconvexParabolic
import Singularity.QuasiconvexFullBoundary
import Singularity.FuchsianCocompactSingularity

/-!
# Exact remaining rigidity interfaces for the noncocompact theorem

The geometry is now proved: quasiconvexity rules out parabolics and, with
full ideal boundary, forces a compact quotient. These reductions use the
actual hitting measure and the already proved cocompact singularity theorem.

Nonsingularity implying quasiconvexity is an EXPLICIT hypothesis here; it has
not been proved. The null-or-full limit-set alternative in the final theorem
is also explicit. These conditional reductions do not establish the general
noncocompact singularity theorem.
-/

noncomputable section
open MeasureTheory Set
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen in
/-- Quasiconvexity and a full ideal limit set imply actual hitting-measure
singularity by the constructed compact quotient. -/
theorem fuchsian_hittingMeasure_singular_of_quasiconvex_full_limitSet
    (D : ℝ) (hqc : HyperbolicQuasiconvex (MulAction.orbit Γ z) D)
    (hfull : projectiveOrbitLimitSet Γ z = Set.univ) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  let : CompactSpace (Quotient (MulAction.orbitRel Γ ℍ)) :=
    projective_cocompact_of_quasiconvex_full_limitSet Γ z D hqc hfull
  exact cocompact_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z

/-- The presence of a parabolic completes the cusp contradiction if the
nonsingularity-to-quasiconvexity implication is supplied. That implication
remains an explicit, unproved hypothesis. -/
theorem fuchsian_parabolic_singularity_of_quasiconvex_rigidity
    (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ)))
    (hrig : ¬ projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z →
      ∃ D : ℝ, HyperbolicQuasiconvex (MulAction.orbit Γ z) D) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  by_contra hns
  exact discrete_projective_parabolic_orbit_not_quasiconvex Γ g hpar z (hrig hns)

include hne hgen in
/-- A precise reduction for the full target: nonsingularity-to-quasiconvexity
and the visual-null-or-full limit-set alternative suffice. Both premises are
explicit, and neither is introduced as an axiom. -/
theorem fuchsian_singularity_of_quasiconvex_rigidity_and_limitSet_dichotomy
    (hrig : ¬ projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z →
      ∃ D : ℝ, HyperbolicQuasiconvex (MulAction.orbit Γ z) D)
    (hlimit : compactPoissonMeasure z (projectiveOrbitLimitSet Γ z) = 0 ∨
      projectiveOrbitLimitSet Γ z = Set.univ) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  rcases hlimit with hnull | hfull
  · exact fuchsian_hittingMeasure_singular_of_null_limitSet Γ hne s μ hpos hmass hgen z hnull
  · by_contra hns
    obtain ⟨D, hD⟩ := hrig hns
    exact hns (fuchsian_hittingMeasure_singular_of_quasiconvex_full_limitSet
      Γ hne s μ hpos hmass hgen z D hD hfull)

end Singularity
