import Singularity.FuchsianCuspOrProperLimitSingularity
import Singularity.FuchsianCocompactSingularity

/-!
# A historical reduction to geometric structure

Before the Dirichlet-end argument, the available cases suggested the
following structural route:
a finitely generated discrete nonelementary group with full ideal limit set
and no parabolics is cocompact. This module does not prove that obligation;
it records that conditional assembly. The full theorem is now proved in
`FuchsianSingularity` by a Dirichlet-end argument that bypasses this
classification theorem. These conditional lemmas are retained for reference.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen

/-- Nonsingularity would force full ideal limit set, absence of parabolics,
and a noncompact hyperbolic quotient, all for the actual finitely generated group. -/
theorem nonsingular_fuchsian_remaining_geometry
    (hns : ¬projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z) :
    projectiveOrbitLimitSet Γ z = univ ∧
      (∀ a : Γ, ¬ProjectiveParabolic (a : PSL(2, ℝ))) ∧
      ¬CompactSpace (Quotient (MulAction.orbitRel Γ ℍ)) := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hproper
    exact hns (proper_limitSet_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z hproper)
  · intro a ha
    exact hns (parabolic_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z ⟨a, ha⟩)
  · intro hc
    letI := hc
    exact hns (cocompact_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z)

/-- This alternative assembly needs the first-kind, parabolic-free
cocompactness implication. That geometric implication is an explicit input to this lemma. -/
theorem fuchsian_hittingMeasure_singular_of_first_kind_structure
    (hstructure : projectiveOrbitLimitSet Γ z = univ →
      (∀ a : Γ, ¬ProjectiveParabolic (a : PSL(2, ℝ))) →
      CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  by_contra hns
  obtain ⟨hfull, hpar, hnc⟩ := nonsingular_fuchsian_remaining_geometry Γ hne s μ hpos hmass hgen z hns
  exact hnc (hstructure hfull hpar)

end Singularity
