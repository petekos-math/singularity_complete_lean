import Singularity.GreenOrbitQuasiconvex
import Singularity.FuchsianQuasiconvexSingularity

/-!
# Reduction of full singularity to a radial upper Green bound

The Green comparison-to-quasiconvexity implication is proved internally.
What remains unproved is the analytic implication from nonsingularity to the
upper Green bound. It is an explicit premise of the final reduction, never
an axiom or an unconditional theorem.
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

include hne hgen

/-- An actual radial upper Green bound already implies hitting-measure
singularity, via the proved word comparison, tracking, and quasiconvex theorem. -/
theorem fuchsian_hittingMeasure_singular_of_green_upper (c C : ℝ) (hc : 0 < c)
    (hupper : ∀ g : Γ, greenDistance s μ 1 g ≤ c * dist z (g • z) + C) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  obtain ⟨D, hD⟩ := projective_orbit_quasiconvex_of_green_upper Γ hne s μ hpos hmass hgen z c C hc hupper
  exact quasiconvex_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z D hD

/-- Exact remaining analytic interface: nonsingularity supplying a radial
upper Green bound would complete the unrestricted singularity theorem. -/
theorem fuchsian_singularity_of_green_upper_rigidity
    (hrig : ¬ projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z →
      ∃ c C : ℝ, 0 < c ∧ ∀ g : Γ, greenDistance s μ 1 g ≤ c * dist z (g • z) + C) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  by_contra hns
  obtain ⟨c, C, hc, hu⟩ := hrig hns
  exact hns (fuchsian_hittingMeasure_singular_of_green_upper Γ hne s μ hpos hmass hgen z c C hc hu)

/-- The usual bounded Green/geometric comparison, if derived from
nonsingularity, also suffices. Neither that rigidity statement nor its
structural prerequisites are asserted by this conditional reduction. -/
theorem fuchsian_singularity_of_green_comparison_rigidity
    (hrig : ¬ projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z →
      ∃ δ C : ℝ, ∀ g : Γ, |greenDistance s μ 1 g - δ * dist z (g • z)| ≤ C) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  apply fuchsian_singularity_of_quasiconvex_rigidity Γ hne s μ hpos hmass hgen z
  intro hns
  obtain ⟨δ, C, hC⟩ := hrig hns
  exact projective_orbit_quasiconvex_of_green_comparison Γ hne s μ hpos hmass hgen z δ C hC

end Singularity
