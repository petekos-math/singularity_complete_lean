import Singularity.QuasiconvexLimitSetDichotomy
import Singularity.FuchsianQuasiconvexReduction

/-!
# Singularity for every discrete nonelementary group with a quasiconvex orbit

The visual-null-or-full alternative is now proved, not assumed. In the null
case, the actual hitting measure is carried by a visual-null limit set. In the
full case, quasiconvexity constructs a compact quotient and the completed
cocompact theorem applies. No symmetry or spectral-gap assumption is added.

The full singularity conjecture still requires proving that nonsingularity
forces a quasiconvex orbit. The final reduction states that remaining analytic
rigidity premise explicitly and does not assert it.
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
/-- Actual hitting-measure singularity for every quasiconvex orbit, including
noncocompact groups. The limit-set alternative is proved internally. -/
theorem quasiconvex_fuchsian_hittingMeasure_singular
    (D : ℝ) (hqc : HyperbolicQuasiconvex (MulAction.orbit Γ z) D) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  rcases quasiconvex_limitSet_visual_null_or_full Γ z D hqc with hnull | hfull
  · exact fuchsian_hittingMeasure_singular_of_null_limitSet Γ hne s μ hpos hmass hgen z hnull
  · exact fuchsian_hittingMeasure_singular_of_quasiconvex_full_limitSet Γ hne s μ hpos hmass hgen z D hqc hfull

include hne hgen in
/-- The quasiconvex theorem in the real boundary chart gives Lebesgue singularity. -/
theorem quasiconvex_fuchsian_hittingMeasure_singular_lebesgue
    (D : ℝ) (hqc : HyperbolicQuasiconvex (MulAction.orbit Γ z) D) :
    finiteBoundaryMeasure (projectiveHittingMeasure Γ s z μ hpos hmass) ⟂ₘ volume :=
  (compact_hitting_singularity_iff _ z).mp
    (quasiconvex_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z D hqc)

include hne hgen in
/-- The remaining exact analytic interface: nonsingularity implying
quasiconvexity would complete the general theorem. No separate limit-set
alternative or virtual-freeness premise is needed in this reduction. -/
theorem fuchsian_singularity_of_quasiconvex_rigidity
    (hrig : ¬ projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z →
      ∃ D : ℝ, HyperbolicQuasiconvex (MulAction.orbit Γ z) D) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  by_contra hns
  obtain ⟨D, hD⟩ := hrig hns
  exact hns (quasiconvex_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z D hD)

end Singularity
