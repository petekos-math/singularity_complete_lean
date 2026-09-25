import Singularity.FuchsianBoundaryConcentration
import Singularity.TranslatedShadowConcentration

/-!
# Relative shadow concentration along actual Fuchsian paths

Translated hitting probabilities concentrate by the proved conditional
expectation theorem. This transfers to any finite measure dominated by the
hitting law, including the matched visual carrier. A shadow cocycle estimate
and uniform positive inverse mass then imply relative concentration.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal Topology
namespace Singularity

/-- Relative concentration is automatic along almost every path ending in E,
for every shadow family with the stated geometric mass and cocycle controls.
The measure can be the hitting law or an equivalent finite visual carrier. -/
theorem fuchsian_shadow_relative_concentration_along_paths
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (m : Measure (OnePoint ℝ)) [IsFiniteMeasure m]
    (hm : m ≪ projectiveHittingMeasure Γ s z μ hpos hmass)
    (hq : ∀ a : Γ, Measure.map (fun ξ : OnePoint ℝ => a • ξ) m ≪ m)
    (S : Γ → Set (OnePoint ℝ)) (hS : ∀ a, MeasurableSet (S a))
    (D : Γ → ℝ) (C : ℝ) {c : ℝ} (hc : 0 < c)
    (hinverse : ∀ a, c ≤ (m ((fun ξ : OnePoint ℝ => a • ξ) ⁻¹' S a)).toReal)
    (hbound : ∀ a, ∀ᵐ ξ ∂m, a • ξ ∈ S a → |stationaryLogCocycle m a ξ - D a| ≤ C)
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      projectiveBoundaryMap Γ s z ω ∈ E →
      Tendsto (fun n => (m (S (walkPosition s 1 n ω) \ E)).toReal /
        (m (S (walkPosition s 1 n ω))).toReal) atTop (𝓝 0) := by
  filter_upwards [fuchsian_reference_complement_concentration
    Γ hne s μ hpos hmass hgen z m hm hE] with ω hω hmem
  apply relative_shadow_error_tendsto_zero_of_translated_concentration m hq
    (fun n => walkPosition s 1 n ω) (fun n => S (walkPosition s 1 n ω))
    (fun n => hS _) hE (fun n => D (walkPosition s 1 n ω)) C hc
    (fun n => hinverse _) (fun n => hbound _)
  simpa only [ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hω hmem)

end Singularity
