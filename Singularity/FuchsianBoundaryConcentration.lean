import Singularity.FuchsianHittingMeasure
import Singularity.WalkBoundaryConcentration
import Singularity.FiniteMeasureAbsoluteContinuity

/-!
# Event concentration for the original nonelementary Fuchsian walk

The named boundary selector obeys the first-step relation by uniqueness of
its geometric limit. Thus translated hitting probabilities converge to the
indicator of each measurable boundary event, with no compactness assumption.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical MatrixGroups UpperHalfPlane Topology
namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen

/-- The actual projective limit is the first increment acting on the future limit. -/
theorem fuchsian_boundaryMap_first_step :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      projectiveBoundaryMap Γ s z ω = (ω 0 : Γ) •
        projectiveBoundaryMap Γ s z (fun k => ω (k + 1)) := by
  let P := infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass
  have hshift : MeasurePreserving (fun (ω : ℕ → s) k => ω (k + 1)) P P :=
    ⟨by fun_prop, infiniteWalkLaw_shift s μ (fun g hg => (hpos g hg).le) hmass 1⟩
  have hlimit := fuchsian_boundaryMap_tendsto Γ hne s μ hpos hmass hgen z
  filter_upwards [hlimit, hshift.quasiMeasurePreserving.ae hlimit] with ω hω ht
  obtain ⟨a, ha⟩ := slTwoProjective_surjective ((ω 0 : Γ) : PSL(2, ℝ))
  have hc := (continuous_const_smul a : Continuous (fun p : OnePoint ℂ => a • p)).tendsto
      (compactBoundaryEmbedding (projectiveBoundaryMap Γ s z (fun k => ω (k + 1))))
      |>.comp ht
  have he (n : ℕ) : hyperbolicCompactEmbedding (walkPosition s 1 (n + 1) ω • z) =
      a • hyperbolicCompactEmbedding (walkPosition s 1 n (fun k => ω (k + 1)) • z) := by
    rw [walkPosition_first_step, mul_smul]
    change hyperbolicCompactEmbedding (((ω 0 : Γ) : PSL(2, ℝ)) • _) = _
    rw [← ha, slTwoProjective_smul_hyperbolic, hyperbolicCompactEmbedding_smul]
  have heq := tendsto_nhds_unique (hω.comp (tendsto_add_atTop_nat 1))
    (show Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 (n + 1) ω • z))
      atTop (𝓝 (a • compactBoundaryEmbedding
        (projectiveBoundaryMap Γ s z (fun k => ω (k + 1))))) by simpa only [he, Function.comp_def] using hc)
  apply compactBoundaryEmbedding_injective
  rw [← compactBoundaryEmbedding_smul] at heq
  convert heq using 1
  change compactBoundaryEmbedding ((((ω 0 : Γ) : PSL(2, ℝ)) • _)) = _
  rw [← ha, slTwoProjective_smul_boundary]

/-- Conditional boundary probabilities concentrate on each measurable event
along almost every path of the original projective random walk. -/
theorem fuchsian_hittingMeasure_event_concentration {E : Set (OnePoint ℝ)}
    (hE : MeasurableSet E) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => (projectiveHittingMeasure Γ s z μ hpos hmass
        ((fun ξ : OnePoint ℝ => walkPosition s 1 n ω • ξ) ⁻¹' E)).toReal)
        atTop (𝓝 (((projectiveBoundaryMap Γ s z) ⁻¹' E).indicator (fun _ => (1 : ℝ)) ω)) :=
  walkBoundaryLaw_event_concentration s μ (fun g hg => (hpos g hg).le) hmass
    (projectiveBoundaryMap Γ s z) (measurable_projectiveBoundaryMap Γ s z)
    (fuchsian_boundaryMap_first_step Γ hne s μ hpos hmass hgen z) hE

/-- On paths ending in E, the pulled-back complement of E has mass tending
to zero. The conclusion uses the actual extended-real measure values. -/
theorem fuchsian_hittingMeasure_complement_concentration {E : Set (OnePoint ℝ)}
    (hE : MeasurableSet E) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      projectiveBoundaryMap Γ s z ω ∈ E →
      Tendsto (fun n => projectiveHittingMeasure Γ s z μ hpos hmass
        ((fun ξ : OnePoint ℝ => walkPosition s 1 n ω • ξ) ⁻¹' Eᶜ)) atTop (𝓝 0) := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  filter_upwards [fuchsian_hittingMeasure_event_concentration
    Γ hne s μ hpos hmass hgen z hE.compl] with ω hω hmem
  have ht : Tendsto (fun n => (projectiveHittingMeasure Γ s z μ hpos hmass
      ((fun ξ : OnePoint ℝ => walkPosition s 1 n ω • ξ) ⁻¹' Eᶜ)).toReal)
      atTop (𝓝 0) := by
    simpa only [Set.indicator_apply, mem_preimage, mem_compl_iff, not_not,
      ite_eq_right (not_not.mpr hmem)] using hω
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_zero]
    using ENNReal.tendsto_ofReal ht

/-- Every finite reference measure dominated by the hitting law has the same
pathwise complement concentration. In particular this applies to the matched
visual carrier under nonsingularity. -/
theorem fuchsian_reference_complement_concentration
    (m : Measure (OnePoint ℝ)) [IsFiniteMeasure m]
    (hm : m ≪ projectiveHittingMeasure Γ s z μ hpos hmass)
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      projectiveBoundaryMap Γ s z ω ∈ E →
      Tendsto (fun n => m ((fun ξ : OnePoint ℝ => walkPosition s 1 n ω • ξ) ⁻¹' Eᶜ))
        atTop (𝓝 0) := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  filter_upwards [fuchsian_hittingMeasure_complement_concentration
    Γ hne s μ hpos hmass hgen z hE] with ω hω hmem
  exact finiteMeasure_tendsto_zero_of_absolutelyContinuous m
    (projectiveHittingMeasure Γ s z μ hpos hmass) hm _ (hω hmem)

end Singularity
