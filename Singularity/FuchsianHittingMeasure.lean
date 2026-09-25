import Singularity.ProjectiveNonelementaryDynamics
import Singularity.ProjectiveStationarity

/-!
# The actual hitting measure for every nonelementary Fuchsian group

For an arbitrary discrete nonelementary subgroup of PSL(2,R), a positive,
finitely supported semigroup-generating probability gives almost-sure geometric
convergence, exact stationarity, and equivalence with every group translate.
The spectral gap is proved from nonelementarity and is not a hypothesis.
The quotient need not be compact. Singularity in the noncocompact case remains
a separate theorem, not a consequence asserted in this module.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped MatrixGroups UpperHalfPlane Topology

namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen in
/-- The named projective law is an actual geometric hitting law, stationary and
quasi-invariant, for any nonelementary Fuchsian group. -/
theorem fuchsian_hittingMeasure_properties :
    (∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (projectiveBoundaryMap Γ s z ω)))) ∧
    projectiveHittingMeasure Γ s z μ hpos hmass =
      (∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℝ => (g : Γ) • p)
        (projectiveHittingMeasure Γ s z μ hpos hmass)) ∧
    ∀ g : Γ,
      Measure.map (fun p : OnePoint ℝ => g • p) (projectiveHittingMeasure Γ s z μ hpos hmass) ≪
        projectiveHittingMeasure Γ s z μ hpos hmass ∧
      projectiveHittingMeasure Γ s z μ hpos hmass ≪
        Measure.map (fun p : OnePoint ℝ => g • p) (projectiveHittingMeasure Γ s z μ hpos hmass) := by
  let : MeasurableSpace (projectiveSubgroupLift Γ) := ⊤
  let : MeasurableSingletonClass (projectiveSubgroupLift Γ) := inferInstance
  have hg := projectiveLiftSupport_generates_of_mass Γ s μ hmass hgen
  let : Countable (projectiveSubgroupLift Γ) := countable_of_finite_jump_generation _ hg
  let : MeasurableMul (projectiveSubgroupLift Γ) :=
    ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  have hr := projectiveNonelementary_lift_rightMarkov_gap Γ hne
    (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ)
    (projectiveLiftWeight_positive Γ s μ hpos) (projectiveLiftWeight_mass Γ s μ hmass) hg
  exact ⟨projectiveBoundaryMap_tendsto Γ s z μ hpos hmass hgen hr,
    projectiveHittingMeasure_stationary Γ s z μ hpos hmass hgen hr,
    projectiveHittingMeasure_translate_equivalent Γ s z μ hpos hmass hgen hr⟩

include hne hgen in
/-- Almost every original projective trajectory converges to the named boundary map. -/
theorem fuchsian_boundaryMap_tendsto :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (projectiveBoundaryMap Γ s z ω))) :=
  (fuchsian_hittingMeasure_properties Γ hne s μ hpos hmass hgen z).1

include hne hgen in
/-- The stationary equation holds with the original, possibly nonsymmetric jump law. -/
theorem fuchsian_hittingMeasure_stationary :
    projectiveHittingMeasure Γ s z μ hpos hmass =
      ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℝ => (g : Γ) • p)
        (projectiveHittingMeasure Γ s z μ hpos hmass) :=
  (fuchsian_hittingMeasure_properties Γ hne s μ hpos hmass hgen z).2.1

include hne hgen in
/-- Every translate of the hitting probability has the same null sets. -/
theorem fuchsian_hittingMeasure_translate_equivalent (g : Γ) :
    Measure.map (fun p : OnePoint ℝ => g • p) (projectiveHittingMeasure Γ s z μ hpos hmass) ≪
      projectiveHittingMeasure Γ s z μ hpos hmass ∧
    projectiveHittingMeasure Γ s z μ hpos hmass ≪
      Measure.map (fun p : OnePoint ℝ => g • p) (projectiveHittingMeasure Γ s z μ hpos hmass) :=
  (fuchsian_hittingMeasure_properties Γ hne s μ hpos hmass hgen z).2.2 g

include hne hgen in
/-- Any other almost-sure version of the geometric boundary limit has the same law. -/
theorem fuchsian_hittingMeasure_unique (b : (ℕ → s) → OnePoint ℝ)
    (hb : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (b ω)))) :
    walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b =
      projectiveHittingMeasure Γ s z μ hpos hmass := by
  apply Measure.map_congr
  filter_upwards [hb, fuchsian_boundaryMap_tendsto Γ hne s μ hpos hmass hgen z] with ω h₁ h₂
  exact compactBoundaryEmbedding_injective (tendsto_nhds_unique h₁ h₂)

end Singularity
