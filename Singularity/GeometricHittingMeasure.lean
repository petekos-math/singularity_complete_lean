import Singularity.RealGeometricHittingLaw
import Singularity.StationaryDensity
import Singularity.BoundaryMeasureClasses

/-!
# The geometric hitting measure and its actual Radon--Nikodym kernels

A measurable version of the constructed real-projective limit defines a named
hitting measure. Its law is independent of the version on null sets. Its
Radon--Nikodym kernels satisfy the already established normalization, positivity,
harmonicity, and cocycle identities. Identification with Martin kernels is proved downstream in
`HittingMartinDensity.lean` under the cocompact hypotheses.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ)
  (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)

/-- A measurable real-projective version of the actual random-walk limit. -/
def geometricBoundaryMap : (ℕ → s) → OnePoint ℝ :=
  (exists_real_geometric_hittingLaw Γ s μ hpos hmass hgen hgap z).choose

theorem measurable_geometricBoundaryMap :
    Measurable (geometricBoundaryMap Γ s μ hpos hmass hgen hgap z) :=
  (exists_real_geometric_hittingLaw Γ s μ hpos hmass hgen hgap z).choose_spec.1

/-- The chosen map is the limit of the orbit positions for almost every path. -/
theorem geometricBoundaryMap_tendsto :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (nhds (compactBoundaryEmbedding (geometricBoundaryMap Γ s μ hpos hmass hgen hgap z ω))) :=
  (exists_real_geometric_hittingLaw Γ s μ hpos hmass hgen hgap z).choose_spec.2.1

/-- The geometric hitting measure is the distribution of that actual limit. -/
def geometricHittingMeasure : Measure (OnePoint ℝ) :=
  walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass
    (geometricBoundaryMap Γ s μ hpos hmass hgen hgap z)

theorem geometricHittingMeasure_probability :
    IsProbabilityMeasure (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) :=
  (exists_real_geometric_hittingLaw Γ s μ hpos hmass hgen hgap z).choose_spec.2.2.1

/-- Exact stationarity holds for the named hitting measure. -/
theorem geometricHittingMeasure_stationary :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z =
      ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℝ => (g : Γ) • p)
        (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) :=
  (exists_real_geometric_hittingLaw Γ s μ hpos hmass hgen hgap z).choose_spec.2.2.2.1

/-- Every group translate of the named hitting law is equivalent to it. -/
theorem geometricHittingMeasure_translate_equivalent (g : Γ) :
    Measure.map (fun p : OnePoint ℝ => g • p) (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) ≪
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ∧
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪
      Measure.map (fun p : OnePoint ℝ => g • p) (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) :=
  (exists_real_geometric_hittingLaw Γ s μ hpos hmass hgen hgap z).choose_spec.2.2.2.2 g

/-- Any other measurable version of the same path limit has exactly this law. -/
theorem geometricHittingMeasure_unique (b : (ℕ → s) → OnePoint ℝ)
    (hl : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (nhds (compactBoundaryEmbedding (b ω)))) :
    walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b =
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z := by
  apply Measure.map_congr
  filter_upwards [hl, geometricBoundaryMap_tendsto Γ s μ hpos hmass hgen hgap z] with ω h1 h2
  exact compactBoundaryEmbedding_injective (tendsto_nhds_unique h1 h2)

/-- Actual hitting derivatives reconstruct the translates of the constructed hitting measure. -/
theorem geometricHittingMeasure_withDensity (g : Γ) :
    (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z).withDensity
      (stationaryDensity (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) g) =
      Measure.map (fun p : OnePoint ℝ => g • p) (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) := by
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact stationaryDensity_withDensity s μ hpos hgen _
    (geometricHittingMeasure_stationary Γ s μ hpos hmass hgen hgap z) g

/-- These derivatives form positive normalized real harmonic functions almost everywhere. -/
theorem geometricHittingMeasure_density_harmonic :
    let ν := geometricHittingMeasure Γ s μ hpos hmass hgen hgap z
    ∀ᵐ ξ ∂ν, stationaryRealDensity ν (1 : Γ) ξ = 1 ∧
      ∀ x : Γ, 0 < stationaryRealDensity ν x ξ ∧
        stationaryRealDensity ν x ξ = ∑ g : s, μ g * stationaryRealDensity ν (x * g) ξ := by
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact stationaryRealDensity_ae_harmonic s μ hpos hgen _
    (geometricHittingMeasure_stationary Γ s μ hpos hmass hgen hgap z)

/-- The Radon--Nikodym cocycle belongs to the actual hitting law. -/
theorem geometricHittingMeasure_density_cocycle (g h : Γ) :
    let ν := geometricHittingMeasure Γ s μ hpos hmass hgen hgap z
    ∀ᵐ ξ ∂ν, stationaryDensity ν (g * h) ξ =
      stationaryDensity ν g ξ * stationaryDensity ν h (g⁻¹ • ξ) := by
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact stationaryDensity_cocycle s μ hpos hgen _
    (geometricHittingMeasure_stationary Γ s μ hpos hmass hgen hgap z) g h

/-- The desired singularity conclusion can be tested in the analytic real chart. -/
theorem geometricHittingMeasure_singularity_iff :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z ↔
      finiteBoundaryMeasure (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) ⟂ₘ volume :=
  compact_hitting_singularity_iff _ z

end Singularity
