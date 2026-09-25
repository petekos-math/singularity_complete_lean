import Singularity.HittingMartinIntegral
import Singularity.RealBoundaryTransport

/-!
# Identifying the actual hitting derivatives with Martin kernels

Bounded continuous tests on the ambient compact sphere determine the pushed
measures. Injectivity of the boundary embedding gives the exact change-of-measure
identity on the real projective boundary, and Radon--Nikodym uniqueness identifies
the actual hitting derivative.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint BoundedContinuousFunction
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

/-- The constructed Martin kernel is the exact density of the translated actual
hitting measure. -/
theorem geometricHittingMeasure_martin_withDensity (x : Γ) :
    Measure.map (fun p : OnePoint ℝ => x • p)
      (geometricHittingMeasure Γ s μ hpos hmass hgen hgap UpperHalfPlane.I) =
    (geometricHittingMeasure Γ s μ hpos hmass hgen hgap UpperHalfPlane.I).withDensity
      (fun p => ENNReal.ofReal ((compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x)) := by
  let ν := geometricHittingMeasure Γ s μ hpos hmass hgen hgap UpperHalfPlane.I
  let K := fun p => (compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x
  have hK : Continuous K := continuous_compactMartinPoint_eval Γ s μ hpos hmass hgen hgap horbit x
  have hKpos (p : OnePoint ℝ) : 0 < K p :=
    martinBoundaryKernel_pos s μ hpos hgen hgap 1 x _
  let : IsProbabilityMeasure ν := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap _
  let : IsLocallyFiniteMeasure (ν.withDensity (fun p => ENNReal.ofReal (K p))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hK
  change Measure.map (fun p : OnePoint ℝ => x • p) ν = ν.withDensity (fun p => ENNReal.ofReal (K p))
  apply measurableEmbedding_compactBoundaryEmbedding.map_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map_of_stronglyMeasurable continuous_compactBoundaryEmbedding.measurable
    φ.continuous.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_const_smul x)
      (show StronglyMeasurable (fun p => φ (compactBoundaryEmbedding p)) from
        (φ.continuous.comp continuous_compactBoundaryEmbedding).stronglyMeasurable),
    integral_map_of_stronglyMeasurable continuous_compactBoundaryEmbedding.measurable
      φ.continuous.stronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hK.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hKpos _).le, smul_eq_mul]
  change (∫ p, φ (compactBoundaryEmbedding (x • p))
      ∂Measure.map (geometricBoundaryMap Γ s μ hpos hmass hgen hgap UpperHalfPlane.I)
        (infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass)) =
    ∫ p, K p * φ (compactBoundaryEmbedding p)
      ∂Measure.map (geometricBoundaryMap Γ s μ hpos hmass hgen hgap UpperHalfPlane.I)
        (infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass)
  rw [integral_map_of_stronglyMeasurable
      (measurable_geometricBoundaryMap Γ s μ hpos hmass hgen hgap UpperHalfPlane.I)
      (show StronglyMeasurable (fun p : OnePoint ℝ => φ (compactBoundaryEmbedding (x • p))) from
        (φ.continuous.comp (continuous_compactBoundaryEmbedding.comp (continuous_const_smul x))).stronglyMeasurable),
    integral_map_of_stronglyMeasurable
      (measurable_geometricBoundaryMap Γ s μ hpos hmass hgen hgap UpperHalfPlane.I)
      (show StronglyMeasurable (fun p => K p * φ (compactBoundaryEmbedding p)) from
        (hK.mul (φ.continuous.comp continuous_compactBoundaryEmbedding)).stronglyMeasurable)]
  exact geometricBoundaryMap_martin_integral Γ s μ hpos hmass hgen hgap horbit x φ

/-- The extended actual Radon--Nikodym derivative equals the constructed Martin kernel. -/
theorem geometricHittingMeasure_density_eq_martin (x : Γ) :
    let ν := geometricHittingMeasure Γ s μ hpos hmass hgen hgap UpperHalfPlane.I
    stationaryDensity ν x =ᵐ[ν]
      (fun p => ENNReal.ofReal ((compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x)) := by
  dsimp only
  let := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap UpperHalfPlane.I
  unfold stationaryDensity
  rw [geometricHittingMeasure_martin_withDensity Γ s μ hpos hmass hgen hgap horbit x]
  exact Measure.rnDeriv_withDensity _
    (continuous_compactMartinPoint_eval Γ s μ hpos hmass hgen hgap horbit x).measurable.ennreal_ofReal

/-- The real actual hitting derivative equals the positive Martin kernel almost everywhere. -/
theorem geometricHittingMeasure_realDensity_eq_martin (x : Γ) :
    let ν := geometricHittingMeasure Γ s μ hpos hmass hgen hgap UpperHalfPlane.I
    stationaryRealDensity ν x =ᵐ[ν]
      (fun p => (compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x) := by
  filter_upwards [geometricHittingMeasure_density_eq_martin Γ s μ hpos hmass hgen hgap horbit x]
    with p hp
  change (stationaryDensity _ x p).toReal = _
  rw [hp]
  exact ENNReal.toReal_ofReal (martinBoundaryKernel_pos s μ hpos hgen hgap 1 x
    (compactMartinPoint Γ s μ hpos hgen hgap horbit p)).le

end Singularity
