import Singularity.InvariantMean
import Singularity.GeometricHittingMeasure

/-!
# Hitting laws from nonamenability

The classical absence of an invariant mean now supplies the spectral gap used
by the geometric boundary construction. No separate operator assumption,
Green-distance comparison, symmetry, or laziness is needed here.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- The actual random-walk limit and hitting law take values on the compact real boundary. -/
theorem exists_real_geometric_hittingLaw_of_nonamenable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hnon : ¬HasInvariantMean Γ) (z : ℍ) :
    ∃ b : (ℕ → s) → OnePoint ℝ, Measurable b ∧
      (∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
        Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z))
          atTop (nhds (compactBoundaryEmbedding (b ω)))) ∧
      let ν := walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b
      IsProbabilityMeasure ν ∧
      ν = (∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℝ => (g : Γ) • p) ν) ∧
      ∀ g : Γ, Measure.map (fun p : OnePoint ℝ => g • p) ν ≪ ν ∧
        ν ≪ Measure.map (fun p : OnePoint ℝ => g • p) ν := by
  exact exists_real_geometric_hittingLaw Γ s μ hpos hmass hgen
    (rightMarkov_nonamenable_spectral_gap s μ hpos hmass hgen hnon) z

end Singularity
