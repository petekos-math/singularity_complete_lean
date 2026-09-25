import Singularity.GeometricLiouvilleComparison
import Singularity.CocompactLiouvilleErgodicity

/-!
# Cocompact current comparison with ergodicity discharged

The actual cocompact lattice action is now proved ergodic for the explicit
Liouville current. The remaining inputs are hitting-measure absolute continuity
and the positive measurable kernel's covariance in the actual derivatives.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- Current proportionality in the cocompact case, with no ergodicity hypothesis. -/
theorem geometricKernelCurrent_eq_liouville_cocompact
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)
    (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)
    (hback : reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪
      compactPoissonMeasure UpperHalfPlane.I)
    (hforward : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪
      compactPoissonMeasure UpperHalfPlane.I)
    (K : BoundaryPair → ℝ) (hK : Measurable K) (hp : ∀ p, 0 < K p)
    (hcov : ∀ g : Γ, ∀ᵐ p ∂geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z,
      K (g⁻¹ • p) = K p /
        (stationaryRealDensity (reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z) g p.val.1 *
          stationaryRealDensity (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) g p.val.2)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K = c • compactLiouvilleCurrent := by
  let := compactLiouvilleCurrent_ergodic Γ
  exact geometricKernelCurrent_eq_liouville_of_ergodic Γ s μ hpos hmass hgen hgap z
    horbit hback hforward K hK hp hcov

end Singularity
