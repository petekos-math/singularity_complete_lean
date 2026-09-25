import Singularity.LiouvilleInvariance
import Singularity.GeometricKernelCurrent

/-!
# Comparison with the concrete Liouville reference current

The reference current is now constructed, has the classical chart density,
and is invariant under the full special-linear group. For the actual hitting
marginals, the remaining rigidity, kernel, and ergodicity hypotheses imply
proportionality. This theorem keeps those unproved hypotheses explicit.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- The concrete hitting-law current is a positive finite multiple of the concrete
Liouville current, conditional on the missing rigidity, covariance, and ergodicity inputs. -/
theorem geometricKernelCurrent_eq_liouville_of_ergodic
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    [ErgodicSMul Γ BoundaryPair compactLiouvilleCurrent]
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
  have := compactLiouvilleCurrent_sigmaFinite
  let : NeZero compactLiouvilleCurrent := ⟨compactLiouvilleCurrent_ne_zero⟩
  have := geometricKernelCurrent_sigmaFinite Γ s μ hpos hmass hgen hgap z K
  let : NeZero (geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K) :=
    ⟨geometricKernelCurrent_ne_zero Γ s μ hpos hmass hgen hgap z horbit K hK hp⟩
  apply invariantMeasure_eq_pos_finite_smul_of_maps (G := Γ)
    compactLiouvilleCurrent (geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K)
  · exact fun g => geometricKernelCurrent_invariant Γ s μ hpos hmass hgen hgap z horbit K hK g (hcov g)
  · have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
    exact boundaryPairCurrent_absolutelyContinuous_liouville _ _ hback hforward K

end Singularity
