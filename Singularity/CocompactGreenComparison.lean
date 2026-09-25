import Singularity.GreenVisualLower
import Singularity.CocompactHittingBounds
import Singularity.GreenPoissonBounds

/-!
# Full Green comparison from the conditional cocompact current argument

The constructed current comparison supplies visual density bounds. The proved
Martin identification and Ancona estimates now supply both sharp Green bounds.
The positive continuous covariant current kernel and the two nonsingularity
inputs remain explicit; this theorem does not construct that kernel.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal
namespace Singularity

/-- Visual bounds for the forward hitting law supply the exact comparison
predicate used by the separator-limit modules, for both walks. -/
theorem geometricHittingMeasure_GreenDistanceComparison
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) (z : ℍ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlow : ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I ≤
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z)
    (hupp : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≤
      ENNReal.ofReal b • compactPoissonMeasure UpperHalfPlane.I) :
    ∃ C : ℝ, 1 ≤ C ∧ GreenDistanceComparison Γ s μ C ∧
      GreenDistanceComparison Γ (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) C := by
  obtain ⟨C, hC, h⟩ := geometricHittingMeasure_implies_Green_comparison Γ s μ hpos hmass hgen hgap
    horbit z a b ha hb hlow hupp
  exact ⟨C, hC, fun x y => (h x y).1, fun x y => (h x y).2⟩

/-- The continuous-current argument now yields the full sharp Green comparison.
Its kernel and marginal nonsingularity assumptions remain explicit. -/
theorem cocompact_current_Green_comparison
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)
    (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)
    (hback : ¬ reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z)
    (hforward : ¬ geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z)
    (K : BoundaryPair → ℝ) (hK : Continuous K) (hp : ∀ p, 0 < K p)
    (hcov : ∀ g : Γ, ∀ᵐ p ∂geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z,
      K (g⁻¹ • p) = K p /
        (stationaryRealDensity (reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z) g p.val.1 *
          stationaryRealDensity (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) g p.val.2)) :
    ∃ C : ℝ, 1 ≤ C ∧ GreenDistanceComparison Γ s μ C ∧
      GreenDistanceComparison Γ (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) C := by
  obtain ⟨a, b, ha, hb, _, hlow, hupp⟩ := geometricHittingMeasure_bounds_of_nonsingular_continuous_current
    Γ s μ hpos hmass hgen hgap z horbit hback hforward K hK hp hcov
  exact geometricHittingMeasure_GreenDistanceComparison Γ s μ hpos hmass hgen hgap (horbit ∞) z
    a b ha hb hlow hupp

end Singularity
