import Singularity.GreenVisualUpper
import Singularity.CocompactHittingBounds

/-!
# The upper half of Green comparison from the cocompact current

The preceding current and density results now supply exponential Green upper
bounds for both the original and reflected walks with one common constant.
The lower half of Green comparison and the actual continuous covariant Naïm
kernel remain unproved. Both nonsingularity assumptions below are explicit.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- A continuous covariant current and nonsingular marginals give the upper Green-distance estimate for both walks. -/
theorem cocompact_current_Green_upper
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
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x y : Γ,
      walkGreen s μ x y ≤ C * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) ∧
      walkGreen (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) x y ≤
        C * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) := by
  obtain ⟨a,b,ha,hb,_,hlow,hupp⟩ := geometricHittingMeasure_bounds_of_nonsingular_continuous_current
    Γ s μ hpos hmass hgen hgap z horbit hback hforward K hK hp hcov
  let C := max 1 (2 * b * walkGreen s μ 1 1 / a)
  have hupper (x y : Γ) : walkGreen s μ x y ≤
      C * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) :=
    (geometricHittingMeasure_implies_Green_upper Γ s μ hpos hmass hgen hgap z
      a b ha hb.le hlow hupp x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  refine ⟨C, le_max_left _ _, fun x y => ⟨hupper x y, ?_⟩⟩
  rw [reflected_walkGreen s μ hgap]
  simpa only [dist_comm] using hupper y x

end Singularity
