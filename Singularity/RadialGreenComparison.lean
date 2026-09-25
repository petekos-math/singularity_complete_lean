import Singularity.RadialCayleySeparation
import Singularity.CocompactExcessAncona

/-!
# Ordinary Green comparison across whole radial regions

The radial separation geometry applies uniformly to every point of each
region, including arbitrarily distant points along an infinite barrier.
Combining it with the proved ordinary Ancona inequality gives the corresponding
unrestricted Green product bound. Its killed-domain counterpart remains separate.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Uniform ordinary Green product comparison for endpoints on opposite sides
of a radial gap, with the center close to the intermediate axis point. -/
theorem cocompact_radial_separated_green_product_bound
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (E : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : SL(2, ℝ)) (t : ℝ) (x o y : Γ),
      axisRadialCoordinate (q • (x • UpperHalfPlane.I)) ≤ t-Real.log 4 →
      t+Real.log 4 ≤ axisRadialCoordinate (q • (y • UpperHalfPlane.I)) →
      dist (q • (o • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I t) ≤ E →
      walkGreen s μ x y ≤ C * (walkGreen s μ x o * walkGreen s μ o y) := by
  obtain ⟨C,hC,hbound⟩ := cocompact_excess_green_product_bound Γ s μ hpos hmass hgen hgap (2*Real.log 4+2*E)
  refine ⟨C,hC,?_⟩
  intro q t x o y hx hy ho
  apply hbound x o y
  have hh := radial_opposite_triangle_excess_near_axis
    (q • (x • UpperHalfPlane.I)) (q • (y • UpperHalfPlane.I))
    (q • (o • UpperHalfPlane.I)) t E hx hy ho
  simpa only [dist_smul] using hh

end Singularity
