import Singularity.AxisTriangleExcess
import Singularity.CocompactGeodesicAncona

/-!
# Uniform Ancona upper bounds from bounded triangle excess

The explicit balanced-point construction discharges the segment-neighborhood
condition for an arbitrary triple. In particular, positive disk separation at
the basepoint gives a uniform Green product bound with no endpoint restriction.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

theorem cocompact_excess_green_product_bound (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ x o y : Γ,
      dist (x • UpperHalfPlane.I) (o • UpperHalfPlane.I) +
      dist (y • UpperHalfPlane.I) (o • UpperHalfPlane.I) -
      dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      walkGreen s μ x y ≤ H * (walkGreen s μ x o * walkGreen s μ o y) := by
  obtain ⟨H, hH, hb⟩ := cocompact_axis_segment_green_upper Γ s μ hpos hmass hgen hgap (D/2 + Real.log 4)
  refine ⟨H, hH, ?_⟩
  intro x o y he
  obtain ⟨g, u, hx, hy, hu, ho⟩ := exists_axis_point_of_triangle_excess
    (x • UpperHalfPlane.I) (o • UpperHalfPlane.I) (y • UpperHalfPlane.I) D he
  exact hb g _ u hu x o y hx hy ho

/-- Positive separation in the disk yields a uniform product bound at i. -/
theorem cocompact_disk_separated_green_product_bound (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℝ, 0 < H ∧ ∀ x y : Γ,
      δ ≤ dist (halfPlaneCayley (x • UpperHalfPlane.I)) (halfPlaneCayley (y • UpperHalfPlane.I)) →
      walkGreen s μ x y ≤ H * (walkGreen s μ x 1 * walkGreen s μ 1 y) := by
  obtain ⟨H, hH, hb⟩ := cocompact_excess_green_product_bound Γ s μ hpos hmass hgen hgap (2 * Real.log (4/δ))
  refine ⟨H, hH, ?_⟩
  intro x y hsep
  apply hb x 1 y
  simpa only [one_smul] using hyperbolic_excess_of_cayley_separation
    (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) δ hδ hsep

end Singularity
