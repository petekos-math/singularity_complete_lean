import Singularity.CocompactAxisAncona
import Singularity.HyperbolicAxisNormalization

/-!
# Two-sided Ancona inequalities along constructed geodesic segments

Each endpoint pair has a unit-speed geodesic line. Uniformly in the endpoints,
a middle orbit point at distance at most K from its segment satisfies both
multiplicative Green bounds. The lower bound is the first-hit inequality; the
upper bound uses the constructed shrinking-ball iteration.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Recenter the axis bound at any parameter in the endpoint interval. -/
theorem cocompact_axis_segment_green_upper (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (K : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (g : SL(2, ℝ)) (t u : ℝ), u ∈ Set.Icc 0 t →
      ∀ x o y : Γ, g • UpperHalfPlane.I = x • UpperHalfPlane.I →
      g • verticalHeightRay UpperHalfPlane.I t = y • UpperHalfPlane.I →
      dist (g • verticalHeightRay UpperHalfPlane.I u) (o • UpperHalfPlane.I) ≤ K →
      walkGreen s μ x y ≤ H * (walkGreen s μ x o * walkGreen s μ o y) := by
  obtain ⟨H, hH, hbound⟩ := cocompact_axis_green_product_bound Γ s μ hpos hmass hgen hgap K
  refine ⟨H, hH, ?_⟩
  intro g t u hu x o y hx hy ho
  apply hbound (g * dilationMatrix u) u (t-u) hu.1 (sub_nonneg.mpr hu.2) x o y
  · rw [mul_smul, verticalHeightRay_I_dilation]
    simpa only [add_neg_cancel, verticalHeightRay_zero] using hx
  · rw [mul_smul, verticalHeightRay_I_dilation]
    simpa only [add_sub_cancel] using hy
  · have hh := verticalHeightRay_I_dilation u 0
    simp only [verticalHeightRay_zero, add_zero] at hh
    simpa only [mul_smul, hh] using ho

/-- For every endpoint pair there is a unit-speed geodesic whose entire segment
satisfies two-sided Ancona inequalities with one uniform constant. No geometric
ball-sequence hypothesis or polynomial distance factor remains. -/
theorem cocompact_geodesic_ancona (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (K : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x y : Γ, ∃ c : ℝ → ℍ,
      Isometry c ∧ c 0 = x • UpperHalfPlane.I ∧
      c (dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) = y • UpperHalfPlane.I ∧
      ∀ t ∈ Set.Icc 0 (dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)),
      ∀ o : Γ, dist (c t) (o • UpperHalfPlane.I) ≤ K →
      (walkGreen s μ x o * walkGreen s μ o y) / C ≤ walkGreen s μ x y ∧
      walkGreen s μ x y ≤ C * (walkGreen s μ x o * walkGreen s μ o y) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨H, hH, hupper⟩ := cocompact_axis_segment_green_upper Γ s μ hpos hmass hgen hgap K
  let C := max H (walkGreen s μ 1 1)
  have hHC : H ≤ C := le_max_left _ _
  have hGC : walkGreen s μ 1 1 ≤ C := le_max_right _ _
  have hC : 1 ≤ C := (walkGreen_diag_ge_one s μ hμ hgap 1).trans hGC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C, hC, ?_⟩
  intro x y
  obtain ⟨g, hx, hy⟩ := exists_oriented_hyperbolic_axis (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)
  refine ⟨fun t => g • verticalHeightRay UpperHalfPlane.I t,
    isometry_hyperbolic_axis g, ?_, hy, ?_⟩
  · simpa only [verticalHeightRay_zero] using hx
  · intro t ht o ho
    constructor
    · apply (div_le_iff₀ hCpos).mpr
      have hdiag : walkGreen s μ o o = walkGreen s μ 1 1 := by
        simpa only [mul_one] using walkGreen_left s μ o 1 1
      have hlower := walkGreen_product_le s μ hμ hmass hgap x o y
      rw [hdiag] at hlower
      calc
        _ ≤ walkGreen s μ 1 1 * walkGreen s μ x y := hlower
        _ ≤ C * walkGreen s μ x y := mul_le_mul_of_nonneg_right hGC (walkGreen_nonneg s μ hμ x y)
        _ = _ := mul_comm _ _
    · exact (hupper g _ t ht x o y hx hy ho).trans (mul_le_mul_of_nonneg_right hHC
        (mul_nonneg (walkGreen_nonneg s μ hμ x o) (walkGreen_nonneg s μ hμ o y)))

end Singularity
