import Singularity.StripGreenDomination
import Singularity.CompactMartinMap
import Singularity.BoundaryPairTransitivity

/-!
# Separators in arbitrary boundary coordinates

An ambient hyperbolic isometry moves the strip, not the random walk. Jump
lengths are unchanged, and changing the basepoint in a triangle excess costs
at most twice the distance between the basepoints.
-/

noncomputable section
open Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- Every ordered distinct boundary pair has opposite finite coordinates. -/
theorem exists_opposite_boundary_chart (p : BoundaryPair) :
    ∃ B : SL(2, ℝ), B • p.val.1 = ((-1 : ℝ) : OnePoint ℝ) ∧
      B • p.val.2 = ((1 : ℝ) : OnePoint ℝ) := by
  let q : BoundaryPair := ⟨(((-1 : ℝ) : OnePoint ℝ), ((1 : ℝ) : OnePoint ℝ)), by norm_num⟩
  obtain ⟨B, hB⟩ := boundaryPair_pretransitive.exists_smul_eq p q
  exact ⟨B, congrArg (fun r : BoundaryPair => r.val.1) hB,
    congrArg (fun r : BoundaryPair => r.val.2) hB⟩

/-- A compact approach becomes a finite complex approach in an ambient chart. -/
theorem compact_approach_in_chart {ι : Type*} {l : Filter ι}
    (B : SL(2, ℝ)) (p : OnePoint ℝ) (ξ : ℝ) (hB : B • p = (ξ : OnePoint ℝ))
    (z : ι → ℍ)
    (hz : Tendsto (fun n => hyperbolicCompactEmbedding (z n)) l
      (𝓝 (compactBoundaryEmbedding p))) :
    Tendsto (fun n => ((B • z n : ℍ) : ℂ)) l (𝓝 (ξ : ℂ)) := by
  have ht := (continuous_const_smul B).continuousAt.tendsto.comp hz
  have he : B • compactBoundaryEmbedding p = compactBoundaryEmbedding (ξ : OnePoint ℝ) := by
    rw [← compactBoundaryEmbedding_smul, hB]
  rw [he] at ht
  change Tendsto (fun n => B • hyperbolicCompactEmbedding (z n)) l
    (𝓝 (((ξ : ℂ) : OnePoint ℂ))) at ht
  have hh : Tendsto (fun n => hyperbolicCompactEmbedding (B • z n)) l
      (𝓝 (((ξ : ℂ) : OnePoint ℂ))) := by
    simpa only [← hyperbolicCompactEmbedding_smul] using ht
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff.mpr hh

/-- The actual group vertices lying in the strip in the chart B. -/
def transverseJumpStrip (Γ : Subgroup SL(2, ℝ)) (s : Finset Γ) (B : SL(2, ℝ)) : Set Γ :=
  {g | B • (g • UpperHalfPlane.I) ∈
    axisRatioStrip (jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s))}

/-- Every allowed path joining the opposite chart sides meets the moved strip. -/
theorem transverseJumpStrip_separates (Γ : Subgroup SL(2, ℝ)) (s : Finset Γ)
    (B : SL(2, ℝ)) (x y : Γ)
    (hx : (B • (x • UpperHalfPlane.I)).re < 0)
    (hy : 0 ≤ (B • (y • UpperHalfPlane.I)).re) :
    SeparatesJumpPaths s (transverseJumpStrip Γ s B) x y := by
  apply separatesJumpPaths_of_invariant_side s _
    {g | (B • (g • UpperHalfPlane.I)).re < 0} _ x y hx (not_lt.mpr hy)
  intro g t ht hg hgt hgn
  apply bounded_jump_preserves_negative_side
    (finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s)
    (B • (g • UpperHalfPlane.I)) (B • ((g * t) • UpperHalfPlane.I)) _ hg hgt hgn
  rw [dist_smul, mul_smul]
  change dist ((g : SL(2, ℝ)) • UpperHalfPlane.I)
    ((g : SL(2, ℝ)) • (t • UpperHalfPlane.I)) ≤ _
  rw [dist_smul]
  exact dist_le_finiteJumpLengthBound Γ UpperHalfPlane.I s ht

/-- Moving the chart changes the triangle excess at i by a uniformly bounded amount. -/
theorem excess_le_chart_excess (B : SL(2, ℝ)) (z w : ℍ) :
    dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - dist z w ≤
      dist (B • z) UpperHalfPlane.I + dist (B • w) UpperHalfPlane.I -
      dist (B • z) (B • w) + 2 * dist UpperHalfPlane.I (B • UpperHalfPlane.I) := by
  have hz := dist_triangle (B • z) UpperHalfPlane.I (B • UpperHalfPlane.I)
  have hw := dist_triangle (B • w) UpperHalfPlane.I (B • UpperHalfPlane.I)
  simp only [dist_smul] at hz hw ⊢
  linarith

/-- Ordinary Ancona supplies square-summable envelopes on every moved strip. -/
theorem transverse_strip_green_domination
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (B : SL(2, ℝ)) {ι : Type*} {l : Filter ι} (x : ι → Γ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hx : Tendsto (fun n => ((B • (x n • UpperHalfPlane.I) : ℍ) : ℂ)) l (𝓝 (ξ : ℂ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in l, ∀ g ∈ transverseJumpStrip Γ s B,
      walkGreen s μ (x n) g / walkGreen s μ (x n) 1 ≤ C * walkGreen s μ 1 g ∧
      walkGreen s μ g (x n) / walkGreen s μ 1 (x n) ≤ C * walkGreen s μ g 1 := by
  obtain ⟨δ, hδ, hsep⟩ := eventually_cayley_separated_from_strip
    (jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s))
    (jumpStripRadius_pos (finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s)).le ξ hξ
    (fun n => B • (x n • UpperHalfPlane.I)) (halfPlaneCayley_tendsto_real _ ξ hx)
  obtain ⟨C, hC, hb⟩ := cocompact_excess_green_product_bound Γ s μ hpos hmass hgen hgap
    (2 * Real.log (4/δ) + 2 * dist UpperHalfPlane.I (B • UpperHalfPlane.I))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsep] with n hn
  intro g hg
  have he := (excess_le_chart_excess B (x n • UpperHalfPlane.I) (g • UpperHalfPlane.I)).trans
    (add_le_add (hyperbolic_excess_of_cayley_separation
      (B • (x n • UpperHalfPlane.I)) (B • (g • UpperHalfPlane.I)) δ hδ (hn _ hg)) le_rfl)
  have hr := hb (x n) 1 g (by simpa only [one_smul] using he)
  have hc := hb g 1 (x n) (by simpa only [one_smul, add_comm, dist_comm] using he)
  constructor
  · apply (div_le_iff₀ (walkGreen_pos s μ hpos hgen hgap (x n) 1)).mpr
    nlinarith only [hr]
  · apply (div_le_iff₀ (walkGreen_pos s μ hpos hgen hgap 1 (x n))).mpr
    nlinarith only [hc]

end Singularity
