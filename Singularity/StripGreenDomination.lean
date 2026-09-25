import Singularity.StripBoundarySeparation
import Singularity.CocompactExcessAncona
import Singularity.GeometricStrip
import Singularity.GreenVanishing

/-!
# Square-summable strip domination directly from ordinary Ancona

Disk separation of a transverse boundary approach from the entire strip gives
one Ancona constant for every strip vertex. The normalized row and column are
therefore dominated by multiples of the fixed base Green row and column.
Those are square summable by the spectral gap. No visual density or sharp
Green-distance comparison is assumed.
-/

noncomputable section
open Filter Set
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Ordinary Ancona bounds all strip coordinates at once along an arbitrary
approach to a nonzero finite endpoint. -/
theorem cocompact_strip_green_domination
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    {ι : Type*} {l : Filter ι} (x : ι → Γ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hx : Tendsto (fun n => ((x n • UpperHalfPlane.I : ℍ) : ℂ)) l (𝓝 (ξ : ℂ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in l, ∀ g ∈ finiteJumpStrip Γ UpperHalfPlane.I s,
      walkGreen s μ (x n) g / walkGreen s μ (x n) 1 ≤ C * walkGreen s μ 1 g ∧
      walkGreen s μ g (x n) / walkGreen s μ 1 (x n) ≤ C * walkGreen s μ g 1 := by
  obtain ⟨δ, hδ, hsep⟩ := eventually_cayley_separated_from_strip
    (jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s))
    (jumpStripRadius_pos (finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s)).le ξ hξ
    (fun n => x n • UpperHalfPlane.I) (halfPlaneCayley_tendsto_real _ ξ hx)
  obtain ⟨C, hC, hb⟩ := cocompact_disk_separated_green_product_bound Γ s μ hpos hmass hgen hgap δ hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsep] with n hn
  intro g hg
  have hr := hb (x n) g (hn _ hg)
  have hc := hb g (x n) (by simpa only [dist_comm] using hn _ hg)
  constructor
  · apply (div_le_iff₀ (walkGreen_pos s μ hpos hgen hgap (x n) 1)).mpr
    nlinarith only [hr]
  · apply (div_le_iff₀ (walkGreen_pos s μ hpos hgen hgap 1 (x n))).mpr
    nlinarith only [hc]

/-- The two fixed Green envelopes furnished by the strip comparison are
square summable on the whole group. -/
theorem green_envelopes_square_summable {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (C D : ℝ) :
    Summable (fun g => (C * walkGreen s μ 1 g) ^ 2) ∧
      Summable (fun g => (D * walkGreen s μ g 1) ^ 2) := by
  constructor
  · simpa only [mul_pow] using (walkGreen_row_square_summable s μ hgap 1).mul_left (C ^ 2)
  · simpa only [mul_pow] using (walkGreen_column_square_summable s μ hgap 1).mul_left (D ^ 2)

end Singularity
