import Singularity.GeometricHittingMeasure

/-!
# Independence of the geometric base point and laws from other initial vertices

Bounded-distance paths have asymptotically identical Cayley coordinates when
one path has summable radial decay. This identifies the actual limit maps and
hitting measures for different points of the upper half-plane. Translating the
initial group vertex translates the boundary limit and its law.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- A bounded-distance companion has the same compact limit as a bounded-jump path
with summable radial decay. -/
theorem compact_tendsto_of_bounded_distance (z w : ℕ → ℍ) (L K : ℝ)
    (hjump : ∀ n, dist (z n) (z (n + 1)) ≤ L)
    (hclose : ∀ n, dist (w n) (z n) ≤ K)
    (hs : Summable (fun n => Real.exp (-dist (z n) UpperHalfPlane.I)))
    {p : OnePoint ℂ} (hz : Tendsto (fun n => hyperbolicCompactEmbedding (z n)) atTop (nhds p)) :
    Tendsto (fun n => hyperbolicCompactEmbedding (w n)) atTop (nhds p) := by
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete
    (cayley_cauchySeq_of_summable_escape z L hjump hs)
  have hd : Tendsto (fun n => dist (halfPlaneCayley (w n)) (halfPlaneCayley (z n)))
      atTop (nhds 0) := by
    apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (by simpa using hs.tendsto_atTop_zero.const_mul (4 * Real.exp K))
    rw [dist_comm]
    exact halfPlaneCayley_dist_le _ _ K (by simpa only [dist_comm] using hclose n)
  have hwq : Tendsto (fun n => halfPlaneCayley (w n)) atTop (nhds q) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) (fun n => dist_triangle _ _ _)
    simpa using hd.add (tendsto_iff_dist_tendsto_zero.mp hq)
  have hp := tendsto_nhds_unique hz (cayley_tendsto_compact hq)
  rw [hp]
  exact cayley_tendsto_compact hwq

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ)
  (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

/-- The chosen boundary maps for two geometric base points agree almost surely. -/
theorem geometricBoundaryMap_basepoint_ae (z w : ℍ) :
    geometricBoundaryMap Γ s μ hpos hmass hgen hgap z =ᵐ[infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass]
      geometricBoundaryMap Γ s μ hpos hmass hgen hgap w := by
  filter_upwards [walk_ae_hyperbolic_radial_summable Γ s μ (fun g hg => (hpos g hg).le) hmass hgap 1 z,
    geometricBoundaryMap_tendsto Γ s μ hpos hmass hgen hgap z,
    geometricBoundaryMap_tendsto Γ s μ hpos hmass hgen hgap w] with ω hs hz hw
  have hc (n : ℕ) : dist (walkPosition s 1 n ω • w) (walkPosition s 1 n ω • z) ≤ dist w z := by
    change dist (((walkPosition s 1 n ω : Γ) : SL(2, ℝ)) • w)
      (((walkPosition s 1 n ω : Γ) : SL(2, ℝ)) • z) ≤ _
    rw [dist_smul]
  have hw' := compact_tendsto_of_bounded_distance _ _ (finiteJumpLengthBound Γ z s) (dist w z)
    (walkPosition_hyperbolic_jump_bound Γ s z 1 ω) hc hs hz
  exact compactBoundaryEmbedding_injective (tendsto_nhds_unique hw' hw)

/-- The actual geometric hitting measure is independent of the base point in the half-plane. -/
theorem geometricHittingMeasure_basepoint (z w : ℍ) :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z =
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap w :=
  Measure.map_congr (geometricBoundaryMap_basepoint_ae Γ s μ hpos hmass hgen hgap z w)

/-- The visual-singularity statement is also independent of the geometric base point. -/
theorem geometricHittingMeasure_basepoint_singularity_iff (z w : ℍ) :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z ↔
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap w ⟂ₘ compactPoissonMeasure w := by
  rw [geometricHittingMeasure_singularity_iff, geometricHittingMeasure_singularity_iff,
    geometricHittingMeasure_basepoint Γ s μ hpos hmass hgen hgap z w]

/-- Starting the group walk at x translates its actual boundary limit by x. -/
theorem geometricBoundaryMap_start_tendsto (z : ℍ) (x : Γ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s x n ω • z)) atTop
        (nhds (compactBoundaryEmbedding (x • geometricBoundaryMap Γ s μ hpos hmass hgen hgap z ω))) := by
  filter_upwards [geometricBoundaryMap_tendsto Γ s μ hpos hmass hgen hgap z] with ω hω
  have h := (continuous_const_smul (x : SL(2, ℝ))).continuousAt.tendsto.comp hω
  have hpath (n : ℕ) : walkPosition s x n ω = x * walkPosition s 1 n ω := by
    simpa only [mul_one] using walkPosition_left s x 1 n ω
  have hpath' : (fun n => hyperbolicCompactEmbedding (walkPosition s x n ω • z)) =
      (fun n => (x : SL(2, ℝ)) • hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) := by
    funext n
    rw [hpath]
    exact compactOrbit_equivariant Γ z x _
  have hb : compactBoundaryEmbedding (x • geometricBoundaryMap Γ s μ hpos hmass hgen hgap z ω) =
      (x : SL(2, ℝ)) • compactBoundaryEmbedding (geometricBoundaryMap Γ s μ hpos hmass hgen hgap z ω) :=
    compactBoundaryEmbedding_smul (x : SL(2, ℝ)) _
  rw [hpath', hb]
  exact h

/-- The translated measure is precisely the law of the boundary limit from the translated initial vertex. -/
theorem geometricHittingMeasure_start_law (z : ℍ) (x : Γ) :
    walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass
      (fun ω => x • geometricBoundaryMap Γ s μ hpos hmass hgen hgap z ω) =
      Measure.map (fun p : OnePoint ℝ => x • p) (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) := by
  rw [geometricHittingMeasure, walkBoundaryLaw, walkBoundaryLaw,
    Measure.map_map (measurable_const_smul x) (measurable_geometricBoundaryMap Γ s μ hpos hmass hgen hgap z)]
  rfl

end Singularity
