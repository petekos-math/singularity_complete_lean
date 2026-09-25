import Singularity.CompactMartinMap

/-!
# Continuity on the entire compact geometric boundary

Diagonal selection of actual orbit approximations upgrades arbitrary-approach
Martin convergence to continuity, including at infinity.
-/

noncomputable section
open Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

include hmass in
/-- Every evaluation of the compact geometric Martin map is continuous. -/
theorem continuous_compactMartinPoint_eval (x : Γ) :
    Continuous (fun p => (compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x) := by
  let : MetricSpace (OnePoint ℂ) := TopologicalSpace.metrizableSpaceMetric (OnePoint ℂ)
  apply continuous_iff_seqContinuous.mpr
  intro p q hp
  choose y hy using fun n => exists_compact_boundary_orbit_approach Γ horbit (p n)
  have hchoose (n : ℕ) : ∃ m : ℕ,
      dist (hyperbolicCompactEmbedding (y n m • UpperHalfPlane.I)) (compactBoundaryEmbedding (p n)) <
        1 / ((n : ℝ) + 1) ∧
      dist (martinQuotient s μ 1 x (y n m))
        ((compactMartinPoint Γ s μ hpos hgen hgap horbit (p n)).val x) < 1 / ((n : ℝ) + 1) := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hg := (hy n).eventually (Metric.ball_mem_nhds _ hε)
    have hm := (compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit (p n)
      (y n) (hy n) x).eventually (Metric.ball_mem_nhds _ hε)
    exact (hg.and hm).exists
  choose m hmg hmm using hchoose
  let z : ℕ → Γ := fun n => y n (m n)
  have hd : Tendsto (fun n => dist (compactBoundaryEmbedding (p n))
      (hyperbolicCompactEmbedding (z n • UpperHalfPlane.I))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [dist_comm]
    exact (hmg n).le
  have hz := (continuous_compactBoundaryEmbedding.continuousAt.tendsto.comp hp).congr_dist hd
  have hq := compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit q z hz x
  apply hq.congr_dist
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hmm n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

include hmass in
/-- The geometric Martin map is continuous on the compact real projective line. -/
theorem continuous_compactMartinPoint :
    Continuous (compactMartinPoint Γ s μ hpos hgen hgap horbit) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi (continuous_compactMartinPoint_eval Γ s μ hpos hmass hgen hgap horbit)

end Singularity
