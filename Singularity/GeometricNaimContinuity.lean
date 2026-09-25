import Singularity.GeometricNaimKernel

/-!
# Joint continuity of the full geometric Naïm kernel

A diagonal choice of orbit approximations reduces boundary-pair continuity to
the proved arbitrary-approach quotient limit, including at infinity.
-/

noncomputable section
open Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

/-- The actual Naïm kernel is jointly continuous off the diagonal. -/
theorem continuous_geometricNaimKernel :
    Continuous (geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit) := by
  let : MetricSpace (OnePoint ℂ) := TopologicalSpace.metrizableSpaceMetric (OnePoint ℂ)
  apply continuous_iff_seqContinuous.mpr
  intro p q hp
  let T := geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit
  choose x hx using fun n => exists_compact_boundary_orbit_approach Γ horbit (p n).val.1
  choose y hy using fun n => exists_compact_boundary_orbit_approach Γ horbit (p n).val.2
  have hchoose (n : ℕ) : ∃ k : ℕ,
      dist (hyperbolicCompactEmbedding (x n k • UpperHalfPlane.I)) (compactBoundaryEmbedding (p n).val.1) <
        1 / ((n : ℝ) + 1) ∧
      dist (hyperbolicCompactEmbedding (y n k • UpperHalfPlane.I)) (compactBoundaryEmbedding (p n).val.2) <
        1 / ((n : ℝ) + 1) ∧
      dist (finiteNaimQuotient s μ 1 (x n k) (y n k)) (T (p n)) < 1 / ((n : ℝ) + 1) := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hx' := (hx n).eventually (Metric.ball_mem_nhds _ hε)
    have hy' := (hy n).eventually (Metric.ball_mem_nhds _ hε)
    have hθ := (geometricNaimKernel_tendsto Γ s μ hpos hmass hgen hgap horbit (p n)
      (x n) (y n) (hx n) (hy n)).eventually (Metric.ball_mem_nhds _ hε)
    exact (hx'.and (hy'.and hθ)).exists
  choose k hkx hky hkθ using hchoose
  let u : ℕ → Γ := fun n => x n (k n)
  let v : ℕ → Γ := fun n => y n (k n)
  have hpx : Tendsto (fun n => compactBoundaryEmbedding (p n).val.1) atTop
      (𝓝 (compactBoundaryEmbedding q.val.1)) :=
    (continuous_compactBoundaryEmbedding.comp (continuous_fst.comp continuous_subtype_val)).continuousAt.tendsto.comp hp
  have hpy : Tendsto (fun n => compactBoundaryEmbedding (p n).val.2) atTop
      (𝓝 (compactBoundaryEmbedding q.val.2)) :=
    (continuous_compactBoundaryEmbedding.comp (continuous_snd.comp continuous_subtype_val)).continuousAt.tendsto.comp hp
  have hdx : Tendsto (fun n => dist (compactBoundaryEmbedding (p n).val.1)
      (hyperbolicCompactEmbedding (u n • UpperHalfPlane.I))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [dist_comm]
    exact (hkx n).le
  have hdy : Tendsto (fun n => dist (compactBoundaryEmbedding (p n).val.2)
      (hyperbolicCompactEmbedding (v n • UpperHalfPlane.I))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [dist_comm]
    exact (hky n).le
  have ht := geometricNaimKernel_tendsto Γ s μ hpos hmass hgen hgap horbit q u v
    (hpx.congr_dist hdx) (hpy.congr_dist hdy)
  apply ht.congr_dist
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hkθ n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end Singularity
