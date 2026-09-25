import Singularity.GeometricMartinConvergence

/-!
# Continuity of the finite real Martin boundary map

For a convergent sequence of boundary coordinates, choose one sufficiently late
point from each of their orbit rays, approximating both the endpoint and one
Martin coordinate. The proved arbitrary-approach convergence identifies the
limit, giving continuity in the product topology.
-/

noncomputable section
open Filter Set
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hmass in
/-- Every evaluation coordinate of the geometric ray Martin map is continuous
on the whole finite real boundary chart. -/
theorem continuous_rayMartinPoint_eval (x : Γ) :
    Continuous (fun ξ : ℝ => (rayMartinPoint Γ s μ hpos hgen hgap ξ).val x) := by
  apply continuous_iff_seqContinuous.mpr
  intro ξ ζ hξ
  have hchoose (n : ℕ) : ∃ m : ℕ,
      dist (((cocompactRaySequence Γ (ξ n) m) • UpperHalfPlane.I : ℍ) : ℂ) (ξ n : ℂ) <
        1 / ((n : ℝ) + 1) ∧
      dist (martinQuotient s μ 1 x (cocompactRaySequence Γ (ξ n) m))
        ((rayMartinPoint Γ s μ hpos hgen hgap (ξ n)).val x) < 1 / ((n : ℝ) + 1) := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hg := (cocompactRaySequence_tendsto Γ (ξ n)).eventually (Metric.ball_mem_nhds _ hε)
    have hm := (rayMartinPoint_tendsto Γ s μ hpos hmass hgen hgap (ξ n) x).eventually
      (Metric.ball_mem_nhds _ hε)
    exact (hg.and hm).exists
  choose m hmg hmm using hchoose
  let y : ℕ → Γ := fun n => cocompactRaySequence Γ (ξ n) (m n)
  have hdist : Tendsto (fun n => dist (ξ n : ℂ) ((y n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [dist_comm]
    exact (hmg n).le
  have hy : Tendsto (fun n => ((y n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (ζ : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hξ).congr_dist hdist
  have hq := real_boundary_martin_tendsto Γ s μ hpos hmass hgen hgap ζ y hy x
  apply hq.congr_dist
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hmm n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

include hmass in
/-- The finite real boundary maps continuously into the actual Martin boundary. -/
theorem continuous_rayMartinPoint :
    Continuous (rayMartinPoint Γ s μ hpos hgen hgap) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi (continuous_rayMartinPoint_eval Γ s μ hpos hmass hgen hgap)

end Singularity
