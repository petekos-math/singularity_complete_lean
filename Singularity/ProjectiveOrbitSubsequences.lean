import Singularity.ProjectiveSubgroupLift
import Singularity.CompactBoundaryEscape

/-!
# Subsequences of projective group orbits

Every sequence in a discrete projective subgroup has a subsequence which
either eventually stays in a finite set of group vertices or has an ideal
orbit limit. This uses compactness of the sphere and properness of the
interior orbit action, and requires no cocompactness.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- A compact interior set contains only finitely many vertices of a
discrete projective-group orbit, counting the stabilizer multiplicities. -/
theorem finite_projective_group_vertices_in_compact
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ)
    {K : Set ℍ} (hK : IsCompact K) : {g : Γ | g • z ∈ K}.Finite := by
  let Λ := projectiveSubgroupLift Γ
  let : DiscreteTopology Λ := projectiveSubgroupLift_discrete Γ
  have hf := finite_group_vertices_in_compact Λ z hK
  apply (hf.image (projectiveLiftProjection Γ)).subset
  intro g hg
  obtain ⟨a, ha⟩ := projectiveLiftProjection_surjective Γ g
  refine ⟨a, ?_, ha⟩
  change a • z ∈ K
  rw [← projectiveLiftProjection_smul_hyperbolic, ha]
  exact hg

/-- A group sequence admits either a finite-valued tail or an ideal orbit
limit after extraction of a strictly increasing subsequence. -/
theorem projective_orbit_subsequence_finite_or_boundary
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (g : ℕ → Γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ K : Finset Γ, ∀ᶠ n in atTop, g (φ n) ∈ K) ∨
        ∃ ξ : OnePoint ℝ,
          Tendsto (fun n => hyperbolicCompactEmbedding (g (φ n) • z)) atTop
            (𝓝 (compactBoundaryEmbedding ξ))) := by
  obtain ⟨p, _, φ, hφ, ht⟩ := (isCompact_univ (X := OnePoint ℂ)).tendsto_subseq
    (fun n => mem_univ (hyperbolicCompactEmbedding (g n • z)))
  refine ⟨φ, hφ, ?_⟩
  cases p with
  | infty => exact Or.inr ⟨∞, ht⟩
  | coe w =>
    have hc : Tendsto (fun n => ((g (φ n) • z : ℍ) : ℂ)) atTop (𝓝 w) :=
      OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff.mpr ht
    have hn : 0 ≤ w.im := ge_of_tendsto (Complex.continuous_im.tendsto w |>.comp hc)
      (Eventually.of_forall (fun n => (g (φ n) • z).im_pos.le))
    by_cases hw : w.im = 0
    · right
      refine ⟨(w.re : OnePoint ℝ), ?_⟩
      have he : (w.re : ℂ) = w := by apply Complex.ext <;> simp [hw]
      change Tendsto (fun n => hyperbolicCompactEmbedding (g (φ n) • z)) atTop
        (𝓝 ((w.re : ℂ) : OnePoint ℂ))
      rw [he]
      exact ht
    · left
      let u : ℍ := ⟨w, lt_of_le_of_ne hn (Ne.symm hw)⟩
      have hu : Tendsto (fun n => g (φ n) • z) atTop (𝓝 u) :=
        UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff.mpr hc
      have hK := finite_projective_group_vertices_in_compact Γ z (isCompact_closedBall u 1)
      refine ⟨hK.toFinset, ?_⟩
      filter_upwards [hu.eventually (Metric.closedBall_mem_nhds u zero_lt_one)] with n hn
      exact hK.mem_toFinset.mpr hn

end Singularity
