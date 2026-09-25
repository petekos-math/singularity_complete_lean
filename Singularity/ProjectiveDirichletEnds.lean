import Singularity.ProjectiveDirichletCell
import Singularity.DirichletHeightBound
import Singularity.BoundedHeightEndpoints

/-!
# A noncompact quotient supplies a bounded-height ideal endpoint

A noncompact quotient forces the closed Dirichlet cell to be unbounded.
Compactifying a sequence going to infinite distance gives an ideal endpoint.
The defining distance comparisons then exclude every orbit point above the
centre in a chart based at that endpoint. No finite-sidedness, finite
generation, or classification of surface ends is required for this step.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- A noncompact quotient produces an ideal limit of points in its cell. -/
theorem exists_ideal_dirichlet_sequence_of_noncompact
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ)
    (hnc : ¬CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))) :
    ∃ p : OnePoint ℝ, ∃ w : ℕ → ℍ,
      (∀ n, w n ∈ projectiveDirichletCell Γ z) ∧
      Tendsto (fun n => hyperbolicCompactEmbedding (w n)) atTop
        (𝓝 (compactBoundaryEmbedding p)) := by
  have hu : ∀ n : ℕ, ∃ w ∈ projectiveDirichletCell Γ z, (n : ℝ) < dist w z := by
    intro n
    by_contra! h
    exact hnc (projective_cocompact_of_bounded_dirichletCell Γ z n h)
  choose w hw hd using hu
  obtain ⟨p, _, φ, hφ, ht⟩ := (isCompact_univ (X := OnePoint ℂ)).tendsto_subseq
    (fun n => mem_univ (hyperbolicCompactEmbedding (w n)))
  have hm : ∀ n, w (φ n) ∈ projectiveDirichletCell Γ z := fun n => hw (φ n)
  cases p with
  | infty => exact ⟨∞, w ∘ φ, hm, ht⟩
  | coe u =>
    have hc : Tendsto (fun n => (w (φ n) : ℂ)) atTop (𝓝 u) :=
      OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff.mpr ht
    have hn : 0 ≤ u.im := ge_of_tendsto (Complex.continuous_im.tendsto u |>.comp hc)
      (Eventually.of_forall (fun n => (w (φ n)).im_pos.le))
    by_cases hi : u.im = 0
    · refine ⟨(u.re : OnePoint ℝ), w ∘ φ, hm, ?_⟩
      have he : (u.re : ℂ) = u := by apply Complex.ext <;> simp [hi]
      change Tendsto (fun n => hyperbolicCompactEmbedding (w (φ n))) atTop
        (𝓝 ((u.re : ℂ) : OnePoint ℂ))
      rwa [he]
    · let v : ℍ := ⟨u, lt_of_le_of_ne hn (Ne.symm hi)⟩
      have hv : Tendsto (fun n => w (φ n)) atTop (𝓝 v) :=
        UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff.mpr hc
      have hdist : Tendsto (fun n => dist (w (φ n)) z) atTop atTop := by
        apply tendsto_atTop_mono (fun n => (hd (φ n)).le)
        exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
      exact (not_tendsto_nhds_of_tendsto_atTop hdist _ (hv.dist tendsto_const_nhds)).elim

/-- An ideal limit of cell points supplies a uniform orbit-height bound
in every chart at that endpoint. -/
theorem projectiveDirichlet_endpoint_height_bound
    (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (p : OnePoint ℝ) (w : ℕ → ℍ)
    (hw : ∀ n, w n ∈ projectiveDirichletCell Γ z)
    (ht : Tendsto (fun n => hyperbolicCompactEmbedding (w n)) atTop
      (𝓝 (compactBoundaryEmbedding p))) :
    p ∈ projectiveBoundedHeightEndpoints Γ z := by
  intro B hB
  refine ⟨(B⁻¹ • z).im, (B⁻¹ • z).im_pos, fun g => ?_⟩
  let S := (fun v : ℍ => B⁻¹ • v) '' projectiveDirichletCell Γ z
  apply im_le_of_infty_mem_closure_dist_le S (B⁻¹ • z) (B⁻¹ • (g • z))
  · have ht' := (continuous_const_smul B⁻¹ : Continuous (fun q : OnePoint ℂ => B⁻¹ • q)).tendsto
      (compactBoundaryEmbedding p) |>.comp ht
    have he : B⁻¹ • compactBoundaryEmbedding p = (∞ : OnePoint ℂ) := by
      rw [← hB, compactBoundaryEmbedding_smul, inv_smul_smul]
      rfl
    have hlim : Tendsto (fun n => hyperbolicCompactEmbedding (B⁻¹ • w n)) atTop
        (𝓝 (∞ : OnePoint ℂ)) := by
      simpa only [Function.comp_def, hyperbolicCompactEmbedding_smul, he] using ht'
    apply isClosed_closure.mem_of_tendsto hlim
    exact Eventually.of_forall (fun n => subset_closure
      ⟨B⁻¹ • w n, ⟨w n, hw n, rfl⟩, rfl⟩)
  · rintro _ ⟨v, hv, rfl⟩
    simpa only [dist_smul] using hv g

/-- Every noncompact discrete projective quotient has a bounded-height
ideal endpoint, irrespective of its parabolic elements or limit set. -/
theorem projectiveBoundedHeightEndpoints_nonempty_of_noncompact
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ)
    (hnc : ¬CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))) :
    (projectiveBoundedHeightEndpoints Γ z).Nonempty := by
  obtain ⟨p, w, hw, ht⟩ := exists_ideal_dirichlet_sequence_of_noncompact Γ z hnc
  exact ⟨p, projectiveDirichlet_endpoint_height_bound Γ z p w hw ht⟩

end Singularity
