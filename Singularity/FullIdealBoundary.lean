import Singularity.FuchsianLimitSet
import Singularity.BoundaryCircle
import Singularity.CayleyExcess
import Mathlib.Topology.Sequences

/-!
# Sets accumulating on the entire ideal boundary

This condition is formulated directly in the compact sphere. It is invariant
under ambient hyperbolic isometries. Opposite boundary approaches give a
uniformly bounded triangle excess at the basepoint i.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- Every ideal point lies in the compactified closure of the given set. -/
def HasFullIdealBoundary (S : Set ℍ) : Prop :=
  ∀ p : OnePoint ℝ, compactBoundaryEmbedding p ∈ closure (hyperbolicCompactEmbedding '' S)

/-- Every ideal point is approached by a sequence of points in the set. -/
theorem HasFullIdealBoundary.exists_sequence {S : Set ℍ} (hS : HasFullIdealBoundary S)
    (p : OnePoint ℝ) :
    ∃ x : ℕ → ℍ, (∀ n, x n ∈ S) ∧
      Tendsto (fun n => hyperbolicCompactEmbedding (x n)) atTop (𝓝 (compactBoundaryEmbedding p)) := by
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp (hS p)
  choose x hx he using hy
  exact ⟨x, hx, by simpa only [he] using hlim⟩

/-- Full ideal boundary is preserved by an ambient isometry. -/
theorem HasFullIdealBoundary.smul_image {S : Set ℍ} (hS : HasFullIdealBoundary S) (B : SL(2, ℝ)) :
    HasFullIdealBoundary ((fun z : ℍ => B • z) '' S) := by
  intro p
  obtain ⟨x, hx, hlim⟩ := hS.exists_sequence (B⁻¹ • p)
  have ht := (continuous_const_smul B).continuousAt.tendsto.comp hlim
  have he : B • compactBoundaryEmbedding (B⁻¹ • p) = compactBoundaryEmbedding p := by
    rw [← compactBoundaryEmbedding_smul, smul_inv_smul]
  rw [he] at ht
  have hlim' : Tendsto (fun n => hyperbolicCompactEmbedding (B • x n)) atTop
      (𝓝 (compactBoundaryEmbedding p)) := by
    simpa only [hyperbolicCompactEmbedding_smul, Function.comp_def] using ht
  apply isClosed_closure.mem_of_tendsto hlim'
  exact Eventually.of_forall fun n => subset_closure ⟨B • x n, ⟨x n, hx n, rfl⟩, rfl⟩

/-- Compact-sphere convergence to the ideal boundary gives convergence of disk coordinates. -/
theorem compact_tendsto_cayley {α : Type*} {l : Filter α} {x : α → ℍ} {p : OnePoint ℝ}
    (h : Tendsto (fun n => hyperbolicCompactEmbedding (x n)) l (𝓝 (compactBoundaryEmbedding p))) :
    Tendsto (fun n => halfPlaneCayley (x n)) l (𝓝 (boundaryCircle p)) := by
  have ht := (cayleyCompactHomeomorph.continuous.tendsto (compactBoundaryEmbedding p)).comp h
  have he (z : ℍ) : cayleyCompactHomeomorph (hyperbolicCompactEmbedding z) =
      (halfPlaneCayley z : OnePoint ℂ) := cayleyMatrix_smul_embedding z
  have ht' : Tendsto (fun n => (halfPlaneCayley (x n) : OnePoint ℂ)) l
      (𝓝 (boundaryCircle p : OnePoint ℂ)) := by
    simpa only [Function.comp_def, he, ← boundaryCircle_compact] using ht
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff.mpr ht'

/-- Full boundary accumulation supplies points with a uniformly small triangle
excess at i; the constant is independent of the set. -/
theorem HasFullIdealBoundary.exists_bounded_excess {S : Set ℍ} (hS : HasFullIdealBoundary S) :
    ∃ x ∈ S, ∃ y ∈ S,
      dist x UpperHalfPlane.I + dist y UpperHalfPlane.I - dist x y ≤ 2 * Real.log 4 := by
  obtain ⟨x, hx, hxl⟩ := hS.exists_sequence (0 : ℝ)
  obtain ⟨y, hy, hyl⟩ := hS.exists_sequence ∞
  have he : dist (boundaryCircle (0 : ℝ)) (boundaryCircle ∞) = 2 := by
    simp only [boundaryCircle_coe, boundaryCircle_infty, Complex.ofReal_zero, zero_sub,
      zero_add, neg_div, div_self Complex.I_ne_zero, dist_eq_norm]
    norm_num [show (-1 : ℂ) - 1 = (-2 : ℝ) by norm_num, Complex.norm_real]
  have ht : Tendsto (fun n => dist (halfPlaneCayley (x n)) (halfPlaneCayley (y n))) atTop (𝓝 2) := by
    simpa only [he] using (compact_tendsto_cayley hxl).dist (compact_tendsto_cayley hyl)
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 2))).exists
  refine ⟨x n, hx n, y n, hy n, ?_⟩
  simpa only [div_one] using hyperbolic_excess_of_cayley_separation (x n) (y n) 1 zero_lt_one hn.le

/-- The full-limit-set condition for a projective orbit agrees with the geometric definition. -/
theorem full_projectiveOrbitLimitSet_iff (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    projectiveOrbitLimitSet Γ z = Set.univ ↔ HasFullIdealBoundary (MulAction.orbit Γ z) := by
  have he : hyperbolicCompactEmbedding '' MulAction.orbit Γ z =
      Set.range (fun g : Γ => hyperbolicCompactEmbedding (g • z)) := by
    ext q
    constructor
    · rintro ⟨w, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g • z, ⟨g, rfl⟩, rfl⟩
  simp only [HasFullIdealBoundary, he, Set.eq_univ_iff_forall, projectiveOrbitLimitSet, Set.mem_preimage]

end Singularity
