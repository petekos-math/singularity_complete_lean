import Singularity.EndpointImageBounds
import Singularity.ParabolicFixedPointCharts
import Singularity.LimitSetDynamics

/-!
# Ideal limits lie in every nontrivial closed invariant boundary set

The endpoint estimate rules out an ideal limit outside a closed set that
contains the images of two distinct boundary points. Consequently the ideal
orbit limit set lies in the closure of every infinite boundary orbit. No
cocompactness, finite generation, or measure-class hypothesis is used.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- If both endpoint images stay in a closed boundary set, every ideal
limit of the interior images belongs to that same set. -/
theorem slTwo_boundary_limit_mem_closed_of_endpoint_images
    (K : Set (OnePoint ℝ)) (hK : IsClosed K) (g : ℕ → SL(2, ℝ)) (z : ℍ)
    (hinfty : ∀ n, g n • (∞ : OnePoint ℝ) ∈ K)
    (hzero : ∀ n, g n • ((0 : ℝ) : OnePoint ℝ) ∈ K)
    (ξ : OnePoint ℝ)
    (ht : Tendsto (fun n => hyperbolicCompactEmbedding (g n • z)) atTop
      (𝓝 (compactBoundaryEmbedding ξ))) : ξ ∈ K := by
  by_contra hnot
  obtain ⟨B, hB⟩ : ∃ B : SL(2, ℝ), B • ξ = (∞ : OnePoint ℝ) := by
    cases ξ with
    | infty => exact ⟨1, one_smul _ _⟩
    | coe r =>
      refine ⟨boundaryPoleMatrix r, ?_⟩
      apply compactBoundary_smul_pole
      simp [boundaryPoleMatrix]
  let K' : Set (OnePoint ℝ) := (fun η : OnePoint ℝ => B⁻¹ • η) ⁻¹' K
  have hK' : IsClosed K' := hK.preimage (continuous_const_smul B⁻¹)
  have hnot' : (∞ : OnePoint ℝ) ∉ K' := by
    change B⁻¹ • (∞ : OnePoint ℝ) ∉ K
    simpa only [← hB, inv_smul_smul] using hnot
  have hc := ((OnePoint.isClosed_iff_of_notMem hnot').mp hK').2
  obtain ⟨M, hM, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hend (η : OnePoint ℝ) (hη : η ∈ K') :
      ∃ r : ℝ, |r| ≤ M ∧ η = (r : OnePoint ℝ) := by
    cases η with
    | infty => exact (hnot' hη).elim
    | coe r => exact ⟨r, by simpa only [Real.norm_eq_abs] using hbound r hη, rfl⟩
  let C := M * (1 + 2 * ‖(z : ℂ)‖ / z.im)
  have hn (n : ℕ) : ‖(((B * g n) • z : ℍ) : ℂ)‖ ≤ C := by
    apply slTwo_interior_norm_bound_of_endpoint_images _ z hM.le
    · apply hend
      change B⁻¹ • ((B * g n) • (∞ : OnePoint ℝ)) ∈ K
      simpa only [mul_smul, inv_smul_smul] using hinfty n
    · apply hend
      change B⁻¹ • ((B * g n) • ((0 : ℝ) : OnePoint ℝ)) ∈ K
      simpa only [mul_smul, inv_smul_smul] using hzero n
  have hlim := (continuous_const_smul B : Continuous (fun w : OnePoint ℂ => B • w)).tendsto
    (compactBoundaryEmbedding ξ) |>.comp ht
  have he : B • compactBoundaryEmbedding ξ = (∞ : OnePoint ℂ) := by
    rw [← compactBoundaryEmbedding_smul, hB]
    rfl
  have ht' : Tendsto (fun n => hyperbolicCompactEmbedding ((B * g n) • z)) atTop
      (𝓝 (∞ : OnePoint ℂ)) := by
    simpa only [Function.comp_def, mul_smul, hyperbolicCompactEmbedding_smul, he] using hlim
  have hclosed : IsClosed (((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall 0 C) :=
    OnePoint.isClosed_image_coe.mpr ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩
  have hmem : (∞ : OnePoint ℂ) ∈ ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall 0 C := by
    apply hclosed.mem_of_tendsto ht'
    apply Eventually.of_forall
    intro n
    exact ⟨(((B * g n) • z : ℍ) : ℂ), by simpa only [Metric.mem_closedBall, dist_zero_right] using hn n, rfl⟩
  exact OnePoint.infty_notMem_image_coe hmem

/-- Every nontrivial closed invariant boundary set contains the actual ideal
orbit limit set, even without discreteness. -/
theorem projectiveOrbitLimitSet_subset_closed_invariant
    (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (K : Set (OnePoint ℝ))
    (hK : IsClosed K) (hpq : K.Nontrivial)
    (hinv : ∀ g : Γ, ∀ p ∈ K, g • p ∈ K) : projectiveOrbitLimitSet Γ z ⊆ K := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hpq
  obtain ⟨B, hB⟩ := exists_smul_baseBoundaryPair ⟨(p, q), hpq⟩
  have he := congrArg Subtype.val hB
  change (B • (∞ : OnePoint ℝ), B • ((0 : ℝ) : OnePoint ℝ)) = (p, q) at he
  have hBp := congrArg Prod.fst he
  have hBq := congrArg Prod.snd he
  change B • (∞ : OnePoint ℝ) = p at hBp
  change B • ((0 : ℝ) : OnePoint ℝ) = q at hBq
  intro ξ hξ
  obtain ⟨x, hx⟩ := (mem_projectiveOrbitLimitSet_iff_sequence Γ z ξ).mp hξ
  choose a ha using fun n => slTwoProjective_surjective (x n : PSL(2, ℝ))
  have hgeo (n : ℕ) (w : ℍ) : a n • w = x n • w := by
    rw [← slTwoProjective_smul_hyperbolic, ha n]
    rfl
  have hbd (n : ℕ) (r : OnePoint ℝ) : a n • r = x n • r := by
    rw [← slTwoProjective_smul_boundary, ha n]
    rfl
  apply slTwo_boundary_limit_mem_closed_of_endpoint_images K hK
    (fun n => a n * B) (B⁻¹ • z) _ _ ξ
  · simpa only [mul_smul, smul_inv_smul, hgeo] using hx
  · intro n
    simpa only [mul_smul, hBp, hbd] using hinv (x n) p hp
  · intro n
    simpa only [mul_smul, hBq, hbd] using hinv (x n) q hq

/-- For a nonelementary projective group, every boundary orbit accumulates
on the entire ideal orbit limit set. -/
theorem projectiveOrbitLimitSet_subset_closure_boundary_orbit
    (Γ : Subgroup PSL(2, ℝ)) (hne : ProjectiveNonelementary Γ)
    (z : ℍ) (p : OnePoint ℝ) :
    projectiveOrbitLimitSet Γ z ⊆ closure (MulAction.orbit Γ p) := by
  apply projectiveOrbitLimitSet_subset_closed_invariant Γ z _ isClosed_closure
  · exact (hne.infinite_boundary_orbits Γ p).nontrivial.mono subset_closure
  · intro g q hq
    exact smul_closure_orbit_subset g p ⟨q, hq, rfl⟩

end Singularity
