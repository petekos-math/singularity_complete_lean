import Singularity.RayMartinBounds
import Singularity.NaimAnconaBounds
import Singularity.CayleyRealBoundary

/-!
# Distinct ray endpoints have disjoint sets of Martin subsequential limits

A Martin limit from one ray tends to zero along every different ray, while
its values on its own ray grow at reciprocal-Green scale. Consequently two
different real boundary endpoints cannot give the same limit function. This
separates geometric endpoints but does not prove uniqueness at one endpoint.
-/

noncomputable section
open Filter
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Distinct limits give uniform separation of all sufficiently late cross pairs. -/
theorem cayley_separated_tails (x y : ℕ → ℍ) (a b : ℂ) (hab : a ≠ b)
    (hx : Tendsto (fun n => halfPlaneCayley (x n)) atTop (𝓝 a))
    (hy : Tendsto (fun n => halfPlaneCayley (y n)) atTop (𝓝 b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      δ ≤ dist (halfPlaneCayley (x m)) (halfPlaneCayley (y n)) := by
  have hd : 0 < dist a b := dist_pos.mpr hab
  have hδ : 0 < dist a b / 3 := by positivity
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hx.eventually (Metric.ball_mem_nhds a hδ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hy.eventually (Metric.ball_mem_nhds b hδ))
  refine ⟨dist a b / 3, hδ, max M N, ?_⟩
  intro m hm n hn
  have hx' := hM m ((le_max_left _ _).trans hm)
  have hy' := hN n ((le_max_right _ _).trans hn)
  change dist (halfPlaneCayley (x m)) a < dist a b / 3 at hx'
  change dist (halfPlaneCayley (y n)) b < dist a b / 3 at hy'
  have hh := dist_triangle4 a (halfPlaneCayley (x m)) (halfPlaneCayley (y n)) b
  rw [dist_comm a (halfPlaneCayley (x m))] at hh
  linarith

/-- A subsequential Martin limit from η vanishes along the orbit ray to ξ≠η. -/
theorem cocompact_cross_ray_martin_limit_zero (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (ξ η : ℝ) (hξη : ξ ≠ η) (H : Γ → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : ∀ z, Tendsto (fun n => martinQuotient s μ 1 z (cocompactRaySequence Γ η (φ n))) atTop (𝓝 (H z))) :
    Tendsto (fun m => H (cocompactRaySequence Γ ξ m)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, N, hsep⟩ := cayley_separated_tails
    (fun n => cocompactRaySequence Γ ξ n • UpperHalfPlane.I)
    (fun n => cocompactRaySequence Γ η n • UpperHalfPlane.I)
    (realBoundaryCayley ξ) (realBoundaryCayley η)
    (fun h => hξη (realBoundaryCayley_injective h))
    (halfPlaneCayley_tendsto_real _ ξ (cocompactRaySequence_tendsto Γ ξ))
    (halfPlaneCayley_tendsto_real _ η (cocompactRaySequence_tendsto Γ η))
  obtain ⟨C, hC, hb⟩ := cocompact_disk_separated_green_product_bound Γ s μ hpos hmass hgen hgap δ hδ
  have hbound : ∀ m ≥ N, H (cocompactRaySequence Γ ξ m) ≤
      C * walkGreen s μ (cocompactRaySequence Γ ξ m) 1 := by
    intro m hm
    apply le_of_tendsto (hlim (cocompactRaySequence Γ ξ m))
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
    unfold martinQuotient
    apply (div_le_iff₀ (walkGreen_pos s μ hpos hgen hgap 1 _)).mpr
    simpa only [mul_assoc] using hb (cocompactRaySequence Γ ξ m) (cocompactRaySequence Γ η (φ n))
      (hsep m hm (φ n) hn)
  have hpositive (z : Γ) : 0 < H z := martin_limit_pos s μ hpos hgen hgap 1
    (fun n => cocompactRaySequence Γ η (φ n)) H hlim z
  have hescape : Tendsto (cocompactRaySequence Γ ξ) atTop cofinite :=
    le_cofinite_iff_eventually_ne.mpr (cocompactRaySequence_eventually_ne Γ ξ)
  have hzero := (walkGreen_column_tendsto_zero s μ (fun g hg => (hpos g hg).le) hgap 1).comp hescape
  have hCzero : Tendsto (fun m => C * walkGreen s μ (cocompactRaySequence Γ ξ m) 1) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using hzero.const_mul C
  exact squeeze_zero' (Eventually.of_forall (fun m => (hpositive _).le))
    ((eventually_ge_atTop N).mono (fun m hm => hbound m hm)) hCzero

/-- Subsequential limits associated with distinct real endpoints are distinct. -/
theorem cocompact_distinct_ray_martin_limits (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (ξ η : ℝ) (hξη : ξ ≠ η) (Hξ Hη : Γ → ℝ) (φ ψ : ℕ → ℕ)
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hξ : ∀ z, Tendsto (fun n => martinQuotient s μ 1 z (cocompactRaySequence Γ ξ (φ n))) atTop (𝓝 (Hξ z)))
    (hη : ∀ z, Tendsto (fun n => martinQuotient s μ 1 z (cocompactRaySequence Γ η (ψ n))) atTop (𝓝 (Hη z))) :
    Hξ ≠ Hη := by
  intro heq
  have hz := cocompact_cross_ray_martin_limit_zero Γ s μ hpos hmass hgen hgap ξ η hξη Hη ψ hψ hη
  rw [← heq] at hz
  have hG := walkGreen_row_escape_tendsto_zero s μ (fun g hg => (hpos g hg).le) hgap 1
    (cocompactRaySequence Γ ξ) (cocompactRaySequence_eventually_ne Γ ξ)
  obtain ⟨C, hC, hb⟩ := cocompact_ray_martin_limit_bounds Γ s μ hpos hmass hgen hgap
  have hh := ge_of_tendsto (hG.mul hz) (Eventually.of_forall (fun m => (hb ξ Hξ φ hφ hξ m).1))
  have hposC : 0 < 1/C := by positivity
  norm_num at hh
  linarith

end Singularity
