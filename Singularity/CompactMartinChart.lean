import Singularity.GeometricMartinCovariance
import Singularity.CocompactHyperbolic

/-!
# Martin convergence in any finite-image boundary chart

A group element moving a geometric boundary point into the finite real chart
transports the proved arbitrary-approach convergence back by the exact Martin
action. An infinite orbit of infinity supplies such a chart at infinity.
-/

noncomputable section
open Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- An infinite orbit of infinity supplies a group element with finite image
there. This is the only additional chart needed beyond the real line. -/
theorem exists_finite_image_infty (Γ : Subgroup SL(2, ℝ))
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) :
    ∃ (g : Γ) (ξ : ℝ), g • (∞ : OnePoint ℝ) = (ξ : OnePoint ℝ) := by
  obtain ⟨g, hg⟩ := exists_lowerLeft_ne_zero_of_infinite_orbit Γ horbit
  have hn : g • (∞ : OnePoint ℝ) ≠ ∞ := by
    intro h
    exact hg ((compactBoundary_fixes_infty_iff g).mp h)
  cases he : g • (∞ : OnePoint ℝ) with
  | infty => exact (hn he).elim
  | coe ξ => exact ⟨g, ξ, he⟩

/-- Each point of the compact boundary can be moved into the finite real chart. -/
theorem exists_finite_image_boundary (Γ : Subgroup SL(2, ℝ))
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) (p : OnePoint ℝ) :
    ∃ (g : Γ) (ξ : ℝ), g • p = (ξ : OnePoint ℝ) := by
  cases p with
  | infty => exact exists_finite_image_infty Γ horbit
  | coe ξ => exact ⟨1, ξ, one_smul _ _⟩

/-- A compact-boundary approach becomes ordinary complex convergence when a
chart moves its endpoint to a finite real coordinate. -/
theorem compact_orbit_approach_finite_image {α : Type*} {l : Filter α}
    (Γ : Subgroup SL(2, ℝ)) (p : OnePoint ℝ) (g : Γ) (ξ : ℝ)
    (hg : g • p = (ξ : OnePoint ℝ)) (y : α → Γ)
    (hy : Tendsto (fun n => hyperbolicCompactEmbedding (y n • UpperHalfPlane.I)) l
      (𝓝 (compactBoundaryEmbedding p))) :
    Tendsto (fun n => (((g * y n) • UpperHalfPlane.I : ℍ) : ℂ)) l (𝓝 (ξ : ℂ)) := by
  have ht := (continuous_const_smul (g : SL(2, ℝ))).continuousAt.tendsto.comp hy
  have he : (g : SL(2, ℝ)) • compactBoundaryEmbedding p = compactBoundaryEmbedding (ξ : OnePoint ℝ) := by
    rw [← compactBoundaryEmbedding_smul]
    exact congrArg compactBoundaryEmbedding hg
  rw [he] at ht
  have hh : Tendsto (fun n => hyperbolicCompactEmbedding ((g * y n) • UpperHalfPlane.I)) l
      (𝓝 ((ξ : ℂ) : OnePoint ℂ)) := by
    change Tendsto (fun n => (g : SL(2, ℝ)) • hyperbolicCompactEmbedding (y n • UpperHalfPlane.I)) l
      (𝓝 ((ξ : ℂ) : OnePoint ℂ)) at ht
    convert ht using 1
    funext n
    rw [mul_smul]
    exact hyperbolicCompactEmbedding_smul g (y n • UpperHalfPlane.I)
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff.mpr hh

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hmass in
/-- Arbitrary approaches to any point with a finite-image chart have a unique
Martin limit, given by transporting the established finite-chart point. -/
theorem compact_martin_tendsto_of_finite_image (p : OnePoint ℝ) (g : Γ) (ξ : ℝ)
    (hg : g • p = (ξ : OnePoint ℝ)) (y : ℕ → Γ)
    (hy : Tendsto (fun n => hyperbolicCompactEmbedding (y n • UpperHalfPlane.I)) atTop
      (𝓝 (compactBoundaryEmbedding p))) (x : Γ) :
    Tendsto (fun n => martinQuotient s μ 1 x (y n)) atTop
      (𝓝 ((martinBoundaryMap s μ hpos hgen hgap 1 g⁻¹
        (rayMartinPoint Γ s μ hpos hgen hgap ξ)).val x)) := by
  have hgy := compact_orbit_approach_finite_image Γ p g ξ hg y hy
  have hnum := real_boundary_martin_tendsto Γ s μ hpos hmass hgen hgap ξ
    (fun n => g * y n) hgy (g * x)
  have hden := real_boundary_martin_tendsto Γ s μ hpos hmass hgen hgap ξ
    (fun n => g * y n) hgy g
  have hp := (rayMartinCluster_harmonic Γ s μ hpos hgen hgap
    (rayMartinPoint_mem Γ s μ hpos hgen hgap ξ)).2.1 g
  have ht := hnum.div hden (ne_of_gt hp)
  change Tendsto (fun n => martinQuotient s μ 1 (g * x) (g * y n) /
    martinQuotient s μ 1 g (g * y n)) atTop _ at ht
  have he (n : ℕ) : martinQuotient s μ 1 (g * x) (g * y n) /
      martinQuotient s μ 1 g (g * y n) = martinQuotient s μ 1 x (y n) := by
    have hh := congrFun (martinTranslate_embedding s μ hpos hgen hgap 1 g⁻¹ (g * y n)) x
    simpa only [martinTranslate, martinEmbedding, inv_inv, mul_one, inv_mul_cancel_left] using hh
  simpa only [he, martinBoundaryMap, martinTranslate, inv_inv, mul_one] using ht

end Singularity
