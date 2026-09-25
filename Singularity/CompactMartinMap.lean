import Singularity.CompactMartinChart

/-!
# A Martin point at every compact geometric boundary point

A finite-image chart defines the point, including at infinity. The resulting
pointwise limit is proved for every approach. Constructed orbit approximations
show independence from the chart and identify the finite-chart restriction.
-/

noncomputable section
open Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Every compact boundary point has an actual orbit approach, obtained by
transporting a chosen finite-endpoint ray. -/
theorem exists_compact_boundary_orbit_approach (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) (p : OnePoint ℝ) :
    ∃ y : ℕ → Γ, Tendsto (fun n => hyperbolicCompactEmbedding (y n • UpperHalfPlane.I)) atTop
      (𝓝 (compactBoundaryEmbedding p)) := by
  obtain ⟨g, ξ, hg⟩ := exists_finite_image_boundary Γ horbit p
  refine ⟨fun n => g⁻¹ * cocompactRaySequence Γ ξ n, ?_⟩
  have ht := OnePoint.continuous_coe.continuousAt.tendsto.comp (cocompactRaySequence_tendsto Γ ξ)
  have hs := (continuous_const_smul ((g⁻¹ : Γ) : SL(2, ℝ))).continuousAt.tendsto.comp ht
  have he : ((g⁻¹ : Γ) : SL(2, ℝ)) • compactBoundaryEmbedding (ξ : OnePoint ℝ) =
      compactBoundaryEmbedding p := by
    rw [← compactBoundaryEmbedding_smul]
    have hh : g⁻¹ • (ξ : OnePoint ℝ) = p := by rw [← hg, inv_smul_smul]
    exact congrArg compactBoundaryEmbedding hh
  change Tendsto (fun n => ((g⁻¹ : Γ) : SL(2, ℝ)) •
    hyperbolicCompactEmbedding (cocompactRaySequence Γ ξ n • UpperHalfPlane.I)) atTop
    (𝓝 (((g⁻¹ : Γ) : SL(2, ℝ)) • compactBoundaryEmbedding (ξ : OnePoint ℝ))) at hs
  rw [he] at hs
  convert hs using 1
  funext n
  rw [mul_smul]
  exact hyperbolicCompactEmbedding_smul g⁻¹ _

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

/-- The geometric Martin point on the entire compact real boundary. -/
def compactMartinPoint (p : OnePoint ℝ) : martinBoundary s μ 1 :=
  let h := exists_finite_image_boundary Γ horbit p
  martinBoundaryMap s μ hpos hgen hgap 1 h.choose⁻¹
    (rayMartinPoint Γ s μ hpos hgen hgap h.choose_spec.choose)

include hmass in
/-- Full pointwise Martin convergence for arbitrary approaches to every compact
boundary point, including infinity. -/
theorem compactMartinPoint_tendsto (p : OnePoint ℝ) (y : ℕ → Γ)
    (hy : Tendsto (fun n => hyperbolicCompactEmbedding (y n • UpperHalfPlane.I)) atTop
      (𝓝 (compactBoundaryEmbedding p))) (x : Γ) :
    Tendsto (fun n => martinQuotient s μ 1 x (y n)) atTop
      (𝓝 ((compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x)) := by
  let h := exists_finite_image_boundary Γ horbit p
  exact compact_martin_tendsto_of_finite_image Γ s μ hpos hmass hgen hgap p
    h.choose h.choose_spec.choose h.choose_spec.choose_spec y hy x

include hmass in
/-- The compact map agrees with the already constructed map on the real chart. -/
theorem compactMartinPoint_coe (ξ : ℝ) :
    compactMartinPoint Γ s μ hpos hgen hgap horbit (ξ : OnePoint ℝ) =
      rayMartinPoint Γ s μ hpos hgen hgap ξ := by
  apply Subtype.ext
  funext x
  have ht := compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit (ξ : OnePoint ℝ)
    (cocompactRaySequence Γ ξ)
    (OnePoint.continuous_coe.continuousAt.tendsto.comp (cocompactRaySequence_tendsto Γ ξ)) x
  exact tendsto_nhds_unique ht (rayMartinPoint_tendsto Γ s μ hpos hmass hgen hgap ξ x)

include hmass in
/-- Every valid finite-image chart gives the same actual Martin boundary point. -/
theorem compactMartinPoint_chart (p : OnePoint ℝ) (g : Γ) (ξ : ℝ)
    (hg : g • p = (ξ : OnePoint ℝ)) :
    compactMartinPoint Γ s μ hpos hgen hgap horbit p =
      martinBoundaryMap s μ hpos hgen hgap 1 g⁻¹ (rayMartinPoint Γ s μ hpos hgen hgap ξ) := by
  obtain ⟨y, hy⟩ := exists_compact_boundary_orbit_approach Γ horbit p
  apply Subtype.ext
  funext x
  exact tendsto_nhds_unique (compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit p y hy x)
    (compact_martin_tendsto_of_finite_image Γ s μ hpos hmass hgen hgap p g ξ hg y hy x)

end Singularity
