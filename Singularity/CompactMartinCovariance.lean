import Singularity.GeometricMartinHomeomorph

/-!
# Equivariance of the complete geometric Martin identification

The homeomorphism respects the genuine group action at every boundary point,
including poles and infinity. The resulting positive kernel has normalized
covariance on the entire compact boundary.
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
/-- The compact geometric Martin map intertwines the actual group actions
without any excluded endpoints. -/
theorem compactMartinPoint_smul (g : Γ) (p : OnePoint ℝ) :
    compactMartinPoint Γ s μ hpos hgen hgap horbit (g • p) =
      martinBoundaryMap s μ hpos hgen hgap 1 g
        (compactMartinPoint Γ s μ hpos hgen hgap horbit p) := by
  obtain ⟨y, hy⟩ := exists_compact_boundary_orbit_approach Γ horbit p
  have hgy : Tendsto (fun n => hyperbolicCompactEmbedding ((g * y n) • UpperHalfPlane.I)) atTop
      (𝓝 (compactBoundaryEmbedding (g • p))) := by
    have hh := (continuous_const_smul (g : SL(2, ℝ))).continuousAt.tendsto.comp hy
    rw [← compactBoundaryEmbedding_smul] at hh
    convert hh using 1
    · funext n
      rw [mul_smul]
      exact hyperbolicCompactEmbedding_smul g _
    · rfl
  apply Subtype.ext
  funext x
  have hlim := compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit (g • p)
    (fun n => g * y n) hgy x
  have hp := martinClosure_pos s μ hpos hgen hgap 1
    (compactMartinPoint Γ s μ hpos hgen hgap horbit p).property.1 (g⁻¹ * 1)
  have ht := (compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit p y hy (g⁻¹ * x)).div
    (compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit p y hy (g⁻¹ * 1)) (ne_of_gt hp)
  change Tendsto (fun n => martinQuotient s μ 1 (g⁻¹ * x) (y n) /
    martinQuotient s μ 1 (g⁻¹ * 1) (y n)) atTop _ at ht
  have he (n : ℕ) : martinQuotient s μ 1 (g⁻¹ * x) (y n) /
      martinQuotient s μ 1 (g⁻¹ * 1) (y n) = martinQuotient s μ 1 x (g * y n) :=
    congrFun (martinTranslate_embedding s μ hpos hgen hgap 1 g (y n)) x
  simp only [he] at ht
  exact tendsto_nhds_unique hlim ht

include hmass in
/-- The actual geometric Martin kernel obeys normalized covariance on the
entire compact boundary, with its denominator known to be strictly positive. -/
theorem compactMartinPoint_kernel_covariance (g x : Γ) (p : OnePoint ℝ) :
    (compactMartinPoint Γ s μ hpos hgen hgap horbit (g • p)).val x =
      (compactMartinPoint Γ s μ hpos hgen hgap horbit p).val (g⁻¹ * x) /
        (compactMartinPoint Γ s μ hpos hgen hgap horbit p).val g⁻¹ := by
  rw [compactMartinPoint_smul Γ s μ hpos hmass hgen hgap horbit g p]
  simp only [martinBoundaryMap, martinTranslate, mul_one]

end Singularity
