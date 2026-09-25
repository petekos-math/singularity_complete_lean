import Singularity.RayMartinUniqueness

/-!
# Full convergence along the chosen cocompact orbit rays

Sequential compactness and uniqueness upgrade the existing subsequential
limits to full pointwise convergence. The resulting ray map is injective into
the actual Martin boundary. Continuity and convergence along arbitrary
geometric approaches are separate obligations.
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

include hpos hmass hgen hgap in
/-- Every ray cluster function is the limit of the entire sequence of Martin
quotients, not merely of one selected subsequence. -/
theorem rayMartinCluster_tendsto {ξ : ℝ} {H : Γ → ℝ}
    (hH : H ∈ rayMartinCluster Γ s μ ξ) (x : Γ) :
    Tendsto (fun n => martinQuotient s μ 1 x (cocompactRaySequence Γ ξ n)) atTop (𝓝 (H x)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, _, hφ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨J, _, _, ψ, hψ, hlim⟩ := martinQuotient_subsequence s μ hpos hgen hgap 1
    (fun n => cocompactRaySequence Γ ξ (ns (φ n)))
  have hJ : J ∈ rayMartinCluster Γ s μ ξ := ⟨ns ∘ φ ∘ ψ, hφ.comp hψ, hlim⟩
  have hEq := rayMartinCluster_subsingleton Γ s μ hpos hmass hgen hgap ξ hJ hH
  subst J
  exact ⟨φ ∘ ψ, hlim x⟩

/-- The actual Martin boundary point obtained as the unique limit of a chosen
cocompact orbit ray. The definition uses the proved nonempty cluster set. -/
def rayMartinPoint (ξ : ℝ) : martinBoundary s μ 1 :=
  ⟨(rayMartinCluster_nonempty Γ s μ hpos hgen hgap ξ).choose,
    rayMartinCluster_subset_boundary Γ s μ hpos hgen hgap ξ
      (rayMartinCluster_nonempty Γ s μ hpos hgen hgap ξ).choose_spec⟩

omit [DiscreteTopology Γ] in
/-- The selected boundary point is an actual ray cluster function. -/
theorem rayMartinPoint_mem (ξ : ℝ) :
    (rayMartinPoint Γ s μ hpos hgen hgap ξ).val ∈ rayMartinCluster Γ s μ ξ :=
  (rayMartinCluster_nonempty Γ s μ hpos hgen hgap ξ).choose_spec

include hmass in
/-- The full ray quotients converge at every evaluation vertex to the
constructed Martin boundary point. -/
theorem rayMartinPoint_tendsto (ξ : ℝ) (x : Γ) :
    Tendsto (fun n => martinQuotient s μ 1 x (cocompactRaySequence Γ ξ n)) atTop
      (𝓝 ((rayMartinPoint Γ s μ hpos hgen hgap ξ).val x)) :=
  rayMartinCluster_tendsto Γ s μ hpos hmass hgen hgap
    (rayMartinPoint_mem Γ s μ hpos hgen hgap ξ) x

include hmass in
/-- Distinct finite geometric directions give distinct actual Martin boundary
points. This asserts injectivity, not a homeomorphism or surjectivity. -/
theorem rayMartinPoint_injective :
    Function.Injective (rayMartinPoint Γ s μ hpos hgen hgap) := by
  intro ξ η he
  by_contra hne
  have hd := rayMartinCluster_disjoint Γ s μ hpos hmass hgen hgap hne
  have hm := rayMartinPoint_mem Γ s μ hpos hgen hgap ξ
  have hn := rayMartinPoint_mem Γ s μ hpos hgen hgap η
  rw [he] at hm
  exact Set.disjoint_left.mp hd hm hn

end Singularity
