import Singularity.RayMartinSeparation
import Singularity.MartinApproximation

/-!
# Ray cluster sets inside the actual Martin boundary

Each finite real boundary direction has a nonempty set of subsequential Martin
limits, contained in the actual abstract Martin boundary. Different directions
have disjoint cluster sets. Singleton cluster sets and continuity remain to be
proved before these sets define the geometric Martin identification.
-/

noncomputable section
open Filter
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- All pointwise subsequential Martin limits along the chosen orbit ray. -/
def rayMartinCluster (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (s : Finset Γ) (μ : Γ → ℝ) (ξ : ℝ) : Set (Γ → ℝ) :=
  {H | ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ z, Tendsto (fun n => martinQuotient s μ 1 z (cocompactRaySequence Γ ξ (φ n))) atTop (𝓝 (H z))}

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

omit [DiscreteTopology Γ] in
include hpos hgen hgap in
/-- Every ray has at least one cluster function. -/
theorem rayMartinCluster_nonempty (ξ : ℝ) : (rayMartinCluster Γ s μ ξ).Nonempty := by
  obtain ⟨H, _, _, φ, hφ, hlim⟩ := martinQuotient_subsequence s μ hpos hgen hgap 1 (cocompactRaySequence Γ ξ)
  exact ⟨H, φ, hφ, hlim⟩

omit [DiscreteTopology Γ] in
include hpos hgen hgap in
/-- Every ray cluster function is an element of the actual Martin boundary. -/
theorem rayMartinCluster_subset_boundary (ξ : ℝ) :
    rayMartinCluster Γ s μ ξ ⊆ martinBoundary s μ 1 := by
  intro H hH
  obtain ⟨φ, hφ, hlim⟩ := hH
  exact martin_limit_mem_boundary s μ hpos hgen hgap 1
    (fun n => cocompactRaySequence Γ ξ (φ n)) H
    (fun z => hφ.tendsto_atTop.eventually ((cocompactRaySequence_eventually_ne Γ ξ z).mono (fun _ h => h.symm))) hlim

include hpos hmass hgen hgap in
/-- Distinct finite boundary directions have disjoint Martin cluster sets. -/
theorem rayMartinCluster_disjoint {ξ η : ℝ} (hξη : ξ ≠ η) :
    Disjoint (rayMartinCluster Γ s μ ξ) (rayMartinCluster Γ s μ η) := by
  apply Set.disjoint_left.mpr
  intro H hξ hη
  obtain ⟨φ, hφ, hφlim⟩ := hξ
  obtain ⟨ψ, hψ, hψlim⟩ := hη
  exact (cocompact_distinct_ray_martin_limits Γ s μ hpos hmass hgen hgap
    ξ η hξη H H φ ψ hφ hψ hφlim hψlim) rfl

end Singularity
