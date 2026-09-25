import Singularity.FuchsianFiniteEntrancePaths
import Singularity.GeometricPathConvergence

/-!
# Closed orbit regions and finite path separators

A region of group vertices whose supported exits pass through a finite set
traps every path avoiding that set. Its orbit closure then controls the
boundary limit. This proves the probabilistic separation condition from
explicit deterministic geometry. Such regions have not been constructed
for the remaining Fuchsian cases here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology
namespace Singularity

/-- Paths avoiding A stay in any starting region whose supported exits
require visiting A first. -/
theorem walkPosition_mem_region_of_avoid
    {Γ : Type*} [Group Γ] (s : Finset Γ) (A V : Set Γ)
    (hstep : ∀ v ∈ V, v ∉ A → ∀ a ∈ s, v * a ∈ V)
    {x : Γ} (hx : x ∈ V) (ω : ℕ → s)
    (havoid : ∀ n, walkPosition s x n ω ∉ A) :
    ∀ n, walkPosition s x n ω ∈ V := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [walkPosition_last_step]
    exact hstep _ ih (havoid n) _ (ω n).property

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen

/-- The actual walk started at x converges to x acting on the named limit. -/
theorem fuchsian_boundaryMap_tendsto_from (x : Γ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s x n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (x • projectiveBoundaryMap Γ s z ω))) := by
  obtain ⟨a, ha⟩ := slTwoProjective_surjective (x : PSL(2, ℝ))
  filter_upwards [fuchsian_boundaryMap_tendsto Γ hne s μ hpos hmass hgen z] with ω hω
  have ht := (continuous_const_smul a : Continuous (fun p : OnePoint ℂ => a • p)).tendsto
    (compactBoundaryEmbedding (projectiveBoundaryMap Γ s z ω)) |>.comp hω
  have hleft (n : ℕ) : hyperbolicCompactEmbedding (walkPosition s x n ω • z) =
      a • hyperbolicCompactEmbedding (walkPosition s 1 n ω • z) := by
    have he : walkPosition s x n ω = x * walkPosition s 1 n ω := by
      simpa only [mul_one] using walkPosition_left s x 1 n ω
    rw [he, mul_smul]
    change hyperbolicCompactEmbedding ((x : PSL(2, ℝ)) • _) = _
    rw [← ha, slTwoProjective_smul_hyperbolic, hyperbolicCompactEmbedding_smul]
  have hright : compactBoundaryEmbedding (x • projectiveBoundaryMap Γ s z ω) =
      a • compactBoundaryEmbedding (projectiveBoundaryMap Γ s z ω) := by
    change compactBoundaryEmbedding ((x : PSL(2, ℝ)) • _) = _
    rw [← ha, slTwoProjective_smul_boundary, compactBoundaryEmbedding_smul]
  simpa only [hleft, hright, Function.comp_def] using ht

/-- If the orbit closure of a trapping region meets the ideal boundary only
inside U, ending outside U forces a visit to its finite exit set. -/
theorem fuchsian_boundary_visit_of_separator_region
    (A : Finset Γ) (V : Set Γ) (U : Set (OnePoint ℝ))
    (hstep : ∀ v ∈ V, v ∉ (A : Set Γ) → ∀ a ∈ s, v * a ∈ V)
    (hboundary : ∀ ξ : OnePoint ℝ,
      compactBoundaryEmbedding ξ ∈ closure ((fun v : Γ => hyperbolicCompactEmbedding (v • z)) '' V) →
        ξ ∈ U)
    (x : Γ) (hx : x ∈ V) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      x • projectiveBoundaryMap Γ s z ω ∉ U → ∃ n, walkPosition s x n ω ∈ A := by
  filter_upwards [fuchsian_boundaryMap_tendsto_from Γ hne s μ hpos hmass hgen z x] with ω hω hout
  by_contra hnever
  push Not at hnever
  have hV := walkPosition_mem_region_of_avoid s (A : Set Γ) V hstep hx ω hnever
  apply hout
  apply hboundary
  apply isClosed_closure.mem_of_tendsto hω
  exact Eventually.of_forall (fun n => subset_closure (mem_image_of_mem _ (hV n)))

/-- A subsequential family of deterministic trapping regions supplies deficit
compactness. Their finite exit sets and boundary-closure control are the
explicit geometric inputs; all probabilistic entrance estimates are derived. -/
theorem fuchsian_deficit_compactness_of_separator_regions
    (hregions : ∀ g : ℕ → Γ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Z : Set (OnePoint ℝ), Z.Finite ∧
        ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U →
          ∃ A : Finset Γ, ∃ V : Set Γ,
            (∀ v ∈ V, v ∉ (A : Set Γ) → ∀ a ∈ s, v * a ∈ V) ∧
            (∀ ξ : OnePoint ℝ, compactBoundaryEmbedding ξ ∈
              closure ((fun v : Γ => hyperbolicCompactEmbedding (v • z)) '' V) → ξ ∈ U) ∧
            ∀ᶠ n in atTop, (g (φ n))⁻¹ ∈ V) :
    FuchsianDeficitCompactness Γ s μ hpos hmass z := by
  apply fuchsian_deficit_compactness_of_path_separators Γ hne s μ hpos hmass hgen z
  intro g
  obtain ⟨φ, hφ, Z, hZ, hZregions⟩ := hregions g
  refine ⟨φ, hφ, Z, hZ, fun U hU hZU => ?_⟩
  obtain ⟨A, V, hstep, hboundary, hV⟩ := hZregions U hU hZU
  refine ⟨A, ?_⟩
  filter_upwards [hV] with n hn
  exact fuchsian_boundary_visit_of_separator_region Γ hne s μ hpos hmass hgen z
    A V U hstep hboundary (g (φ n))⁻¹ hn

end Singularity
