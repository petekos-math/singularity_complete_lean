import Singularity.BoundaryFactorDeficitCompactness
import Singularity.FuchsianDeficitCompactness

/-!
# Transferring auxiliary-boundary compactness to the actual hitting law

A continuous equivariant map with the correct pushforward law transfers
source deficit compactness to the geometric boundary. The auxiliary boundary,
its law, the factor, and its compactness estimate are explicit inputs; none
of these are asserted to exist for an arbitrary Fuchsian group in this file.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped MatrixGroups UpperHalfPlane ENNReal Topology
namespace Singularity

/-- A continuous boundary factor with the actual hitting pushforward suffices
to transfer the geometric compactness property, with no fiber-cardinality
hypothesis. Construction of such source data is a separate obligation. -/
theorem fuchsian_deficit_compactness_of_boundary_factor
    (Γ : Subgroup PSL(2, ℝ)) [MeasurableSpace Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (z : ℍ)
    {B : Type*} [TopologicalSpace B] [MeasurableSpace B]
    [MulAction Γ B] [MeasurableConstSMul Γ B]
    (ν : Measure B) [IsFiniteMeasure ν] (π : B → OnePoint ℝ)
    (hπ : Measurable π) (hcont : Continuous π)
    (heq : ∀ g : Γ, ∀ ξ, π (g • ξ) = g • π ξ)
    (hlaw : Measure.map π ν = projectiveHittingMeasure Γ s z μ hpos hmass)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)
    (hcompact : ∀ g : ℕ → Γ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Z : Set B, Z.Finite ∧ ∀ U : Set B, IsOpen U → Z ⊆ U → ∃ R : ℝ,
        ∀ᶠ n in atTop, ∀ᵐ ξ ∂ν, ξ ∉ U →
          greenDistance s μ 1 (g (φ n)) - stationaryLogCocycle ν (g (φ n)) ξ ≤ R) :
    FuchsianDeficitCompactness Γ s μ hpos hmass z := by
  have h := boundaryFactor_deficit_compactness ν π hπ hcont heq hq
    (fun g => greenDistance s μ 1 g) hcompact
  rw [hlaw] at h
  intro g
  obtain ⟨φ, hφ, Z, hZ, hbound⟩ := h g
  refine ⟨φ, hφ, Z, hZ, fun U hU hZU => ?_⟩
  obtain ⟨R, hR⟩ := hbound U hU hZU
  refine ⟨R, ?_⟩
  filter_upwards [hR] with n hn
  filter_upwards [hn] with ξ hξ hbad
  by_contra hnot
  apply hbad
  change greenDistance s μ 1 (g (φ n)) -
    stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) (g (φ n))
      ((g (φ n))⁻¹ • (g (φ n) • ξ)) ≤ R
  simpa only [inv_smul_smul] using hξ hnot

end Singularity
