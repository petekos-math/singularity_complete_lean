import Singularity.BoundaryFactorCocycleBounds

/-!
# Deficit compactness descends through a continuous boundary factor

Exceptional sets are pushed forward, and their open neighborhoods are pulled
back. The local cocycle bound descends by measure domination, rather than by
identifying derivatives on fibers. No injectivity or finite-fiber assumption
is needed. Compactness on the source boundary remains a premise.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Singularity

/-- A continuous equivariant measured factor preserves the subsequential
finite-exception compactness property for cocycle deficits. -/
theorem boundaryFactor_deficit_compactness
    {Γ B C : Type*} [Group Γ]
    [TopologicalSpace B] [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
    [TopologicalSpace C] [MeasurableSpace C] [OpensMeasurableSpace C]
    [MulAction Γ C] [MeasurableConstSMul Γ C]
    (ν : Measure B) [IsFiniteMeasure ν] (π : B → C)
    (hπ : Measurable π) (hcont : Continuous π)
    (heq : ∀ g : Γ, ∀ ξ, π (g • ξ) = g • π ξ)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)
    (D : Γ → ℝ)
    (hcompact : ∀ g : ℕ → Γ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Z : Set B, Z.Finite ∧ ∀ U : Set B, IsOpen U → Z ⊆ U → ∃ R : ℝ,
        ∀ᶠ n in atTop, ∀ᵐ ξ ∂ν, ξ ∉ U →
          D (g (φ n)) - stationaryLogCocycle ν (g (φ n)) ξ ≤ R) :
    ∀ g : ℕ → Γ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Z : Set C, Z.Finite ∧ ∀ U : Set C, IsOpen U → Z ⊆ U → ∃ R : ℝ,
        ∀ᶠ n in atTop, ∀ᵐ η ∂Measure.map π ν, η ∉ U →
          D (g (φ n)) - stationaryLogCocycle (Measure.map π ν) (g (φ n)) η ≤ R := by
  intro g
  obtain ⟨φ, hφ, Z, hZ, hZbound⟩ := hcompact g
  refine ⟨φ, hφ, π '' Z, hZ.image π, fun U hU hZU => ?_⟩
  obtain ⟨R, hR⟩ := hZbound (π ⁻¹' U) (hU.preimage hcont)
    (fun ξ hξ => hZU (mem_image_of_mem π hξ))
  refine ⟨R, ?_⟩
  filter_upwards [hR] with n hn
  exact boundaryFactor_cocycle_deficit_bound ν π hπ heq hq
    (g (φ n)) (D (g (φ n))) R hU.measurableSet.compl hn

end Singularity
