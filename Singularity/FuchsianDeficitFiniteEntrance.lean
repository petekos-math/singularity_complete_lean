import Singularity.FiniteEntranceHarmonicDeficit
import Singularity.FuchsianDeficitCompactness

/-!
# Finite entrance representations suffice for deficit compactness

This reduces the missing analytic estimate to a precise entrance
representation away from a finite exceptional set. The representation is
an explicit hypothesis: the geometric construction of its entrance sets is
not supplied by this module.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology
namespace Singularity

/-- A uniformly chosen finite entrance set for each exceptional neighborhood
supplies the Green-deficit compactness estimate. The entrance representation
itself must still be proved from geometry. -/
theorem fuchsian_deficit_compactness_of_finite_entrance
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (hentrance : ∀ g : ℕ → Γ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Z : Set (OnePoint ℝ), Z.Finite ∧
        ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ A : Finset Γ,
          ∀ᶠ n in atTop, ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass, ξ ∉ U →
            stationaryRealDensity (projectiveHittingMeasure Γ s z μ hpos hmass) (g (φ n))⁻¹ ξ ≤
              ∑ a : A, firstEntranceKernel s μ (A : Set Γ) (g (φ n))⁻¹ a *
                stationaryRealDensity (projectiveHittingMeasure Γ s z μ hpos hmass) (a : Γ) ξ) :
    FuchsianDeficitCompactness Γ s μ hpos hmass z := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableMul Γ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  intro g
  obtain ⟨φ, hφ, Z, hZ, hZentrance⟩ := hentrance g
  refine ⟨φ, hφ, Z, hZ, fun U hU hZU => ?_⟩
  obtain ⟨A, hA⟩ := hZentrance U hU hZU
  obtain ⟨R, hR⟩ := stationary_deficit_bound_of_finite_entrance s μ hpos hmass hgen
    (projectiveNonelementary_rightMarkov_gap Γ hne s μ hpos hmass hgen)
    (projectiveHittingMeasure Γ s z μ hpos hmass)
    (fuchsian_hittingMeasure_stationary Γ hne s μ hpos hmass hgen z) A
  refine ⟨R, ?_⟩
  filter_upwards [hA] with n hn
  filter_upwards [hR (g (φ n)) Uᶜ hn] with ξ hξ hbad
  by_contra hnot
  apply hbad
  change greenDistance s μ 1 (g (φ n)) -
    stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) (g (φ n))
      ((g (φ n))⁻¹ • (g (φ n) • ξ)) ≤ R
  simpa only [inv_smul_smul] using hξ hnot

end Singularity
