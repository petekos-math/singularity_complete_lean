import Singularity.FuchsianDeficitAECover
import Singularity.ExceptionalShadowUniformMass
import Singularity.StationaryAtoms
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# The remaining deficit-shadow compactness property

This named property is an explicit hypothesis, not an axiom or a proved
geometric fact. It controls exceptional complements along a subsequence of
every group sequence. It implies both uniform inverse mass and the countable
almost-everywhere coverage needed in the rigidity assembly.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal Topology
namespace Singularity

/-- The outstanding geometric compactness statement, formulated modulo
hitting-null sets to avoid dependence on a derivative's null-domain values. -/
def FuchsianDeficitCompactness (Γ : Subgroup PSL(2, ℝ)) [MeasurableSpace Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (z : ℍ) : Prop :=
  ∀ g : ℕ → Γ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ Z : Set (OnePoint ℝ), Z.Finite ∧
      ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ R : ℝ,
        ∀ᶠ n in atTop, ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
          g (φ n) • ξ ∉ fuchsianGreenDeficitShadow Γ s μ hpos hmass z R (g (φ n)) → ξ ∈ U

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen

/-- The actual hitting law of every nonelementary Fuchsian walk is atomless. -/
theorem fuchsian_hittingMeasure_nullSingleton :
    NullSingletonClass (projectiveHittingMeasure Γ s z μ hpos hmass) := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  exact stationary_nullSingleton_of_infinite_orbits s μ hpos hmass hgen _
    (fuchsian_hittingMeasure_stationary Γ hne s μ hpos hmass hgen z)
    (fun ξ => hne.infinite_boundary_orbits Γ ξ)

/-- The outstanding compactness property would imply uniform almost-full
inverse mass. This is a proved implication, not a proof of compactness itself. -/
theorem fuchsianGreenDeficitShadow_uniform_full_mass_of_compactness
    (hcompact : FuchsianDeficitCompactness Γ s μ hpos hmass z)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ g : Γ, projectiveHittingMeasure Γ s z μ hpos hmass
      (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹'
        fuchsianGreenDeficitShadow Γ s μ hpos hmass z N g)ᶜ) < ε := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  let := fuchsian_hittingMeasure_nullSingleton Γ hne s μ hpos hmass hgen z
  apply uniform_shadow_mass_of_exceptional_subsequences
    (projectiveHittingMeasure Γ s z μ hpos hmass)
    (fun N g => (fun ξ : OnePoint ℝ => g • ξ) ⁻¹'
      fuchsianGreenDeficitShadow Γ s μ hpos hmass z N g)
    (fun g _ _ h => preimage_mono (fuchsianGreenDeficitShadow_mono Γ s μ hpos hmass z g
      (by exact_mod_cast h))) ?_ hε
  intro g
  obtain ⟨φ, hφ, Z, hZ, hconv⟩ := hcompact g
  refine ⟨φ, hφ, Z, hZ, fun U hU hZU => ?_⟩
  obtain ⟨R, hR⟩ := hconv U hU hZU
  obtain ⟨N, hN⟩ := exists_nat_ge R
  refine ⟨N, ?_⟩
  filter_upwards [hR] with n hn
  filter_upwards [hn] with ξ hξ hbad
  apply hξ
  exact fun hmem => hbad (fuchsianGreenDeficitShadow_mono Γ s μ hpos hmass z (g (φ n)) hN hmem)

/-- Compactness supplies the canonical mixed cover for every group sequence,
including every actual random-walk path. -/
theorem fuchsianMixedDeficitShadow_ae_cover_of_compactness
    (hcompact : FuchsianDeficitCompactness Γ s μ hpos hmass z) (g : ℕ → Γ) :
    ∃ N : ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : Finset Γ,
      ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
        ∃ a ∈ F, ∀ᶠ n in atTop,
          g (φ n) • (a⁻¹ • ξ) ∈ fuchsianMixedDeficitShadow Γ s μ hpos hmass z N (g (φ n)) := by
  obtain ⟨φ, hφ, Z, hZ, hconv⟩ := hcompact g
  obtain ⟨ψ, hψ, N, F, hF⟩ := fuchsianMixedDeficitShadow_ae_finite_eventual_cover
    Γ hne s μ hpos hmass hgen z (fun n => g (φ n)) hZ hconv
  exact ⟨N, φ ∘ ψ, hφ.comp hψ, F, hF⟩

end Singularity
