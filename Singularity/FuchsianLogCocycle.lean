import Singularity.StationaryCocycleDomain
import Singularity.RadonNikodymCoboundary
import Singularity.FuchsianHittingErgodicity
import Singularity.GreenWordComparison

/-!
# Logarithmic cocycles for the actual projective hitting measure

All cocycle and Green estimates use the original walk, with its spectral gap
proved from nonelementarity. Under nonsingularity, the hitting and visual
cocycles differ by the logarithm of the actual visual density. This identity
does not supply a uniform bound on that density.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

local notation "ν" => projectiveHittingMeasure Γ s z μ hpos hmass

include hne hgen

/-- The actual hitting cocycle is bounded between the two directed Green distances. -/
theorem fuchsian_logCocycle_green_bounds :
    ∀ᵐ ξ ∂ν, ∀ g : Γ, -greenDistance s μ g 1 ≤ stationaryLogCocycle ν g ξ ∧
      stationaryLogCocycle ν g ξ ≤ greenDistance s μ 1 g := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableMul Γ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  exact stationaryLogCocycle_ae_green_bounds s μ hpos hgen ν
    (fuchsian_hittingMeasure_stationary Γ hne s μ hpos hmass hgen z) hmass
    (projectiveNonelementary_rightMarkov_gap Γ hne s μ hpos hmass hgen)

/-- A single invariant conull domain supports the exact cocycle identities and
all Green bounds for the actual projective hitting measure. -/
theorem fuchsian_logCocycle_invariant_domain :
    ∃ E : Set (OnePoint ℝ), MeasurableSet E ∧ (∀ᵐ ξ ∂ν, ξ ∈ E) ∧
      (∀ g : Γ, (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' E = E) ∧
      ∀ ξ ∈ E, stationaryLogCocycle ν (1 : Γ) ξ = 0 ∧
        (∀ g h : Γ, stationaryLogCocycle ν (g * h) ξ =
          stationaryLogCocycle ν g (h • ξ) + stationaryLogCocycle ν h ξ) ∧
        (∀ g : Γ, -greenDistance s μ g 1 ≤ stationaryLogCocycle ν g ξ ∧
          stationaryLogCocycle ν g ξ ≤ greenDistance s μ 1 g) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableMul Γ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  exact stationaryLogCocycle_invariant_domain s μ hpos hmass hgen
    (projectiveNonelementary_rightMarkov_gap Γ hne s μ hpos hmass hgen) ν
    (fuchsian_hittingMeasure_stationary Γ hne s μ hpos hmass hgen z)

/-- Every element's cocycle is essentially bounded, with a common linear
word-length bound. No symmetry of the jump probabilities is assumed. -/
theorem fuchsian_logCocycle_word_bound :
    ∃ b : ℝ, 0 < b ∧ ∀ᵐ ξ ∂ν, ∀ g : Γ,
      |stationaryLogCocycle ν g ξ| ≤ b * (wordDistance s hgen 1 g : ℝ) := by
  obtain ⟨a, b, D, _, hb, _, hcomp⟩ :=
    projectiveNonelementary_greenDistance_word_comparison Γ hne s μ hpos hmass hgen
  refine ⟨b, hb, ?_⟩
  filter_upwards [fuchsian_logCocycle_green_bounds Γ hne s μ hpos hmass hgen z] with ξ hξ
  intro g
  apply abs_le.mpr
  have hforward := (hcomp 1 g).2
  have hbackward := (hcomp g 1).2
  rw [wordDistance_symm s hgen g 1] at hbackward
  constructor <;> linarith [(hξ g).1, (hξ g).2]

/-- Under nonsingularity, hitting and visual cocycles differ by the logarithm
of the actual density, simultaneously for every group element. -/
theorem fuchsian_logCocycle_visual_coboundary
    (hns : ¬ ν ⟂ₘ compactPoissonMeasure z) :
    ∀ᵐ ξ ∂ν, ∀ g : Γ,
      stationaryLogCocycle ν g ξ = stationaryLogCocycle (compactPoissonMeasure z) g ξ +
        Real.log (((ν).rnDeriv (compactPoissonMeasure z) ξ).toReal) -
        Real.log (((ν).rnDeriv (compactPoissonMeasure z) (g • ξ)).toReal) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  let := compactPoissonMeasure_probability z
  apply ae_all_iff.mpr
  intro g
  exact stationaryLogCocycle_change_measure ν (compactPoissonMeasure z)
    (fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular Γ hne s μ hpos hmass hgen z hns)
    (fun g => (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z g).1)
    (fun g => compactPoissonMeasure_projective_quasiInvariant z (g : PSL(2, ℝ))) g

end Singularity
