import Singularity.FuchsianMixedDeficitShadows
import Singularity.ShadowEstimatesFromInverseMass
import Singularity.InvariantVisualShadows

/-!
# Complete local estimates for the concrete mixed family

Both logarithmic cocycle estimates are established internally. Uniform
positive inverse mass is the explicit remaining input to the two-sided
exponential mass estimates, for the hitting law and the visual carrier.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal
namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (z : ℍ)

/-- Hitting-measure exponential and cocycle estimates for the actual mixed
family; only a uniform positive inverse-mass bound remains as input. -/
theorem fuchsianMixedDeficitShadow_hitting_estimates
    (hne : ProjectiveNonelementary Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (N : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hinverse : ∀ g : Γ, ENNReal.ofReal c ≤ projectiveHittingMeasure Γ s z μ hpos hmass
      ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g)) :
    let ν := projectiveHittingMeasure Γ s z μ hpos hmass
    let C := (N : ℝ) - Real.log c
    ∀ g : Γ,
      (ENNReal.ofReal (Real.exp (-greenDistance s μ 1 g - C)) ≤
          ν (fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g) ∧
        ν (fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g) ≤
          ENNReal.ofReal (Real.exp (-greenDistance s μ 1 g + C))) ∧
      ∀ᵐ ξ ∂ν, g • ξ ∈ fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g →
        |stationaryLogCocycle ν g ξ - greenDistance s μ 1 g| ≤ C := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  dsimp only
  intro g
  apply shadow_estimates_of_positive_inverse_mass _
    (fun a => (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z a).1)
    (by simp) g (measurableSet_fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g)
    (greenDistance s μ 1 g) N hc hc1 (hinverse g)
  filter_upwards [fuchsianMixedDeficitShadow_logCocycle_bound Γ s μ hpos hmass z hne hgen]
    with ξ hξ
  exact hξ N g

omit [DiscreteTopology Γ] [MeasurableSingletonClass Γ] in
/-- The restricted visual side has the same form of estimates on the same
mixed sets, using the proved visual cocycle formula. -/
theorem fuchsianMixedDeficitShadow_carrier_estimates
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' E = E)
    (N : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hinverse : ∀ g : Γ, ENNReal.ofReal c ≤ ((compactPoissonMeasure z).restrict E)
      ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g)) :
    let m := (compactPoissonMeasure z).restrict E
    let C := Real.log (verticalShadowFactor (1 / ((N : ℝ) + 1))) - Real.log c
    ∀ g : Γ,
      (ENNReal.ofReal (Real.exp (-dist z (g • z) - C)) ≤
          m (fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g) ∧
        m (fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g) ≤
          ENNReal.ofReal (Real.exp (-dist z (g • z) + C))) ∧
      ∀ᵐ ξ ∂m, g • ξ ∈ fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g →
        |stationaryLogCocycle m g ξ - dist z (g • z)| ≤ C := by
  let := compactPoissonMeasure_probability z
  have hq (g : Γ) : Measure.map (fun ξ : OnePoint ℝ => g • ξ) (compactPoissonMeasure z) ≪
      compactPoissonMeasure z := compactPoissonMeasure_projective_quasiInvariant z (g : PSL(2, ℝ))
  dsimp only
  intro g
  apply shadow_estimates_of_positive_inverse_mass ((compactPoissonMeasure z).restrict E)
    (fun a => invariant_restrict_quasiInvariant (compactPoissonMeasure z) hE hinv hq a)
    ((Measure.restrict_le_self _).trans (le_of_eq (measure_univ (μ := compactPoissonMeasure z))))
    g (measurableSet_fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g)
    (dist z (g • z)) (Real.log (verticalShadowFactor (1 / ((N : ℝ) + 1)))) hc hc1 (hinverse g)
  filter_upwards [invariant_visual_logCocycle_shadow_error Γ z hE hinv g
    (by positivity : (0 : ℝ) < 1 / ((N : ℝ) + 1))] with ξ hξ hmem
  exact hξ hmem.2

end Singularity
