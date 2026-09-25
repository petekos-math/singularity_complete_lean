import Singularity.InvariantVisualShadowComparison
import Singularity.FuchsianDensityCocycle

/-!
# Matching the invariant visual carrier to the actual hitting measure

Under nonsingularity, the restricted visual measure is equivalent to the
hitting law and retains the original visual cocycle. Its shadow masses have
the uniform exponential estimates required by the rigidity argument. No full
visual measure equivalence or harmonic-shadow estimate is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- The positive invariant carrier can be chosen with unchanged density and
visual cocycles and with uniform visual shadow estimates. All cocycle
identities and bounds hold simultaneously for the countable group. -/
theorem fuchsian_hittingMeasure_visualCarrier_shadow_data
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (hns : ¬ projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z) :
    let ν := projectiveHittingMeasure Γ s z μ hpos hmass
    let m := compactPoissonMeasure z
    ∃ E : Set (OnePoint ℝ), ∃ r C : ℝ,
      MeasurableSet E ∧ (∀ᵐ ξ ∂ν, ξ ∈ E) ∧ 0 < m E ∧
      (∀ g : Γ, (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' E = E) ∧
      (ν ≪ m.restrict E) ∧ (m.restrict E ≪ ν) ∧ 0 < r ∧
      (ν.rnDeriv (m.restrict E) =ᵐ[ν] ν.rnDeriv m) ∧
      (∀ g : Γ, Measure.map (fun ξ : OnePoint ℝ => g • ξ) (m.restrict E) ≪ m.restrict E) ∧
      (∀ g : Γ, ENNReal.ofReal (Real.exp (-dist z (g • z) - C)) ≤
          (m.restrict E) (visualShadow z (g • z) r) ∧
        (m.restrict E) (visualShadow z (g • z) r) ≤
          ENNReal.ofReal (Real.exp (-dist z (g • z) + C))) ∧
      ∀ᵐ ξ ∂ν, ∀ g : Γ,
        stationaryLogCocycle (m.restrict E) g ξ = stationaryLogCocycle m g ξ ∧
        (g • ξ ∈ visualShadow z (g • z) r →
          |stationaryLogCocycle (m.restrict E) g ξ - dist z (g • z)| ≤ C) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let ν := projectiveHittingMeasure Γ s z μ hpos hmass
  let m := compactPoissonMeasure z
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  let := compactPoissonMeasure_probability z
  obtain ⟨E, hE, hfull, hinv, hνE, hEν, _⟩ :=
    fuchsian_hittingMeasure_invariant_visual_carrier Γ hne s μ hpos hmass hgen z hns
  have hpositive : 0 < m E := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hv : ν univ = 0 := hνE (show (m.restrict E) univ = 0 by simpa using hzero)
    simp only [measure_univ, one_ne_zero] at hv
  have hq (g : Γ) : Measure.map (fun ξ : OnePoint ℝ => g • ξ) m ≪ m :=
    compactPoissonMeasure_projective_quasiInvariant z (g : PSL(2, ℝ))
  obtain ⟨r, C, hr, hb⟩ := invariant_visualShadow_exponential_comparison Γ z hE hinv hpositive
  refine ⟨E, r, C, hE, hfull, hpositive, hinv, hνE, hEν, hr, ?_, ?_, ?_, ?_⟩
  · exact rnDeriv_restrict_reference_of_conull ν m
      (fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular Γ hne s μ hpos hmass hgen z hns)
      hE hfull
  · exact invariant_restrict_quasiInvariant m hE hinv hq
  · exact fun g => (hb g).1
  · apply ae_all_iff.mpr
    intro g
    filter_upwards [hνE.ae_le (stationaryLogCocycle_invariant_restrict m hE hinv hq g),
      hνE.ae_le (hb g).2] with ξ he hs
    exact ⟨he, hs⟩

end Singularity
