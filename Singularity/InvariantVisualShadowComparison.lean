import Singularity.InvariantVisualShadows

/-!
# Uniform exponential visual estimates on a positive invariant carrier

The restricted visual measure need not be a probability measure. Its positive
mass is absorbed into the additive shadow constant, yielding the exact form
needed by the common-shadow rigidity theorem.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- A positive invariant visual carrier supports uniform exponential shadow
mass bounds and a uniform cocycle error with the same additive constant. -/
theorem invariant_visualShadow_exponential_comparison
    (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' E = E)
    (hpos : 0 < compactPoissonMeasure z E) :
    ∃ r C : ℝ, 0 < r ∧ ∀ g : Γ,
      (ENNReal.ofReal (Real.exp (-dist z (g • z) - C)) ≤
        ((compactPoissonMeasure z).restrict E) (visualShadow z (g • z) r) ∧
       ((compactPoissonMeasure z).restrict E) (visualShadow z (g • z) r) ≤
        ENNReal.ofReal (Real.exp (-dist z (g • z) + C))) ∧
      ∀ᵐ ξ ∂(compactPoissonMeasure z).restrict E,
        ξ ∈ (fun η : OnePoint ℝ => g • η) ⁻¹' visualShadow z (g • z) r →
        |stationaryLogCocycle ((compactPoissonMeasure z).restrict E) g ξ - dist z (g • z)| ≤ C := by
  let := compactPoissonMeasure_probability z
  obtain ⟨r, hr, hhalf⟩ := invariant_visualShadow_uniform_half_mass Γ z hpos
  let a : ℝ := (compactPoissonMeasure z E / 2).toReal
  have hmass : compactPoissonMeasure z E ≤ 1 := (measure_mono (subset_univ E)).trans_eq (measure_univ (μ := compactPoissonMeasure z))
  have hhalfle : compactPoissonMeasure z E / 2 ≤ 1 := ENNReal.half_le_self.trans hmass
  have hfinite : compactPoissonMeasure z E / 2 ≠ ⊤ := ne_top_of_le_ne_top (by simp) hhalfle
  have ha : 0 < a := ENNReal.toReal_pos (ENNReal.half_pos hpos.ne').ne' hfinite
  have ha1 : a ≤ 1 := by
    simpa [a] using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hhalfle
  have hloga : Real.log a ≤ 0 := Real.log_nonpos ha.le ha1
  let C := Real.log (verticalShadowFactor r) - Real.log a
  have hC : Real.log (verticalShadowFactor r) ≤ C := by dsimp [C]; linarith
  refine ⟨r, C, hr, fun g => ?_⟩
  have hb := invariant_visualShadow_mass_bounds Γ z hE hinv g hr
  constructor
  · constructor
    · calc
        ENNReal.ofReal (Real.exp (-dist z (g • z) - C)) =
            ENNReal.ofReal (Real.exp (-dist z (g • z) - Real.log (verticalShadowFactor r))) *
              (compactPoissonMeasure z E / 2) := by
            rw [← ENNReal.ofReal_toReal hfinite, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
            change ENNReal.ofReal (Real.exp (-dist z (g • z) - C)) =
              ENNReal.ofReal (Real.exp (-dist z (g • z) - Real.log (verticalShadowFactor r)) * a)
            congr 1
            rw [← Real.exp_log ha, ← Real.exp_add]
            congr 1
            dsimp [C]
            ring
        _ ≤ ENNReal.ofReal (Real.exp (-dist z (g • z) - Real.log (verticalShadowFactor r))) *
            ((compactPoissonMeasure z).restrict E)
              ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r) := by
            gcongr
            exact hhalf g
        _ ≤ _ := hb.1
    · apply hb.2.trans
      have hm : ((compactPoissonMeasure z).restrict E)
          ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r) ≤ 1 :=
        (Measure.restrict_le_self _).trans ((measure_mono (subset_univ _)).trans_eq
          (measure_univ (μ := compactPoissonMeasure z)))
      calc
        _ ≤ ENNReal.ofReal (Real.exp (-dist z (g • z) + Real.log (verticalShadowFactor r))) * 1 := by gcongr
        _ ≤ _ := by
          rw [mul_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  · filter_upwards [invariant_visual_logCocycle_shadow_error Γ z hE hinv g hr] with ξ hξ hmem
    exact (hξ hmem).trans hC

end Singularity
