import Singularity.CocycleShadowMeasure

/-!
# Exponential shadow estimates from a uniform inverse-mass bound

For a finite measure of total mass at most one, a local cocycle estimate
and inverse mass at least c give exponential shadow estimates with constant
C - log c. This is the remaining mass input for the concrete deficit family.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace Singularity

/-- Absorb a positive inverse-shadow mass into the additive shadow constant.
No global lower bound on the mass is silently supplied by this statement. -/
theorem shadow_estimates_of_positive_inverse_mass
    {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
    [MeasurableConstSMul Γ B] (ν : Measure B) [IsFiniteMeasure ν]
    (hq : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) ν ≪ ν)
    (htotal : ν univ ≤ 1) (g : Γ) {S : Set B} (hS : MeasurableSet S)
    (D C : ℝ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hmass : ENNReal.ofReal c ≤ ν ((fun ξ : B => g • ξ) ⁻¹' S))
    (hbound : ∀ᵐ ξ ∂ν, g • ξ ∈ S → |stationaryLogCocycle ν g ξ - D| ≤ C) :
    (ENNReal.ofReal (Real.exp (-D - (C - Real.log c))) ≤ ν S ∧
      ν S ≤ ENNReal.ofReal (Real.exp (-D + (C - Real.log c)))) ∧
      ∀ᵐ ξ ∂ν, g • ξ ∈ S → |stationaryLogCocycle ν g ξ - D| ≤ C - Real.log c := by
  have hlog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hC : C ≤ C - Real.log c := by linarith
  have hb := shadow_mass_bounds_of_logCocycle ν hq g hS D C hbound
  constructor
  · constructor
    · calc
        _ = ENNReal.ofReal (Real.exp (-D - C)) * ENNReal.ofReal c := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          congr 1
          rw [show -D - (C - Real.log c) = (-D - C) + Real.log c by ring,
            Real.exp_add, Real.exp_log hc]
        _ ≤ ENNReal.ofReal (Real.exp (-D - C)) * ν ((fun ξ : B => g • ξ) ⁻¹' S) := by gcongr
        _ ≤ ν S := hb.1
    · apply hb.2.trans
      have hm : ν ((fun ξ : B => g • ξ) ⁻¹' S) ≤ 1 :=
        (measure_mono (subset_univ _)).trans htotal
      calc
        _ ≤ ENNReal.ofReal (Real.exp (-D + C)) * 1 := by gcongr
        _ ≤ _ := by
          rw [mul_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  · filter_upwards [hbound] with ξ hξ hmem
    exact (hξ hmem).trans hC

end Singularity
