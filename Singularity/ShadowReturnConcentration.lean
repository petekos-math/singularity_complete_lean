import Singularity.CocycleShadowMeasure

/-!
# Pulling relative shadow errors back to the base measure

A shadow cocycle estimate bounds the mass of the inverse image of a bad
subset by a uniform constant times its relative shadow mass. Therefore a
differentiation statement in the shadows yields vanishing return error.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B]
  (ν : Measure B) [IsFiniteMeasure ν]
  (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)

include hq

/-- Relative error in a shadow controls absolute error after pulling back.
The uniform factor is exp(2C) times the total mass. -/
theorem inverse_shadow_error_le_relative (g : Γ) {S E : Set B}
    (hS : MeasurableSet S) (hE : MeasurableSet E) (hpos : 0 < ν S) (D C : ℝ)
    (hbound : ∀ᵐ ξ ∂ν, g • ξ ∈ S → |stationaryLogCocycle ν g ξ - D| ≤ C) :
    (ν ((fun ξ : B => g • ξ) ⁻¹' (S \ E))).toReal ≤
      Real.exp (2 * C) * (ν univ).toReal * ((ν (S \ E)).toReal / (ν S).toReal) := by
  have hbad : ∀ᵐ ξ ∂ν, g • ξ ∈ S \ E → |stationaryLogCocycle ν g ξ - D| ≤ C := by
    filter_upwards [hbound] with ξ hξ hmem
    exact hξ hmem.1
  have hl := (shadow_mass_bounds_of_logCocycle ν hq g (hS.diff hE) D C hbad).1
  have hu := (shadow_mass_bounds_of_logCocycle ν hq g hS D C hbound).2
  have hu' : ν S ≤ ENNReal.ofReal (Real.exp (-D + C)) * ν univ := by
    apply hu.trans
    gcongr
    exact subset_univ _
  have hlr := ENNReal.toReal_mono (measure_ne_top ν (S \ E)) hl
  have hur := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)) hu'
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hlr hur
  have hp : 0 < (ν S).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hcancel : Real.exp (D + C) * Real.exp (-D - C) = 1 := by
    rw [← Real.exp_add]
    rw [show D + C + (-D - C) = 0 by ring, Real.exp_zero]
  have hproduct : Real.exp (D + C) * Real.exp (-D + C) = Real.exp (2 * C) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (D + C) * (Real.exp (-D - C) *
        (ν ((fun ξ : B => g • ξ) ⁻¹' (S \ E))).toReal) := by rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp (D + C) * (ν (S \ E)).toReal :=
      mul_le_mul_of_nonneg_left hlr (Real.exp_nonneg _)
    _ = (Real.exp (D + C) * (ν S).toReal) * ((ν (S \ E)).toReal / (ν S).toReal) := by
      field_simp
    _ ≤ (Real.exp (D + C) * (Real.exp (-D + C) * (ν univ).toReal)) *
        ((ν (S \ E)).toReal / (ν S).toReal) := by
      gcongr
    _ = _ := by rw [← mul_assoc (Real.exp (D + C)), hproduct]

/-- Relative shadow concentration implies vanishing inverse-image error.
This supplies the error hypothesis in the return-cover construction. -/
theorem inverse_shadow_error_tendsto_zero
    (g : ℕ → Γ) (S : ℕ → Set B) {E : Set B}
    (hS : ∀ n, MeasurableSet (S n)) (hE : MeasurableSet E)
    (hpos : ∀ n, 0 < ν (S n)) (D : ℕ → ℝ) (C : ℝ)
    (hbound : ∀ n, ∀ᵐ ξ ∂ν, g n • ξ ∈ S n → |stationaryLogCocycle ν (g n) ξ - D n| ≤ C)
    (hratio : Tendsto (fun n => (ν (S n \ E)).toReal / (ν (S n)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => ν ((fun ξ : B => g n • ξ) ⁻¹' (S n \ E))) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => (ν ((fun ξ : B => g n • ξ) ⁻¹' (S n \ E))).toReal) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hratio.const_mul (Real.exp (2 * C) * (ν univ).toReal))
      (fun _ => ENNReal.toReal_nonneg) (fun n => ?_)
    exact inverse_shadow_error_le_relative ν hq (g n) (hS n) hE (hpos n) (D n) C (hbound n)
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_zero]
    using ENNReal.tendsto_ofReal hr

end Singularity
