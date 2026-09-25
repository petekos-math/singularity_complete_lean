import Singularity.CocycleShadowMeasure

/-!
# Relative shadow concentration from translated measure concentration

A lower bound on inverse-shadow mass and a uniform cocycle error transfer
concentration of translated measures into relative concentration inside the
shadows. Thus the latter is not a separate differentiation premise along a
path for which the translated measures are known to concentrate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B] (ν : Measure B) [IsFiniteMeasure ν]
  (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)

include hq

/-- A quantitative relative-error bound using a positive inverse-shadow mass. -/
theorem relative_shadow_error_le_translated_complement (g : Γ) {S E : Set B}
    (hS : MeasurableSet S) (hE : MeasurableSet E) (D C : ℝ) {c : ℝ} (hc : 0 < c)
    (hmass : c ≤ (ν ((fun ξ : B => g • ξ) ⁻¹' S)).toReal)
    (hbound : ∀ᵐ ξ ∂ν, g • ξ ∈ S → |stationaryLogCocycle ν g ξ - D| ≤ C) :
    (ν (S \ E)).toReal / (ν S).toReal ≤
      (Real.exp (2 * C) / c) * (ν ((fun ξ : B => g • ξ) ⁻¹' Eᶜ)).toReal := by
  have hl := (shadow_mass_bounds_of_logCocycle ν hq g hS D C hbound).1
  have hbad : ∀ᵐ ξ ∂ν, g • ξ ∈ S \ E → |stationaryLogCocycle ν g ξ - D| ≤ C := by
    filter_upwards [hbound] with ξ hξ hmem
    exact hξ hmem.1
  have hu := (shadow_mass_bounds_of_logCocycle ν hq g (hS.diff hE) D C hbad).2
  have hu' : ν (S \ E) ≤ ENNReal.ofReal (Real.exp (-D + C)) *
      ν ((fun ξ : B => g • ξ) ⁻¹' Eᶜ) := by
    apply hu.trans
    gcongr
    exact fun ξ hξ => hξ.2
  have hlr := ENNReal.toReal_mono (measure_ne_top ν S) hl
  have hur := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)) hu'
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hlr hur
  have hlc : Real.exp (-D - C) * c ≤ (ν S).toReal :=
    (mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)).trans hlr
  have hp : 0 < (ν S).toReal := (mul_pos (Real.exp_pos _) hc).trans_le hlc
  rw [div_le_iff₀ hp]
  have he : Real.exp (2 * C) * Real.exp (-D - C) = Real.exp (-D + C) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (-D + C) * (ν ((fun ξ : B => g • ξ) ⁻¹' Eᶜ)).toReal := hur
    _ = ((Real.exp (2 * C) / c) * (ν ((fun ξ : B => g • ξ) ⁻¹' Eᶜ)).toReal) *
        (Real.exp (-D - C) * c) := by
      rw [← he]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlc (by positivity)

/-- Uniform inverse mass and cocycle control give relative concentration in
shadows whenever translated measures concentrate on E. -/
theorem relative_shadow_error_tendsto_zero_of_translated_concentration
    (g : ℕ → Γ) (S : ℕ → Set B) {E : Set B}
    (hS : ∀ n, MeasurableSet (S n)) (hE : MeasurableSet E) (D : ℕ → ℝ)
    (C : ℝ) {c : ℝ} (hc : 0 < c)
    (hmass : ∀ n, c ≤ (ν ((fun ξ : B => g n • ξ) ⁻¹' S n)).toReal)
    (hbound : ∀ n, ∀ᵐ ξ ∂ν, g n • ξ ∈ S n →
      |stationaryLogCocycle ν (g n) ξ - D n| ≤ C)
    (hcon : Tendsto (fun n => (ν ((fun ξ : B => g n • ξ) ⁻¹' Eᶜ)).toReal)
      atTop (𝓝 0)) :
    Tendsto (fun n => (ν (S n \ E)).toReal / (ν (S n)).toReal) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hcon.const_mul (Real.exp (2 * C) / c))
    (fun n => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun n => relative_shadow_error_le_translated_complement ν hq (g n)
      (hS n) hE (D n) C hc (hmass n) (hbound n))

end Singularity
