import Singularity.RadonNikodymCoboundary

/-!
# Shadow masses from logarithmic Radon–Nikodym estimates

This is the measure-theoretic part of the shadow lemma. The logarithmic
cocycle is the one defined from the actual translated measure. A local
cocycle estimate controls the mass of every measurable subset of a shadow.
No geometric or Martin-boundary identification is assumed here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B]
  (ν : Measure B) [IsFiniteMeasure ν]
  (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)

include hq

/-- Exponentiating the negative actual log cocycle recovers the inverse
translated Radon–Nikodym derivative almost everywhere. -/
theorem exp_neg_stationaryLogCocycle (g : Γ) :
    ∀ᵐ ξ ∂ν, ENNReal.ofReal (Real.exp (-stationaryLogCocycle ν g ξ)) =
      stationaryDensity ν g⁻¹ ξ := by
  filter_upwards [translate_realDensity_pos ν hq g⁻¹,
    Measure.rnDeriv_lt_top (Measure.map (fun ξ : B => g⁻¹ • ξ) ν) ν] with ξ hp hf
  simp only [stationaryLogCocycle, neg_neg, Real.exp_log hp]
  exact ENNReal.ofReal_toReal hf.ne

/-- The mass of an image is the integral of the exponential of the negative
logarithmic cocycle, including when the cocycle is merely measurable. -/
theorem measure_smul_image_eq_lintegral_logCocycle (g : Γ) {E : Set B}
    (hE : MeasurableSet E) :
    ν ((fun ξ : B => g • ξ) '' E) =
      ∫⁻ ξ in E, ENNReal.ofReal (Real.exp (-stationaryLogCocycle ν g ξ)) ∂ν := by
  have he : (fun ξ : B => g⁻¹ • ξ) ⁻¹' E = (fun ξ : B => g • ξ) '' E := by
    ext ξ
    constructor
    · intro h
      exact ⟨g⁻¹ • ξ, h, smul_inv_smul g ξ⟩
    · rintro ⟨η, hη, rfl⟩
      simpa using hη
  rw [← he, ← Measure.map_apply (measurable_const_smul g⁻¹) hE,
    ← Measure.setLIntegral_rnDeriv (hq g⁻¹) E]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (exp_neg_stationaryLogCocycle ν hq g)] with ξ hξ
  exact hξ.symm

/-- A cocycle magnitude estimate on a measurable set gives two-sided
exponential bounds for its image mass. -/
theorem measure_smul_image_bounds_of_logCocycle (g : Γ) {E : Set B}
    (hE : MeasurableSet E) (D C : ℝ)
    (hbound : ∀ᵐ ξ ∂ν, ξ ∈ E → |stationaryLogCocycle ν g ξ - D| ≤ C) :
    ENNReal.ofReal (Real.exp (-D - C)) * ν E ≤ ν ((fun ξ : B => g • ξ) '' E) ∧
      ν ((fun ξ : B => g • ξ) '' E) ≤ ENNReal.ofReal (Real.exp (-D + C)) * ν E := by
  rw [measure_smul_image_eq_lintegral_logCocycle ν hq g hE]
  have hb := (ae_restrict_iff' hE).mpr hbound
  constructor
  · calc
      _ = ∫⁻ _ in E, ENNReal.ofReal (Real.exp (-D - C)) ∂ν := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hb] with ξ hξ
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hξ).2]))
  · calc
      _ ≤ ∫⁻ _ in E, ENNReal.ofReal (Real.exp (-D + C)) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hb] with ξ hξ
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hξ).1]))
      _ = _ := by simp

/-- Shadow formulation: apply the local derivative estimate on the inverse
image of the shadow. The inverse-shadow mass is retained exactly. -/
theorem shadow_mass_bounds_of_logCocycle (g : Γ) {S : Set B}
    (hS : MeasurableSet S) (D C : ℝ)
    (hbound : ∀ᵐ ξ ∂ν, ξ ∈ (fun η : B => g • η) ⁻¹' S →
      |stationaryLogCocycle ν g ξ - D| ≤ C) :
    ENNReal.ofReal (Real.exp (-D - C)) * ν ((fun ξ : B => g • ξ) ⁻¹' S) ≤ ν S ∧
      ν S ≤ ENNReal.ofReal (Real.exp (-D + C)) * ν ((fun ξ : B => g • ξ) ⁻¹' S) := by
  have h := measure_smul_image_bounds_of_logCocycle ν hq g
    (hS.preimage (measurable_const_smul g)) D C hbound
  simpa only [image_preimage_eq _ (MulAction.surjective g)] using h

end Singularity
