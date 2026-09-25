import Singularity.CocycleShadowMeasure

/-!
# The measure estimate for mixed shadows

Intersecting two shadows retains an explicit mass bound if the complements
of their inverse images are small. Combined with the actual logarithmic
cocycle estimate, this proves the exponential mixed-shadow estimate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace Singularity

/-- A quantitative intersection bound, expressed in terms of complement masses. -/
theorem probability_inter_lower_of_compl_bounds {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν] {S T : Set B}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (a b : ℝ≥0∞)
    (ha : ν Sᶜ ≤ a) (hb : ν Tᶜ ≤ b) :
    1 - (a + b) ≤ ν (S ∩ T) := by
  have hc : ν (S ∩ T)ᶜ ≤ a + b := by
    rw [compl_inter]
    exact (measure_union_le _ _).trans (add_le_add ha hb)
  calc
    1 - (a + b) ≤ 1 - ν (S ∩ T)ᶜ := tsub_le_tsub_left hc _
    _ = ν (S ∩ T) := by
      rw [← measure_univ (μ := ν), ← measure_compl (hS.inter hT).compl (measure_ne_top _ _)]
      simp

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B]
  (ν : Measure B) [IsProbabilityMeasure ν]
  (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)

include hq

/-- Mixed shadows have exponential mass bounds once their inverse complements
are small and one of the shadows carries the cocycle estimate. -/
theorem mixed_shadow_mass_bounds_of_logCocycle (g : Γ) {S T : Set B}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (D C : ℝ)
    (hbound : ∀ᵐ ξ ∂ν, ξ ∈ (fun η : B => g • η) ⁻¹' S →
      |stationaryLogCocycle ν g ξ - D| ≤ C)
    (a b : ℝ≥0∞)
    (ha : ν (((fun ξ : B => g • ξ) ⁻¹' S)ᶜ) ≤ a)
    (hb : ν (((fun ξ : B => g • ξ) ⁻¹' T)ᶜ) ≤ b) :
    ENNReal.ofReal (Real.exp (-D - C)) * (1 - (a + b)) ≤ ν (S ∩ T) ∧
      ν (S ∩ T) ≤ ENNReal.ofReal (Real.exp (-D + C)) := by
  have he : ∀ᵐ ξ ∂ν, ξ ∈ (fun η : B => g • η) ⁻¹' (S ∩ T) →
      |stationaryLogCocycle ν g ξ - D| ≤ C := by
    filter_upwards [hbound] with ξ hξ hmem
    exact hξ hmem.1
  have h := shadow_mass_bounds_of_logCocycle ν hq g (hS.inter hT) D C he
  have hl := probability_inter_lower_of_compl_bounds ν
    (hS.preimage (measurable_const_smul g)) (hT.preimage (measurable_const_smul g)) a b ha hb
  constructor
  · apply le_trans ?_ h.1
    gcongr
    exact hl
  · apply h.2.trans
    have hm : ν ((fun ξ : B => g • ξ) ⁻¹' (S ∩ T)) ≤ 1 := by
      exact (measure_mono (subset_univ _)).trans_eq (measure_univ (μ := ν))
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-D + C)) * 1 := by gcongr
      _ = _ := mul_one _

/-- If the two inverse-shadow complements each have mass at most one quarter,
the mixed shadow has a uniform positive exponential lower bound. -/
theorem mixed_shadow_mass_bounds_of_quarter_complements (g : Γ) {S T : Set B}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (D C : ℝ)
    (hbound : ∀ᵐ ξ ∂ν, ξ ∈ (fun η : B => g • η) ⁻¹' S →
      |stationaryLogCocycle ν g ξ - D| ≤ C)
    (ha : ν (((fun ξ : B => g • ξ) ⁻¹' S)ᶜ) ≤ 1 / 4)
    (hb : ν (((fun ξ : B => g • ξ) ⁻¹' T)ᶜ) ≤ 1 / 4) :
    ENNReal.ofReal (Real.exp (-D - C)) / 2 ≤ ν (S ∩ T) ∧
      ν (S ∩ T) ≤ ENNReal.ofReal (Real.exp (-D + C)) := by
  have h := mixed_shadow_mass_bounds_of_logCocycle ν hq g hS hT D C hbound
    (1 / 4) (1 / 4) ha hb
  have he : (1 : ℝ≥0∞) - (1 / 4 + 1 / 4) = 1 / 2 := by
    have hn : (1 : ℝ≥0) - (1 / 4 + 1 / 4) = 1 / 2 := tsub_eq_of_eq_add (by norm_num)
    have he := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hn
    simpa only [ENNReal.coe_sub, ENNReal.coe_add,
      ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
      ENNReal.coe_one, ENNReal.coe_ofNat] using he
  rw [he] at h
  simpa only [div_eq_mul_inv, one_mul] using h

end Singularity
