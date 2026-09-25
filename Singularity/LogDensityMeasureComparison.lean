import Singularity.LogDensityBounds

/-!
# From bounded log density to comparison of measures

The density bound must hold on the full reference measure class. Equivalence
of the measures is therefore explicit; absolute continuity in only one
direction does not control reference mass outside the density's carrier.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

/-- A bounded logarithmic density of equivalent finite measures yields the
corresponding two-sided exponential comparison of the measures themselves. -/
theorem measure_exp_comparison_of_logDensity_bound {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) [IsFiniteMeasure ν] [IsFiniteMeasure m]
    (hac : ν ≪ m) (hreverse : m ≪ ν) (C : ℝ)
    (hbound : ∀ᵐ ξ ∂ν, |Real.log ((ν.rnDeriv m ξ).toReal)| ≤ C) :
    ENNReal.ofReal (Real.exp (-C)) • m ≤ ν ∧ ν ≤ ENNReal.ofReal (Real.exp C) • m := by
  have hd : ∀ᵐ ξ ∂m, ENNReal.ofReal (Real.exp (-C)) ≤ ν.rnDeriv m ξ ∧
      ν.rnDeriv m ξ ≤ ENNReal.ofReal (Real.exp C) := by
    filter_upwards [hreverse.ae_le hbound, Measure.rnDeriv_pos' hreverse,
      Measure.rnDeriv_lt_top ν m] with ξ hb hp hf
    have hreal : 0 < (ν.rnDeriv m ξ).toReal := ENNReal.toReal_pos hp.ne' hf.ne
    have hl := Real.exp_le_exp.mpr (abs_le.mp hb).1
    have hu := Real.exp_le_exp.mpr (abs_le.mp hb).2
    rw [Real.exp_log hreal] at hl hu
    constructor
    · simpa only [ENNReal.ofReal_toReal hf.ne] using ENNReal.ofReal_le_ofReal hl
    · simpa only [ENNReal.ofReal_toReal hf.ne] using ENNReal.ofReal_le_ofReal hu
  constructor
  · apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.smul_apply, smul_eq_mul, ← Measure.setLIntegral_rnDeriv hac S]
    calc
      _ = ∫⁻ _ in S, ENNReal.ofReal (Real.exp (-C)) ∂m := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hd] with ξ hξ
        exact hξ.1
  · apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.smul_apply, smul_eq_mul, ← Measure.setLIntegral_rnDeriv hac S]
    calc
      _ ≤ ∫⁻ _ in S, ENNReal.ofReal (Real.exp C) ∂m := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hd] with ξ hξ
        exact hξ.2
      _ = _ := by simp

end Singularity
