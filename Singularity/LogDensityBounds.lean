import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Logarithmic bounds from measure domination

Two-sided exponential comparison of measures gives the corresponding bound
on the logarithm of their actual Radon–Nikodym derivative.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace Singularity

/-- Domination by a scalar multiple gives the almost-everywhere real density bound. -/
theorem real_rnDeriv_le_of_le_smul {X : Type*} [MeasurableSpace X]
    (ν m : Measure X) [SigmaFinite ν] [SigmaFinite m] (C : ℝ) (hC : 0 ≤ C)
    (hdom : ν ≤ ENNReal.ofReal C • m) :
    ∀ᵐ x ∂m, (ν.rnDeriv m x).toReal ≤ C := by
  have h := ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν m)
    (g := fun _ : X => ENNReal.ofReal C) (fun S hS _ => by
      calc
        ∫⁻ x in S, ν.rnDeriv m x ∂m ≤ ν S := Measure.setLIntegral_rnDeriv_le S
        _ ≤ (ENNReal.ofReal C • m) S := hdom S
        _ = ∫⁻ x in S, ENNReal.ofReal C ∂m := by simp)
  filter_upwards [h] with x hx
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hx

/-- Reverse domination gives the lower density bound when the measure is
absolutely continuous; finiteness of the derivative is handled almost everywhere. -/
theorem real_rnDeriv_ge_of_smul_le {X : Type*} [MeasurableSpace X]
    (ν m : Measure X) [SigmaFinite ν] [SigmaFinite m] (hac : ν ≪ m)
    (c : ℝ) (hc : 0 ≤ c) (hdom : ENNReal.ofReal c • m ≤ ν) :
    ∀ᵐ x ∂m, c ≤ (ν.rnDeriv m x).toReal := by
  have h := ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (measurable_const : Measurable (fun _ : X => ENNReal.ofReal c))
    (g := ν.rnDeriv m) (fun S hS _ => by
      calc
        ∫⁻ x in S, ENNReal.ofReal c ∂m = (ENNReal.ofReal c • m) S := by simp
        _ ≤ ν S := hdom S
        _ = ∫⁻ x in S, ν.rnDeriv m x ∂m := (Measure.setLIntegral_rnDeriv hac S).symm)
  filter_upwards [h, Measure.rnDeriv_lt_top ν m] with x hx hf
  simpa only [ENNReal.toReal_ofReal hc] using ENNReal.toReal_mono hf.ne hx

/-- Exponential measure comparison becomes an absolute bound on the log density. -/
theorem log_rnDeriv_abs_le_of_exp_comparison {X : Type*} [MeasurableSpace X]
    (ν m : Measure X) [SigmaFinite ν] [SigmaFinite m] (D : ℝ)
    (hlower : ENNReal.ofReal (Real.exp (-D)) • m ≤ ν)
    (hupper : ν ≤ ENNReal.ofReal (Real.exp D) • m) :
    ∀ᵐ x ∂m, |Real.log ((ν.rnDeriv m x).toReal)| ≤ D := by
  have hac := Measure.absolutelyContinuous_of_le_smul hupper
  filter_upwards [real_rnDeriv_ge_of_smul_le ν m hac _ (Real.exp_nonneg _) hlower,
    real_rnDeriv_le_of_le_smul ν m _ (Real.exp_nonneg _) hupper] with x hl hu
  have hl' := Real.log_le_log (Real.exp_pos _) hl
  have hu' := Real.log_le_log ((Real.exp_pos _).trans_le hl) hu
  rw [Real.log_exp] at hl' hu'
  exact abs_le.mpr ⟨hl', hu'⟩

end Singularity
