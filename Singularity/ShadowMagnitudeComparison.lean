import Singularity.MixedShadowMeasure

/-!
# Recovering cocycle magnitudes from shadow masses

These estimates isolate the numerical end of the rigidity argument. They do
not assume that an arbitrary hitting law has geometric or Green shadow bounds.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Singularity

/-- Two exponential mass bounds control the logarithmic mass with the same
additive error. Finite measure ensures the real logarithm is well-defined. -/
theorem log_measure_error_of_exp_bounds {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν] (S : Set B) (D C : ℝ)
    (hl : ENNReal.ofReal (Real.exp (-D - C)) ≤ ν S)
    (hu : ν S ≤ ENNReal.ofReal (Real.exp (-D + C))) :
    |Real.log (ν S).toReal + D| ≤ C := by
  have hlr : Real.exp (-D - C) ≤ (ν S).toReal := by
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
      ENNReal.toReal_mono (measure_ne_top _ _) hl
  have hur : (ν S).toReal ≤ Real.exp (-D + C) := by
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  have hp : 0 < (ν S).toReal := (Real.exp_pos _).trans_le hlr
  have hlogl := Real.log_le_log (Real.exp_pos _) hlr
  have hlogu := Real.log_le_log hp hur
  rw [Real.log_exp] at hlogl hlogu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exponential comparison of measures bounds the difference of their log
masses on each positive-mass set. -/
theorem log_measure_difference_of_exp_comparison {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) [IsFiniteMeasure ν] [IsFiniteMeasure m] (S : Set B)
    (hS : 0 < m S) (K : ℝ)
    (hl : ENNReal.ofReal (Real.exp (-K)) • m ≤ ν)
    (hu : ν ≤ ENNReal.ofReal (Real.exp K) • m) :
    |Real.log (ν S).toReal - Real.log (m S).toReal| ≤ K := by
  have hp : 0 < (m S).toReal := ENNReal.toReal_pos hS.ne' (measure_ne_top _ _)
  have hlr := ENNReal.toReal_mono (measure_ne_top ν S) (hl S)
  have ht : (ENNReal.ofReal (Real.exp K) • m) S ≠ ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hur := ENNReal.toReal_mono ht (hu S)
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hlr hur
  have hlp : 0 < (ν S).toReal := (mul_pos (Real.exp_pos _) hp).trans_le hlr
  have hlogl := Real.log_le_log (mul_pos (Real.exp_pos _) hp) hlr
  have hlogu := Real.log_le_log hlp hur
  rw [Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp] at hlogl hlogu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Comparable measures with exponential estimates on one common shadow have
uniformly comparable magnitudes. This is the final numerical rigidity step. -/
theorem shadow_magnitude_comparison {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) [IsFiniteMeasure ν] [IsFiniteMeasure m] (S : Set B)
    (Dν Dm Cν Cm K : ℝ)
    (hνl : ENNReal.ofReal (Real.exp (-Dν - Cν)) ≤ ν S)
    (hνu : ν S ≤ ENNReal.ofReal (Real.exp (-Dν + Cν)))
    (hml : ENNReal.ofReal (Real.exp (-Dm - Cm)) ≤ m S)
    (hmu : m S ≤ ENNReal.ofReal (Real.exp (-Dm + Cm)))
    (hl : ENNReal.ofReal (Real.exp (-K)) • m ≤ ν)
    (hu : ν ≤ ENNReal.ofReal (Real.exp K) • m) :
    |Dν - Dm| ≤ Cν + Cm + K := by
  have hp : 0 < m S := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le hml
  have h1 := log_measure_error_of_exp_bounds ν S Dν Cν hνl hνu
  have h2 := log_measure_error_of_exp_bounds m S Dm Cm hml hmu
  have h3 := log_measure_difference_of_exp_comparison ν m S hp K hl hu
  apply abs_le.mpr
  rcases abs_le.mp h1 with ⟨h1l, h1u⟩
  rcases abs_le.mp h2 with ⟨h2l, h2u⟩
  rcases abs_le.mp h3 with ⟨h3l, h3u⟩
  constructor <;> linarith

/-- For an upper magnitude estimate only the reference shadow's lower mass,
the target shadow's upper mass, and one-sided measure domination are needed. -/
theorem shadow_magnitude_upper_of_one_sided_comparison {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) (S : Set B) (Dν Dm C K a : ℝ) (ha : 0 < a)
    (hml : ENNReal.ofReal (Real.exp (-Dm)) * ENNReal.ofReal a ≤ m S)
    (hνu : ν S ≤ ENNReal.ofReal (Real.exp (C - Dν)))
    (hdom : m ≤ ENNReal.ofReal (Real.exp K) • ν) :
    Dν ≤ Dm + K + C - Real.log a := by
  have hb : ENNReal.ofReal (Real.exp (-Dm) * a) ≤
      ENNReal.ofReal (Real.exp K * Real.exp (C - Dν)) := by
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_mul (Real.exp_nonneg _)]
    apply hml.trans
    apply (hdom S).trans
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  have hbr : Real.exp (-Dm) * a ≤ Real.exp K * Real.exp (C - Dν) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) ha) hbr
  rw [Real.log_mul (Real.exp_pos _).ne' ha.ne', Real.log_mul
    (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp, Real.log_exp] at hlog
  linarith

end Singularity
