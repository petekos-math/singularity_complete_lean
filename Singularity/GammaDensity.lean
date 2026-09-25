import Singularity.FourierReduction
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Fourier.Convolution

/-!
# A logarithmic exponential density and its Fourier transform

The density g(t) = exp(t) exp(-exp(t)) has Fourier transform
Gamma(1 - 2πiξ). Its autocorrelation will give the Liouville kernel.
-/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform

namespace Singularity

/-- The logarithm of a unit exponential random variable has this density. -/
def gammaDensity (t : ℝ) : ℝ := Real.exp t * Real.exp (-Real.exp t)

/-- Complex-valued version, used by the Fourier integral. -/
def gammaDensityC (t : ℝ) : ℂ := gammaDensity t

theorem gammaDensity_pos (t : ℝ) : 0 < gammaDensity t := by
  unfold gammaDensity
  positivity

theorem gammaDensity_continuous : Continuous gammaDensity := by
  unfold gammaDensity
  fun_prop

/-- Integrability follows by the change of variables x = exp(t). -/
theorem gammaDensity_integrable : Integrable gammaDensity := by
  change Integrable (fun t => Real.exp t * Real.exp (-Real.exp t))
  simpa [smul_eq_mul] using
    (integrable_comp_exp (fun x : ℝ => Real.exp (-x))).mpr (integrableOn_exp_neg_Ioi 0)

theorem gammaDensityC_integrable : Integrable gammaDensityC := gammaDensity_integrable.ofReal

/-- The density has total mass one. -/
theorem gammaDensity_integral : ∫ t, gammaDensity t = 1 := by
  change (∫ t, Real.exp t • Real.exp (-Real.exp t)) = 1
  rw [integral_comp_exp (fun x : ℝ => Real.exp (-x))]
  simpa using integral_exp_mul_Ioi (a := -1) (by norm_num) 0

/-- Complex powers of a positive real exponential. -/
theorem cpow_real_exp (t : ℝ) (z : ℂ) : (Real.exp t : ℂ) ^ z = Complex.exp ((t : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne')]
  rw [← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

/-- Pointwise identity for the change of variables in the Fourier integral. -/
theorem gammaDensity_fourier_integrand (ξ t : ℝ) :
    Complex.exp ((-2 * Real.pi * t * ξ : ℝ) * Complex.I) * gammaDensityC t =
      Real.exp t • ((Real.exp (-Real.exp t) : ℂ) *
        (Real.exp t : ℂ) ^ ((1 - (2 * Real.pi * ξ : ℝ) * Complex.I) - 1)) := by
  rw [cpow_real_exp]
  simp only [gammaDensityC, gammaDensity, Complex.ofReal_mul, Complex.real_smul]
  have he : ((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I =
      (t : ℂ) * ((1 - (2 * Real.pi * ξ : ℝ) * Complex.I) - 1) := by push_cast; ring
  push_cast at he ⊢
  rw [he]
  ring

/-- Exact Fourier integral, in Mathlib's frequency convention. -/
theorem fourier_gammaDensity (ξ : ℝ) :
    𝓕 gammaDensityC ξ = Complex.Gamma (1 - (2 * Real.pi * ξ : ℝ) * Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul, gammaDensity_fourier_integrand]
  rw [integral_comp_exp (fun x : ℝ => (Real.exp (-x) : ℂ) *
    (x : ℂ) ^ ((1 - (2 * Real.pi * ξ : ℝ) * Complex.I) - 1))]
  symm
  exact Complex.Gamma_eq_integral (by simp)

/-- The Fourier transform has no zeros. -/
theorem fourier_gammaDensity_ne_zero (ξ : ℝ) : 𝓕 gammaDensityC ξ ≠ 0 := by
  rw [fourier_gammaDensity]
  exact Complex.Gamma_ne_zero_of_re_pos (by simp)

end Singularity
