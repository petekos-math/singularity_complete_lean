import Singularity.GammaDensity

/-!
# The Liouville kernel as an autocorrelation

This identifies its ordinary Fourier transform with a product of Gamma values,
which is nonzero at every real frequency.
-/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform Convolution ComplexConjugate

namespace Singularity

/-- The logarithmic-coordinate Liouville kernel, written using exponentials. -/
def liouvilleKernel (t : ℝ) : ℝ := Real.exp (-t) / (1 + Real.exp (-t)) ^ 2

def liouvilleKernelC (t : ℝ) : ℂ := liouvilleKernel t

/-- The familiar hyperbolic-secant expression for the same kernel. -/
theorem liouvilleKernel_eq_cosh (t : ℝ) :
    liouvilleKernel t = 1 / (4 * Real.cosh (t / 2) ^ 2) := by
  have he : Real.exp (-t) = (Real.exp (t / 2))⁻¹ ^ 2 := by
    rw [← Real.exp_neg, pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold liouvilleKernel
  rw [he, Real.cosh_eq, Real.exp_neg]
  have hp := Real.exp_pos (t / 2)
  field_simp
  ring

/-- The identity which permits the substitution x = exp(s). -/
theorem gammaDensity_autocorrelation_integrand (t s : ℝ) :
    gammaDensity s * gammaDensity (s - t) =
      Real.exp (-t) * (Real.exp s *
        (Real.exp s * Real.exp (-((1 + Real.exp (-t)) * Real.exp s)))) := by
  have he : Real.exp (s - t) = Real.exp s * Real.exp (-t) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have he' : Real.exp (-Real.exp s) * Real.exp (-(Real.exp s * Real.exp (-t))) =
      Real.exp (-((1 + Real.exp (-t)) * Real.exp s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold gammaDensity
  rw [he]
  calc
    Real.exp s * Real.exp (-Real.exp s) *
        (Real.exp s * Real.exp (-t) * Real.exp (-(Real.exp s * Real.exp (-t)))) =
        Real.exp (-t) * (Real.exp s * (Real.exp s *
          (Real.exp (-Real.exp s) * Real.exp (-(Real.exp s * Real.exp (-t)))))) := by ring
    _ = _ := by rw [he']

/-- Exact autocorrelation integral. -/
theorem gammaDensity_autocorrelation (t : ℝ) :
    ∫ s, gammaDensity s * gammaDensity (s - t) = liouvilleKernel t := by
  simp_rw [gammaDensity_autocorrelation_integrand]
  rw [integral_const_mul]
  have hs := integral_comp_exp
    (fun x : ℝ => x * Real.exp (-((1 + Real.exp (-t)) * x)))
  simp only [smul_eq_mul] at hs
  rw [hs]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2)
    (by norm_num) (r := 1 + Real.exp (-t)) (by positivity)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, Real.Gamma_two, mul_one] at hi
  rw [hi]
  simp [liouvilleKernel, div_eq_mul_inv]

/-- The Liouville kernel is the convolution of g with its reflection. -/
theorem liouvilleKernel_eq_convolution : liouvilleKernelC =
    gammaDensityC ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t => gammaDensityC (-t)) := by
  funext t
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply', gammaDensityC]
  have hsub (s : ℝ) : -(t - s) = s - t := by ring
  simp_rw [hsub, ← Complex.ofReal_mul]
  exact (congrArg (fun x : ℝ => (x : ℂ)) (gammaDensity_autocorrelation t)).symm.trans
    (integral_ofReal (f := fun s => gammaDensity s * gammaDensity (s - t))).symm

/-- This also proves absolute integrability of the actual kernel. -/
theorem liouvilleKernelC_integrable : Integrable liouvilleKernelC := by
  rw [liouvilleKernel_eq_convolution]
  exact gammaDensityC_integrable.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) gammaDensityC_integrable.comp_neg

/-- Reflection reverses the frequency in the ordinary Fourier transform. -/
theorem fourier_reflected_gammaDensity (ξ : ℝ) :
    𝓕 (fun t => gammaDensityC (-t)) ξ = 𝓕 gammaDensityC (-ξ) := by
  exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) gammaDensityC ξ

/-- The actual Fourier transform of the Liouville kernel. -/
theorem fourier_liouvilleKernel_gamma (ξ : ℝ) :
    𝓕 liouvilleKernelC ξ =
      Complex.Gamma (1 - (2 * Real.pi * ξ : ℝ) * Complex.I) *
      Complex.Gamma (1 + (2 * Real.pi * ξ : ℝ) * Complex.I) := by
  rw [liouvilleKernel_eq_convolution,
    Real.fourier_mul_convolution_eq gammaDensityC_integrable gammaDensityC_integrable.comp_neg,
    fourier_reflected_gammaDensity, fourier_gammaDensity, fourier_gammaDensity]
  congr 2
  push_cast
  ring

/-- Nonvanishing follows from Mathlib's Gamma nonvanishing theorem. -/
theorem fourier_liouvilleKernel_ne_zero (ξ : ℝ) : 𝓕 liouvilleKernelC ξ ≠ 0 := by
  rw [fourier_liouvilleKernel_gamma]
  exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp))
    (Complex.Gamma_ne_zero_of_re_pos (by simp))

/-- The transform is a positive squared absolute value. -/
theorem fourier_liouvilleKernel_norm_sq (ξ : ℝ) :
    𝓕 liouvilleKernelC ξ = (‖Complex.Gamma (1 - (2 * Real.pi * ξ : ℝ) * Complex.I)‖ : ℂ) ^ 2 := by
  rw [fourier_liouvilleKernel_gamma]
  have hc : (1 + (2 * Real.pi * ξ : ℝ) * Complex.I : ℂ) =
      conj (1 - (2 * Real.pi * ξ : ℝ) * Complex.I) := by
    simp only [map_sub, map_mul, map_one, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hc, Complex.Gamma_conj, Complex.mul_conj']

/-- Euler's reflection formula evaluates the Gamma product explicitly. -/
theorem gamma_product_liouvilleMultiplier (ω : ℝ) :
    Complex.Gamma (1 - (ω : ℂ) * Complex.I) *
      Complex.Gamma (1 + (ω : ℂ) * Complex.I) = (liouvilleMultiplier ω : ℂ) := by
  by_cases hω : ω = 0
  · simp [hω, liouvilleMultiplier]
  have hz : (ω : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) Complex.I_ne_zero
  have hs : Real.sinh (Real.pi * ω) ≠ 0 := by
    simpa using mul_ne_zero Real.pi_ne_zero hω
  have hsc : (Real.sinh (Real.pi * ω) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [show (1 + (ω : ℂ) * Complex.I) = (ω : ℂ) * Complex.I + 1 by ring,
    Complex.Gamma_add_one _ hz]
  calc
    Complex.Gamma (1 - (ω : ℂ) * Complex.I) *
        ((ω : ℂ) * Complex.I * Complex.Gamma ((ω : ℂ) * Complex.I)) =
        (ω : ℂ) * Complex.I * (Complex.Gamma ((ω : ℂ) * Complex.I) *
          Complex.Gamma (1 - (ω : ℂ) * Complex.I)) := by ring
    _ = (ω : ℂ) * Complex.I * (Real.pi / Complex.sin (Real.pi * ((ω : ℂ) * Complex.I))) := by
      rw [Complex.Gamma_mul_Gamma_one_sub]
    _ = (liouvilleMultiplier ω : ℂ) := by
      rw [← mul_assoc (Real.pi : ℂ), Complex.sin_mul_I,
        ← Complex.ofReal_mul, ← Complex.ofReal_sinh]
      simp only [liouvilleMultiplier, ite_eq_right hω, Complex.ofReal_div, Complex.ofReal_mul]
      field_simp

/-- The exact hyperbolic-sine multiplier, including its value at zero. -/
theorem fourier_liouvilleKernel (ξ : ℝ) :
    𝓕 liouvilleKernelC ξ = (liouvilleMultiplier (2 * Real.pi * ξ) : ℂ) := by
  rw [fourier_liouvilleKernel_gamma, gamma_product_liouvilleMultiplier]

end Singularity
