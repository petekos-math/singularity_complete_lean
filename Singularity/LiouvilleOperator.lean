import Singularity.ConvolutionKernel
import Singularity.LiouvilleFourier
import Singularity.AnalysisKernel

/-!
# Injectivity of Liouville convolution and the analytic contradiction

The convolution operator and the lattice analysis operator are both constructed
from their kernels. Injectivity and nontrivial kernel are proved, not hypotheses.
Only the proposed factorization (and base-density conditions) remains an input.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace Singularity

/-- Convolution by c times the logarithmic Liouville kernel. -/
def liouvilleConvolution (c : ℝ) : RealLineL2 →L[ℂ] RealLineL2 :=
  (c : ℂ) • convolutionL2 liouvilleKernelC liouvilleKernelC_integrable

/-- The genuine Liouville convolution is injective for positive c. -/
theorem liouvilleConvolution_injective {c : ℝ} (hc : 0 < c) :
    Function.Injective (liouvilleConvolution c) := by
  have hbase := convolutionL2_injective liouvilleKernelC liouvilleKernelC_integrable
    (Filter.Eventually.of_forall fourier_liouvilleKernel_ne_zero)
  have hcz : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  intro f g hfg
  apply hbase
  exact smul_right_injective RealLineL2 hcz hfg

/-- The explicit multiplier identity on L², with all analytic hypotheses discharged. -/
theorem liouvilleConvolution_fourier_ae (c : ℝ) (f : RealLineL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ (liouvilleConvolution c f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (c : ℂ) * (liouvilleMultiplier (2 * Real.pi * ξ) : ℂ) *
        (Lp.fourierTransformₗᵢ ℝ ℂ f : ℝ → ℂ) ξ := by
  change (Lp.fourierTransformₗᵢ ℝ ℂ ((c : ℂ) •
    convolutionL2 liouvilleKernelC liouvilleKernelC_integrable f) : ℝ → ℂ) =ᵐ[volume] _
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (c : ℂ)
      (Lp.fourierTransformₗᵢ ℝ ℂ (convolutionL2 liouvilleKernelC liouvilleKernelC_integrable f)),
    fourier_convolutionL2_ae liouvilleKernelC liouvilleKernelC_integrable f] with ξ hsm hmul
  rw [hsm]
  change (c : ℂ) * _ = _
  rw [hmul, fourier_liouvilleKernel]
  ring

/-- A weak integral formula for the actual convolution, for arbitrary L² vectors. -/
theorem liouvilleConvolution_inner (c : ℝ) (f h : RealLineL2) :
    inner ℂ h (liouvilleConvolution c f) =
      (c : ℂ) * ∫ t, liouvilleKernelC t * inner ℂ h (realTranslation t f) := by
  rw [liouvilleConvolution, smul_apply, inner_smul_right,
    convolutionL2_inner]

/-- The operator has exactly the physical-space Liouville kernel in weak form.
The change in integration order is justified in `convolution_kernel_fubini`. -/
theorem liouvilleConvolution_inner_cosh (c : ℝ) (f h : RealLineL2) :
    inner ℂ h (liouvilleConvolution c f) =
      ∫ s, ∫ t, (c / (4 * Real.cosh ((s - t) / 2) ^ 2) : ℝ) *
        inner ℂ (h s) (f t) := by
  rw [liouvilleConvolution, smul_apply, inner_smul_right, convolutionL2_inner_kernel]
  simp_rw [← integral_const_mul]
  congr 1
  funext s
  congr 1
  funext t
  simp only [liouvilleKernelC, liouvilleKernel_eq_cosh]
  push_cast
  ring

/-- The analytic contradiction for the actual Liouville and lattice analysis
operators. The geometric current factorization is the remaining substantive input. -/
theorem impossible_liouville_factorization {J : Type*} [Fintype J]
    {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) (k : J → ℝ → ℝ) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hk : ∀ j t, 0 ≤ k j t)
    (hint : ∀ j, Integrable (k j)) (hmass : ∀ j, ∫ t, k j t ≤ 1)
    (hdecay : ∀ j t, k j t ≤ C j * Real.exp (-|t|))
    (M : SequenceL2 (ℤ × J) →L[ℂ] SequenceL2 (ℤ × J))
    (L : SequenceL2 (ℤ × J) →L[ℂ] RealLineL2)
    (hfactor : liouvilleConvolution c = L.comp (M.comp
      (translatedDensityFamily hτ k C hC hk hint hmass hdecay).analysis)) : False :=
  impossible_translated_analysis_factorization hτ k C hC hk hint hmass hdecay
    (liouvilleConvolution c) M L (liouvilleConvolution_injective hc) hfactor

end Singularity
