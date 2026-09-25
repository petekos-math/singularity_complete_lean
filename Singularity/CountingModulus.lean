import Singularity.CountingSequence
import Singularity.MarkovAdjoint

/-!
# Pointwise modulus in counting-measure L²

The modulus is an actual L² vector with the same norm. It commutes with right
translations and dominates absolute inner products. Positivity of the Markov
weights then controls the full complex quadratic form by its value on the
nonnegative modulus vector.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate Classical

namespace Singularity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

/-- The complex-valued pointwise modulus belongs to the same counting L² space. -/
theorem memLp_counting_modulus (f : GroupL2 X) :
    MemLp (fun x => (‖f x‖ : ℂ)) 2 Measure.count := by
  apply mem_countingL2_of_bound (counting_square_summable f)
  intro x
  simp

/-- Modulus as a concrete vector in the complex Hilbert space. -/
def countingModulus (f : GroupL2 X) : GroupL2 X :=
  (memLp_counting_modulus f).toLp (fun x => (‖f x‖ : ℂ))

theorem countingModulus_apply (f : GroupL2 X) (x : X) : countingModulus f x = (‖f x‖ : ℂ) :=
  Measure.ae_count_iff.mp (memLp_counting_modulus f).coeFn_toLp x

/-- Taking pointwise modulus preserves the Hilbert norm. -/
theorem countingModulus_norm (f : GroupL2 X) : ‖countingModulus f‖ = ‖f‖ := by
  have hs : ‖countingModulus f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [counting_norm_sq, counting_norm_sq]
    simp only [countingModulus_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  nlinarith [norm_nonneg f, norm_nonneg (countingModulus f)]

/-- The modulus pairing is the integral of the absolute pointwise pairing. -/
theorem countingModulus_inner (f g : GroupL2 X) :
    (inner ℂ (countingModulus f) (countingModulus g)).re =
      ∫ x, ‖inner ℂ (f x) (g x)‖ ∂Measure.count := by
  change (RCLike.re : ℂ → ℝ) (inner ℂ (countingModulus f) (countingModulus g)) = _
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) (countingModulus f) (countingModulus g))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [countingModulus_apply]

/-- Complex inner products are dominated by the positive modulus pairing. -/
theorem countingModulus_inner_bound (f g : GroupL2 X) :
    ‖inner ℂ f g‖ ≤ (inner ℂ (countingModulus f) (countingModulus g)).re := by
  rw [countingModulus_inner, L2.inner_def]
  exact norm_integral_le_integral_norm _

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ] [Countable Γ]

/-- Modulus commutes with the actual right-translation representation. -/
theorem countingModulus_rightTranslation (g : Γ) (f : GroupL2 Γ) :
    countingModulus (rightTranslation g f) = rightTranslation g (countingModulus f) := by
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro x
  rw [countingModulus_apply,
    Measure.ae_count_iff.mp (rightTranslation_apply_ae g f) x,
    Measure.ae_count_iff.mp (rightTranslation_apply_ae g (countingModulus f)) x,
    ]
  exact (countingModulus_apply f (x * g)).symm

omit [MeasurableSingletonClass Γ] [Countable Γ] in
/-- Exact real-part formula for the Markov quadratic form. -/
theorem rightMarkov_inner_re (s : Finset Γ) (μ : Γ → ℝ) (f : GroupL2 Γ) :
    (inner ℂ (rightMarkov s μ f) f).re =
      ∑ g ∈ s, μ g * (inner ℂ (rightTranslation g f) f).re := by
  simp only [rightMarkov, _root_.sum_apply, _root_.smul_apply,
    LinearIsometry.coe_toContinuousLinearMap, sum_inner, inner_smul_left, Complex.conj_ofReal,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Nonnegative jump weights allow control of the complex quadratic form by modulus. -/
theorem rightMarkov_quadratic_modulus_bound (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (f : GroupL2 Γ) :
    ‖inner ℂ (rightMarkov s μ f) f‖ ≤
      (inner ℂ (rightMarkov s μ (countingModulus f)) (countingModulus f)).re := by
  rw [rightMarkov_inner_re]
  have he : inner ℂ (rightMarkov s μ f) f =
      ∑ g ∈ s, (μ g : ℂ) * inner ℂ (rightTranslation g f) f := by
    simp only [rightMarkov, _root_.sum_apply, _root_.smul_apply,
      LinearIsometry.coe_toContinuousLinearMap, sum_inner, inner_smul_left, Complex.conj_ofReal]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g hg
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ g hg)]
  apply mul_le_mul_of_nonneg_left _ (hμ g hg)
  simpa only [countingModulus_rightTranslation] using countingModulus_inner_bound (rightTranslation g f) f

end Singularity
