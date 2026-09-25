import Singularity.CountingModulus
import Singularity.QuadraticSpectralGap

/-!
# Translation energy and the non-lazy spectral gap

The exact Dirichlet energy identity and pointwise modulus control show that a
uniform positive translation-energy bound forces spectral radius strictly below
one. No identity jump, symmetry, or operator-norm gap is assumed.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]

/-- The weighted squared displacement under the support translations. -/
def markovEnergy (s : Finset Γ) (μ : Γ → ℝ) (f : GroupL2 Γ) : ℝ :=
  ∑ g ∈ s, μ g * ‖rightTranslation g f - f‖ ^ 2

/-- Translation energy is nonnegative for a probability jump law. -/
theorem markovEnergy_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (f : GroupL2 Γ) : 0 ≤ markovEnergy s μ f :=
  Finset.sum_nonneg (fun g hg => mul_nonneg (hμ g hg) (sq_nonneg _))

/-- Translation energy is homogeneous of degree two. -/
theorem markovEnergy_smul (s : Finset Γ) (μ : Γ → ℝ) (a : ℂ) (f : GroupL2 Γ) :
    markovEnergy s μ (a • f) = ‖a‖ ^ 2 * markovEnergy s μ f := by
  simp only [markovEnergy, map_smul, ← smul_sub, norm_smul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

variable [MeasurableSingletonClass Γ] [Countable Γ]

omit [MeasurableSingletonClass Γ] [Countable Γ] in
/-- The exact real-part Dirichlet identity for the possibly nonsymmetric walk. -/
theorem markovEnergy_identity (s : Finset Γ) (μ : Γ → ℝ)
    (hmass : ∑ g ∈ s, μ g = 1) (f : GroupL2 Γ) :
    markovEnergy s μ f = 2 * (‖f‖ ^ 2 - (inner ℂ (rightMarkov s μ f) f).re) := by
  rw [rightMarkov_inner_re]
  unfold markovEnergy
  simp_rw [norm_sub_sq (𝕜 := ℂ), rightTranslation_norm]
  calc
    _ = ∑ g ∈ s, (2 * μ g * ‖f‖ ^ 2 - 2 * (μ g * (inner ℂ (rightTranslation g f) f).re)) := by
      apply Finset.sum_congr rfl
      intro g _
      change μ g * (‖f‖ ^ 2 - 2 * (inner ℂ (rightTranslation g f) f).re + ‖f‖ ^ 2) = _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, hmass]
      ring

/-- A uniform positive energy bound gives a strict quadratic bound on the Markov operator. -/
theorem rightMarkov_quadratic_bound_of_energy (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (c : ℝ) (henergy : ∀ f : GroupL2 Γ, c * ‖f‖ ^ 2 ≤ markovEnergy s μ f)
    (f : GroupL2 Γ) :
    ‖inner ℂ (rightMarkov s μ f) f‖ ≤ max (1 - c / 2) 0 * ‖f‖ ^ 2 := by
  apply (rightMarkov_quadratic_modulus_bound s μ hμ f).trans
  have h := henergy (countingModulus f)
  rw [markovEnergy_identity s μ hmass, countingModulus_norm] at h
  have hbound : (inner ℂ (rightMarkov s μ (countingModulus f)) (countingModulus f)).re ≤
      (1 - c / 2) * ‖f‖ ^ 2 := by nlinarith
  exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

/-- The energy criterion proves the spectral gap of the original, non-lazy Markov operator. -/
theorem rightMarkov_spectral_gap_of_energy (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    {c : ℝ} (hc : 0 < c)
    (henergy : ∀ f : GroupL2 Γ, c * ‖f‖ ^ 2 ≤ markovEnergy s μ f) :
    spectralRadius ℂ (rightMarkov s μ) < 1 := by
  apply spectralRadius_lt_one_of_quadratic_bound _ (le_max_right _ _)
    (max_lt (by linarith : 1 - c / 2 < 1) zero_lt_one)
  exact rightMarkov_quadratic_bound_of_energy s μ hμ hmass c henergy

end Singularity
