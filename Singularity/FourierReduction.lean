import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Verified pieces of the Fourier contradiction

The finite-dimensional kernel lemma in this module is pointwise.
`FrequencyKernel.lean` now proves measurable unit-vector selection for the actual
frequency matrix. `LatticeObstruction.lean` completes the finite-band/translation
argument. The abstract multiplier lemma here takes a multiplier identity as input;
`LiouvilleFourier.lean` and `LiouvilleOperator.lean` now prove that identity for the
actual Liouville convolution. The geometric current factorization is still missing.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Singularity

/-- Rank-nullity, applied to the `N × (N+1)` frequency matrix. -/
theorem frequency_matrix_has_kernel {N : ℕ}
    (B : (Fin (N + 1) → ℂ) →ₗ[ℂ] (Fin N → ℂ)) :
    ∃ v, v ≠ 0 ∧ B v = 0 := by
  have hdim : Module.finrank ℂ (Fin N → ℂ) <
      Module.finrank ℂ (Fin (N + 1) → ℂ) := by
    simp only [Module.finrank_pi, Fintype.card_fin]
    exact Nat.lt_succ_self N
  obtain ⟨v, hv, hn⟩ := B.ker.ne_bot_iff.mp
    (LinearMap.ker_ne_bot_of_finrank_lt hdim)
  exact ⟨v, hn, hv⟩

/-- The continuous extension at zero of the expected (angular-frequency)
convolution multiplier, without its positive scalar prefactor. -/
def liouvilleMultiplier (ω : ℝ) : ℝ :=
  if ω = 0 then 1 else Real.pi * ω / Real.sinh (Real.pi * ω)

/-- This establishes positivity of the expression, not its identification
with a Fourier transform. -/
theorem liouvilleMultiplier_pos (ω : ℝ) : 0 < liouvilleMultiplier ω := by
  unfold liouvilleMultiplier
  split_ifs with h
  · norm_num
  · rcases lt_or_gt_of_ne h with hneg | hpos
    · apply div_pos_of_neg_of_neg
      · exact mul_neg_of_pos_of_neg Real.pi_pos hneg
      · exact Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos hneg)
    · apply div_pos
      · exact mul_pos Real.pi_pos hpos
      · exact Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hpos)

abbrev RealLineL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Injectivity of an `L²` operator follows from an a.e. nonzero multiplier.
Mathlib's Fourier transform uses the `exp(-2π i x ξ)` convention. -/
theorem injective_of_fourier_multiplier
    (C : RealLineL2 →L[ℂ] RealLineL2) (m : ℝ → ℂ)
    (hm : ∀ᵐ ξ ∂volume, m ξ ≠ 0)
    (hdiag : ∀ f : RealLineL2,
      (Lp.fourierTransformₗᵢ ℝ ℂ (C f) : ℝ → ℂ) =ᵐ[volume]
        fun ξ => m ξ * (Lp.fourierTransformₗᵢ ℝ ℂ f : ℝ → ℂ) ξ) :
    Function.Injective C := by
  intro f g hfg
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  apply Lp.ext
  filter_upwards [hdiag f, hdiag g, hm] with ξ hf hg hmξ
  have hsame : (Lp.fourierTransformₗᵢ ℝ ℂ (C f) : ℝ → ℂ) ξ =
      (Lp.fourierTransformₗᵢ ℝ ℂ (C g) : ℝ → ℂ) ξ := by rw [hfg]
  rw [hf, hg] at hsame
  exact mul_left_cancel₀ hmξ hsame

/-- The sign check for the multiplier in Mathlib's frequency convention.
The factor `2π` converts angular frequency to cycles per unit length. -/
theorem liouvilleMultiplier_scaled_ne_zero {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    (↑(c * liouvilleMultiplier (2 * Real.pi * ξ)) : ℂ) ≠ 0 := by
  exact_mod_cast (mul_pos hc (liouvilleMultiplier_pos _)).ne'

section Factorization

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The final algebraic contradiction. Its hypotheses must be established
for the actual boundary analysis operators before singularity follows. -/
theorem impossible_factorization
    (C : E →L[𝕜] E) (H : E →L[𝕜] F)
    (M : F →L[𝕜] F) (L : F →L[𝕜] E)
    (hfactor : C = L.comp (M.comp H))
    (hC : Function.Injective C)
    (hH : ∃ v, v ≠ 0 ∧ H v = 0) : False := by
  obtain ⟨v, hv, hHv⟩ := hH
  apply hv
  apply hC
  simp [hfactor, hHv]

end Factorization
end Singularity
