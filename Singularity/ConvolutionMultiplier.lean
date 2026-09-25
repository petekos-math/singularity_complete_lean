import Singularity.L2Convolution

/-!
# The L¹–L² convolution multiplier theorem

We prove the multiplier identity for the Bochner convolution operator. Fubini is
justified by the product of the L¹ kernel norm and an L¹ inner-product density.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace Singularity

/-- The ordinary Fourier transform of an L¹ kernel is continuous. -/
theorem integrable_fourier_continuous {k : ℝ → ℂ} (hk : Integrable k) : Continuous (𝓕 k) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hk

/-- Its uniform bound. -/
theorem integrable_fourier_norm_le {k : ℝ → ℂ} (_hk : Integrable k) (ξ : ℝ) :
    ‖𝓕 k ξ‖ ≤ ∫ t, ‖k t‖ := by
  rw [Real.fourier_real_eq]
  apply (norm_integral_le_integral_norm _).trans_eq
  simp only [Circle.norm_smul]

/-- The Fourier transform of the kernel as an L-infinity multiplier. -/
def fourierKernelLinf (k : ℝ → ℂ) (hk : Integrable k) : Lp ℂ ⊤ (volume : Measure ℝ) :=
  (memLp_top_of_bound (integrable_fourier_continuous hk).aestronglyMeasurable (∫ t, ‖k t‖)
    (Filter.Eventually.of_forall (integrable_fourier_norm_le hk))).toLp (𝓕 k)

/-- The bounded Fourier multiplier on L². -/
def fourierKernelMultiplier (k : ℝ → ℂ) (hk : Integrable k) : RealLineL2 →L[ℂ] RealLineL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 (fourierKernelLinf k hk)

theorem fourierKernelMultiplier_apply_ae (k : ℝ → ℂ) (hk : Integrable k) (f : RealLineL2) :
    (fourierKernelMultiplier k hk f : ℝ → ℂ) =ᵐ[volume] fun ξ => 𝓕 k ξ * f ξ := by
  have hm : (fourierKernelLinf k hk : ℝ → ℂ) =ᵐ[volume] 𝓕 k := MemLp.coeFn_toLp _
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (fourierKernelLinf k hk) f,
    hm] with ξ hξ hmξ
  exact hξ.trans (by rw [hmξ]; rfl)

/-- Joint continuity of the scalar phase. -/
theorem translationPhase_joint_continuous : Continuous (fun p : ℝ × ℝ => translationPhase p.1 p.2) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_fst.neg.mul continuous_snd))

/-- Integrability of the family of modulated vectors. -/
theorem modulationL2_integrable {k : ℝ → ℂ} (hk : Integrable k) (g : RealLineL2) :
    Integrable (fun t => k t • frequencyModulation t g) := by
  have h := (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
    (convolutionL2_integrable hk ((Lp.fourierTransformₗᵢ ℝ ℂ).symm g))
  simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    Function.comp_def, map_smul, fourier_realTranslation, LinearIsometryEquiv.apply_symm_apply] using h

/-- The weak scalar formula for a modulated L² vector. -/
theorem modulationL2_inner (a : ℝ) (h g : RealLineL2) :
    inner ℂ h (frequencyModulation a g) =
      ∫ ξ, translationPhase a ξ * inner ℂ (h ξ) (g ξ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [frequencyModulation_apply_ae a g] with ξ hξ
  rw [hξ]
  exact inner_smul_right _ _ _

/-- Absolute integrability of the double integral used in the multiplier proof. -/
theorem multiplier_fubini_integrable {k : ℝ → ℂ} (hk : Integrable k) (h g : RealLineL2) :
    Integrable (fun p : ℝ × ℝ => k p.1 * translationPhase p.1 p.2 * inner ℂ (h p.2) (g p.2))
      (volume.prod volume) := by
  apply (hk.norm.mul_prod (L2.integrable_inner (𝕜 := ℂ) h g).norm).mono'
  · exact (hk.aestronglyMeasurable.comp_fst.mul
      translationPhase_joint_continuous.aestronglyMeasurable).mul
        (L2.integrable_inner (𝕜 := ℂ) h g).aestronglyMeasurable.comp_snd
  · exact Filter.Eventually.of_forall (fun p => by
      simp only [norm_mul, translationPhase_norm, mul_one, le_refl])

/-- Integrating the modulation phase gives the ordinary Fourier transform. -/
theorem integral_kernel_phase (k : ℝ → ℂ) (ξ : ℝ) :
    ∫ t, k t * translationPhase t ξ = 𝓕 k ξ := by
  rw [Real.fourier_real_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    simp [translationPhase, Circle.smul_def, mul_comm])

/-- The Bochner integral of modulated vectors is multiplication by the
ordinary Fourier transform of the kernel. -/
theorem integral_modulation_eq_multiplier (k : ℝ → ℂ) (hk : Integrable k) (g : RealLineL2) :
    (∫ t, k t • frequencyModulation t g) = fourierKernelMultiplier k hk g := by
  apply ext_inner_left ℂ
  intro h
  rw [← integral_inner (modulationL2_integrable hk g)]
  simp_rw [inner_smul_right, modulationL2_inner, ← integral_const_mul]
  have hfub := integral_integral_swap
    (f := fun t ξ : ℝ => k t * translationPhase t ξ * inner ℂ (h ξ) (g ξ))
    (multiplier_fubini_integrable hk h g)
  calc
    ∫ t, ∫ ξ, k t * (translationPhase t ξ * inner ℂ (h ξ) (g ξ)) =
        ∫ ξ, ∫ t, (k t * translationPhase t ξ) * inner ℂ (h ξ) (g ξ) := by
      simpa only [mul_assoc] using hfub
    _ = ∫ ξ, 𝓕 k ξ * inner ℂ (h ξ) (g ξ) := by
      simp_rw [integral_mul_const, integral_kernel_phase]
    _ = inner ℂ h (fourierKernelMultiplier k hk g) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [fourierKernelMultiplier_apply_ae k hk g] with ξ hξ
      rw [hξ]
      exact (inner_smul_right _ _ _).symm

/-- Fourier diagonalization of convolution on all of L². -/
theorem fourier_convolutionL2 (k : ℝ → ℂ) (hk : Integrable k) (f : RealLineL2) :
    Lp.fourierTransformₗᵢ ℝ ℂ (convolutionL2 k hk f) =
      fourierKernelMultiplier k hk (Lp.fourierTransformₗᵢ ℝ ℂ f) := by
  rw [fourier_convolutionL2_integral, integral_modulation_eq_multiplier]

/-- The representative-level multiplier identity is almost everywhere. -/
theorem fourier_convolutionL2_ae (k : ℝ → ℂ) (hk : Integrable k) (f : RealLineL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ (convolutionL2 k hk f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => 𝓕 k ξ * (Lp.fourierTransformₗᵢ ℝ ℂ f : ℝ → ℂ) ξ := by
  rw [fourier_convolutionL2]
  exact fourierKernelMultiplier_apply_ae k hk _

/-- Nonvanishing of the kernel transform implies injectivity of convolution. -/
theorem convolutionL2_injective (k : ℝ → ℂ) (hk : Integrable k)
    (hnz : ∀ᵐ ξ ∂volume, 𝓕 k ξ ≠ 0) : Function.Injective (convolutionL2 k hk) :=
  injective_of_fourier_multiplier (convolutionL2 k hk) (𝓕 k) hnz (fourier_convolutionL2_ae k hk)

end Singularity
