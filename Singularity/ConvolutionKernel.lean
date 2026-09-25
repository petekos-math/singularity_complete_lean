import Singularity.ConvolutionMultiplier
import Singularity.WeightedCauchySchwarz

/-!
# The physical-kernel formula for L² convolution

We identify the Bochner convolution with the expected double-integral pairing.
Absolute integrability of the double integral is proved using Cauchy–Schwarz.
-/

noncomputable section
open MeasureTheory

namespace Singularity

/-- The integral of the product of the absolute values satisfies Cauchy–Schwarz. -/
theorem integral_norm_mul_norm_L2 (f g : RealLineL2) :
    ∫ t, ‖f t‖ * ‖g t‖ ≤ ‖f‖ * ‖g‖ := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using Lp.memLp f) (by simpa using Lp.memLp g)
  have hf : ∫ t, ‖f t‖ ^ 2 = ‖f‖ ^ 2 := by
    simpa only [Lp.toLp_coeFn] using (toL2_norm_sq (Lp.memLp f)).symm
  have hg : ∫ t, ‖g t‖ ^ 2 = ‖g‖ ^ 2 := by
    simpa only [Lp.toLp_coeFn] using (toL2_norm_sq (Lp.memLp g)).symm
  simpa only [Real.rpow_two, hf, hg, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg f), Real.sqrt_sq (norm_nonneg g)] using h

/-- The translated inner-product density has a uniform L¹ bound. -/
theorem integral_norm_inner_translation_le (u : ℝ) (h f : RealLineL2) :
    ∫ s, ‖inner ℂ (h s) (f (s - u))‖ ≤ ‖h‖ * ‖f‖ := by
  calc
    ∫ s, ‖inner ℂ (h s) (f (s - u))‖ =
        ∫ s, ‖h s‖ * ‖realTranslation u f s‖ := by
      apply integral_congr_ae
      filter_upwards [realTranslation_apply_ae u f] with s hs
      rw [hs]
      simp [RCLike.inner_apply, mul_comm]
    _ ≤ ‖h‖ * ‖realTranslation u f‖ := integral_norm_mul_norm_L2 h _
    _ = ‖h‖ * ‖f‖ := by rw [(realTranslation u).norm_map]

/-- Joint integrability, including the L² inputs that need not belong to L¹. -/
theorem convolution_kernel_fubini {k : ℝ → ℂ} (hk : Integrable k) (h f : RealLineL2) :
    Integrable (fun p : ℝ × ℝ => k p.1 * inner ℂ (h p.2) (f (p.2 - p.1)))
      (volume.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => k p.1 * inner ℂ (h p.2) (f (p.2 - p.1))) (volume.prod volume) := by
    apply hk.aestronglyMeasurable.comp_fst.mul
    exact ((Lp.stronglyMeasurable h).comp_measurable measurable_snd).aestronglyMeasurable.inner
      ((Lp.stronglyMeasurable f).comp_measurable
        (measurable_snd.sub measurable_fst)).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun u => by
      apply ((L2.integrable_inner (𝕜 := ℂ) h (realTranslation u f)).const_mul (k u)).congr
      filter_upwards [realTranslation_apply_ae u f] with s hs
      rw [hs])
  · apply (hk.norm.mul_const (‖h‖ * ‖f‖)).mono' hm.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      simp_rw [norm_mul]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_norm_inner_translation_le u h f) (norm_nonneg _))

/-- The weak physical-space kernel formula for actual L² convolution. -/
theorem convolutionL2_inner_kernel (k : ℝ → ℂ) (hk : Integrable k) (f h : RealLineL2) :
    inner ℂ h (convolutionL2 k hk f) =
      ∫ s, ∫ t, k (s - t) * inner ℂ (h s) (f t) := by
  rw [convolutionL2_inner]
  have hfub := integral_integral_swap
    (f := fun u s : ℝ => k u * inner ℂ (h s) (f (s - u)))
    (convolution_kernel_fubini hk h f)
  calc
    ∫ u, k u * inner ℂ h (realTranslation u f) =
        ∫ u, ∫ s, k u * inner ℂ (h s) (f (s - u)) := by
      congr 1
      funext u
      rw [L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [realTranslation_apply_ae u f] with s hs
      rw [hs]
    _ = ∫ s, ∫ u, k u * inner ℂ (h s) (f (s - u)) := hfub
    _ = ∫ s, ∫ t, k (s - t) * inner ℂ (h s) (f t) := by
      congr 1
      funext s
      rw [← integral_sub_left_eq_self
        (fun u => k u * inner ℂ (h s) (f (s - u))) volume s]
      simp only [sub_sub_cancel]

end Singularity
