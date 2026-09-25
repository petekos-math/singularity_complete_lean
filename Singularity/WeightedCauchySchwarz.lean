import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weighted Cauchy–Schwarz for the boundary densities

The weight is nonnegative and integrable. The function is complex-valued;
this is the estimate needed before summing the analysis coefficients.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Singularity

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The L² norm of a raw function, expressed without choosing a representative. -/
theorem toL2_norm_sq {f : X → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (hf.toLp f) (hf.toLp f))]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, ← norm_sq_eq_re_inner (𝕜 := ℂ)]

/-- Cauchy–Schwarz for complex functions represented in L². -/
theorem integral_inner_sq_le {f g : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, inner ℂ (f x) (g x) ∂μ‖ ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hi : inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℂ (f x) (g x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_inner_le_norm (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)) 2
  rwa [hi, mul_pow, toL2_norm_sq hf, toL2_norm_sq hg] at h

/-- Weighted Cauchy–Schwarz, with all integrability hypotheses explicit. -/
theorem weighted_cauchy_schwarz {f : X → ℂ} {k : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (hk : Integrable k μ)
    (hk_nonneg : ∀ x, 0 ≤ k x)
    (hfk : Integrable (fun x => ‖f x‖ ^ 2 * k x) μ) :
    ‖∫ x, (k x : ℂ) * f x ∂μ‖ ^ 2 ≤
      (∫ x, k x ∂μ) * (∫ x, ‖f x‖ ^ 2 * k x ∂μ) := by
  let s : X → ℂ := fun x => (Real.sqrt (k x) : ℂ)
  have hs_meas : AEStronglyMeasurable s μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_sqrt.comp_aestronglyMeasurable hk.aestronglyMeasurable)
  have hs_sq (x : X) : ‖s x‖ ^ 2 = k x := by
    simp only [s, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sq_sqrt (hk_nonneg x)
  have hs : MemLp s 2 μ :=
    (memLp_two_iff_integrable_sq_norm hs_meas).mpr (by simpa only [hs_sq] using hk)
  have hsf_sq (x : X) : ‖s x * f x‖ ^ 2 = ‖f x‖ ^ 2 * k x := by
    rw [norm_mul, mul_pow, hs_sq, mul_comm]
  have hsf : MemLp (fun x => s x * f x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (hs_meas.mul hf)).mpr
      (by simpa only [Pi.mul_apply, hsf_sq] using hfk)
  have hi (x : X) : inner ℂ (s x) (s x * f x) = (k x : ℂ) * f x := by
    simp only [s, RCLike.inner_apply, Complex.conj_ofReal]
    calc
      _ = (Real.sqrt (k x) : ℂ) ^ 2 * f x := by ring
      _ = _ := by rw [← Complex.ofReal_pow, Real.sq_sqrt (hk_nonneg x)]
  simpa only [hi, hs_sq, hsf_sq] using integral_inner_sq_le hs hsf

/-- If each density has total mass at most one, one factor disappears. -/
theorem weighted_cauchy_schwarz_mass_le_one {f : X → ℂ} {k : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (hk : Integrable k μ)
    (hk_nonneg : ∀ x, 0 ≤ k x) (hkmass : ∫ x, k x ∂μ ≤ 1)
    (hfk : Integrable (fun x => ‖f x‖ ^ 2 * k x) μ) :
    ‖∫ x, (k x : ℂ) * f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 * k x ∂μ := by
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2 * k x ∂μ :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hk_nonneg x))
  exact (weighted_cauchy_schwarz hf hk hk_nonneg hfk).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hkmass hnonneg)

end Singularity
