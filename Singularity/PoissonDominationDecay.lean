import Singularity.FiniteBoundaryChart
import Singularity.VisualPoissonRay
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Exponential decay forced by domination of visual measures

If t times the visual measure at z is bounded by B times visual measure at i,
then t is at most 2 B exp(-d(i,z)). The proof compares explicit Poisson
densities and the hyperbolic distance formula. The factor two avoids needing
an exact maximizer of the compact-boundary Poisson kernel.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical ENNReal UpperHalfPlane

namespace Singularity

/-- A quadratic coefficient whose multiples of every square are bounded is nonpositive. -/
theorem nonpos_of_mul_sq_bounded (a b : ℝ) (h : ∀ t : ℝ, a * t ^ 2 ≤ b) : a ≤ 0 := by
  by_contra ha
  have ha : 0 < a := lt_of_not_ge ha
  let u := (max b 0 + 1) / a
  have hu : 0 ≤ u := le_of_lt (div_pos (by positivity) ha)
  have ht := h (Real.sqrt u)
  rw [Real.sq_sqrt hu] at ht
  have he : a * u = max b 0 + 1 := by dsimp [u]; field_simp
  rw [he] at ht
  linarith [le_max_left b 0]

/-- A visual-measure domination gives the corresponding everywhere polynomial Poisson inequality. -/
theorem poisson_domination_quadratic (z : ℍ) (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hdom : ENNReal.ofReal t • poissonBoundaryMeasure z ≤
      ENNReal.ofReal B • poissonBoundaryMeasure UpperHalfPlane.I) :
    ∀ ξ : ℝ, t * z.im * (1 + ξ ^ 2) ≤ B * ((ξ - z.re) ^ 2 + z.im ^ 2) := by
  have hd : volume.withDensity (fun ξ => ENNReal.ofReal (t * halfPlanePoisson z.re z.im ξ)) ≤
      volume.withDensity (fun ξ => ENNReal.ofReal (B * halfPlanePoisson 0 1 ξ)) := by
    simpa only [poissonBoundaryMeasure, smul_halfPlanePoissonMeasure _ _ ht,
      smul_halfPlanePoissonMeasure _ _ hB, UpperHalfPlane.I_re, UpperHalfPlane.I_im] using hdom
  have hae := ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    ((measurable_const.mul (measurable_halfPlanePoisson z.re z.im)).ennreal_ofReal)
    (g := fun ξ => ENNReal.ofReal (B * halfPlanePoisson 0 1 ξ))
    (fun E hE _ => by simpa only [withDensity_apply _ hE, Pi.mul_apply] using hd E)
  have hquad : ∀ᵐ ξ ∂volume, t * z.im * (1 + ξ ^ 2) ≤ B * ((ξ - z.re) ^ 2 + z.im ^ 2) := by
    filter_upwards [hae] with ξ hξ
    simp only [Pi.mul_apply] at hξ
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hξ
    simp only [ENNReal.toReal_ofReal (mul_nonneg ht (halfPlanePoisson_nonneg z.re z.im_pos ξ)),
      ENNReal.toReal_ofReal (mul_nonneg hB (halfPlanePoisson_nonneg 0 (by norm_num : (0 : ℝ) < 1) ξ))] at hr
    unfold halfPlanePoisson at hr
    simp only [sub_zero, one_pow, ← mul_div_assoc, mul_one] at hr
    have h1 : 0 < Real.pi * ((ξ - z.re) ^ 2 + z.im ^ 2) := by positivity
    have h2 : 0 < Real.pi * (ξ ^ 2 + 1) := by positivity
    have hh := (div_le_div_iff₀ h1 h2).mp hr
    apply (mul_le_mul_iff_left₀ Real.pi_pos).mp
    nlinarith only [hh]
  have hc : IsClosed {ξ : ℝ | t * z.im * (1 + ξ ^ 2) ≤ B * ((ξ - z.re) ^ 2 + z.im ^ 2)} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have he := (Measure.dense_of_ae hquad).closure_eq
  intro ξ
  exact hc.closure_subset (he.symm ▸ mem_univ ξ)

/-- Poisson domination has exponential hyperbolic decay in its scalar coefficient. -/
theorem poisson_domination_exp_decay (z : ℍ) (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hdom : ENNReal.ofReal t • poissonBoundaryMeasure z ≤
      ENNReal.ofReal B • poissonBoundaryMeasure UpperHalfPlane.I) :
    t ≤ 2 * B * Real.exp (-dist UpperHalfPlane.I z) := by
  have hq := poisson_domination_quadratic z t B ht hB hdom
  have hy : t * z.im ≤ B := by
    have hcoef := nonpos_of_mul_sq_bounded (t * z.im - B)
      (B * (z.re ^ 2 + z.im ^ 2) - t * z.im) (fun ξ => by
        have h1 := hq ξ
        have h2 := hq (-ξ)
        nlinarith only [h1,h2])
    linarith
  have hx : t * (1 + z.re ^ 2) ≤ B * z.im := by
    have h := hq z.re
    simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at h
    nlinarith [z.im_pos]
  have hc := UpperHalfPlane.cosh_dist' UpperHalfPlane.I z
  rw [Real.cosh_eq] at hc
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, zero_sub, neg_sq, one_pow, mul_one] at hc
  have he : Real.exp (dist UpperHalfPlane.I z) * z.im ≤ z.re ^ 2 + z.im ^ 2 + 1 := by
    have hcle := (eq_div_iff (show (2 : ℝ) * z.im ≠ 0 by positivity)).mp hc
    nlinarith [Real.exp_pos (-dist UpperHalfPlane.I z), z.im_pos]
  have hte : t * Real.exp (dist UpperHalfPlane.I z) ≤ 2 * B := by
    have h1 := mul_le_mul_of_nonneg_left he ht
    have h2 := mul_le_mul_of_nonneg_right hy z.im_pos.le
    nlinarith [z.im_pos]
  have hf := mul_le_mul_of_nonneg_right hte (Real.exp_pos (-dist UpperHalfPlane.I z)).le
  simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using hf

/-- The same decay estimate holds on the full compact projective boundary. -/
theorem compactPoisson_domination_exp_decay (z : ℍ) (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hdom : ENNReal.ofReal t • compactPoissonMeasure z ≤
      ENNReal.ofReal B • compactPoissonMeasure UpperHalfPlane.I) :
    t ≤ 2 * B * Real.exp (-dist UpperHalfPlane.I z) := by
  apply poisson_domination_exp_decay z t B ht hB
  have h := finiteBoundaryMeasure_poisson_bound
    (ENNReal.ofReal t • compactPoissonMeasure z) UpperHalfPlane.I B hdom
  rw [finiteBoundaryMeasure, Measure.map_smul _ measurable_finiteBoundaryCoordinate.aemeasurable] at h
  change ENNReal.ofReal t • finiteBoundaryMeasure (compactRealMeasure (poissonBoundaryMeasure z)) ≤ _ at h
  rwa [finiteBoundaryMeasure_compactRealMeasure] at h

end Singularity
