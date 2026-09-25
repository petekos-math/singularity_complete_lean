import Singularity.Operators
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Spectral control by a quadratic-form bound

The modulus of the quadratic form, rather than the operator norm, controls the
spectrum. Lax--Milgram/coercivity supplies the resolvent outside the quadratic
bound. This works for non-self-adjoint operators and is suitable for the
non-lazy right Markov operator.
-/

noncomputable section
open scoped InnerProductSpace

namespace Singularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A quadratic bound gives coercivity of every normalized resolvent. -/
theorem quadratic_bound_coercive (P : E →L[ℂ] E) (q : ℝ)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) (a : ℂ) :
    Coercive (1 - a • P) (1 - ‖a‖ * q) := by
  intro v
  have h := mul_le_mul_of_nonneg_left (hP v) (norm_nonneg a)
  have hr := Complex.re_le_norm (inner ℂ (a • P v) v)
  rw [inner_smul_left, norm_mul, Complex.norm_conj] at hr
  change (1 - ‖a‖ * q) * ‖v‖ ^ 2 ≤
    (inner ℂ (v - a • P v) v).re
  have hself : (inner ℂ v v).re = ‖v‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  rw [inner_sub_left, Complex.sub_re, hself, inner_smul_left]
  nlinarith

/-- Coercivity makes the normalized resolvent an invertible bounded operator. -/
theorem quadratic_bound_isUnit (P : E →L[ℂ] E) (q : ℝ)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) (a : ℂ)
    (ha : ‖a‖ * q < 1) : IsUnit (1 - a • P) := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ((quadratic_bound_coercive P q hP a).equiv (by linarith)).bijective

/-- Every complex number outside the quadratic bound lies in the resolvent set. -/
theorem quadratic_bound_resolvent (P : E →L[ℂ] E) {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) {k : ℂ} (hk : q < ‖k‖) :
    k ∈ resolventSet ℂ P := by
  have hk0 : k ≠ 0 := norm_pos_iff.mp (hq.trans_lt hk)
  have hunit := quadratic_bound_isUnit P q hP k⁻¹ (by
    rw [norm_inv, inv_mul_lt_iff₀ (hq.trans_lt hk), mul_one]
    exact hk)
  apply spectrum.mem_resolventSet_iff.mpr
  have he : algebraMap ℂ (E →L[ℂ] E) k - P = k • (1 - k⁻¹ • P) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hk0, one_smul,
      Algebra.algebraMap_eq_smul_one]
  rw [he]
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  obtain ⟨hinj, hsurj⟩ := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  constructor
  · intro v w hvw
    apply hinj
    exact (smul_right_injective _ hk0) hvw
  · intro w
    obtain ⟨v, hv⟩ := hsurj (k⁻¹ • w)
    refine ⟨v, ?_⟩
    change k • ((1 - k⁻¹ • P) v) = w
    rw [hv, smul_smul, mul_inv_cancel₀ hk0, one_smul]

/-- Every spectral value is bounded by the modulus bound on the quadratic form. -/
theorem quadratic_bound_spectrum (P : E →L[ℂ] E) {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) {k : ℂ}
    (hk : k ∈ spectrum ℂ P) : ‖k‖ ≤ q := by
  by_contra h
  exact hk (quadratic_bound_resolvent P hq hP (lt_of_not_ge h))

/-- The quadratic bound controls the full operator spectral radius. -/
theorem spectralRadius_le_of_quadratic_bound (P : E →L[ℂ] E) {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) :
    spectralRadius ℂ P ≤ ENNReal.ofReal q := by
  rw [spectralRadius_eq_of_unital]
  apply iSup₂_le
  intro k hk
  simpa only [ofReal_norm, enorm] using
    ENNReal.ofReal_le_ofReal (quadratic_bound_spectrum P hq hP hk)

/-- A strict quadratic bound proves the spectral gap without a norm-gap assumption. -/
theorem spectralRadius_lt_one_of_quadratic_bound (P : E →L[ℂ] E) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) : spectralRadius ℂ P < 1 :=
  (spectralRadius_le_of_quadratic_bound P hq hP).trans_lt
    (by simpa using ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1) |>.mpr hq1)

end Singularity
