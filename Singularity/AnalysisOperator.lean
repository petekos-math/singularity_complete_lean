import Singularity.DominatedLimit
import Singularity.WeightedCauchySchwarz

/-!
# Constructing the boundary analysis operator

A family of nonnegative row densities, each of mass at most one, with a uniform
bound on the sum of the columns defines a bounded map L² → ℓ². The coordinate
formula is the integral in the writeup, including for complex-valued inputs.

The hypotheses are stated for chosen measurable representatives. The proof does
not assume boundedness of the analysis map, nor square summability of its output.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Singularity

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The analytic data required of the logarithmic hitting densities. The
finite-sum overlap condition follows from a bounded nonnegative column sum. -/
structure DensityFamily (X ι : Type*) [MeasurableSpace X] (μ : Measure X) where
  density : ι → X → ℝ
  nonneg : ∀ i x, 0 ≤ density i x
  integrable : ∀ i, Integrable (density i) μ
  mass_le_one : ∀ i, ∫ x, density i x ∂μ ≤ 1
  overlapBound : ℝ
  overlapBound_nonneg : 0 ≤ overlapBound
  overlap : ∀ (s : Finset ι) x, ∑ i ∈ s, density i x ≤ overlapBound

/-- Every row is bounded by the same overlap constant. -/
theorem DensityFamily.row_le (K : DensityFamily X ι μ) (i : ι) (x : X) :
    K.density i x ≤ K.overlapBound := by
  classical
  simpa using K.overlap ({i} : Finset ι) x

/-- The row density itself is square integrable. -/
theorem DensityFamily.row_memL2 (K : DensityFamily X ι μ) (i : ι) :
    MemLp (fun x => (K.density i x : ℂ)) 2 μ := by
  have hm := Complex.continuous_ofReal.comp_aestronglyMeasurable
    (K.integrable i).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply ((K.integrable i).const_mul K.overlapBound).mono' (hm.norm.pow 2)
  filter_upwards [] with x
  change ‖‖(K.density i x : ℂ)‖ ^ 2‖ ≤ K.overlapBound * K.density i x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  nlinarith [K.nonneg i x, K.row_le i x]

/-- A square-integrable input is square integrable against each row weight. -/
theorem DensityFamily.weighted_square_integrable (K : DensityFamily X ι μ)
    (f : Lp ℂ 2 μ) (i : ι) :
    Integrable (fun x => ‖f x‖ ^ 2 * K.density i x) μ := by
  have hf : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (Lp.memLp f).integrable_norm_pow (by decide)
  apply (hf.mul_const K.overlapBound).mono'
    ((Lp.aestronglyMeasurable f).norm.pow 2 |>.mul (K.integrable i).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖‖f x‖ ^ 2 * K.density i x‖ ≤ ‖f x‖ ^ 2 * K.overlapBound
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (K.nonneg i x))]
  exact mul_le_mul_of_nonneg_left (K.row_le i x) (sq_nonneg _)

/-- The coordinate functional is continuous and complex-linear. -/
def DensityFamily.coefficient (K : DensityFamily X ι μ) (i : ι) :
    Lp ℂ 2 μ →L[ℂ] ℂ :=
  innerSL ℂ ((K.row_memL2 i).toLp (fun x => (K.density i x : ℂ)))

/-- The continuous coordinate functional is the required integral. -/
theorem DensityFamily.coefficient_eq_integral (K : DensityFamily X ι μ)
    (i : ι) (f : Lp ℂ 2 μ) :
    K.coefficient i f = ∫ x, (K.density i x : ℂ) * f x ∂μ := by
  change inner ℂ ((K.row_memL2 i).toLp _) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(K.row_memL2 i).coeFn_toLp] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- The weighted Cauchy–Schwarz estimate for an individual coefficient. -/
theorem DensityFamily.coefficient_sq_le (K : DensityFamily X ι μ)
    (i : ι) (f : Lp ℂ 2 μ) :
    ‖K.coefficient i f‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 * K.density i x ∂μ := by
  rw [K.coefficient_eq_integral]
  exact weighted_cauchy_schwarz_mass_le_one (Lp.aestronglyMeasurable f)
    (K.integrable i) (K.nonneg i) (K.mass_le_one i) (K.weighted_square_integrable f i)

/-- The finite-sum Bessel bound. This proves square summability, rather than
assuming it in the type of the output. -/
theorem DensityFamily.bessel_bound (K : DensityFamily X ι μ)
    (f : Lp ℂ 2 μ) (s : Finset ι) :
    ∑ i ∈ s, ‖K.coefficient i f‖ ^ 2 ≤ K.overlapBound * ‖f‖ ^ 2 := by
  have hfint : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (Lp.memLp f).integrable_norm_pow (by decide)
  calc
    ∑ i ∈ s, ‖K.coefficient i f‖ ^ 2 ≤
        ∑ i ∈ s, ∫ x, ‖f x‖ ^ 2 * K.density i x ∂μ :=
      Finset.sum_le_sum (fun i _ => K.coefficient_sq_le i f)
    _ = ∫ x, ∑ i ∈ s, ‖f x‖ ^ 2 * K.density i x ∂μ :=
      (integral_finsetSum s (fun i _ => K.weighted_square_integrable f i)).symm
    _ ≤ ∫ x, ‖f x‖ ^ 2 * K.overlapBound ∂μ := by
      apply integral_mono_ae
        (integrable_finsetSum s (fun i _ => K.weighted_square_integrable f i))
        (hfint.mul_const K.overlapBound)
      filter_upwards [] with x
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (K.overlap s x) (sq_nonneg _)
    _ = K.overlapBound * ‖f‖ ^ 2 := by
      rw [integral_mul_const, mul_comm]
      congr 1
      have h := toL2_norm_sq (Lp.memLp f)
      simpa only [Lp.toLp_coeFn] using h.symm

/-- The coefficient vector belongs to ℓ² for every L² input. -/
theorem DensityFamily.coefficients_memℓp (K : DensityFamily X ι μ) (f : Lp ℂ 2 μ) :
    Memℓp (fun i => K.coefficient i f) 2 := by
  apply memℓp_gen' (C := K.overlapBound * ‖f‖ ^ 2)
  intro s
  simpa using K.bessel_bound f s

/-- Analysis as a linear map, with its ℓ² membership already proved. -/
def DensityFamily.analysisLinear (K : DensityFamily X ι μ) :
    Lp ℂ 2 μ →ₗ[ℂ] SequenceL2 ι where
  toFun f := ⟨fun i => K.coefficient i f, K.coefficients_memℓp f⟩
  map_add' f g := by ext i; exact map_add (K.coefficient i) f g
  map_smul' c f := by ext i; exact map_smul (K.coefficient i) c f

/-- The operator norm estimate before bundling continuity. -/
theorem DensityFamily.analysisLinear_bound (K : DensityFamily X ι μ) (f : Lp ℂ 2 μ) :
    ‖K.analysisLinear f‖ ≤ Real.sqrt K.overlapBound * ‖f‖ := by
  apply lp.norm_le_of_forall_sum_le (p := 2) (by norm_num) (by positivity)
  intro s
  have hs := K.bessel_bound f s
  simpa only [analysisLinear, LinearMap.coe_mk, AddHom.coe_mk, ENNReal.toReal_ofNat, Real.rpow_two, mul_pow,
    Real.sq_sqrt K.overlapBound_nonneg] using hs

/-- The bounded analysis operator used in the current factorization. -/
def DensityFamily.analysis (K : DensityFamily X ι μ) :
    Lp ℂ 2 μ →L[ℂ] SequenceL2 ι :=
  K.analysisLinear.mkContinuous (Real.sqrt K.overlapBound) K.analysisLinear_bound

/-- Its coordinates are exactly the integrals from the writeup. -/
theorem DensityFamily.analysis_apply (K : DensityFamily X ι μ) (f : Lp ℂ 2 μ) (i : ι) :
    K.analysis f i = ∫ x, (K.density i x : ℂ) * f x ∂μ :=
  K.coefficient_eq_integral i f

/-- A quantitative operator-norm bound. -/
theorem DensityFamily.analysis_norm_le (K : DensityFamily X ι μ) :
    ‖K.analysis‖ ≤ Real.sqrt K.overlapBound := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact K.analysisLinear_bound

end Singularity
