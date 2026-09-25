import Singularity.AnalysisOperator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Pointwise density vectors and their Bochner integrals

For a countable density family, the column at each point belongs to ℓ², is
uniformly bounded, and depends measurably on that point. On L¹∩L² the analysis
operator is its Bochner integral against the input function.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Singularity

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The overlap bound controls the squared norm of every finite column. -/
theorem DensityFamily.column_square_bound (K : DensityFamily X ι μ) (x : X) (s : Finset ι) :
    ∑ i ∈ s, ‖(K.density i x : ℂ)‖ ^ 2 ≤ K.overlapBound ^ 2 := by
  calc
    ∑ i ∈ s, ‖(K.density i x : ℂ)‖ ^ 2 = ∑ i ∈ s, K.density i x ^ 2 := by
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ i ∈ s, K.overlapBound * K.density i x := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [K.nonneg i x, K.row_le i x]
    _ = K.overlapBound * ∑ i ∈ s, K.density i x := (Finset.mul_sum _ _ _).symm
    _ ≤ K.overlapBound ^ 2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (K.overlap s x) K.overlapBound_nonneg

/-- The actual column vector, with its ℓ² membership proved. -/
def DensityFamily.column (K : DensityFamily X ι μ) (x : X) : SequenceL2 ι :=
  ⟨fun i => (K.density i x : ℂ), memℓp_gen' (C := K.overlapBound ^ 2)
    (fun s => by simpa using K.column_square_bound x s)⟩

theorem DensityFamily.column_apply (K : DensityFamily X ι μ) (x : X) (i : ι) :
    K.column x i = (K.density i x : ℂ) := rfl

/-- Uniform bound in the Hilbert-space norm. -/
theorem DensityFamily.column_norm_le (K : DensityFamily X ι μ) (x : X) :
    ‖K.column x‖ ≤ K.overlapBound := by
  apply lp.norm_le_of_forall_sum_le (p := 2) (by norm_num) K.overlapBound_nonneg
  intro s
  simpa only [column_apply, ENNReal.toReal_ofNat, Real.rpow_two] using K.column_square_bound x s

/-- Strong measurability follows from the countable coordinate expansion. -/
theorem DensityFamily.column_aestronglyMeasurable [Countable ι] (K : DensityFamily X ι μ) :
    AEStronglyMeasurable K.column μ := by
  classical
  have hm : ∀ i : ι, AEStronglyMeasurable
      (fun x => lp.single (E := fun _ : ι => ℂ) 2 i (K.column x i)) μ := by
    intro i
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) 2 i).continuous.comp_aestronglyMeasurable
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (K.integrable i).aestronglyMeasurable)
  have he (x : X) : (∑' i, lp.single (E := fun _ : ι => ℂ) 2 i (K.column x i)) = K.column x :=
    (lp.hasSum_single ENNReal.ofNat_ne_top (K.column x)).tsum_eq
  simpa only [he] using AEStronglyMeasurable.tsum (L := .unconditional ι) hm

/-- The vector-valued integrand is integrable for every L¹ input. -/
theorem DensityFamily.column_integrable [Countable ι] (K : DensityFamily X ι μ)
    {f : X → ℂ} (hf : Integrable f μ) : Integrable (fun x => f x • K.column x) μ := by
  apply (hf.norm.mul_const K.overlapBound).mono'
    (hf.aestronglyMeasurable.smul K.column_aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖f x • K.column x‖ ≤ ‖f x‖ * K.overlapBound
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (K.column_norm_le x) (norm_nonneg _))

/-- The analysis operator equals the Bochner integral on L¹∩L². -/
theorem DensityFamily.analysis_eq_integral [Countable ι] (K : DensityFamily X ι μ)
    (f : Lp ℂ 2 μ) (hf : Integrable (f : X → ℂ) μ) :
    K.analysis f = ∫ x, f x • K.column x ∂μ := by
  ext i
  have he := (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).integral_comp_comm (K.column_integrable hf)
  change (∫ x, f x * (K.density i x : ℂ) ∂μ) = (∫ x, f x • K.column x ∂μ) i at he
  rw [K.analysis_apply, ← he]
  simp only [mul_comm]

end Singularity
