import Singularity.HyperbolicTraceNormalization
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Contraction of the two unipotent subgroups

Explicit matrix multiplication proves exponential contraction of the upper
and lower shears under opposite diagonal conjugations. These are the concrete
inputs to the Mautner fixed-vector argument for SL(2,ℝ).
-/

noncomputable section
open Filter
open scoped Classical Topology MatrixGroups

namespace Singularity

/-- The upper triangular unipotent one-parameter subgroup. -/
def upperShearMatrix (u : ℝ) : SL(2, ℝ) := ⟨!![1, u; 0, 1], by simp⟩

theorem upperShearMatrix_zero : upperShearMatrix 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upperShearMatrix]

theorem lowerShearMatrix_zero : lowerShearMatrix 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lowerShearMatrix]

theorem continuous_upperShearMatrix : Continuous upperShearMatrix := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> first | exact continuous_id | exact continuous_const

theorem continuous_lowerShearMatrix : Continuous lowerShearMatrix := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> first | exact continuous_id | exact continuous_const

/-- Inversion of the diagonal subgroup negates its parameter. -/
theorem dilationMatrix_inv (t : ℝ) : (dilationMatrix t)⁻¹ = dilationMatrix (-t) := by
  have h := dilationMatrixHom.map_inv (Multiplicative.ofAdd t)
  exact h.symm

/-- Upper shears contract under backward diagonal conjugation. -/
theorem dilationMatrix_conjugate_upper (t u : ℝ) :
    (dilationMatrix t)⁻¹ * upperShearMatrix u * dilationMatrix t =
      upperShearMatrix (Real.exp (-t) * u) := by
  have he : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  rw [dilationMatrix_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [upperShearMatrix, dilationMatrix, neg_div, Real.exp_neg, mul_assoc]
  rw [← he, mul_inv_rev]
  ring

/-- Lower shears contract under forward diagonal conjugation. -/
theorem dilationMatrix_conjugate_lower (t u : ℝ) :
    dilationMatrix t * lowerShearMatrix u * (dilationMatrix t)⁻¹ =
      lowerShearMatrix (Real.exp (-t) * u) := by
  have he : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  rw [dilationMatrix_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [lowerShearMatrix, dilationMatrix, neg_div, Real.exp_neg, mul_assoc]
  rw [← he, mul_inv_rev]
  ring

/-- The contraction coefficient tends to zero along positive multiples of a fixed time. -/
theorem shearParameter_tendsto_zero (τ u : ℝ) (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * τ)) * u) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) * τ) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hτ
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)
  simpa using he.mul_const u

/-- The actual conjugated upper matrices converge to the identity. -/
theorem upperShear_conjugates_tendsto_one (τ u : ℝ) (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => (dilationMatrix ((n : ℝ) * τ))⁻¹ * upperShearMatrix u *
      dilationMatrix ((n : ℝ) * τ)) atTop (nhds 1) := by
  simp only [dilationMatrix_conjugate_upper]
  simpa only [upperShearMatrix_zero, Function.comp_def] using
    continuous_upperShearMatrix.continuousAt.tendsto.comp (shearParameter_tendsto_zero τ u hτ)

/-- The actual conjugated lower matrices converge to the identity. -/
theorem lowerShear_conjugates_tendsto_one (τ u : ℝ) (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => dilationMatrix ((n : ℝ) * τ) * lowerShearMatrix u *
      (dilationMatrix ((n : ℝ) * τ))⁻¹) atTop (nhds 1) := by
  simp only [dilationMatrix_conjugate_lower]
  simpa only [lowerShearMatrix_zero, Function.comp_def] using
    continuous_lowerShearMatrix.continuousAt.tendsto.comp (shearParameter_tendsto_zero τ u hτ)

end Singularity
