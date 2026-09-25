import Singularity.Mautner
import Singularity.ShearContraction

/-!
# Mautner's fixed-vector conclusion for SL(2,ℝ)

A continuous isometric action has the same fixed points for a single positive
hyperbolic dilation as for the full group. Contraction proves invariance under
both shear subgroups, and transvection generation proves the conclusion.
-/

noncomputable section
open scoped MatrixGroups Topology

namespace Singularity

theorem upperShearMatrix_eq_transvection (u : ℝ) :
    upperShearMatrix u = Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 from zero_ne_one) u := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upperShearMatrix, Matrix.SpecialLinearGroup.transvection_coe]

theorem lowerShearMatrix_eq_transvection (u : ℝ) :
    lowerShearMatrix u = Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 from one_ne_zero) u := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShearMatrix, Matrix.SpecialLinearGroup.transvection_coe]

/-- The two shear subgroups together detect fixed points for the entire group. -/
theorem fixed_slTwo_of_fixed_shears {X : Type*} [MulAction SL(2, ℝ) X]
    (v : X) (hu : ∀ u, upperShearMatrix u • v = v)
    (hl : ∀ u, lowerShearMatrix u • v = v) (g : SL(2, ℝ)) : g • v = v := by
  apply Matrix.SL2.transvection_induction (fun g => g • v = v) _ _ g
  · intro i j hij u
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa only [upperShearMatrix_eq_transvection] using hu u
    · simpa only [lowerShearMatrix_eq_transvection] using hl u
    · exact (hij rfl).elim
  · intro a b ha hb
    rw [mul_smul, hb, ha]

/-- A positive diagonal time has exactly the fixed vectors of the full group. -/
theorem fixed_slTwo_of_fixed_dilation {X : Type*} [MetricSpace X]
    [MulAction SL(2, ℝ) X] [IsIsometricSMul SL(2, ℝ) X]
    [ContinuousSMul SL(2, ℝ) X] (τ : ℝ) (hτ : 0 < τ)
    (v : X) (hfix : dilationMatrix τ • v = v) (g : SL(2, ℝ)) : g • v = v := by
  have ha (n : ℕ) : dilationMatrix ((n : ℝ) * τ) • v = v := by
    simpa only [← dilationMatrix_zpow, Int.cast_natCast] using
      fixed_zpow_of_fixed (dilationMatrix τ) v hfix (n : ℤ)
  apply fixed_slTwo_of_fixed_shears v
  · intro u
    exact fixed_of_conjugates_tendsto_one
      (fun n : ℕ => dilationMatrix ((n : ℝ) * τ)) (upperShearMatrix u) v
      (continuous_id.smul continuous_const).continuousAt ha (upperShear_conjugates_tendsto_one τ u hτ)
  · intro u
    apply fixed_of_conjugates_tendsto_one (l := Filter.atTop)
      (fun n : ℕ => (dilationMatrix ((n : ℝ) * τ))⁻¹) (lowerShearMatrix u) v
      (continuous_id.smul continuous_const).continuousAt
    · intro n
      exact inv_smul_eq_iff.mpr (ha n).symm
    · simpa only [inv_inv] using lowerShear_conjugates_tendsto_one τ u hτ

end Singularity
