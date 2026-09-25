import Singularity.MobiusMeasureAction
import Singularity.CyclicOrbits
import Singularity.MobiusBoundaryAnalysis

/-!
# Diagonal hyperbolic elements and lattice orbit measures

An explicit one-parameter subgroup of SL(2,ℝ) acts on the boundary by positive
dilation. Its integer powers give exactly the translations nτ after the
logarithmic change of coordinates. Pushforward composition is justified by
the almost-everywhere Möbius action law.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

/-- The diagonal special linear matrix whose boundary dilation is exp(t). -/
def dilationMatrix (t : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.exp (t / 2), 0; 0, (Real.exp (t / 2))⁻¹], by simp⟩

theorem dilationMatrix_zero : dilationMatrix 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [dilationMatrix]

/-- These matrices form a one-parameter subgroup. -/
theorem dilationMatrix_add (s t : ℝ) : dilationMatrix (s + t) = dilationMatrix s * dilationMatrix t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [dilationMatrix, add_div, Real.exp_add, mul_inv_rev, mul_comm]

/-- The one-parameter subgroup as a multiplicative homomorphism. -/
def dilationMatrixHom : Multiplicative ℝ →* SL(2, ℝ) where
  toFun t := dilationMatrix t.toAdd
  map_one' := dilationMatrix_zero
  map_mul' s t := dilationMatrix_add s.toAdd t.toAdd

/-- Positive and negative integer powers correspond to the parameter n t. -/
theorem dilationMatrix_zpow (t : ℝ) (n : ℤ) : dilationMatrix ((n : ℝ) * t) = dilationMatrix t ^ n := by
  have h := dilationMatrixHom.map_zpow (Multiplicative.ofAdd t) n
  change dilationMatrix ((Multiplicative.ofAdd t ^ n).toAdd) = dilationMatrix t ^ n at h
  simpa only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul] using h

/-- The real boundary action is dilation by exp(t), with no finite pole. -/
theorem realBoundaryMobius_dilationMatrix (t : ℝ) :
    realBoundaryMobius (dilationMatrix t) = (fun u => Real.exp t * u) := by
  funext u
  have he : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp [realBoundaryMobius, dilationMatrix]
  rw [mul_right_comm, he]

/-- The one-parameter subgroup is injective; positive τ therefore gives an
infinite-order element for the cyclic strip-orbit construction. -/
theorem dilationMatrix_injective : Function.Injective dilationMatrix := by
  intro s t h
  have he := congrArg (fun g : SL(2, ℝ) => realBoundaryMobius g 1) h
  simpa only [realBoundaryMobius_dilationMatrix, mul_one, Real.exp_eq_exp] using he

/-- A nonzero dilation parameter gives an infinite-order special linear matrix. -/
theorem dilationMatrix_infinite_order {t : ℝ} (ht : t ≠ 0) : ¬IsOfFinOrder (dilationMatrix t) := by
  apply injective_zpow_iff_not_isOfFinOrder.mp
  intro m n h
  change dilationMatrix t ^ m = dilationMatrix t ^ n at h
  rw [← dilationMatrix_zpow, ← dilationMatrix_zpow] at h
  have he := mul_right_cancel₀ ht (dilationMatrix_injective h)
  exact_mod_cast he

/-- The orbit measure for a^n b is exactly the dilation pushforward of b_*ν. -/
theorem dilationOrbit_map (ν : Measure ℝ) (hac : ν ≪ volume) (τ : ℝ) (n : ℤ) (b : SL(2, ℝ)) :
    Measure.map (realBoundaryMobius (dilationMatrix τ ^ n * b)) ν =
      Measure.map (fun u : ℝ => Real.exp ((n : ℝ) * τ) * u)
        (Measure.map (realBoundaryMobius b) ν) := by
  rw [← dilationMatrix_zpow, map_realBoundaryMobius_mul ν hac, realBoundaryMobius_dilationMatrix]

end Singularity
