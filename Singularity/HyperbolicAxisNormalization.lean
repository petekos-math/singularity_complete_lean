import Singularity.AxisBallSeparation
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Order.IntermediateValue

/-!
# Placing two points on an isometric image of the vertical axis

Rotations fixing i can move any point to the vertical axis. The existence
argument is an intermediate-value argument for the real part, not an assumed
geodesic or transitivity theorem on pairs of interior points.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The determinant-one rotation family fixing i. -/
def axisRotation (t : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.cos t, Real.sin t; -Real.sin t, Real.cos t], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [Real.sin_sq_add_cos_sq t]⟩

theorem continuous_axisRotation : Continuous axisRotation := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    first | exact Real.continuous_cos | exact Real.continuous_sin | exact Real.continuous_sin.neg

theorem axisRotation_zero : axisRotation 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [axisRotation]

/-- Every member of the rotation family fixes i. -/
theorem axisRotation_smul_I (t : ℝ) : axisRotation t • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [axisRotation, RingHom.id_apply, Algebra.algebraMap_self,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.ofReal_neg, UpperHalfPlane.coe_I]
  have hd := UpperHalfPlane.denom_ne_zero (axisRotation t) UpperHalfPlane.I
  change ((-Real.sin t : ℝ) : ℂ) * Complex.I + (Real.cos t : ℂ) ≠ 0 at hd
  rw [Complex.ofReal_neg] at hd
  rw [div_eq_iff hd]
  linear_combination (Real.sin t : ℂ) * Complex.I_sq

/-- A quarter turn acts by z ↦ -1/z. -/
theorem axisRotation_quarter_coe (z : ℍ) :
    ((axisRotation (Real.pi / 2) • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [axisRotation, RingHom.id_apply, Algebra.algebraMap_self,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.ofReal_neg]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- The quarter turn reverses the signed vertical-axis parameter. -/
theorem axisRotation_quarter_ray (t : ℝ) :
    axisRotation (Real.pi / 2) • verticalHeightRay UpperHalfPlane.I t =
      verticalHeightRay UpperHalfPlane.I (-t) := by
  apply UpperHalfPlane.ext
  rw [axisRotation_quarter_coe]
  apply Complex.ext
  · simp [verticalHeightRay, Complex.inv_re]
  · simp [verticalHeightRay, Complex.inv_im, Complex.normSq, Real.exp_neg]
    field_simp

/-- Some rotation fixing i moves any given point to the vertical axis. -/
theorem exists_axisRotation_re_zero (z : ℍ) :
    ∃ t : ℝ, (axisRotation t • z).re = 0 := by
  let f : ℝ → ℝ := fun t => (axisRotation t • z).re
  have hf : Continuous f := UpperHalfPlane.continuous_re.comp (continuous_axisRotation.smul continuous_const)
  have hzero : f 0 = z.re := by simp [f, axisRotation_zero]
  have hquarter : f (Real.pi / 2) = -z.re / Complex.normSq (z : ℂ) := by
    change (((axisRotation (Real.pi / 2) • z : ℍ) : ℂ).re) = _
    rw [axisRotation_quarter_coe, Complex.neg_re, Complex.inv_re, neg_div]
    rfl
  have hnorm : 0 ≤ Complex.normSq (z : ℂ) := Complex.normSq_nonneg _
  by_cases hz : 0 ≤ z.re
  · have hh : 0 ∈ Set.Icc (f (Real.pi / 2)) (f 0) := by
      rw [hzero, hquarter]
      exact ⟨div_nonpos_of_nonpos_of_nonneg (by linarith) hnorm, hz⟩
    exact intermediate_value_univ (Real.pi / 2) 0 hf hh
  · have hh : 0 ∈ Set.Icc (f 0) (f (Real.pi / 2)) := by
      rw [hzero, hquarter]
      exact ⟨le_of_not_ge hz, div_nonneg (by linarith) hnorm⟩
    exact intermediate_value_univ 0 (Real.pi / 2) hf hh

/-- Two arbitrary interior points lie on one isometric image of the vertical
axis. The parameter difference equals their hyperbolic distance in absolute value. -/
theorem exists_hyperbolic_axis_through (z w : ℍ) :
    ∃ (g : SL(2, ℝ)) (t : ℝ), g • UpperHalfPlane.I = z ∧
      g • verticalHeightRay UpperHalfPlane.I t = w ∧ |t| = dist z w := by
  let h := z.toSL2R
  obtain ⟨t, ht⟩ := exists_axisRotation_re_zero (h⁻¹ • w)
  let v := axisRotation t • (h⁻¹ • w)
  have hv : v = verticalHeightRay UpperHalfPlane.I (Real.log v.im) := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change v.re = 0
      exact ht
    · simp [verticalHeightRay, Real.exp_log v.im_pos]
  let g := h * (axisRotation t)⁻¹
  have hg : g • UpperHalfPlane.I = z := by
    have hi : (axisRotation t)⁻¹ • UpperHalfPlane.I = UpperHalfPlane.I := by
      exact (congrArg ((axisRotation t)⁻¹ • ·) (axisRotation_smul_I t)).symm.trans
        (by simp)
    dsimp [g, h]
    rw [mul_smul, hi, UpperHalfPlane.toSL2R_smul_I]
  have hw : g • verticalHeightRay UpperHalfPlane.I (Real.log v.im) = w := by
    rw [← hv]
    dsimp [g, v]
    simp only [mul_smul, inv_smul_smul, smul_inv_smul]
  refine ⟨g, Real.log v.im, hg, hw, ?_⟩
  rw [← hg, ← hw, dist_smul]
  have hd := verticalHeightRay_dist_eq UpperHalfPlane.I 0 (Real.log v.im)
  simpa only [verticalHeightRay_zero, zero_sub, abs_neg] using hd.symm

/-- Orient the axis so the second point has parameter equal to its distance
from the first point. -/
theorem exists_oriented_hyperbolic_axis (z w : ℍ) :
    ∃ g : SL(2, ℝ), g • UpperHalfPlane.I = z ∧
      g • verticalHeightRay UpperHalfPlane.I (dist z w) = w := by
  obtain ⟨g, t, hg, hw, ht⟩ := exists_hyperbolic_axis_through z w
  by_cases hpos : 0 ≤ t
  · refine ⟨g, hg, ?_⟩
    have hd : dist z w = t := by simpa only [abs_of_nonneg hpos] using ht.symm
    rwa [hd]
  · have hneg : t ≤ 0 := le_of_not_ge hpos
    have hd : dist z w = -t := by simpa only [abs_of_nonpos hneg] using ht.symm
    refine ⟨g * axisRotation (Real.pi / 2), ?_, ?_⟩
    · rw [mul_smul, axisRotation_smul_I, hg]
    · rw [mul_smul, hd, axisRotation_quarter_ray, neg_neg, hw]

/-- Every isometric image of the parameterized vertical axis is a unit-speed
geodesic line. -/
theorem isometry_hyperbolic_axis (g : SL(2, ℝ)) :
    Isometry (fun t : ℝ => g • verticalHeightRay UpperHalfPlane.I t) := by
  apply Isometry.of_dist_eq
  intro a b
  rw [dist_smul, verticalHeightRay_dist_eq, Real.dist_eq]

/-- Every pair of points is joined by one of the constructed unit-speed lines. -/
theorem exists_hyperbolic_geodesic_line (z w : ℍ) :
    ∃ c : ℝ → ℍ, Isometry c ∧ c 0 = z ∧ c (dist z w) = w := by
  obtain ⟨g, hg, hw⟩ := exists_oriented_hyperbolic_axis z w
  exact ⟨fun t => g • verticalHeightRay UpperHalfPlane.I t,
    isometry_hyperbolic_axis g, by simpa only [verticalHeightRay_zero] using hg, hw⟩

end Singularity
