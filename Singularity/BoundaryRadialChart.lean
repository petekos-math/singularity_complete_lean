import Singularity.RadialCoordinate
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction

/-!
# A radial chart at a finite boundary point

The chart sends the chosen ray exactly to the vertical axis and every approach
to its finite endpoint to radial coordinate +infinity. Approaches may be
arbitrarily tangential.
-/

noncomputable section
open Filter
open scoped Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- The standard section acts by the affine map z ↦ w.im*z+w.re. -/
theorem toSL2R_smul_coe_affine (w z : ℍ) :
    ((w.toSL2R • z : ℍ) : ℂ) = (w.im : ℂ) * (z : ℂ) + (w.re : ℂ) := by
  have hs : (Real.sqrt w.im : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr w.im_pos)
  have hs2 : (Real.sqrt w.im : ℂ) ^ 2 = (w.im : ℂ) := by
    exact_mod_cast (Real.sq_sqrt w.im_pos.le)
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [UpperHalfPlane.coe_toSL2R, RingHom.id_apply, Algebra.algebraMap_self,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_div, Complex.ofReal_one]
  field_simp
  linear_combination (z : ℂ) * hs2

/-- The affine section carries the vertical axis to the vertical ray through w. -/
theorem toSL2R_smul_axis (w : ℍ) (t : ℝ) :
    w.toSL2R • verticalHeightRay UpperHalfPlane.I t = verticalHeightRay w t := by
  apply UpperHalfPlane.ext
  rw [toSL2R_smul_coe_affine]
  apply Complex.ext <;> simp [verticalHeightRay, mul_comm]

/-- The pole-normalized chart of the ray to ξ. -/
def finiteBoundaryRadialChart (ξ : ℝ) : SL(2, ℝ) :=
  (boundaryPoleMatrix ξ • UpperHalfPlane.I).toSL2R⁻¹ * boundaryPoleMatrix ξ

/-- Ray time is exactly the axis parameter in this chart. -/
theorem finiteBoundaryRadialChart_ray (ξ t : ℝ) :
    finiteBoundaryRadialChart ξ • finiteBoundaryRay ξ t = verticalHeightRay UpperHalfPlane.I t := by
  unfold finiteBoundaryRadialChart finiteBoundaryRay
  rw [mul_smul, smul_inv_smul, ← toSL2R_smul_axis, inv_smul_smul]

/-- Complex formula for the pole transformation. -/
theorem boundaryPoleMatrix_coe (ξ : ℝ) (z : ℍ) :
    ((boundaryPoleMatrix ξ • z : ℍ) : ℂ) = -((z : ℂ) - (ξ : ℂ))⁻¹ := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [boundaryPoleMatrix, sub_eq_add_neg, div_eq_mul_inv]

/-- Every finite-boundary approach escapes in norm after the pole transformation. -/
theorem boundaryPoleMatrix_norm_tendsto {α : Type*} {l : Filter α}
    (ξ : ℝ) (z : α → ℍ) (hz : Tendsto (fun n => (z n : ℂ)) l (𝓝 (ξ : ℂ))) :
    Tendsto (fun n => ‖((boundaryPoleMatrix ξ • z n : ℍ) : ℂ)‖) l atTop := by
  have hzero : Tendsto (fun n => ‖(z n : ℂ) - (ξ : ℂ)‖) l (𝓝 0) := by
    simpa using (hz.sub_const (ξ : ℂ)).norm
  have hp (n : α) : 0 < ‖(z n : ℂ) - (ξ : ℂ)‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, UpperHalfPlane.coe_im, Complex.ofReal_im, sub_zero,
      Complex.zero_im] at hi
    exact (z n).im_pos.ne' hi
  have ht := tendsto_inv_nhdsGT_zero.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hzero, Filter.Eventually.of_forall hp⟩)
  simpa only [boundaryPoleMatrix_coe, norm_neg, norm_inv, Function.comp_def] using ht

/-- Arbitrary, including tangential, approaches to ξ go to radial +infinity
in the ray-normalized chart. -/
theorem finiteBoundaryRadialChart_tendsto {α : Type*} {l : Filter α}
    (ξ : ℝ) (z : α → ℍ) (hz : Tendsto (fun n => (z n : ℂ)) l (𝓝 (ξ : ℂ))) :
    Tendsto (fun n => axisRadialCoordinate (finiteBoundaryRadialChart ξ • z n)) l atTop := by
  let w := boundaryPoleMatrix ξ • UpperHalfPlane.I
  have hnorm : Tendsto (fun n => ‖((finiteBoundaryRadialChart ξ • z n : ℍ) : ℂ)‖) l atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(boundaryPoleMatrix_norm_tendsto ξ z hz).eventually_ge_atTop
      (w.im * b + |w.re|)] with n hn
    have he : ((boundaryPoleMatrix ξ • z n : ℍ) : ℂ) =
        (w.im : ℂ) * ((finiteBoundaryRadialChart ξ • z n : ℍ) : ℂ) + (w.re : ℂ) := by
      rw [← toSL2R_smul_coe_affine]
      simp [finiteBoundaryRadialChart, w, mul_smul]
    have hh := norm_add_le ((w.im : ℂ) * ((finiteBoundaryRadialChart ξ • z n : ℍ) : ℂ)) (w.re : ℂ)
    rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos w.im_pos,
      Complex.norm_real, Real.norm_eq_abs] at hh
    nlinarith [w.im_pos]
  simpa only [axisRadialCoordinate_eq_log_norm, Function.comp_def] using Real.tendsto_log_atTop.comp hnorm

end Singularity
