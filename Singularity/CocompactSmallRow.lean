import Singularity.CocompactRayApproximation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cocompactness supplies matrices with a shrinking lower row

Uniform density of an orbit gives arbitrarily large imaginary parts. The identity
im(g i)=1/(c²+d²) then supplies a sequence whose lower row tends to zero.
-/

noncomputable section
open Filter
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- The lower row of a determinant-one matrix is nonzero. -/
theorem slTwo_lower_row_sq_pos (g : SL(2, ℝ)) : 0 < g 1 0 ^ 2 + g 1 1 ^ 2 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  by_contra h
  have hc : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 1), sq_nonneg (g 1 0)]
  have hd : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 1), sq_nonneg (g 1 0)]
  simp [hc, hd] at hdet

/-- The imaginary part of g i records the squared norm of its lower row. -/
theorem slTwo_im_smul_I (g : SL(2, ℝ)) :
    (g • UpperHalfPlane.I).im = 1 / (g 1 0 ^ 2 + g 1 1 ^ 2) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  change ((g • UpperHalfPlane.I : ℍ) : ℂ).im = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [Complex.div_im, Complex.normSq_apply]
  rw [← sub_div, hdet]
  simp [pow_two, add_comm]

/-- An orbit of a cocompact subgroup reaches arbitrarily large heights. -/
theorem cocompact_orbit_height_unbounded (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] (R : ℝ) :
    ∃ g : Γ, R < (g • UpperHalfPlane.I).im := by
  obtain ⟨D, _, hcover⟩ := cocompact_orbit_uniform_bound Γ
  let z : ℍ := ⟨⟨0, Real.exp D * (|R| + 1)⟩, by positivity⟩
  obtain ⟨g, hg⟩ := hcover z
  have hdist : dist z (g • UpperHalfPlane.I) ≤ D := by simpa only [dist_comm] using hg
  have hheight := (UpperHalfPlane.im_le_im_mul_exp_dist z (g • UpperHalfPlane.I)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdist) (g • UpperHalfPlane.I).im_pos.le)
  change Real.exp D * (|R| + 1) ≤ (g • UpperHalfPlane.I).im * Real.exp D at hheight
  have hbound : |R| + 1 ≤ (g • UpperHalfPlane.I).im := by
    nlinarith [Real.exp_pos D]
  exact ⟨g, lt_of_lt_of_le (by linarith [le_abs_self R]) hbound⟩

/-- A cocompact subgroup has a sequence of matrices with both lower entries tending to zero. -/
theorem exists_cocompact_small_lower_row (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    ∃ g : ℕ → Γ,
      Tendsto (fun n => (g n : SL(2, ℝ)) 1 0) atTop (nhds 0) ∧
      Tendsto (fun n => (g n : SL(2, ℝ)) 1 1) atTop (nhds 0) := by
  choose g hg using fun n : ℕ => cocompact_orbit_height_unbounded Γ ((n : ℝ) + 1)
  have hbound (n : ℕ) : (g n : SL(2, ℝ)) 1 0 ^ 2 + (g n : SL(2, ℝ)) 1 1 ^ 2 ≤
      1 / ((n : ℝ) + 1) := by
    have h := hg n
    change (n : ℝ) + 1 < ((g n : SL(2, ℝ)) • UpperHalfPlane.I).im at h
    rw [slTwo_im_smul_I] at h
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    have h' := (lt_div_iff₀ (slTwo_lower_row_sq_pos (g n))).mp h
    linarith
  have hs : Tendsto (fun n => (g n : SL(2, ℝ)) 1 0 ^ 2 + (g n : SL(2, ℝ)) 1 1 ^ 2)
      atTop (nhds 0) := squeeze_zero (fun n => by positivity) hbound
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hentry (j : Fin 2) : Tendsto (fun n => (g n : SL(2, ℝ)) 1 j) atTop (nhds 0) := by
    have hsq : Tendsto (fun n => (g n : SL(2, ℝ)) 1 j ^ 2) atTop (nhds 0) := by
      apply squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hs
      fin_cases j <;> dsimp <;> nlinarith [sq_nonneg ((g n : SL(2, ℝ)) 1 0), sq_nonneg ((g n : SL(2, ℝ)) 1 1)]
    have habs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    have hn : Tendsto (fun n => ‖(g n : SL(2, ℝ)) 1 j‖) atTop (nhds 0) := by
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using habs
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hn
  exact ⟨g, hentry 0, hentry 1⟩

end Singularity
