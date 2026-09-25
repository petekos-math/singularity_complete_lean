import Singularity.LimitSetDynamics

/-!
# Visual comparison at arbitrary basepoints and a limit-set saturation criterion

Visual measures at points a bounded hyperbolic distance apart are uniformly
comparable. Since the limit-set mass is constant along an orbit, Poisson
concentration along a sequence uniformly near that orbit forces full ideal
boundary. Concentration is an explicit input here, not a Fatou theorem assumed
without proof.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- Visual Harnack comparison at any pair of basepoints. -/
theorem compactPoissonMeasure_le_exp_dist_between (z w : ℍ) :
    compactPoissonMeasure z ≤ ENNReal.ofReal (Real.exp (dist w z)) • compactPoissonMeasure w := by
  let B := w.toSL2R
  have hh := Measure.map_mono (compactPoissonMeasure_le_exp_dist (B⁻¹ • z)) (measurable_const_smul B)
  rw [Measure.map_smul _ (measurable_const_smul B).aemeasurable,
    compactPoissonMeasure_covariance, compactPoissonMeasure_covariance, smul_inv_smul] at hh
  have hd : dist UpperHalfPlane.I (B⁻¹ • z) = dist w z := by
    rw [← dist_smul B, smul_inv_smul]
    simp only [B, UpperHalfPlane.toSL2R_smul_I]
  simpa only [hd, B, UpperHalfPlane.toSL2R_smul_I] using hh

/-- The visual mass of the complement is also constant along the orbit. -/
theorem projectiveOrbitLimitSet_compl_visual_mass_orbit (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (g : Γ) :
    compactPoissonMeasure (g • z) (projectiveOrbitLimitSet Γ z)ᶜ =
      compactPoissonMeasure z (projectiveOrbitLimitSet Γ z)ᶜ := by
  let := compactPoissonMeasure_probability z
  let := compactPoissonMeasure_probability (g • z)
  rw [measure_compl (isClosed_projectiveOrbitLimitSet Γ z).measurableSet (measure_ne_top _ _),
    measure_compl (isClosed_projectiveOrbitLimitSet Γ z).measurableSet (measure_ne_top _ _),
    measure_univ, measure_univ, projectiveOrbitLimitSet_visual_mass_orbit]

/-- Visual mass seen from a point near the orbit controls the fixed basepoint mass. -/
theorem limitSet_compl_mass_le_of_near_orbit (Γ : Subgroup PSL(2, ℝ)) (z w : ℍ) (D : ℝ)
    (hnear : ∃ g : Γ, dist w (g • z) ≤ D) :
    compactPoissonMeasure z (projectiveOrbitLimitSet Γ z)ᶜ ≤
      ENNReal.ofReal (Real.exp D) * compactPoissonMeasure w (projectiveOrbitLimitSet Γ z)ᶜ := by
  obtain ⟨g, hg⟩ := hnear
  rw [← projectiveOrbitLimitSet_compl_visual_mass_orbit Γ z g]
  have hh := compactPoissonMeasure_le_exp_dist_between (g • z) w (projectiveOrbitLimitSet Γ z)ᶜ
  simp only [Measure.smul_apply, smul_eq_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hg)) (by positivity))

/-- Concentration of visual measures at points uniformly near an orbit forces
the orbit limit set to be the entire boundary. -/
theorem full_limitSet_of_visual_concentration_near_orbit (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    (w : ℕ → ℍ) (D : ℝ) (hnear : ∀ n, ∃ g : Γ, dist (w n) (g • z) ≤ D)
    (hlim : Tendsto (fun n => compactPoissonMeasure (w n) (projectiveOrbitLimitSet Γ z)ᶜ) atTop (𝓝 0)) :
    projectiveOrbitLimitSet Γ z = Set.univ := by
  have ht := ENNReal.Tendsto.const_mul hlim (Or.inr (by simp : ENNReal.ofReal (Real.exp D) ≠ ⊤))
  have hz : compactPoissonMeasure z (projectiveOrbitLimitSet Γ z)ᶜ = 0 := by
    apply le_antisymm _ (by positivity)
    have hh := ge_of_tendsto ht (Eventually.of_forall fun n =>
      limitSet_compl_mass_le_of_near_orbit Γ z (w n) D (hnear n))
    simpa only [mul_zero] using hh
  apply closed_eq_univ_of_full_visual_mass z _ (isClosed_projectiveOrbitLimitSet Γ z)
  let := compactPoissonMeasure_probability z
  have hh := measure_add_measure_compl (isClosed_projectiveOrbitLimitSet Γ z).measurableSet
    (μ := compactPoissonMeasure z)
  simpa only [hz, add_zero, measure_univ] using hh

end Singularity
