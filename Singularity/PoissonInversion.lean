import Singularity.PoissonMeasure

/-!
# Inversion covariance of the Poisson measure

The finite real-chart inversion is u ↦ -1/u, with its value at zero irrelevant
to these absolutely continuous measures. The Jacobian is proved off zero and
the exceptional singleton is removed using its zero Lebesgue measure.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

def boundaryInversion (u : ℝ) : ℝ := -u⁻¹

theorem measurable_boundaryInversion : Measurable boundaryInversion := by
  unfold boundaryInversion
  fun_prop

theorem boundaryInversion_involutive : Function.Involutive boundaryInversion := by
  intro u
  simp [boundaryInversion]

theorem boundaryInversion_image_ne_zero : boundaryInversion '' ({0}ᶜ : Set ℝ) = {0}ᶜ := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [boundaryInversion] using hv
  · intro hu
    refine ⟨boundaryInversion u, ?_, boundaryInversion_involutive u⟩
    simpa [boundaryInversion] using hu

theorem hasDerivAt_boundaryInversion {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt boundaryInversion ((u ^ 2)⁻¹) u := by
  change HasDerivAt (fun v : ℝ => -v⁻¹) ((u ^ 2)⁻¹) u
  convert! (hasDerivAt_inv hu).neg using 1
  simp

/-- The inverse-square Jacobian transports Lebesgue measure through inversion. -/
theorem boundaryInversion_jacobian_map :
    Measure.map boundaryInversion (volume.withDensity (fun u : ℝ => ENNReal.ofReal ((u ^ 2)⁻¹))) =
      volume := by
  have hz : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by simp [ae_iff]
  have hr : (volume : Measure ℝ).restrict {0}ᶜ = volume :=
    Measure.restrict_eq_self_of_ae_mem (by simpa using hz)
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh measurable_boundaryInversion,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable (fun u => h (boundaryInversion u)) from hh.comp measurable_boundaryInversion)]
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul
    (measurableSet_singleton (0 : ℝ)).compl
    (fun u hu => (hasDerivAt_boundaryInversion (by simpa using hu)).hasDerivWithinAt)
    boundaryInversion_involutive.injective.injOn h
  rw [boundaryInversion_image_ne_zero, hr] at hj
  simpa only [Pi.mul_apply, abs_inv, abs_of_nonneg (sq_nonneg (_ : ℝ))] using hj.symm

/-- The distance-squared denominator identity behind inversion covariance. -/
theorem poisson_inversion_denominator (x : ℝ) {y u : ℝ} (hy : 0 < y) (hu : u ≠ 0) :
    (boundaryInversion u - (-x / (x ^ 2 + y ^ 2))) ^ 2 + (y / (x ^ 2 + y ^ 2)) ^ 2 =
      ((u - x) ^ 2 + y ^ 2) / (u ^ 2 * (x ^ 2 + y ^ 2)) := by
  have hr : x ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold boundaryInversion
  field_simp [hu, hr]
  ring

/-- The Poisson kernel transforms with the inverse-square boundary Jacobian. -/
theorem halfPlanePoisson_inversion (x : ℝ) {y : ℝ} (hy : 0 < y)
    {u : ℝ} (hu : u ≠ 0) :
    (u ^ 2)⁻¹ * halfPlanePoisson (-x / (x ^ 2 + y ^ 2)) (y / (x ^ 2 + y ^ 2))
      (boundaryInversion u) = halfPlanePoisson x y u := by
  unfold halfPlanePoisson
  rw [poisson_inversion_denominator x hy hu]
  have hr : x ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hd : (u - x) ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hu, hr, hd]

/-- Inversion of the boundary transports the Poisson probability measure to
the measure at the inverted upper-half-plane point. -/
theorem halfPlanePoissonMeasure_inversion (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Measure.map boundaryInversion (halfPlanePoissonMeasure x y) =
      halfPlanePoissonMeasure (-x / (x ^ 2 + y ^ 2)) (y / (x ^ 2 + y ^ 2)) := by
  let P := halfPlanePoisson (-x / (x ^ 2 + y ^ 2)) (y / (x ^ 2 + y ^ 2))
  have hP : Measurable P := measurable_halfPlanePoisson _ _
  have h := map_withDensity_comp boundaryInversion measurable_boundaryInversion
    (volume.withDensity (fun u : ℝ => ENNReal.ofReal ((u ^ 2)⁻¹)))
    (fun u => ENNReal.ofReal (P u)) hP.ennreal_ofReal
  rw [boundaryInversion_jacobian_map, ← withDensity_mul _ (by fun_prop)
    (hP.ennreal_ofReal.comp measurable_boundaryInversion)] at h
  have heq : (volume : Measure ℝ).withDensity
      ((fun u => ENNReal.ofReal ((u ^ 2)⁻¹)) * (fun u => ENNReal.ofReal (P u)) ∘ boundaryInversion) =
      halfPlanePoissonMeasure x y := by
    apply withDensity_congr_ae
    have hz : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by simp [ae_iff]
    filter_upwards [hz] with u hu
    change ENNReal.ofReal ((u ^ 2)⁻¹) * ENNReal.ofReal (P (boundaryInversion u)) = _
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _))]
    exact congrArg ENNReal.ofReal (halfPlanePoisson_inversion x hy hu)
  rw [heq] at h
  exact h

end Singularity
