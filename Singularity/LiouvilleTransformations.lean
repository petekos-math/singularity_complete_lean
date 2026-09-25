import Singularity.LiouvilleCurrent

/-!
# Elementary invariances of the real Liouville measure

Translations, positive dilations, and inversion preserve dx dy/(x-y)².
The inversion proof uses the established inverse-square Lebesgue Jacobian;
its exceptional coordinate axes are null for the absolutely continuous current.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical ENNReal

namespace Singularity

/-- The finite-chart Liouville measure is absolutely continuous with respect to planar product volume. -/
theorem realLiouvilleMeasure_absolutelyContinuous :
    realLiouvilleMeasure ≪ (volume : Measure ℝ).prod volume :=
  withDensity_absolutelyContinuous _ _

/-- Simultaneous translation of the two endpoints preserves the real current. -/
theorem realLiouvilleMeasure_translate (a : ℝ) :
    Measure.map (fun p : ℝ × ℝ => (a + p.1, a + p.2)) realLiouvilleMeasure = realLiouvilleMeasure := by
  apply weightedProduct_invariant_of_div (MeasurableEquiv.addLeft a) (MeasurableEquiv.addLeft a)
    volume volume (fun _ => 1) (fun _ => 1) (fun p : ℝ × ℝ => 1 / (p.1 - p.2) ^ 2)
    measurable_const measurable_const (by fun_prop) (fun _ => one_pos) (fun _ => one_pos)
  · simpa using (measurePreserving_add_left volume a).map_eq
  · simpa using (measurePreserving_add_left volume a).map_eq
  · exact Eventually.of_forall (fun p => by simp)

/-- Simultaneous positive dilation preserves the real current. -/
theorem realLiouvilleMeasure_dilate (a : ℝ) (ha : 0 < a) :
    Measure.map (fun p : ℝ × ℝ => (a * p.1, a * p.2)) realLiouvilleMeasure = realLiouvilleMeasure := by
  apply weightedProduct_invariant_of_div (MeasurableEquiv.mulLeft₀ a ha.ne') (MeasurableEquiv.mulLeft₀ a ha.ne')
    volume volume (fun _ => a⁻¹) (fun _ => a⁻¹) (fun p : ℝ × ℝ => 1 / (p.1 - p.2) ^ 2)
    measurable_const measurable_const (by fun_prop) (fun _ => inv_pos.mpr ha) (fun _ => inv_pos.mpr ha)
  · change Measure.map (fun x : ℝ => a * x) volume = _
    rw [Real.map_volume_mul_left ha.ne', withDensity_const]
    simp only [abs_of_pos (inv_pos.mpr ha)]
  · change Measure.map (fun x : ℝ => a * x) volume = _
    rw [Real.map_volume_mul_left ha.ne', withDensity_const]
    simp only [abs_of_pos (inv_pos.mpr ha)]
  · apply Eventually.of_forall
    intro p
    change 1 / (a⁻¹ * p.1 - a⁻¹ * p.2) ^ 2 = (1 / (p.1 - p.2) ^ 2) / (a⁻¹ * a⁻¹)
    rw [← mul_sub, mul_pow]
    simp only [mul_inv_rev, inv_pow, inv_inv, div_eq_mul_inv]
    ring

/-- The real-chart inversion is a measurable involutive equivalence. -/
def boundaryInversionMeasurableEquiv : ℝ ≃ᵐ ℝ where
  toEquiv := boundaryInversion_involutive.toPerm
  measurable_toFun := measurable_boundaryInversion
  measurable_invFun := measurable_boundaryInversion

/-- The pushforward density of Lebesgue measure under inversion. -/
theorem boundaryInversion_map_volume :
    Measure.map boundaryInversion volume =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal ((x ^ 2)⁻¹)) := by
  have h := congrArg (Measure.map boundaryInversion) boundaryInversion_jacobian_map
  rw [Measure.map_map measurable_boundaryInversion measurable_boundaryInversion] at h
  have he : boundaryInversion ∘ boundaryInversion = id := funext boundaryInversion_involutive
  rw [he, Measure.map_id] at h
  exact h.symm

/-- The scalar inverse-square kernel cancels the two inversion Jacobians off zero. -/
theorem realLiouville_inversion_covariance (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 / (boundaryInversion x - boundaryInversion y) ^ 2 =
      (1 / (x - y) ^ 2) / ((x ^ 2)⁻¹ * (y ^ 2)⁻¹) := by
  have hd : boundaryInversion x - boundaryInversion y = (x - y) / (x * y) := by
    unfold boundaryInversion
    field_simp
    ring
  rw [hd, div_pow]
  simp only [mul_pow, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Simultaneous inversion preserves the real current; exceptional axes are null. -/
theorem realLiouvilleMeasure_invert :
    Measure.map (fun p : ℝ × ℝ => (boundaryInversion p.1, boundaryInversion p.2)) realLiouvilleMeasure =
      realLiouvilleMeasure := by
  have hz : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  have hp : ∀ᵐ x : ℝ ∂volume, 0 < (x ^ 2)⁻¹ := hz.mono (fun x hx => inv_pos.mpr (sq_pos_of_ne_zero hx))
  apply weightedProduct_invariant_of_div_ae boundaryInversionMeasurableEquiv boundaryInversionMeasurableEquiv
    volume volume (fun x => (x ^ 2)⁻¹) (fun x => (x ^ 2)⁻¹) (fun p : ℝ × ℝ => 1 / (p.1 - p.2) ^ 2)
    (by fun_prop) (by fun_prop) (by fun_prop) hp hp boundaryInversion_map_volume boundaryInversion_map_volume
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hz, Measure.quasiMeasurePreserving_snd.ae hz]
    with p hx hy
  exact realLiouville_inversion_covariance p.1 p.2 hx hy

end Singularity
