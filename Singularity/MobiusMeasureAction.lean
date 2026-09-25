import Singularity.PoissonMobius

/-!
# Composition of real-chart Möbius pushforwards

The real-chart formula is not a pointwise action at poles. We prove its group
law almost everywhere and the exact group law on absolutely continuous
measures. No exceptional value is silently treated as a valid boundary action.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

/-- A real special linear matrix has at most one finite boundary pole. -/
theorem realBoundaryMobius_denominator_ae (g : SL(2, ℝ)) :
    ∀ᵐ u : ℝ ∂volume, g 1 0 * u + g 1 1 ≠ 0 := by
  by_cases hc : g 1 0 = 0
  · have hd : g 1 1 ≠ 0 := by
      have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
        simpa only [Matrix.det_fin_two] using g.det_coe
      intro h
      simp [hc, h] at hdet
    exact Eventually.of_forall (fun u => by simpa [hc] using hd)
  · have h : ∀ᵐ u : ℝ ∂volume, u ≠ -(g 1 1) / g 1 0 := by simp [ae_iff]
    filter_upwards [h] with u hu
    intro he
    apply hu
    apply (eq_div_iff hc).mpr
    nlinarith

/-- Composition holds at every point away from the inner map's pole, even
when the composite map has a pole. -/
theorem realBoundaryMobius_mul_of_denominator_ne_zero (g h : SL(2, ℝ)) (u : ℝ)
    (hu : h 1 0 * u + h 1 1 ≠ 0) :
    realBoundaryMobius g (realBoundaryMobius h u) = realBoundaryMobius (g * h) u := by
  unfold realBoundaryMobius
  simp only [← mul_div_assoc]
  rw [div_add' _ _ _ hu, div_add' _ _ _ hu, div_div_div_cancel_right₀ hu]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  congr 1 <;> ring

/-- The finite-chart Möbius formula satisfies the group law almost everywhere. -/
theorem realBoundaryMobius_mul_ae (g h : SL(2, ℝ)) :
    (realBoundaryMobius g ∘ realBoundaryMobius h) =ᵐ[volume] realBoundaryMobius (g * h) := by
  filter_upwards [realBoundaryMobius_denominator_ae h] with u hu
  exact realBoundaryMobius_mul_of_denominator_ne_zero g h u hu

theorem realBoundaryMobius_one : realBoundaryMobius (1 : SL(2, ℝ)) = id := by
  funext u
  simp [realBoundaryMobius]

/-- Every Möbius map preserves real Lebesgue null sets under pullback. -/
theorem quasiMeasurePreserving_realBoundaryMobius (g : SL(2, ℝ)) :
    Measure.QuasiMeasurePreserving (realBoundaryMobius g) volume volume := by
  have hac : volume ≪ poissonBoundaryMeasure UpperHalfPlane.I :=
    (halfPlanePoissonMeasure_measureClass _ UpperHalfPlane.I.im_pos).2
  have h := hac.map (measurable_realBoundaryMobius g)
  rw [poissonBoundaryMeasure_mobius] at h
  exact ⟨measurable_realBoundaryMobius g,
    h.trans (halfPlanePoissonMeasure_measureClass _ (g • UpperHalfPlane.I).im_pos).1⟩

/-- An absolutely continuous boundary measure stays absolutely continuous
under a Möbius pushforward. -/
theorem absolutelyContinuous_map_realBoundaryMobius (ν : Measure ℝ) (hac : ν ≪ volume)
    (g : SL(2, ℝ)) : Measure.map (realBoundaryMobius g) ν ≪ volume :=
  (hac.map (measurable_realBoundaryMobius g)).trans
    (quasiMeasurePreserving_realBoundaryMobius g).absolutelyContinuous

/-- The action law is exact for pushforwards of absolutely continuous measures. -/
theorem map_realBoundaryMobius_mul (ν : Measure ℝ) (hac : ν ≪ volume) (g h : SL(2, ℝ)) :
    Measure.map (realBoundaryMobius (g * h)) ν =
      Measure.map (realBoundaryMobius g) (Measure.map (realBoundaryMobius h) ν) := by
  rw [Measure.map_map (measurable_realBoundaryMobius g) (measurable_realBoundaryMobius h)]
  exact (Measure.map_congr (hac.ae_eq (realBoundaryMobius_mul_ae g h))).symm

/-- Inverse group elements undo the pushforward on absolutely continuous measures. -/
theorem map_realBoundaryMobius_inv (ν : Measure ℝ) (hac : ν ≪ volume) (g : SL(2, ℝ)) :
    Measure.map (realBoundaryMobius g⁻¹) (Measure.map (realBoundaryMobius g) ν) = ν := by
  rw [← map_realBoundaryMobius_mul ν hac, inv_mul_cancel, realBoundaryMobius_one, Measure.map_id]

end Singularity
