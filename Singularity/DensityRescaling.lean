import Singularity.PoissonMeasure
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Rescaling a Lebesgue density point

The complement of a measurable density-one set has density zero. After
translation and positive dilation, its Lebesgue measure in every fixed bounded
window tends to zero. These are the local estimates for Poisson concentration.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical Topology ENNReal

namespace Singularity

/-- Density one of a measurable set is density zero of its complement. -/
theorem density_compl_tendsto_zero (S : Set ℝ) (hS : MeasurableSet S) (x : ℝ)
    (h : Tendsto (fun r : ℝ => volume (S ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun r : ℝ => volume (Sᶜ ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
  have he (r : ℝ) (hr : 0 < r) :
      volume (Sᶜ ∩ closedBall x r) / volume (closedBall x r) =
        1 - volume (S ∩ closedBall x r) / volume (closedBall x r) := by
    have hpos : volume (closedBall x r) ≠ 0 := by rw [Real.volume_closedBall]; exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    have htop : volume (closedBall x r) ≠ ⊤ := by rw [Real.volume_closedBall]; exact ENNReal.ofReal_ne_top
    have hsum : volume (Sᶜ ∩ closedBall x r) + volume (S ∩ closedBall x r) = volume (closedBall x r) := by
      simpa only [Set.sdiff_eq, inter_comm, add_comm] using measure_inter_add_sdiff (closedBall x r) hS
    have hsub := ENNReal.eq_sub_of_add_eq' htop hsum
    rw [hsub, ENNReal.sub_div (fun _ _ => hpos), ENNReal.div_self hpos htop]
  have ht := (ENNReal.continuous_sub_left (by simp : (1 : ℝ≥0∞) ≠ ⊤)).tendsto 1 |>.comp h
  simp only [tsub_self, Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (he r hr).symm

/-- Lebesgue measure under a translated positive dilation. -/
theorem volume_affine_preimage (x r : ℝ) (hr : 0 < r) (S : Set ℝ) :
    volume ((fun t : ℝ => x + r * t) ⁻¹' S) = ENNReal.ofReal r⁻¹ * volume S := by
  change volume ((fun t : ℝ => r * t) ⁻¹' ((fun t : ℝ => x + t) ⁻¹' S)) = _
  rw [Real.volume_preimage_mul_left hr.ne', measure_preimage_add, abs_of_pos (inv_pos.mpr hr)]

/-- The measure of the rescaled set in a fixed window is its local density
multiplied by the length of that window. -/
theorem volume_rescaled_inter_ball (S : Set ℝ) (x r R : ℝ) (hr : 0 < r) (hR : 0 < R) :
    volume (((fun t : ℝ => x + r * t) ⁻¹' S) ∩ closedBall 0 R) =
      ENNReal.ofReal (2 * R) * (volume (S ∩ closedBall x (r * R)) / volume (closedBall x (r * R))) := by
  have he : ((fun t : ℝ => x + r * t) ⁻¹' S) ∩ closedBall 0 R =
      (fun t : ℝ => x + r * t) ⁻¹' (S ∩ closedBall x (r * R)) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq,
      add_sub_cancel_left, sub_zero, abs_mul, abs_of_pos hr]
    exact and_congr_right fun _ => (mul_le_mul_iff_right₀ hr).symm
  rw [he, volume_affine_preimage x r hr]
  have hp : volume (closedBall x (r * R)) ≠ 0 := by
    rw [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have htop : volume (closedBall x (r * R)) ≠ ⊤ := by
    rw [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_top
  have hc : ENNReal.ofReal r⁻¹ * volume (closedBall x (r * R)) = ENNReal.ofReal (2 * R) := by
    rw [Real.volume_closedBall, ← ENNReal.ofReal_mul (inv_pos.mpr hr).le]
    congr 1
    field_simp
  calc
    _ = ENNReal.ofReal r⁻¹ * (volume (closedBall x (r * R)) *
        (volume (S ∩ closedBall x (r * R)) / volume (closedBall x (r * R)))) := by
      rw [ENNReal.mul_div_cancel hp htop]
    _ = _ := by rw [← mul_assoc, hc]

/-- Density zero implies vanishing measure after rescaling in each fixed window. -/
theorem density_zero_rescaled_ball (S : Set ℝ) (x : ℝ)
    (h : Tendsto (fun r : ℝ => volume (S ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 0)) (R : ℝ) (hR : 0 < R) :
    Tendsto (fun r : ℝ => volume (((fun t : ℝ => x + r * t) ⁻¹' S) ∩ closedBall 0 R))
      (𝓝[>] 0) (𝓝 0) := by
  have hr : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun r : ℝ => r * R) := continuous_id.mul continuous_const
      simpa only [zero_mul] using (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hR
  have ht := ENNReal.Tendsto.const_mul (h.comp hr)
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * R) ≠ ⊤))
  simp only [mul_zero, Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (volume_rescaled_inter_ball S x r R hr hR).symm

end Singularity
