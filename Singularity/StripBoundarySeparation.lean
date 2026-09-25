import Singularity.CayleyRealBoundary
import Singularity.PeriodicStrip

/-!
# Disk separation of a strip from transverse boundary points

A finite nonzero real endpoint is uniformly separated in Cayley coordinates
from the entire fixed-width axis strip. Every approach to that endpoint is
therefore eventually separated from all strip vertices at once.
-/

noncomputable section
open Filter Set
open scoped Topology UpperHalfPlane
namespace Singularity

/-- The interior-to-boundary Cayley difference has the same explicit formula
as the two-interior-point difference. -/
theorem halfPlaneCayley_sub_realBoundary (z : ℍ) (ξ : ℝ) :
    halfPlaneCayley z - realBoundaryCayley ξ =
      (2 * Complex.I) * ((z : ℂ) - (ξ : ℂ)) /
        (((z : ℂ) + Complex.I) * ((ξ : ℂ) + Complex.I)) := by
  unfold halfPlaneCayley realBoundaryCayley
  field_simp [halfPlaneCayley_denominator_ne_zero z, realBoundaryCayley_denominator_ne_zero ξ]
  ring

/-- A transverse finite endpoint has a positive uniform disk distance from
all points of a fixed axis strip. -/
theorem axisRatioStrip_cayley_separation (R : ℝ) (hR : 0 ≤ R) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ axisRatioStrip R,
      δ ≤ dist (halfPlaneCayley z) (realBoundaryCayley ξ) := by
  let q := |ξ| / (R + 1)
  let B := ‖(ξ : ℂ) + Complex.I‖
  have hq : 0 < q := div_pos (abs_pos.mpr hξ) (by linarith)
  have hB : 0 < B := norm_pos_iff.mpr (realBoundaryCayley_denominator_ne_zero ξ)
  refine ⟨2 * q / ((q + B) * B), by positivity, fun z hz => ?_⟩
  let A := ‖(z : ℂ) - (ξ : ℂ)‖
  let W := ‖(z : ℂ) + Complex.I‖
  have hW : 0 < W := norm_pos_iff.mpr (halfPlaneCayley_denominator_ne_zero z)
  have hi : z.im ≤ A := by simpa [A] using Complex.im_le_norm ((z : ℂ) - (ξ : ℂ))
  have hr : |ξ - z.re| ≤ A := by
    simpa only [Complex.sub_re, Complex.ofReal_re, UpperHalfPlane.coe_re, abs_sub_comm, A] using
      Complex.abs_re_le_norm ((z : ℂ) - (ξ : ℂ))
  have hz' : |z.re| ≤ R * z.im := by
    change |z.re / z.im| ≤ R at hz
    rw [abs_div, abs_of_pos z.im_pos] at hz
    exact (div_le_iff₀ z.im_pos).mp hz
  have hξA : |ξ| ≤ A * (R + 1) := by
    have ht : |ξ| ≤ |ξ - z.re| + |z.re| := by
      simpa only [sub_add_cancel] using abs_add_le (ξ - z.re) z.re
    have hmul := mul_le_mul_of_nonneg_left hi hR
    nlinarith
  have hqA : q ≤ A := (div_le_iff₀ (by linarith : 0 < R + 1)).mpr hξA
  have hWA : W ≤ A + B := by
    calc
      W = ‖((z : ℂ) - (ξ : ℂ)) + ((ξ : ℂ) + Complex.I)‖ := by dsimp [W]; congr 1; ring
      _ ≤ A + B := norm_add_le _ _
  have hdist : dist (halfPlaneCayley z) (realBoundaryCayley ξ) = 2 * A / (W * B) := by
    rw [dist_eq_norm, halfPlaneCayley_sub_realBoundary, norm_div, norm_mul, norm_mul,
      norm_mul, Complex.norm_two, Complex.norm_I, mul_one]
  rw [hdist]
  apply (div_le_div_iff₀ (mul_pos (add_pos hq hB) hB) (mul_pos hW hB)).mpr
  have hh : q * W ≤ A * (q + B) := by
    nlinarith [mul_le_mul_of_nonneg_left hWA hq.le,
      mul_le_mul_of_nonneg_right hqA hB.le]
  nlinarith [mul_le_mul_of_nonneg_right hh hB.le]

/-- Any approach to a transverse finite endpoint is eventually uniformly
separated from the whole strip, with one bound for all its points. -/
theorem eventually_cayley_separated_from_strip {ι : Type*} {l : Filter ι}
    (R : ℝ) (hR : 0 ≤ R) (ξ : ℝ) (hξ : ξ ≠ 0) (x : ι → ℍ)
    (hx : Tendsto (fun n => halfPlaneCayley (x n)) l (𝓝 (realBoundaryCayley ξ))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in l, ∀ z ∈ axisRatioStrip R,
      δ ≤ dist (halfPlaneCayley (x n)) (halfPlaneCayley z) := by
  obtain ⟨δ, hδ, hb⟩ := axisRatioStrip_cayley_separation R hR ξ hξ
  refine ⟨δ / 2, by positivity, ?_⟩
  filter_upwards [hx.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < δ / 2))] with n hn
  intro z hz
  have ht := dist_triangle (halfPlaneCayley z) (halfPlaneCayley (x n)) (realBoundaryCayley ξ)
  have hn' : dist (halfPlaneCayley (x n)) (realBoundaryCayley ξ) < δ / 2 := hn
  rw [dist_comm (halfPlaneCayley z) (halfPlaneCayley (x n))] at ht
  linarith [hb z hz]

end Singularity
