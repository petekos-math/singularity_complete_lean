import Singularity.VisualPoissonRay
import Singularity.PeriodicStrip

/-!
# Boundary convergence for points a bounded distance from a ray

A lower bound for the height after sending ξ to infinity yields an explicit
Euclidean distance bound to ξ. Consequently bounded-distance ray approaches
converge to the same finite boundary point and eventually have its sign.
-/

noncomputable section
open Filter Set
open scoped MatrixGroups UpperHalfPlane Topology

namespace Singularity

/-- The transformed height bounds Euclidean distance from the pole. -/
theorem dist_boundary_le_inv_pole_height (ξ : ℝ) (z : ℍ) :
    dist (z : ℂ) (ξ : ℂ) ≤ ((boundaryPoleMatrix ξ • z).im)⁻¹ := by
  have hi : z.im ≤ ‖(z : ℂ) - (ξ : ℂ)‖ := by
    simpa using Complex.im_le_norm ((z : ℂ) - (ξ : ℂ))
  have hs : ‖(z : ℂ) - (ξ : ℂ)‖ ^ 2 = (ξ - z.re) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  rw [dist_eq_norm, boundaryPoleMatrix_smul_im, inv_div, le_div_iff₀ z.im_pos]
  nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg ((z : ℂ) - (ξ : ℂ)))]

/-- A point within distance D of the ray is exponentially close to ξ in the
ordinary complex-plane metric. -/
theorem near_finiteBoundaryRay_dist_bound (ξ t D : ℝ) (z : ℍ)
    (hz : dist z (finiteBoundaryRay ξ t) ≤ D) :
    dist (z : ℂ) (ξ : ℂ) ≤ (1 + ξ ^ 2) * Real.exp (D - t) := by
  have h := UpperHalfPlane.im_le_im_mul_exp_dist
    (boundaryPoleMatrix ξ • finiteBoundaryRay ξ t) (boundaryPoleMatrix ξ • z)
  rw [dist_smul, dist_comm (finiteBoundaryRay ξ t) z] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz)
    (boundaryPoleMatrix ξ • z).im_pos.le)
  simp only [finiteBoundaryRay, smul_inv_smul] at h'
  change Real.exp t * (boundaryPoleMatrix ξ • UpperHalfPlane.I).im ≤
    (boundaryPoleMatrix ξ • z).im * Real.exp D at h'
  have hp : 0 < Real.exp t * (boundaryPoleMatrix ξ • UpperHalfPlane.I).im := by positivity
  calc
    dist (z : ℂ) (ξ : ℂ) ≤ ((boundaryPoleMatrix ξ • z).im)⁻¹ :=
      dist_boundary_le_inv_pole_height ξ z
    _ ≤ Real.exp D / (Real.exp t * (boundaryPoleMatrix ξ • UpperHalfPlane.I).im) := by
      rw [le_div_iff₀ hp]
      calc
        _ ≤ ((boundaryPoleMatrix ξ • z).im)⁻¹ *
            ((boundaryPoleMatrix ξ • z).im * Real.exp D) :=
          mul_le_mul_of_nonneg_left h' (inv_pos.mpr (boundaryPoleMatrix ξ • z).im_pos).le
        _ = Real.exp D := by rw [← mul_assoc, inv_mul_cancel₀ (boundaryPoleMatrix ξ • z).im_pos.ne', one_mul]
    _ = (1 + ξ ^ 2) * Real.exp (D - t) := by
      rw [boundaryPoleMatrix_smul_im]
      simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, sub_zero, one_pow]
      rw [Real.exp_sub]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

/-- Bounded-distance approaches converge to the same finite boundary point. -/
theorem near_finiteBoundaryRay_tendsto {α : Type*} {l : Filter α}
    (ξ D : ℝ) (t : α → ℝ) (ht : Tendsto t l atTop) (z : α → ℍ)
    (hz : ∀ n, dist (z n) (finiteBoundaryRay ξ (t n)) ≤ D) :
    Tendsto (fun n => (z n : ℂ)) l (𝓝 (ξ : ℂ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => near_finiteBoundaryRay_dist_bound ξ (t n) D (z n) (hz n))
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul ((1 + ξ ^ 2) * Real.exp D)
  simpa only [mul_zero, Real.exp_sub, Real.exp_neg, div_eq_mul_inv, mul_assoc, Function.comp_def] using h

/-- In particular the real parts converge to ξ. -/
theorem near_finiteBoundaryRay_re_tendsto {α : Type*} {l : Filter α}
    (ξ D : ℝ) (t : α → ℝ) (ht : Tendsto t l atTop) (z : α → ℍ)
    (hz : ∀ n, dist (z n) (finiteBoundaryRay ξ (t n)) ≤ D) :
    Tendsto (fun n => (z n).re) l (𝓝 ξ) :=
  Complex.continuous_re.continuousAt.tendsto.comp (near_finiteBoundaryRay_tendsto ξ D t ht z hz)

/-- Approaches to a negative boundary coordinate are eventually on the negative side. -/
theorem near_finiteBoundaryRay_eventually_negative {α : Type*} {l : Filter α}
    {ξ : ℝ} (hξ : ξ < 0) (D : ℝ) (t : α → ℝ) (ht : Tendsto t l atTop) (z : α → ℍ)
    (hz : ∀ n, dist (z n) (finiteBoundaryRay ξ (t n)) ≤ D) :
    ∀ᶠ n in l, (z n).re < 0 :=
  (near_finiteBoundaryRay_re_tendsto ξ D t ht z hz).eventually (gt_mem_nhds hξ)

/-- Approaches to a positive boundary coordinate are eventually on the positive side. -/
theorem near_finiteBoundaryRay_eventually_positive {α : Type*} {l : Filter α}
    {ξ : ℝ} (hξ : 0 < ξ) (D : ℝ) (t : α → ℝ) (ht : Tendsto t l atTop) (z : α → ℍ)
    (hz : ∀ n, dist (z n) (finiteBoundaryRay ξ (t n)) ≤ D) :
    ∀ᶠ n in l, 0 < (z n).re :=
  (near_finiteBoundaryRay_re_tendsto ξ D t ht z hz).eventually (lt_mem_nhds hξ)

/-- Heights of a bounded-distance ray approach tend to zero at a finite endpoint. -/
theorem near_finiteBoundaryRay_im_tendsto {α : Type*} {l : Filter α}
    (ξ D : ℝ) (t : α → ℝ) (ht : Tendsto t l atTop) (z : α → ℍ)
    (hz : ∀ n, dist (z n) (finiteBoundaryRay ξ (t n)) ≤ D) :
    Tendsto (fun n => (z n).im) l (𝓝 0) :=
  Complex.continuous_im.continuousAt.tendsto.comp (near_finiteBoundaryRay_tendsto ξ D t ht z hz)

/-- Every fixed-width ratio strip is eventually avoided away from its endpoints. -/
theorem near_finiteBoundaryRay_eventually_outside_strip {α : Type*} {l : Filter α}
    {ξ : ℝ} (hξ : ξ ≠ 0) (D R : ℝ) (t : α → ℝ) (ht : Tendsto t l atTop) (z : α → ℍ)
    (hz : ∀ n, dist (z n) (finiteBoundaryRay ξ (t n)) ≤ D) :
    ∀ᶠ n in l, z n ∉ axisRatioStrip R := by
  have hre := (near_finiteBoundaryRay_re_tendsto ξ D t ht z hz).abs
  have him := (near_finiteBoundaryRay_im_tendsto ξ D t ht z hz).const_mul R
  have he : Tendsto (fun n => |(z n).re| - R * (z n).im) l (𝓝 |ξ|) := by
    simpa only [mul_zero, sub_zero] using hre.sub him
  filter_upwards [he.eventually (lt_mem_nhds (abs_pos.mpr hξ))] with n hn
  intro hmem
  change |(z n).re / (z n).im| ≤ R at hmem
  rw [abs_div, abs_of_pos (z n).im_pos] at hmem
  have hle := (div_le_iff₀ (z n).im_pos).mp hmem
  linarith

/-- Distance from i tends to infinity along every nonnegative-time bounded
ray approach, independently of its finite endpoint. -/
theorem near_finiteBoundaryRay_dist_tendsto {α : Type*} {l : Filter α}
    (ξ D : ℝ) (t : α → ℝ) (ht : Tendsto t l atTop) (hpos : ∀ n, 0 ≤ t n)
    (z : α → ℍ) (hz : ∀ n, dist (z n) (finiteBoundaryRay ξ (t n)) ≤ D) :
    Tendsto (fun n => dist UpperHalfPlane.I (z n)) l atTop := by
  have ht' : Tendsto (fun n => t n - D) l atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [ht.eventually_ge_atTop (b + D)] with n hn
    linarith
  apply tendsto_atTop_mono (f := fun n => t n - D) _ ht'
  intro n
  have h := dist_triangle UpperHalfPlane.I (z n) (finiteBoundaryRay ξ (t n))
  rw [finiteBoundaryRay_dist ξ (hpos n)] at h
  linarith [hz n]

end Singularity
