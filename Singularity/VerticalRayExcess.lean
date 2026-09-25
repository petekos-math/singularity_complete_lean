import Singularity.QuasiconvexFullBoundary
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform triangle excess along a ray toward infinity

An endpoint approaching infinity eventually has Euclidean norm larger than
any fixed ray height. The hyperbolic cosine formula then bounds the triangle
excess by log 4, uniformly in that ray height. This is enough to transfer
quasiconvexity from finite segments to ideal rays.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- An interior sequence converging to the ideal point infinity escapes in Euclidean norm. -/
theorem norm_tendsto_of_compact_infty {x : ℕ → ℍ}
    (h : Tendsto (fun n => hyperbolicCompactEmbedding (x n)) atTop (𝓝 (∞ : OnePoint ℂ))) :
    Tendsto (fun n => ‖(x n : ℂ)‖) atTop atTop := by
  have ht : Tendsto (fun n => (x n : ℂ)) atTop (coclosedCompact ℂ) := by
    rw [← OnePoint.comap_coe_nhds_infty]
    exact tendsto_comap_iff.mpr h
  rw [coclosedCompact_eq_cocompact] at ht
  exact tendsto_norm_cocompact_atTop.comp ht

/-- A high-enough endpoint gives a uniform cosine-ratio estimate along the vertical ray. -/
theorem cosh_dist_verticalRay_le (y : ℍ) (t : ℝ)
    (hnorm : Real.exp t ≤ ‖(y : ℂ)‖) :
    Real.cosh (dist (verticalHeightRay UpperHalfPlane.I t) y) ≤
      (2 / Real.exp t) * Real.cosh (dist UpperHalfPlane.I y) := by
  have hsq : Real.exp t ^ 2 ≤ y.re ^ 2 + y.im ^ 2 := by
    have h := pow_le_pow_left₀ (Real.exp_pos t).le hnorm 2
    simpa only [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, ← pow_two] using h
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist']
  change ((0 - y.re) ^ 2 + (Real.exp t * 1) ^ 2 + y.im ^ 2) /
    (2 * (Real.exp t * 1) * y.im) ≤
      (2 / Real.exp t) * (((0 - y.re) ^ 2 + 1 ^ 2 + y.im ^ 2) / (2 * 1 * y.im))
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * Real.exp t * y.im by positivity)).mp
  field_simp
  nlinarith

/-- A ray point lies within a uniformly bounded triangle excess of a segment
from i to any endpoint with sufficiently large Euclidean norm. -/
theorem verticalRay_triangle_excess (y : ℍ) (t : ℝ) (ht : 0 ≤ t)
    (hnorm : Real.exp t ≤ ‖(y : ℂ)‖) :
    dist UpperHalfPlane.I (verticalHeightRay UpperHalfPlane.I t) +
      dist y (verticalHeightRay UpperHalfPlane.I t) - dist UpperHalfPlane.I y ≤ Real.log 4 := by
  have hc := cosh_dist_verticalRay_le y t hnorm
  have he : Real.exp (dist (verticalHeightRay UpperHalfPlane.I t) y) ≤
      (4 / Real.exp t) * Real.exp (dist UpperHalfPlane.I y) := by
    calc
      _ ≤ 2 * Real.cosh (dist (verticalHeightRay UpperHalfPlane.I t) y) := exp_le_two_cosh _
      _ ≤ 2 * ((2 / Real.exp t) * Real.cosh (dist UpperHalfPlane.I y)) := by gcongr
      _ ≤ (4 / Real.exp t) * Real.exp (dist UpperHalfPlane.I y) := by
        have hh := cosh_le_exp_of_nonneg (dist UpperHalfPlane.I y) dist_nonneg
        calc
          _ = (4 / Real.exp t) * Real.cosh (dist UpperHalfPlane.I y) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
  have hr : (4 / Real.exp t) * Real.exp (dist UpperHalfPlane.I y) =
      Real.exp (Real.log 4 - t + dist UpperHalfPlane.I y) := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [hr] at he
  have hd := Real.exp_le_exp.mp he
  rw [verticalHeightRay_dist UpperHalfPlane.I ht, dist_comm y]
  linarith

/-- Quasiconvexity supplies orbit-independent tracking of a ray whenever the set
has an ideal sequence tending to infinity. The initial point need not be i. -/
theorem HyperbolicQuasiconvex.near_verticalRay {S : Set ℍ} {D : ℝ}
    (hS : HyperbolicQuasiconvex S D) (a : ℍ) (ha : a ∈ S)
    (x : ℕ → ℍ) (hx : ∀ n, x n ∈ S)
    (hlim : Tendsto (fun n => hyperbolicCompactEmbedding (x n)) atTop (𝓝 (∞ : OnePoint ℂ)))
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ v ∈ S, dist (verticalHeightRay UpperHalfPlane.I t) v ≤
      D + dist a UpperHalfPlane.I + (3 / 2 : ℝ) * Real.log 4 := by
  obtain ⟨n, hn⟩ := ((norm_tendsto_of_compact_infty hlim).eventually_ge_atTop (Real.exp t)).exists
  have he := verticalRay_triangle_excess (x n) t ht hn
  have h1 := dist_triangle a UpperHalfPlane.I (verticalHeightRay UpperHalfPlane.I t)
  have h2 := dist_triangle UpperHalfPlane.I a (x n)
  have he' : dist a (verticalHeightRay UpperHalfPlane.I t) +
      dist (x n) (verticalHeightRay UpperHalfPlane.I t) - dist a (x n) ≤
        Real.log 4 + 2 * dist a UpperHalfPlane.I := by
    rw [dist_comm UpperHalfPlane.I a] at h2
    linarith
  obtain ⟨v, hv, hd⟩ := hS.near_of_excess a ha (x n) (hx n)
    (verticalHeightRay UpperHalfPlane.I t) (Real.log 4 + 2 * dist a UpperHalfPlane.I) he'
  exact ⟨v, hv, by linarith⟩

end Singularity
