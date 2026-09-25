import Singularity.ProjectiveEndpointHeight

/-!
# An ideal Dirichlet endpoint excludes a horoball

If `v` lies higher than `z`, the hyperbolic half-plane closer to `z` than
to `v` is bounded in the ordinary complex plane. Consequently a set with
infinity in its compactified closure cannot be closer to `z` than to a
higher point. This is the horoball exclusion needed for Dirichlet ends.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- A quadratic inequality bounds a nonnegative variable. -/
theorem nonneg_le_of_quadratic_bound {N a b : ℝ} (_hN : 0 ≤ N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : N ^ 2 ≤ a * N + b) :
    N ≤ a + b + 1 := by
  by_contra hn
  have hn' : a + b + 1 < N := lt_of_not_ge hn
  have h1 : 1 ≤ N := by linarith
  have h2 := mul_nonneg hb (sub_nonneg.mpr h1)
  have h3 := mul_pos (sub_pos.mpr hn') (show 0 < N by linarith)
  nlinarith

/-- A hyperbolic bisector with the competing point higher than the centre
bounds the centre's side in Euclidean norm. -/
theorem bounded_complex_norm_of_dist_le_of_im_lt (z v : ℍ) (h : z.im < v.im) :
    ∃ C : ℝ, ∀ w : ℍ, dist w z ≤ dist w v → ‖(w : ℂ)‖ ≤ C := by
  let δ := v.im - z.im
  let A := v.im * z.re - z.im * v.re
  let B := z.im * (v.re ^ 2 + v.im ^ 2) - v.im * (z.re ^ 2 + z.im ^ 2)
  have hδ : 0 < δ := sub_pos.mpr h
  refine ⟨2 * |A| / δ + |B| / δ + 1, fun w hw => ?_⟩
  have hc : Real.cosh (dist w z) ≤ Real.cosh (dist w v) :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg dist_nonneg] using hw)
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hc
  have hc' := (div_le_div_iff₀
    (show 0 < 2 * w.im * z.im by positivity)
    (show 0 < 2 * w.im * v.im by positivity)).mp hc
  have hp : v.im * ((w.re - z.re) ^ 2 + w.im ^ 2 + z.im ^ 2) ≤
      z.im * ((w.re - v.re) ^ 2 + w.im ^ 2 + v.im ^ 2) := by
    nlinarith [w.im_pos]
  have hn : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change w.re * w.re + w.im * w.im = _
    ring
  have hq : δ * ‖(w : ℂ)‖ ^ 2 ≤ 2 * A * w.re + B := by
    rw [hn]
    dsimp [δ, A, B]
    nlinarith [hp]
  have hr : A * w.re ≤ |A| * ‖(w : ℂ)‖ :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm (w : ℂ)) (abs_nonneg A))
  apply nonneg_le_of_quadratic_bound (norm_nonneg _) (by positivity) (by positivity)
  apply (mul_le_mul_iff_right₀ hδ).mp
  have he : δ * (2 * |A| / δ * ‖(w : ℂ)‖ + |B| / δ) =
      2 * |A| * ‖(w : ℂ)‖ + |B| := by field_simp
  rw [he]
  nlinarith [le_abs_self B]

/-- Infinity in the compactified closure forces every competitor to lie
no higher than the centre. -/
theorem im_le_of_infty_mem_closure_dist_le (S : Set ℍ) (z v : ℍ)
    (hinfty : (∞ : OnePoint ℂ) ∈ closure (hyperbolicCompactEmbedding '' S))
    (hS : ∀ w ∈ S, dist w z ≤ dist w v) : v.im ≤ z.im := by
  by_contra hn
  obtain ⟨C, hC⟩ := bounded_complex_norm_of_dist_le_of_im_lt z v (lt_of_not_ge hn)
  have hk : IsCompact ((fun u : ℂ => (u : OnePoint ℂ)) '' Metric.closedBall 0 C) :=
    (isCompact_closedBall (0 : ℂ) C).image OnePoint.continuous_coe
  have hsub : hyperbolicCompactEmbedding '' S ⊆
      (fun u : ℂ => (u : OnePoint ℂ)) '' Metric.closedBall 0 C := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨(w : ℂ), ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hC w (hS w hw)
  have hx := (closure_minimal hsub hk.isClosed) hinfty
  exact OnePoint.infty_notMem_image_coe hx

end Singularity
