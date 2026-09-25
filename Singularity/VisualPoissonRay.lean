import Singularity.DilationGeometry

/-!
# Visual Poisson kernels and a uniform radial estimate

Sending a finite boundary point ξ to infinity turns its ray from i into a
vertical ray. The logarithmic-height Lipschitz estimate in the hyperbolic
metric yields exp(t - d(rξ(t),w)) ≤ P_w(ξ), uniformly in w and t.
-/

noncomputable section
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- A special linear matrix sending the boundary coordinate ξ to infinity. -/
def boundaryPoleMatrix (ξ : ℝ) : SL(2, ℝ) := ⟨!![0, -1; 1, -ξ], by simp⟩

/-- Its imaginary part is the unnormalized Poisson expression. -/
theorem boundaryPoleMatrix_smul_im (ξ : ℝ) (z : ℍ) :
    (boundaryPoleMatrix ξ • z).im = z.im / ((ξ - z.re) ^ 2 + z.im ^ 2) := by
  change ((boundaryPoleMatrix ξ • z : ℍ) : ℂ).im = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [boundaryPoleMatrix, Complex.div_im, Complex.normSq_apply]
  ring

/-- The visual Poisson kernel relative to base point i, expressed as a height ratio. -/
def visualPoisson (z : ℍ) (ξ : ℝ) : ℝ :=
  (boundaryPoleMatrix ξ • z).im / (boundaryPoleMatrix ξ • UpperHalfPlane.I).im

theorem visualPoisson_pos (z : ℍ) (ξ : ℝ) : 0 < visualPoisson z ξ :=
  div_pos (boundaryPoleMatrix ξ • z).im_pos (boundaryPoleMatrix ξ • UpperHalfPlane.I).im_pos

/-- The explicit visual Poisson formula has value one at base point i. -/
theorem visualPoisson_eq (z : ℍ) (ξ : ℝ) :
    visualPoisson z ξ = z.im * (1 + ξ ^ 2) / ((ξ - z.re) ^ 2 + z.im ^ 2) := by
  unfold visualPoisson
  rw [boundaryPoleMatrix_smul_im, boundaryPoleMatrix_smul_im]
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, sub_zero, one_pow]
  simp only [div_div_eq_mul_div, div_one]
  ring

/-- Relate the visual kernel to the normalized real-boundary density. -/
theorem visualPoisson_eq_density (z : ℍ) (ξ : ℝ) :
    visualPoisson z ξ = (Real.pi * (1 + ξ ^ 2)) * halfPlanePoisson z.re z.im ξ := by
  rw [visualPoisson_eq]
  unfold halfPlanePoisson
  field_simp

/-- The vertical ray through w, parametrized by logarithmic height. -/
def verticalHeightRay (w : ℍ) (t : ℝ) : ℍ :=
  ⟨⟨w.re, Real.exp t * w.im⟩, mul_pos (Real.exp_pos t) w.im_pos⟩

theorem verticalHeightRay_zero (w : ℍ) : verticalHeightRay w 0 = w := by
  apply UpperHalfPlane.ext
  apply Complex.ext <;> simp [verticalHeightRay]

/-- The parameter is hyperbolic distance from the starting point for t ≥ 0. -/
theorem verticalHeightRay_dist (w : ℍ) {t : ℝ} (ht : 0 ≤ t) :
    dist w (verticalHeightRay w t) = t := by
  rw [UpperHalfPlane.dist_of_re_eq (show w.re = (verticalHeightRay w t).re from rfl)]
  change dist (Real.log w.im) (Real.log (Real.exp t * w.im)) = t
  rw [Real.log_mul (Real.exp_ne_zero _) w.im_pos.ne', Real.log_exp, Real.dist_eq]
  have he : Real.log w.im - (t + Real.log w.im) = -t := by ring
  rw [he, abs_neg, abs_of_nonneg ht]

/-- The ray from i towards the finite boundary point ξ. -/
def finiteBoundaryRay (ξ t : ℝ) : ℍ :=
  (boundaryPoleMatrix ξ)⁻¹ • verticalHeightRay (boundaryPoleMatrix ξ • UpperHalfPlane.I) t

theorem finiteBoundaryRay_zero (ξ : ℝ) : finiteBoundaryRay ξ 0 = UpperHalfPlane.I := by
  simp [finiteBoundaryRay, verticalHeightRay_zero]

/-- The finite-boundary ray also has unit-speed distance from i. -/
theorem finiteBoundaryRay_dist (ξ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    dist UpperHalfPlane.I (finiteBoundaryRay ξ t) = t := by
  rw [← dist_smul (boundaryPoleMatrix ξ) UpperHalfPlane.I (finiteBoundaryRay ξ t)]
  simpa [finiteBoundaryRay] using verticalHeightRay_dist (boundaryPoleMatrix ξ • UpperHalfPlane.I) ht

/-- The radial exponent is bounded above by the visual Poisson kernel.
The bound holds at every interior point, with no strip or limiting hypothesis. -/
theorem finiteBoundaryRay_poisson_bound (ξ t : ℝ) (z : ℍ) :
    Real.exp (t - dist (finiteBoundaryRay ξ t) z) ≤ visualPoisson z ξ := by
  have h := UpperHalfPlane.im_div_exp_dist_le
    (verticalHeightRay (boundaryPoleMatrix ξ • UpperHalfPlane.I) t) (boundaryPoleMatrix ξ • z)
  have hd : dist (verticalHeightRay (boundaryPoleMatrix ξ • UpperHalfPlane.I) t)
      (boundaryPoleMatrix ξ • z) = dist (finiteBoundaryRay ξ t) z := by
    rw [← dist_smul (boundaryPoleMatrix ξ) (finiteBoundaryRay ξ t) z]
    simp [finiteBoundaryRay]
  rw [hd] at h
  change Real.exp t * (boundaryPoleMatrix ξ • UpperHalfPlane.I).im /
    Real.exp (dist (finiteBoundaryRay ξ t) z) ≤ (boundaryPoleMatrix ξ • z).im at h
  unfold visualPoisson
  rw [Real.exp_sub, le_div_iff₀ (boundaryPoleMatrix ξ • UpperHalfPlane.I).im_pos]
  calc
    _ = Real.exp t * (boundaryPoleMatrix ξ • UpperHalfPlane.I).im /
        Real.exp (dist (finiteBoundaryRay ξ t) z) := by ring
    _ ≤ _ := h

/-- Moving a ray point by at most D costs only exp(2D) in the uniform bound. -/
theorem near_finiteBoundaryRay_poisson_bound (ξ : ℝ) {t D : ℝ} (ht : 0 ≤ t)
    (x z : ℍ) (hx : dist x (finiteBoundaryRay ξ t) ≤ D) :
    Real.exp (dist x UpperHalfPlane.I - dist x z) ≤
      Real.exp (2 * D) * visualPoisson z ξ := by
  have h₁ := dist_triangle x (finiteBoundaryRay ξ t) UpperHalfPlane.I
  have h₂ := dist_triangle (finiteBoundaryRay ξ t) x z
  rw [dist_comm (finiteBoundaryRay ξ t) UpperHalfPlane.I, finiteBoundaryRay_dist ξ ht] at h₁
  rw [dist_comm (finiteBoundaryRay ξ t) x] at h₂
  calc
    Real.exp (dist x UpperHalfPlane.I - dist x z) ≤
        Real.exp (2 * D + (t - dist (finiteBoundaryRay ξ t) z)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (2 * D) * Real.exp (t - dist (finiteBoundaryRay ξ t) z) := Real.exp_add _ _
    _ ≤ Real.exp (2 * D) * visualPoisson z ξ :=
      mul_le_mul_of_nonneg_left (finiteBoundaryRay_poisson_bound ξ t z) (Real.exp_pos _).le

end Singularity
