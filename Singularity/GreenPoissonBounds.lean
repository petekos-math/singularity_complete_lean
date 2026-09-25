import Singularity.VisualPoissonDecay
import Singularity.GeometricStrip

/-!
# Green quotient bounds from the hyperbolic distance comparison

The uniform two-sided Green-versus-distance comparison is an explicit hypothesis
here. From it we prove the visual Poisson bounds for all interior targets and
then the exponential bounds on actual cyclic group orbits. No boundary-limit
or coordinate-envelope hypothesis is used to prove these estimates.
-/

noncomputable section
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- The uniform distance comparison that must ultimately follow from rigidity. -/
def GreenDistanceComparison (Γ : Subgroup SL(2, ℝ)) (s : Finset Γ) (μ : Γ → ℝ) (C : ℝ) : Prop :=
  ∀ x y : Γ,
    C⁻¹ * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) ≤ walkGreen s μ x y ∧
    walkGreen s μ x y ≤ C * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I))

/-- A lower denominator estimate and upper numerator estimate give the distance difference. -/
theorem quotient_le_exp_distance_difference {a b C p q : ℝ} (hC : 0 < C)
    (hb : C⁻¹ * Real.exp (-p) ≤ b) (ha : a ≤ C * Real.exp (-q)) :
    a / b ≤ C ^ 2 * Real.exp (p - q) := by
  have hlow : 0 < C⁻¹ * Real.exp (-p) := mul_pos (inv_pos.mpr hC) (Real.exp_pos _)
  calc
    a / b ≤ (C * Real.exp (-q)) / b := div_le_div_of_nonneg_right ha (hlow.trans_le hb).le
    _ ≤ (C * Real.exp (-q)) / (C⁻¹ * Real.exp (-p)) :=
      div_le_div_of_nonneg_left (mul_pos hC (Real.exp_pos _)).le hlow hb
    _ = C ^ 2 * Real.exp (p - q) := by
      rw [Real.exp_sub, Real.exp_neg, Real.exp_neg]
      field_simp

variable (Γ : Subgroup SL(2, ℝ)) (s : Finset Γ) (μ : Γ → ℝ) {C : ℝ}
  (hC : 0 < C) (hcmp : GreenDistanceComparison Γ s μ C)

include hC hcmp in
/-- The comparison gives strict positivity of all denominators used here. -/
theorem GreenDistanceComparison_positive (x y : Γ) : 0 < walkGreen s μ x y :=
  lt_of_lt_of_le (mul_pos (inv_pos.mpr hC) (Real.exp_pos _)) (hcmp x y).1

include hC hcmp in
/-- Uniform row bound near a finite-boundary ray, valid at every group vertex. -/
theorem greenDistance_row_poisson_bound (ξ : ℝ) {t D : ℝ} (ht : 0 ≤ t) (x g : Γ)
    (hx : dist (x • UpperHalfPlane.I) (finiteBoundaryRay ξ t) ≤ D) :
    walkGreen s μ x g / walkGreen s μ x 1 ≤
      (C ^ 2 * Real.exp (2 * D)) * visualPoisson (g • UpperHalfPlane.I) ξ := by
  have hr := quotient_le_exp_distance_difference hC (hcmp x 1).1 (hcmp x g).2
  simp only [one_smul] at hr
  exact hr.trans ((mul_le_mul_of_nonneg_left
    (near_finiteBoundaryRay_poisson_bound ξ ht (x • UpperHalfPlane.I) (g • UpperHalfPlane.I) hx)
    (sq_nonneg C)).trans_eq (mul_assoc _ _ _).symm)

include hC hcmp in
/-- The same comparison bounds columns; symmetry of the random walk is unnecessary. -/
theorem greenDistance_column_poisson_bound (ξ : ℝ) {t D : ℝ} (ht : 0 ≤ t) (y g : Γ)
    (hy : dist (y • UpperHalfPlane.I) (finiteBoundaryRay ξ t) ≤ D) :
    walkGreen s μ g y / walkGreen s μ 1 y ≤
      (C ^ 2 * Real.exp (2 * D)) * visualPoisson (g • UpperHalfPlane.I) ξ := by
  have hr := quotient_le_exp_distance_difference hC (hcmp 1 y).1 (hcmp g y).2
  simp only [one_smul] at hr
  rw [dist_comm UpperHalfPlane.I (y • UpperHalfPlane.I),
    dist_comm (g • UpperHalfPlane.I) (y • UpperHalfPlane.I)] at hr
  exact hr.trans ((mul_le_mul_of_nonneg_left
    (near_finiteBoundaryRay_poisson_bound ξ ht (y • UpperHalfPlane.I) (g • UpperHalfPlane.I) hy)
    (sq_nonneg C)).trans_eq (mul_assoc _ _ _).symm)

include hC hcmp in
/-- Actual cyclic row quotients have a uniform exponential envelope. -/
theorem greenDistance_row_orbit_bound (a b : Γ) {τ ξ : ℝ}
    (ha : (a : SL(2, ℝ)) = dilationMatrix τ) (hτ : 0 < τ) (hξ : ξ ≠ 0)
    {t D : ℝ} (ht : 0 ≤ t) (x : Γ)
    (hx : dist (x • UpperHalfPlane.I) (finiteBoundaryRay ξ t) ≤ D) (n : ℤ) :
    walkGreen s μ x (a ^ n * b) / walkGreen s μ x 1 ≤
      ((C ^ 2 * Real.exp (2 * D)) * visualPoissonEnvelope (b • UpperHalfPlane.I) ξ) *
        Real.exp (-τ * |(n : ℝ)|) := by
  have h := greenDistance_row_poisson_bound Γ s μ hC hcmp ξ ht x (a ^ n * b) hx
  rw [mul_smul, subgroup_dilation_zpow_smul Γ a ha] at h
  exact h.trans ((mul_le_mul_of_nonneg_left
    (visualPoisson_zpow_decay (b • UpperHalfPlane.I) hξ hτ n) (by positivity)).trans_eq
      (mul_assoc _ _ _).symm)

include hC hcmp in
/-- Actual cyclic column quotients have the corresponding exponential envelope. -/
theorem greenDistance_column_orbit_bound (a b : Γ) {τ ξ : ℝ}
    (ha : (a : SL(2, ℝ)) = dilationMatrix τ) (hτ : 0 < τ) (hξ : ξ ≠ 0)
    {t D : ℝ} (ht : 0 ≤ t) (y : Γ)
    (hy : dist (y • UpperHalfPlane.I) (finiteBoundaryRay ξ t) ≤ D) (n : ℤ) :
    walkGreen s μ (a ^ n * b) y / walkGreen s μ 1 y ≤
      ((C ^ 2 * Real.exp (2 * D)) * visualPoissonEnvelope (b • UpperHalfPlane.I) ξ) *
        Real.exp (-τ * |(n : ℝ)|) := by
  have h := greenDistance_column_poisson_bound Γ s μ hC hcmp ξ ht y (a ^ n * b) hy
  rw [mul_smul, subgroup_dilation_zpow_smul Γ a ha] at h
  exact h.trans ((mul_le_mul_of_nonneg_left
    (visualPoisson_zpow_decay (b • UpperHalfPlane.I) hξ hτ n) (by positivity)).trans_eq
      (mul_assoc _ _ _).symm)

include hC hcmp in
/-- Complex norms of the positive normalized Green entries are the real ratios. -/
theorem greenDistance_complex_quotient_norm (x y u v : Γ) :
    ‖(walkGreen s μ x y : ℂ) / (walkGreen s μ u v : ℂ)‖ =
      walkGreen s μ x y / walkGreen s μ u v := by
  rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (GreenDistanceComparison_positive Γ s μ hC hcmp x y)
      (GreenDistanceComparison_positive Γ s μ hC hcmp u v))]

end Singularity
