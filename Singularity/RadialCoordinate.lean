import Singularity.VisualPoissonRay
import Singularity.GeometricStrip

/-!
# A Lipschitz coordinate for nested geodesic half-planes

The coordinate log |z| is a half-difference of two logarithmic heights, hence
is 1-Lipschitz in the hyperbolic metric. Its level sets are semicircles centered
at zero and its value on the vertical axis at height exp(t) is exactly t.
-/

noncomputable section
open scoped MatrixGroups UpperHalfPlane
namespace Singularity

/-- Signed radial coordinate along the oriented axis from zero to infinity. -/
def axisRadialCoordinate (z : ℍ) : ℝ :=
  (Real.log z.im - Real.log (boundaryPoleMatrix 0 • z).im) / 2

/-- The coordinate has the elementary logarithmic-radius formula. -/
theorem axisRadialCoordinate_eq_log_norm (z : ℍ) :
    axisRadialCoordinate z = Real.log ‖(z : ℂ)‖ := by
  have hn : 0 < z.re ^ 2 + z.im ^ 2 := by
    nlinarith [sq_nonneg z.re, sq_pos_of_pos z.im_pos]
  have he : z.re ^ 2 + z.im ^ 2 = ‖(z : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  unfold axisRadialCoordinate
  rw [boundaryPoleMatrix_smul_im]
  simp only [zero_sub, neg_sq]
  rw [Real.log_div z.im_pos.ne' hn.ne', he, Real.log_pow]
  ring

/-- Each coordinate difference is bounded by hyperbolic distance. -/
theorem axisRadialCoordinate_dist_le (z w : ℍ) :
    |axisRadialCoordinate z - axisRadialCoordinate w| ≤ dist z w := by
  have h₁ := UpperHalfPlane.dist_log_im_le z w
  have h₂ := UpperHalfPlane.dist_log_im_le (boundaryPoleMatrix 0 • z) (boundaryPoleMatrix 0 • w)
  rw [dist_smul] at h₂
  rw [Real.dist_eq, abs_le] at h₁ h₂
  unfold axisRadialCoordinate
  rw [abs_le]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- The coordinate equals the unit-speed parameter on the vertical axis. -/
theorem axisRadialCoordinate_axis (t : ℝ) :
    axisRadialCoordinate (verticalHeightRay UpperHalfPlane.I t) = t := by
  rw [axisRadialCoordinate_eq_log_norm]
  have he : ((verticalHeightRay UpperHalfPlane.I t : ℍ) : ℂ) = (Real.exp t : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [verticalHeightRay, Complex.exp_ofReal_re]
  rw [he, norm_mul]
  simp

/-- Hyperbolic balls about axis points lie between explicit coordinate levels. -/
theorem axisRadialCoordinate_near_axis (z : ℍ) (t R : ℝ)
    (hz : dist z (verticalHeightRay UpperHalfPlane.I t) ≤ R) :
    t - R ≤ axisRadialCoordinate z ∧ axisRadialCoordinate z ≤ t + R := by
  have hh := (axisRadialCoordinate_dist_le z (verticalHeightRay UpperHalfPlane.I t)).trans hz
  rw [axisRadialCoordinate_axis, abs_le] at hh
  constructor <;> linarith [hh.1, hh.2]

/-- In every isometric coordinate chart the same finite jump bound controls
the radial coordinate of all vertices of the group orbit. -/
theorem axisRadialCoordinate_jump_bound (Γ : Subgroup SL(2, ℝ)) (s : Finset Γ)
    (q : SL(2, ℝ)) (z : ℍ) (x g : Γ) (hg : g ∈ s) :
    |axisRadialCoordinate (q • ((x*g) • z)) - axisRadialCoordinate (q • (x • z))| ≤
      finiteJumpLengthBound Γ z s := by
  apply (axisRadialCoordinate_dist_le _ _).trans
  rw [dist_smul, mul_smul]
  change dist ((x : SL(2, ℝ)) • (g • z)) ((x : SL(2, ℝ)) • z) ≤ _
  rw [dist_smul, dist_comm]
  exact dist_le_finiteJumpLengthBound Γ z s hg

end Singularity
