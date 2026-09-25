import Singularity.AxisBallSeparation

/-!
# Endpoint-pair geometry for balls near an axis

The estimates keep track of the error when axis centers are replaced by nearby
orbit centers. They supply triangle excess and both distance bounds needed by
the finite geometric entrance iteration.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Distances between points near two axis positions differ from their
parameter separation by at most the sum of the two approximation radii. -/
theorem axis_nearby_distance_bounds (g : SL(2, ℝ)) (a b r₁ r₂ : ℝ) (x y : ℍ)
    (hab : a ≤ b)
    (hx : dist x (g • verticalHeightRay UpperHalfPlane.I a) ≤ r₁)
    (hy : dist y (g • verticalHeightRay UpperHalfPlane.I b) ≤ r₂) :
    b - a - r₁ - r₂ ≤ dist x y ∧ dist x y ≤ b - a + r₁ + r₂ := by
  have hd : dist (g • verticalHeightRay UpperHalfPlane.I a)
      (g • verticalHeightRay UpperHalfPlane.I b) = b - a := by
    rw [dist_smul, verticalHeightRay_dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  have hlo := dist_triangle4 (g • verticalHeightRay UpperHalfPlane.I a) x y
    (g • verticalHeightRay UpperHalfPlane.I b)
  have hhi := dist_triangle4 x (g • verticalHeightRay UpperHalfPlane.I a)
    (g • verticalHeightRay UpperHalfPlane.I b) y
  rw [hd, dist_comm (g • verticalHeightRay UpperHalfPlane.I a) x] at hlo
  rw [hd, dist_comm (g • verticalHeightRay UpperHalfPlane.I b) y] at hhi
  constructor <;> linarith

/-- Axis-ball triangle excess is stable when its intermediate center is
approximated within E by an arbitrary point. -/
theorem axis_balls_excess_near_center (g : SL(2, ℝ)) (a c b r₁ r₂ E : ℝ) (x y o : ℍ)
    (ha : a + 1 ≤ c) (hb : c + 1 ≤ b)
    (hx : dist x (g • verticalHeightRay UpperHalfPlane.I a) ≤ r₁)
    (hy : dist y (g • verticalHeightRay UpperHalfPlane.I b) ≤ r₂)
    (hm₁ : r₁ + Real.log 64 ≤ c - a) (hm₂ : r₂ + Real.log 64 ≤ b - c)
    (ho : dist (g • verticalHeightRay UpperHalfPlane.I c) o ≤ E) :
    dist x o + dist y o - dist x y ≤ 2 * Real.log 32 + 2 * E :=
  triangle_excess_change_center x y (g • verticalHeightRay UpperHalfPlane.I c) o
    (2 * Real.log 32) E (axis_balls_excess g a c b r₁ r₂ x y ha hb hx hy hm₁ hm₂) ho

/-- Full endpoint-pair bounds for two orbit balls whose centers approximate
opposite axis positions; the intermediate orbit center may also be approximate. -/
theorem orbit_axis_ball_pair_geometry (Γ : Subgroup SL(2, ℝ))
    (g : SL(2, ℝ)) (a c b r₁ r₂ E : ℝ) (v u w x y : Γ)
    (ha : a + 1 ≤ c) (hb : c + 1 ≤ b)
    (hv : dist (v • UpperHalfPlane.I) (g • verticalHeightRay UpperHalfPlane.I a) ≤ E)
    (hu : dist (u • UpperHalfPlane.I) (g • verticalHeightRay UpperHalfPlane.I c) ≤ E)
    (hw : dist (w • UpperHalfPlane.I) (g • verticalHeightRay UpperHalfPlane.I b) ≤ E)
    (hx : dist (x • UpperHalfPlane.I) (v • UpperHalfPlane.I) ≤ r₁)
    (hy : dist (y • UpperHalfPlane.I) (w • UpperHalfPlane.I) ≤ r₂)
    (hm₁ : r₁ + E + Real.log 64 ≤ c - a)
    (hm₂ : r₂ + E + Real.log 64 ≤ b - c) :
    b - a - r₁ - r₂ - 2 * E ≤ dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ∧
    dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ b - a + r₁ + r₂ + 2 * E ∧
    dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
      dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
      dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ 2 * Real.log 32 + 2 * E := by
  have hx' : dist (x • UpperHalfPlane.I) (g • verticalHeightRay UpperHalfPlane.I a) ≤ r₁ + E :=
    (dist_triangle _ (v • UpperHalfPlane.I) _).trans (add_le_add hx hv)
  have hy' : dist (y • UpperHalfPlane.I) (g • verticalHeightRay UpperHalfPlane.I b) ≤ r₂ + E :=
    (dist_triangle _ (w • UpperHalfPlane.I) _).trans (add_le_add hy hw)
  have hd := axis_nearby_distance_bounds g a b (r₁ + E) (r₂ + E)
    (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) (by linarith) hx' hy'
  refine ⟨by linarith [hd.1], by linarith [hd.2], ?_⟩
  exact axis_balls_excess_near_center g a c b (r₁ + E) (r₂ + E) E
    (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) (u • UpperHalfPlane.I)
    ha hb hx' hy' hm₁ hm₂ (by simpa only [dist_comm] using hu)

end Singularity
