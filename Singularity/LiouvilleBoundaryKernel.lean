import Singularity.BoundaryCircle

/-!
# The explicit Liouville kernel on compact boundary pairs

Relative to the visual probability at i in each variable, the kernel is
4π² divided by squared chordal distance in Cayley circle coordinates. This
normalization yields dx dy/(x-y)² in the finite real chart.
-/

noncomputable section
open Set OnePoint
open scoped Classical Topology

namespace Singularity

/-- The Liouville density relative to the two visual probabilities at i. -/
def liouvilleBoundaryKernel (p : BoundaryPair) : ℝ :=
  4 * Real.pi ^ 2 / dist (boundaryCircle p.val.1) (boundaryCircle p.val.2) ^ 2

/-- Distinctness gives a strictly positive denominator. -/
theorem boundaryPair_circle_dist_pos (p : BoundaryPair) :
    0 < dist (boundaryCircle p.val.1) (boundaryCircle p.val.2) :=
  dist_pos.mpr (fun h => p.property (boundaryCircle_injective h))

theorem liouvilleBoundaryKernel_pos (p : BoundaryPair) : 0 < liouvilleBoundaryKernel p := by
  unfold liouvilleBoundaryKernel
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
    (sq_pos_of_pos (boundaryPair_circle_dist_pos p))

/-- The kernel is continuous on all distinct compact endpoints, including infinity. -/
theorem continuous_liouvilleBoundaryKernel : Continuous liouvilleBoundaryKernel := by
  apply Continuous.div continuous_const
    (((continuous_boundaryCircle.comp (continuous_fst.comp continuous_subtype_val)).dist
      (continuous_boundaryCircle.comp (continuous_snd.comp continuous_subtype_val))).pow 2)
  intro p
  exact (sq_pos_of_pos (boundaryPair_circle_dist_pos p)).ne'

/-- Regard two distinct real numbers as a pair of compact boundary points. -/
def finiteBoundaryPair (x y : ℝ) (hxy : x ≠ y) : BoundaryPair :=
  ⟨((x : OnePoint ℝ), (y : OnePoint ℝ)), fun h => hxy (OnePoint.coe_injective h)⟩

/-- The explicit real-chart value of the compact Liouville kernel. -/
theorem liouvilleBoundaryKernel_finite (x y : ℝ) (hxy : x ≠ y) :
    liouvilleBoundaryKernel (finiteBoundaryPair x y hxy) =
      Real.pi ^ 2 * (x ^ 2 + 1) * (y ^ 2 + 1) / (x - y) ^ 2 := by
  change 4 * Real.pi ^ 2 / dist (boundaryCircle (x : OnePoint ℝ)) (boundaryCircle (y : OnePoint ℝ)) ^ 2 = _
  rw [boundaryCircle_dist_sq]
  have hx : x ^ 2 + 1 ≠ 0 := by positivity
  have hy : y ^ 2 + 1 ≠ 0 := by positivity
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
  field_simp

/-- Multiplying by the two visual densities produces the classical Liouville density. -/
theorem liouvilleBoundaryKernel_poisson_density (x y : ℝ) (hxy : x ≠ y) :
    halfPlanePoisson 0 1 x * halfPlanePoisson 0 1 y *
      liouvilleBoundaryKernel (finiteBoundaryPair x y hxy) = 1 / (x - y) ^ 2 := by
  rw [liouvilleBoundaryKernel_finite]
  unfold halfPlanePoisson
  simp only [sub_zero, one_pow]
  have hx : x ^ 2 + 1 ≠ 0 := by positivity
  have hy : y ^ 2 + 1 ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero]

end Singularity
