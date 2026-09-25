import Singularity.BoundaryPairTransitivity
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The real special-linear center and projective projection

The kernel of SL(2,ℝ) → PSL(2,ℝ) is exactly {I, -I}. Both kernel elements
act trivially on the real projective boundary and the upper half-plane.
-/

noncomputable section
open Set OnePoint
open scoped MatrixGroups UpperHalfPlane Classical

namespace Singularity

/-- The real special-linear center contains exactly the two scalar signs. -/
theorem slTwo_mem_center_iff (g : SL(2, ℝ)) :
    g ∈ Subgroup.center SL(2, ℝ) ↔ g = 1 ∨ g = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, he⟩
    have hr' : r ^ 2 = 1 := by simpa using hr
    rcases sq_eq_one_iff.mp hr' with rfl | rfl
    · left
      apply Subtype.ext
      simpa using he.symm
    · right
      apply Subtype.ext
      rw [← he]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.scalar]
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨-1, by simp, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.scalar]

/-- The two real scalar signs are distinct. -/
theorem slTwo_neg_one_ne_one : (-1 : SL(2, ℝ)) ≠ 1 := by
  intro h
  have hh := congrArg (fun g : SL(2, ℝ) => g 0 0) h
  norm_num at hh

theorem slTwo_center_finite : (Subgroup.center SL(2, ℝ) : Set SL(2, ℝ)).Finite := by
  have he : (Subgroup.center SL(2, ℝ) : Set SL(2, ℝ)) = {1, -1} := by
    ext g
    simp only [SetLike.mem_coe, slTwo_mem_center_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [he]
  exact Set.toFinite _

theorem slTwo_center_isClosed : IsClosed (Subgroup.center SL(2, ℝ) : Set SL(2, ℝ)) :=
  slTwo_center_finite.isClosed

/-- The canonical real projective projection, as a group homomorphism. -/
def slTwoProjective : SL(2, ℝ) →* PSL(2, ℝ) := QuotientGroup.mk' _

theorem slTwoProjective_surjective : Function.Surjective slTwoProjective :=
  QuotientGroup.mk'_surjective _

theorem continuous_slTwoProjective : Continuous slTwoProjective := QuotientGroup.continuous_mk

theorem slTwoProjective_eq_one_iff (g : SL(2, ℝ)) :
    slTwoProjective g = 1 ↔ g = 1 ∨ g = -1 :=
  (QuotientGroup.eq_one_iff g).trans (slTwo_mem_center_iff g)

/-- The boundary action kills the entire projective kernel. -/
theorem slTwo_center_boundary_fix (g : SL(2, ℝ)) (hg : g ∈ Subgroup.center SL(2, ℝ))
    (x : OnePoint ℝ) : g • x = x := by
  rcases (slTwo_mem_center_iff g).mp hg with rfl | rfl
  · exact one_smul _ _
  · cases x with
    | infty => simp [compactBoundary_smul_infty_formula]
    | coe x => simp [compactBoundary_smul_coe_formula]

/-- The hyperbolic action also kills the entire projective kernel. -/
theorem slTwo_center_hyperbolic_fix (g : SL(2, ℝ)) (hg : g ∈ Subgroup.center SL(2, ℝ))
    (z : ℍ) : g • z = z := by
  rcases (slTwo_mem_center_iff g).mp hg with rfl | rfl
  · exact one_smul _ _
  · apply UpperHalfPlane.ext
    simp [UpperHalfPlane.coe_specialLinearGroup_apply]

end Singularity
