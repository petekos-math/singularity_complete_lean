import Singularity.SLTwoProjective
import Singularity.SLTwoHaar

/-!
# Actual PSL(2,ℝ) actions on the boundary and hyperbolic plane

Both actions descend through the proved trivial action of the center. The
canonical projection intertwines them exactly, and every projective element
acts continuously. No choice of a matrix lift is part of either action.
-/

noncomputable section
open Set OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- The projective boundary action as a permutation representation. -/
def projectiveBoundaryPerm : PSL(2, ℝ) →* Equiv.Perm (OnePoint ℝ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℝ))
    (MulAction.toPermHom SL(2, ℝ) (OnePoint ℝ)) (by
      intro g hg
      apply Equiv.ext
      exact slTwo_center_boundary_fix g hg)

instance projectiveBoundaryAction : MulAction PSL(2, ℝ) (OnePoint ℝ) :=
  MulAction.compHom (OnePoint ℝ) projectiveBoundaryPerm

/-- Boundary action is independent of the central sign of a matrix lift. -/
theorem slTwoProjective_smul_boundary (g : SL(2, ℝ)) (x : OnePoint ℝ) :
    slTwoProjective g • x = g • x := rfl

/-- The projective hyperbolic action as a permutation representation. -/
def projectiveHyperbolicPerm : PSL(2, ℝ) →* Equiv.Perm ℍ :=
  QuotientGroup.lift (Subgroup.center SL(2, ℝ))
    (MulAction.toPermHom SL(2, ℝ) ℍ) (by
      intro g hg
      apply Equiv.ext
      exact slTwo_center_hyperbolic_fix g hg)

instance projectiveHyperbolicAction : MulAction PSL(2, ℝ) ℍ :=
  MulAction.compHom ℍ projectiveHyperbolicPerm

/-- The canonical projection intertwines the hyperbolic actions exactly. -/
theorem slTwoProjective_smul_hyperbolic (g : SL(2, ℝ)) (z : ℍ) :
    slTwoProjective g • z = g • z := rfl

instance projectiveBoundaryContinuous : ContinuousConstSMul PSL(2, ℝ) (OnePoint ℝ) where
  continuous_const_smul q := by
    obtain ⟨g, rfl⟩ := slTwoProjective_surjective q
    exact continuous_const_smul g

instance projectiveHyperbolicContinuous : ContinuousConstSMul PSL(2, ℝ) ℍ where
  continuous_const_smul q := by
    obtain ⟨g, rfl⟩ := slTwoProjective_surjective q
    exact continuous_const_smul g

instance projectiveSubgroupBoundaryContinuous (Γ : Subgroup PSL(2, ℝ)) :
    ContinuousConstSMul Γ (OnePoint ℝ) where
  continuous_const_smul g := continuous_const_smul (g : PSL(2, ℝ))

instance projectiveSubgroupHyperbolicContinuous (Γ : Subgroup PSL(2, ℝ)) :
    ContinuousConstSMul Γ ℍ where
  continuous_const_smul g := continuous_const_smul (g : PSL(2, ℝ))

/-- A projective isometry preserves the hyperbolic distance. -/
theorem projective_dist_smul (g : PSL(2, ℝ)) (z w : ℍ) :
    dist (g • z) (g • w) = dist z w := by
  obtain ⟨g, rfl⟩ := slTwoProjective_surjective g
  exact dist_smul g z w

/-- The projective hyperbolic action is transitive. -/
theorem projectiveHyperbolic_pretransitive : MulAction.IsPretransitive PSL(2, ℝ) ℍ := by
  constructor
  intro z w
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) z w
  exact ⟨slTwoProjective g, hg⟩

end Singularity
