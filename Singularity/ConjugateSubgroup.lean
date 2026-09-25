import Singularity.HyperbolicTraceSquare
import Singularity.CompactBoundary
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Normalizing a Fuchsian subgroup by conjugation

The subgroup B⁻¹ Γ B has the same topological group structure as Γ. Its
hyperbolic-plane and compact-boundary actions are conjugate by B. A hyperbolic
trace element therefore supplies a positive dilation inside an actual discrete
conjugate subgroup.
-/

noncomputable section
open Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- The subgroup B⁻¹ Γ B, expressed as a preimage under conjugation by B. -/
def conjugateSubgroup (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ)) : Subgroup SL(2, ℝ) :=
  Γ.comap (MulAut.conj B).toMonoidHom

/-- Undoing the change of coordinates is a group isomorphism. -/
def conjugateSubgroupEquiv (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ)) :
    conjugateSubgroup Γ B ≃* Γ where
  toFun a := ⟨B * a * B⁻¹, a.property⟩
  invFun g := ⟨B⁻¹ * g * B, by
    change B * (B⁻¹ * (g : SL(2, ℝ)) * B) * B⁻¹ ∈ Γ
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using g.property⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv g := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

/-- The coordinate isomorphism is a homeomorphism for the induced group topologies. -/
def conjugateSubgroupHomeomorph (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ)) :
    conjugateSubgroup Γ B ≃ₜ Γ where
  toEquiv := (conjugateSubgroupEquiv Γ B).toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

/-- Conjugation preserves discreteness of the subgroup. -/
theorem conjugateSubgroup_discrete (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (B : SL(2, ℝ)) : DiscreteTopology (conjugateSubgroup Γ B) :=
  (conjugateSubgroupHomeomorph Γ B).symm.discreteTopology

/-- The real compact-boundary actions are conjugate under the same matrix. -/
theorem conjugateSubgroup_boundary_action (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ))
    (a : conjugateSubgroup Γ B) (p : OnePoint ℝ) :
    B • (a • p) = conjugateSubgroupEquiv Γ B a • (B • p) := by
  change B • ((a : SL(2, ℝ)) • p) = (B * a * B⁻¹) • (B • p)
  simp only [mul_smul, inv_smul_smul]

/-- The hyperbolic-plane actions are conjugate under the same matrix. -/
theorem conjugateSubgroup_hyperbolic_action (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ))
    (a : conjugateSubgroup Γ B) (z : ℍ) :
    B • (a • z) = conjugateSubgroupEquiv Γ B a • (B • z) := by
  change B • ((a : SL(2, ℝ)) • z) = (B * a * B⁻¹) • (B • z)
  simp only [mul_smul, inv_smul_smul]

/-- A positive diagonal element belongs to the normalized subgroup whenever its
conjugate belongs to the original subgroup. -/
theorem dilationMatrix_mem_conjugateSubgroup (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ))
    (a : Γ) (t : ℝ) (ha : (a : SL(2, ℝ)) = B * dilationMatrix t * B⁻¹) :
    dilationMatrix t ∈ conjugateSubgroup Γ B := by
  change B * dilationMatrix t * B⁻¹ ∈ Γ
  rw [← ha]
  exact a.property

/-- A hyperbolic trace supplies a discrete normalized subgroup containing a positive dilation. -/
theorem exists_discrete_normalized_subgroup (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (a : Γ) (htrace : 2 < |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1|) :
    ∃ (B : SL(2, ℝ)) (t : ℝ), 0 < t ∧ DiscreteTopology (conjugateSubgroup Γ B) ∧
      dilationMatrix t ∈ conjugateSubgroup Γ B := by
  obtain ⟨t, ht, B, hB⟩ := exists_dilation_conjugacy_of_abs_trace (a : SL(2, ℝ)) htrace
  exact ⟨B, t, ht, conjugateSubgroup_discrete Γ B,
    dilationMatrix_mem_conjugateSubgroup Γ B (a ^ 2) t hB⟩

/-- Conjugation carries each compact-boundary orbit onto the corresponding original orbit. -/
theorem conjugateSubgroup_boundary_orbit (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ))
    (p : OnePoint ℝ) :
    (fun x : OnePoint ℝ => B • x) '' MulAction.orbit (conjugateSubgroup Γ B) p =
      MulAction.orbit Γ (B • p) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨conjugateSubgroupEquiv Γ B a, (conjugateSubgroup_boundary_action Γ B a p).symm⟩
  · rintro ⟨g, rfl⟩
    let a := (conjugateSubgroupEquiv Γ B).symm g
    refine ⟨a • p, ⟨a, rfl⟩, ?_⟩
    change B • (a • p) = g • (B • p)
    rw [conjugateSubgroup_boundary_action]
    exact congrArg (fun h : Γ => h • (B • p)) ((conjugateSubgroupEquiv Γ B).apply_symm_apply g)

/-- Infinitude of boundary orbits is preserved under the change of coordinates. -/
theorem conjugateSubgroup_boundary_orbit_infinite_iff (Γ : Subgroup SL(2, ℝ)) (B : SL(2, ℝ))
    (p : OnePoint ℝ) :
    (MulAction.orbit (conjugateSubgroup Γ B) p).Infinite ↔
      (MulAction.orbit Γ (B • p)).Infinite := by
  rw [← conjugateSubgroup_boundary_orbit]
  exact (Set.infinite_image_iff (MulAction.injective B).injOn).symm

end Singularity
