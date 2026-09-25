import Singularity.ProjectiveActions
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Lifting projective Fuchsian subgroups to SL(2,ℝ)

Take the full inverse image under the actual projective projection. The lift
maps onto the projective subgroup, preserves every geometric orbit, preserves
compactness of the hyperbolic orbit quotient, and is discrete whenever the
projective subgroup is discrete. The central sign is kept explicitly.
-/

noncomputable section
open Set OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- Full special-linear inverse image of a projective subgroup. -/
def projectiveSubgroupLift (Γ : Subgroup PSL(2, ℝ)) : Subgroup SL(2, ℝ) :=
  Γ.comap slTwoProjective

/-- Projection from the lifted subgroup to the original projective group. -/
def projectiveLiftProjection (Γ : Subgroup PSL(2, ℝ)) : projectiveSubgroupLift Γ →* Γ where
  toFun g := ⟨slTwoProjective g, g.property⟩
  map_one' := Subtype.ext (map_one slTwoProjective)
  map_mul' g h := Subtype.ext (map_mul slTwoProjective (g : SL(2, ℝ)) (h : SL(2, ℝ)))

theorem projectiveLiftProjection_surjective (Γ : Subgroup PSL(2, ℝ)) :
    Function.Surjective (projectiveLiftProjection Γ) := by
  intro g
  obtain ⟨h, hh⟩ := slTwoProjective_surjective (g : PSL(2, ℝ))
  refine ⟨⟨h, ?_⟩, Subtype.ext hh⟩
  change slTwoProjective h ∈ Γ
  rw [hh]
  exact g.property

theorem continuous_projectiveLiftProjection (Γ : Subgroup PSL(2, ℝ)) :
    Continuous (projectiveLiftProjection Γ) :=
  (continuous_slTwoProjective.comp continuous_subtype_val).subtype_mk _

/-- Both lifted and projective actions are literally the same at each element. -/
theorem projectiveLiftProjection_smul_boundary (Γ : Subgroup PSL(2, ℝ))
    (g : projectiveSubgroupLift Γ) (x : OnePoint ℝ) :
    projectiveLiftProjection Γ g • x = g • x := rfl

theorem projectiveLiftProjection_smul_hyperbolic (Γ : Subgroup PSL(2, ℝ))
    (g : projectiveSubgroupLift Γ) (z : ℍ) :
    projectiveLiftProjection Γ g • z = g • z := rfl

/-- The lift has exactly the same boundary orbits. -/
theorem projectiveSubgroupLift_boundary_orbit (Γ : Subgroup PSL(2, ℝ)) (x : OnePoint ℝ) :
    MulAction.orbit (projectiveSubgroupLift Γ) x = MulAction.orbit Γ x := by
  ext y
  rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨projectiveLiftProjection Γ g, hg⟩
  · rintro ⟨g, hg⟩
    obtain ⟨h, rfl⟩ := projectiveLiftProjection_surjective Γ g
    exact ⟨h, hg⟩

/-- The lift has exactly the same hyperbolic orbits. -/
theorem projectiveSubgroupLift_hyperbolic_orbit (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    MulAction.orbit (projectiveSubgroupLift Γ) z = MulAction.orbit Γ z := by
  ext w
  rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨projectiveLiftProjection Γ g, hg⟩
  · rintro ⟨g, hg⟩
    obtain ⟨h, rfl⟩ := projectiveLiftProjection_surjective Γ g
    exact ⟨h, hg⟩

theorem projectiveSubgroupLift_hyperbolic_orbitRel (Γ : Subgroup PSL(2, ℝ)) :
    MulAction.orbitRel (projectiveSubgroupLift Γ) ℍ = MulAction.orbitRel Γ ℍ := by
  apply Setoid.ext
  intro z w
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, projectiveSubgroupLift_hyperbolic_orbit]

/-- Cocompactness is unchanged because the geometric orbit relations coincide. -/
theorem projectiveSubgroupLift_cocompact (Γ : Subgroup PSL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    CompactSpace (Quotient (MulAction.orbitRel (projectiveSubgroupLift Γ) ℍ)) := by
  rw [projectiveSubgroupLift_hyperbolic_orbitRel]
  infer_instance

/-- Infinite boundary orbits are unchanged by the projective lift. -/
theorem projectiveSubgroupLift_infinite_orbits (Γ : Subgroup PSL(2, ℝ))
    (h : ∀ x : OnePoint ℝ, (MulAction.orbit Γ x).Infinite) :
    ∀ x : OnePoint ℝ, (MulAction.orbit (projectiveSubgroupLift Γ) x).Infinite := by
  intro x
  rw [projectiveSubgroupLift_boundary_orbit]
  exact h x

/-- The other element of the central fibre belongs to every full lift. -/
def projectiveLiftSign (Γ : Subgroup PSL(2, ℝ)) : projectiveSubgroupLift Γ :=
  ⟨-1, by
    change slTwoProjective (-1) ∈ Γ
    rw [(slTwoProjective_eq_one_iff _).mpr (Or.inr rfl)]
    exact Γ.one_mem⟩

theorem projectiveLiftSign_ne_one (Γ : Subgroup PSL(2, ℝ)) : projectiveLiftSign Γ ≠ 1 := by
  intro h
  exact slTwo_neg_one_ne_one (congrArg Subtype.val h)

theorem projectiveLiftSign_square (Γ : Subgroup PSL(2, ℝ)) : projectiveLiftSign Γ ^ 2 = 1 := by
  apply Subtype.ext
  simp [projectiveLiftSign]

/-- The projection has exactly the two-element central kernel. -/
theorem projectiveLiftProjection_eq_one_iff (Γ : Subgroup PSL(2, ℝ))
    (g : projectiveSubgroupLift Γ) :
    projectiveLiftProjection Γ g = 1 ↔ g = 1 ∨ g = projectiveLiftSign Γ := by
  constructor
  · intro h
    have hh := (slTwoProjective_eq_one_iff g).mp (congrArg Subtype.val h)
    exact hh.elim (fun h₁ => Or.inl (Subtype.ext h₁)) (fun h₁ => Or.inr (Subtype.ext h₁))
  · rintro (rfl | rfl)
    · exact map_one _
    · apply Subtype.ext
      exact (slTwoProjective_eq_one_iff _).mpr (Or.inr rfl)

/-- A discrete projective subgroup has a discrete full special-linear lift. -/
theorem projectiveSubgroupLift_discrete (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] :
    DiscreteTopology (projectiveSubgroupLift Γ) := by
  have hU : IsOpen {g : projectiveSubgroupLift Γ | projectiveLiftProjection Γ g = 1} :=
    (isOpen_discrete ({1} : Set Γ)).preimage (continuous_projectiveLiftProjection Γ)
  have hV : IsOpen {g : projectiveSubgroupLift Γ | (g : SL(2, ℝ)) ≠ -1} :=
    isClosed_singleton.isOpen_compl.preimage continuous_subtype_val
  have he : {g : projectiveSubgroupLift Γ | projectiveLiftProjection Γ g = 1} ∩
      {g : projectiveSubgroupLift Γ | (g : SL(2, ℝ)) ≠ -1} = {1} := by
    ext g
    constructor
    · rintro ⟨hg, hn⟩
      rcases (projectiveLiftProjection_eq_one_iff Γ g).mp hg with rfl | rfl
      · rfl
      · exact (hn rfl).elim
    · rintro rfl
      exact ⟨map_one _, Ne.symm slTwo_neg_one_ne_one⟩
  exact discreteTopology_of_isOpen_singleton_one (he ▸ hU.inter hV)

end Singularity
