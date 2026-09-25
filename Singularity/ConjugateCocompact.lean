import Singularity.ConjugateSubgroup
import Singularity.CocompactRayApproximation

/-!
# Cocompactness under subgroup normalization

A compact orbit cover is transported by the ambient hyperbolic isometry. Its
image covers the normalized quotient, proving compactness without an assumed
identification of quotient spaces.
-/

noncomputable section
open Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- Conjugating the subgroup preserves compactness of the actual hyperbolic orbit quotient. -/
theorem conjugateSubgroup_cocompact (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] (B : SL(2, ℝ)) :
    CompactSpace (Quotient (MulAction.orbitRel (conjugateSubgroup Γ B) ℍ)) := by
  obtain ⟨K, hK, hcover⟩ := exists_compact_orbit_cover Γ
  let K' : Set ℍ := (fun z : ℍ => B⁻¹ • z) '' K
  have hK' : IsCompact K' := hK.image (continuous_const_smul B⁻¹)
  let π : ℍ → Quotient (MulAction.orbitRel (conjugateSubgroup Γ B) ℍ) := Quotient.mk _
  have hπ : Continuous π := continuous_quotient_mk'
  have hsurj : π '' K' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h z =>
      obtain ⟨g, hg⟩ := hcover (B • z)
      let a := (conjugateSubgroupEquiv Γ B).symm g
      have he : conjugateSubgroupEquiv Γ B a = g :=
        (conjugateSubgroupEquiv Γ B).apply_symm_apply g
      have him : B • (a • z) ∈ K := by
        rw [conjugateSubgroup_hyperbolic_action, he]
        exact hg
      refine ⟨a • z, ⟨B • (a • z), him, inv_smul_smul B (a • z)⟩, ?_⟩
      apply Quotient.sound
      exact MulAction.orbitRel_apply.mpr ⟨a, rfl⟩
  exact isCompact_univ_iff.mp (hsurj ▸ hK'.image hπ)

/-- A cocompact discrete subgroup with a hyperbolic trace admits coordinates in which
all the established strip-geometry hypotheses concerning the group are preserved. -/
theorem exists_cocompact_normalized_subgroup (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (a : Γ) (htrace : 2 < |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1|) :
    ∃ (B : SL(2, ℝ)) (t : ℝ), 0 < t ∧ DiscreteTopology (conjugateSubgroup Γ B) ∧
      CompactSpace (Quotient (MulAction.orbitRel (conjugateSubgroup Γ B) ℍ)) ∧
      dilationMatrix t ∈ conjugateSubgroup Γ B := by
  obtain ⟨B, t, ht, hdisc, hmem⟩ := exists_discrete_normalized_subgroup Γ a htrace
  exact ⟨B, t, ht, hdisc, conjugateSubgroup_cocompact Γ B, hmem⟩

end Singularity
