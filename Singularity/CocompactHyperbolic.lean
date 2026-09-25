import Singularity.SmallRowHyperbolic
import Singularity.CocompactSmallRow
import Singularity.ConjugateCocompact

/-!
# Existence of a hyperbolic element in the cocompact case

Cocompactness provides matrices whose lower row tends to zero. An infinite orbit
of infinity supplies an element not fixing it. The determinant/trace argument
therefore produces a hyperbolic element, and the proved normalization gives a
positive dilation in an actual cocompact conjugate subgroup.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- A compact-boundary SL transformation fixes infinity precisely when its lower-left entry vanishes. -/
theorem compactBoundary_fixes_infty_iff (g : SL(2, ℝ)) :
    g • (∞ : OnePoint ℝ) = ∞ ↔ g 1 0 = 0 := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ g) • (∞ : OnePoint ℝ) = ∞ ↔ _
  rw [OnePoint.smul_infty_eq_ite]
  change (if g 1 0 = 0 then (∞ : OnePoint ℝ) else ((g 0 0 / g 1 0 : ℝ) : OnePoint ℝ)) = ∞ ↔ _
  by_cases hc : g 1 0 = 0 <;> simp [hc]

/-- An infinite boundary orbit of infinity rules out an entirely upper triangular subgroup. -/
theorem exists_lowerLeft_ne_zero_of_infinite_orbit (Γ : Subgroup SL(2, ℝ))
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) :
    ∃ b : Γ, (b : SL(2, ℝ)) 1 0 ≠ 0 := by
  by_contra h
  push Not at h
  have hsub : MulAction.orbit Γ (∞ : OnePoint ℝ) ⊆ {∞} := by
    rintro p ⟨b, rfl⟩
    exact (compactBoundary_fixes_infty_iff (b : SL(2, ℝ))).mpr (h b)
  exact horbit ((Set.finite_singleton _).subset hsub)

/-- Cocompactness and an infinite boundary orbit of infinity imply existence of a hyperbolic trace. -/
theorem exists_hyperbolic_of_cocompact (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) :
    ∃ a : Γ, 2 < |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1| := by
  obtain ⟨g, hc, hd⟩ := exists_cocompact_small_lower_row Γ
  obtain ⟨b, hb⟩ := exists_lowerLeft_ne_zero_of_infinite_orbit Γ horbit
  exact exists_hyperbolic_of_small_lower_row Γ g hc hd b hb

/-- No hyperbolic element or conjugating matrix is assumed in this normalized-group existence theorem. -/
theorem exists_normalized_cocompact_of_infinite_orbit (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) :
    ∃ (B : SL(2, ℝ)) (t : ℝ), 0 < t ∧ DiscreteTopology (conjugateSubgroup Γ B) ∧
      CompactSpace (Quotient (MulAction.orbitRel (conjugateSubgroup Γ B) ℍ)) ∧
      dilationMatrix t ∈ conjugateSubgroup Γ B := by
  obtain ⟨a, ha⟩ := exists_hyperbolic_of_cocompact Γ horbit
  exact exists_cocompact_normalized_subgroup Γ a ha

end Singularity
