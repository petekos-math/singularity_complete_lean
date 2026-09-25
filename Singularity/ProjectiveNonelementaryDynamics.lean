import Singularity.NonelementaryHyperbolic
import Singularity.ProjectiveNonelementary
import Singularity.ProjectiveSubgroupLift

/-!
# Hyperbolic dynamics and the spectral gap for nonelementary projective groups

The geometric finite-orbit definition produces a hyperbolic element in the
special-linear lift. Its north--south dynamics descends to the original PSL₂
action, where ping-pong gives a free subgroup and rules out invariant means.
Cocompactness and even discreteness are unnecessary for this part.
-/

noncomputable section
open Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- Geometric nonelementarity produces an actual hyperbolic matrix in the full lift. -/
theorem projectiveNonelementary_exists_hyperbolic_lift (Γ : Subgroup PSL(2, ℝ))
    (h : ProjectiveNonelementary Γ) :
    ∃ a : projectiveSubgroupLift Γ, 2 < |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1| := by
  apply exists_hyperbolic_of_infinite_geometric_orbits
  · intro z
    rw [projectiveSubgroupLift_hyperbolic_orbit]
    exact h.infinite_hyperbolic_orbits Γ z
  · exact projectiveSubgroupLift_infinite_orbits Γ (h.infinite_boundary_orbits Γ)

/-- An element of the original projective group has uniform north--south dynamics. -/
theorem projectiveNonelementary_exists_northSouth (Γ : Subgroup PSL(2, ℝ))
    (h : ProjectiveNonelementary Γ) :
    ∃ (g : Γ) (p q : OnePoint ℝ), p ≠ q ∧ UniformNorthSouth g p q := by
  obtain ⟨a, ha⟩ := projectiveNonelementary_exists_hyperbolic_lift Γ h
  obtain ⟨t, ht, B, hB⟩ := exists_dilation_conjugacy_of_abs_trace (a : SL(2, ℝ)) ha
  refine ⟨projectiveLiftProjection Γ (a ^ 2), B • ∞, B • ((0 : ℝ) : OnePoint ℝ), ?_, ?_⟩
  · exact fun he => (by simp : (∞ : OnePoint ℝ) ≠ ((0 : ℝ) : OnePoint ℝ))
      (MulAction.injective B he)
  · intro U hU V hV
    filter_upwards [(dilationMatrix_northSouth ht).conjugate B U hU V hV] with n hn
    intro x hx
    rw [← map_pow, projectiveLiftProjection_smul_boundary]
    change ((a : SL(2, ℝ)) ^ 2) ^ n • x ∈ U
    rw [hB]
    exact hn x hx

/-- Nonelementarity gives a free subgroup of the original projective subgroup. -/
theorem projectiveNonelementary_exists_free_subgroup (Γ : Subgroup PSL(2, ℝ))
    (h : ProjectiveNonelementary Γ) :
    ∃ j : FreeGroup Bool →* Γ, Function.Injective j := by
  obtain ⟨g, p, q, hpq, hdyn⟩ := projectiveNonelementary_exists_northSouth Γ h
  exact exists_free_subgroup_of_northSouth hpq hdyn
    (h.infinite_boundary_orbits Γ p) (h.infinite_boundary_orbits Γ q)

/-- A nonelementary projective group has no invariant mean. -/
theorem projectiveNonelementary_no_invariantMean (Γ : Subgroup PSL(2, ℝ))
    (h : ProjectiveNonelementary Γ) : ¬HasInvariantMean Γ := by
  obtain ⟨j, hj⟩ := projectiveNonelementary_exists_free_subgroup Γ h
  exact no_invariantMean_of_free_subgroup j hj

/-- The original right Markov operator has spectral radius less than one, without
symmetry, laziness, or compactness of the geometric quotient. -/
theorem projectiveNonelementary_rightMarkov_gap (Γ : Subgroup PSL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (h : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    spectralRadius ℂ (rightMarkov s μ) < 1 :=
  rightMarkov_nonamenable_spectral_gap s μ hpos hmass hgen
    (projectiveNonelementary_no_invariantMean Γ h)

/-- The full lift has the same nonelementary spectral-gap conclusion. -/
theorem projectiveNonelementary_lift_rightMarkov_gap (Γ : Subgroup PSL(2, ℝ))
    [MeasurableSpace (projectiveSubgroupLift Γ)] [MeasurableSingletonClass (projectiveSubgroupLift Γ)]
    [MeasurableMul (projectiveSubgroupLift Γ)]
    (h : ProjectiveNonelementary Γ)
    (s : Finset (projectiveSubgroupLift Γ)) (μ : projectiveSubgroupLift Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set (projectiveSubgroupLift Γ)) = ⊤) :
    spectralRadius ℂ (rightMarkov s μ) < 1 := by
  obtain ⟨a, ha⟩ := projectiveNonelementary_exists_hyperbolic_lift Γ h
  exact rightMarkov_gap_of_abs_trace (projectiveSubgroupLift Γ) a ha
    (projectiveSubgroupLift_infinite_orbits Γ (h.infinite_boundary_orbits Γ)) s μ hpos hmass hgen

end Singularity
