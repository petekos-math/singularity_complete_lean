import Singularity.ParabolicCommonFixedPoint
import Singularity.TraceNonamenable

/-!
# Nonelementarity supplies a hyperbolic element without compactness

If a subgroup of SL(2,R) has no hyperbolic trace, the elliptic and parabolic
commutator arguments produce a common interior or ideal fixed point. Thus
infinite geometric orbits supply the hyperbolic element needed for the already
proved ping-pong and spectral-gap arguments, also in the noncocompact case.
-/

noncomputable section
open Set Filter OnePoint MeasureTheory
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- A group all of whose traces have absolute value at most two has a common
fixed point in the hyperbolic plane or on its ideal boundary. -/
theorem common_fixedPoint_of_trace_bound (Γ : Subgroup SL(2, ℝ))
    (hbound : ∀ g : Γ, |(g : SL(2, ℝ)) 0 0 + (g : SL(2, ℝ)) 1 1| ≤ 2) :
    (∃ z : ℍ, ∀ g : Γ, g • z = z) ∨
      (∃ p : OnePoint ℝ, ∀ g : Γ, g • p = p) := by
  by_cases hell : ∃ a : Γ, |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1| < 2
  · obtain ⟨a, ha⟩ := hell
    exact Or.inl (exists_common_fixedPoint_of_elliptic Γ hbound a ha)
  push Not at hell
  right
  by_cases hc : ∃ a : Γ, (a : SL(2, ℝ)) 1 0 ≠ 0
  · obtain ⟨a, ha⟩ := hc
    apply exists_common_boundary_fixedPoint_of_parabolic Γ hbound a _ ha
    have he := le_antisymm (hbound a) (hell a)
    nlinarith [sq_abs ((a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1)]
  · push Not at hc
    exact ⟨∞, fun g => (compactBoundary_fixes_infty_iff g).mpr (hc g)⟩

/-- A common fixed point has a singleton orbit. -/
theorem orbit_eq_singleton_of_forall_smul_eq {G X : Type*} [Group G] [MulAction G X]
    (x : X) (hx : ∀ g : G, g • x = x) : MulAction.orbit G x = {x} := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact hx g
  · rintro rfl
    exact MulAction.mem_orbit_self _

/-- Every subgroup with infinite interior and boundary orbits contains a hyperbolic element.
No discreteness or cocompactness is needed for this algebraic conclusion. -/
theorem exists_hyperbolic_of_infinite_geometric_orbits (Γ : Subgroup SL(2, ℝ))
    (hinterior : ∀ z : ℍ, (MulAction.orbit Γ z).Infinite)
    (hboundary : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) :
    ∃ a : Γ, 2 < |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1| := by
  by_contra h
  push Not at h
  rcases common_fixedPoint_of_trace_bound Γ h with ⟨z, hz⟩ | ⟨p, hp⟩
  · apply hinterior z
    rw [orbit_eq_singleton_of_forall_smul_eq z hz]
    exact Set.finite_singleton z
  · apply hboundary p
    rw [orbit_eq_singleton_of_forall_smul_eq p hp]
    exact Set.finite_singleton p

/-- Nonelementarity alone supplies the hyperbolic element in the invariant-mean obstruction. -/
theorem fuchsian_no_invariantMean_of_infinite_geometric_orbits (Γ : Subgroup SL(2, ℝ))
    (hinterior : ∀ z : ℍ, (MulAction.orbit Γ z).Infinite)
    (hboundary : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) : ¬HasInvariantMean Γ := by
  obtain ⟨a, ha⟩ := exists_hyperbolic_of_infinite_geometric_orbits Γ hinterior hboundary
  exact fuchsian_no_invariantMean_of_abs_trace Γ a ha hboundary

/-- The original, possibly nonsymmetric right Markov operator has a spectral gap
under geometric nonelementarity and finite semigroup generation. -/
theorem rightMarkov_gap_of_infinite_geometric_orbits (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (hinterior : ∀ z : ℍ, (MulAction.orbit Γ z).Infinite)
    (hboundary : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    spectralRadius ℂ (rightMarkov s μ) < 1 :=
  rightMarkov_nonamenable_spectral_gap s μ hpos hmass hgen
    (fuchsian_no_invariantMean_of_infinite_geometric_orbits Γ hinterior hboundary)

end Singularity
