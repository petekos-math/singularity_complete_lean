import Singularity.VisualShadowExceptionalLimit
import Singularity.AdjustableExceptionalCover
import Singularity.ProjectiveNonelementary

/-!
# Finite eventual coverage by actual visual inverse shadows

The exceptional-point subsequence and nonelementary orbit escape provide a
finite corrected eventual cover for every sequence of group elements. All
geometric hypotheses in this visual statement are proved, without a
cocompactness, random-walk, or nonsingularity assumption.
-/

noncomputable section
open Set Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology

namespace Singularity

/-- Every group sequence has a subsequence whose sufficiently wide inverse
visual shadows cover the boundary eventually after finitely many corrections. -/
theorem fuchsian_visualShadow_finite_eventual_cover
    (Γ : Subgroup PSL(2, ℝ)) (hne : ProjectiveNonelementary Γ)
    (g : ℕ → Γ) (z : ℍ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ r : ℝ, 0 < r ∧ ∃ F : Finset Γ,
      ∀ ξ : OnePoint ℝ, ∃ a ∈ F, ∀ᶠ n in atTop,
        g (φ n) • (a⁻¹ • ξ) ∈ visualShadow z (g (φ n) • z) r := by
  obtain ⟨φ, hφ, p, hp⟩ := projective_visualShadow_exceptional_subsequence
    (fun n => (g n : PSL(2, ℝ))) z
  have hescape (ξ : OnePoint ℝ) : ∃ a : Γ, a⁻¹ • ξ ∉ ({p} : Set (OnePoint ℝ)) := by
    by_contra hnone
    push Not at hnone
    apply hne.infinite_boundary_orbits Γ ξ
    apply (finite_singleton p).subset
    rintro η ⟨a, rfl⟩
    simpa only [inv_inv] using hnone a⁻¹
  obtain ⟨U, hU, hpU, F, hF⟩ := finite_corrections_avoid_exceptional_neighborhood
    ({p} : Set (OnePoint ℝ)) isClosed_singleton hescape
  obtain ⟨r, hr, hex⟩ := hp U hU (hpU (mem_singleton p))
  refine ⟨φ, hφ, r, hr, F, fun ξ => ?_⟩
  obtain ⟨a, ha, hnot⟩ := hF ξ
  refine ⟨a, ha, ?_⟩
  filter_upwards [hex] with n hn
  by_contra hbad
  exact hnot (hn hbad)

end Singularity
