import Singularity.BoundaryFiniteEntranceRepresentation
import Singularity.FuchsianBoundaryConcentration
import Singularity.FuchsianDeficitFiniteEntrance

/-!
# Finite entrance representations from actual Fuchsian paths

The density representation is proved whenever the indicated boundary event
forces an actual walk to visit the finite set. Compactness therefore follows
from a pathwise finite-separator property. Constructing those separators in
the unrestricted geometry remains a separate, unproved obligation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology
namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen

/-- Actual hitting densities have an exact finite entrance representation
on a region whose sample paths must visit the given finite set. -/
theorem fuchsian_density_finite_entrance_of_boundary_visit
    (A : Finset Γ) (x : Γ) {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hvisit : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      x • projectiveBoundaryMap Γ s z ω ∈ E → ∃ n, walkPosition s x n ω ∈ A) :
    ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass, ξ ∈ E →
      stationaryRealDensity (projectiveHittingMeasure Γ s z μ hpos hmass) x ξ =
        ∑ a : A, firstEntranceKernel s μ (A : Set Γ) x a *
          stationaryRealDensity (projectiveHittingMeasure Γ s z μ hpos hmass) (a : Γ) ξ := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableMul Γ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  exact walkBoundaryLaw_density_finite_entrance s μ (fun g hg => (hpos g hg).le) hmass
    (projectiveNonelementary_rightMarkov_gap Γ hne s μ hpos hmass hgen)
    (projectiveBoundaryMap Γ s z) (measurable_projectiveBoundaryMap Γ s z)
    (fuchsian_boundaryMap_first_step Γ hne s μ hpos hmass hgen z)
    (fun g => (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z g).1)
    A x hE hvisit

/-- The remaining sufficient geometry can be stated solely in terms of
actual sample paths: outside each exceptional neighborhood, all late starting
points use one finite separator. The entrance representation and deficit
bound then follow internally. This does not construct those separators. -/
theorem fuchsian_deficit_compactness_of_path_separators
    (hsep : ∀ g : ℕ → Γ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Z : Set (OnePoint ℝ), Z.Finite ∧
        ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ A : Finset Γ,
          ∀ᶠ n in atTop, ∀ᵐ ω ∂infiniteWalkLaw s μ (fun a ha => (hpos a ha).le) hmass,
            (g (φ n))⁻¹ • projectiveBoundaryMap Γ s z ω ∉ U →
              ∃ k, walkPosition s (g (φ n))⁻¹ k ω ∈ A) :
    FuchsianDeficitCompactness Γ s μ hpos hmass z := by
  apply fuchsian_deficit_compactness_of_finite_entrance Γ hne s μ hpos hmass hgen z
  intro g
  obtain ⟨φ, hφ, Z, hZ, hbound⟩ := hsep g
  refine ⟨φ, hφ, Z, hZ, fun U hU hZU => ?_⟩
  obtain ⟨A, hA⟩ := hbound U hU hZU
  refine ⟨A, ?_⟩
  filter_upwards [hA] with n hn
  filter_upwards [fuchsian_density_finite_entrance_of_boundary_visit
    Γ hne s μ hpos hmass hgen z A (g (φ n))⁻¹ hU.measurableSet.compl hn] with ξ hξ hnot
  exact (hξ hnot).le

end Singularity
