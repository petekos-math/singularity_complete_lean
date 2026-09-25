import Singularity.ProjectiveCuspExitSets
import Singularity.ChartBoundaryArcs
import Singularity.FuchsianFiniteSeparatorRegions

/-!
# Local Green-deficit bounds from two actual cusps

Two parabolic endpoints determine a half-plane with a finite exit set.
Almost every path starting on that side and ending on the opposite ideal
arc visits this set. The actual hitting density therefore has a finite
entrance representation there, giving a uniform Green-deficit bound.
No entrance or separation hypothesis is left in these local statements.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped Classical MatrixGroups UpperHalfPlane Topology
namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
  (a b : Γ) (ha : ProjectiveParabolic (a : PSL(2, ℝ)))
  (hb : ProjectiveParabolic (b : PSL(2, ℝ)))
  (p q : OnePoint ℝ) (hap : a • p = p) (hbq : b • q = q)
  (B : SL(2, ℝ)) (hBp : B • (∞ : OnePoint ℝ) = p)
  (hBq : B • ((0 : ℝ) : OnePoint ℝ) = q)

include hne hgen ha hb hap hbq hBp hBq

/-- The same finite set is visited on every opposite-arc boundary event,
uniformly over starting vertices on the negative side of the cusp chart. -/
theorem fuchsian_cusp_chart_boundary_visit :
    ∃ A : Finset Γ, ∀ x : Γ, (B⁻¹ • (x • z)).re < 0 →
      ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
        x • projectiveBoundaryMap Γ s z ω ∉ chartNonpositiveBoundaryArc B →
          ∃ n, walkPosition s x n ω ∈ A := by
  obtain ⟨A, hA⟩ := projective_cusp_chart_finite_exit_set Γ z s a b ha hb p q hap hbq B hBp hBq
  refine ⟨A, fun x hx => ?_⟩
  exact fuchsian_boundary_visit_of_separator_region Γ hne s μ hpos hmass hgen z
    A {v : Γ | (B⁻¹ • (v • z)).re < 0} (chartNonpositiveBoundaryArc B)
    hA (boundary_mem_arc_of_negative_chart_closure z B) x hx

/-- Opposite a half-plane bounded by two cusps, the actual hitting density
has an exact finite entrance formula, uniformly in its starting vertex. -/
theorem fuchsian_cusp_chart_density_representation :
    ∃ A : Finset Γ, ∀ x : Γ, (B⁻¹ • (x • z)).re < 0 →
      ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
        ξ ∉ chartNonpositiveBoundaryArc B →
          stationaryRealDensity (projectiveHittingMeasure Γ s z μ hpos hmass) x ξ =
            ∑ v : A, firstEntranceKernel s μ (A : Set Γ) x v *
              stationaryRealDensity (projectiveHittingMeasure Γ s z μ hpos hmass) (v : Γ) ξ := by
  obtain ⟨A, hA⟩ := fuchsian_cusp_chart_boundary_visit Γ hne s μ hpos hmass hgen z
    a b ha hb p q hap hbq B hBp hBq
  refine ⟨A, fun x hx => ?_⟩
  exact fuchsian_density_finite_entrance_of_boundary_visit Γ hne s μ hpos hmass hgen z A x
    (isClosed_chartNonpositiveBoundaryArc B).measurableSet.compl (hA x hx)

/-- The Green minus stationary-cocycle deficit is uniformly bounded on the
opposite ideal arc whenever the inverse orbit point lies in the cusp half-plane. -/
theorem fuchsian_cusp_chart_deficit_bound :
    ∃ R : ℝ, ∀ g : Γ, (B⁻¹ • (g⁻¹ • z)).re < 0 →
      ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
        ξ ∉ chartNonpositiveBoundaryArc B →
          greenDistance s μ 1 g -
            stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) g ξ ≤ R := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableMul Γ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  obtain ⟨A, hA⟩ := fuchsian_cusp_chart_density_representation Γ hne s μ hpos hmass hgen z
    a b ha hb p q hap hbq B hBp hBq
  obtain ⟨R, hR⟩ := stationary_deficit_bound_of_finite_entrance s μ hpos hmass hgen
    (projectiveNonelementary_rightMarkov_gap Γ hne s μ hpos hmass hgen)
    (projectiveHittingMeasure Γ s z μ hpos hmass)
    (fuchsian_hittingMeasure_stationary Γ hne s μ hpos hmass hgen z) A
  refine ⟨R, fun g hg => hR g (chartNonpositiveBoundaryArc B)ᶜ ?_⟩
  filter_upwards [hA g⁻¹ hg] with ξ hξ hnot
  exact (hξ hnot).le

end Singularity
