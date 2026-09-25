import Singularity.ShrinkingBoundaryCharts
import Singularity.ProjectiveOrbitSubsequences
import Singularity.FuchsianCuspDeficit
import Singularity.FuchsianSingularityFromDeficitCompactness

/-!
# Singularity with full ideal limit set and a parabolic

Relative density of parabolic fixed points becomes density on the circle
when the ideal limit set is full. The resulting shrinking cusp charts give
finite path separators around every ideal orbit limit. Finite-valued tails
are handled by entrance at time zero. This proves deficit compactness and
hence singularity, with no additional compactness or entrance premise.

The geometric hypotheses here are explicit: full ideal limit set and the
existence of a parabolic. Identifying all nonuniform lattices, or all
remaining finitely generated Fuchsian groups, with the covered cases is a
separate obligation.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
  (hfull : projectiveOrbitLimitSet Γ z = univ)
  (hpar : ∃ g : Γ, ProjectiveParabolic (g : PSL(2, ℝ)))

include hne hgen hfull hpar

/-- Full ideal boundary and one parabolic supply the previously conditional
Green-deficit compactness property, using actual finite path separators. -/
theorem fuchsian_deficit_compactness_of_full_limitSet_parabolic :
    FuchsianDeficitCompactness Γ s μ hpos hmass z := by
  apply fuchsian_deficit_compactness_of_path_separators Γ hne s μ hpos hmass hgen z
  intro g
  obtain ⟨φ, hφ, hfinite | ⟨ξ, ht⟩⟩ :=
    projective_orbit_subsequence_finite_or_boundary Γ z (fun n => (g n)⁻¹)
  · obtain ⟨A, hA⟩ := hfinite
    refine ⟨φ, hφ, ∅, finite_empty, fun U _ _ => ⟨A, ?_⟩⟩
    filter_upwards [hA] with n hn
    apply Eventually.of_forall
    intro ω _
    exact ⟨0, hn⟩
  · refine ⟨φ, hφ, {ξ}, finite_singleton ξ, fun U hU hξU => ?_⟩
    obtain ⟨B, hp, hq, hBU, hcenter⟩ := exists_small_parabolic_boundary_chart
      Γ hne z hfull hpar ξ U hU (hξU (mem_singleton ξ))
    obtain ⟨a, ha, hap⟩ := hp
    obtain ⟨b, hb, hbq⟩ := hq
    obtain ⟨A, hA⟩ := fuchsian_cusp_chart_boundary_visit Γ hne s μ hpos hmass hgen z
      a b ha hb (B • (∞ : OnePoint ℝ)) (B • ((0 : ℝ) : OnePoint ℝ)) hap hbq B rfl rfl
    have hneg := eventually_negative_chart_of_boundary_tendsto
      (fun n => (g (φ n))⁻¹ • z) B ξ ht hcenter
    refine ⟨A, ?_⟩
    filter_upwards [hneg] with n hn
    filter_upwards [hA (g (φ n))⁻¹ hn] with ω hω hout
    exact hω (fun hin => hout (hBU hin))

/-- Singularity for every discrete nonelementary projective group with
full ideal limit set and a parabolic, without symmetry of the walk. -/
theorem full_limitSet_parabolic_fuchsian_hittingMeasure_singular :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z :=
  fuchsian_hittingMeasure_singular_of_deficit_compactness Γ hne s μ hpos hmass hgen z
    (fuchsian_deficit_compactness_of_full_limitSet_parabolic Γ hne s μ hpos hmass hgen z hfull hpar)

/-- The corresponding singularity in the real boundary chart. -/
theorem full_limitSet_parabolic_fuchsian_hittingMeasure_singular_lebesgue :
    finiteBoundaryMeasure (projectiveHittingMeasure Γ s z μ hpos hmass) ⟂ₘ volume :=
  (compact_hitting_singularity_iff _ z).mp
    (full_limitSet_parabolic_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z hfull hpar)

end Singularity
