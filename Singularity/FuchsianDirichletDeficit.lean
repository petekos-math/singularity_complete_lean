import Singularity.BoundedHeightSeparators
import Singularity.ProjectiveDirichletEnds
import Singularity.FuchsianCuspOrProperLimitSingularity

/-!
# Deficit compactness from a noncompact quotient of the first kind

A Dirichlet end supplies one bounded-height endpoint. Its orbit is dense
when the limit set is full. Two such endpoints give the finite separators
needed by the previously verified analytic argument.
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

include hne hgen

/-- Dense bounded-height endpoints imply the full deficit-compactness property. -/
theorem fuchsian_deficit_compactness_of_dense_bounded_height_endpoints
    (hdense : Dense (projectiveBoundedHeightEndpoints Γ z)) :
    FuchsianDeficitCompactness Γ s μ hpos hmass z := by
  apply fuchsian_deficit_compactness_of_path_separators Γ hne s μ hpos hmass hgen z
  intro g
  obtain ⟨φ, hφ, hfinite | ⟨ξ, ht⟩⟩ :=
    projective_orbit_subsequence_finite_or_boundary Γ z (fun n => (g n)⁻¹)
  · obtain ⟨A, hA⟩ := hfinite
    refine ⟨φ, hφ, ∅, finite_empty, fun U _ _ => ⟨A, ?_⟩⟩
    filter_upwards [hA] with n hn
    exact Eventually.of_forall (fun ω _ => ⟨0, hn⟩)
  · refine ⟨φ, hφ, {ξ}, finite_singleton ξ, fun U hU hξU => ?_⟩
    obtain ⟨B, hp, hq, hBU, hcenter⟩ := exists_small_boundary_chart_of_dense
      _ hdense ξ U hU (hξU (mem_singleton ξ))
    obtain ⟨A, hA⟩ := projective_boundedHeight_chart_finite_exit_set Γ z s B hp hq
    have hneg := eventually_negative_chart_of_boundary_tendsto
      (fun n => (g (φ n))⁻¹ • z) B ξ ht hcenter
    refine ⟨A, ?_⟩
    filter_upwards [hneg] with n hn
    have hvisit := fuchsian_boundary_visit_of_separator_region Γ hne s μ hpos hmass hgen z
      A {v : Γ | (B⁻¹ • (v • z)).re < 0} (chartNonpositiveBoundaryArc B)
      hA (boundary_mem_arc_of_negative_chart_closure z B) (g (φ n))⁻¹ hn
    filter_upwards [hvisit] with ω hω hout
    exact hω (fun hin => hout (hBU hin))

/-- No classification of finitely generated Fuchsian groups is needed:
noncompactness and a full ideal limit set already supply deficit compactness. -/
theorem fuchsian_deficit_compactness_of_noncompact_full_limitSet
    (hnc : ¬CompactSpace (Quotient (MulAction.orbitRel Γ ℍ)))
    (hfull : projectiveOrbitLimitSet Γ z = univ) :
    FuchsianDeficitCompactness Γ s μ hpos hmass z := by
  apply fuchsian_deficit_compactness_of_dense_bounded_height_endpoints Γ hne s μ hpos hmass hgen z
  exact dense_projectiveBoundedHeightEndpoints_of_full_limitSet Γ hne z hfull
    (projectiveBoundedHeightEndpoints_nonempty_of_noncompact Γ z hnc)

end Singularity
