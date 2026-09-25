import Singularity.ProjectiveEndpointStrips
import Singularity.DenseStripEndpoints
import Singularity.ShrinkingBoundaryCharts
import Singularity.FuchsianFiniteSeparatorRegions
import Singularity.FuchsianSingularityFromDeficitCompactness

/-!
# Singularity with a cusp or a proper ideal limit set

Parabolic fixed points and ordinary boundary points provide finite strips.
Their union is dense when a parabolic exists or the ideal limit set is
proper. Shrinking charts then yield the full subsequential path-separator
property, without any assumption of full limit set or visual nullity.

The full theorem in `FuchsianSingularity` also handles a noncompact quotient
with full ideal limit set, using bounded-height Dirichlet endpoints.
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

/-- Dense parabolic-or-ordinary endpoints prove deficit compactness for
proper limit sets and for every group containing a parabolic. -/
theorem fuchsian_deficit_compactness_of_parabolic_or_proper_limitSet
    (hgeom : projectiveOrbitLimitSet Γ z ≠ univ ∨
      ∃ a : Γ, ProjectiveParabolic (a : PSL(2, ℝ))) :
    FuchsianDeficitCompactness Γ s μ hpos hmass z := by
  have hdense := dense_parabolic_or_ordinary_endpoints Γ hne z hgeom
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
    obtain ⟨A, hA⟩ := projective_endpoint_chart_finite_exit_set Γ z s B hp hq
    have hneg := eventually_negative_chart_of_boundary_tendsto
      (fun n => (g (φ n))⁻¹ • z) B ξ ht hcenter
    refine ⟨A, ?_⟩
    filter_upwards [hneg] with n hn
    have hvisit := fuchsian_boundary_visit_of_separator_region Γ hne s μ hpos hmass hgen z
      A {v : Γ | (B⁻¹ • (v • z)).re < 0} (chartNonpositiveBoundaryArc B)
      hA (boundary_mem_arc_of_negative_chart_closure z B) (g (φ n))⁻¹ hn
    filter_upwards [hvisit] with ω hω hout
    exact hω (fun hin => hout (hBU hin))

/-- Singularity holds whenever the ideal limit set is proper or the group
contains a parabolic. No symmetry, boundary-nullity, or compactness premise
is added to the actual hitting law. -/
theorem parabolic_or_proper_limitSet_fuchsian_hittingMeasure_singular
    (hgeom : projectiveOrbitLimitSet Γ z ≠ univ ∨
      ∃ a : Γ, ProjectiveParabolic (a : PSL(2, ℝ))) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z :=
  fuchsian_hittingMeasure_singular_of_deficit_compactness Γ hne s μ hpos hmass hgen z
    (fuchsian_deficit_compactness_of_parabolic_or_proper_limitSet Γ hne s μ hpos hmass hgen z hgeom)

/-- In particular, every discrete nonelementary group containing a parabolic
has singular hitting measure for the given finite generating law. -/
theorem parabolic_fuchsian_hittingMeasure_singular
    (hpar : ∃ a : Γ, ProjectiveParabolic (a : PSL(2, ℝ))) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z :=
  parabolic_or_proper_limitSet_fuchsian_hittingMeasure_singular
    Γ hne s μ hpos hmass hgen z (Or.inr hpar)

/-- Every proper ideal limit set gives singularity, without a separate
hypothesis that the limit set is visual-null or the orbit quasiconvex. -/
theorem proper_limitSet_fuchsian_hittingMeasure_singular
    (hproper : projectiveOrbitLimitSet Γ z ≠ univ) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z :=
  parabolic_or_proper_limitSet_fuchsian_hittingMeasure_singular
    Γ hne s μ hpos hmass hgen z (Or.inl hproper)

/-- The combined conclusion in the real boundary chart. -/
theorem parabolic_or_proper_limitSet_fuchsian_hittingMeasure_singular_lebesgue
    (hgeom : projectiveOrbitLimitSet Γ z ≠ univ ∨
      ∃ a : Γ, ProjectiveParabolic (a : PSL(2, ℝ))) :
    finiteBoundaryMeasure (projectiveHittingMeasure Γ s z μ hpos hmass) ⟂ₘ volume :=
  (compact_hitting_singularity_iff _ z).mp
    (parabolic_or_proper_limitSet_fuchsian_hittingMeasure_singular Γ hne s μ hpos hmass hgen z hgeom)

end Singularity
