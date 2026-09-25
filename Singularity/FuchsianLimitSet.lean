import Singularity.FuchsianHittingMeasure

/-!
# The actual hitting measure is carried by the ideal orbit limit set

Define the ideal limit set directly as the boundary part of the closure of an
orbit in the compact sphere. Almost-sure convergence places the actual hitting
law on this closed set. Consequently, a visual-null orbit limit set implies
singularity, also for noncocompact groups. Visual nullity is an explicit
hypothesis here; it is not asserted for every noncocompact group.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped MatrixGroups UpperHalfPlane Topology

namespace Singularity

/-- Ideal accumulation points of the orbit of `z`, expressed in the compact boundary. -/
def projectiveOrbitLimitSet (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) : Set (OnePoint ℝ) :=
  compactBoundaryEmbedding ⁻¹' closure (Set.range (fun g : Γ => hyperbolicCompactEmbedding (g • z)))

/-- The ideal orbit limit set is closed. -/
theorem isClosed_projectiveOrbitLimitSet (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    IsClosed (projectiveOrbitLimitSet Γ z) :=
  isClosed_closure.preimage continuous_compactBoundaryEmbedding

/-- The ideal orbit limit set is a compact measurable subset of the boundary. -/
theorem isCompact_projectiveOrbitLimitSet (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    IsCompact (projectiveOrbitLimitSet Γ z) :=
  (isClosed_projectiveOrbitLimitSet Γ z).isCompact

/-- Every ideal limit of actual orbit points belongs to the orbit limit set. -/
theorem mem_projectiveOrbitLimitSet_of_tendsto (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    (g : ℕ → Γ) (p : OnePoint ℝ)
    (h : Tendsto (fun n => hyperbolicCompactEmbedding (g n • z)) atTop
      (𝓝 (compactBoundaryEmbedding p))) : p ∈ projectiveOrbitLimitSet Γ z := by
  apply isClosed_closure.mem_of_tendsto h
  exact Eventually.of_forall (fun n => subset_closure (Set.mem_range_self (g n)))

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen in
/-- Almost every boundary limit lies in the actual ideal orbit limit set. -/
theorem fuchsian_boundaryMap_mem_limitSet :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      projectiveBoundaryMap Γ s z ω ∈ projectiveOrbitLimitSet Γ z := by
  filter_upwards [fuchsian_boundaryMap_tendsto Γ hne s μ hpos hmass hgen z] with ω hω
  exact mem_projectiveOrbitLimitSet_of_tendsto Γ z (fun n => walkPosition s 1 n ω) _ hω

include hne hgen in
/-- The complement of the orbit limit set has zero hitting probability. -/
theorem fuchsian_hittingMeasure_limitSet_compl :
    projectiveHittingMeasure Γ s z μ hpos hmass (projectiveOrbitLimitSet Γ z)ᶜ = 0 := by
  unfold projectiveHittingMeasure walkBoundaryLaw
  rw [Measure.map_apply (measurable_projectiveBoundaryMap Γ s z)
    (isClosed_projectiveOrbitLimitSet Γ z).measurableSet.compl]
  exact ae_iff.mp (fuchsian_boundaryMap_mem_limitSet Γ hne s μ hpos hmass hgen z)

include hne hgen in
/-- The ideal orbit limit set has full hitting probability. -/
theorem fuchsian_hittingMeasure_limitSet :
    projectiveHittingMeasure Γ s z μ hpos hmass (projectiveOrbitLimitSet Γ z) = 1 := by
  have := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  rw [← measure_univ (μ := projectiveHittingMeasure Γ s z μ hpos hmass)]
  exact measure_eq_measure_of_null_sdiff (Set.subset_univ _) (by
    simpa only [Set.compl_eq_univ_sdiff] using fuchsian_hittingMeasure_limitSet_compl Γ hne s μ hpos hmass hgen z)

include hne hgen in
/-- A visual-null ideal orbit limit set gives singularity of the actual hitting law.
The nullity hypothesis remains explicit, including in noncocompact applications. -/
theorem fuchsian_hittingMeasure_singular_of_null_limitSet
    (hnull : compactPoissonMeasure z (projectiveOrbitLimitSet Γ z) = 0) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  exact ⟨(projectiveOrbitLimitSet Γ z)ᶜ, (isClosed_projectiveOrbitLimitSet Γ z).measurableSet.compl,
    fuchsian_hittingMeasure_limitSet_compl Γ hne s μ hpos hmass hgen z, by simpa using hnull⟩

end Singularity
