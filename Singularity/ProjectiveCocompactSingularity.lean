import Singularity.ProjectiveHittingMeasure
import Singularity.CocompactHittingSingularity

/-!
# Cocompact singularity for the actual PSL(2,ℝ) walk

Lift each jump with both signs and half its original weight. All hypotheses
of the SL₂ theorem are proved for this lift, and the projective hitting law
has already been identified with its actual hitting law. The spectral gap
and the choice of lift do not occur as assumptions of the conclusion.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped MatrixGroups UpperHalfPlane Topology

namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)

include hgen horbit in
/-- Singularity of the actual projective hitting law, without symmetry or a spectral-gap assumption. -/
theorem projective_cocompact_hittingMeasure_singular :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  let := projectiveSubgroupLift_discrete Γ
  let := projectiveSubgroupLift_cocompact Γ
  let : MeasurableSpace (projectiveSubgroupLift Γ) := ⊤
  let : MeasurableSingletonClass (projectiveSubgroupLift Γ) := inferInstance
  have hg := projectiveLiftSupport_generates_of_mass Γ s μ hmass hgen
  let : Countable (projectiveSubgroupLift Γ) := countable_of_finite_jump_generation _ hg
  let : MeasurableMul (projectiveSubgroupLift Γ) :=
    ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  have hp := projectiveLiftWeight_positive Γ s μ hpos
  have hm := projectiveLiftWeight_mass Γ s μ hmass
  have ho := projectiveSubgroupLift_infinite_orbits Γ horbit
  have hr := rightMarkov_gap_of_cocompact (projectiveSubgroupLift Γ) ho
    (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ) hp hm hg
  rw [projectiveHittingMeasure_eq_lift Γ s z μ hpos hmass hgen hr]
  exact cocompact_hittingMeasure_singular (projectiveSubgroupLift Γ)
    (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ) hp hm hg hr ho z

include hgen horbit in
/-- Under the same geometric hypotheses the named map is the almost-sure limit
of the original projective random walk, not just the lifted walk. -/
theorem projective_cocompact_boundaryMap_tendsto :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Filter.Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) Filter.atTop
        (𝓝 (compactBoundaryEmbedding (projectiveBoundaryMap Γ s z ω))) := by
  let := projectiveSubgroupLift_discrete Γ
  let := projectiveSubgroupLift_cocompact Γ
  let : MeasurableSpace (projectiveSubgroupLift Γ) := ⊤
  let : MeasurableSingletonClass (projectiveSubgroupLift Γ) := inferInstance
  have hg := projectiveLiftSupport_generates_of_mass Γ s μ hmass hgen
  let : Countable (projectiveSubgroupLift Γ) := countable_of_finite_jump_generation _ hg
  let : MeasurableMul (projectiveSubgroupLift Γ) :=
    ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  have hr := rightMarkov_gap_of_cocompact (projectiveSubgroupLift Γ)
    (projectiveSubgroupLift_infinite_orbits Γ horbit)
    (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ)
    (projectiveLiftWeight_positive Γ s μ hpos) (projectiveLiftWeight_mass Γ s μ hmass) hg
  exact projectiveBoundaryMap_tendsto Γ s z μ hpos hmass hgen hr

end Singularity
