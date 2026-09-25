import Singularity.FuchsianHittingMeasure
import Singularity.GeometricHittingErgodicity
import Singularity.LimitSetDynamics

/-!
# Ergodicity and nonsingularity for general projective hitting laws

These statements concern the actual hitting measure of any discrete
nonelementary subgroup, without a compactness or quasiconvexity assumption.
Nonsingularity implies absolute continuity, but no uniform density bound or
converse absolute continuity is asserted.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- Every projective transformation preserves the visual measure class. -/
theorem compactPoissonMeasure_projective_quasiInvariant (z : ℍ) (g : PSL(2, ℝ)) :
    Measure.map (fun ξ : OnePoint ℝ => g • ξ) (compactPoissonMeasure z) ≪ compactPoissonMeasure z := by
  rw [compactPoissonMeasure_projective_covariance]
  exact compactPoissonMeasure_absolutelyContinuous _ _

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen

/-- Almost invariant measurable boundary sets have hitting probability zero or one. -/
theorem fuchsian_hittingMeasure_invariant_zero_one {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' E =ᵐ[
      projectiveHittingMeasure Γ s z μ hpos hmass] E) :
    projectiveHittingMeasure Γ s z μ hpos hmass E = 0 ∨
      projectiveHittingMeasure Γ s z μ hpos hmass E = 1 := by
  let : MeasurableSpace (projectiveSubgroupLift Γ) := ⊤
  let : MeasurableSingletonClass (projectiveSubgroupLift Γ) := inferInstance
  let : DiscreteTopology (projectiveSubgroupLift Γ) := projectiveSubgroupLift_discrete Γ
  have hg := projectiveLiftSupport_generates_of_mass Γ s μ hmass hgen
  let : Countable (projectiveSubgroupLift Γ) := countable_of_finite_jump_generation _ hg
  let : MeasurableMul (projectiveSubgroupLift Γ) :=
    ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  have hr := projectiveNonelementary_lift_rightMarkov_gap Γ hne
    (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ)
    (projectiveLiftWeight_positive Γ s μ hpos) (projectiveLiftWeight_mass Γ s μ hmass) hg
  rw [projectiveHittingMeasure_eq_lift Γ s z μ hpos hmass hgen hr] at hinv ⊢
  apply geometricHittingMeasure_invariant_zero_one (projectiveSubgroupLift Γ)
    (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ)
    (projectiveLiftWeight_positive Γ s μ hpos) (projectiveLiftWeight_mass Γ s μ hmass) hg hr z hE
  intro g
  exact hinv (projectiveLiftProjection Γ g)

/-- Nonsingularity against visual measure implies absolute continuity for the
actual projective hitting law, with no compactness assumption. -/
theorem fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular
    (hns : ¬ projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z) :
    projectiveHittingMeasure Γ s z μ hpos hmass ≪ compactPoissonMeasure z := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  exact absolutelyContinuous_of_invariant_zero_one (G := Γ) _ _
    (fun g => compactPoissonMeasure_projective_quasiInvariant z (g : PSL(2, ℝ)))
    (fun _ hE hinv => fuchsian_hittingMeasure_invariant_zero_one Γ hne s μ hpos hmass hgen z hE hinv) hns

/-- The general projective hitting law is either singular or absolutely continuous. -/
theorem fuchsian_hittingMeasure_singular_or_absolutelyContinuous :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z ∨
      projectiveHittingMeasure Γ s z μ hpos hmass ≪ compactPoissonMeasure z := by
  by_cases h : projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z
  · exact Or.inl h
  · exact Or.inr (fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular Γ hne s μ hpos hmass hgen z h)

end Singularity
