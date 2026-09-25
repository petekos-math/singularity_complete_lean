import Singularity.ProjectiveHittingMeasure

/-!
# Stationarity and quasi-invariance survive the projective lift

The two half-weight signs have the same boundary action. Summing their
contributions recovers exactly the original stationary equation. The equality
of the actual hitting laws then also transfers equivalence with every translate.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- Summing two half-weight lifts recovers any finite linear combination on the projective group. -/
theorem projectiveLiftSupport_weighted_sum (Γ : Subgroup PSL(2, ℝ))
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    {M : Type*} [AddCommMonoid M] [Module ℝ≥0∞ M] (f : Γ → M) :
    ∑ g ∈ projectiveLiftSupport Γ s, ENNReal.ofReal (projectiveLiftWeight Γ μ g) •
      f (projectiveLiftProjection Γ g) = ∑ g ∈ s, ENNReal.ofReal (μ g) • f g := by
  rw [projectiveLiftSupport, Finset.sum_union (projectiveLiftSupport_disjoint Γ s),
    Finset.sum_map, Finset.sum_map]
  change (∑ g ∈ s, ENNReal.ofReal (μ (projectiveLiftProjection Γ (projectiveLiftSection Γ g)) / 2) •
    f (projectiveLiftProjection Γ (projectiveLiftSection Γ g))) +
    (∑ g ∈ s, ENNReal.ofReal (μ (projectiveLiftProjection Γ (projectiveLiftSign Γ * projectiveLiftSection Γ g)) / 2) •
    f (projectiveLiftProjection Γ (projectiveLiftSign Γ * projectiveLiftSection Γ g))) = _
  simp only [map_mul, projectiveLiftProjection_sign, projectiveLiftProjection_section, one_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← add_smul, ← ENNReal.ofReal_add (div_nonneg (hμ g hg) (by norm_num))
    (div_nonneg (hμ g hg) (by norm_num))]
  congr 2
  ring

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableSpace (projectiveSubgroupLift Γ)] [MeasurableSingletonClass (projectiveSubgroupLift Γ)]
  [MeasurableMul (projectiveSubgroupLift Γ)]
  (s : Finset Γ) (z : ℍ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ)) < 1)

attribute [local instance] projectiveSubgroupLift_discrete

include hgen hgap in
/-- Exact stationarity for the projective hitting law, using the original jump probabilities. -/
theorem projectiveHittingMeasure_stationary :
    projectiveHittingMeasure Γ s z μ hpos hmass =
      ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℝ => (g : Γ) • p)
        (projectiveHittingMeasure Γ s z μ hpos hmass) := by
  rw [projectiveHittingMeasure_eq_lift Γ s z μ hpos hmass hgen hgap]
  let ν := geometricHittingMeasure (projectiveSubgroupLift Γ) (projectiveLiftSupport Γ s)
    (projectiveLiftWeight Γ μ) (projectiveLiftWeight_positive Γ s μ hpos)
    (projectiveLiftWeight_mass Γ s μ hmass) (projectiveLiftSupport_generates_of_mass Γ s μ hmass hgen) hgap z
  have hs := geometricHittingMeasure_stationary (projectiveSubgroupLift Γ) (projectiveLiftSupport Γ s)
    (projectiveLiftWeight Γ μ) (projectiveLiftWeight_positive Γ s μ hpos)
    (projectiveLiftWeight_mass Γ s μ hmass) (projectiveLiftSupport_generates_of_mass Γ s μ hmass hgen) hgap z
  change ν = _ at hs ⊢
  rw [hs]
  have he := projectiveLiftSupport_weighted_sum Γ s μ (fun g hg => (hpos g hg).le)
    (fun g => Measure.map (fun p : OnePoint ℝ => g • p) ν)
  rw [← Finset.sum_coe_sort (projectiveLiftSupport Γ s), ← Finset.sum_coe_sort s] at he
  exact he

include hgen hgap in
/-- Every original projective group translate has the same null sets as the hitting law. -/
theorem projectiveHittingMeasure_translate_equivalent (g : Γ) :
    Measure.map (fun p : OnePoint ℝ => g • p) (projectiveHittingMeasure Γ s z μ hpos hmass) ≪
      projectiveHittingMeasure Γ s z μ hpos hmass ∧
    projectiveHittingMeasure Γ s z μ hpos hmass ≪
      Measure.map (fun p : OnePoint ℝ => g • p) (projectiveHittingMeasure Γ s z μ hpos hmass) := by
  rw [projectiveHittingMeasure_eq_lift Γ s z μ hpos hmass hgen hgap]
  obtain ⟨a, rfl⟩ := projectiveLiftProjection_surjective Γ g
  exact geometricHittingMeasure_translate_equivalent (projectiveSubgroupLift Γ) (projectiveLiftSupport Γ s)
    (projectiveLiftWeight Γ μ) (projectiveLiftWeight_positive Γ s μ hpos)
    (projectiveLiftWeight_mass Γ s μ hmass) (projectiveLiftSupport_generates_of_mass Γ s μ hmass hgen) hgap z a

end Singularity
